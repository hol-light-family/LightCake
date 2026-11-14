(* ========================================================================= *)
(* data_to_word_memoryProof_p1: part 1 of 7 (HOL4 lines 1-2747) of the port  *)
(* of HOL4 compiler/backend/proofs/data_to_word_memoryProofScript.sml        *)
(* (CakeML v3479).  Part of the correctness proof for data_to_word.          *)
(* The parts _p1 ... _p7 are loaded one after the other (each needs the     *)
(* previous one); data_to_word_memoryProof.ml needs the last.                *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "hol4/finite_map.ml";;
needs "hol4/sptree.ml";;
needs "hol4/sorting.ml";;
needs "hol4/int_bitwise.ml";;
needs "hol4/set_sep.ml";;
needs "hol4/multiword.ml";;
needs "basis/pure/mlstring.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/data_space.ml";;
needs "compiler/backend/semantics/bvlSem.ml";;
needs "compiler/backend/gc/gc_shared.ml";;
needs "compiler/backend/gc/copying_gc.ml";;
needs "compiler/backend/gc/gen_gc.ml";;
needs "compiler/backend/gc/gen_gc_partial.ml";;
needs "compiler/backend/data_to_word.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/semantics/dataSem.ml";;
needs "compiler/backend/gc/gc_combined.ml";;
(* HOL4 ancestors not needed by part 1: dataProps, labSem, While and the   *)
(* word_gc functions                                                       *)

prioritize_num();;
type_invention_error := true;;

(* ===== PART 1: HOL4 lines 1-2747 ===== *)

let _ = cake_add_simps [LENGTH_REPLICATE];;

(* HOL4 line 30 (val LESS_4) *)
let LESS_4 = prove
 (`!i. i < 4 <=> (i = 0) \/ (i = 1) \/ (i = 2) \/ (i = 3)`,
  ARITH_TAC);;

(* HOL4 line 31 (val LESS_8) *)
let LESS_8 = prove
 (`!i. i < 8 <=> (i = 0) \/ (i = 1) \/ (i = 2) \/ (i = 3) \/
                 (i = 4) \/ (i = 5) \/ (i = 6) \/ (i = 7)`,
  ARITH_TAC);;

(* HOL4 line 34 *)
let word_eq = prove
 (`!w v:A word. w = v <=> !n. bit n w = bit n v`,
  MATCH_ACCEPT_TAC WORD_EQ_BITS);;

(* HOL4 line 42 *)
let ZIP_REPLICATE = prove
 (`!n (x:A) (y:B). ZIP (REPLICATE n x) (REPLICATE n y) = REPLICATE n (x,y)`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[REPLICATE; ZIP; HD; TL]);;

(* HOL4 line 50 *)
let MEM_EL_APPEND_MID = prove
 (`!n l (c:A) r.
     n < LENGTH l + (LENGTH r + 1) ==>
     MEM (EL n (APPEND (APPEND l [c]) r)) l \/
     EL n (APPEND (APPEND l [c]) r) = c \/
     MEM (EL n (APPEND (APPEND l [c]) r)) r`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `MEM (EL n (APPEND (APPEND l [c:A]) r)) (APPEND (APPEND l [c]) r)`
    MP_TAC THENL
   [MATCH_MP_TAC EL_MEM THEN REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN
    ASM_ARITH_TAC;
    REWRITE_TAC[MEM_APPEND; MEM] THEN MESON_TAC[]]);;

(* HOL4 line 60 *)
let MAX_LIST_sum_bound = prove
 (`!ls. SUM ls <= MAX_LIST ls * LENGTH ls`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[SUM; MAX_LIST; LENGTH; MULT_CLAUSES; LE_REFL] THEN
  MATCH_MP_TAC LE_ADD2 THEN CONJ_TAC THENL
   [REWRITE_TAC[MAX] THEN ARITH_TAC;
    TRANS_TAC LE_TRANS `MAX_LIST t * LENGTH (t:num list)` THEN
    ASM_REWRITE_TAC[LE_MULT_RCANCEL] THEN REWRITE_TAC[MAX] THEN ARITH_TAC]);;

(* HOL4 line 68 *)
let MAX_LIST_bounded_elements = prove
 (`!l1 l2. ALL2 (<=) l1 l2 ==> MAX_LIST l1 <= MAX_LIST l2`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[ALL2; MAX_LIST; LE_REFL] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t':num list`) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MAX] THEN ASM_ARITH_TAC);;

(* HOL4 line 74 *)
let MAX_LIST_MAP = prove
 (`!f l. (!x y. x < y ==> f x < f y)
         ==> MAX_LIST (MAP f l) = if NULL l then 0 else f (MAX_LIST l)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; NULL; MAX_LIST] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `!a b. f (MAX a b) = MAX (f a) (f b)` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    DISJ_CASES_TAC(ARITH_RULE `a < b \/ a = b \/ b < a`) THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`a:num`; `b:num`]) THEN
      ASM_REWRITE_TAC[MAX] THEN ASM_ARITH_TAC;
      FIRST_X_ASSUM DISJ_CASES_TAC THENL
       [ASM_REWRITE_TAC[MAX; LE_REFL];
        FIRST_X_ASSUM(MP_TAC o SPECL [`b:num`; `a:num`]) THEN
        ASM_REWRITE_TAC[MAX] THEN ASM_ARITH_TAC]];
    ALL_TAC] THEN
  COND_CASES_TAC THENL
   [SUBGOAL_THEN `t:num list = []` SUBST_ALL_TAC THENL
     [ASM_MESON_TAC[NULL_EQ]; ALL_TAC] THEN
    REWRITE_TAC[MAX_LIST; MAX; LE] THEN
    ASM_CASES_TAC `h = 0` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ASM_REWRITE_TAC[]]);;

(* HOL4 line 86 *)
let w2i_i2w_IMP = prove
 (`!i. ival (iword i:A word) = i
       ==> integer_word_INT_MIN (:A) <= i /\ i <= integer_word_INT_MAX (:A)`,
  GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[IVAL_IWORD_INT_RANGE; IVAL_BOUND]);;

(* HOL4 line 117 *)
let word_i2w_sub = prove
 (`!a b. word_sub (iword a) (iword b):A word = iword (a - b)`,
  REWRITE_TAC[IWORD_INT_SUB]);;

(* HOL4 line 126: Datatype tag.  BlockTag: immutable Block; RefTag: mutable *)
(* arrays / references; BytesTag: mutable byte arrays / immutable strings; *)
(* ThunkTag: mutable thunks; NumTag: immutable bignum on the heap;          *)
(* Word64Tag: immutable word64 on the heap                                 *)
let data_to_word_memoryProof_tag_INDUCT,data_to_word_memoryProof_tag_RECURSION =
  cake_type
  "data_to_word_memoryProof_tag = BlockTag num
                                | RefTag
                                | BytesTag bool num
                                | ThunkTag thunk_mode
                                | NumTag bool
                                | Word64Tag";;

(* HOL4 line 135 *)
let BlockRep_def = cake_def
  `BlockRep tag (xs:(A heap_address)list) =
     DataElement xs (LENGTH xs) (BlockTag tag,[]:B list)`;;

(* HOL4 lines 139-140: Type ml_el, Type ml_heap (written out, see the       *)
(* header)                                                                  *)

(* HOL4 line 142 *)
let data_to_word_memoryProof_Bytes_def = cake_def
  `Bytes is_bigendian cmp_by_contents (bs:byte list) (ws:(A word)list) =
     (let ws = write_bytes bs ws is_bigendian in
      DataElement [] (LENGTH ws)
        (BytesTag cmp_by_contents (LENGTH bs), MAP wl_Word ws))
     :((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element`;;

(* HOL4 line 148 *)
let data_to_word_memoryProof_Bignum_def = cake_def
  `Bignum i =
     (let (sign,payload) = (i2mw i:bool#(A word)list) in
      DataElement [] (LENGTH payload) (NumTag sign, MAP wl_Word payload))
     :((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element`;;

(* HOL4 line 154 *)
let BlockNil_def = cake_def
  `BlockNil n = word_add (word_shl (word n) 4) (word 2):A word`;;

(* HOL4 line 158 *)
let Word64Rep_DEF = new_definition
  `Word64Rep (s:A->bool) (w:int64) =
     (if dimindex (:A) < 64 then
        DataElement [] 2 (Word64Tag, [wl_Word (word_extract 63 32 w);
                                      wl_Word (word_extract 31 0 w)])
      else
        DataElement [] 1 (Word64Tag, [wl_Word (word_extract 63 0 w:A word)]))
     :((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element`;;

let Word64Rep_def = prove
 (`!w:int64. Word64Rep (:A) w =
     (if dimindex (:A) < 64 then
        DataElement [] 2 (Word64Tag, [wl_Word (word_extract 63 32 w);
                                      wl_Word (word_extract 31 0 w)])
      else
        DataElement [] 1 (Word64Tag, [wl_Word (word_extract 63 0 w:A word)]))
     :((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element`,
  REWRITE_TAC[Word64Rep_DEF]);;

(* HOL4 line 166 *)
let Word64Rep_DataElement = prove
 (`!(a:A->bool) w:int64. ?ws.
     Word64Rep a w:((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
                   heap_element =
     DataElement [] (LENGTH ws) (Word64Tag,ws)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[Word64Rep_DEF] THEN COND_CASES_TAC THEN
  SIMP[LENGTH]);;

(* HOL4 line 172 *)
let ThunkBlock_def = cake_def
  `ThunkBlock ev (x:A heap_address) = DataElement [x] 1 (ThunkTag ev,[]:B list)`;;

(* HOL4 line 176 *)
let v_size_LEMMA = prove
 (`!vs v. MEM v vs ==> data_v_size v <= list_size data_v_size vs`,
  MESON_TAC[MEM_LIST_SIZE; LT_IMP_LE]);;

(* HOL4 line 194 *)
let ref_ptr_annot_def = cake_def
  `ref_ptr_annot conf (SOME (MutBlock tg fin l (c:B) r)) =
     (wl_Word (ptr_bits conf tg (LENGTH l + 1 + LENGTH r)):(A)word_loc) /\
   ref_ptr_annot conf _ = wl_Word (word 0)`;;
let _ = cake_add_simps [ref_ptr_annot_def];;

(* HOL4 line 200 *)
let v_inv_ck_rules,v_inv_ck_ind,v_inv_ck_cases,v_inv_ck_strongind =
  cake_inductive
  `(!ck conf i refs f tf heap.
      small_int (:A) i ==>
      v_inv_ck ck conf (data_Number i) (refs:(data_v bvl_ref)spt)
        (gc_shared_Data (wl_Word (Smallnum i)),f,tf,
         heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
               heap_element)list)) /\
   (!ck conf i refs ptr f tf heap.
      ~small_int (:A) i /\
      heap_lookup ptr heap = SOME (Bignum i) ==>
      v_inv_ck ck conf (data_Number i) refs
        (Pointer ptr (wl_Word (word 0)),f,tf,
         heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
               heap_element)list)) /\
   (!ck conf w refs ptr f tf heap.
      heap_lookup ptr heap = SOME (Word64Rep (:A) w) ==>
      v_inv_ck ck conf (data_Word64 w) refs
        (Pointer ptr (wl_Word (word 0)),f,tf,
         heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
               heap_element)list)) /\
   (!ck conf n refs f tf heap.
      v_inv_ck ck conf (data_CodePtr n) refs
        (gc_shared_Data (wl_Loc n 0),f,tf,
         heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
               heap_element)list)) /\
   (!ck conf b n refs f tf heap.
      n IN FDOM f /\
      (!ev v. ~(lookup n refs = SOME (bvl_Thunk ev v))) /\
      (!tg fin l c r. lookup n refs = SOME (MutBlock tg fin l c r) ==> ~b) ==>
      v_inv_ck ck conf (data_RefPtr b n) refs
        (Pointer (FAPPLY f n) (ref_ptr_annot conf (lookup n refs)),f,tf,
         heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
               heap_element)list)) /\
   (!ck conf n refs ev v x f tf heap.
      lookup n refs = SOME (bvl_Thunk ev v) /\
      (ev = Evaluated ==> data_dest_thunk v refs = data_NotThunk) /\
      n IN FDOM f /\
      heap_lookup (FAPPLY f n) heap = SOME (ThunkBlock ev x) /\
      (~(ck = 0) ==> v_inv_ck (ck - 1) conf v refs (x,f,tf,heap)) ==>
      v_inv_ck ck conf (data_RefPtr F n) refs
        (Pointer (FAPPLY f n) (wl_Word (word 0)),f,tf,
         heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
               heap_element)list)) /\
   (!ck conf n refs v x f tf heap.
      lookup n refs = SOME (bvl_Thunk Evaluated v) /\
      data_dest_thunk v refs = data_NotThunk /\
      (~(ck = 0) ==> v_inv_ck (ck - 1) conf v refs (x,f,tf,heap)) ==>
      v_inv_ck ck conf (data_RefPtr F n) refs
        (x,f,tf,
         heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
               heap_element)list)) /\
   (!ck conf ts n vs refs f tf heap.
      vs = [] /\
      n < dimword(:A) DIV 16 /\
      ts = 0 ==>
      v_inv_ck ck conf (data_Block ts n vs) refs
        (gc_shared_Data (wl_Word (BlockNil n)),f,tf,
         heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
               heap_element)list)) /\
   (!ck conf ts n vs refs xs ptr f tf heap.
      ~(vs = []) /\
      (~(ck = 0) ==>
       ALL2 (\v x. v_inv_ck (ck - 1) conf v refs (x,f,tf,heap)) vs xs) /\
      FLOOKUP tf ts = SOME ptr /\
      heap_lookup ptr heap = SOME (BlockRep n xs) ==>
      v_inv_ck ck conf (data_Block ts n vs) refs
        (Pointer ptr (wl_Word (ptr_bits conf n (LENGTH xs))),f,tf,
         heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
               heap_element)list))`;;

(* HOL4's names of the rules [~NumberSmall:] ... *)
let v_inv_ck_NumberSmall = el 0 (CONJUNCTS v_inv_ck_rules);;
let v_inv_ck_NumberBig = el 1 (CONJUNCTS v_inv_ck_rules);;
let v_inv_ck_Word64 = el 2 (CONJUNCTS v_inv_ck_rules);;
let v_inv_ck_CodePtr = el 3 (CONJUNCTS v_inv_ck_rules);;
let v_inv_ck_RefPtr = el 4 (CONJUNCTS v_inv_ck_rules);;
let v_inv_ck_RefPtrThunk = el 5 (CONJUNCTS v_inv_ck_rules);;
let v_inv_ck_RefPtrThunkInlined = el 6 (CONJUNCTS v_inv_ck_rules);;
let v_inv_ck_BlockNil = el 7 (CONJUNCTS v_inv_ck_rules);;
let v_inv_ck_BlockCons = el 8 (CONJUNCTS v_inv_ck_rules);;

(* HOL4 line 250 *)
let v_inv_eq = cake_def
  `v_inv conf v refs (x,f,tf,heap) <=>
     !ck. v_inv_ck ck conf v refs
            (x,f,tf,heap:(((A)word_loc,data_to_word_memoryProof_tag#
                           ((A)word_loc)list)heap_element)list)`;;

(* HOL4 line 255 *)
let ThunkBlock_11 = prove
 (`!ev1 (x1:A heap_address) ev2 x2.
     ThunkBlock ev1 x1:(A,data_to_word_memoryProof_tag#B list)heap_element = ThunkBlock ev2 x2 <=>
     ev1 = ev2 /\ x1 = x2`,
  REWRITE_TAC[ThunkBlock_def; injectivity "heap_element"; PAIR_EQ; CONS_11;
              injectivity "data_to_word_memoryProof_tag"] THEN
  MESON_TAC[]);;
let _ = cake_add_simps [ThunkBlock_11];;

(* MP1AUX: the cases of a data_v value *)
let MP1AUX_data_v_nchotomy = CONJUNCT1 (cases "data_v");;

(* MP1AUX: inversion of v_inv_ck for each kind of value (HOL4 uses     *)
(* simp [Once v_inv_ck_cases] for these)                                 *)
let MP1AUX_v_inv_ck_Number = prove
 (`!ck conf i (refs:(data_v bvl_ref)spt) x f tf
    heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
          heap_element)list.
     v_inv_ck ck conf (data_Number i) refs (x,f,tf,heap) <=>
     if small_int (:A) i then x = gc_shared_Data (wl_Word (Smallnum i)) else
       ?ptr. x = Pointer ptr (wl_Word (word 0)) /\
             heap_lookup ptr heap = SOME (Bignum i)`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [v_inv_ck_cases] THEN
  SIMP[PAIR_EQ] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let MP1AUX_v_inv_ck_Word64 = prove
 (`!ck conf w (refs:(data_v bvl_ref)spt) x f tf
    heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
          heap_element)list.
     v_inv_ck ck conf (data_Word64 w) refs (x,f,tf,heap) <=>
     ?ptr. x = Pointer ptr (wl_Word (word 0)) /\
           heap_lookup ptr heap = SOME (Word64Rep (:A) w)`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [v_inv_ck_cases] THEN
  SIMP[PAIR_EQ] THEN MESON_TAC[]);;

let MP1AUX_v_inv_ck_CodePtr = prove
 (`!ck conf n (refs:(data_v bvl_ref)spt) x f tf
    heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
          heap_element)list.
     v_inv_ck ck conf (data_CodePtr n) refs (x,f,tf,heap) <=>
     x = gc_shared_Data (wl_Loc n 0)`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [v_inv_ck_cases] THEN
  SIMP[PAIR_EQ] THEN MESON_TAC[]);;

let MP1AUX_v_inv_ck_RefPtr = prove
 (`!ck conf b n (refs:(data_v bvl_ref)spt) x f tf
    heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
          heap_element)list.
     v_inv_ck ck conf (data_RefPtr b n) refs (x,f,tf,heap) <=>
     (n IN FDOM f /\
      (!ev v. ~(lookup n refs = SOME (bvl_Thunk ev v))) /\
      (!tg fin l c r. lookup n refs = SOME (MutBlock tg fin l c r) ==> ~b) /\
      x = Pointer (FAPPLY f n) (ref_ptr_annot conf (lookup n refs))) \/
     (?ev v y.
         (lookup n refs = SOME (bvl_Thunk ev v) /\
          (ev = Evaluated ==> data_dest_thunk v refs = data_NotThunk) /\
          n IN FDOM f /\
          heap_lookup (FAPPLY f n) heap = SOME (ThunkBlock ev y) /\
          ~b /\
          x = Pointer (FAPPLY f n) (wl_Word (word 0))) /\
         (~(ck = 0) ==> v_inv_ck (ck - 1) conf v refs (y,f,tf,heap))) \/
     (?v. (lookup n refs = SOME (bvl_Thunk Evaluated v) /\
           data_dest_thunk v refs = data_NotThunk /\
           ~b) /\
          (~(ck = 0) ==> v_inv_ck (ck - 1) conf v refs (x,f,tf,heap)))`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [v_inv_ck_cases] THEN
  SIMP[PAIR_EQ] THEN MESON_TAC[]);;

let MP1AUX_v_inv_ck_Block = prove
 (`!ck conf ts n vs (refs:(data_v bvl_ref)spt) x f tf
    heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
          heap_element)list.
     v_inv_ck ck conf (data_Block ts n vs) refs (x,f,tf,heap) <=>
     if vs = []
     then x = gc_shared_Data (wl_Word (BlockNil n)) /\
          n < dimword(:A) DIV 16 /\
          ts = 0
     else
       ?ptr xs.
         (~(ck = 0) ==>
          ALL2 (\v x. v_inv_ck (ck - 1) conf v refs (x,f,tf,heap)) vs xs) /\
         FLOOKUP tf ts = SOME ptr /\
         x = Pointer ptr (wl_Word (ptr_bits conf n (LENGTH xs))) /\
         heap_lookup ptr heap = SOME (BlockRep n xs)`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [v_inv_ck_cases] THEN
  SIMP[PAIR_EQ] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

(* MP1AUX: a theorem whose conclusion has the given head constant *)
let MP1AUX_HEAD c th =
  try fst(dest_const(fst(strip_comb(concl th)))) = c with Failure _ -> false;;

(* HOL4 line 262 *)
let v_inv_ck_mono = prove
 (`!ck conf v refs x f tf
    heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
          heap_element)list.
     v_inv_ck ck conf v refs (x,f,tf,heap) ==>
     !ck'. ck' <= ck ==> v_inv_ck ck' conf v refs (x,f,tf,heap)`,
  INDUCT_TAC THENL [REWRITE_TAC[LE] THEN MESON_TAC[]; ALL_TAC] THEN
  GEN_TAC THEN X_GEN_TAC `v:data_v` THEN
  STRUCT_CASES_TAC(ISPEC `v:data_v` MP1AUX_data_v_nchotomy) THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[MP1AUX_v_inv_ck_Number; MP1AUX_v_inv_ck_Word64;
              MP1AUX_v_inv_ck_CodePtr; MP1AUX_v_inv_ck_RefPtr;
              MP1AUX_v_inv_ck_Block; NOT_SUC; SUC_SUB1] THENL
   [MESON_TAC[];
    MESON_TAC[];
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL [MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `ptr:num` (X_CHOOSE_THEN
      `xs:(((A)word_loc)heap_address)list` STRIP_ASSUME_TAC)) THEN
    REPEAT STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`ptr:num`; `xs:(((A)word_loc)heap_address)list`] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (MP1AUX_HEAD "ALL2")) THEN
    MATCH_MP_TAC MONO_ALL2 THEN REPEAT GEN_TAC THEN BETA_TAC THEN
    ASM_MESON_TAC[ARITH_RULE `ck' <= SUC ck ==> ck' - 1 <= ck`];
    MESON_TAC[];
    ASM_MESON_TAC[ARITH_RULE `ck' <= SUC ck ==> ck' - 1 <= ck`]]);;

(* MP1AUX: two monotone (decreasing) families of conditions *)
let MP1AUX_MONO_DISJ = prove
 (`!a (b:num->bool) (c:num->bool).
     (!k. b (SUC k) ==> b k) /\ (!k. c (SUC k) ==> c k) /\
     (!ck. a \/ b ck \/ c ck) ==> a \/ (!ck. b ck) \/ (!ck. c ck)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "BM")
    (CONJUNCTS_THEN2 (LABEL_TAC "CM") (LABEL_TAC "H"))) THEN
  SUBGOAL_THEN `!j k. j <= k ==> (b:num->bool) k ==> b j` (LABEL_TAC "BT") THENL
   [GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[LE] THENL
     [DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[];
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      DISCH_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[IMP_IMP]) THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "BM" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!j k. j <= k ==> (c:num->bool) k ==> c j` (LABEL_TAC "CT") THENL
   [GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[LE] THENL
     [DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[];
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      DISCH_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[IMP_IMP]) THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "CM" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_CASES_TAC `a:bool` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `!ck. (b:num->bool) ck` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `k1:num` o REWRITE_RULE[NOT_FORALL_THM]) THEN
  X_GEN_TAC `k:num` THEN
  REMOVE_THEN "H" (MP_TAC o SPEC `k + k1:num`) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  ASM_MESON_TAC[ARITH_RULE `k1 <= k + k1:num`; ARITH_RULE `k <= k + k1:num`]);;

(* MP1AUX: the RefPtr clause of v_inv_def *)
let MP1AUX_v_inv_RefPtr = prove
 (`!conf b n (refs:(data_v bvl_ref)spt) x f tf
    heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
          heap_element)list.
     v_inv conf (data_RefPtr b n) refs (x,f,tf,heap) <=>
     (n IN FDOM f /\
      (!ev v. ~(lookup n refs = SOME (bvl_Thunk ev v))) /\
      (!tg fin l c r. lookup n refs = SOME (MutBlock tg fin l c r) ==> ~b) /\
      x = Pointer (FAPPLY f n) (ref_ptr_annot conf (lookup n refs))) \/
     (?ev v y.
         lookup n refs = SOME (bvl_Thunk ev v) /\
         (ev = Evaluated ==> data_dest_thunk v refs = data_NotThunk) /\
         n IN FDOM f /\
         heap_lookup (FAPPLY f n) heap = SOME (ThunkBlock ev y) /\
         v_inv conf v refs (y,f,tf,heap) /\
         ~b /\
         x = Pointer (FAPPLY f n) (wl_Word (word 0))) \/
     (?v. lookup n refs = SOME (bvl_Thunk Evaluated v) /\
          data_dest_thunk v refs = data_NotThunk /\
          ~b /\
          v_inv conf v refs (x,f,tf,heap))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[v_inv_eq; MP1AUX_v_inv_ck_RefPtr] THEN
  EQ_TAC THENL
   [DISCH_TAC THEN
    FIRST_ASSUM(fun th ->
      let ck,body = dest_forall(concl th) in
      let a,bc = dest_disj body in
      let b,c = dest_disj bc in
      MP_TAC(ISPECL [a; mk_abs(ck,b); mk_abs(ck,c)] MP1AUX_MONO_DISJ)) THEN
    BETA_TAC THEN ASM_REWRITE_TAC[NOT_SUC; SUC_SUB1] THEN ANTS_TAC THENL
     [CONJ_TAC THEN GEN_TAC THEN
      MESON_TAC[v_inv_ck_mono; ARITH_RULE `k - 1 <= k`];
      ALL_TAC] THEN
    STRIP_TAC THENL
     [ASM_REWRITE_TAC[];
      DISJ2_TAC THEN DISJ1_TAC THEN
      FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC `0`) THEN
      MAP_EVERY EXISTS_TAC [`ev:thunk_mode`; `v:data_v`;
                            `y:((A)word_loc)heap_address`] THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `k:num` THEN
      FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[NOT_SUC; SUC_SUB1] o
                    SPEC `SUC k`) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
      SUBGOAL_THEN `v':data_v = v /\ y':((A)word_loc)heap_address = y`
        (fun th -> ASM_MESON_TAC[th]) THEN
      ASM_MESON_TAC[option_INJ; injectivity "bvl_ref"; ThunkBlock_11];
      DISJ2_TAC THEN DISJ2_TAC THEN
      FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC `0`) THEN
      EXISTS_TAC `v:data_v` THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `k:num` THEN
      FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[NOT_SUC; SUC_SUB1] o
                    SPEC `SUC k`) THEN
      SUBGOAL_THEN `v':data_v = v` (fun th -> ASM_MESON_TAC[th]) THEN
      ASM_MESON_TAC[option_INJ; injectivity "bvl_ref"]];
    STRIP_TAC THEN GEN_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

(* MP1AUX: the Block clause of v_inv_def *)
let MP1AUX_v_inv_Block = prove
 (`!conf ts n vs (refs:(data_v bvl_ref)spt) x f tf
    heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
          heap_element)list.
     v_inv conf (data_Block ts n vs) refs (x,f,tf,heap) <=>
     if vs = []
     then x = gc_shared_Data (wl_Word (BlockNil n)) /\
          n < dimword(:A) DIV 16 /\
          ts = 0
     else
       ?ptr xs.
         ALL2 (\v x. v_inv conf v refs (x,f,tf,heap)) vs xs /\
         FLOOKUP tf ts = SOME ptr /\
         x = Pointer ptr (wl_Word (ptr_bits conf n (LENGTH xs))) /\
         heap_lookup ptr heap = SOME (BlockRep n xs)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[v_inv_eq; MP1AUX_v_inv_ck_Block] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN EQ_TAC THENL
   [DISCH_TAC THEN FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC `0`) THEN
    MAP_EVERY EXISTS_TAC [`ptr:num`; `xs:(((A)word_loc)heap_address)list`] THEN
    ASM_REWRITE_TAC[LIST_REL_EL_EQN] THEN
    SUBGOAL_THEN
     `!k. ALL2 (\v x. v_inv_ck k conf v refs (x,f,tf,heap)) vs
               (xs:(((A)word_loc)heap_address)list)`
     MP_TAC THENL
     [X_GEN_TAC `k:num` THEN
      FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[NOT_SUC; SUC_SUB1] o
                    SPEC `SUC k`) THEN
      SUBGOAL_THEN `xs':(((A)word_loc)heap_address)list = xs`
        (fun th -> ASM_MESON_TAC[th]) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[BlockRep_def]) THEN
      ASM_MESON_TAC[option_INJ; injectivity "heap_element"];
      REWRITE_TAC[LIST_REL_EL_EQN] THEN MESON_TAC[]];
    STRIP_TAC THEN GEN_TAC THEN
    MAP_EVERY EXISTS_TAC [`ptr:num`; `xs:(((A)word_loc)heap_address)list`] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC
     `ALL2 (\v x. !ck. v_inv_ck ck conf v refs (x,f,tf,heap)) vs
           (xs:(((A)word_loc)heap_address)list)` THEN
    MATCH_MP_TAC MONO_ALL2 THEN SIMP_TAC[]]);;

(* HOL4 line 274 *)
let v_inv_def = prove
 (`(!conf i refs x f tf
     heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
           heap_element)list.
     v_inv conf (data_Number i) (refs:(data_v bvl_ref)spt) (x,f,tf,heap) <=>
     if small_int (:A) i then x = gc_shared_Data (wl_Word (Smallnum i)) else
       ?ptr. x = Pointer ptr (wl_Word (word 0)) /\
             heap_lookup ptr heap = SOME (Bignum i)) /\
   (!conf w refs x f tf
     heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
           heap_element)list.
     v_inv conf (data_Word64 w) refs (x,f,tf,heap) <=>
     ?ptr. x = Pointer ptr (wl_Word (word 0)) /\
           heap_lookup ptr heap = SOME (Word64Rep (:A) w)) /\
   (!conf n refs x f tf
     heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
           heap_element)list.
     v_inv conf (data_CodePtr n) refs (x,f,tf,heap) <=>
     x = gc_shared_Data (wl_Loc n 0)) /\
   (!conf b n refs x f tf
     heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
           heap_element)list.
     v_inv conf (data_RefPtr b n) refs (x,f,tf,heap) <=>
     (n IN FDOM f /\
      (!ev v. ~(lookup n refs = SOME (bvl_Thunk ev v))) /\
      (!tg fin l c r. lookup n refs = SOME (MutBlock tg fin l c r) ==> ~b) /\
      x = Pointer (FAPPLY f n) (ref_ptr_annot conf (lookup n refs))) \/
     (?ev v y.
         lookup n refs = SOME (bvl_Thunk ev v) /\
         (ev = Evaluated ==> data_dest_thunk v refs = data_NotThunk) /\
         n IN FDOM f /\
         heap_lookup (FAPPLY f n) heap = SOME (ThunkBlock ev y) /\
         v_inv conf v refs (y,f,tf,heap) /\
         ~b /\
         x = Pointer (FAPPLY f n) (wl_Word (word 0))) \/
     (?v. lookup n refs = SOME (bvl_Thunk Evaluated v) /\
          data_dest_thunk v refs = data_NotThunk /\
          ~b /\
          v_inv conf v refs (x,f,tf,heap))) /\
   (!conf ts n vs refs x f tf
     heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
           heap_element)list.
     v_inv conf (data_Block ts n vs) refs (x,f,tf,heap) <=>
     if vs = []
     then x = gc_shared_Data (wl_Word (BlockNil n)) /\
          n < dimword(:A) DIV 16 /\
          ts = 0
     else
       ?ptr xs.
         ALL2 (\v x. v_inv conf v refs (x,f,tf,heap)) vs xs /\
         FLOOKUP tf ts = SOME ptr /\
         x = Pointer ptr (wl_Word (ptr_bits conf n (LENGTH xs))) /\
         heap_lookup ptr heap = SOME (BlockRep n xs))`,
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[v_inv_eq; MP1AUX_v_inv_ck_Number];
    REWRITE_TAC[v_inv_eq; MP1AUX_v_inv_ck_Word64];
    REWRITE_TAC[v_inv_eq; MP1AUX_v_inv_ck_CodePtr];
    REWRITE_TAC[MP1AUX_v_inv_RefPtr];
    REWRITE_TAC[MP1AUX_v_inv_Block]]);;

(* HOL4 line 361 *)
let v_inv_RefPtr_T = prove
 (`!conf n refs x f tf
    heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
          heap_element)list.
     v_inv conf (data_RefPtr T n) (refs:(data_v bvl_ref)spt) (x,f,tf,heap) <=>
     n IN FDOM f /\
     (!ev v. ~(lookup n refs = SOME (bvl_Thunk ev v))) /\
     (!tg fin l c r. ~(lookup n refs = SOME (MutBlock tg fin l c r))) /\
     x = Pointer (FAPPLY f n) (wl_Word (word 0))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[v_inv_def] THEN
  SUBGOAL_THEN
   `(!tg fin l c r. ~(lookup n refs = SOME (MutBlock tg fin l c r))) ==>
    ref_ptr_annot conf (lookup n (refs:(data_v bvl_ref)spt)) =
    wl_Word (word 0):(A)word_loc`
   ASSUME_TAC THENL
   [CASES_ON `lookup n (refs:(data_v bvl_ref)spt)` THEN
    REWRITE_TAC[ref_ptr_annot_def] THEN
    SPEC_TAC(`a:data_v bvl_ref`,`a:data_v bvl_ref`) THEN
    MATCH_MP_TAC bvl_ref_INDUCT THEN REWRITE_TAC[ref_ptr_annot_def] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_MESON_TAC[]);;

(* HOL4 line 375 *)
let MEM_IMP_v_size = prove
 (`!l a. MEM a l ==> data_v_size a < 1 + list_size data_v_size l`,
  MESON_TAC[MEM_LIST_SIZE; ARITH_RULE `a < b ==> a < 1 + b`]);;

(* HOL4 line 383 *)
let get_refs_def = cake_def_wf
  `measure data_v_size` TERM_TAC
  `(get_refs (data_Number _) = []) /\
   (get_refs (data_Word64 _) = []) /\
   (get_refs (data_CodePtr _) = []) /\
   (get_refs (data_RefPtr _ p) = [p]) /\
   (get_refs (data_Block _ _ vs) = FLAT (MAP get_refs vs))`;;
let get_refs_ind = cake_ind "get_refs";;

(* HOL4 line 394 *)
let ref_edge_def = cake_def
  `ref_edge refs x res <=>
     match lookup x refs with
       SOME (bvl_ValueArray ys) -> MEM res (get_refs (data_Block 0 ARB ys))
     | SOME (bvl_Thunk _ v) -> MEM res (get_refs (data_Block 0 ARB [v]))
     | SOME (MutBlock _ _ l c r) ->
         MEM res (get_refs (data_Block 0 ARB (APPEND (APPEND l [c]) r)))
     | _ -> F`;;

(* HOL4 line 403 *)
let reachable_refs_def = cake_def
  `reachable_refs roots refs t <=>
     ?x r. MEM x roots /\ MEM r (get_refs x) /\ RTC (ref_edge refs) r t`;;

(* HOL4 line 408 *)
let RefBlock_def = cake_def
  `RefBlock (xs:(A heap_address)list) =
     DataElement xs (LENGTH xs) (RefTag,[]:B list)`;;

(* HOL4 line 412 *)
let dest_evaluated_thunk_rel_rules,dest_evaluated_thunk_rel_ind,
    dest_evaluated_thunk_rel_cases,dest_evaluated_thunk_rel_strongind =
  cake_inductive
  `!x:A heap_address.
     dest_evaluated_thunk_rel (ThunkBlock Evaluated x:(A,data_to_word_memoryProof_tag#B list)heap_element) x`;;

(* HOL4 line 416 *)
let bc_ref_inv_def = cake_def
  `bc_ref_inv conf n refs (f,tf,heap,be) <=>
     match (FLOOKUP f n, lookup n refs) with
       (SOME x, SOME (bvl_ValueArray ys)) ->
         (?zs. heap_lookup x heap = SOME (RefBlock zs) /\
               ALL2 (\z y. v_inv conf y refs (z,f,tf,heap)) zs ys)
     | (SOME x, SOME (bvl_ByteArray flag bs)) ->
         (let ws = LENGTH bs DIV (dimindex (:A) DIV 8) + 1 in
          heap_lookup x heap =
            SOME (Bytes be flag bs (REPLICATE ws (word 0:A word))))
     | (SOME x, SOME (bvl_Thunk ev v)) ->
         (?z:(A word_loc)heap_address.
            heap_lookup x heap = SOME (ThunkBlock ev z) /\
            (ev = Evaluated ==> data_dest_thunk v refs = data_NotThunk) /\
            v_inv conf v refs (z,f,tf,heap))
     | (SOME x, SOME (MutBlock tg fin l c r)) ->
         (!gs. ~(data_to_word_config_gc_kind conf = Generational gs)) /\
         (~fin ==> ~(x IN IMAGE (FAPPLY tf) (FDOM tf))) /\
         (?zs. heap_lookup x heap = SOME (BlockRep tg zs) /\
               ALL2 (\z y. v_inv conf y refs (z,f,tf,heap)) zs
                    (APPEND (APPEND l [c]) r))
     | _ -> F`;;

(* HOL4 line 448 *)
let v_all_ts_def = cake_def_wf
  `measure data_v_size` TERM_TAC
  `v_all_ts (data_Block ts _ xs) = CONS ts (FLAT (MAP v_all_ts xs)) /\
   v_all_ts _ = []`;;
let v_all_ts_ind = cake_ind "v_all_ts";;

(* HOL4 line 456 *)
let find_ref_def = cake_def
  `(find_ref (bvl_ValueArray l) (x:A) <=> MEM x l) /\
   (find_ref (bvl_Thunk m v) x <=> v = x) /\
   (find_ref (MutBlock tg fin l c r) x <=> MEM x (APPEND (APPEND l [c]) r)) /\
   (find_ref _ _ <=> F)`;;
let _ = cake_add_simps [find_ref_def];;

(* HOL4 line 464 *)
let all_ts_def = cake_def
  `all_ts refs stack =
     let refs_v = {x | ?n r. lookup n refs = SOME r /\ find_ref r x} in
     {ts | ?x. (x IN refs_v \/ MEM x stack) /\ MEM ts (v_all_ts x)}`;;

(* HOL4 line 470 *)
let be_ok_def = cake_def
  `be_ok (b1:bool) b2 <=> b1 = b2`;;

(* HOL4 line 474 *)
let v_all_vs_def = cake_def
  `v_all_vs (CONS (data_Block ts tag l) xs) =
     APPEND (CONS (data_Block ts tag l) (v_all_vs l)) (v_all_vs xs) /\
   v_all_vs (CONS x xs) = CONS x (v_all_vs xs) /\
   v_all_vs [] = []`;;
let v_all_vs_ind = cake_ind "v_all_vs";;

(* HOL4 line 480 *)
let all_vs_def = cake_def
  `all_vs refs stack =
     {v | ?(n:num) l. lookup n refs = SOME (bvl_ValueArray l) /\
                      MEM v (v_all_vs l)} UNION
     {v | ?n ev x. lookup n refs = SOME (bvl_Thunk ev x) /\
                   MEM v (v_all_vs [x])} UNION
     {v | ?n tg fin l c r. lookup n refs = SOME (MutBlock tg fin l c r) /\
                           MEM v (v_all_vs (APPEND (APPEND l [c]) r))} UNION
     {v | MEM v (v_all_vs stack)}`;;

(* HOL4 line 489 *)
let blocks_unique_def = cake_def
  `blocks_unique ts vs <=>
     !t a1 xs1 a2 xs2.
       data_Block t a1 xs1 IN vs /\ ~(xs1 = []) /\
       data_Block t a2 xs2 IN vs /\ ~(xs2 = []) ==>
       a1 = a2 /\ xs1 = xs2 /\ t < ts`;;

(* HOL4 line 498 *)
let bc_stack_ref_inv_def = cake_def
  `bc_stack_ref_inv conf ts stack refs
     (roots, heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
                   heap_element)list, be) <=>
     ?f tf.
       INJ (FAPPLY f) (FDOM f) {a | isSomeDataElement (heap_lookup a heap)} /\
       FDOM f SUBSET (domain refs) /\
       INJ (FAPPLY tf) (FDOM tf) {a | isSomeDataElement (heap_lookup a heap)} /\
       FDOM tf SUBSET (all_ts refs stack) /\
       FDOM tf SUBSET {n | n < ts} /\ be_ok (data_to_word_config_be conf) be /\
       blocks_unique ts (all_vs refs stack) /\
       ALL2 (\v x. v_inv conf v refs (x,f,tf,heap)) stack roots /\
       !n. reachable_refs stack refs n /\ n IN FDOM f ==>
           bc_ref_inv conf n refs (f,tf,heap,be)`;;

(* HOL4 line 514 *)
let data_up_to_def = cake_def
  `data_up_to a (heap:((A,B)heap_element)list) <=>
     ?h1 h2. heap_split a heap = SOME (h1,h2) /\ ALL isDataElement h1`;;

(* HOL4 line 519 *)
let unused_space_inv_def = cake_def
  `unused_space_inv ptr l (heap:((A,B)heap_element)list) <=>
     (~(l = 0) ==> heap_lookup ptr heap = SOME (Unused (l - 1))) /\
     ptr + l <= heap_length heap /\
     data_up_to ptr heap`;;

(* HOL4 line 526 *)
let isMutTag_def = cake_def
  `isMutTag t <=> t = RefTag \/ ?ev. t = ThunkTag ev`;;

(* HOL4 line 530 *)
let isRef_def = cake_def
  `(isRef (DataElement ys l (tag,qs):(A,data_to_word_memoryProof_tag#B)
                                      heap_element) <=> isMutTag tag) /\
   (isRef (_:(A,data_to_word_memoryProof_tag#B)heap_element) <=> F)`;;

(* HOL4 line 535 *)
let gen_start_ok_def = cake_def
  `gen_start_ok (heap:((A,B)heap_element)list) refs_start gen_start <=>
     ?h1 h2.
       heap_split gen_start heap = SOME (h1,h2) /\
       !xs l d p e.
         MEM (DataElement xs l d) h1 /\ MEM (Pointer p e) xs ==>
         p < gen_start \/ refs_start <= p`;;

(* HOL4 line 544 *)
let gen_state_ok_def = cake_def
  `gen_state_ok a refs_start (heap:((A,B)heap_element)list)
     (GenState _ starts) <=>
     ALL (\s. s <= a) starts /\
     ALL (gen_start_ok heap refs_start) starts`;;

(* HOL4 line 550 *)
let gc_kind_inv_def = cake_def
  `gc_kind_inv c a sp sp1 (gens:gen_state)
     (heap:((A,data_to_word_memoryProof_tag#B)heap_element)list) <=>
     match data_to_word_config_gc_kind c with
       data_to_word_None -> sp1 = 0
     | data_to_word_Simple -> sp1 = 0
     | Generational sizes ->
         gen_state_ok a (a + sp + sp1) heap gens /\
         ?h1 h2. heap_split (a + sp + sp1) heap = SOME (h1,h2) /\
                 ALL (\x. ~isRef x) h1 /\ ALL isRef h2`;;

(* HOL4 line 561 *)
let abs_ml_inv_def = cake_def
  `abs_ml_inv conf stack refs (roots,heap,be,a,sp,sp1,gens) limit ts <=>
     roots_ok roots heap /\ heap_ok heap limit /\
     gc_kind_inv conf a sp sp1 gens heap /\
     unused_space_inv a (sp + sp1) heap /\
     bc_stack_ref_inv conf ts stack refs
       (roots,heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
                    heap_element)list,be)`;;

(* HOL4 line 573 *)
let word_list_limit = prove
 (`!ws:((A)word_loc)list.
     ALL isWord ws /\ ALL_DISTINCT ws ==> LENGTH ws <= dimword(:A)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o MATCH_MP ALL_DISTINCT_CARD_LIST_TO_SET) THEN
  SUBGOAL_THEN
   `CARD (set_of_list (ws:((A)word_loc)list)) =
    CARD (IMAGE (\x:(A)word_loc. val (theWord x)) (set_of_list ws))`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN
    REWRITE_TAC[FINITE_SET_OF_LIST; IN_SET_OF_LIST] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_MEM; isWord_exists]) THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `?a b. (x:(A)word_loc) = wl_Word (a:A word) /\ (y:(A)word_loc) = wl_Word b`
      STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[theWord_def; VAL_EQ]) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[theWord_def; VAL_EQ];
    TRANS_TAC LE_TRANS `CARD {m:num | m < dimword(:A)}` THEN CONJ_TAC THENL
     [MATCH_MP_TAC CARD_SUBSET THEN
      REWRITE_TAC[FINITE_NUMSEG_LT; SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      REWRITE_TAC[dimword_def; VAL_BOUND];
      REWRITE_TAC[CARD_NUMSEG_LT; LE_REFL]]]);;

(* HOL4 line 594 *)
let MOD_EQ_0_0 = prove
 (`!n b. 0 < b ==> (n MOD b = 0) ==> n < b ==> (n = 0)`,
  REPEAT STRIP_TAC THEN ASM_MESON_TAC[MOD_LT]);;

(* HOL4 line 600 *)
let EVERY2_IMP_EVERY = prove
 (`!(P:A->B->bool) xs ys.
     ALL2 P xs ys ==> ALL (\(x,y). P y x) (ZIP ys xs)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[ALL2; ZIP; ALL; HD; TL] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN ASM_MESON_TAC[]);;

(* HOL4 line 606 *)
let EVERY2_IMP_EVERY2 = prove
 (`!xs ys (P1:A->B->bool) P2.
     (!x y. MEM x xs /\ MEM y ys /\ P1 x y ==> P2 x y) ==>
     ALL2 P1 xs ys ==> ALL2 P2 xs ys`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[ALL2; MEM] THEN
  ASM_MESON_TAC[]);;

(* HOL4 line 615 *)
let MEM_EVERY2_IMP = prove
 (`!l (x:A) zs (P:B->A->bool). MEM x l /\ ALL2 P zs l ==> ?z. MEM z zs /\ P z x`,
  LIST_INDUCT_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[ALL2; MEM] THEN ASM_MESON_TAC[]);;

(* HOL4 lines 621-622 (val): EVERY2_LENGTH is bound in hol4/list.ml (the  *)
(* statement of HOL4's LIST_REL_LENGTH)                                     *)
let EVERY2_IMP_LENGTH = EVERY2_LENGTH;;

(* HOL4 line 624 *)
let EVERY2_APPEND_CONS = prove
 (`!xs (y:A) ys zs (P:A->B->bool).
     ALL2 P (APPEND xs (CONS y ys)) zs ==>
     ?t1 t t2. zs = APPEND t1 (CONS t t2) /\ LENGTH t1 = LENGTH xs /\
               ALL2 P xs t1 /\ P y t /\ ALL2 P ys t2`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `zs:B list` list_CASES) THEN
  REWRITE_TAC[APPEND; ALL2] THENL
   [STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`[]:B list`; `h:B`; `t:B list`] THEN
    ASM_REWRITE_TAC[APPEND; LENGTH; ALL2];
    STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`y:A`; `ys:A list`; `t':B list`;
                                  `P:A->B->bool`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `u1:B list` (X_CHOOSE_THEN `u:B`
      (X_CHOOSE_THEN `u2:B list` STRIP_ASSUME_TAC))) THEN
    MAP_EVERY EXISTS_TAC [`CONS (h':B) u1`; `u:B`; `u2:B list`] THEN
    ASM_REWRITE_TAC[APPEND; LENGTH; ALL2]]);;

(* HOL4 line 637 *)
let EVERY2_SWAP = prove
 (`!(P:A->B->bool) xs ys. ALL2 P xs ys ==> ALL2 (\y x. P x y) ys xs`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[ALL2] THEN ASM_MESON_TAC[]);;

(* HOL4 line 643 *)
let EVERY2_APPEND_IMP_APPEND = prove
 (`!xs1 xs2 ys (P:A->B->bool).
     ALL2 P (APPEND xs1 xs2) ys ==>
     ?ys1 ys2. ys = APPEND ys1 ys2 /\ ALL2 P xs1 ys1 /\ ALL2 P xs2 ys2`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[APPEND] THENL
   [STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`[]:B list`; `ys:B list`] THEN
    ASM_REWRITE_TAC[APPEND; ALL2];
    STRUCT_CASES_TAC(ISPEC `ys:B list` list_CASES) THEN REWRITE_TAC[ALL2] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`xs2:A list`; `t':B list`; `P:A->B->bool`]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`CONS (h':B) ys1`; `ys2:B list`] THEN
    ASM_REWRITE_TAC[APPEND; ALL2]]);;

(* HOL4 lines 654-659 (val) *)
let EVERY2_IMP_APPEND = EVERY2_APPEND_suff;;
let IMP_EVERY2_APPEND = EVERY2_IMP_APPEND;;
let EVERY2_EQ_EL = LIST_REL_EL_EQN;;

let EVERY2_IMP_EL = prove
 (`!xs ys (P:A->B->bool).
     ALL2 P xs ys ==> !n. n < LENGTH ys ==> P (EL n xs) (EL n ys)`,
  MESON_TAC[EVERY2_EQ_EL]);;

(* HOL4 line 662 *)
let EVERY2_MAP_FST_SND = prove
 (`!(P:A->B->bool) xs.
     ALL2 P (MAP FST xs) (MAP SND xs) <=> ALL (\(x,y). P x y) xs`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; ALL2; ALL] THEN
  POP_ASSUM(SUBST1_TAC) THEN
  SPEC_TAC(`h:A#B`,`h:A#B`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[]);;

(* HOL4 line 668 *)
let fapply_fupdate_update = prove
 (`!(f:(A,B)fmap) p. FAPPLY (f |+ p) = (FST p =+ SND p) (FAPPLY f)`,
  GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM; FUN_EQ_THM; FAPPLY_FUPDATE_THM;
                          APPLY_UPDATE_THM] THEN
  MESON_TAC[]);;

(* HOL4 line 675 *)
let heap_lookup_APPEND1 = prove
 (`!h1 z (h2:((A,B)heap_element)list).
     heap_length h1 <= z ==>
     heap_lookup z (APPEND h1 h2) = heap_lookup (z - heap_length h1) h2`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NOT_LESS_IMP_heap_lookup THEN
  ASM_ARITH_TAC);;

(* HOL4 line 684 *)
let heap_lookup_APPEND2 = prove
 (`!h1 z (h2:((A,B)heap_element)list).
     z < heap_length h1 ==>
     heap_lookup z (APPEND h1 h2) = heap_lookup z h1`,
  REWRITE_TAC[gc_shared_LESS_IMP_heap_lookup]);;

(* HOL4 line 693: heap_lookup_APPEND *)
let data_to_word_memoryProof_heap_lookup_APPEND = prove
 (`!a h1 (h2:((A,B)heap_element)list).
     heap_lookup a (APPEND h1 h2) =
     if a < heap_length h1 then heap_lookup a h1
     else heap_lookup (a - heap_length h1) h2`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[gc_shared_LESS_IMP_heap_lookup; NOT_LESS_IMP_heap_lookup]);;

(* HOL4 line 705: LENGTH_ADDR_MAP *)
let data_to_word_memoryProof_LENGTH_ADDR_MAP = prove
 (`!(xs:(A heap_address)list) f. LENGTH (ADDR_MAP f xs) = LENGTH xs`,
  REWRITE_TAC[GSYM ADDR_MAP_LENGTH]);;

(* HOL4 line 711 *)
let EL_ADDR_MAP = prove
 (`!(xs:(A heap_address)list) n f.
     n < LENGTH xs ==> EL n (ADDR_MAP f xs) = ADDR_APPLY f (EL n xs)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; CONJUNCT1 LT] THEN
  INDUCT_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `h:A heap_address` (cases "heap_address")) THEN
  ASM_SIMP_TAC[ADDR_MAP_def; ADDR_APPLY_def; EL; HD; TL; LT_SUC; LT_0]);;

let _ = cake_add_simps [LIST_REL_def];;

(* HOL4 line 721 *)
let evaluated_thunk_ptr_def = cake_def
  `evaluated_thunk_ptr refs n <=>
     ?v:data_v. lookup n refs = SOME (bvl_Thunk Evaluated v)`;;

(* HOL4 line 725 (val v_ind: the induction theorem of data_v with EVERY P  *)
(* for the payload of a block; prefixed: closProps binds v_ind)             *)
let data_to_word_memoryProof_v_ind = prove
 (`!P. (!i. P (data_Number i)) /\ (!w. P (data_Word64 w)) /\
       (!ts n l. ALL P l ==> P (data_Block ts n l)) /\
       (!n. P (data_CodePtr n)) /\ (!b n. P (data_RefPtr b n))
       ==> !v. P v`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`P:data_v->bool`; `ALL (P:data_v->bool)`] data_v_INDUCT) THEN
  ASM_SIMP_TAC[ALL] THEN MESON_TAC[]);;

(* MP1AUX: the domain and values of a composition of finite maps *)
let MP1AUX_f_o_f = prove
 (`!(g:(B,C)fmap) (f:(A,B)fmap) x.
     (x IN FDOM (g f_o_f f) <=> x IN FDOM f /\ FAPPLY f x IN FDOM g) /\
     (x IN FDOM (g f_o_f f) ==> FAPPLY (g f_o_f f) x = FAPPLY g (FAPPLY f x))`,
  REPEAT GEN_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[f_o_f_DEF; IN_INTER; IN_ELIM_THM]; MESON_TAC[f_o_f_DEF]]);;

(* MP1AUX: gc_related moves a heap element without pointers unchanged *)
let MP1AUX_gc_related_nil = prove
 (`!(g:(num,num)fmap) (heap1:((A,B)heap_element)list) heap2 ptr x.
     gc_related g heap1 heap2 /\ ptr IN FDOM g /\
     heap_lookup ptr heap1 = SOME x /\ (?l d. x = DataElement [] l d) ==>
     heap_lookup (FAPPLY g ptr) heap2 = SOME x`,
  REWRITE_TAC[gc_related_def] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_MESON_TAC[ADDR_MAP_def]);;

(* MP1AUX: what gc_related says about one data element *)
let MP1AUX_gc_related_lookup = prove
 (`!(g:(num,num)fmap) (heap1:((A,B)heap_element)list) heap2 i xs l d.
     gc_related g heap1 heap2 /\ i IN FDOM g /\
     heap_lookup i heap1 = SOME (DataElement xs l d) ==>
     heap_lookup (FAPPLY g i) heap2 =
       SOME (DataElement (ADDR_MAP (FAPPLY g) xs) l d) /\
     (!ptr u. MEM (Pointer ptr u) xs ==> ptr IN FDOM g)`,
  REWRITE_TAC[gc_related_def] THEN MESON_TAC[]);;

(* MP1AUX: ADDR_MAP of a one element list *)
let MP1AUX_ADDR_MAP_SING = prove
 (`!(g:num->num) (x:A heap_address). ADDR_MAP g [x] = [ADDR_APPLY g x]`,
  GEN_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `x:A heap_address` (cases "heap_address")) THEN
  REWRITE_TAC[ADDR_MAP_def; ADDR_APPLY_def]);;

(* MP1AUX: Bignum and Word64Rep elements have no pointers *)
let MP1AUX_Bignum_nil = prove
 (`!i. ?l d. Bignum i:((A)word_loc,data_to_word_memoryProof_tag#
                       ((A)word_loc)list)heap_element = DataElement [] l d`,
  GEN_TAC THEN REWRITE_TAC[data_to_word_memoryProof_Bignum_def] THEN
  MP_TAC(ISPEC `i2mw i:bool#(A word)list` PAIR_SURJECTIVE) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN SIMP[] THEN MESON_TAC[]);;

let MP1AUX_Word64Rep_nil = prove
 (`!w:int64. ?l d. Word64Rep (:A) w = DataElement [] l d`,
  MESON_TAC[Word64Rep_DataElement]);;

(* MP1AUX: a Bytes element has no pointers *)
let MP1AUX_Bytes_nil = prove
 (`!be flag bs (ws:(A word)list).
     ?l d. Bytes be flag bs ws:((A)word_loc,data_to_word_memoryProof_tag#
                                ((A)word_loc)list)heap_element =
           DataElement [] l d`,
  REWRITE_TAC[data_to_word_memoryProof_Bytes_def; LET_DEF; LET_END_DEF] THEN
  MESON_TAC[]);;

(* MP1AUX: FLOOKUP of a composition of finite maps *)
let MP1AUX_FLOOKUP_f_o_f = prove
 (`!(g:(B,C)fmap) (f:(A,B)fmap) x y.
     FLOOKUP f x = SOME y /\ y IN FDOM g ==> FLOOKUP (g f_o_f f) x = SOME (FAPPLY g y)`,
  REWRITE_TAC[flookup_thm] THEN MESON_TAC[MP1AUX_f_o_f]);;

(* MP1AUX: the get_refs half of v_inv_related_lemma (HOL4 proves both halves in one induction) *)
let MP1AUX_v_inv_related_get_refs = prove
 (`!conf (g:(num,num)fmap)
    (heap2:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
            heap_element)list) w refs x f tf heap1.
     v_inv conf w refs (x,f,tf,heap1) /\ gc_related g heap1 heap2 /\
     (!ptr u. x = Pointer ptr u ==> ptr IN FDOM g) ==>
     ALL (\n. ~(n IN evaluated_thunk_ptr refs) ==> FAPPLY f n IN FDOM g)
         (get_refs w)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  MATCH_MP_TAC data_to_word_memoryProof_v_ind THEN
  REWRITE_TAC[get_refs_def; ALL] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`ts:num`; `n:num`; `l:data_v list`] THEN DISCH_TAC THEN
    REPEAT GEN_TAC THEN REWRITE_TAC[MP1AUX_v_inv_Block] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[MAP; FLAT; ALL] THEN
    STRIP_TAC THEN REWRITE_TAC[EVERY_FLAT; EVERY_MAP; EVERY_MEM] THEN
    X_GEN_TAC `v:data_v` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`l:data_v list`; `xs:(((A)word_loc)heap_address)list`;
      `\v x. v_inv conf v refs (x,f,tf,heap1:(((A)word_loc,data_to_word_memoryProof_tag#
              ((A)word_loc)list)heap_element)list)`; `v:data_v`] LIST_REL_MEM_IMP) THEN
    ASM_REWRITE_TAC[] THEN BETA_TAC THEN
    DISCH_THEN(X_CHOOSE_THEN `y:((A)word_loc)heap_address` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `v:data_v` o REWRITE_RULE[GSYM ALL_MEM]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`y:((A)word_loc)heap_address`; `tf:(num,num)fmap`;
      `heap1:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
              heap_element)list`] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [gc_related_def]) THEN
    STRIP_TAC THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`ptr:num`; `xs:(((A)word_loc)heap_address)list`;
      `LENGTH (xs:(((A)word_loc)heap_address)list)`;
      `(BlockTag n,[]:((A)word_loc)list)`]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[BlockRep_def]) THEN ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_MESON_TAC[];
    REPEAT GEN_TAC THEN REWRITE_TAC[MP1AUX_v_inv_RefPtr] THEN
    REWRITE_TAC[IN; evaluated_thunk_ptr_def] THEN
    STRIP_TAC THEN ASM_MESON_TAC[]]);;

(* MP1AUX: the v_inv_ck half of v_inv_related_lemma *)
let MP1AUX_v_inv_related_ck = prove
 (`!conf (g:(num,num)fmap)
    (heap2:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
            heap_element)list) ck w refs x f tf heap1.
     v_inv conf w refs (x,f,tf,heap1) /\
     gc_related g heap1 heap2 /\
     (!ptr u. x = Pointer ptr u ==> ptr IN FDOM g) ==>
     v_inv_ck ck conf w refs (ADDR_APPLY (FAPPLY g) x,g f_o_f f,g f_o_f tf,heap2)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC num_WF THEN
  X_GEN_TAC `ck:num` THEN DISCH_THEN(LABEL_TAC "IH") THEN X_GEN_TAC `w:data_v` THEN
  STRUCT_CASES_TAC(ISPEC `w:data_v` MP1AUX_data_v_nchotomy) THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[v_inv_def; MP1AUX_v_inv_ck_Number; MP1AUX_v_inv_ck_Word64;
              MP1AUX_v_inv_ck_CodePtr; MP1AUX_v_inv_ck_RefPtr;
              MP1AUX_v_inv_ck_Block] THENL
   [(* Number *)
    COND_CASES_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[ADDR_APPLY_def] THEN
    EXISTS_TAC `FAPPLY (g:(num,num)fmap) ptr` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC MP1AUX_gc_related_nil THEN
    EXISTS_TAC `heap1:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
                       heap_element)list` THEN
    ASM_MESON_TAC[MP1AUX_Bignum_nil];
    (* Word64 *)
    STRIP_TAC THEN ASM_REWRITE_TAC[ADDR_APPLY_def] THEN
    EXISTS_TAC `FAPPLY (g:(num,num)fmap) ptr` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC MP1AUX_gc_related_nil THEN
    EXISTS_TAC `heap1:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
                       heap_element)list` THEN
    ASM_MESON_TAC[MP1AUX_Word64Rep_nil];
    (* Block *)
    COND_CASES_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[ADDR_APPLY_def] THEN
    MP_TAC(ISPECL [`g:(num,num)fmap`;
      `heap1:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
              heap_element)list`;
      `heap2:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
              heap_element)list`;
      `ptr:num`; `xs:(((A)word_loc)heap_address)list`;
      `LENGTH (xs:(((A)word_loc)heap_address)list)`;
      `(BlockTag a1,[]:((A)word_loc)list)`] MP1AUX_gc_related_lookup) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[BlockRep_def]) THEN ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC] THEN
    MAP_EVERY EXISTS_TAC [`FAPPLY (g:(num,num)fmap) ptr`;
      `ADDR_MAP (FAPPLY (g:(num,num)fmap)) (xs:(((A)word_loc)heap_address)list)`] THEN
    ASM_REWRITE_TAC[BlockRep_def; GSYM ADDR_MAP_LENGTH] THEN
    CONJ_TAC THENL
     [ALL_TAC; MATCH_MP_TAC MP1AUX_FLOOKUP_f_o_f THEN ASM_MESON_TAC[]] THEN
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (MP1AUX_HEAD "ALL2")) THEN
    REWRITE_TAC[LIST_REL_EL_EQN; GSYM ADDR_MAP_LENGTH] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `i < LENGTH (xs:(((A)word_loc)heap_address)list)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[EL_ADDR_MAP] THEN BETA_TAC THEN
    USE_THEN "IH" (MP_TAC o SPEC `ck - 1`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN MATCH_MP_TAC] THEN
    EXISTS_TAC `heap1:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
                       heap_element)list` THEN
    ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_MESON_TAC[MEM_EL];
    (* CodePtr *)
    STRIP_TAC THEN ASM_REWRITE_TAC[ADDR_APPLY_def];
    (* RefPtr *)
    DISCH_THEN(CONJUNCTS_THEN2
      (DISJ_CASES_THEN2 STRIP_ASSUME_TAC
        (DISJ_CASES_THEN2 STRIP_ASSUME_TAC STRIP_ASSUME_TAC))
      (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THENL
     [SUBGOAL_THEN `FAPPLY (f:(num,num)fmap) a1 IN FDOM (g:(num,num)fmap)`
        ASSUME_TAC THENL
       [UNDISCH_TAC `!ptr (u:(A)word_loc). (x:((A)word_loc)heap_address) =
                       Pointer ptr u ==> ptr IN FDOM (g:(num,num)fmap)` THEN
        ASM_REWRITE_TAC[injectivity "heap_address"] THEN MESON_TAC[];
        ALL_TAC] THEN
      DISJ1_TAC THEN ASM_SIMP_TAC[MP1AUX_f_o_f; ADDR_APPLY_def] THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `FAPPLY (f:(num,num)fmap) a1 IN FDOM (g:(num,num)fmap)`
        ASSUME_TAC THENL
       [UNDISCH_TAC `!ptr (u:(A)word_loc). (x:((A)word_loc)heap_address) =
                       Pointer ptr u ==> ptr IN FDOM (g:(num,num)fmap)` THEN
        ASM_REWRITE_TAC[injectivity "heap_address"] THEN MESON_TAC[];
        ALL_TAC] THEN
      DISJ2_TAC THEN DISJ1_TAC THEN
      MP_TAC(ISPECL [`g:(num,num)fmap`;
        `heap1:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
                heap_element)list`;
        `heap2:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
                heap_element)list`;
        `FAPPLY (f:(num,num)fmap) a1`; `[y:((A)word_loc)heap_address]`; `1`;
        `(ThunkTag ev,[]:((A)word_loc)list)`] MP1AUX_gc_related_lookup) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ThunkBlock_def]) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[MP1AUX_ADDR_MAP_SING; MEM] THEN STRIP_TAC THEN
      MAP_EVERY EXISTS_TAC [`ev:thunk_mode`; `v:data_v`;
        `ADDR_APPLY (FAPPLY (g:(num,num)fmap)) (y:((A)word_loc)heap_address)`] THEN
      ASM_SIMP_TAC[MP1AUX_f_o_f; ADDR_APPLY_def; ThunkBlock_def] THEN
      DISCH_TAC THEN USE_THEN "IH" (MP_TAC o SPEC `ck - 1`) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN MATCH_MP_TAC] THEN
      EXISTS_TAC `heap1:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
                         heap_element)list` THEN
      ASM_SIMP_TAC[] THEN ASM_MESON_TAC[];
      DISJ2_TAC THEN DISJ2_TAC THEN EXISTS_TAC `v:data_v` THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_TAC THEN USE_THEN "IH" (MP_TAC o SPEC `ck - 1`) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN MATCH_MP_TAC] THEN
      EXISTS_TAC `heap1:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
                         heap_element)list` THEN
      ASM_REWRITE_TAC[]]]);;

(* HOL4 line 732 *)
let v_inv_related_lemma = prove
 (`!conf g heap2 ck w refs x f tf heap1.
     v_inv conf w refs (x,f,tf,heap1) /\
     gc_related g heap1
       (heap2:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
               heap_element)list) /\
     (!ptr u. x = Pointer ptr u ==> ptr IN FDOM g) ==>
     v_inv_ck ck conf w refs (ADDR_APPLY (FAPPLY g) x,g f_o_f f,g f_o_f tf,heap2) /\
     ALL (\n. ~(n IN evaluated_thunk_ptr refs) ==> FAPPLY f n IN FDOM g)
         (get_refs w)`,
  MESON_TAC[MP1AUX_v_inv_related_ck; MP1AUX_v_inv_related_get_refs]);;

(* HOL4 line 822 *)
let v_inv_related = prove
 (`!conf g heap1 heap2 refs w x f tf.
     gc_related g heap1
       (heap2:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
               heap_element)list) /\
     (!ptr u. x = Pointer ptr u ==> ptr IN FDOM g) /\
     v_inv conf w refs (x,f,tf,heap1) ==>
     v_inv conf w refs (ADDR_APPLY (FAPPLY g) x,g f_o_f f,g f_o_f tf,heap2) /\
     ALL (\n. ~(n IN evaluated_thunk_ptr refs) ==> FAPPLY f n IN FDOM g)
         (get_refs w)`,
  REWRITE_TAC[v_inv_eq] THEN MESON_TAC[v_inv_eq; v_inv_related_lemma]);;

(* MP1AUX: the first half of v_inv_related *)
let MP1AUX_v_inv_related1 = prove
 (`!conf (g:(num,num)fmap) heap1
    (heap2:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
            heap_element)list) refs w x f tf.
     gc_related g heap1 heap2 /\
     (!ptr u. x = Pointer ptr u ==> ptr IN FDOM g) /\
     v_inv conf w refs (x,f,tf,heap1) ==>
     v_inv conf w refs (ADDR_APPLY (FAPPLY g) x,g f_o_f f,g f_o_f tf,heap2)`,
  MESON_TAC[v_inv_related]);;

(* HOL4 line 834 *)
let EVERY2_ADDR_MAP = prove
 (`!(P:A heap_address->B->bool) g zs l.
     ALL2 P (ADDR_MAP g zs) l <=> ALL2 (\x y. P (ADDR_APPLY g x) y) zs l`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[ADDR_MAP_def; ALL2_DEF];
    STRUCT_CASES_TAC(ISPEC `h:A heap_address` (cases "heap_address")) THEN
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ADDR_MAP_def; ALL2; ADDR_APPLY_def]]);;

(* MP1AUX: the payload of a moved block satisfies v_inv after the gc *)
let MP1AUX_ALL2_v_inv_related = prove
 (`!conf (g:(num,num)fmap) heap1
    (heap2:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
            heap_element)list) refs f tf zs ys.
     gc_related g heap1 heap2 /\
     (!ptr u. MEM (Pointer ptr u) zs ==> ptr IN FDOM g) /\
     ALL2 (\z y. v_inv conf y refs (z,f,tf,heap1)) zs ys ==>
     ALL2 (\z y. v_inv conf y refs (z,g f_o_f f,g f_o_f tf,heap2))
          (ADDR_MAP (FAPPLY g) zs) ys`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EVERY2_ADDR_MAP] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_comb o concl)) THEN
  MATCH_MP_TAC EVERY2_IMP_EVERY2 THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC MP1AUX_v_inv_related1 THEN
  EXISTS_TAC `heap1:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
                     heap_element)list` THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* HOL4 line 843 *)
let bc_ref_inv_related = prove
 (`!g heap1 heap2 conf n refs f tf be.
     gc_related g heap1
       (heap2:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
               heap_element)list) /\
     bc_ref_inv conf n refs (f,tf,heap1,be) /\ FAPPLY f n IN FDOM g ==>
     bc_ref_inv conf n refs (g f_o_f f,g f_o_f tf,heap2,be)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `n IN FDOM (f:(num,num)fmap)` ASSUME_TAC THENL
   [UNDISCH_TAC `bc_ref_inv conf n refs
                   (f,tf,heap1:(((A)word_loc,data_to_word_memoryProof_tag#
                                 ((A)word_loc)list)heap_element)list,be)` THEN
    REWRITE_TAC[bc_ref_inv_def; FLOOKUP_DEF] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `FLOOKUP (f:(num,num)fmap) n = SOME (FAPPLY f n) /\
    FLOOKUP ((g:(num,num)fmap) f_o_f f) n = SOME (FAPPLY g (FAPPLY f n))`
   STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MP1AUX_FLOOKUP_f_o_f; flookup_thm]; ALL_TAC] THEN
  UNDISCH_TAC `bc_ref_inv conf n refs
                 (f,tf,heap1:(((A)word_loc,data_to_word_memoryProof_tag#
                               ((A)word_loc)list)heap_element)list,be)` THEN
  ASM_REWRITE_TAC[bc_ref_inv_def] THEN CASE_REWRITE_TAC[] THEN
  CASES_ON `lookup n (refs:(data_v bvl_ref)spt)` THEN CASE_REWRITE_TAC[] THEN
  STRUCT_CASES_TAC(ISPEC `a:data_v bvl_ref` (cases "bvl_ref")) THEN
  CASE_REWRITE_TAC[LET_DEF; LET_END_DEF] THENL
   [(* ValueArray *)
    DISCH_THEN(X_CHOOSE_THEN `zs:(((A)word_loc)heap_address)list` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`g:(num,num)fmap`;
      `heap1:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
              heap_element)list`;
      `heap2:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
              heap_element)list`;
      `FAPPLY (f:(num,num)fmap) n`; `zs:(((A)word_loc)heap_address)list`;
      `LENGTH (zs:(((A)word_loc)heap_address)list)`;
      `(RefTag,[]:((A)word_loc)list)`] MP1AUX_gc_related_lookup) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[RefBlock_def]) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN
    EXISTS_TAC `ADDR_MAP (FAPPLY (g:(num,num)fmap))
                         (zs:(((A)word_loc)heap_address)list)` THEN
    ASM_REWRITE_TAC[RefBlock_def; GSYM ADDR_MAP_LENGTH] THEN
    MATCH_MP_TAC MP1AUX_ALL2_v_inv_related THEN
    EXISTS_TAC `heap1:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
                       heap_element)list` THEN
    ASM_REWRITE_TAC[];
    (* ByteArray *)
    DISCH_TAC THEN MATCH_MP_TAC MP1AUX_gc_related_nil THEN
    EXISTS_TAC `heap1:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
                       heap_element)list` THEN
    ASM_REWRITE_TAC[MP1AUX_Bytes_nil];
    (* Thunk *)
    DISCH_THEN(X_CHOOSE_THEN `z:((A)word_loc)heap_address` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`g:(num,num)fmap`;
      `heap1:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
              heap_element)list`;
      `heap2:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
              heap_element)list`;
      `FAPPLY (f:(num,num)fmap) n`; `[z:((A)word_loc)heap_address]`; `1`;
      `(ThunkTag a0,[]:((A)word_loc)list)`] MP1AUX_gc_related_lookup) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ThunkBlock_def]) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MP1AUX_ADDR_MAP_SING; MEM] THEN STRIP_TAC THEN
    EXISTS_TAC `ADDR_APPLY (FAPPLY (g:(num,num)fmap))
                           (z:((A)word_loc)heap_address)` THEN
    ASM_REWRITE_TAC[ThunkBlock_def] THEN
    MATCH_MP_TAC MP1AUX_v_inv_related1 THEN
    EXISTS_TAC `heap1:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
                       heap_element)list` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    (* MutBlock *)
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[IN_IMAGE; CONTRAPOS_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `t:num` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `t:num` THEN
      FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[MP1AUX_f_o_f] o
        check (fun th -> is_comb(concl th) &&
               can (find_term ((=) `FDOM:(num,num)fmap->num->bool`)) (concl th))) THEN
      SUBGOAL_THEN
       `FAPPLY ((g:(num,num)fmap) f_o_f (tf:(num,num)fmap)) t = FAPPLY g (FAPPLY tf t)`
       (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
       [ASM_MESON_TAC[MP1AUX_f_o_f]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [gc_related_def] o
                    check (MP1AUX_HEAD "gc_related")) THEN
      REWRITE_TAC[INJ] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`g:(num,num)fmap`;
        `heap1:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
                heap_element)list`;
        `heap2:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
                heap_element)list`;
        `FAPPLY (f:(num,num)fmap) n`; `zs:(((A)word_loc)heap_address)list`;
        `LENGTH (zs:(((A)word_loc)heap_address)list)`;
        `(BlockTag a0,[]:((A)word_loc)list)`] MP1AUX_gc_related_lookup) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[BlockRep_def]) THEN ASM_REWRITE_TAC[] THEN
      STRIP_TAC THEN
      EXISTS_TAC `ADDR_MAP (FAPPLY (g:(num,num)fmap))
                           (zs:(((A)word_loc)heap_address)list)` THEN
      ASM_REWRITE_TAC[BlockRep_def; GSYM ADDR_MAP_LENGTH] THEN
      MATCH_MP_TAC MP1AUX_ALL2_v_inv_related THEN
      EXISTS_TAC `heap1:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
                         heap_element)list` THEN
      ASM_REWRITE_TAC[]]]);;

(* HOL4 line 883 *)
let gc_inline_rel_rules,gc_inline_rel_ind,gc_inline_rel_cases,
    gc_inline_rel_strongind =
  cake_inductive
  `(!inline (h1:((A,B)heap_element)list) x.
      gc_inline_rel inline h1 x x) /\
   (!inline h1 p block x (u:A).
      heap_lookup p h1 = SOME block /\
      inline block x ==>
      gc_inline_rel inline h1 (Pointer p u) x)`;;

let gc_inline_rel_unchanged = el 0 (CONJUNCTS gc_inline_rel_rules);;

let gc_inline_rel_inline = el 1 (CONJUNCTS gc_inline_rel_rules);;

(* HOL4 line 891 *)
let gc_heap_inline_rel_rules,gc_heap_inline_rel_ind,gc_heap_inline_rel_cases,
    gc_heap_inline_rel_strongind =
  cake_inductive
  `(!inline (h1:((A,B)heap_element)list) x.
      gc_heap_inline_rel inline h1 x x) /\
   (!inline h1 xs ys n (d:B).
      ALL2 (gc_inline_rel inline h1) xs ys ==>
      gc_heap_inline_rel inline h1 (DataElement xs n d) (DataElement ys n d))`;;

let gc_heap_inline_rel_unchanged = el 0 (CONJUNCTS gc_heap_inline_rel_rules);;

let gc_heap_inline_rel_inline = el 1 (CONJUNCTS gc_heap_inline_rel_rules);;

(* HOL4 line 898 *)
let gc_inline_def = cake_def
  `gc_inline inline (r1,h1:((A,B)heap_element)list) (r2,h2) <=>
     ALL2 (gc_inline_rel inline h1) r1 r2 /\
     ALL2 (gc_heap_inline_rel inline h1) h1 h2`;;

(* HOL4 line 904 *)
let gc_related_roots_heap_def = cake_def
  `gc_related_roots_heap f (r1,h1:((A,B)heap_element)list) (r2,h2) <=>
     gc_related f h1 h2 /\
     r2 = ADDR_MAP (FAPPLY f) r1 /\
     (!ptr (u:A). MEM (Pointer ptr u) r1 ==> ptr IN FDOM f)`;;

(* HOL4 line 911 *)
let gc_inline_related_def = cake_def
  `gc_inline_related inline f (r1,h1:((A,B)heap_element)list) (r2,h2) <=>
     ?ri hi. gc_inline inline (r1,h1) (ri,hi) /\
             gc_related_roots_heap f (ri,hi) (r2,h2)`;;

(* MP1AUX: related heap elements have the same length and kind *)
let MP1AUX_gc_heap_inline_rel_el_length = prove
 (`!inline (h1:((A,B)heap_element)list) x y.
     gc_heap_inline_rel inline h1 x y ==>
     el_length x = el_length y /\ (isDataElement x <=> isDataElement y)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[gc_heap_inline_rel_cases] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[el_length_def] THEN
  REWRITE_TAC[isDataElement_def; injectivity "heap_element"] THEN MESON_TAC[]);;

(* HOL4 line 917 *)
let gc_heap_inline_rel_heap_lookup = prove
 (`!(heap:((A,data_to_word_memoryProof_tag#B list)heap_element)list)
    heap1 heap2.
     ALL2 (gc_heap_inline_rel dest_evaluated_thunk_rel heap) heap1 heap2 ==>
     !a. isSomeDataElement (heap_lookup a heap1) <=>
         isSomeDataElement (heap_lookup a heap2)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[ALL2] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
    `t':((A,data_to_word_memoryProof_tag#B list)heap_element)list`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MP1AUX_gc_heap_inline_rel_el_length) THEN
  GEN_TAC THEN REWRITE_TAC[heap_lookup_def] THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `a = 0` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[isSomeDataElement_def; option_INJ; GSYM isDataElement_def] THEN
    ASM_REWRITE_TAC[];
    COND_CASES_TAC THEN ASM_REWRITE_TAC[]]);;

(* HOL4 line 929 *)
let ThunkBlock_not_EQ = prove
 (`!ev (x:((A)word_loc)heap_address) i w n xs zs be flag bs ys.
     ~(ThunkBlock ev x = Bignum i) /\
     ~(ThunkBlock ev x = Word64Rep (:A) w) /\
     ~(ThunkBlock ev x = BlockRep n xs:((A)word_loc,data_to_word_memoryProof_tag#
                                         ((A)word_loc)list)heap_element) /\
     ~(ThunkBlock ev x = RefBlock zs:((A)word_loc,data_to_word_memoryProof_tag#
                                      ((A)word_loc)list)heap_element) /\
     ~(ThunkBlock ev x = Bytes be flag bs ys)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `i:int` (INST_TYPE [`:A`,`:A`] MP1AUX_Bignum_nil)) THEN
  DISCH_THEN(X_CHOOSE_THEN `l1:num` (X_CHOOSE_THEN
    `d1:data_to_word_memoryProof_tag#((A)word_loc)list` SUBST1_TAC)) THEN
  MP_TAC(ISPEC `w:int64` (INST_TYPE [`:A`,`:A`] MP1AUX_Word64Rep_nil)) THEN
  DISCH_THEN(X_CHOOSE_THEN `l2:num` (X_CHOOSE_THEN
    `d2:data_to_word_memoryProof_tag#((A)word_loc)list` SUBST1_TAC)) THEN
  MP_TAC(ISPECL [`be:bool`; `flag:bool`; `bs:byte list`; `ys:(A word)list`]
           MP1AUX_Bytes_nil) THEN
  DISCH_THEN(X_CHOOSE_THEN `l3:num` (X_CHOOSE_THEN
    `d3:data_to_word_memoryProof_tag#((A)word_loc)list` SUBST1_TAC)) THEN
  REWRITE_TAC[ThunkBlock_def; BlockRep_def; RefBlock_def;
              injectivity "heap_element"; NOT_CONS_NIL; PAIR_EQ;
              distinctness "data_to_word_memoryProof_tag"]);;

(* HOL4 line 941 *)
let LIST_REL_gc_heap_inline_DataElement = prove
 (`!(base:((A,data_to_word_memoryProof_tag#B list)heap_element)list)
    xs n d heap1 heap2.
     ALL2 (gc_heap_inline_rel dest_evaluated_thunk_rel base) heap1 heap2 ==>
     !ptr.
       heap_lookup ptr heap1 = SOME (DataElement xs n d) ==>
       ?ys.
         heap_lookup ptr heap2 = SOME (DataElement ys n d) /\
         ALL2 (gc_inline_rel dest_evaluated_thunk_rel base) xs ys`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[ALL2; heap_lookup_def; option_DISTINCT] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
    `t':((A,data_to_word_memoryProof_tag#B list)heap_element)list`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MP1AUX_gc_heap_inline_rel_el_length) THEN
  GEN_TAC THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[option_INJ] THEN DISCH_THEN SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (MP1AUX_HEAD "gc_heap_inline_rel")) THEN
    ONCE_REWRITE_TAC[gc_heap_inline_rel_cases] THEN
    REWRITE_TAC[injectivity "heap_element"] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[option_INJ; injectivity "heap_element"] THENL
     [EXISTS_TAC `xs:(A heap_address)list` THEN
      REWRITE_TAC[ALL2_ALL; GSYM ALL_MEM; gc_inline_rel_rules];
      ASM_MESON_TAC[]];
    COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT] THEN
    FIRST_X_ASSUM(ACCEPT_TAC o SPEC
      `ptr - el_length (h':(A,data_to_word_memoryProof_tag#B list)heap_element)` o
      check (is_forall o concl))]);;

(* MP1AUX: a data element of the heap after inlining *)
let MP1AUX_inline_lookup = prove
 (`!(base:((A,data_to_word_memoryProof_tag#B list)heap_element)list)
    heap1 heap2 ptr xs n d.
     ALL2 (gc_heap_inline_rel dest_evaluated_thunk_rel base) heap1 heap2 /\
     heap_lookup ptr heap1 = SOME (DataElement xs n d) ==>
     ?ys. heap_lookup ptr heap2 = SOME (DataElement ys n d) /\
          ALL2 (gc_inline_rel dest_evaluated_thunk_rel base) xs ys`,
  MESON_TAC[LIST_REL_gc_heap_inline_DataElement]);;

(* MP1AUX: an element without pointers is unchanged by inlining *)
let MP1AUX_inline_nil = prove
 (`!(base:((A,data_to_word_memoryProof_tag#B list)heap_element)list)
    heap1 heap2 ptr x.
     ALL2 (gc_heap_inline_rel dest_evaluated_thunk_rel base) heap1 heap2 /\
     heap_lookup ptr heap1 = SOME x /\ (?l d. x = DataElement [] l d) ==>
     heap_lookup ptr heap2 = SOME x`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MP_TAC(ISPECL [`base:((A,data_to_word_memoryProof_tag#B list)heap_element)list`;
                 `heap1:((A,data_to_word_memoryProof_tag#B list)heap_element)list`;
                 `heap2:((A,data_to_word_memoryProof_tag#B list)heap_element)list`;
                 `ptr:num`; `[]:(A heap_address)list`; `l:num`;
                 `d:data_to_word_memoryProof_tag#B list`] MP1AUX_inline_lookup) THEN
  ASM_REWRITE_TAC[ALL2_DEF] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

(* MP1AUX: ALL2 with a one element list *)
let MP1AUX_ALL2_SING = prove
 (`!(P:A->B->bool) x ys. ALL2 P [x] ys <=> ?y. ys = [y] /\ P x y`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[ALL2; NOT_CONS_NIL; CONS_11] THEN
  STRUCT_CASES_TAC(ISPEC `t:B list` list_CASES) THEN
  REWRITE_TAC[ALL2; NOT_CONS_NIL; CONS_11] THEN MESON_TAC[]);;

(* MP1AUX: a reference that is not a thunk is not stored as a ThunkBlock *)
let MP1AUX_bc_ref_inv_not_thunk = prove
 (`!conf n refs f tf be ev x
    (heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
           heap_element)list).
     bc_ref_inv conf n refs (f,tf,heap,be) /\
     (!ev v. ~(lookup n refs = SOME (bvl_Thunk ev v))) /\
     heap_lookup (FAPPLY f n) heap = SOME (ThunkBlock ev x) ==> F`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bc_ref_inv_def; FLOOKUP_DEF] THEN
  COND_CASES_TAC THEN CASE_REWRITE_TAC[] THEN
  CASES_ON `lookup n (refs:(data_v bvl_ref)spt)` THEN CASE_REWRITE_TAC[] THEN
  STRUCT_CASES_TAC(ISPEC `a:data_v bvl_ref` (cases "bvl_ref")) THEN
  CASE_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[injectivity "bvl_ref"; option_INJ] THEN
  ASM_MESON_TAC[ThunkBlock_not_EQ; option_INJ]);;

(* MP1AUX: reachability through blocks and thunks *)
let MP1AUX_reachable_refs_Block = prove
 (`!v l refs m ts n.
     MEM v l /\ reachable_refs [v] refs m ==>
     reachable_refs [data_Block ts n l] refs m`,
  REWRITE_TAC[reachable_refs_def; MEM] THEN REPEAT STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`data_Block ts n l`; `r:num`] THEN
  ASM_REWRITE_TAC[get_refs_def; MEM_FLAT; MEM_MAP] THEN ASM_MESON_TAC[]);;

let MP1AUX_reachable_refs_Thunk = prove
 (`!n refs ev v m b.
     lookup n refs = SOME (bvl_Thunk ev v) /\ reachable_refs [v] refs m ==>
     reachable_refs [data_RefPtr b n] refs m`,
  REWRITE_TAC[reachable_refs_def; MEM] THEN REPEAT STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`data_RefPtr b n`; `n:num`] THEN
  REWRITE_TAC[get_refs_def; MEM] THEN MATCH_MP_TAC RTC_TRANS_R THEN
  EXISTS_TAC `r:num` THEN ASM_REWRITE_TAC[ref_edge_def] THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[get_refs_def; MAP; FLAT; APPEND_NIL] THEN ASM_MESON_TAC[]);;

let MP1AUX_reachable_refs_RefPtr = prove
 (`!b n refs. reachable_refs [data_RefPtr b n] refs n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[reachable_refs_def; MEM] THEN
  MAP_EVERY EXISTS_TAC [`data_RefPtr b n`; `n:num`] THEN
  REWRITE_TAC[get_refs_def; MEM; RTC_REFL]);;

(* MP1AUX: split the inlining relation for a pointer that was inlined *)
let MP1AUX_INL_TAC =
  FIRST_X_ASSUM(fun th -> if is_exists(concl th) then
     X_CHOOSE_THEN `p:num` (X_CHOOSE_THEN
       `blk:((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element`
       (X_CHOOSE_THEN `u:(A)word_loc` STRIP_ASSUME_TAC)) th
     else failwith "MP1AUX_INL_TAC") THEN
  RULE_ASSUM_TAC(REWRITE_RULE[dest_evaluated_thunk_rel_cases]);;

(* HOL4 line 957 *)
let gc_heap_inline_rel_v_inv_lemma = prove
 (`!conf be ck v refs x1 x2 f tf heap1
    heap2:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
           heap_element)list.
     v_inv conf v refs (x1,f,tf,heap1) ==>
     ALL2 (gc_heap_inline_rel dest_evaluated_thunk_rel heap1) heap1 heap2 /\
     (!n. n IN FDOM f /\ reachable_refs [v] refs n ==>
          bc_ref_inv conf n refs (f,tf,heap1,be)) /\
     gc_inline_rel dest_evaluated_thunk_rel heap1 x1 x2 ==>
     v_inv_ck ck conf v refs (x2,f,tf,heap2)`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC num_WF THEN X_GEN_TAC `ck:num` THEN
  DISCH_THEN(LABEL_TAC "IH") THEN X_GEN_TAC `v:data_v` THEN
  STRUCT_CASES_TAC(ISPEC `v:data_v` MP1AUX_data_v_nchotomy) THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[v_inv_def; MP1AUX_v_inv_ck_Number; MP1AUX_v_inv_ck_Word64;
              MP1AUX_v_inv_ck_CodePtr; MP1AUX_v_inv_ck_RefPtr;
              MP1AUX_v_inv_ck_Block] THEN
  DISCH_THEN(LABEL_TAC "V") THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "H")
    (CONJUNCTS_THEN2 (LABEL_TAC "R") (fun th -> LABEL_TAC "G" th THEN
      DISJ_CASES_TAC (GEN_REWRITE_RULE I [gc_inline_rel_cases] th)))) THENL
   [(* Number, not inlined *)
    REMOVE_THEN "V" MP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    EXISTS_TAC `ptr:num` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MP1AUX_inline_nil THEN
    MAP_EVERY EXISTS_TAC
     [`heap1:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
              heap_element)list`;
      `heap1:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
              heap_element)list`] THEN
    ASM_REWRITE_TAC[MP1AUX_Bignum_nil];
    (* Number, inlined *)
    MP1AUX_INL_TAC THEN REMOVE_THEN "V" MP_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[distinctness "heap_address"; injectivity "heap_address"] THEN
    STRIP_TAC THEN ASM_MESON_TAC[ThunkBlock_not_EQ; option_INJ];
    (* Word64, not inlined *)
    REMOVE_THEN "V" MP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN STRIP_TAC THEN
    EXISTS_TAC `ptr:num` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MP1AUX_inline_nil THEN
    MAP_EVERY EXISTS_TAC
     [`heap1:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
              heap_element)list`;
      `heap1:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
              heap_element)list`] THEN
    ASM_REWRITE_TAC[MP1AUX_Word64Rep_nil];
    (* Word64, inlined *)
    MP1AUX_INL_TAC THEN REMOVE_THEN "V" MP_TAC THEN
    ASM_REWRITE_TAC[injectivity "heap_address"] THEN
    STRIP_TAC THEN ASM_MESON_TAC[ThunkBlock_not_EQ; option_INJ];
    (* Block, not inlined *)
    REMOVE_THEN "V" MP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `ptr:num` (X_CHOOSE_THEN
    `xs:(((A)word_loc)heap_address)list` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`heap1:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list`;
                 `heap1:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list`;
                 `heap2:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list`;
                 `ptr:num`; `xs:(((A)word_loc)heap_address)list`;
                 `LENGTH (xs:(((A)word_loc)heap_address)list)`;
                 `(BlockTag a1,[]:((A)word_loc)list)`] MP1AUX_inline_lookup) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[BlockRep_def]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `ys:(((A)word_loc)heap_address)list` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `LENGTH (ys:(((A)word_loc)heap_address)list) =
                LENGTH (xs:(((A)word_loc)heap_address)list)` ASSUME_TAC THENL
   [ASM_MESON_TAC[EVERY2_LENGTH]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`ptr:num`; `ys:(((A)word_loc)heap_address)list`] THEN
  ASM_REWRITE_TAC[BlockRep_def] THEN DISCH_TAC THEN
  REWRITE_TAC[LIST_REL_EL_EQN] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[EVERY2_LENGTH]; ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `v_inv conf (EL i a2) refs
      (EL i (xs:(((A)word_loc)heap_address)list),f,tf,
       heap1:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
              heap_element)list) /\
    gc_inline_rel dest_evaluated_thunk_rel heap1 (EL i xs)
      (EL i (ys:(((A)word_loc)heap_address)list))`
   STRIP_ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[LIST_REL_EL_EQN]) THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  USE_THEN "IH" (MP_TAC o SPEC `ck - 1`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MATCH_MP_TAC o REWRITE_RULE[IMP_IMP]) THEN
  MAP_EVERY EXISTS_TAC [`EL i (xs:(((A)word_loc)heap_address)list)`;
    `heap1:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list`] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN USE_THEN "R" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MP1AUX_reachable_refs_Block THEN
  EXISTS_TAC `EL i (a2:data_v list)` THEN ASM_MESON_TAC[MEM_EL];
    (* Block, inlined *)
    MP1AUX_INL_TAC THEN REMOVE_THEN "V" MP_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[distinctness "heap_address"; injectivity "heap_address"] THEN
    STRIP_TAC THEN ASM_MESON_TAC[ThunkBlock_not_EQ; option_INJ];
    (* CodePtr, not inlined *)
    REMOVE_THEN "V" MP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[];
    (* CodePtr, inlined *)
    MP1AUX_INL_TAC THEN REMOVE_THEN "V" MP_TAC THEN
    ASM_REWRITE_TAC[distinctness "heap_address"];
    (* RefPtr, not inlined *)
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
  REMOVE_THEN "V" (DISJ_CASES_THEN2 (fun th -> DISJ1_TAC THEN ACCEPT_TAC th)
    (DISJ_CASES_THEN2
      (X_CHOOSE_THEN `ev:thunk_mode` (X_CHOOSE_THEN `v:data_v`
        (X_CHOOSE_THEN `y:((A)word_loc)heap_address` STRIP_ASSUME_TAC)))
      (X_CHOOSE_THEN `v:data_v` STRIP_ASSUME_TAC))) THENL
   [DISJ2_TAC THEN DISJ1_TAC THEN
    MP_TAC(ISPECL [`heap1:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list`;
                   `heap1:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list`;
                   `heap2:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list`;
                   `FAPPLY (f:(num,num)fmap) a1`; `[y:((A)word_loc)heap_address]`; `1`;
                   `(ThunkTag ev,[]:((A)word_loc)list)`] MP1AUX_inline_lookup) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ThunkBlock_def]) THEN
    ASM_REWRITE_TAC[MP1AUX_ALL2_SING] THEN
    DISCH_THEN(X_CHOOSE_THEN `ys:(((A)word_loc)heap_address)list`
      (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `y':((A)word_loc)heap_address`
        STRIP_ASSUME_TAC))) THEN
    MAP_EVERY EXISTS_TAC [`ev:thunk_mode`; `v:data_v`;
                          `y':((A)word_loc)heap_address`] THEN
    ASM_REWRITE_TAC[ThunkBlock_def] THEN DISCH_TAC THEN
    USE_THEN "IH" (MP_TAC o SPEC `ck - 1`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MATCH_MP_TAC o REWRITE_RULE[IMP_IMP]) THEN
    MAP_EVERY EXISTS_TAC [`y:((A)word_loc)heap_address`;
      `heap1:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN USE_THEN "R" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MP1AUX_reachable_refs_Thunk THEN
    MAP_EVERY EXISTS_TAC [`ev:thunk_mode`; `v:data_v`] THEN ASM_REWRITE_TAC[];
    DISJ2_TAC THEN DISJ2_TAC THEN EXISTS_TAC `v:data_v` THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    USE_THEN "IH" (MP_TAC o SPEC `ck - 1`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MATCH_MP_TAC o REWRITE_RULE[IMP_IMP]) THEN
    MAP_EVERY EXISTS_TAC [`x1:((A)word_loc)heap_address`;
      `heap1:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN USE_THEN "R" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MP1AUX_reachable_refs_Thunk THEN
    MAP_EVERY EXISTS_TAC [`Evaluated`; `v:data_v`] THEN ASM_REWRITE_TAC[]];
    (* RefPtr, inlined *)
    MP1AUX_INL_TAC THEN
  REMOVE_THEN "V" (DISJ_CASES_THEN2 STRIP_ASSUME_TAC
    (DISJ_CASES_THEN2
      (X_CHOOSE_THEN `ev:thunk_mode` (X_CHOOSE_THEN `v:data_v`
        (X_CHOOSE_THEN `y:((A)word_loc)heap_address` STRIP_ASSUME_TAC)))
      (X_CHOOSE_THEN `v:data_v` STRIP_ASSUME_TAC))) THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[injectivity "heap_address"]) THEN
    FIRST_X_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = `x1:((A)word_loc)heap_address`
      then SUBST_ALL_TAC th else failwith "") THEN
    RULE_ASSUM_TAC(REWRITE_RULE[injectivity "heap_address"]) THEN
    REFUTE_THEN(K ALL_TAC) THEN MATCH_MP_TAC MP1AUX_bc_ref_inv_not_thunk THEN
    MAP_EVERY EXISTS_TAC [`conf:data_to_word_config`; `a1:num`; `refs:(data_v bvl_ref)spt`;
      `f:(num,num)fmap`; `tf:(num,num)fmap`; `be:bool`; `Evaluated`;
      `x2:((A)word_loc)heap_address`;
      `heap1:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    TRY(USE_THEN "R" MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[MP1AUX_reachable_refs_RefPtr] THEN NO_TAC) THEN
    ASM_MESON_TAC[];
    SUBGOAL_THEN `ev = Evaluated /\ x2:((A)word_loc)heap_address = y` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[injectivity "heap_address"; option_INJ; ThunkBlock_11]; ALL_TAC] THEN
  DISJ2_TAC THEN DISJ2_TAC THEN EXISTS_TAC `v:data_v` THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ASM_SIMP_TAC[] THEN DISCH_TAC THEN
  USE_THEN "IH" (MP_TAC o SPEC `ck - 1`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MATCH_MP_TAC o REWRITE_RULE[IMP_IMP]) THEN
  MAP_EVERY EXISTS_TAC [`y:((A)word_loc)heap_address`;
    `heap1:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list`] THEN
  ASM_REWRITE_TAC[gc_inline_rel_rules] THEN REPEAT STRIP_TAC THEN
  USE_THEN "R" MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MP1AUX_reachable_refs_Thunk THEN
  MAP_EVERY EXISTS_TAC [`Evaluated`; `v:data_v`] THEN ASM_REWRITE_TAC[];
    DISJ2_TAC THEN DISJ2_TAC THEN EXISTS_TAC `v:data_v` THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  USE_THEN "IH" (MP_TAC o SPEC `ck - 1`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MATCH_MP_TAC o REWRITE_RULE[IMP_IMP]) THEN
  MAP_EVERY EXISTS_TAC [`x1:((A)word_loc)heap_address`;
    `heap1:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  USE_THEN "R" MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MP1AUX_reachable_refs_Thunk THEN
  MAP_EVERY EXISTS_TAC [`Evaluated`; `v:data_v`] THEN ASM_REWRITE_TAC[]]]);;

(* HOL4 line 1046 *)
let gc_heap_inline_rel_v_inv = prove
 (`!conf be v refs x1 x2 f tf heap1
    heap2:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
           heap_element)list.
     ALL2 (gc_heap_inline_rel dest_evaluated_thunk_rel heap1) heap1 heap2 /\
     (!n. n IN FDOM f /\ reachable_refs [v] refs n ==>
          bc_ref_inv conf n refs (f,tf,heap1,be)) /\
     v_inv conf v refs (x1,f,tf,heap1) /\
     gc_inline_rel dest_evaluated_thunk_rel heap1 x1 x2 ==>
     v_inv conf v refs (x2,f,tf,heap2)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[v_inv_eq] THEN GEN_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] gc_heap_inline_rel_v_inv_lemma) THEN
  MAP_EVERY EXISTS_TAC [`be:bool`; `x1:((A)word_loc)heap_address`;
    `heap1:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
            heap_element)list`] THEN
  ASM_REWRITE_TAC[]);;

(* MP1AUX: reachability through one more edge *)
let MP1AUX_reachable_refs_via = prove
 (`!stack refs n v m.
     reachable_refs stack refs n /\
     (!x. MEM x (get_refs v) ==> ref_edge refs n x) /\
     reachable_refs [v] refs m ==>
     reachable_refs stack refs m`,
  REWRITE_TAC[reachable_refs_def; MEM] THEN REPEAT STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`x:data_v`; `r:num`] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC RTC_TRANS THEN EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC RTC_TRANS_R THEN EXISTS_TAC `r':num` THEN
  ASM_MESON_TAC[]);;

(* MP1AUX: an element of a reference payload is one edge away *)
let MP1AUX_ref_edge_payload = prove
 (`!n refs v vs.
     MEM v vs /\
     (lookup n refs = SOME (bvl_ValueArray vs) \/
      (?ev. vs = [v] /\ lookup n refs = SOME (bvl_Thunk ev v)) \/
      (?tg fin l c r. vs = APPEND (APPEND l [c]) r /\
                      lookup n refs = SOME (MutBlock tg fin l c r))) ==>
     !x. MEM x (get_refs v) ==> ref_edge refs n x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[ref_edge_def] THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[get_refs_def; MEM_FLAT; MEM_MAP] THEN ASM_MESON_TAC[MEM]);;

(* MP1AUX: reachability from a member of the stack *)
let MP1AUX_reachable_refs_MEM = prove
 (`!v stack refs m.
     MEM v stack /\ reachable_refs [v] refs m ==> reachable_refs stack refs m`,
  REWRITE_TAC[reachable_refs_def; MEM] THEN MESON_TAC[]);;

(* MP1AUX: v_inv of the payload of a reference after inlining *)
let MP1AUX_inline_payload = prove
 (`!conf be refs f tf heap1
    (heap2:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
            heap_element)list) zs zs' vals.
     ALL2 (gc_heap_inline_rel dest_evaluated_thunk_rel heap1) heap1 heap2 /\
     (!v m. MEM v vals /\ m IN FDOM f /\ reachable_refs [v] refs m ==>
            bc_ref_inv conf m refs (f,tf,heap1,be)) /\
     ALL2 (\z y. v_inv conf y refs (z,f,tf,heap1)) zs vals /\
     ALL2 (gc_inline_rel dest_evaluated_thunk_rel heap1) zs zs' ==>
     ALL2 (\z y. v_inv conf y refs (z,f,tf,heap2)) zs' vals`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `LENGTH (zs:(((A)word_loc)heap_address)list) = LENGTH (vals:data_v list) /\
    (!i. i < LENGTH zs ==>
         v_inv conf (EL i vals) refs (EL i zs,f,tf,heap1)) /\
    LENGTH zs = LENGTH (zs':(((A)word_loc)heap_address)list) /\
    (!i. i < LENGTH zs ==>
         gc_inline_rel dest_evaluated_thunk_rel heap1 (EL i zs) (EL i zs'))`
   STRIP_ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[LIST_REL_EL_EQN]) THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[LIST_REL_EL_EQN] THEN CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC gc_heap_inline_rel_v_inv THEN
  MAP_EVERY EXISTS_TAC [`be:bool`; `EL i (zs:(((A)word_loc)heap_address)list)`;
    `heap1:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
            heap_element)list`] THEN
  SUBGOAL_THEN `i < LENGTH (zs:(((A)word_loc)heap_address)list)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  EXISTS_TAC `EL i (vals:data_v list)` THEN ASM_MESON_TAC[MEM_EL]);;

(* MP1AUX: bc_ref_inv after inlining *)
let MP1AUX_bc_ref_inv_inline = prove
 (`!conf n refs f tf be heap1
    (heap2:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
            heap_element)list).
     ALL2 (gc_heap_inline_rel dest_evaluated_thunk_rel heap1) heap1 heap2 /\
     bc_ref_inv conf n refs (f,tf,heap1,be) /\
     (!v m. (!x. MEM x (get_refs v) ==> ref_edge refs n x) /\ m IN FDOM f /\
            reachable_refs [v] refs m ==> bc_ref_inv conf m refs (f,tf,heap1,be)) ==>
     bc_ref_inv conf n refs (f,tf,heap2,be)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "H")
    (CONJUNCTS_THEN2 MP_TAC (LABEL_TAC "R"))) THEN
  REWRITE_TAC[bc_ref_inv_def] THEN
  CASES_ON `FLOOKUP (f:(num,num)fmap) n` THEN CASE_REWRITE_TAC[] THEN
  CASES_ON `lookup n (refs:(data_v bvl_ref)spt)` THEN CASE_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `a':data_v bvl_ref` (cases "bvl_ref")) THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  CASE_REWRITE_TAC[LET_DEF; LET_END_DEF] THENL
   [(* ValueArray *)
    DISCH_THEN(X_CHOOSE_THEN `zs:(((A)word_loc)heap_address)list` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL
     [`heap1:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list`;
      `heap1:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list`;
      `heap2:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list`;
      `a:num`; `zs:(((A)word_loc)heap_address)list`;
      `LENGTH (zs:(((A)word_loc)heap_address)list)`;
      `(RefTag,[]:((A)word_loc)list)`] MP1AUX_inline_lookup) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[RefBlock_def]) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `ys:(((A)word_loc)heap_address)list` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `ys:(((A)word_loc)heap_address)list` THEN
    SUBGOAL_THEN `LENGTH (ys:(((A)word_loc)heap_address)list) =
                  LENGTH (zs:(((A)word_loc)heap_address)list)` ASSUME_TAC THENL
     [ASM_MESON_TAC[EVERY2_LENGTH]; ALL_TAC] THEN
    ASM_REWRITE_TAC[RefBlock_def] THEN
    MATCH_MP_TAC MP1AUX_inline_payload THEN
    MAP_EVERY EXISTS_TAC [`be:bool`;
      `heap1:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list`;
      `zs:(((A)word_loc)heap_address)list`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN USE_THEN "R" MATCH_MP_TAC THEN
    EXISTS_TAC `v:data_v` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MP1AUX_ref_edge_payload THEN EXISTS_TAC `a'':data_v list` THEN
    ASM_REWRITE_TAC[];
    (* ByteArray *)
    DISCH_TAC THEN MATCH_MP_TAC MP1AUX_inline_nil THEN
    MAP_EVERY EXISTS_TAC
     [`heap1:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list`;
      `heap1:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list`] THEN
    ASM_REWRITE_TAC[MP1AUX_Bytes_nil];
    (* Thunk *)
    DISCH_THEN(X_CHOOSE_THEN `z:((A)word_loc)heap_address` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL
     [`heap1:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list`;
      `heap1:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list`;
      `heap2:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list`;
      `a:num`; `[z:((A)word_loc)heap_address]`; `1`;
      `(ThunkTag a0,[]:((A)word_loc)list)`] MP1AUX_inline_lookup) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ThunkBlock_def]) THEN
    ASM_REWRITE_TAC[MP1AUX_ALL2_SING] THEN
    DISCH_THEN(X_CHOOSE_THEN `ys:(((A)word_loc)heap_address)list`
      (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `z':((A)word_loc)heap_address`
        STRIP_ASSUME_TAC))) THEN
    EXISTS_TAC `z':((A)word_loc)heap_address` THEN
    ASM_REWRITE_TAC[ThunkBlock_def] THEN
    MATCH_MP_TAC gc_heap_inline_rel_v_inv THEN
    MAP_EVERY EXISTS_TAC [`be:bool`; `z:((A)word_loc)heap_address`;
      `heap1:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN USE_THEN "R" MATCH_MP_TAC THEN
    EXISTS_TAC `a1:data_v` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MP1AUX_ref_edge_payload THEN EXISTS_TAC `[a1:data_v]` THEN
    ASM_REWRITE_TAC[MEM] THEN MESON_TAC[];
    (* MutBlock *)
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL
     [`heap1:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list`;
      `heap1:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list`;
      `heap2:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list`;
      `a:num`; `zs:(((A)word_loc)heap_address)list`;
      `LENGTH (zs:(((A)word_loc)heap_address)list)`;
      `(BlockTag a0,[]:((A)word_loc)list)`] MP1AUX_inline_lookup) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[BlockRep_def]) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `ys:(((A)word_loc)heap_address)list` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `ys:(((A)word_loc)heap_address)list` THEN
    SUBGOAL_THEN `LENGTH (ys:(((A)word_loc)heap_address)list) =
                  LENGTH (zs:(((A)word_loc)heap_address)list)` ASSUME_TAC THENL
     [ASM_MESON_TAC[EVERY2_LENGTH]; ALL_TAC] THEN
    ASM_REWRITE_TAC[BlockRep_def] THEN
    MATCH_MP_TAC MP1AUX_inline_payload THEN
    MAP_EVERY EXISTS_TAC [`be:bool`;
      `heap1:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list`;
      `zs:(((A)word_loc)heap_address)list`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN USE_THEN "R" MATCH_MP_TAC THEN
    EXISTS_TAC `v:data_v` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MP1AUX_ref_edge_payload THEN
    EXISTS_TAC `APPEND (APPEND a2 [a3]) (a4:data_v list)` THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[]]);;

(* HOL4 line 1059 *)
let bc_stack_ref_inv_gc_inline = prove
 (`!conf ts stack refs roots1 roots2 be heap1
    heap2:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
           heap_element)list.
     gc_inline dest_evaluated_thunk_rel (roots1,heap1) (roots2,heap2) /\
     bc_stack_ref_inv conf ts stack refs (roots1,heap1,be) ==>
     bc_stack_ref_inv conf ts stack refs (roots2,heap2,be)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[gc_inline_def; bc_stack_ref_inv_def] THEN
  STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`f:(num,num)fmap`; `tf:(num,num)fmap`] THEN
  FIRST_ASSUM(ASSUME_TAC o GSYM o MATCH_MP gc_heap_inline_rel_heap_lookup o
              check (MP1AUX_HEAD "ALL2")) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [SUBGOAL_THEN
     `LENGTH (stack:data_v list) = LENGTH (roots1:(((A)word_loc)heap_address)list) /\
      (!i. i < LENGTH stack ==>
           v_inv conf (EL i stack) refs (EL i roots1,f,tf,heap1)) /\
      LENGTH roots1 = LENGTH (roots2:(((A)word_loc)heap_address)list) /\
      (!i. i < LENGTH roots1 ==>
           gc_inline_rel dest_evaluated_thunk_rel heap1 (EL i roots1) (EL i roots2))`
     STRIP_ASSUME_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[LIST_REL_EL_EQN]) THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[LIST_REL_EL_EQN] THEN CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC gc_heap_inline_rel_v_inv THEN
    MAP_EVERY EXISTS_TAC [`be:bool`;
      `EL i (roots1:(((A)word_loc)heap_address)list)`;
      `heap1:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
              heap_element)list`] THEN
    SUBGOAL_THEN `i < LENGTH (roots1:(((A)word_loc)heap_address)list)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (fun th ->
      try let b = snd(dest_imp(snd(dest_forall(concl th)))) in
          fst(dest_const(fst(strip_comb b))) = "bc_ref_inv"
      with Failure _ -> false)) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MP1AUX_reachable_refs_MEM THEN
    EXISTS_TAC `EL i (stack:data_v list)` THEN ASM_MESON_TAC[MEM_EL];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MP1AUX_bc_ref_inv_inline THEN
    EXISTS_TAC `heap1:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
                       heap_element)list` THEN
    ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (fun th ->
      try let b = snd(dest_imp(snd(dest_forall(concl th)))) in
          fst(dest_const(fst(strip_comb b))) = "bc_ref_inv"
      with Failure _ -> false)) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MP1AUX_reachable_refs_via THEN
    MAP_EVERY EXISTS_TAC [`n:num`; `v:data_v`] THEN ASM_REWRITE_TAC[]]);;

(* HOL4 line 1147 *)
let bc_stack_ref_inv_gc_related_roots_heap = prove
 (`!g conf ts stack refs roots1 roots2 be heap1
    heap2:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
           heap_element)list.
     gc_related_roots_heap g (roots1,heap1) (roots2,heap2) /\
     bc_stack_ref_inv conf ts stack refs (roots1,heap1,be) ==>
     bc_stack_ref_inv conf ts stack refs (roots2,heap2,be)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bc_stack_ref_inv_def; gc_related_roots_heap_def] THEN
  STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`(g:(num,num)fmap) f_o_f (f:(num,num)fmap)`; `(g:(num,num)fmap) f_o_f (tf:(num,num)fmap)`] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [gc_related_def]) THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[INJ; IN_ELIM_THM]) THEN
    REWRITE_TAC[INJ; IN_ELIM_THM] THEN ASM_MESON_TAC[MP1AUX_f_o_f];
    ASM_MESON_TAC[FDOM_F_COMP_G_SUBSET_FDOM_G; SUBSET_TRANS];
    RULE_ASSUM_TAC(REWRITE_RULE[INJ; IN_ELIM_THM]) THEN
    REWRITE_TAC[INJ; IN_ELIM_THM] THEN ASM_MESON_TAC[MP1AUX_f_o_f];
    ASM_MESON_TAC[FDOM_F_COMP_G_SUBSET_FDOM_G; SUBSET_TRANS];
    ASM_MESON_TAC[FDOM_F_COMP_G_SUBSET_FDOM_G; SUBSET_TRANS];
    UNDISCH_TAC `ALL2 (\v x. v_inv conf v refs (x,f,tf,heap1)) stack
                      (roots1:(((A)word_loc)heap_address)list)` THEN
    REWRITE_TAC[LIST_REL_EL_EQN; GSYM ADDR_MAP_LENGTH] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `i < LENGTH (roots1:(((A)word_loc)heap_address)list)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[EL_ADDR_MAP] THEN
    MATCH_MP_TAC MP1AUX_v_inv_related1 THEN
    EXISTS_TAC `heap1:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
                       heap_element)list` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MEM_EL];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC bc_ref_inv_related THEN
    EXISTS_TAC `heap1:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
                       heap_element)list` THEN
    ASM_MESON_TAC[MP1AUX_f_o_f]]);;

(* HOL4 line 1173 *)
let bc_stack_ref_inv_related = prove
 (`!g conf ts stack refs roots1 roots2 be heap1
    heap2:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
           heap_element)list.
     gc_inline_related dest_evaluated_thunk_rel g (roots1,heap1) (roots2,heap2) /\
     bc_stack_ref_inv conf ts stack refs (roots1,heap1,be) ==>
     bc_stack_ref_inv conf ts stack refs (roots2,heap2,be)`,
  REWRITE_TAC[gc_inline_related_def] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC bc_stack_ref_inv_gc_related_roots_heap THEN
  MAP_EVERY EXISTS_TAC [`g:(num,num)fmap`; `ri:(((A)word_loc)heap_address)list`;
    `hi:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
         heap_element)list`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC bc_stack_ref_inv_gc_inline THEN
  MAP_EVERY EXISTS_TAC [`roots1:(((A)word_loc)heap_address)list`;
    `heap1:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
            heap_element)list`] THEN
  ASM_REWRITE_TAC[]);;

let _ = Gc.compact();;

(* HOL4 line 1183 *)
let data_up_to_APPEND = prove
 (`!xs (ys:((A,B)heap_element)list).
     data_up_to (heap_length xs) (APPEND xs ys) <=> ALL isDataElement xs`,
  SIMP[data_up_to_def; heap_split_APPEND_if; LT_REFL; SUB_REFL; APPEND_NIL]);;
let _ = cake_add_simps [data_up_to_APPEND];;

(* HOL4 line 1189 *)
let all_reachable_from_roots_def = cake_def
  `all_reachable_from_roots roots (heap:((A,B)heap_element)list) <=>
     !p xs l d.
       heap_lookup p heap = SOME (DataElement xs l d) ==>
       p IN reachable_addresses roots heap`;;

(* HOL4 line 1196 *)
let IN_reachable_addresses = prove
 (`!x (roots:(A heap_address)list) (heap:((A,B)heap_element)list).
     x IN reachable_addresses roots heap <=>
     ?t x'. MEM (Pointer x' t) roots /\ RTC (gc_edge heap) x' x`,
  REWRITE_TAC[IN; reachable_addresses_def]);;

(* MP1AUX: a pointer of a list is mapped by ADDR_MAP (HOL4 does this     *)
(* inline with MEM_SPLIT and ADDR_MAP_APPEND)                              *)
let MP1AUX_MEM_Pointer_ADDR_MAP = prove
 (`!xs (g:num->num) x (t:A).
     MEM (Pointer x t) xs ==> MEM (Pointer (g x) t) (ADDR_MAP g xs)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MEM] THEN REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `h:A heap_address` (cases "heap_address")) THEN
  REWRITE_TAC[ADDR_MAP_def; MEM; injectivity "heap_address";
              distinctness "heap_address"] THEN
  ASM_MESON_TAC[]);;

(* HOL4 line 1200 *)
let reachable_addresses_related = prove
 (`!k roots (heap:((A,B)heap_element)list) f heap2.
     k IN reachable_addresses roots heap /\ gc_related f heap heap2 /\
     reachable_addresses roots heap SUBSET FDOM f ==>
     FAPPLY f k IN reachable_addresses (ADDR_MAP (FAPPLY f) roots) heap2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_reachable_addresses] THEN
  STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`t:A`; `FAPPLY (f:(num,num)fmap) x'`] THEN
  ASM_SIMP_TAC[MP1AUX_MEM_Pointer_ADDR_MAP] THEN
  SUBGOAL_THEN `(x':num) IN FDOM (f:(num,num)fmap)` MP_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    REWRITE_TAC[IN_reachable_addresses] THEN ASM_MESON_TAC[RTC_REFL];
    ALL_TAC] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [gc_related_def]) THEN
  SUBGOAL_THEN
   `!a b. RTC (gc_edge (heap:((A,B)heap_element)list)) a b ==>
          a IN FDOM (f:(num,num)fmap) ==>
          b IN FDOM f /\
          RTC (gc_edge (heap2:((A,B)heap_element)list)) (FAPPLY f a) (FAPPLY f b)`
   (fun th -> ASM_MESON_TAC[th]) THEN
  MATCH_MP_TAC RTC_INDUCT THEN BETA_TAC THEN REWRITE_TAC[RTC_REFL] THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`a:num`; `b:num`] THEN REWRITE_TAC[gc_edge_def] THEN
    DISCH_THEN(X_CHOOSE_THEN `ys:(A heap_address)list` (X_CHOOSE_THEN `ll:num`
      (X_CHOOSE_THEN `dd:B` (X_CHOOSE_THEN `tt:A` STRIP_ASSUME_TAC)))) THEN
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`a:num`; `ys:(A heap_address)list`; `ll:num`;
                                  `dd:B`]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC RTC_INC THEN REWRITE_TAC[gc_edge_def] THEN
    MAP_EVERY EXISTS_TAC [`ADDR_MAP (FAPPLY (f:(num,num)fmap)) (ys:(A heap_address)list)`; `ll:num`;
                          `dd:B`; `tt:A`] THEN
    ASM_SIMP_TAC[MP1AUX_MEM_Pointer_ADDR_MAP];
    MESON_TAC[RTC_TRANS]]);;

(* HOL4 line 1231 *)
let IMP_all_reachable_from_roots = prove
 (`!f roots (heap:((A,B)heap_element)list) heap2.
     FDOM f = reachable_addresses roots heap /\
     FRANGE f = {a | isSomeDataElement (heap_lookup a heap2)} /\
     gc_related f heap heap2 ==>
     all_reachable_from_roots (ADDR_MAP (FAPPLY f) roots) heap2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[all_reachable_from_roots_def] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(p:num) IN FRANGE (f:(num,num)fmap)` MP_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM; isSomeDataElement_def] THEN
    MAP_EVERY EXISTS_TAC [`xs:(A heap_address)list`; `l:num`; `d:B`] THEN
    REFL_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[IN_FRANGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC reachable_addresses_related THEN
  EXISTS_TAC `heap:((A,B)heap_element)list` THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN ASM_MESON_TAC[]);;

(* HOL4 line 1246 *)
let heap_lookup_expand_eq_SOME = prove
 (`!a (heap:((A,B)heap_element)list) n ys l d.
     heap_lookup a (APPEND heap (heap_expand n)) = SOME (DataElement ys l d) <=>
     heap_lookup a heap = SOME (DataElement ys l d)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[data_to_word_memoryProof_heap_lookup_APPEND] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `~(heap_lookup a (heap:((A,B)heap_element)list) = SOME (DataElement ys l d))`
   (fun th -> REWRITE_TAC[th]) THENL
   [ASM_MESON_TAC[heap_lookup_LESS]; ALL_TAC] THEN
  REWRITE_TAC[heap_expand_def] THEN COND_CASES_TAC THEN
  REWRITE_TAC[heap_lookup_def] THEN REPEAT COND_CASES_TAC THEN
  REWRITE_TAC[option_INJ; distinctness "heap_element"; option_DISTINCT;
              heap_lookup_def]);;

(* HOL4 line 1256 *)
let isSomeDataElement_heap_lookup = prove
 (`!a (heap:((A,B)heap_element)list) n.
     isSomeDataElement (heap_lookup a (APPEND heap (heap_expand n))) =
     isSomeDataElement (heap_lookup a heap)`,
  REWRITE_TAC[isSomeDataElement_def; heap_lookup_expand_eq_SOME]);;

(* HOL4 line 1263 *)
let gc_related_APPEND_heap_expand = prove
 (`!f (heap:((A,B)heap_element)list) heap2 n.
     gc_related f heap (APPEND heap2 (heap_expand n)) = gc_related f heap heap2`,
  REWRITE_TAC[gc_related_def; isSomeDataElement_heap_lookup;
              heap_lookup_expand_eq_SOME]);;

(* MP1AUX: gc_inline with nothing inlined *)
let MP1AUX_gc_inline_refl = prove
 (`!inline (r:(A heap_address)list) (h:((A,B)heap_element)list).
     gc_inline inline (r,h) (r,h)`,
  REWRITE_TAC[gc_inline_def; ALL2_ALL; GSYM ALL_MEM; gc_inline_rel_rules;
              gc_heap_inline_rel_rules]);;

(* MP1AUX: bc_stack_ref_inv after a gc that is described by gc_related *)
let MP1AUX_bc_stack_ref_inv_gc = prove
 (`!(f:(num,num)fmap) conf ts stack refs roots
    (heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
           heap_element)list) heap2 be.
     bc_stack_ref_inv conf ts stack refs (roots,heap,be) /\
     gc_related f heap heap2 /\
     (!ptr u. MEM (Pointer ptr u) roots ==> ptr IN FDOM f) ==>
     bc_stack_ref_inv conf ts stack refs (ADDR_MAP (FAPPLY f) roots,heap2,be)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC bc_stack_ref_inv_related THEN
  MAP_EVERY EXISTS_TAC [`f:(num,num)fmap`; `roots:(((A)word_loc)heap_address)list`;
    `heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
           heap_element)list`] THEN
  ASM_REWRITE_TAC[gc_inline_related_def] THEN
  MAP_EVERY EXISTS_TAC [`roots:(((A)word_loc)heap_address)list`;
    `heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
           heap_element)list`] THEN
  ASM_REWRITE_TAC[MP1AUX_gc_inline_refl; gc_related_roots_heap_def]);;

(* MP1AUX: heap_lookup at the end of a prefix (heap_lookup_heap_length of *)
(* HOL4 line 2328, needed earlier here)                                    *)
let MP1AUX_heap_lookup_heap_length = prove
 (`!h1 (h2:((A,B)heap_element)list).
     heap_lookup (heap_length h1) (APPEND h1 h2) = heap_lookup 0 h2`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[NOT_LESS_IMP_heap_lookup; LT_REFL; SUB_REFL]);;

(* HOL4 line 1269: full_gc_thm *)
let data_to_word_memoryProof_full_gc_thm = prove
 (`!conf stack refs roots
    heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
          heap_element)list be a sp sp1 gens limit ts.
     abs_ml_inv conf stack refs (roots,heap,be,a,sp,sp1,gens) limit ts /\
     data_to_word_config_gc_kind conf = data_to_word_Simple ==>
     ?roots2 heap2 a2.
       full_gc (roots,heap,limit) = (roots2,heap2,a2,T) /\
       abs_ml_inv conf stack refs
         (roots2,APPEND heap2 (heap_expand (limit - a2)),be,
          a2,limit - a2,0,gens) limit ts /\
       heap_length heap2 = a2 /\
       heap_length (heap_filter (reachable_addresses roots heap) heap) =
       heap_length heap2 /\
       all_reachable_from_roots roots2 (APPEND heap2 (heap_expand (limit - a2))) /\
       ALL isDataElement heap2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[abs_ml_inv_def] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`roots:(((A)word_loc)heap_address)list`;
                 `heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
                        heap_element)list`; `limit:num`] full_gc_related) THEN
  MP_TAC(ISPECL [`roots:(((A)word_loc)heap_address)list`;
                 `heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
                        heap_element)list`; `limit:num`] full_gc_ok) THEN
  MP_TAC(ISPECL [`roots:(((A)word_loc)heap_address)list`;
                 `heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
                        heap_element)list`; `limit:num`] full_gc_LENGTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`ADDR_MAP (FAPPLY (f:(num,num)fmap)) (roots:(((A)word_loc)heap_address)list)`;
    `heap2'':(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
              heap_element)list`;
    `heap_length (heap2'':(((A)word_loc,data_to_word_memoryProof_tag#
                             ((A)word_loc)list)heap_element)list)`] THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[gc_kind_inv_def] THEN CASE_REWRITE_TAC[];
    REWRITE_TAC[unused_space_inv_def; ADD_CLAUSES; MP1AUX_heap_lookup_heap_length;
                heap_length_APPEND; gc_shared_heap_length_heap_expand;
                data_up_to_APPEND; LE_REFL] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[heap_expand_def] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[heap_lookup_def];
    MATCH_MP_TAC MP1AUX_bc_stack_ref_inv_gc THEN
    EXISTS_TAC `heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
                      heap_element)list` THEN
    ASM_REWRITE_TAC[IN_reachable_addresses] THEN MESON_TAC[RTC_REFL];
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC IMP_all_reachable_from_roots THEN
    EXISTS_TAC `heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
                      heap_element)list` THEN
    ASM_REWRITE_TAC[isSomeDataElement_heap_lookup];
    ASM_REWRITE_TAC[]]);;

(* HOL4 line 1318 *)
let make_gc_conf_def = cake_def
  `make_gc_conf limit =
     gen_gc_conf_REC limit (isMutTag o FST)
       :(data_to_word_memoryProof_tag#A)gen_gc_conf`;;

(* MP1AUX: the configuration made by make_gc_conf *)
let MP1AUX_make_gc_conf = prove
 (`!limit. gen_gc_conf_limit (make_gc_conf limit:(data_to_word_memoryProof_tag#A)gen_gc_conf) =
           limit /\
           (!t r. gen_gc_conf_isRef (make_gc_conf limit:(data_to_word_memoryProof_tag#A)gen_gc_conf)
                    (t,r) <=> isMutTag t)`,
  REWRITE_TAC[make_gc_conf_def; gen_gc_conf_FIELDS.ri_accessors; o_THM]);;

let MP1AUX_isRef_DataElement = prove
 (`!(cc:(data_to_word_memoryProof_tag#B)gen_gc_conf) (xs:(A heap_address)list) l dd.
     (!t r. gen_gc_conf_isRef cc (t,r) <=> isMutTag t) ==>
     (isRef (DataElement xs l dd) <=> gen_gc_conf_isRef cc dd)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBST1_TAC(ISPEC `dd:data_to_word_memoryProof_tag#B` (GSYM PAIR)) THEN
  ASM_REWRITE_TAC[isRef_def]);;

let MP1AUX_SPLIT_LEAF_TAC =
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[gc_state_FIELDS.ri_accfupds; K_THM; ALL_APPEND; ALL] THEN
  ASM_SIMP_TAC[MP1AUX_isRef_DataElement] THEN
  ASM_REWRITE_TAC[isDataElement_def] THEN MESON_TAC[];;

(* HOL4 line 1323 *)
let gc_move_data_refs_split = prove
 (`!(cc:(data_to_word_memoryProof_tag#B)gen_gc_conf)
    (s:(A,data_to_word_memoryProof_tag#B)gc_state) x x1 s1.
     gen_gc_gc_move cc s x = (x1,s1) /\
     (!t r. gen_gc_conf_isRef cc (t,r) <=> isMutTag t) /\
     ALL isDataElement (gc_state_h2 s) /\ ALL (\x. ~isRef x) (gc_state_h2 s) /\
     ALL isRef (gc_state_r4 s) ==>
     ALL isDataElement (gc_state_h2 s1) /\
     ALL (\x. ~isRef x) (gc_state_h2 s1) /\ ALL isRef (gc_state_r4 s1)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `x:A heap_address` (cases "heap_address")) THEN
  REWRITE_TAC[gen_gc_gc_move_def; LET_DEF; LET_END_DEF] THEN REPEAT GEN_TAC THENL
   [ALL_TAC; MP1AUX_SPLIT_LEAF_TAC] THEN
  CASES_ON `heap_lookup a0 (gc_state_heap (s:(A,data_to_word_memoryProof_tag#B)gc_state))` THEN
  CASE_REWRITE_TAC[] THENL [MP1AUX_SPLIT_LEAF_TAC; ALL_TAC] THEN
  STRUCT_CASES_TAC(ISPEC `a:(A,data_to_word_memoryProof_tag#B)heap_element`
                         (cases "heap_element")) THEN
  CASE_REWRITE_TAC[] THENL [MP1AUX_SPLIT_LEAF_TAC; MP1AUX_SPLIT_LEAF_TAC; ALL_TAC] THEN
  COND_CASES_TAC THEN PAIRARG_TAC THEN MP1AUX_SPLIT_LEAF_TAC);;

(* HOL4 line 1337 *)
let gc_move_list_data_refs_split = prove
 (`!(cc:(data_to_word_memoryProof_tag#B)gen_gc_conf) x x1
    (s:(A,data_to_word_memoryProof_tag#B)gc_state) s1.
     gen_gc_gc_move_list cc s x = (x1,s1) /\
     (!t r. gen_gc_conf_isRef cc (t,r) <=> isMutTag t) /\
     ALL isDataElement (gc_state_h2 s) /\ ALL (\x. ~isRef x) (gc_state_h2 s) /\
     ALL isRef (gc_state_r4 s) ==>
     ALL isDataElement (gc_state_h2 s1) /\
     ALL (\x. ~isRef x) (gc_state_h2 s1) /\ ALL isRef (gc_state_r4 s1)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[gen_gc_gc_move_list_def] THENL
   [REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN PAIRARG_TAC THEN PAIRARG_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  MP_TAC(SPECL [`cc:(data_to_word_memoryProof_tag#B)gen_gc_conf`;
                `s:(A,data_to_word_memoryProof_tag#B)gc_state`; `h:A heap_address`;
                `x':A heap_address`;
                `state':(A,data_to_word_memoryProof_tag#B)gc_state`]
         gc_move_data_refs_split) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl)) THEN
  MAP_EVERY EXISTS_TAC [`xs':(A heap_address)list`;
                        `state':(A,data_to_word_memoryProof_tag#B)gc_state`] THEN
  ASM_REWRITE_TAC[]);;

(* HOL4 line 1348 *)
let gc_move_refs_data_refs_split = prove
 (`!(cc:(data_to_word_memoryProof_tag#B)gen_gc_conf)
    (s:(A,data_to_word_memoryProof_tag#B)gc_state) s1.
     gc_move_refs cc s = s1 /\
     (!t r. gen_gc_conf_isRef cc (t,r) <=> isMutTag t) /\
     ALL isDataElement (APPEND (gc_state_h1 s) (gc_state_h2 s)) /\
     ALL (\x. ~isRef x) (APPEND (gc_state_h1 s) (gc_state_h2 s)) /\
     ALL isRef (APPEND (APPEND (APPEND (gc_state_r1 s) (gc_state_r2 s))
                               (gc_state_r3 s)) (gc_state_r4 s)) ==>
     ALL isDataElement (APPEND (gc_state_h1 s1) (gc_state_h2 s1)) /\
     ALL (\x. ~isRef x) (APPEND (gc_state_h1 s1) (gc_state_h2 s1)) /\
     ALL isRef (APPEND (APPEND (APPEND (gc_state_r1 s1) (gc_state_r2 s1))
                               (gc_state_r3 s1)) (gc_state_r4 s1))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) MP_TAC) THEN
  SPEC_TAC(`s:(A,data_to_word_memoryProof_tag#B)gc_state`,
           `s:(A,data_to_word_memoryProof_tag#B)gc_state`) THEN
  SPEC_TAC(`cc:(data_to_word_memoryProof_tag#B)gen_gc_conf`,
           `cc:(data_to_word_memoryProof_tag#B)gen_gc_conf`) THEN
  MATCH_MP_TAC gc_move_refs_ind THEN
  MAP_EVERY X_GEN_TAC [`cc:(data_to_word_memoryProof_tag#B)gen_gc_conf`;
                       `s:(A,data_to_word_memoryProof_tag#B)gc_state`] THEN
  DISCH_THEN(LABEL_TAC "IH") THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[gc_move_refs_def] THEN
  MP_TAC(ISPEC `gc_state_r2 (s:(A,data_to_word_memoryProof_tag#B)gc_state)` list_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th)
    (X_CHOOSE_THEN `h:(A,data_to_word_memoryProof_tag#B)heap_element`
      (X_CHOOSE_THEN `t:((A,data_to_word_memoryProof_tag#B)heap_element)list`
        (fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th)))) THEN
  CASE_REWRITE_TAC[] THENL
   [REWRITE_TAC[gc_state_FIELDS.ri_accfupds; K_THM; ALL_APPEND; ALL] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ALL_APPEND; ALL]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `h:(A,data_to_word_memoryProof_tag#B)heap_element`
               (cases "heap_element")) THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN CASE_REWRITE_TAC[] THENL
   [REWRITE_TAC[gc_state_FIELDS.ri_accfupds; K_THM] THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[gc_state_FIELDS.ri_accfupds; K_THM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  PAIRARG_TAC THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REMOVE_THEN "IH" (MP_TAC o SPECL [`a0:(A heap_address)list`; `xs':(A heap_address)list`;
     `a1:num`; `a2:data_to_word_memoryProof_tag#B`;
     `t:((A,data_to_word_memoryProof_tag#B)heap_element)list`;
     `state':(A,data_to_word_memoryProof_tag#B)gc_state`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GSYM o MATCH_MP gen_gc_gc_move_list_IMP) THEN
  MP_TAC(SPECL [`cc:(data_to_word_memoryProof_tag#B)gen_gc_conf`;
                `a0:(A heap_address)list`; `xs':(A heap_address)list`;
                `s:(A,data_to_word_memoryProof_tag#B)gc_state`;
                `state':(A,data_to_word_memoryProof_tag#B)gc_state`]
         gc_move_list_data_refs_split) THEN
  FIRST_ASSUM(fun th -> if (try lhs(concl th) =
      `gc_state_r2 (s:(A,data_to_word_memoryProof_tag#B)gc_state)`
      with Failure _ -> false)
    then RULE_ASSUM_TAC(REWRITE_RULE[th]) else NO_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ALL_APPEND; ALL]) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  REWRITE_TAC[gc_state_FIELDS.ri_accfupds; K_THM; ALL_APPEND; ALL] THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MP1AUX_isRef_DataElement]);;

(* HOL4 line 1370 *)
let gc_move_data_data_refs_split = prove
 (`!(cc:(data_to_word_memoryProof_tag#B)gen_gc_conf)
    (s:(A,data_to_word_memoryProof_tag#B)gc_state) s1.
     gen_gc_gc_move_data cc s = s1 /\
     (!t r. gen_gc_conf_isRef cc (t,r) <=> isMutTag t) /\
     ALL (\x. ~isRef x) (APPEND (gc_state_h1 s) (gc_state_h2 s)) /\
     ALL isDataElement (APPEND (gc_state_h1 s) (gc_state_h2 s)) /\
     ALL isRef (APPEND (APPEND (APPEND (gc_state_r1 s) (gc_state_r2 s))
                               (gc_state_r3 s)) (gc_state_r4 s)) ==>
     ALL isDataElement (APPEND (gc_state_h1 s1) (gc_state_h2 s1)) /\
     ALL (\x. ~isRef x) (APPEND (gc_state_h1 s1) (gc_state_h2 s1)) /\
     ALL isRef (APPEND (APPEND (APPEND (gc_state_r1 s1) (gc_state_r2 s1))
                               (gc_state_r3 s1)) (gc_state_r4 s1))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) MP_TAC) THEN
  SPEC_TAC(`s:(A,data_to_word_memoryProof_tag#B)gc_state`,
           `s:(A,data_to_word_memoryProof_tag#B)gc_state`) THEN
  SPEC_TAC(`cc:(data_to_word_memoryProof_tag#B)gen_gc_conf`,
           `cc:(data_to_word_memoryProof_tag#B)gen_gc_conf`) THEN
  MATCH_MP_TAC gen_gc_gc_move_data_ind THEN
  MAP_EVERY X_GEN_TAC [`cc:(data_to_word_memoryProof_tag#B)gen_gc_conf`;
                       `s:(A,data_to_word_memoryProof_tag#B)gc_state`] THEN
  DISCH_THEN(LABEL_TAC "IH") THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[gen_gc_gc_move_data_def] THEN
  MP_TAC(ISPEC `gc_state_h2 (s:(A,data_to_word_memoryProof_tag#B)gc_state)` list_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th)
    (X_CHOOSE_THEN `h:(A,data_to_word_memoryProof_tag#B)heap_element`
      (X_CHOOSE_THEN `t:((A,data_to_word_memoryProof_tag#B)heap_element)list`
        (fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th)))) THEN
  CASE_REWRITE_TAC[] THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  COND_CASES_TAC THENL
   [REWRITE_TAC[gc_state_FIELDS.ri_accfupds; K_THM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `h:(A,data_to_word_memoryProof_tag#B)heap_element`
               (cases "heap_element")) THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN CASE_REWRITE_TAC[] THENL
   [REWRITE_TAC[gc_state_FIELDS.ri_accfupds; K_THM] THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[gc_state_FIELDS.ri_accfupds; K_THM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  PAIRARG_TAC THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REMOVE_THEN "IH" (MP_TAC o SPECL
    [`t:((A,data_to_word_memoryProof_tag#B)heap_element)list`;
     `a0:(A heap_address)list`; `xs':(A heap_address)list`;
     `a1:num`; `a2:data_to_word_memoryProof_tag#B`;
     `state':(A,data_to_word_memoryProof_tag#B)gc_state`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GSYM o MATCH_MP gen_gc_gc_move_list_IMP) THEN
  MP_TAC(SPECL [`cc:(data_to_word_memoryProof_tag#B)gen_gc_conf`;
                `a0:(A heap_address)list`; `xs':(A heap_address)list`;
                `s:(A,data_to_word_memoryProof_tag#B)gc_state`;
                `state':(A,data_to_word_memoryProof_tag#B)gc_state`]
         gc_move_list_data_refs_split) THEN
  ANTS_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[ALL_APPEND]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (MP1AUX_HEAD "IS_PREFIX")) THEN
  ASM_REWRITE_TAC[IS_PREFIX_DEF; IS_PREFIX_APPEND] THEN
  DISCH_THEN(X_CHOOSE_THEN `rest:((A,data_to_word_memoryProof_tag#B)heap_element)list`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th; APPEND; ALL; ALL_APPEND]) THEN
               REWRITE_TAC[th])) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ALL_APPEND; ALL]) THEN
  ASM_REWRITE_TAC[gc_state_FIELDS.ri_accfupds; K_THM; ALL_APPEND; ALL; APPEND; TL;
                  isDataElement_def] THEN
  CONJ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  ASM_MESON_TAC[MP1AUX_isRef_DataElement]);;

(* MP1AUX: the steps of gc_move_loop keep the split of the heap *)
let MP1AUX_gc_move_loop_steps = prove
 (`!(cc:(data_to_word_memoryProof_tag#B)gen_gc_conf)
    (s:(A,data_to_word_memoryProof_tag#B)gc_state).
     (!t r. gen_gc_conf_isRef cc (t,r) <=> isMutTag t) /\
     ALL isDataElement (APPEND (gc_state_h1 s) (gc_state_h2 s)) /\
     ALL (\x. ~isRef x) (APPEND (gc_state_h1 s) (gc_state_h2 s)) /\
     ALL isRef (APPEND (APPEND (APPEND (gc_state_r1 s) (gc_state_r2 s))
                               (gc_state_r3 s)) (gc_state_r4 s)) ==>
     (!s'. s' = gen_gc_gc_move_data cc s \/
           s' = gc_move_refs cc (gc_state_r4_fupd (K [])
                  (gc_state_r2_fupd (K (gc_state_r4 s)) s)) \/
           s' = gc_state_ok_fupd (K F) (gen_gc_gc_move_data cc s) \/
           s' = gc_state_ok_fupd (K F) (gc_move_refs cc (gc_state_r4_fupd (K [])
                  (gc_state_r2_fupd (K (gc_state_r4 s)) s))) ==>
           ALL isDataElement (APPEND (gc_state_h1 s') (gc_state_h2 s')) /\
           ALL (\x. ~isRef x) (APPEND (gc_state_h1 s') (gc_state_h2 s')) /\
           ALL isRef (APPEND (APPEND (APPEND (gc_state_r1 s') (gc_state_r2 s'))
                                     (gc_state_r3 s')) (gc_state_r4 s')))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cc:(data_to_word_memoryProof_tag#B)gen_gc_conf`;
                `s:(A,data_to_word_memoryProof_tag#B)gc_state`;
                `gen_gc_gc_move_data (cc:(data_to_word_memoryProof_tag#B)gen_gc_conf)
                   (s:(A,data_to_word_memoryProof_tag#B)gc_state)`]
               gc_move_data_data_refs_split) THEN
  MP_TAC(SPECL [`cc:(data_to_word_memoryProof_tag#B)gen_gc_conf`;
                `gc_state_r4_fupd (K []) (gc_state_r2_fupd
                   (K (gc_state_r4 (s:(A,data_to_word_memoryProof_tag#B)gc_state))) s)`;
                `gc_move_refs (cc:(data_to_word_memoryProof_tag#B)gen_gc_conf)
                   (gc_state_r4_fupd (K []) (gc_state_r2_fupd
                     (K (gc_state_r4 (s:(A,data_to_word_memoryProof_tag#B)gc_state))) s))`]
               gc_move_refs_data_refs_split) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ALL_APPEND]) THEN
  ASM_REWRITE_TAC[gc_state_FIELDS.ri_accfupds; K_THM; ALL_APPEND; ALL] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[gc_state_FIELDS.ri_accfupds; K_THM]);;

(* MP1AUX: rewrite the other assumptions with the assumption tm = t *)
let MP1AUX_REWRITE_ASMS_WITH tm =
  FIRST_ASSUM(fun th -> if (try lhs(concl th) = tm with Failure _ -> false)
    then RULE_ASSUM_TAC(fun a -> if concl a = concl th then a else REWRITE_RULE[th] a)
    else NO_TAC);;

(* HOL4 line 1392 *)
let gc_move_loop_data_refs_split = prove
 (`!clock (cc:(data_to_word_memoryProof_tag#B)gen_gc_conf)
    (s:(A,data_to_word_memoryProof_tag#B)gc_state) s1.
     gen_gc_gc_move_loop cc s clock = s1 /\
     (!t r. gen_gc_conf_isRef cc (t,r) <=> isMutTag t) /\
     ALL isDataElement (APPEND (gc_state_h1 s) (gc_state_h2 s)) /\
     ALL (\x. ~isRef x) (APPEND (gc_state_h1 s) (gc_state_h2 s)) /\
     ALL isRef (APPEND (APPEND (APPEND (gc_state_r1 s) (gc_state_r2 s))
                               (gc_state_r3 s)) (gc_state_r4 s)) ==>
     ALL isDataElement (APPEND (gc_state_h1 s1) (gc_state_h2 s1)) /\
     ALL (\x. ~isRef x) (APPEND (gc_state_h1 s1) (gc_state_h2 s1)) /\
     ALL isRef (APPEND (APPEND (APPEND (gc_state_r1 s1) (gc_state_r2 s1))
                               (gc_state_r3 s1)) (gc_state_r4 s1))`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) MP_TAC) THEN
  SPEC_TAC(`s:(A,data_to_word_memoryProof_tag#B)gc_state`,
           `s:(A,data_to_word_memoryProof_tag#B)gc_state`) THEN
  SPEC_TAC(`cc:(data_to_word_memoryProof_tag#B)gen_gc_conf`,
           `cc:(data_to_word_memoryProof_tag#B)gen_gc_conf`) THEN
  SPEC_TAC(`clock:num`,`clock:num`) THEN
  INDUCT_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MP1AUX_gc_move_loop_steps) THEN
  ONCE_REWRITE_TAC[gen_gc_gc_move_loop_def] THEN
  CASES_ON `gc_state_r4 (s:(A,data_to_word_memoryProof_tag#B)gc_state)` THEN
  CASE_REWRITE_TAC[] THENL
   [CASES_ON `gc_state_h2 (s:(A,data_to_word_memoryProof_tag#B)gc_state)` THEN
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THENL
     [ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl)) THEN REWRITE_TAC[]];
    MP1AUX_REWRITE_ASMS_WITH
      `gc_state_r4 (s:(A,data_to_word_memoryProof_tag#B)gc_state)` THEN
    REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl)) THEN REWRITE_TAC[];
    CASES_ON `gc_state_h2 (s:(A,data_to_word_memoryProof_tag#B)gc_state)` THEN
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[LET_DEF; LET_END_DEF; SUC_SUB1] THENL
     [ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        is_forall(snd(dest_forall(concl th))))) THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl)) THEN REWRITE_TAC[]];
    MP1AUX_REWRITE_ASMS_WITH
      `gc_state_r4 (s:(A,data_to_word_memoryProof_tag#B)gc_state)` THEN
    REWRITE_TAC[LET_DEF; LET_END_DEF; SUC_SUB1] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      is_forall(snd(dest_forall(concl th))))) THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl)) THEN REWRITE_TAC[]]);;

(* HOL4 line 1418 *)
let gen_gc_data_refs_split = prove
 (`!roots1 (s:(A,data_to_word_memoryProof_tag#B)gc_state)
    (cc:(data_to_word_memoryProof_tag#B)gen_gc_conf) roots heap.
     gen_gc cc (roots,heap) = (roots1,s) /\
     (!t r. gen_gc_conf_isRef cc (t,r) <=> isMutTag t) ==>
     ALL (\x. ~isRef x) (APPEND (gc_state_h1 s) (gc_state_h2 s)) /\
     ALL isDataElement (APPEND (gc_state_h1 s) (gc_state_h2 s)) /\
     ALL isRef (APPEND (APPEND (APPEND (gc_state_r1 s) (gc_state_r2 s))
                               (gc_state_r3 s)) (gc_state_r4 s))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[gen_gc_def; LET_DEF; LET_END_DEF] THEN
  PAIRARG_TAC THEN REWRITE_TAC[LET_DEF; LET_END_DEF; PAIR_EQ] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cc:(data_to_word_memoryProof_tag#B)gen_gc_conf`;
                `roots:(A heap_address)list`; `roots':(A heap_address)list`;
                `gc_state_ok_fupd (K (heap_length
                   (heap:((A,data_to_word_memoryProof_tag#B)heap_element)list) =
                   gen_gc_conf_limit (cc:(data_to_word_memoryProof_tag#B)gen_gc_conf)))
                   (gc_state_n_fupd (K (gen_gc_conf_limit cc))
                   (gc_state_heap_fupd (K heap) empty_state))`;
                `state':(A,data_to_word_memoryProof_tag#B)gc_state`]
         gc_move_list_data_refs_split) THEN
  ASM_REWRITE_TAC[empty_state_def; gc_state_FIELDS.ri_accfupds;
                  gc_state_FIELDS.ri_accessors; K_THM; ALL] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP gen_gc_gc_move_list_IMP) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[empty_state_def; gc_state_FIELDS.ri_accfupds;
                              gc_state_FIELDS.ri_accessors; K_THM]) THEN
  MP_TAC(SPECL [`gen_gc_conf_limit (cc:(data_to_word_memoryProof_tag#B)gen_gc_conf)`;
                `cc:(data_to_word_memoryProof_tag#B)gen_gc_conf`;
                `state':(A,data_to_word_memoryProof_tag#B)gc_state`;
                `s:(A,data_to_word_memoryProof_tag#B)gc_state`]
         gc_move_loop_data_refs_split) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
     lhs(concl th) = `[]:((A,data_to_word_memoryProof_tag#B)heap_element)list`))) THEN
  ASM_REWRITE_TAC[APPEND; ALL] THEN MESON_TAC[]);;

(* HOL4 line 1436 *)
let heap_expand_not_isRef = prove
 (`!n. ALL (\x. ~isRef x)
           (heap_expand n:((A,data_to_word_memoryProof_tag#B)heap_element)list)`,
  GEN_TAC THEN REWRITE_TAC[heap_expand_def] THEN COND_CASES_TAC THEN
  REWRITE_TAC[ALL; isRef_def]);;

(* HOL4 line 1442 *)
let reset_gens_def = cake_def
  `reset_gens conf a =
     match data_to_word_config_gc_kind conf with
       Generational sizes -> GenState 0 (MAP (K a) sizes)
     | _ -> GenState 0 []`;;

(* HOL4 line 1449 *)
let gen_state_ok_reset = prove
 (`!(h:((A,B)heap_element)list) n r l conf.
     heap_ok (APPEND (APPEND h (heap_expand n)) r) l ==>
     gen_state_ok (heap_length h) (n + heap_length h)
       (APPEND (APPEND h (heap_expand n)) r) (reset_gens conf (heap_length h))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[reset_gens_def] THEN
  CASES_ON `data_to_word_config_gc_kind conf` THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[gen_state_ok_def; ALL; EVERY_MAP; K_THM; LE_REFL; ALL_T] THEN
  SUBGOAL_THEN
   `gen_start_ok (APPEND (APPEND h (heap_expand n)) (r:((A,B)heap_element)list))
      (n + heap_length h) (heap_length h)`
   (fun th -> REWRITE_TAC[th; ALL_T]) THEN
  REWRITE_TAC[gen_start_ok_def; GSYM APPEND_ASSOC; heap_split_length] THEN
  MAP_EVERY EXISTS_TAC [`h:((A,B)heap_element)list`;
                        `APPEND (heap_expand n) (r:((A,B)heap_element)list)`] THEN
  REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [heap_ok_def]) THEN
  DISCH_THEN(MP_TAC o SPECL [`xs:(A heap_address)list`; `l':num`; `d:B`;
                             `p:num`; `e:A`] o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[MEM_APPEND] THEN
  ASM_CASES_TAC `p < heap_length (h:((A,B)heap_element)list)` THEN
  ASM_REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  ASM_SIMP_TAC[NOT_LESS_IMP_heap_lookup] THEN
  REWRITE_TAC[heap_expand_def] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[APPEND] THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[heap_lookup_def; el_length_def; isSomeDataElement_def] THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[option_INJ; distinctness "heap_element"; option_DISTINCT] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT] THEN ASM_ARITH_TAC);;

(* HOL4 line 1471: gen_gc_thm *)
let data_to_word_memoryProof_gen_gc_thm = prove
 (`!conf stack refs roots
    heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
          heap_element)list be a sp sp1 gens limit ts.
     abs_ml_inv conf stack refs (roots,heap,be,a,sp,sp1,gens) limit ts ==>
     ?roots2 state2.
       gen_gc (make_gc_conf limit) (roots,heap) = (roots2,state2) /\
       abs_ml_inv conf stack refs
         (roots2,APPEND (APPEND (gc_state_h1 state2)
                                (heap_expand (gc_state_n state2)))
                        (gc_state_r1 state2),be,
          gc_state_a state2,gc_state_n state2,0,
          reset_gens conf (gc_state_a state2)) limit ts /\
       gc_state_ok state2 /\
       heap_length (APPEND (gc_state_h1 state2) (gc_state_r1 state2)) =
       heap_length (heap_filter (reachable_addresses roots heap) heap) /\
       ALL isDataElement (gc_state_h1 state2) /\
       ALL isDataElement (gc_state_r1 state2) /\
       all_reachable_from_roots roots2
         (APPEND (APPEND (gc_state_h1 state2) (heap_expand (gc_state_n state2)))
                 (gc_state_r1 state2))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[abs_ml_inv_def] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`make_gc_conf limit:(data_to_word_memoryProof_tag#((A)word_loc)list)
                                      gen_gc_conf`;
                 `roots:(((A)word_loc)heap_address)list`;
                 `heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
                        heap_element)list`] gen_gc_related) THEN
  MP_TAC(ISPECL [`make_gc_conf limit:(data_to_word_memoryProof_tag#((A)word_loc)list)
                                      gen_gc_conf`;
                 `roots:(((A)word_loc)heap_address)list`;
                 `heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
                        heap_element)list`] gen_gc_ok) THEN
  ASM_REWRITE_TAC[MP1AUX_make_gc_conf] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`ADDR_MAP (FAPPLY (f:(num,num)fmap)) (roots:(((A)word_loc)heap_address)list)`;
    `state':(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)gc_state)`] THEN
  REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`ADDR_MAP (FAPPLY (f:(num,num)fmap)) (roots:(((A)word_loc)heap_address)list)`;
    `state':(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)gc_state)`;
    `make_gc_conf limit:(data_to_word_memoryProof_tag#((A)word_loc)list)gen_gc_conf`;
    `roots:(((A)word_loc)heap_address)list`;
    `heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list`]
    gen_gc_data_refs_split) THEN
  ASM_REWRITE_TAC[MP1AUX_make_gc_conf] THEN
  REWRITE_TAC[ALL_APPEND] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ALL_APPEND]) THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[gc_kind_inv_def] THEN
  CASES_ON `data_to_word_config_gc_kind conf` THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[ADD_CLAUSES] THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[ADD_SYM] THEN MATCH_MP_TAC gen_state_ok_reset THEN
    EXISTS_TAC `limit:num` THEN ASM_REWRITE_TAC[];
    MAP_EVERY EXISTS_TAC
     [`APPEND (gc_state_h1 (state':(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)gc_state)))
              (heap_expand (gc_state_n state'))`;
      `gc_state_r1 (state':(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)gc_state))`] THEN
    REWRITE_TAC[GSYM(REWRITE_CONV[heap_length_APPEND; gc_shared_heap_length_heap_expand]
      `heap_length (APPEND (gc_state_h1 (state':(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)gc_state)))
                          (heap_expand (gc_state_n state')))`)] THEN
    ASM_REWRITE_TAC[heap_split_length; ALL_APPEND; heap_expand_not_isRef]];
    REWRITE_TAC[unused_space_inv_def; ADD_CLAUSES; GSYM APPEND_ASSOC;
              MP1AUX_heap_lookup_heap_length; data_up_to_APPEND; heap_length_APPEND;
              gc_shared_heap_length_heap_expand] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[heap_expand_def] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[APPEND; heap_lookup_def];
    ARITH_TAC];
    MATCH_MP_TAC MP1AUX_bc_stack_ref_inv_gc THEN
  EXISTS_TAC `heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
                    heap_element)list` THEN
  ASM_REWRITE_TAC[IN_reachable_addresses] THEN MESON_TAC[RTC_REFL];
    MATCH_MP_TAC IMP_all_reachable_from_roots THEN
  EXISTS_TAC `heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
                    heap_element)list` THEN
  ASM_REWRITE_TAC[]]);;

(* HOL4 line 1529 *)
let has_gen_def = cake_def
  `has_gen (GenState _ xs) <=> ~(xs = [])`;;

(* MP1AUX: a heap of length 0 is empty *)
let MP1AUX_heap_length_0 = prove
 (`!l:((A,B)heap_element)list. heap_length l = 0 <=> l = []`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[heap_length_NIL; GC1AUX_heap_length_CONS; NOT_CONS_NIL] THEN
  MP_TAC(ISPEC `h:(A,B)heap_element` el_length_GT_0) THEN ARITH_TAC);;

(* HOL4 line 1533 *)
let heap_split_heap_split = prove
 (`!(heap:((A,B)heap_element)list) n1 n2 h1 h2 h3 h4.
     heap_split n2 heap = SOME (h3,h4) /\
     heap_split n1 heap = SOME (h1,h2) /\ n1 <= n2 ==>
     ?m. h2 = APPEND m h4 /\ h3 = APPEND h1 m /\
         heap = APPEND (APPEND h1 m) h4 /\
         heap_split (n2 - heap_length h1) h2 = SOME (m,h4)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP heap_split_heap_length o
                       check (MP1AUX_HEAD "="))) THEN
  SUBGOAL_THEN `APPEND h1 h2 = APPEND h3 (h4:((A,B)heap_element)list)` MP_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[APPEND_EQ_APPEND] THEN
  DISCH_THEN(DISJ_CASES_THEN (X_CHOOSE_THEN `l:((A,B)heap_element)list`
    STRIP_ASSUME_TAC)) THENL
   [SUBGOAL_THEN `l:((A,B)heap_element)list = []` SUBST_ALL_TAC THENL
     [REWRITE_TAC[GSYM MP1AUX_heap_length_0] THEN
      UNDISCH_TAC `heap_length (h1:((A,B)heap_element)list) = n1` THEN
      UNDISCH_TAC `heap_length (h3:((A,B)heap_element)list) = n2` THEN
      ASM_REWRITE_TAC[heap_length_APPEND] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[APPEND; APPEND_NIL]) THEN
    EXISTS_TAC `[]:((A,B)heap_element)list` THEN
    ASM_REWRITE_TAC[APPEND; APPEND_NIL; SUB_REFL; heap_split_0] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `APPEND h3 h4 = heap:((A,B)heap_element)list` THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[];
      SUBGOAL_THEN `n2:num = n1` SUBST1_TAC THENL
       [UNDISCH_TAC `heap_length (h1:((A,B)heap_element)list) = n1` THEN
        UNDISCH_TAC `heap_length (h3:((A,B)heap_element)list) = n2` THEN
        ASM_REWRITE_TAC[] THEN ARITH_TAC;
        REWRITE_TAC[SUB_REFL; heap_split_0]]];
    EXISTS_TAC `l:((A,B)heap_element)list` THEN
    ASM_REWRITE_TAC[GSYM APPEND_ASSOC] THEN
    UNDISCH_TAC `heap_length (h3:((A,B)heap_element)list) = n2` THEN
    ASM_REWRITE_TAC[heap_length_APPEND] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[ADD_SUB2; heap_split_length] THEN
    UNDISCH_TAC `APPEND h1 h2 = heap:((A,B)heap_element)list` THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[]]);;

(* HOL4 line 1560 *)
let heap_split_LESS_EQ = prove
 (`!(heap:((A,B)heap_element)list) n x.
     heap_split n heap = SOME x ==> n <= heap_length heap`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`h1:((A,B)heap_element)list`; `h2:((A,B)heap_element)list`] THEN
  DISCH_THEN(MP_TAC o MATCH_MP heap_split_heap_length) THEN
  REWRITE_TAC[heap_length_APPEND] THEN
  MP_TAC(ARITH_RULE `!a b c n:num. a = n /\ a + b = c ==> n <= c`) THEN
  MESON_TAC[]);;

(* HOL4 line 1568 *)
let isRef_heap_expand = prove
 (`!x. ALL (\x. ~isRef x)
           (heap_expand x:((A,data_to_word_memoryProof_tag#B)heap_element)list)`,
  REWRITE_TAC[heap_expand_not_isRef]);;

let MP1AUX_isRef_FST = prove
 (`!(xs:(A heap_address)list) l (d:data_to_word_memoryProof_tag#B).
     isRef (DataElement xs l d) <=> isMutTag (FST d)`,
  REPEAT GEN_TAC THEN
  SUBST1_TAC(ISPEC `d:data_to_word_memoryProof_tag#B` (GSYM PAIR)) THEN
  REWRITE_TAC[isRef_def]);;

let MP1AUX_isRef_isDataElement = prove
 (`!x:(A,data_to_word_memoryProof_tag#B)heap_element. isRef x ==> isDataElement x`,
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `x:(A,data_to_word_memoryProof_tag#B)heap_element`
                                        (cases "heap_element")) THEN
  REWRITE_TAC[isRef_def; isDataElement_def] THEN MESON_TAC[]);;

let MP1AUX_similar_data_isRef = prove
 (`!(c:C) (refs:((P,data_to_word_memoryProof_tag#Q)heap_element)list) r1.
     ALL2 (similar_data c) refs r1 /\ ALL isRef refs ==> ALL isRef r1`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[ALL2; ALL] THEN
  STRIP_TAC THEN CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  UNDISCH_TAC `isRef (h:(P,data_to_word_memoryProof_tag#Q)heap_element)` THEN
  UNDISCH_TAC `similar_data (c:C) (h:(P,data_to_word_memoryProof_tag#Q)heap_element) h'` THEN
  STRUCT_CASES_TAC(ISPEC `h:(P,data_to_word_memoryProof_tag#Q)heap_element` (cases "heap_element")) THEN
  STRUCT_CASES_TAC(ISPEC `h':(P,data_to_word_memoryProof_tag#Q)heap_element` (cases "heap_element")) THEN
  REWRITE_TAC[similar_data_def; isRef_def; distinctness "heap_element"; MP1AUX_isRef_FST] THEN
  MESON_TAC[]);;

let MP1AUX_roots_ok_gc = prove
 (`!(g:(num,num)fmap) (heap:((A,B)heap_element)list) heap2 roots.
     gc_related g heap heap2 /\ (!ptr u. MEM (Pointer ptr u) roots ==> ptr IN FDOM g) ==>
     roots_ok (ADDR_MAP (FAPPLY g) roots) heap2`,
  REWRITE_TAC[roots_ok_def; gc_related_def; INJ; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP MEM_ADDR_MAP) THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ASM_MESON_TAC[]);;

(* HOL4 line 1574 *)
let gen_gc_partial_thm = prove
 (`!conf stack refs roots
    heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
          heap_element)list be a sp sp1 gens limit ts xs.
     abs_ml_inv conf stack refs (roots,heap,be,a,sp,sp1,gens) limit ts /\
     has_gen gens /\ data_to_word_config_gc_kind conf = Generational xs ==>
     ?roots2 state2.
       partial_gc
         (make_partial_conf (make_gc_conf limit) gens (a + (sp + sp1)))
         (roots,heap) = (roots2,state2) /\
       abs_ml_inv conf stack refs
         (roots2,APPEND (APPEND (APPEND (gc_state_old state2)
                                        (gc_state_h1 state2))
                                (heap_expand (gc_state_n state2)))
                        (gc_state_r1 state2),be,
          gc_state_a state2,gc_state_n state2,0,
          reset_gens conf (gc_state_a state2)) limit ts /\
       gc_state_ok state2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[abs_ml_inv_def] THEN
  STRUCT_CASES_TAC(ISPEC `gens:gen_state` (cases "gen_state")) THEN
  REWRITE_TAC[has_gen_def] THEN
  STRUCT_CASES_TAC(ISPEC `a1:num list` list_CASES) THEN
  REWRITE_TAC[NOT_CONS_NIL] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[gc_kind_inv_def]) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_comb(concl th) &&
    can (find_term (fun t -> try fst(dest_const t) = "gen_state_ok"
                             with Failure _ -> false)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[gen_state_ok_def; ALL] THEN STRIP_TAC THEN
  ABBREV_TAC `cc = make_partial_conf (make_gc_conf limit:(data_to_word_memoryProof_tag#
                     ((A)word_loc)list)gen_gc_conf) (GenState a0 (CONS h t)) (a + sp + sp1)` THEN
  SUBGOAL_THEN `gen_gc_partial_conf_limit (cc:(data_to_word_memoryProof_tag#
                  ((A)word_loc)list)gen_gc_partial_conf) = limit /\
                gen_gc_partial_conf_gen_start cc = h /\
                gen_gc_partial_conf_refs_start cc = a + sp + sp1 /\
                (!d. gen_gc_partial_conf_isRef cc d <=> isMutTag (FST d))`
    STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "cc" THEN
    REWRITE_TAC[make_partial_conf_def; make_gc_conf_def; HD;
                gen_gc_partial_conf_FIELDS.ri_accessors;
                gen_gc_conf_FIELDS.ri_accessors; o_THM];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `ha:(((A)word_loc,data_to_word_memoryProof_tag#
                                   ((A)word_loc)list)heap_element)list`
    (X_CHOOSE_THEN `hb:(((A)word_loc,data_to_word_memoryProof_tag#
                         ((A)word_loc)list)heap_element)list`
      STRIP_ASSUME_TAC) o GEN_REWRITE_RULE I [gen_start_ok_def] o
    check (MP1AUX_HEAD "gen_start_ok")) THEN
  MP_TAC(ISPECL [`heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list`;
    `h:num`; `a + sp + sp1:num`;
    `ha:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list`;
    `hb:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list`;
    `h1:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list`;
    `h2:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list`]
    heap_split_heap_split) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:(((A)word_loc,data_to_word_memoryProof_tag#
                                 ((A)word_loc)list)heap_element)list`
    STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o check (MP1AUX_HEAD "unused_space_inv")) THEN
  REWRITE_TAC[unused_space_inv_def; data_up_to_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `hx:(((A)word_loc,data_to_word_memoryProof_tag#
                         ((A)word_loc)list)heap_element)list`
      (X_CHOOSE_THEN `hy:(((A)word_loc,data_to_word_memoryProof_tag#
                           ((A)word_loc)list)heap_element)list`
        STRIP_ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list`;
    `h:num`; `a:num`;
    `ha:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list`;
    `hb:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list`;
    `hx:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list`;
    `hy:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list`]
    heap_split_heap_split) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `m':(((A)word_loc,data_to_word_memoryProof_tag#
                                  ((A)word_loc)list)heap_element)list`
    STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `heap_gen_ok (heap:(((A)word_loc,data_to_word_memoryProof_tag#
                   ((A)word_loc)list)heap_element)list) cc` ASSUME_TAC THENL
   [REWRITE_TAC[heap_gen_ok_def] THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC
     [`ha:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list`;
      `m:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list`;
      `h2:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ALL_APPEND]) THEN
    UNDISCH_TAC `heap_ok (heap:(((A)word_loc,data_to_word_memoryProof_tag#
                    ((A)word_loc)list)heap_element)list) limit` THEN
    REWRITE_TAC[heap_ok_def] THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC;
      ASM_ARITH_TAC;
      UNDISCH_TAC `ALL isDataElement (hx:(((A)word_loc,data_to_word_memoryProof_tag#
                     ((A)word_loc)list)heap_element)list)` THEN
      ASM_REWRITE_TAC[ALL_APPEND] THEN SIMP_TAC[];
      RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_MEM]) THEN REWRITE_TAC[GSYM ALL_MEM] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC MP1AUX_isRef_isDataElement THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `heap_segment (h,a + sp + sp1) (heap:(((A)word_loc,
                      data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list) =
                    SOME (ha,m,h2)` MP_TAC THENL
       [UNDISCH_TAC `heap_split ((a + sp + sp1) - heap_length (ha:(((A)word_loc,
                       data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list))
                       (hb:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
                           heap_element)list) =
                     SOME (m,h2:(((A)word_loc,data_to_word_memoryProof_tag#
                                 ((A)word_loc)list)heap_element)list)` THEN
        UNDISCH_TAC `heap_split h (heap:(((A)word_loc,data_to_word_memoryProof_tag#
                       ((A)word_loc)list)heap_element)list) =
                     SOME (ha,hb:(((A)word_loc,data_to_word_memoryProof_tag#
                                  ((A)word_loc)list)heap_element)list)` THEN
        REWRITE_TAC[heap_segment_def] THEN
        DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN CASE_REWRITE_TAC[] THEN
        DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
        SUBGOAL_THEN `~(a + sp + sp1 < h)` (fun th -> REWRITE_TAC[th]) THENL
         [ASM_ARITH_TAC; ALL_TAC] THEN
        CASE_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `APPEND (APPEND ha m') hy = heap:(((A)word_loc,
                      data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list`
        SUBST1_TAC THENL [ASM_REWRITE_TAC[]; MESON_TAC[]];
      FIRST_ASSUM(fun th -> if is_forall(concl th) &&
        can (find_term ((=) `ha:(((A)word_loc,data_to_word_memoryProof_tag#
                                 ((A)word_loc)list)heap_element)list`)) (concl th)
        then MESON_TAC[th] else NO_TAC);
      UNDISCH_TAC `ALL (\x. ~isRef x) (h1:(((A)word_loc,data_to_word_memoryProof_tag#
                     ((A)word_loc)list)heap_element)list)` THEN
      ASM_REWRITE_TAC[ALL_APPEND; GSYM ALL_MEM] THEN BETA_TAC THEN
      REWRITE_TAC[MEM_APPEND] THEN MESON_TAC[MP1AUX_isRef_FST];
      UNDISCH_TAC `ALL (\x. ~isRef x) (h1:(((A)word_loc,data_to_word_memoryProof_tag#
                     ((A)word_loc)list)heap_element)list)` THEN
      ASM_REWRITE_TAC[GSYM ALL_MEM] THEN BETA_TAC THEN REWRITE_TAC[MEM_APPEND] THEN
      MESON_TAC[MP1AUX_isRef_FST];
      UNDISCH_TAC `ALL isRef (h2:(((A)word_loc,data_to_word_memoryProof_tag#
                     ((A)word_loc)list)heap_element)list)` THEN
      REWRITE_TAC[GSYM ALL_MEM] THEN MESON_TAC[MP1AUX_isRef_FST]];
    ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
     let fv = frees(concl th) in
     exists (fun v -> try fst(dest_var v) = "m'" || fst(dest_var v) = "hy" || fst(dest_var v) = "hx"
                      with Failure _ -> false) fv))) THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> try lhs(concl th) = `heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list` with Failure _ -> false)) THEN
  FIRST_ASSUM(fun th -> if (try rhs(concl th) = `heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list` with Failure _ -> false)
    then REWRITE_TAC[th] else NO_TAC) THEN
  SUBGOAL_THEN `heap_segment (h,a + sp + sp1) (heap:(((A)word_loc,
                      data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list) =
                    SOME (ha,m,h2)` ASSUME_TAC THENL
       [UNDISCH_TAC `heap_split ((a + sp + sp1) - heap_length (ha:(((A)word_loc,
                       data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list))
                       (hb:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
                           heap_element)list) =
                     SOME (m,h2:(((A)word_loc,data_to_word_memoryProof_tag#
                                 ((A)word_loc)list)heap_element)list)` THEN
        UNDISCH_TAC `heap_split h (heap:(((A)word_loc,data_to_word_memoryProof_tag#
                       ((A)word_loc)list)heap_element)list) =
                     SOME (ha,hb:(((A)word_loc,data_to_word_memoryProof_tag#
                                  ((A)word_loc)list)heap_element)list)` THEN
        REWRITE_TAC[heap_segment_def] THEN
        DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN CASE_REWRITE_TAC[] THEN
        DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
        SUBGOAL_THEN `~(a + sp + sp1 < h)` (fun th -> REWRITE_TAC[th]) THENL
         [ASM_ARITH_TAC; ALL_TAC] THEN
        CASE_REWRITE_TAC[];
        ALL_TAC] THEN
  MP_TAC(ISPECL [`roots:(((A)word_loc)heap_address)list`;
    `heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list`;
    `cc:(data_to_word_memoryProof_tag#((A)word_loc)list)gen_gc_partial_conf`]
    partial_gc_related) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s2:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)gc_state)`
    (X_CHOOSE_THEN `g:(num,num)fmap` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`cc:(data_to_word_memoryProof_tag#((A)word_loc)list)gen_gc_partial_conf`;
    `roots:(((A)word_loc)heap_address)list`;
    `heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list`;
    `ADDR_MAP (FAPPLY (g:(num,num)fmap)) (roots:(((A)word_loc)heap_address)list)`;
    `s2:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)gc_state)`]
    partial_gc_IMP) THEN
  ASM_REWRITE_TAC[injectivity "option"; PAIR_EQ] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> try rhs(concl th) = `heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list` with Failure _ -> false)) THEN
  RVEQ_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`ADDR_MAP (FAPPLY (g:(num,num)fmap)) (roots:(((A)word_loc)heap_address)list)`;
    `s2:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)gc_state)`] THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `gc_state_a (s2:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)gc_state)) =
                heap_length (APPEND (gc_state_old s2) (gc_state_h1 s2))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[heap_length_APPEND]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [(* roots_ok *)
    MATCH_MP_TAC MP1AUX_roots_ok_gc THEN
  EXISTS_TAC `heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list` THEN
  ASM_REWRITE_TAC[];
    (* gc_kind_inv *)
    REWRITE_TAC[gc_kind_inv_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[ADD_CLAUSES; GSYM heap_length_APPEND] THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[ADD_SYM] THEN MATCH_MP_TAC gen_state_ok_reset THEN
    EXISTS_TAC `gen_gc_partial_conf_limit (cc:(data_to_word_memoryProof_tag#((A)word_loc)list)gen_gc_partial_conf)` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC
   [`APPEND (APPEND (gc_state_old (s2:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)gc_state)))
                    (gc_state_h1 s2)) (heap_expand (gc_state_n s2))`;
    `gc_state_r1 (s2:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)gc_state))`] THEN
  SUBGOAL_THEN
   `heap_length (APPEND (gc_state_old (s2:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)gc_state)))
                        (gc_state_h1 s2)) + gc_state_n s2 =
    heap_length (APPEND (APPEND (gc_state_old s2) (gc_state_h1 s2)) (heap_expand (gc_state_n s2)))`
   SUBST1_TAC THENL
   [REWRITE_TAC[heap_length_APPEND; gc_shared_heap_length_heap_expand]; ALL_TAC] THEN
  REWRITE_TAC[heap_split_length; ALL_APPEND; heap_expand_not_isRef] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ALL_APPEND]) THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC(INST_TYPE [`:(data_to_word_memoryProof_tag#((A)word_loc)list)gen_gc_partial_conf`,`:C`] MP1AUX_similar_data_isRef) THEN
    MAP_EVERY EXISTS_TAC [`cc:(data_to_word_memoryProof_tag#((A)word_loc)list)gen_gc_partial_conf`;
      `refs':(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list`] THEN
    ASM_REWRITE_TAC[]] THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN
  X_GEN_TAC `x:((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `isDataElement (x:((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)`
    MP_TAC THENL
   [UNDISCH_TAC `ALL isDataElement (gc_state_h1 (s2:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)gc_state)))` THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[isDataElement_def] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[MP1AUX_isRef_FST] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`ys:(((A)word_loc)heap_address)list`; `l:num`;
    `d:data_to_word_memoryProof_tag#((A)word_loc)list`] o
    check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `curr:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `ALL (\x. ~isRef x) (gc_state_old (s2:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)gc_state))) /\ ALL (\x. ~isRef x) (curr:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list)` THEN
  REWRITE_TAC[GSYM ALL_MEM] THEN
  DISCH_THEN(MP_TAC o SPEC `DataElement xs' l' d':((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element` o CONJUNCT2) THEN
  ASM_REWRITE_TAC[MP1AUX_isRef_FST];
    (* unused_space_inv *)
    REWRITE_TAC[ADD_CLAUSES; heap_expand_def] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  ONCE_REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  REWRITE_TAC[APPEND; GSYM heap_length_APPEND; heap_lookup_PREFIX];
    REWRITE_TAC[heap_length_APPEND; gc_shared_heap_length_heap_expand] THEN ARITH_TAC;
    SUBGOAL_THEN `ALL isDataElement (gc_state_old (s2:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)gc_state)))` ASSUME_TAC THENL
  [FIRST_ASSUM(MP_TAC o REWRITE_RULE[heap_gen_ok_def] o check (MP1AUX_HEAD "heap_gen_ok")) THEN
   ASM_REWRITE_TAC[option_INJ; PAIR_EQ] THEN MESON_TAC[];
   ALL_TAC] THEN
  REWRITE_TAC[GSYM data_up_to_def] THEN
  ONCE_REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  ASM_REWRITE_TAC[GSYM heap_length_APPEND; data_up_to_APPEND; ALL_APPEND];
    (* bc_stack_ref_inv *)
    MATCH_MP_TAC MP1AUX_bc_stack_ref_inv_gc THEN
  EXISTS_TAC `heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list` THEN
  ASM_REWRITE_TAC[]]);;

(* HOL4 line 1715 (the variable x of the second clause is xs here: in one *)
(* quotation a variable has one type)                                       *)
let data_pointers_def = cake_def
  `(data_pointers ([]:((A,B)heap_element)list) = []) /\
   (data_pointers (CONS (DataElement xs y z) rest) =
      CONS 0 (MAP (\n. n + el_length (DataElement xs y z)) (data_pointers rest))) /\
   (data_pointers (CONS x rest) =
      MAP (\n. n + el_length x) (data_pointers rest))`;;

let data_pointers_ind = cake_ind "data_pointers";;

(* HOL4 line 1723 *)
let lookup_len_def = cake_def
  `lookup_len (heap:((A,B)heap_element)list) p =
     match heap_lookup p heap with NONE -> 0 | SOME x -> el_length x`;;

(* HOL4 line 1728 *)
let data_length_def = cake_def
  `data_length (heap:((A,B)heap_element)list) =
     SUM (MAP (lookup_len heap) (data_pointers heap))`;;

(* MP1AUX: lookup_len of a cons, past its head *)
let MP1AUX_lookup_len_CONS = prove
 (`!(x:(A,B)heap_element) xs n.
     lookup_len (CONS x xs) (n + el_length x) = lookup_len xs n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lookup_len_def; heap_lookup_def] THEN
  MP_TAC(ISPEC `x:(A,B)heap_element` el_length_GT_0) THEN DISCH_TAC THEN
  ASM_SIMP_TAC[ARITH_RULE
    `1 <= e ==> ~(n + e = 0) /\ ~(n + e < e) /\ (n + e) - e = n`]);;

(* MP1AUX: the sum of lookup_len over the shifted data pointers *)
let MP1AUX_SUM_lookup_len_CONS = prove
 (`!(x:(A,B)heap_element) xs l.
     SUM (MAP (lookup_len (CONS x xs)) (MAP (\n. n + el_length x) l)) =
     SUM (MAP (lookup_len xs) l)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[MAP; SUM; MP1AUX_lookup_len_CONS]);;

(* MP1AUX: the data pointers of a heap are inside it *)
let MP1AUX_MEM_data_pointers = prove
 (`!heap:((A,B)heap_element)list p.
     MEM p (data_pointers heap) ==> p < heap_length heap`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[data_pointers_def; MEM] THEN
  MP_TAC(ISPEC `h:(A,B)heap_element` el_length_GT_0) THEN
  STRUCT_CASES_TAC(ISPEC `h:(A,B)heap_element` (cases "heap_element")) THEN
  REWRITE_TAC[data_pointers_def; MEM; MEM_MAP; heap_length_def; MAP; SUM] THEN
  REWRITE_TAC[GSYM heap_length_def] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN RES_TAC THEN ASM_ARITH_TAC);;

(* HOL4 line 1733 *)
let data_pointers_heap_expand = prove
 (`!(heap:((A,B)heap_element)list) n.
     data_pointers (APPEND heap (heap_expand n)) = data_pointers heap`,
  LIST_INDUCT_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[APPEND; heap_expand_def] THEN COND_CASES_TAC THEN
    REWRITE_TAC[data_pointers_def; MAP];
    GEN_TAC THEN REWRITE_TAC[APPEND] THEN
    STRUCT_CASES_TAC(ISPEC `h:(A,B)heap_element` (cases "heap_element")) THEN
    ASM_REWRITE_TAC[data_pointers_def]]);;

(* HOL4 line 1744 *)
let data_length_APPEND_heap_expand = prove
 (`!(heap:((A,B)heap_element)list) n.
     data_length (APPEND heap (heap_expand n)) = data_length heap`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_length_def; data_pointers_heap_expand] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC MAP_EQ THEN REWRITE_TAC[GSYM ALL_MEM] THEN
  X_GEN_TAC `p:num` THEN DISCH_TAC THEN REWRITE_TAC[lookup_len_def] THEN
  SUBGOAL_THEN
   `heap_lookup p (APPEND heap (heap_expand n)) =
    heap_lookup p (heap:((A,B)heap_element)list)` SUBST1_TAC THENL
   [MATCH_MP_TAC gc_shared_LESS_IMP_heap_lookup THEN
    ASM_MESON_TAC[MP1AUX_MEM_data_pointers];
    REFL_TAC]);;

(* HOL4 line 1759 *)
let data_length_heap_length = prove
 (`!heap:((A,B)heap_element)list.
     ALL isDataElement heap ==> data_length heap = heap_length heap`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALL] THENL
   [REWRITE_TAC[data_length_def; data_pointers_def; MAP; SUM; heap_length_NIL];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (fun th ->
    FIRST_X_ASSUM(MP_TAC o C MATCH_MP th))) THEN
  REWRITE_TAC[isDataElement_def] THEN DISCH_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  REWRITE_TAC[data_length_def; data_pointers_def; MAP; SUM;
              MP1AUX_SUM_lookup_len_CONS] THEN
  REWRITE_TAC[GSYM data_length_def] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[lookup_len_def; heap_lookup_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[heap_length_def; MAP; SUM]);;

(* HOL4 line 1773 *)
let data_length_CONS = prove
 (`!(x:(A,B)heap_element) xs. data_length (CONS x xs) = data_length [x] + data_length xs`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `x:(A,B)heap_element` (cases "heap_element")) THEN
  REWRITE_TAC[data_length_def; data_pointers_def; MAP; SUM;
              MP1AUX_SUM_lookup_len_CONS; ADD_CLAUSES] THEN
  REWRITE_TAC[lookup_len_def; heap_lookup_def] THEN CASE_REWRITE_TAC[]);;

(* HOL4 line 1783 *)
let data_length_APPEND = prove
 (`!xs ys:((A,B)heap_element)list.
     data_length (APPEND xs ys) = data_length xs + data_length ys`,
  LIST_INDUCT_TAC THEN GEN_TAC THENL
   [REWRITE_TAC[APPEND; data_length_def; data_pointers_def; MAP; SUM; ADD_CLAUSES];
    REWRITE_TAC[APPEND] THEN ONCE_REWRITE_TAC[data_length_CONS] THEN
    ASM_REWRITE_TAC[ADD_ASSOC]]);;

(* HOL4 line 1791 *)
let data_length_heap_expand = prove
 (`!n. data_length (heap_expand n:((A,B)heap_element)list) = 0`,
  GEN_TAC THEN REWRITE_TAC[heap_expand_def] THEN COND_CASES_TAC THEN
  REWRITE_TAC[data_length_def; data_pointers_def; MAP; SUM]);;

(* HOL4 line 1797 *)
let gc_combined_thm = prove
 (`!conf stack refs roots
    heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
          heap_element)list be a sp sp1 gens limit ts do_partial.
     abs_ml_inv conf stack refs (roots,heap,be,a,sp,sp1,gens) limit ts /\
     (do_partial ==> has_gen gens) ==>
     ?roots2 heap2 gens2 n2 a2.
       gc_combined (make_gc_conf limit) (data_to_word_config_gc_kind conf)
         (roots,heap,gens,a + sp + sp1,do_partial) =
       (roots2,heap2,a2,n2,gens2,T) /\
       abs_ml_inv conf stack refs (roots2,heap2,be,a2,n2,0,gens2) limit ts /\
       (~(data_to_word_config_gc_kind conf = data_to_word_None) /\
        (~(data_to_word_config_gc_kind conf = data_to_word_Simple) ==> ~do_partial)
        ==> all_reachable_from_roots roots2 heap2 /\
            heap_length heap2 = data_length heap2 + n2)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `data_to_word_config_gc_kind conf` (cases "gc_kind")) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[gc_combined_def; distinctness "gc_kind"] THEN
  STRIP_TAC THENL
   [(* data_to_word_None *)
    MAP_EVERY EXISTS_TAC [`roots:(((A)word_loc)heap_address)list`;
    `heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list`;
    `gens:gen_state`; `0`; `0`] THEN REWRITE_TAC[] THEN
  UNDISCH_TAC `abs_ml_inv conf stack refs (roots,heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list,be,a,sp,sp1,gens) limit ts` THEN
  REWRITE_TAC[abs_ml_inv_def; unused_space_inv_def; gc_kind_inv_def; data_up_to_def] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[LE_0; ADD_CLAUSES; heap_split_0; option_INJ; PAIR_EQ] THEN
  MESON_TAC[ALL];
    (* data_to_word_Simple *)
    FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] data_to_word_memoryProof_full_gc_thm) o
    check (MP1AUX_HEAD "abs_ml_inv")) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[MP1AUX_make_gc_conf] THEN CASE_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`roots2:(((A)word_loc)heap_address)list`;
    `APPEND heap2 (heap_expand (limit - a2)):(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list`;
    `gens:gen_state`; `limit - a2:num`; `a2:num`] THEN
  ASM_REWRITE_TAC[heap_length_APPEND; gc_shared_heap_length_heap_expand;
                  data_length_APPEND_heap_expand] THEN
  ASM_SIMP_TAC[data_length_heap_length];
    (* Generational *)
    ASM_CASES_TAC `do_partial:bool` THEN ASM_REWRITE_TAC[LET_DEF; LET_END_DEF] THENL
     [(* partial *)
      SUBGOAL_THEN `has_gen gens` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`conf:data_to_word_config`; `stack:(data_v)list`;
    `refs:((data_v)bvl_ref)spt`; `roots:(((A)word_loc)heap_address)list`;
    `heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list`;
    `be:bool`; `a:num`; `sp:num`; `sp1:num`; `gens:gen_state`; `limit:num`; `ts:num`;
    `a':num list`] gen_gc_partial_thm) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> MP1AUX_HEAD "abs_ml_inv" th &&
    can (find_term (fun t -> try fst(dest_var t) = "state2" with Failure _ -> false)) (concl th))) THEN
  ASM_REWRITE_TAC[reset_gens_def] THEN CASE_REWRITE_TAC[] THEN DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC [`roots2:(((A)word_loc)heap_address)list`;
    `APPEND (APPEND (APPEND (gc_state_old state2) (gc_state_h1 state2))
       (heap_expand (gc_state_n state2))) (gc_state_r1 (state2:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)gc_state)))`;
    `GenState 0 (MAP (K (gc_state_a (state2:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)gc_state)))) (a':num list))`;
    `gc_state_n (state2:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)gc_state))`;
    `gc_state_a (state2:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)gc_state))`] THEN
  ASM_REWRITE_TAC[];
      (* full generational *)
      FIRST_ASSUM(MP_TAC o MATCH_MP data_to_word_memoryProof_gen_gc_thm o
    check (MP1AUX_HEAD "abs_ml_inv")) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> MP1AUX_HEAD "abs_ml_inv" th &&
    can (find_term (fun t -> try fst(dest_var t) = "state2" with Failure _ -> false)) (concl th))) THEN
  ASM_REWRITE_TAC[reset_gens_def] THEN CASE_REWRITE_TAC[] THEN DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC [`roots2:(((A)word_loc)heap_address)list`;
    `APPEND (APPEND (gc_state_h1 state2) (heap_expand (gc_state_n state2)))
       (gc_state_r1 (state2:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)gc_state)))`;
    `GenState 0 (MAP (K (gc_state_a (state2:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)gc_state)))) (a':num list))`;
    `gc_state_n (state2:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)gc_state))`;
    `gc_state_a (state2:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)gc_state))`] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[data_length_APPEND; data_length_heap_length; data_length_heap_expand;
               heap_length_APPEND; gc_shared_heap_length_heap_expand] THEN
  ARITH_TAC]]);;

let _ = Gc.compact();;

(* HOL4 line 1834 *)
let heap_store_def = cake_def
  `(heap_store a (y:((A,B)heap_element)list) [] = ([],F)) /\
   (heap_store a y (CONS x xs) =
      if a = 0 then (APPEND y xs, (el_length x = heap_length y)) else
      if a < el_length x then (CONS x xs,F) else
        let (xs,c) = heap_store (a - el_length x) y xs in
        (CONS x xs,c))`;;

(* HOL4 line 1843 *)
let isUnused_def = cake_def
  `isUnused (x:(A,B)heap_element) <=> ?k. x = Unused k`;;

(* HOL4 line 1847 *)
let isSomeUnused_def = cake_def
  `isSomeUnused (x:((A,B)heap_element)option) <=> ?k. x = SOME (Unused k)`;;

(* HOL4 line 1851 *)
let heap_store_unused_def = cake_def
  `heap_store_unused a sp (x:(A,B)heap_element) xs =
     if heap_lookup a xs = SOME (Unused (sp - 1)) /\ el_length x <= sp then
       heap_store a (APPEND (heap_expand (sp - el_length x)) [x]) xs
     else (xs,F)`;;

(* HOL4 line 1858 *)
let heap_store_unused_alt_def = cake_def
  `heap_store_unused_alt a sp (x:(A,B)heap_element) xs =
     if heap_lookup a xs = SOME (Unused (sp - 1)) /\ el_length x <= sp then
       heap_store a (APPEND [x] (heap_expand (sp - el_length x))) xs
     else (xs,F)`;;

(* HOL4 line 1865 *)
let heap_store_lemma = prove
 (`!xs (y:((A,B)heap_element)list) x ys.
     heap_store (heap_length xs) y (APPEND xs (CONS x ys)) =
     (APPEND (APPEND xs y) ys, (heap_length y = el_length x))`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[APPEND; heap_length_NIL; GC1AUX_heap_length_CONS] THEN
  ONCE_REWRITE_TAC[heap_store_def] THEN REWRITE_TAC[] THENL
   [REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[];
    GC1AUX_EL_LENGTH_TAC THEN
    ASM_SIMP_TAC[ARITH_RULE
      `1 <= e ==> ~(e + n = 0) /\ ~(e + n < e) /\ (e + n) - e = n`] THEN
    SIMP[APPEND]]);;

(* HOL4 line 1877 *)
let heap_store_rel_def = cake_def
  `heap_store_rel (heap:((A,B)heap_element)list) heap2 <=>
     !ptr. isSomeDataElement (heap_lookup ptr heap) ==>
           heap_lookup ptr heap2 = heap_lookup ptr heap`;;

(* HOL4 line 1883 *)
let isSomeDataElement_heap_lookup_lemma1 = prove
 (`!n k (xs:((A,B)heap_element)list).
     isSomeDataElement (heap_lookup n (CONS (Unused k) xs)) <=>
     k < n /\ isSomeDataElement (heap_lookup (n - (k + 1)) xs)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[heap_lookup_def; el_length_def] THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[isSomeDataElement_def; option_INJ; distinctness "heap_element";
                LT];
    ALL_TAC] THEN
  ASM_CASES_TAC `n < k + 1` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `~(k < n)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_ARITH_TAC; REWRITE_TAC[isSomeDataElement_def; option_DISTINCT]];
    ASM_SIMP_TAC[ARITH_RULE `~(n < k + 1) ==> k < n`]]);;

(* HOL4 line 1892 *)
let isSomeDataElement_heap_lookup_lemma2 = prove
 (`!n k (xs:((A,B)heap_element)list).
     isSomeDataElement (heap_lookup n (APPEND (heap_expand k) xs)) <=>
     k <= n /\ isSomeDataElement (heap_lookup (n - k) xs)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[heap_expand_def] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[APPEND; LE_0; SUB_0; isSomeDataElement_heap_lookup_lemma1] THEN
  ASM_SIMP_TAC[ARITH_RULE `~(k = 0) ==> (k - 1 + 1 = k) /\ (k - 1 < n <=> k <= n)`]);;

(* HOL4 line 1903 *)
let isSomeDataElement_heap_lookup_lemma3 = prove
 (`!n (x:(A,B)heap_element) xs.
     ~(n = 0) ==>
     (isSomeDataElement (heap_lookup n (CONS x xs)) <=>
      el_length x <= n /\ isSomeDataElement (heap_lookup (n - el_length x) xs))`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[heap_lookup_def] THEN
  COND_CASES_TAC THENL
   [SUBGOAL_THEN `~(el_length (x:(A,B)heap_element) <= n)`
      (fun th -> REWRITE_TAC[th]) THENL
     [ASM_ARITH_TAC; REWRITE_TAC[isSomeDataElement_def; option_DISTINCT]];
    ASM_SIMP_TAC[ARITH_RULE `~(n < e) ==> e <= n`]]);;

(* MP1AUX: replacing an element u by a heap segment y of the same length *)
(* changes no heap_lookup outside the segment                             *)
let MP1AUX_heap_lookup_outside = prove
 (`!ha (u:(A,B)heap_element) hb y p.
     heap_length y = el_length u /\
     (p < heap_length ha \/ heap_length ha + el_length u <= p) ==>
     heap_lookup p (APPEND ha (APPEND y hb)) =
     heap_lookup p (APPEND ha (CONS u hb))`,
  REPEAT GEN_TAC THEN STRIP_TAC THENL
   [ASM_SIMP_TAC[gc_shared_LESS_IMP_heap_lookup];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(p < heap_length (ha:((A,B)heap_element)list))` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[NOT_LESS_IMP_heap_lookup] THEN
  SUBGOAL_THEN `~(p - heap_length (ha:((A,B)heap_element)list) <
                  heap_length (y:((A,B)heap_element)list))` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[NOT_LESS_IMP_heap_lookup] THEN
  REWRITE_TAC[heap_lookup_def] THEN
  MP_TAC(ISPEC `u:(A,B)heap_element` el_length_GT_0) THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(p - heap_length (ha:((A,B)heap_element)list) = 0) /\
                ~(p - heap_length ha < el_length (u:(A,B)heap_element))`
    (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC);;

(* MP1AUX: no data element starts inside an unused element *)
let MP1AUX_lookup_Unused_not_SDE = prove
 (`!ha hb n p.
     heap_length ha <= p /\ p < heap_length ha + n + 1 ==>
     ~isSomeDataElement
        (heap_lookup p (APPEND ha (CONS (Unused n:(A,B)heap_element) hb)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(p < heap_length (ha:((A,B)heap_element)list))` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[NOT_LESS_IMP_heap_lookup] THEN REWRITE_TAC[heap_lookup_def; el_length_def] THEN
  SUBGOAL_THEN `p - heap_length (ha:((A,B)heap_element)list) < n + 1`
    (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  COND_CASES_TAC THEN
  REWRITE_TAC[isSomeDataElement_def; option_INJ; option_DISTINCT;
              distinctness "heap_element"]);;

(* MP1AUX: replacing an unused element by a segment of the same length *)
(* keeps every data element                                             *)
let MP1AUX_heap_store_rel_replace = prove
 (`!ha hb n (y:((A,B)heap_element)list).
     heap_length y = n + 1 ==>
     heap_store_rel (APPEND ha (CONS (Unused n) hb)) (APPEND (APPEND ha y) hb)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[heap_store_rel_def; GSYM APPEND_ASSOC] THEN
  X_GEN_TAC `p:num` THEN
  ASM_CASES_TAC `p < heap_length (ha:((A,B)heap_element)list) \/
                 heap_length ha + n + 1 <= p` THENL
   [DISCH_TAC THEN MATCH_MP_TAC MP1AUX_heap_lookup_outside THEN
    ASM_REWRITE_TAC[el_length_def];
    MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN
    MATCH_MP_TAC MP1AUX_lookup_Unused_not_SDE THEN ASM_ARITH_TAC]);;

(* MP1AUX: the data elements after such a replacement *)
let MP1AUX_SDE_set_replace = prove
 (`!ha hb n (y:((A,B)heap_element)list) q.
     heap_length y = n + 1 /\ q < n + 1 /\
     (!p. p < n + 1
          ==> (isSomeDataElement (heap_lookup p (APPEND y hb)) <=> p = q)) ==>
     {p | isSomeDataElement (heap_lookup p (APPEND (APPEND ha y) hb))} =
     (heap_length ha + q) INSERT
     {p | isSomeDataElement (heap_lookup p (APPEND ha (CONS (Unused n) hb)))}`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[EXTENSION; IN_INSERT; IN_ELIM_THM; GSYM APPEND_ASSOC] THEN
  X_GEN_TAC `p:num` THEN
  ASM_CASES_TAC `p < heap_length (ha:((A,B)heap_element)list) \/
                 heap_length ha + n + 1 <= p` THENL
   [SUBGOAL_THEN `~(p = heap_length (ha:((A,B)heap_element)list) + q)`
      (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC MP1AUX_heap_lookup_outside THEN
    ASM_REWRITE_TAC[el_length_def];
    ALL_TAC] THEN
  SUBGOAL_THEN `~isSomeDataElement (heap_lookup p
                  (APPEND ha (CONS (Unused n:(A,B)heap_element) hb)))`
    (fun th -> REWRITE_TAC[th]) THENL
   [MATCH_MP_TAC MP1AUX_lookup_Unused_not_SDE THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(p < heap_length (ha:((A,B)heap_element)list))` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP NOT_LESS_IMP_heap_lookup th]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `p - heap_length (ha:((A,B)heap_element)list)` o
                check (is_forall o concl)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN ASM_ARITH_TAC);;

(* MP1AUX: inside heap_expand k ++ [x] the only data element is x *)
let MP1AUX_inside_expand_x = prove
 (`!k (x:(A,B)heap_element) hb p.
     isDataElement x /\ p < k + el_length x ==>
     (isSomeDataElement (heap_lookup p (APPEND (APPEND (heap_expand k) [x]) hb)) <=>
      p = k)`,
  REWRITE_TAC[GSYM APPEND_ASSOC; APPEND; isSomeDataElement_heap_lookup_lemma2] THEN
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `k:num <= p` THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC; ASM_ARITH_TAC] THEN
  REWRITE_TAC[heap_lookup_def] THEN
  ASM_CASES_TAC `p:num = k` THEN ASM_REWRITE_TAC[SUB_REFL] THENL
   [UNDISCH_TAC `isDataElement (x:(A,B)heap_element)` THEN
    REWRITE_TAC[isDataElement_def; isSomeDataElement_def; option_INJ];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(p - k = 0) /\ p - k < el_length (x:(A,B)heap_element)`
    (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[isSomeDataElement_def; option_DISTINCT]);;

(* MP1AUX: inside [x] ++ heap_expand k the only data element is x *)
let MP1AUX_inside_x_expand = prove
 (`!k (x:(A,B)heap_element) hb p.
     isDataElement x /\ p < el_length x + k ==>
     (isSomeDataElement (heap_lookup p (APPEND (APPEND [x] (heap_expand k)) hb)) <=>
      p = 0)`,
  REWRITE_TAC[GSYM APPEND_ASSOC; APPEND; heap_lookup_def] THEN
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `p = 0` THEN ASM_REWRITE_TAC[] THENL
   [UNDISCH_TAC `isDataElement (x:(A,B)heap_element)` THEN
    REWRITE_TAC[isDataElement_def; isSomeDataElement_def; option_INJ];
    ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[isSomeDataElement_def; option_DISTINCT] THEN
  REWRITE_TAC[GSYM isSomeDataElement_def; isSomeDataElement_heap_lookup_lemma2] THEN
  ASM_ARITH_TAC);;

(* HOL4 line 1914 *)
let IMP_heap_store_unused = prove
 (`!a sp (heap:((A,B)heap_element)list) x.
     unused_space_inv a sp heap /\ el_length x <= sp ==>
     ?heap2. heap_store_unused a sp x heap = (heap2,T) /\
             unused_space_inv a (sp - el_length x) heap2 /\
             heap_lookup ((a + sp) - el_length x) heap2 = SOME x /\
             ~isSomeDataElement (heap_lookup ((a + sp) - el_length x) heap) /\
             heap_length heap2 = heap_length heap /\
             (~isForwardPointer x ==>
              FILTER isForwardPointer heap2 = FILTER isForwardPointer heap) /\
             (!xs l d.
                MEM (DataElement xs l d) heap2 <=>
                x = DataElement xs l d \/ MEM (DataElement xs l d) heap) /\
             (isDataElement x ==>
              {a | isSomeDataElement (heap_lookup a heap2)} =
              ((a + sp) - el_length x) INSERT
              {a | isSomeDataElement (heap_lookup a heap)}) /\
             heap_store_rel heap heap2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[unused_space_inv_def] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `x:(A,B)heap_element` el_length_GT_0) THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(sp = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `?ha hb. heap = APPEND ha (CONS (Unused (sp - 1)) hb) /\
                        a = heap_length (ha:((A,B)heap_element)list)`
    STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC heap_lookup_SPLIT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ABBREV_TAC `k = sp - el_length (x:(A,B)heap_element)` THEN
  SUBGOAL_THEN `sp = k + el_length (x:(A,B)heap_element)` SUBST_ALL_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `(a + k + e) - e = a + k:num`; ADD_SUB] THEN
  SUBGOAL_THEN
   `heap_length (APPEND (heap_expand k) [x:(A,B)heap_element]) =
    el_length (Unused ((k + el_length x) - 1):(A,B)heap_element)`
   ASSUME_TAC THENL
   [REWRITE_TAC[heap_length_APPEND; gc_shared_heap_length_heap_expand;
                heap_length_def; MAP; SUM; el_length_def] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `heap_store_unused (heap_length (ha:((A,B)heap_element)list))
      (k + el_length (x:(A,B)heap_element)) x
      (APPEND ha (CONS (Unused ((k + el_length x) - 1)) hb)) =
    (APPEND (APPEND ha (APPEND (heap_expand k) [x])) hb, T)`
   SUBST1_TAC THENL
   [REWRITE_TAC[heap_store_unused_def; heap_lookup_PREFIX; LE_ADDR; ADD_SUB] THEN
    ASM_REWRITE_TAC[heap_store_lemma];
    ALL_TAC] THEN
  REWRITE_TAC[PAIR_EQ; UNWIND_THM1] THEN
  SUBGOAL_THEN `ALL isDataElement (ha:((A,B)heap_element)list)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (MP1AUX_HEAD "data_up_to")) THEN
    REWRITE_TAC[data_up_to_APPEND];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[el_length_def]) THEN
  SUBGOAL_THEN `(k + el_length (x:(A,B)heap_element)) - 1 + 1 = k + el_length x`
    ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [(* unused space: lookup *)
    DISCH_THEN(fun th -> REWRITE_TAC[heap_expand_def; th]) THEN
    REWRITE_TAC[GSYM APPEND_ASSOC; APPEND; heap_lookup_PREFIX];
    (* unused space: length *)
    REWRITE_TAC[heap_length_APPEND; gc_shared_heap_length_heap_expand] THEN
    REWRITE_TAC[heap_length_def; MAP; SUM; el_length_def] THEN ASM_ARITH_TAC;
    (* unused space: data_up_to *)
    ASM_REWRITE_TAC[GSYM APPEND_ASSOC; data_up_to_APPEND];
    (* the new element *)
    SUBGOAL_THEN `heap_length ha + k =
                  heap_length (APPEND ha (heap_expand k:((A,B)heap_element)list))`
      SUBST1_TAC THENL
     [REWRITE_TAC[heap_length_APPEND; gc_shared_heap_length_heap_expand]; ALL_TAC] THEN
    REWRITE_TAC[GSYM APPEND_ASSOC; APPEND] THEN ONCE_REWRITE_TAC[APPEND_ASSOC] THEN
    REWRITE_TAC[heap_lookup_PREFIX];
    (* no data element there before *)
    MATCH_MP_TAC MP1AUX_lookup_Unused_not_SDE THEN ASM_ARITH_TAC;
    (* length *)
    REWRITE_TAC[heap_length_APPEND; gc_shared_heap_length_heap_expand] THEN
    REWRITE_TAC[heap_length_def; MAP; SUM; el_length_def] THEN ASM_ARITH_TAC;
    (* forward pointers *)
    DISCH_TAC THEN REWRITE_TAC[FILTER_APPEND; FILTER; heap_expand_def] THEN
    ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[FILTER; APPEND; isForwardPointer_def; APPEND_NIL];
    (* data elements *)
    REPEAT GEN_TAC THEN REWRITE_TAC[MEM_APPEND; MEM; heap_expand_def] THEN
    COND_CASES_TAC THEN REWRITE_TAC[MEM; distinctness "heap_element"] THEN MESON_TAC[];
    (* the set of data elements *)
    DISCH_TAC THEN MATCH_MP_TAC MP1AUX_SDE_set_replace THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [ASM_ARITH_TAC;
      REPEAT STRIP_TAC THEN MATCH_MP_TAC MP1AUX_inside_expand_x THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];
    (* heap_store_rel *)
    MATCH_MP_TAC MP1AUX_heap_store_rel_replace THEN ASM_REWRITE_TAC[]]);;

(* HOL4 line 2035 *)
let IMP_heap_store_unused_alt = prove
 (`!a sp (heap:((A,B)heap_element)list) x.
     unused_space_inv a sp heap /\ el_length x <= sp ==>
     ?heap2. heap_store_unused_alt a sp x heap = (heap2,T) /\
             (isDataElement x ==>
              unused_space_inv (a + el_length x) (sp - el_length x) heap2) /\
             heap_lookup a heap2 = SOME x /\
             ~isSomeDataElement (heap_lookup a heap) /\
             heap_length heap2 = heap_length heap /\
             (~isForwardPointer x ==>
              FILTER isForwardPointer heap2 = FILTER isForwardPointer heap) /\
             (!xs l d.
                MEM (DataElement xs l d) heap2 <=>
                x = DataElement xs l d \/ MEM (DataElement xs l d) heap) /\
             (isDataElement x ==>
              {a | isSomeDataElement (heap_lookup a heap2)} =
              a INSERT {a | isSomeDataElement (heap_lookup a heap)}) /\
             heap_store_rel heap heap2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[unused_space_inv_def] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `x:(A,B)heap_element` el_length_GT_0) THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(sp = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `?ha hb. heap = APPEND ha (CONS (Unused (sp - 1)) hb) /\
                        a = heap_length (ha:((A,B)heap_element)list)`
    STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC heap_lookup_SPLIT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ABBREV_TAC `k = sp - el_length (x:(A,B)heap_element)` THEN
  SUBGOAL_THEN `sp = k + el_length (x:(A,B)heap_element)` SUBST_ALL_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ADD_SUB] THEN
  SUBGOAL_THEN
   `heap_length (APPEND [x:(A,B)heap_element] (heap_expand k)) =
    el_length (Unused ((k + el_length x) - 1):(A,B)heap_element)`
   ASSUME_TAC THENL
   [REWRITE_TAC[heap_length_APPEND; gc_shared_heap_length_heap_expand] THEN
    REWRITE_TAC[heap_length_def; MAP; SUM; el_length_def] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `heap_store_unused_alt (heap_length (ha:((A,B)heap_element)list))
      (k + el_length (x:(A,B)heap_element)) x
      (APPEND ha (CONS (Unused ((k + el_length x) - 1)) hb)) =
    (APPEND (APPEND ha (APPEND [x] (heap_expand k))) hb, T)`
   SUBST1_TAC THENL
   [REWRITE_TAC[heap_store_unused_alt_def; heap_lookup_PREFIX; LE_ADDR; ADD_SUB] THEN
    ASM_REWRITE_TAC[heap_store_lemma];
    ALL_TAC] THEN
  REWRITE_TAC[PAIR_EQ; UNWIND_THM1] THEN
  SUBGOAL_THEN `ALL isDataElement (ha:((A,B)heap_element)list)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (MP1AUX_HEAD "data_up_to")) THEN
    REWRITE_TAC[data_up_to_APPEND];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[el_length_def]) THEN
  SUBGOAL_THEN `(k + el_length (x:(A,B)heap_element)) - 1 + 1 = k + el_length x`
    ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ALL_TAC THEN
  REPEAT CONJ_TAC THENL
   [(* unused space *)
    DISCH_TAC THEN
    SUBGOAL_THEN `APPEND (APPEND ha (APPEND [x] (heap_expand k))) hb =
                  APPEND (APPEND ha [x:(A,B)heap_element])
                         (APPEND (heap_expand k) (hb:((A,B)heap_element)list))`
      SUBST1_TAC THENL [REWRITE_TAC[APPEND_ASSOC]; ALL_TAC] THEN
    SUBGOAL_THEN `heap_length ha + el_length x =
                  heap_length (APPEND ha [x:(A,B)heap_element])` SUBST1_TAC THENL
     [REWRITE_TAC[heap_length_APPEND] THEN
      REWRITE_TAC[heap_length_def; MAP; SUM; ADD_CLAUSES];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [DISCH_THEN(fun th -> REWRITE_TAC[heap_expand_def; th]) THEN
      REWRITE_TAC[APPEND; heap_lookup_PREFIX];
      REWRITE_TAC[heap_length_APPEND; gc_shared_heap_length_heap_expand] THEN
      REWRITE_TAC[heap_length_def; MAP; SUM; el_length_def] THEN ASM_ARITH_TAC;
      ASM_REWRITE_TAC[data_up_to_APPEND; ALL_APPEND; ALL]];
    (* the new element *)
    REWRITE_TAC[GSYM APPEND_ASSOC; APPEND; heap_lookup_PREFIX];
    (* no data element there before *)
    MATCH_MP_TAC MP1AUX_lookup_Unused_not_SDE THEN ASM_ARITH_TAC;
    (* length *)
    REWRITE_TAC[heap_length_APPEND; gc_shared_heap_length_heap_expand] THEN
    REWRITE_TAC[heap_length_def; MAP; SUM; el_length_def] THEN ASM_ARITH_TAC;
    (* forward pointers *)
    DISCH_TAC THEN REWRITE_TAC[FILTER_APPEND; FILTER; heap_expand_def] THEN
    ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[FILTER; APPEND; isForwardPointer_def; APPEND_NIL];
    (* data elements *)
    REPEAT GEN_TAC THEN REWRITE_TAC[MEM_APPEND; MEM; heap_expand_def] THEN
    COND_CASES_TAC THEN REWRITE_TAC[MEM; distinctness "heap_element"] THEN MESON_TAC[];
    (* the set of data elements *)
    DISCH_TAC THEN
    MP_TAC(ISPECL [`ha:((A,B)heap_element)list`; `hb:((A,B)heap_element)list`;
      `(k + el_length (x:(A,B)heap_element)) - 1`;
      `APPEND [x:(A,B)heap_element] (heap_expand k)`; `0`] MP1AUX_SDE_set_replace) THEN
    REWRITE_TAC[ADD_CLAUSES] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_ARITH_TAC;
      REPEAT STRIP_TAC THEN MATCH_MP_TAC MP1AUX_inside_x_expand THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];
    (* heap_store_rel *)
    MATCH_MP_TAC MP1AUX_heap_store_rel_replace THEN ASM_REWRITE_TAC[]]);;

(* HOL4 line 2134 *)
let heap_store_rel_lemma = prove
 (`!h1 (h2:((A,B)heap_element)list) n ys l d.
     heap_store_rel h1 h2 /\ heap_lookup n h1 = SOME (DataElement ys l d) ==>
     heap_lookup n h2 = SOME (DataElement ys l d)`,
  REWRITE_TAC[heap_store_rel_def; isSomeDataElement_def] THEN MESON_TAC[]);;

(* MP1AUX: heap_store_rel keeps every data element *)
let MP1AUX_heap_store_rel_lookup = prove
 (`!h1 (h2:((A,B)heap_element)list) n x.
     heap_store_rel h1 h2 /\ heap_lookup n h1 = SOME x /\ isDataElement x ==>
     heap_lookup n h2 = SOME x`,
  REWRITE_TAC[heap_store_rel_def; isSomeDataElement_def; isDataElement_def] THEN
  MESON_TAC[]);;

(* MP1AUX: the heap representations of values are data elements *)
let MP1AUX_isDataElement_reps = prove
 (`(!i. isDataElement (Bignum i:((A)word_loc,data_to_word_memoryProof_tag#
                                 ((A)word_loc)list)heap_element)) /\
   (!w. isDataElement (Word64Rep (:A) w)) /\
   (!n xs. isDataElement (BlockRep n xs:((A)word_loc,data_to_word_memoryProof_tag#
                                         ((A)word_loc)list)heap_element)) /\
   (!ev y. isDataElement (ThunkBlock ev y:((A)word_loc,data_to_word_memoryProof_tag#
                                           ((A)word_loc)list)heap_element))`,
  REWRITE_TAC[isDataElement_def; BlockRep_def; ThunkBlock_def] THEN
  MESON_TAC[MP1AUX_Bignum_nil; MP1AUX_Word64Rep_nil]);;

(* HOL4 line 2143 *)
let v_inv_SUBMAP_lemma = prove
 (`!conf f1 tf1 heap1 ck w refs x f tf
    heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
          heap_element)list.
     v_inv conf w refs (x,f,tf,heap) ==>
     f SUBMAP f1 /\ tf SUBMAP tf1 /\ heap_store_rel heap heap1 ==>
     v_inv_ck ck conf w refs (x,f1,tf1,heap1)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC num_WF THEN
  X_GEN_TAC `ck:num` THEN DISCH_THEN(LABEL_TAC "IH") THEN X_GEN_TAC `w:data_v` THEN
  STRUCT_CASES_TAC(ISPEC `w:data_v` MP1AUX_data_v_nchotomy) THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[v_inv_def; MP1AUX_v_inv_ck_Number; MP1AUX_v_inv_ck_Word64;
              MP1AUX_v_inv_ck_CodePtr; MP1AUX_v_inv_ck_RefPtr;
              MP1AUX_v_inv_ck_Block] THENL
   [(* Number *)
    COND_CASES_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `ptr:num` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MP1AUX_heap_store_rel_lookup THEN
    EXISTS_TAC `heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
                      heap_element)list` THEN
    ASM_REWRITE_TAC[MP1AUX_isDataElement_reps];
    (* Word64 *)
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `ptr:num` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MP1AUX_heap_store_rel_lookup THEN
    EXISTS_TAC `heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
                      heap_element)list` THEN
    ASM_REWRITE_TAC[MP1AUX_isDataElement_reps];
    (* Block *)
    COND_CASES_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`ptr:num`; `xs:(((A)word_loc)heap_address)list`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [DISCH_TAC THEN
      UNDISCH_TAC `ALL2 (\v x. v_inv conf v refs (x,f,tf,heap:(((A)word_loc,
                     data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list))
                     a2 (xs:(((A)word_loc)heap_address)list)` THEN
      MATCH_MP_TAC MONO_ALL2 THEN REPEAT GEN_TAC THEN BETA_TAC THEN DISCH_TAC THEN
      USE_THEN "IH" (MP_TAC o SPEC `ck - 1`) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[IMP_IMP]] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`f:(num,num)fmap`; `tf:(num,num)fmap`;
        `heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
               heap_element)list`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC FLOOKUP_SUBMAP THEN EXISTS_TAC `tf:(num,num)fmap` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC MP1AUX_heap_store_rel_lookup THEN
      EXISTS_TAC `heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
                        heap_element)list` THEN
      ASM_REWRITE_TAC[MP1AUX_isDataElement_reps]];
    (* CodePtr *)
    MESON_TAC[];
    (* RefPtr *)
    DISCH_THEN(DISJ_CASES_THEN2 STRIP_ASSUME_TAC
      (DISJ_CASES_THEN2 STRIP_ASSUME_TAC STRIP_ASSUME_TAC)) THEN
    STRIP_TAC THENL
     [SUBGOAL_THEN `a1 IN FDOM (f1:(num,num)fmap) /\ FAPPLY f1 a1 = FAPPLY f a1`
        STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[SUBMAP_DEF]; ALL_TAC] THEN
      DISJ1_TAC THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `a1 IN FDOM (f1:(num,num)fmap) /\ FAPPLY f1 a1 = FAPPLY f a1`
        STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[SUBMAP_DEF]; ALL_TAC] THEN
      DISJ2_TAC THEN DISJ1_TAC THEN
      MAP_EVERY EXISTS_TAC [`ev:thunk_mode`; `v:data_v`;
                            `y:((A)word_loc)heap_address`] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC MP1AUX_heap_store_rel_lookup THEN
        EXISTS_TAC `heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
                          heap_element)list` THEN
        ASM_REWRITE_TAC[MP1AUX_isDataElement_reps];
        DISCH_TAC THEN USE_THEN "IH" (MP_TAC o SPEC `ck - 1`) THEN
        ANTS_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[IMP_IMP]] THEN
        DISCH_THEN MATCH_MP_TAC THEN
        MAP_EVERY EXISTS_TAC [`f:(num,num)fmap`; `tf:(num,num)fmap`;
          `heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
                 heap_element)list`] THEN
        ASM_REWRITE_TAC[]];
      DISJ2_TAC THEN DISJ2_TAC THEN EXISTS_TAC `v:data_v` THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN USE_THEN "IH" (MP_TAC o SPEC `ck - 1`) THEN
        ANTS_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[IMP_IMP]] THEN
        DISCH_THEN MATCH_MP_TAC THEN
        MAP_EVERY EXISTS_TAC [`f:(num,num)fmap`; `tf:(num,num)fmap`;
          `heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
                 heap_element)list`] THEN
        ASM_REWRITE_TAC[]]]);;

(* HOL4 line 2186 *)
let v_inv_SUBMAP = prove
 (`!conf refs f f1 tf tf1
    (heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
           heap_element)list) heap1 w x.
     f SUBMAP f1 /\ tf SUBMAP tf1 /\ heap_store_rel heap heap1 /\
     v_inv conf w refs (x,f,tf,heap) ==>
     v_inv conf w refs (x,f1,tf1,heap1)`,
  MESON_TAC[v_inv_eq; v_inv_SUBMAP_lemma]);;

(* HOL4 line 2196 *)
let heap_store_rel_v_inv = prove
 (`!conf refs f tf
    (heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
           heap_element)list) heap1 w x.
     heap_store_rel heap heap1 /\ v_inv conf w refs (x,f,tf,heap) ==>
     v_inv conf w refs (x,f,tf,heap1)`,
  MESON_TAC[v_inv_SUBMAP; SUBMAP_REFL]);;

(* HOL4 line 2205 *)
let heap_store_unused_alt_thm = prove
 (`!a n (heap:((A,B)heap_element)list) h1 h2 heap2 x.
     heap_split (a + n) heap = SOME (h1,h2) /\
     heap_store_unused_alt a n x heap = (heap2,T) /\
     unused_space_inv (a + el_length x) (n - el_length x) heap2 ==>
     ?h0. h1 = APPEND h0 [Unused (n - 1)] /\
          heap = APPEND h1 h2 /\ heap_length h0 = a /\
          heap2 = APPEND (APPEND (APPEND h0 [x]) (heap_expand (n - el_length x)))
                         h2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[heap_store_unused_alt_def] THEN
  COND_CASES_TAC THENL [ALL_TAC; REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[]] THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN STRIP_TAC THEN
  MP_TAC(ISPEC `x:(A,B)heap_element` el_length_GT_0) THEN DISCH_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP heap_split_heap_length o
                check (MP1AUX_HEAD "=" )) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
    try fst(dest_var(rhs(concl th))) = "heap" with Failure _ -> false)) THEN
  SUBGOAL_THEN `a < heap_length (h1:((A,B)heap_element)list)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE
    [MATCH_MP gc_shared_LESS_IMP_heap_lookup th])) THEN
  MP_TAC(ISPECL [`h1:((A,B)heap_element)list`; `a:num`;
                 `Unused (n - 1):(A,B)heap_element`] heap_lookup_SPLIT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `ha:((A,B)heap_element)list`
    (X_CHOOSE_THEN `hb:((A,B)heap_element)list` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `hb:((A,B)heap_element)list = []` SUBST_ALL_TAC THENL
   [REWRITE_TAC[GSYM MP1AUX_heap_length_0] THEN
    UNDISCH_TAC `heap_length (APPEND ha (CONS (Unused (n - 1)) hb)) =
                 heap_length (ha:((A,B)heap_element)list) + n` THEN
    REWRITE_TAC[heap_length_APPEND] THEN
    REWRITE_TAC[heap_length_def; MAP; SUM; el_length_def] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `ha:((A,B)heap_element)list` THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> MP1AUX_HEAD "=" th &&
    can (find_term (fun t -> try fst(dest_const t) = "heap_store"
                             with Failure _ -> false)) (concl th))) THEN
  REWRITE_TAC[GSYM APPEND_ASSOC; APPEND; heap_store_lemma; PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) (K ALL_TAC)) THEN
  REWRITE_TAC[GSYM APPEND_ASSOC; APPEND]);;

(* MP1AUX: a successful heap_store replaces one element *)
let MP1AUX_heap_store_T = prove
 (`!heap a (y:((A,B)heap_element)list) heap2.
     heap_store a y heap = (heap2,T) ==>
     ?xs x ys. heap = APPEND xs (CONS x ys) /\ a = heap_length xs /\
               heap2 = APPEND (APPEND xs y) ys`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[heap_store_def; PAIR_EQ] THEN REPEAT GEN_TAC THEN
  COND_CASES_TAC THENL
   [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`[]:((A,B)heap_element)list`; `h:(A,B)heap_element`;
                          `t:((A,B)heap_element)list`] THEN
    ASM_REWRITE_TAC[APPEND; heap_length_NIL];
    ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  PAIRARG_TAC THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a - el_length (h:(A,B)heap_element)`;
    `y:((A,B)heap_element)list`; `xs:((A,B)heap_element)list`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `xs0:((A,B)heap_element)list`
    (X_CHOOSE_THEN `x0:(A,B)heap_element`
      (X_CHOOSE_THEN `ys0:((A,B)heap_element)list` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`CONS (h:(A,B)heap_element) xs0`; `x0:(A,B)heap_element`;
                        `ys0:((A,B)heap_element)list`] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
    try fst(dest_var(rhs(concl th))) = "heap2" with Failure _ -> false)) THEN
  ASM_REWRITE_TAC[APPEND] THEN
  SUBGOAL_THEN `heap_length (CONS (h:(A,B)heap_element) xs0) =
                el_length h + heap_length xs0` SUBST1_TAC THENL
   [REWRITE_TAC[heap_length_def; MAP; SUM]; ASM_ARITH_TAC]);;

(* HOL4 line 2231 *)
let heap_store_unused_alt_heap_lookup = prove
 (`!(heap:((A,B)heap_element)list) heap2 a k x n.
     heap_store_unused_alt a k x heap = (heap2,T) /\ n < a ==>
     heap_lookup n heap = heap_lookup n heap2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[heap_store_unused_alt_def] THEN
  COND_CASES_TAC THENL [ALL_TAC; REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[]] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP MP1AUX_heap_store_T o check (fun th ->
    MP1AUX_HEAD "=" th &&
    can (find_term (fun t -> try fst(dest_const t) = "heap_store"
                             with Failure _ -> false)) (concl th))) THEN
  DISCH_THEN(X_CHOOSE_THEN `xs:((A,B)heap_element)list`
    (X_CHOOSE_THEN `z:(A,B)heap_element`
      (X_CHOOSE_THEN `ys:((A,B)heap_element)list` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `n < heap_length (xs:((A,B)heap_element)list)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  ASM_SIMP_TAC[gc_shared_LESS_IMP_heap_lookup]);;

(* HOL4 line 2254 *)
let heap_split_heap_store = prove
 (`!(heap:((A,B)heap_element)list) e h1 h2 a y heap2.
     heap_split e heap = SOME (h1,h2) /\
     heap_store a y heap = (heap2,T) /\ e <= a ==>
     ?h3. heap_split e heap2 = SOME (h1,h3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP heap_split_heap_length o
                check (MP1AUX_HEAD "=")) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP MP1AUX_heap_store_T o check (MP1AUX_HEAD "=")) THEN
  DISCH_THEN(X_CHOOSE_THEN `xs:((A,B)heap_element)list`
    (X_CHOOSE_THEN `x:(A,B)heap_element`
      (X_CHOOSE_THEN `ys:((A,B)heap_element)list` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `?l. xs = APPEND h1 (l:((A,B)heap_element)list)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `APPEND h1 h2 = heap:((A,B)heap_element)list` THEN
    ASM_REWRITE_TAC[APPEND_EQ_APPEND] THEN STRIP_TAC THENL
     [EXISTS_TAC `[]:((A,B)heap_element)list` THEN REWRITE_TAC[APPEND_NIL] THEN
      SUBGOAL_THEN `l:((A,B)heap_element)list = []` SUBST_ALL_TAC THENL
       [REWRITE_TAC[GSYM MP1AUX_heap_length_0] THEN
        UNDISCH_TAC `heap_length (h1:((A,B)heap_element)list) = e` THEN
        ASM_REWRITE_TAC[heap_length_APPEND] THEN ASM_ARITH_TAC;
        ASM_REWRITE_TAC[APPEND_NIL]];
      EXISTS_TAC `l:((A,B)heap_element)list` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `APPEND l (APPEND y ys):((A,B)heap_element)list` THEN
  ASM_REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    try fst(dest_var(rhs(concl th))) = "e" with Failure _ -> false)) THEN
  REWRITE_TAC[heap_split_length]);;

(* HOL4 line 2273 *)
let heap_store_unused_alt_gen_state_ok = prove
 (`!a k (x:(A,B)heap_element) heap heap2 gens.
     heap_store_unused_alt a k x heap = (heap2,T) /\
     gen_state_ok a (a + k) heap gens ==>
     gen_state_ok (a + el_length x) (a + k) heap2 gens`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `gens:gen_state` (cases "gen_state")) THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST1_TAC THEN
  REWRITE_TAC[gen_state_ok_def; heap_store_unused_alt_def] THEN
  COND_CASES_TAC THENL [ALL_TAC; REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[]] THEN
  REWRITE_TAC[GSYM ALL_MEM] THEN BETA_TAC THEN STRIP_TAC THEN CONJ_TAC THEN
  X_GEN_TAC `s:num` THEN DISCH_TAC THEN
  (SUBGOAL_THEN `s <= a /\ gen_start_ok (heap:((A,B)heap_element)list) (a + k) s`
     STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC]) THEN
  TRY(ASM_ARITH_TAC) THEN
  UNDISCH_TAC `gen_start_ok (heap:((A,B)heap_element)list) (a + k) s` THEN
  REWRITE_TAC[gen_start_ok_def] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`heap:((A,B)heap_element)list`; `s:num`;
    `h1:((A,B)heap_element)list`; `h2:((A,B)heap_element)list`; `a:num`;
    `APPEND [x:(A,B)heap_element] (heap_expand (k - el_length x))`;
    `heap2:((A,B)heap_element)list`] heap_split_heap_store) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`h1:((A,B)heap_element)list`; `h3:((A,B)heap_element)list`] THEN
  ASM_REWRITE_TAC[]);;

(* HOL4 line 2290 *)
let isDataElement_lemmas = prove
 (`!x1 x2 (x3:B) tag (ys1:(A heap_address)list) (w:int64)
    (ws:(C heap_address)list) y1 y2 y3 (y4:(D word)list) ev (v:E heap_address)
    i.
     isDataElement (DataElement x1 x2 x3:(A,B)heap_element) /\
     isDataElement (BlockRep tag ys1:(A,data_to_word_memoryProof_tag#B list)
                                     heap_element) /\
     isDataElement (Word64Rep (:D) w) /\
     isDataElement (RefBlock ws:(C,data_to_word_memoryProof_tag#B list)
                               heap_element) /\
     isDataElement (Bytes y1 y2 y3 y4) /\
     isDataElement (ThunkBlock ev v:(E,data_to_word_memoryProof_tag#B list)
                                    heap_element) /\
     isDataElement (Bignum i:((D)word_loc,data_to_word_memoryProof_tag#
                               ((D)word_loc)list)heap_element)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[isDataElement_def; BlockRep_def; RefBlock_def; ThunkBlock_def] THEN
  MP_TAC(ISPECL [`(:D)`; `w:int64`] Word64Rep_DataElement) THEN
  MP_TAC(ISPECL [`y1:bool`; `y2:bool`; `y3:byte list`; `y4:(D word)list`]
                MP1AUX_Bytes_nil) THEN
  MP_TAC(INST_TYPE [`:D`,`:A`] (SPEC `i:int` MP1AUX_Bignum_nil)) THEN
  MESON_TAC[]);;

let _ = cake_add_simps [isDataElement_lemmas];;

(* HOL4 line 2305 *)
let list_to_BlockReps_def = cake_def
  `(list_to_BlockReps conf (t:((A)word_loc)heap_address) a [] =
      (ARB:(((A)word_loc,data_to_word_memoryProof_tag#B list)heap_element)list)) /\
   (list_to_BlockReps conf t a (CONS h l) =
      match l with
        [] -> [BlockRep cons_tag [h;t]]
      | _ ->
          CONS (BlockRep cons_tag
                  [h; Pointer (a + 3) (wl_Word (ptr_bits conf cons_tag 2))])
               (list_to_BlockReps conf t (a + 3) l))`;;

let list_to_BlockReps_ind = cake_ind "list_to_BlockReps";;

(* HOL4 line 2316 *)
let list_to_BlockReps_heap_length = prove
 (`!conf (x:((A)word_loc)heap_address) xs len.
     ~(xs = []) ==>
     heap_length (list_to_BlockReps conf x len xs
                  :(((A)word_loc,data_to_word_memoryProof_tag#B list)
                    heap_element)list) =
     3 * LENGTH xs`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[NOT_CONS_NIL] THEN
  GEN_TAC THEN ONCE_REWRITE_TAC[list_to_BlockReps_def] THEN
  MP_TAC(ISPEC `t:(((A)word_loc)heap_address)list` list_CASES) THEN
    STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[GC1AUX_heap_length_CONS; heap_length_NIL; BlockRep_def;
              el_length_def; LENGTH] THEN
  ASM_SIMP_TAC[NOT_CONS_NIL; LENGTH] THEN ARITH_TAC);;

(* HOL4 line 2328 *)
let heap_lookup_heap_length = prove
 (`!h1 (h2:((A,B)heap_element)list).
     heap_lookup (heap_length h1) (APPEND h1 h2) = heap_lookup 0 h2`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[NOT_LESS_IMP_heap_lookup; LT_REFL; SUB_REFL]);;

(* HOL4 line 2334 *)
let list_to_BlockReps_heap_lookup_0 = prove
 (`!conf (x:((A)word_loc)heap_address) len xs.
     ~(xs = []) ==>
     isSomeDataElement
       (heap_lookup 0 (list_to_BlockReps conf x len xs
                       :(((A)word_loc,data_to_word_memoryProof_tag#B list)
                         heap_element)list))`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[NOT_CONS_NIL] THEN
  ONCE_REWRITE_TAC[list_to_BlockReps_def] THEN
  MP_TAC(ISPEC `t:(((A)word_loc)heap_address)list` list_CASES) THEN
    STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[heap_lookup_def; isSomeDataElement_def; BlockRep_def; option_INJ;
              injectivity "heap_element"] THEN
  MESON_TAC[]);;

(* HOL4 line 2343 *)
let list_to_BlockReps_isDataElement = prove
 (`!conf xs (x:((A)word_loc)heap_address) len.
     ~(xs = []) ==>
     ALL isDataElement (list_to_BlockReps conf x len xs
                        :(((A)word_loc,data_to_word_memoryProof_tag#B list)
                          heap_element)list)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[NOT_CONS_NIL] THEN
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[list_to_BlockReps_def] THEN
  MP_TAC(ISPEC `t:(((A)word_loc)heap_address)list` list_CASES) THEN
    STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[ALL; isDataElement_lemmas] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[NOT_CONS_NIL]);;

(* HOL4 line 2352 *)
let list_to_BlockReps_data_up_to_lem = prove
 (`!conf (x:((A)word_loc)heap_address) len xs
    (h1:(((A)word_loc,data_to_word_memoryProof_tag#B list)heap_element)list) h2.
     ~(xs = []) /\ h1 = list_to_BlockReps conf x len xs ==>
     data_up_to (heap_length h1) (APPEND h1 h2)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[data_up_to_APPEND] THEN
  ASM_SIMP_TAC[list_to_BlockReps_isDataElement]);;

(* HOL4 line 2360 *)
let list_to_BlockReps_data_up_to = prove
 (`!conf (x:((A)word_loc)heap_address) len xs
    (h2:(((A)word_loc,data_to_word_memoryProof_tag#B list)heap_element)list).
     ~(xs = []) ==>
     data_up_to (heap_length (list_to_BlockReps conf x len xs
                              :(((A)word_loc,data_to_word_memoryProof_tag#B list)
                                heap_element)list))
                (APPEND (list_to_BlockReps conf x len xs) h2)`,
  MESON_TAC[list_to_BlockReps_data_up_to_lem]);;

(* HOL4 line 2365 *)
let list_to_BlockReps_ForwardPointer = prove
 (`!conf (x:((A)word_loc)heap_address) len xs.
     ~(xs = []) ==>
     FILTER isForwardPointer
       (list_to_BlockReps conf x len xs
        :(((A)word_loc,data_to_word_memoryProof_tag#B list)heap_element)list) =
     []`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPECL [`x:((A)word_loc)heap_address`; `len:num`] o
    MATCH_MP (SPEC `conf:data_to_word_config` list_to_BlockReps_isDataElement)) THEN
  SPEC_TAC(`list_to_BlockReps conf (x:((A)word_loc)heap_address) len xs
            :(((A)word_loc,data_to_word_memoryProof_tag#B list)heap_element)list`,
           `hs:(((A)word_loc,data_to_word_memoryProof_tag#B list)heap_element)list`) THEN
  REWRITE_TAC[EVERY_isDataElement_IMP_LEMMA]);;

(* HOL4 line 2374 *)
let list_to_BlockReps_Ref = prove
 (`!xs len (x:((A)word_loc)heap_address) conf.
     ~(xs = []) ==>
     ALL (\v. ~isRef v)
       (list_to_BlockReps conf x len xs
        :(((A)word_loc,data_to_word_memoryProof_tag#B list)heap_element)list)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[NOT_CONS_NIL] THEN
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[list_to_BlockReps_def] THEN
  MP_TAC(ISPEC `t:(((A)word_loc)heap_address)list` list_CASES) THEN
    STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[ALL; BlockRep_def; isRef_def; isMutTag_def;
              distinctness "data_to_word_memoryProof_tag"] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[NOT_CONS_NIL]);;

(* HOL4 line 2382 *)
let list_to_BlockReps_NULL = prove
 (`!conf (x:((A)word_loc)heap_address) len xs.
     ~(xs = []) ==>
     ~(list_to_BlockReps conf x len xs
       :(((A)word_loc,data_to_word_memoryProof_tag#B list)heap_element)list =
       [])`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[NOT_CONS_NIL] THEN ONCE_REWRITE_TAC[list_to_BlockReps_def] THEN
  MP_TAC(ISPEC `t:(((A)word_loc)heap_address)list` list_CASES) THEN
    STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[NOT_CONS_NIL]);;

(* HOL4 line 2392 *)
let list_to_BlockReps_MEM = prove
 (`!v conf (x:((A)word_loc)heap_address) len h t.
     MEM v (list_to_BlockReps conf x len (CONS h t)
            :(((A)word_loc,data_to_word_memoryProof_tag#B list)heap_element)
             list) ==>
     MEM v (list_to_BlockReps conf x (len + 3) t) \/
     v = BlockRep cons_tag
           [h; Pointer (len + 3) (wl_Word (ptr_bits conf cons_tag 2))] \/
     v = BlockRep cons_tag [h; x]`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[list_to_BlockReps_def] THEN
  MP_TAC(ISPEC `t:(((A)word_loc)heap_address)list` list_CASES) THEN
    STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[MEM] THEN MESON_TAC[]);;

(* HOL4 line 2403 *)
let list_to_BlockReps_Pointer_lem = prove
 (`!conf (x:((A)word_loc)heap_address) xs len ys l
    (d:data_to_word_memoryProof_tag#B list) ptr u.
     let allocd = list_to_BlockReps conf x len xs in
       ~(xs = []) /\
       MEM (DataElement ys l d) allocd /\
       MEM (Pointer ptr u) ys ==>
         Pointer ptr u = x \/
         MEM (Pointer ptr u) xs \/
         (ptr < len + heap_length allocd /\
          ptr > len /\
          isSomeDataElement (heap_lookup (ptr - len) allocd))`,
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN BETA_TAC THEN
  (GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[NOT_CONS_NIL] THEN
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[list_to_BlockReps_def] THEN
  MP_TAC(ISPEC `t:(((A)word_loc)heap_address)list` list_CASES) THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN CASE_REWRITE_TAC[] THENL
   [REWRITE_TAC[MEM; BlockRep_def; injectivity "heap_element"] THEN STRIP_TAC THEN
    UNDISCH_TAC `MEM (Pointer ptr u) (ys:(((A)word_loc)heap_address)list)` THEN
    ASM_REWRITE_TAC[MEM] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[MEM; NOT_CONS_NIL] THEN STRIP_TAC) THENL
   [FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[BlockRep_def; injectivity "heap_element"] o
    check (MP1AUX_HEAD "=")) THEN STRIP_TAC THEN
  UNDISCH_TAC `MEM (Pointer ptr u) (ys:(((A)word_loc)heap_address)list)` THEN
  ASM_REWRITE_TAC[MEM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[injectivity "heap_address"]) THEN
  DISJ2_TAC THEN DISJ2_TAC THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN2 SUBST_ALL_TAC (K ALL_TAC) o check
    (fun th -> is_conj(concl th) && (try fst(dest_var(lhs(fst(dest_conj(concl th))))) = "ptr"
                                     with Failure _ -> false))) THEN
  SUBGOAL_THEN `el_length (BlockRep cons_tag
      [h; Pointer (len + 3) (wl_Word (ptr_bits conf cons_tag 2))]:
      (((A)word_loc,data_to_word_memoryProof_tag#B list)heap_element)) = 3`
    ASSUME_TAC THENL
   [REWRITE_TAC[BlockRep_def; el_length_def; LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[heap_lookup_def; ARITH_RULE `(len + 3) - len = 3`] THEN
  ASM_REWRITE_TAC[ARITH_RULE `~(3 = 0) /\ ~(3 < 3) /\ 3 - 3 = 0`] THEN
  REWRITE_TAC[heap_length_def; MAP; SUM] THEN REWRITE_TAC[GSYM heap_length_def] THEN
  ASM_SIMP_TAC[list_to_BlockReps_heap_length; NOT_CONS_NIL;
               list_to_BlockReps_heap_lookup_0] THEN
  REWRITE_TAC[LENGTH] THEN ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPECL [`len + 3`; `ys:(((A)word_loc)heap_address)list`; `l:num`;
    `d:data_to_word_memoryProof_tag#B list`; `ptr:num`; `u:(A)word_loc`]) THEN
  ASM_REWRITE_TAC[NOT_CONS_NIL; MEM] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  DISJ2_TAC THEN DISJ2_TAC THEN
  SUBGOAL_THEN `el_length (BlockRep cons_tag
      [h; Pointer (len + 3) (wl_Word (ptr_bits conf cons_tag 2))]:
      (((A)word_loc,data_to_word_memoryProof_tag#B list)heap_element)) = 3`
    ASSUME_TAC THENL
   [REWRITE_TAC[BlockRep_def; el_length_def; LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[heap_length_def; MAP; SUM] THEN REWRITE_TAC[GSYM heap_length_def] THEN
  REWRITE_TAC[heap_lookup_def] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(ptr - len = 0) /\ ~(ptr - len < 3) /\
                (ptr - len) - 3 = ptr - (len + 3)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

(* HOL4 line 2435 *)
let list_to_BlockReps_Pointer = prove
 (`!conf (x:((A)word_loc)heap_address) xs len ys l
    (d:data_to_word_memoryProof_tag#B list) ptr u.
     ~(xs = []) /\
     MEM (DataElement ys l d) (list_to_BlockReps conf x len xs) /\
     MEM (Pointer ptr u) ys ==>
     Pointer ptr u = x \/
     MEM (Pointer ptr u) xs \/
     (ptr < len + heap_length (list_to_BlockReps conf x len xs
                                :(((A)word_loc,data_to_word_memoryProof_tag#B list)
                                  heap_element)list) /\
      ptr > len /\
      isSomeDataElement (heap_lookup (ptr - len)
                           (list_to_BlockReps conf x len xs
                            :(((A)word_loc,data_to_word_memoryProof_tag#B list)
                              heap_element)list)))`,
  MP_TAC list_to_BlockReps_Pointer_lem THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN BETA_TAC THEN REWRITE_TAC[]);;

(* HOL4 line 2439 *)
let list_to_v_get_refs = prove
 (`!xs t r ts.
     MEM r (get_refs (data_list_to_v ts t xs)) ==>
     ?x. (MEM x xs \/ x = t) /\ MEM r (get_refs x)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[data_list_to_v_def; MEM] THENL
   [MESON_TAC[]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[get_refs_def; MAP; FLAT; APPEND_NIL; MEM_APPEND] THEN
  STRIP_TAC THENL
   [EXISTS_TAC `h:data_v` THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPECL [`t':data_v`; `r:num`; `ts + 1`]) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[]]);;

(* MP1AUX: filling the start of an unused block keeps every data element *)
let MP1AUX_heap_store_rel_expand = prove
 (`!ha hb (hs:((A,B)heap_element)list) sp.
     0 < heap_length hs /\ heap_length hs <= sp ==>
     heap_store_rel (APPEND (APPEND ha (heap_expand sp)) hb)
                    (APPEND (APPEND (APPEND ha hs)
                                    (heap_expand (sp - heap_length hs))) hb)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[heap_store_rel_def] THEN
  X_GEN_TAC `ptr:num` THEN
  ASM_CASES_TAC `ptr < heap_length (ha:((A,B)heap_element)list)` THENL
   [ASM_SIMP_TAC[GSYM APPEND_ASSOC; gc_shared_LESS_IMP_heap_lookup];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  ASM_SIMP_TAC[NOT_LESS_IMP_heap_lookup] THEN
  SUBGOAL_THEN `heap_expand sp:((A,B)heap_element)list = [Unused (sp - 1)]`
    SUBST1_TAC THENL
   [REWRITE_TAC[heap_expand_def] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[APPEND; heap_lookup_def; el_length_def] THEN
  ASM_CASES_TAC `ptr - heap_length (ha:((A,B)heap_element)list) = 0` THEN
  ASM_REWRITE_TAC[isSomeDataElement_def; option_INJ; distinctness "heap_element"] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT] THEN
  DISCH_THEN(K ALL_TAC) THEN
  REWRITE_TAC[APPEND_ASSOC] THEN
  SUBGOAL_THEN
   `~(ptr - heap_length (ha:((A,B)heap_element)list) <
      heap_length (APPEND hs (heap_expand (sp - heap_length hs)):
                   ((A,B)heap_element)list))`
   ASSUME_TAC THENL
   [REWRITE_TAC[heap_length_APPEND; gc_shared_heap_length_heap_expand] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[NOT_LESS_IMP_heap_lookup] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[heap_length_APPEND; gc_shared_heap_length_heap_expand] THEN
  ASM_ARITH_TAC);;

(* HOL4 line 2448 (the first of two theorems of this name; the unused    *)
(* bound variable y of HOL4 is left out)                                  *)
let v_inv_lemma = prove
 (`!conf ha hb hs sp ck v refs x f tf.
     v_inv conf v refs
       (x,f,tf,APPEND (APPEND ha (heap_expand sp)) hb
               :(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
                 heap_element)list) ==>
     0 < heap_length hs /\ heap_length hs <= sp ==>
     v_inv_ck ck conf v refs
       (x,f,tf,APPEND (APPEND (APPEND ha hs)
                              (heap_expand (sp - heap_length hs))) hb)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP v_inv_SUBMAP_lemma o check (MP1AUX_HEAD "v_inv")) THEN
  DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[SUBMAP_REFL] THEN
  MATCH_MP_TAC MP1AUX_heap_store_rel_expand THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 2504 (allow_rebind: replaces the theorem above) *)
let v_inv_lemma = prove
 (`!conf v refs x f tf hs ha hb sp.
     0 < heap_length hs /\
     heap_length hs <= sp /\
     v_inv conf v refs
       (x,f,tf,APPEND (APPEND ha (heap_expand sp)) hb
               :(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
                 heap_element)list) ==>
     v_inv conf v refs
       (x,f,tf,APPEND (APPEND (APPEND ha hs)
                              (heap_expand (sp - heap_length hs))) hb)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[v_inv_eq] THEN GEN_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP v_inv_lemma) THEN
  ASM_SIMP_TAC[]);;

(* HOL4 line 2514 *)
let v_inv_LIST_REL = prove
 (`!conf refs f tf
    (hs:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
         heap_element)list) ha hb sp l1 l2.
     0 < heap_length hs /\
     heap_length hs <= sp /\
     ALL2 (\z y. v_inv conf y refs
                   (z,f,tf,APPEND (APPEND ha (heap_expand sp)) hb)) l1 l2
     ==>
     ALL2 (\z y. v_inv conf y refs
                   (z,f,tf,APPEND (APPEND (APPEND ha hs)
                                          (heap_expand (sp - heap_length hs)))
                                  hb)) l1 l2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_comb o concl)) THEN
  MATCH_MP_TAC MONO_ALL2 THEN REPEAT GEN_TAC THEN BETA_TAC THEN
  ASM_MESON_TAC[v_inv_lemma]);;

(* HOL4 line 2528 *)
let bind_each_def = cake_def
  `bind_each tf ts (k:num) (i:num) 0 = (tf:(num,num)fmap) /\
   bind_each tf ts (k:num) i (SUC n) = bind_each tf (ts + 1) (k + i) i n |+ (ts,k)`;;

(* HOL4 line 2533 *)
let bind_each_MONO = prove
 (`!n t1 t2 tf k i.
     t1 < t2 /\ (!t. t IN FDOM tf ==> t < t1)
     ==> ~(t1 IN FDOM (bind_each tf t2 k i n))`,
  INDUCT_TAC THEN REWRITE_TAC[bind_each_def; FDOM_FUPDATE; IN_INSERT] THENL
   [MESON_TAC[LT_REFL];
    REPEAT STRIP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`t1:num`; `t2 + 1`; `tf:(num,num)fmap`;
                                  `k + i:num`; `i:num`]) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

(* HOL4 line 2544 *)
let bind_each_SUBMAP = prove
 (`!n tf ts k i.
     (!t. t IN FDOM tf ==> t < ts) ==> tf SUBMAP bind_each tf ts k i n`,
  INDUCT_TAC THEN REWRITE_TAC[bind_each_def; SUBMAP_REFL] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBMAP_TRANS THEN
  EXISTS_TAC `bind_each tf (ts + 1) (k + i) i n` THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_MESON_TAC[ARITH_RULE `t < ts ==> t < ts + 1`];
    MATCH_MP_TAC SUBMAP_FUPDATE_EXTENDED THEN MATCH_MP_TAC bind_each_MONO THEN
    ASM_REWRITE_TAC[ARITH_RULE `ts < ts + 1`]]);;

(* MP1AUX: heap_store_rel is reflexive *)
let MP1AUX_heap_store_rel_refl = prove
 (`!heap:((A,B)heap_element)list. heap_store_rel heap heap`,
  REWRITE_TAC[heap_store_rel_def]);;

(* HOL4 line 2561 *)
let v_inv_list_to_v_lem = prove
 (`!conf refs f tf rs xs t (rt:((A)word_loc)heap_address) ha hb sp ts.
     let hm = list_to_BlockReps conf rt (heap_length ha) rs in
       ~(rs = []) /\
       v_inv conf t refs
         (rt,f,tf,APPEND (APPEND ha (heap_expand sp)) hb
                  :(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
                    heap_element)list) /\
       ALL2 (\v x. v_inv conf v refs
                     (x,f,tf,APPEND (APPEND ha (heap_expand sp)) hb)) xs rs /\
       heap_length hm <= sp /\ (!t. t IN FDOM tf ==> t < ts)
       ==>
       v_inv conf (data_list_to_v ts t xs) refs
         (Pointer (heap_length ha) (wl_Word (ptr_bits conf cons_tag 2)),
          f, bind_each tf ts (heap_length ha) 3 (LENGTH xs),
          APPEND (APPEND (APPEND ha hm) (heap_expand (sp - heap_length hm))) hb)`,
  (REWRITE_TAC[LET_DEF; LET_END_DEF] THEN BETA_TAC THEN
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL [REWRITE_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `r:((A)word_loc)heap_address` THEN
  X_GEN_TAC `rs:(((A)word_loc)heap_address)list` THEN
  DISCH_THEN(LABEL_TAC "IH") THEN
  X_GEN_TAC `xs:(data_v)list` THEN
  MP_TAC(ISPEC `xs:(data_v)list` list_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC
    (X_CHOOSE_THEN `x:data_v` (X_CHOOSE_THEN `xs1:(data_v)list` SUBST1_TAC))) THEN
  REWRITE_TAC[ALL2] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(ts IN FDOM (tf:(num,num)fmap))` ASSUME_TAC THENL
   [ASM_MESON_TAC[LT_REFL]; ALL_TAC] THEN
  REWRITE_TAC[data_list_to_v_def; LENGTH; bind_each_def] THEN
  MP_TAC(ISPEC `rs:(((A)word_loc)heap_address)list` list_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC
    (X_CHOOSE_THEN `r2:((A)word_loc)heap_address`
      (X_CHOOSE_THEN `rs2:(((A)word_loc)heap_address)list` SUBST_ALL_TAC)))) THENL
   [(* one element *)
    FIRST_X_ASSUM(MP_TAC o check (MP1AUX_HEAD "ALL2")) THEN
  MP_TAC(ISPEC `xs1:(data_v)list` list_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC
    (X_CHOOSE_THEN `x2:data_v` (X_CHOOSE_THEN `xs2:(data_v)list` SUBST1_TAC))) THEN
  REWRITE_TAC[ALL2] THEN
  REWRITE_TAC[data_list_to_v_def; LENGTH; bind_each_def] THEN
  SUBGOAL_THEN `list_to_BlockReps conf (rt:((A)word_loc)heap_address)
                  (heap_length (ha:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list)) [r] =
                [BlockRep cons_tag [r; rt]:((A)word_loc,data_to_word_memoryProof_tag#
                                            ((A)word_loc)list)heap_element]`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL
   [ONCE_REWRITE_TAC[list_to_BlockReps_def] THEN CASE_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `heap_length [BlockRep cons_tag [r; rt]:((A)word_loc,
                  data_to_word_memoryProof_tag#((A)word_loc)list)heap_element] = 3`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th] THEN
               ASSUME_TAC th) THENL
   [REWRITE_TAC[heap_length_def; MAP; SUM; BlockRep_def; el_length_def; LENGTH] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `heap_store_rel (APPEND (APPEND ha (heap_expand sp)) hb)
      (APPEND (APPEND (APPEND ha [BlockRep cons_tag [r; rt]])
                      (heap_expand (sp - 3)))
              (hb:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
                   heap_element)list))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ha:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
                         heap_element)list`;
                   `hb:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
                         heap_element)list`;
                   `[BlockRep cons_tag [r; rt]:((A)word_loc,
                      data_to_word_memoryProof_tag#((A)word_loc)list)heap_element]`;
                   `sp:num`] MP1AUX_heap_store_rel_expand) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(tf:(num,num)fmap) SUBMAP tf |+ (ts,heap_length
                  (ha:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
                       heap_element)list))` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBMAP_FUPDATE_EXTENDED THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[v_inv_def; NOT_CONS_NIL] THEN
  MAP_EVERY EXISTS_TAC
   [`heap_length (ha:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
                      heap_element)list)`;
    `[r; rt]:(((A)word_loc)heap_address)list`] THEN
  REWRITE_TAC[ALL2; LENGTH; FLOOKUP_UPDATE; ARITH_RULE `SUC (SUC 0) = 2`] THEN
  BETA_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC v_inv_SUBMAP THEN
    MAP_EVERY EXISTS_TAC [`f:(num,num)fmap`; `tf:(num,num)fmap`;
      `APPEND (APPEND ha (heap_expand sp)) (hb:(((A)word_loc,
         data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list)`] THEN
    ASM_REWRITE_TAC[SUBMAP_REFL];
    MATCH_MP_TAC v_inv_SUBMAP THEN
    MAP_EVERY EXISTS_TAC [`f:(num,num)fmap`; `tf:(num,num)fmap`;
      `APPEND (APPEND ha (heap_expand sp)) (hb:(((A)word_loc,
         data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list)`] THEN
    ASM_REWRITE_TAC[SUBMAP_REFL];
    REWRITE_TAC[GSYM APPEND_ASSOC; APPEND; heap_lookup_PREFIX]];
    (* two or more elements *)
    ABBREV_TAC `B1 = BlockRep cons_tag
     [r; Pointer (heap_length (ha:(((A)word_loc,data_to_word_memoryProof_tag#
                    ((A)word_loc)list)heap_element)list) + 3)
                 (wl_Word (ptr_bits conf cons_tag 2))]
     :((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element` THEN
  ABBREV_TAC `hm = list_to_BlockReps conf (rt:((A)word_loc)heap_address)
     (heap_length (ha:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
                       heap_element)list) + 3) (CONS r2 rs2)
     :(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list` THEN
  SUBGOAL_THEN `list_to_BlockReps conf (rt:((A)word_loc)heap_address)
                  (heap_length (ha:(((A)word_loc,data_to_word_memoryProof_tag#
                     ((A)word_loc)list)heap_element)list)) (CONS r (CONS r2 rs2)) =
                CONS (B1:((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
                          heap_element)
                     (hm:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
                          heap_element)list)` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN
                                     REWRITE_TAC[th]) THENL
   [ONCE_REWRITE_TAC[list_to_BlockReps_def] THEN CASE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `el_length (B1:((A)word_loc,data_to_word_memoryProof_tag#
                  ((A)word_loc)list)heap_element) = 3` ASSUME_TAC THENL
   [EXPAND_TAC "B1" THEN REWRITE_TAC[BlockRep_def; el_length_def; LENGTH] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `heap_length (CONS (B1:((A)word_loc,data_to_word_memoryProof_tag#
                  ((A)word_loc)list)heap_element) hm) =
                3 + heap_length (hm:(((A)word_loc,data_to_word_memoryProof_tag#
                                       ((A)word_loc)list)heap_element)list)`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL
   [REWRITE_TAC[heap_length_def; MAP; SUM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `heap_length [B1:((A)word_loc,data_to_word_memoryProof_tag#
                  ((A)word_loc)list)heap_element] = 3` ASSUME_TAC THENL
   [REWRITE_TAC[heap_length_def; MAP; SUM] THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  REMOVE_THEN "IH" (MP_TAC o SPECL [`xs1:(data_v)list`; `t:data_v`;
    `rt:((A)word_loc)heap_address`;
    `APPEND ha [B1:((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
                   heap_element]`;
    `hb:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
         heap_element)list`; `sp - 3`; `ts + 1`]) THEN
  ASM_REWRITE_TAC[heap_length_APPEND; NOT_CONS_NIL] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`conf:data_to_word_config`; `t:data_v`;
        `refs:((data_v)bvl_ref)spt`; `rt:((A)word_loc)heap_address`;
        `f:(num,num)fmap`; `tf:(num,num)fmap`;
        `[B1:((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
             heap_element]`;
        `ha:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
             heap_element)list`;
        `hb:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
             heap_element)list`; `sp:num`] v_inv_lemma) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
      UNDISCH_TAC `ALL2 (\v x. v_inv conf v refs
         (x,f,tf,APPEND (APPEND ha (heap_expand sp))
                  (hb:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
                       heap_element)list))) xs1 (CONS r2 rs2)` THEN
      MATCH_MP_TAC MONO_ALL2 THEN REPEAT GEN_TAC THEN BETA_TAC THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`conf:data_to_word_config`; `x':data_v`;
        `refs:((data_v)bvl_ref)spt`; `y:((A)word_loc)heap_address`;
        `f:(num,num)fmap`; `tf:(num,num)fmap`;
        `[B1:((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
             heap_element]`;
        `ha:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
             heap_element)list`;
        `hb:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
             heap_element)list`; `sp:num`] v_inv_lemma) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
      ASM_ARITH_TAC;
      ASM_MESON_TAC[ARITH_RULE `t < ts ==> t < ts + 1`]];
    DISCH_TAC] THEN
    SUBGOAL_THEN
   `APPEND (APPEND (APPEND (APPEND ha [B1]) hm) (heap_expand (sp - 3 - heap_length hm))) hb =
    APPEND (APPEND (APPEND ha (CONS B1 hm)) (heap_expand (sp - (3 + heap_length hm))))
           (hb:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
                heap_element)list)`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [REWRITE_TAC[GSYM APPEND_ASSOC; APPEND;
                ARITH_RULE `!sp h. sp - 3 - h = sp - (3 + h)`];
    ALL_TAC] THEN
  SUBGOAL_THEN `heap_length (CONS (B1:((A)word_loc,data_to_word_memoryProof_tag#
                  ((A)word_loc)list)heap_element) hm) = 3 + heap_length hm`
    ASSUME_TAC THENL
   [REWRITE_TAC[heap_length_def; MAP; SUM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `heap_store_rel (APPEND (APPEND ha (heap_expand sp)) hb)
      (APPEND (APPEND (APPEND ha (CONS B1 hm)) (heap_expand (sp - (3 + heap_length hm))))
              (hb:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
                   heap_element)list))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ha:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
                         heap_element)list`;
                   `hb:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
                         heap_element)list`;
                   `CONS (B1:((A)word_loc,data_to_word_memoryProof_tag#
                      ((A)word_loc)list)heap_element) hm`;
                   `sp:num`] MP1AUX_heap_store_rel_expand) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `bind_each tf (ts + 1) (heap_length ha + 3) 3 (LENGTH (xs1:(data_v)list)) SUBMAP
    bind_each tf (ts + 1) (heap_length ha + 3) 3 (LENGTH xs1) |+
      (ts,heap_length (ha:(((A)word_loc,data_to_word_memoryProof_tag#
                            ((A)word_loc)list)heap_element)list))` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBMAP_FUPDATE_EXTENDED THEN MATCH_MP_TAC bind_each_MONO THEN
    ASM_REWRITE_TAC[ARITH_RULE `ts < ts + 1`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(tf:(num,num)fmap) SUBMAP
    bind_each tf (ts + 1) (heap_length ha + 3) 3 (LENGTH (xs1:(data_v)list)) |+
      (ts,heap_length (ha:(((A)word_loc,data_to_word_memoryProof_tag#
                            ((A)word_loc)list)heap_element)list))` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBMAP_TRANS THEN
    EXISTS_TAC `bind_each tf (ts + 1) (heap_length (ha:(((A)word_loc,
      data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list) + 3) 3
      (LENGTH (xs1:(data_v)list))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC bind_each_SUBMAP THEN
    ASM_MESON_TAC[ARITH_RULE `t < ts ==> t < ts + 1`];
    ALL_TAC] THEN
  REWRITE_TAC[v_inv_def; NOT_CONS_NIL] THEN
  MAP_EVERY EXISTS_TAC
   [`heap_length (ha:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
                      heap_element)list)`;
    `[r:((A)word_loc)heap_address; Pointer (heap_length (ha:(((A)word_loc,data_to_word_memoryProof_tag#
                    ((A)word_loc)list)heap_element)list) + 3)
                 (wl_Word (ptr_bits conf cons_tag 2))]`] THEN
  REWRITE_TAC[ALL2; LENGTH; FLOOKUP_UPDATE; ARITH_RULE `SUC (SUC 0) = 2`] THEN
  BETA_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC v_inv_SUBMAP THEN
    MAP_EVERY EXISTS_TAC [`f:(num,num)fmap`; `tf:(num,num)fmap`;
      `APPEND (APPEND ha (heap_expand sp)) (hb:(((A)word_loc,
         data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list)`] THEN
    ASM_REWRITE_TAC[SUBMAP_REFL];
    MATCH_MP_TAC v_inv_SUBMAP THEN
    MAP_EVERY EXISTS_TAC [`f:(num,num)fmap`;
      `bind_each tf (ts + 1) (heap_length (ha:(((A)word_loc,
         data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list) + 3) 3
         (LENGTH (xs1:(data_v)list))`;
      `APPEND (APPEND (APPEND ha (CONS B1 hm)) (heap_expand (sp - (3 + heap_length hm))))
              (hb:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
                   heap_element)list)`] THEN
    ASM_REWRITE_TAC[SUBMAP_REFL; MP1AUX_heap_store_rel_refl];
    ASM_REWRITE_TAC[GSYM APPEND_ASSOC; APPEND; heap_lookup_PREFIX]]]);;

(* HOL4 line 2670 *)
let v_inv_list_to_v = prove
 (`!conf refs f tf rs xs t (rt:((A)word_loc)heap_address) ha hb sp ts.
     ~(rs = []) /\
     v_inv conf t refs
       (rt,f,tf,APPEND (APPEND ha (heap_expand sp)) hb
                :(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
                  heap_element)list) /\
     ALL2 (\v x. v_inv conf v refs
                   (x,f,tf,APPEND (APPEND ha (heap_expand sp)) hb)) xs rs /\
     heap_length (list_to_BlockReps conf rt (heap_length ha) rs
                  :(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
                    heap_element)list) <= sp /\
     (!t. t IN FDOM tf ==> t < ts)
     ==>
     v_inv conf (data_list_to_v ts t xs) refs
       (Pointer (heap_length ha) (wl_Word (ptr_bits conf cons_tag 2)),
        f, bind_each tf ts (heap_length ha) 3 (LENGTH xs),
        APPEND (APPEND (APPEND ha (list_to_BlockReps conf rt (heap_length ha) rs))
                       (heap_expand
                          (sp - heap_length (list_to_BlockReps conf rt
                                               (heap_length ha) rs
                                 :(((A)word_loc,data_to_word_memoryProof_tag#
                                    ((A)word_loc)list)heap_element)list)))) hb)`,
  MP_TAC v_inv_list_to_v_lem THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN BETA_TAC THEN REWRITE_TAC[]);;

(* MP1AUX: the time stamps of a block value *)
let MP1AUX_MEM_v_all_ts_Block = prove
 (`!t ts tag xs.
     MEM t (v_all_ts (data_Block ts tag xs)) <=>
     t = ts \/ ?y. MEM y xs /\ MEM t (v_all_ts y)`,
  REWRITE_TAC[v_all_ts_def; MEM; MEM_FLAT; MEM_MAP] THEN MESON_TAC[]);;

(* MP1AUX: a value that is not a block has no time stamps *)
let MP1AUX_v_all_ts_no_block = prove
 (`!v. (!ts tag xs. ~(v = data_Block ts tag xs)) ==> v_all_ts v = []`,
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `v:data_v` MP1AUX_data_v_nchotomy) THEN
  REWRITE_TAC[v_all_ts_def; injectivity "data_v"; distinctness "data_v"] THEN
  MESON_TAC[]);;

(* HOL4 line 2675 *)
let all_ts_cons = prove
 (`!refs stack ts tag xs.
     all_ts refs (CONS (data_Block ts tag xs) stack) =
     ts INSERT all_ts refs (APPEND xs stack)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[all_ts_def; LET_DEF; LET_END_DEF; EXTENSION; IN_INSERT;
              IN_ELIM_THM; MEM; MEM_APPEND] THEN
  MESON_TAC[MP1AUX_MEM_v_all_ts_Block]);;

(* HOL4 line 2693 *)
let all_ts_cons_no_block = prove
 (`!refs stack v.
     (!ts tag xs. ~(v = data_Block ts tag xs)) ==>
     all_ts refs (CONS v stack) = all_ts refs stack`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP MP1AUX_v_all_ts_no_block) THEN
  REWRITE_TAC[all_ts_def; LET_DEF; LET_END_DEF; EXTENSION; IN_ELIM_THM; MEM] THEN
  ASM_MESON_TAC[MEM]);;

(* HOL4 line 2704 *)
let all_ts_in_no_block = prove
 (`!refs stack v t.
     (!ts tag xs. ~(v = data_Block ts tag xs)) /\
     t IN all_ts refs (CONS v stack)
     ==> t IN all_ts refs stack`,
  MESON_TAC[all_ts_cons_no_block]);;

(* HOL4 line 2715 *)
let all_ts_append = prove
 (`!refs x y. all_ts refs (APPEND x y) = all_ts refs x UNION all_ts refs y`,
  REWRITE_TAC[all_ts_def; LET_DEF; LET_END_DEF; EXTENSION; IN_UNION;
              IN_ELIM_THM; MEM_APPEND] THEN
  MESON_TAC[]);;

(* HOL4 line 2724 *)
let all_ts_head = prove
 (`!refs x xs. all_ts refs (CONS x xs) = all_ts refs [x] UNION all_ts refs xs`,
  REWRITE_TAC[GSYM all_ts_append; APPEND]);;

(* HOL4 line 2730 *)
let v_all_vs_MEM = prove
 (`!l ts tag xs.
     MEM (data_Block ts tag xs) (v_all_vs l)
     ==> ?x y. v_all_vs l =
               APPEND (APPEND x (CONS (data_Block ts tag xs) (v_all_vs xs))) y`,
  let USE_IH_TAC =
    FIRST_X_ASSUM(fun mem -> FIRST_X_ASSUM(fun ih -> MP_TAC(MATCH_MP ih mem))) THEN
    DISCH_THEN(X_CHOOSE_THEN `x0:(data_v)list`
      (X_CHOOSE_THEN `y0:(data_v)list` SUBST1_TAC)) in
  let CONS_WITNESS_TAC : tactic = fun (asl,w as g) ->
    let c = rand(rator(lhs(snd(strip_exists w)))) in
    MAP_EVERY EXISTS_TAC
     [mk_comb(mk_comb(`CONS:data_v->(data_v)list->(data_v)list`,c),`x0:(data_v)list`);
      `y0:(data_v)list`] g in
  MATCH_MP_TAC v_all_vs_ind THEN REWRITE_TAC[v_all_vs_def; MEM; MEM_APPEND] THEN
  REWRITE_TAC[distinctness "data_v"; injectivity "data_v"] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  STRIP_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`[]:(data_v)list`; `v_all_vs xs`] THEN
    REWRITE_TAC[APPEND];
    USE_IH_TAC THEN
    MAP_EVERY EXISTS_TAC [`CONS (data_Block ts tag l) x0`;
                          `APPEND y0 (v_all_vs xs)`] THEN
    REWRITE_TAC[APPEND; GSYM APPEND_ASSOC];
    USE_IH_TAC THEN
    MAP_EVERY EXISTS_TAC [`CONS (data_Block ts tag l) (APPEND (v_all_vs l) x0)`;
                          `y0:(data_v)list`] THEN
    REWRITE_TAC[APPEND; GSYM APPEND_ASSOC];
    USE_IH_TAC THEN CONS_WITNESS_TAC THEN REWRITE_TAC[APPEND; GSYM APPEND_ASSOC];
    USE_IH_TAC THEN CONS_WITNESS_TAC THEN REWRITE_TAC[APPEND; GSYM APPEND_ASSOC];
    USE_IH_TAC THEN CONS_WITNESS_TAC THEN REWRITE_TAC[APPEND; GSYM APPEND_ASSOC];
    USE_IH_TAC THEN CONS_WITNESS_TAC THEN REWRITE_TAC[APPEND; GSYM APPEND_ASSOC]]);;
