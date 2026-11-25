(* ========================================================================= *)
(* cfLetAuto: port of HOL4 characteristic/cfLetAutoScript.sml (CakeML        *)
(* v3479).  Definitions and lemmas that support the implementation of the    *)
(* xlet_auto tactic.                                                         *)
(*                                                                           *)
(* Notation as in characteristic/cfHeapsBase.ml (STAR for HOL4's star,       *)
(* set_sep_cond for its ampersand, set_sep_one for one, ~~>> and ~~> for     *)
(* cell and REF); LIST_REL is ALL2, EVERY is ALL, HOL4's unit () is one,     *)
(* INT and NUM are ml_INT and ml_NUM.  HOL4's variable abs (an interface     *)
(* name in HOL Light) is a, as in translator/ml_translator.ml.               *)
(* HOL4's proofs of NON_OVERLAP_FFI_PART_HFS use ALL_DISTINCT_FLAT_MEM_IMP   *)
(* and ALL_DISTINCT_FLAT_FST_IMP of the theory cf (not ported yet): local    *)
(* copies CF1AUX_ALL_DISTINCT_FLAT_MEM_IMP and CF1AUX_ALL_DISTINCT_FLAT_FST_ *)
(* IMP here.  Helper lemmas that are not HOL4 theorems are CF1AUX_.          *)
(* ========================================================================= *)

needs "characteristic/cfStore.ml";;
needs "characteristic/cfHeapsBase.ml";;
needs "hol4/set_sep.ml";;
needs "translator/ml_translator.ml";;

type_invention_error := true;;

(* Rewrite rules for the int_of_num & operator *)

let cf_INT_OF_NUM_ADD = prove
 (`!(x:num) (y:num). (&x:int) + &y = &(x + y)`,
  REWRITE_TAC[INT_OF_NUM_ADD]);;

let INT_OF_NUM_TIMES = prove
 (`!(x:num) (y:num). (&x:int) * &y = &(x * y)`,
  REWRITE_TAC[INT_OF_NUM_MUL]);;

let cf_INT_OF_NUM_LE = prove
 (`!(x:num) (y:num). (&x <= (&y):int) <=> (x <= y)`,
  REWRITE_TAC[INT_OF_NUM_LE]);;

let INT_OF_NUM_LESS = prove
 (`!(x:num) (y:num). (&x < (&y):int) <=> (x < y)`,
  REWRITE_TAC[INT_OF_NUM_LT]);;

let cf_INT_OF_NUM_GE = prove
 (`!(x:num) (y:num). (&x >= (&y):int) <=> (x >= y)`,
  REWRITE_TAC[INT_OF_NUM_GE]);;

let INT_OF_NUM_GREAT = prove
 (`!(x:num) (y:num). (&x > (&y):int) <=> (x > y)`,
  REWRITE_TAC[INT_OF_NUM_GT]);;

let cf_INT_OF_NUM_EQ = prove
 (`!(x:num) (y:num). (&x = (&y):int) <=> (x = y)`,
  REWRITE_TAC[INT_OF_NUM_EQ]);;

let INT_OF_NUM_SUBS = prove
 (`!(x:num) (y:num) (z:num). (&x - (&y):int = &z) <=> (x - y = z) /\ y <= x`,
  REWRITE_TAC[INT_EQ_SUB_RADD; INT_OF_NUM_ADD; INT_OF_NUM_EQ] THEN ARITH_TAC);;

let INT_OF_NUM_SUBS_2 = prove
 (`!(x:num) (y:num). y <= x ==> (&x - (&y):int = &(x - y))`,
  SIMP_TAC[INT_OF_NUM_SUB]);;

(* TODO: move that *)
let SPLIT_SUBSET = prove
 (`SPLIT (s:A->bool) (u, v) ==> u SUBSET s /\ v SUBSET s`,
  REWRITE_TAC[SPLIT_def] THEN SET_TAC[]);;

(* Predicate stating that a heap is valid *)
let HEAP_FROM_STATE_def = cake_def
  `HEAP_FROM_STATE (s:heap) <=>
     ?(f:(ffi->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)) (st:(ffi)state).
       s = st2heap f st`;;

let VALID_HEAP_def = cake_def
  `VALID_HEAP (s:heap) <=>
     ?(f:(ffi->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)) (st:(ffi)state).
       s SUBSET (st2heap f st)`;;

let VALID_HEAP_SUBSET = prove
 (`VALID_HEAP s1 ==> s2 SUBSET s1 ==> VALID_HEAP s2`,
  REWRITE_TAC[VALID_HEAP_def] THEN MESON_TAC[SUBSET_TRANS]);;

(* A theorem to remove the pure facts from the heap predicates *)
let cf_HCOND_EXTRACT = prove
 (`((set_sep_cond A STAR (H:(B->bool)->bool)) s <=> A /\ H s) /\
   ((H STAR set_sep_cond A) s <=> H s /\ A) /\
   ((H STAR set_sep_cond A STAR H') s <=> (H STAR H') s /\ A)`,
  REWRITE_TAC[cond_MOVE; cond_STAR] THEN CONV_TAC TAUT);;

(* Definitions and theorems used to compare two heap conditions *)
let HPROP_INJ_def = cake_def
  `HPROP_INJ (H1:hprop) (H2:hprop) PF <=>
     !s. VALID_HEAP s ==>
         !G1 G2. (H1 STAR G1) s ==>
                 ((H2 STAR G2) s <=> (set_sep_cond PF STAR H1 STAR G2) s)`;;

(* HOL4: a commented-out HPROP_FRAME_IMP and HPROP_FRAME_HCOND *)

(* The following lemmas aim to prove that a valid heap can not have one     *)
(* pointer pointing to two different values                                 *)

let PTR_MEM_LEM = prove
 (`!s l xv H. (l ~~>> xv STAR H) s ==> cf_Mem l xv IN s`,
  REWRITE_TAC[STAR_def; SPLIT_def; cf_cell_def; set_sep_one_def] THEN SET_TAC[]);;

(* Intermediate lemma to reason on subsets of heaps *)
let HEAP_SUBSET_GC = prove
 (`!s s' (H:hprop). s SUBSET s' ==> H s ==> (H STAR cf_GC) s'`,
  REWRITE_TAC[STAR_def; SPLIT_EQ; cf_GC_def; SEP_EXISTS_THM] THEN
  REPEAT STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`s:heap`; `s' DIFF s:heap`] THEN
  ASM_REWRITE_TAC[] THEN EXISTS_TAC `\x:heap. T` THEN REWRITE_TAC[]);;

(* UNIQUE_PTRS property for a heap converted from a state *)
let UNIQUE_PTRS_HFS = prove
 (`!s. HEAP_FROM_STATE s ==>
       !l xv xv' H H'. (l ~~>> xv STAR H) s /\ (l ~~>> xv' STAR H') s ==> xv' = xv`,
  REWRITE_TAC[HEAP_FROM_STATE_def] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `cf_Mem l xv IN s /\ cf_Mem l xv' IN s` MP_TAC THENL
   [ASM_MESON_TAC[PTR_MEM_LEM]; ALL_TAC] THEN
  ASM_REWRITE_TAC[st2heap_def; IN_UNION; Mem_NOT_IN_ffi2heap] THEN
  MESON_TAC[store2heap_IN_unique_key]);;

let UNIQUE_PTRS = prove
 (`!s. VALID_HEAP s ==>
       !l xv xv' H H'. (l ~~>> xv STAR H) s /\ (l ~~>> xv' STAR H') s ==> xv' = xv`,
  REWRITE_TAC[VALID_HEAP_def] THEN REPEAT STRIP_TAC THEN
  QSPEC_THEN "st2heap f st" MP_TAC UNIQUE_PTRS_HFS THEN
  REWRITE_TAC[HEAP_FROM_STATE_def] THEN
  ANTS_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`l:num`; `H STAR cf_GC`; `H' STAR cf_GC`] THEN
  REWRITE_TAC[STAR_ASSOC] THEN ASM_MESON_TAC[HEAP_SUBSET_GC]);;

let PTR_IN_HEAP = prove
 (`!l xv H s. (Loc T l ~~> xv STAR H) s ==> cf_Mem l (Refv xv) IN s`,
  REWRITE_TAC[cf_REF_def; SEP_CLAUSES; SEP_EXISTS_THM; GSYM STAR_ASSOC; cond_STAR] THEN
  SIMP[] THEN MESON_TAC[PTR_MEM_LEM]);;

(* HOL4: prove_hprop_inj_tac thm *)
let CF1AUX_HPROP_INJ_TAC th =
  REWRITE_TAC[HPROP_INJ_def; SEP_CLAUSES; GSYM STAR_ASSOC; cf_HCOND_EXTRACT] THEN
  MESON_TAC[th];;

let PTR_HPROP_INJ = prove
 (`!l xv xv'. HPROP_INJ (l ~~>> xv) (l ~~>> xv') (xv' = xv)`,
  CF1AUX_HPROP_INJ_TAC UNIQUE_PTRS);;

(* Unicity results for pointers (HOL4: solve_unique_refs) *)
let CF1AUX_UNIQUE_REFS_TAC =
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[cf_REF_def; cf_ARRAY_def; cf_W8ARRAY_def; SEP_CLAUSES; SEP_EXISTS_THM;
              GSYM STAR_ASSOC; cond_STAR] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP UNIQUE_PTRS) THEN
  GVS[] THEN ASM_MESON_TAC[injectivity "store_v"];;

let UNIQUE_REFS = prove
 (`!s r xv xv' H H'.
     VALID_HEAP s ==> (r ~~> xv STAR H) s /\ (r ~~> xv' STAR H') s ==> xv' = xv`,
  CF1AUX_UNIQUE_REFS_TAC);;

let UNIQUE_ARRAYS = prove
 (`!s a av av' H H'.
     VALID_HEAP s ==> (cf_ARRAY a av STAR H) s /\ (cf_ARRAY a av' STAR H') s ==> av' = av`,
  CF1AUX_UNIQUE_REFS_TAC);;

let UNIQUE_W8ARRAYS = prove
 (`!s a av av' H H'.
     VALID_HEAP s ==>
     (cf_W8ARRAY a av STAR H) s /\ (cf_W8ARRAY a av' STAR H') s ==> av' = av`,
  CF1AUX_UNIQUE_REFS_TAC);;

let REF_HPROP_INJ = prove
 (`!r xv xv'. HPROP_INJ (r ~~> xv) (r ~~> xv') (xv' = xv)`,
  CF1AUX_HPROP_INJ_TAC UNIQUE_REFS);;

let ARRAY_HPROP_INJ = prove
 (`!a av av'. HPROP_INJ (cf_ARRAY a av) (cf_ARRAY a av') (av' = av)`,
  CF1AUX_HPROP_INJ_TAC UNIQUE_ARRAYS);;

let W8ARRAY_HPROP_INJ = prove
 (`!a av av'. HPROP_INJ (cf_W8ARRAY a av) (cf_W8ARRAY a av') (av' = av)`,
  CF1AUX_HPROP_INJ_TAC UNIQUE_W8ARRAYS);;

(* helpers: HOL4's cf ALL_DISTINCT_FLAT_MEM_IMP and ALL_DISTINCT_FLAT_FST_IMP *)
(* (theory cf, not ported yet)                                               *)

let CF1AUX_ALL_DISTINCT_FLAT_MEM_IMP = prove
 (`!p2 ns ns' (m:A). ALL_DISTINCT (FLAT p2) /\ MEM ns' p2 /\ MEM ns p2 /\
                     MEM m ns' /\ MEM m ns ==> ns = ns'`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[FLAT; MEM; ALL_DISTINCT_APPEND] THEN
  ASM_MESON_TAC[MEM_FLAT]);;

let CF1AUX_NONEMPTY_MEM = prove
 (`!l:A list. ~(l = []) ==> ?e. MEM e l`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MEM] THEN MESON_TAC[]);;

let CF1AUX_FLAT_MAP_FST_MEM = prove
 (`!t (ns:A list) (u:B) e. MEM (ns,u) t /\ MEM e ns ==> MEM e (FLAT (MAP FST t))`,
  REWRITE_TAC[MEM_FLAT; MEM_MAP] THEN MESON_TAC[FST]);;

let CF1AUX_ALL_DISTINCT_FLAT_FST_IMP = prove
 (`!p2 (ns:A list) (u:B) u'.
     ALL_DISTINCT (FLAT (MAP FST p2)) /\
     MEM (ns,u') p2 /\ MEM (ns,u) p2 /\ ~(ns = []) ==> u = u'`,
  let pair_tac =
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
      check (fun th -> is_eq(concl th) && is_var(rhs(concl th)))) THEN
    MP_TAC(ISPEC `ns:A list` CF1AUX_NONEMPTY_MEM) THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[FST]) THEN
    ASM_MESON_TAC[CF1AUX_FLAT_MAP_FST_MEM] in
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; FLAT; MEM; ALL_DISTINCT_APPEND] THEN
  REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[PAIR_EQ]; pair_tac; pair_tac; ASM_MESON_TAC[]]);;

(* A valid heap must have proper ffi partitions *)
let NON_OVERLAP_FFI_PART_HFS = prove
 (`!s. HEAP_FROM_STATE s ==>
       !s1 u1 ns1 ts1 s2 u2 ns2 ts2.
         cf_FFI_part s1 u1 ns1 ts1 IN s /\ cf_FFI_part s2 u2 ns2 ts2 IN s /\
         (?p. MEM p ns1 /\ MEM p ns2) ==>
         s2 = s1 /\ u2 = u1 /\ ns2 = ns1 /\ ts2 = ts1`,
  REWRITE_TAC[HEAP_FROM_STATE_def; LEFT_IMP_EXISTS_THM] THEN
  REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[st2heap_def; IN_UNION; cf_FFI_part_NOT_IN_store2heap] THEN
  PAIR_CASES_ON `f:(ffi->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)` THEN
  REWRITE_TAC[ffi2heap_def] THEN COND_CASES_TAC THEN
  SIMP[IN_INSERT; IN_ELIM_THM; IN_SING] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[parts_ok_def]) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `ns2:mlstring list = ns1` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC CF1AUX_ALL_DISTINCT_FLAT_MEM_IMP THEN
    MAP_EVERY EXISTS_TAC [`MAP FST (f1:((mlstring)list#ffi_next)list)`; `p:mlstring`] THEN
    ASM_REWRITE_TAC[MEM_MAP] THEN CONJ_TAC THEN ASM_MESON_TAC[FST];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[option_INJ]; ASM_MESON_TAC[CF1AUX_ALL_DISTINCT_FLAT_FST_IMP]]);;

let NON_OVERLAP_FFI_PART = prove
 (`!s. VALID_HEAP s ==>
       !s1 u1 ns1 ts1 s2 u2 ns2 ts2.
         cf_FFI_part s1 u1 ns1 ts1 IN s /\ cf_FFI_part s2 u2 ns2 ts2 IN s /\
         (?p. MEM p ns1 /\ MEM p ns2) ==>
         s2 = s1 /\ u2 = u1 /\ ns2 = ns1 /\ ts2 = ts1`,
  REWRITE_TAC[VALID_HEAP_def] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  QSPEC_THEN "st2heap f st" MP_TAC NON_OVERLAP_FFI_PART_HFS THEN
  REWRITE_TAC[HEAP_FROM_STATE_def] THEN
  ANTS_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM SET_TAC[]);;

(* A minor lemma *)
let FFI_PORT_IN_HEAP_LEM = prove
 (`!s u ns events (H:hprop) h.
     (set_sep_one (cf_FFI_part s u ns events) STAR H) h ==>
     cf_FFI_part s u ns events IN h`,
  REWRITE_TAC[set_sep_one_def; STAR_def; SPLIT_def] THEN SET_TAC[]);;

(* Another important theorem *)
let FRAME_UNIQUE_IO = prove
 (`!s. VALID_HEAP s ==>
       !s1 u1 ns1 s2 u2 ns2 H1 H2.
         (cf_IO s1 u1 ns1 STAR H1) s /\ (cf_IO s2 u2 ns2 STAR H2) s ==>
         (?pn. MEM pn ns1 /\ MEM pn ns2) ==>
         s2 = s1 /\ u2 = u1 /\ ns2 = ns1`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[cf_IO_def; SEP_CLAUSES; SEP_EXISTS_THM] THEN
  REWRITE_TAC[cond_MOVE; cond_STAR] THEN REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP FFI_PORT_IN_HEAP_LEM)) THEN
  MP_TAC(SPEC `s:heap` NON_OVERLAP_FFI_PART) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`s1:ffi`; `u1:ffi_next`; `ns1:(mlstring)list`;
    `events:(io_event)list`; `s2:ffi`; `u2:ffi_next`; `ns2:(mlstring)list`;
    `events':(io_event)list`]) THEN
  ASM_MESON_TAC[]);;

let IO_HPROP_INJ = prove
 (`!s1 u1 ns1 s2 u2 ns2 (H1:A) (H2:B).
     (?pn. MEM pn ns1 /\ MEM pn ns2) ==>
     HPROP_INJ (cf_IO s1 u1 ns1) (cf_IO s2 u2 ns2) (s2 = s1 /\ u2 = u1 /\ ns2 = ns1)`,
  REWRITE_TAC[HPROP_INJ_def; GSYM STAR_ASSOC; cf_HCOND_EXTRACT] THEN
  MESON_TAC[FRAME_UNIQUE_IO]);;

(* Theorems and rewrites for REPLICATE and LIST_REL *)

let APPEND_LENGTH_INEQ = prove
 (`!(l1:A list) l2.
     LENGTH l1 <= LENGTH (APPEND l1 l2) /\ LENGTH l2 <= LENGTH (APPEND l1 l2)`,
  REWRITE_TAC[LENGTH_APPEND] THEN ARITH_TAC);;

(* helper: the lists of copies of one value *)
let CF1AUX_REPLICATE_ALL = prove
 (`!(l:A list) x. l = REPLICATE (LENGTH l) x <=> ALL (\y. y = x) l`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[LENGTH; REPLICATE; ALL; CONS_11]);;

let REPLICATE_APPEND_RIGHT = prove
 (`APPEND a b = REPLICATE n (x:A) ==> b = REPLICATE (LENGTH b) x`,
  DISCH_THEN(MP_TAC o AP_TERM `ALL (\y:A. y = x)`) THEN
  REWRITE_TAC[CF1AUX_REPLICATE_ALL; ALL_APPEND; EVERY_REPLICATE] THEN
  SIMP_TAC[]);;

let REPLICATE_APPEND_LEFT = prove
 (`APPEND a b = REPLICATE n (x:A) ==> a = REPLICATE (LENGTH a) x`,
  DISCH_THEN(MP_TAC o AP_TERM `ALL (\y:A. y = x)`) THEN
  REWRITE_TAC[CF1AUX_REPLICATE_ALL; ALL_APPEND; EVERY_REPLICATE] THEN
  SIMP_TAC[]);;

let REPLICATE_APPEND_DECOMPOSE = prove
 (`APPEND a b = REPLICATE n (x:A) <=>
   a = REPLICATE (LENGTH a) x /\ b = REPLICATE (LENGTH b) x /\
   LENGTH a + LENGTH b = n`,
  EQ_TAC THENL
   [MESON_TAC[REPLICATE_APPEND_LEFT; REPLICATE_APPEND_RIGHT; LENGTH_APPEND;
              LENGTH_REPLICATE];
    STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[GSYM REPLICATE_APPEND] THEN BINOP_TAC THEN
    FIRST_ASSUM ACCEPT_TAC]);;

let REPLICATE_APPEND_DECOMPOSE_SYM =
  CONV_RULE (LAND_CONV SYM_CONV) REPLICATE_APPEND_DECOMPOSE;;

let REPLICATE_PLUS_ONE = prove
 (`REPLICATE (n + 1) (x:A) = CONS x (REPLICATE n x)`,
  REWRITE_TAC[GSYM ADD1; REPLICATE]);;

(* helpers: ALL2 on an APPEND, split at the length of the first part *)

let CF1AUX_ALL2_APPEND_TAKE_DROP = prove
 (`!(R:A->B->bool) a b x.
     ALL2 R (APPEND a b) x <=>
     ALL2 R a (TAKE (LENGTH a) x) /\ ALL2 R b (DROP (LENGTH a) x)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[APPEND; LENGTH; TAKE_0; DROP_0; ALL2] THEN
  REPEAT GEN_TAC THEN QSPEC_THEN "x" STRUCT_CASES_TAC list_CASES THEN
  ASM_REWRITE_TAC[ALL2; TAKE_DEF; DROP_DEF; NOT_SUC; SUC_SUB1; CONJ_ASSOC]);;

let CF1AUX_ALL2_TAKE_DROP_APPEND = prove
 (`!(R:A->B->bool) a b x.
     ALL2 R x (APPEND a b) <=>
     ALL2 R (TAKE (LENGTH a) x) a /\ ALL2 R (DROP (LENGTH a) x) b`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[APPEND; LENGTH; TAKE_0; DROP_0; ALL2] THEN
  REPEAT GEN_TAC THEN QSPEC_THEN "x" STRUCT_CASES_TAC list_CASES THEN
  ASM_REWRITE_TAC[ALL2; TAKE_DEF; DROP_DEF; NOT_SUC; SUC_SUB1; CONJ_ASSOC]);;

let LIST_REL_DECOMPOSE_RIGHT_recip = prove
 (`!R:A->B->bool.
     ALL2 R (APPEND a b) x ==>
     ALL2 R a (TAKE (LENGTH a) x) /\ ALL2 R b (DROP (LENGTH a) x)`,
  SIMP_TAC[CF1AUX_ALL2_APPEND_TAKE_DROP]);;

let LIST_REL_DECOMPOSE_RIGHT_imp = prove
 (`!R:A->B->bool.
     ALL2 R a (TAKE (LENGTH a) x) /\ ALL2 R b (DROP (LENGTH a) x) ==>
     ALL2 R (APPEND a b) x`,
  SIMP_TAC[CF1AUX_ALL2_APPEND_TAKE_DROP]);;

let LIST_REL_DECOMPOSE_RIGHT = prove
 (`!R:A->B->bool.
     ALL2 R (APPEND a b) x <=>
     ALL2 R a (TAKE (LENGTH a) x) /\ ALL2 R b (DROP (LENGTH a) x)`,
  MESON_TAC[LIST_REL_DECOMPOSE_RIGHT_recip; LIST_REL_DECOMPOSE_RIGHT_imp]);;

let LIST_REL_DECOMPOSE_LEFT_recip = prove
 (`!R:A->B->bool.
     ALL2 R x (APPEND a b) ==>
     ALL2 R (TAKE (LENGTH a) x) a /\ ALL2 R (DROP (LENGTH a) x) b`,
  SIMP_TAC[CF1AUX_ALL2_TAKE_DROP_APPEND]);;

let LIST_REL_DECOMPOSE_LEFT_imp = prove
 (`!R:A->B->bool.
     ALL2 R (TAKE (LENGTH a) x) a /\ ALL2 R (DROP (LENGTH a) x) b ==>
     ALL2 R x (APPEND a b)`,
  SIMP_TAC[CF1AUX_ALL2_TAKE_DROP_APPEND]);;

let LIST_REL_DECOMPOSE_LEFT = prove
 (`!R:A->B->bool.
     ALL2 R x (APPEND a b) <=>
     ALL2 R (TAKE (LENGTH a) x) a /\ ALL2 R (DROP (LENGTH a) x) b`,
  MESON_TAC[LIST_REL_DECOMPOSE_LEFT_recip; LIST_REL_DECOMPOSE_LEFT_imp]);;

let HEAD_TAIL = prove
 (`~(l = []) ==> CONS (HD l) (TL l) = (l:A list)`,
  QSPEC_THEN "l" STRUCT_CASES_TAC list_CASES THEN REWRITE_TAC[HD; TL; NOT_CONS_NIL]);;

let HEAD_TAIL_DECOMPOSE_RIGHT = prove
 (`CONS x a = b <=> ~(b = []) /\ x = HD b /\ (a:A list) = TL b`,
  QSPEC_THEN "b" STRUCT_CASES_TAC list_CASES THEN
  REWRITE_TAC[HD; TL; NOT_CONS_NIL; CONS_11]);;

let HEAD_TAIL_DECOMPOSE_LEFT = prove
 (`b = CONS x a <=> ~(b = []) /\ x = HD b /\ (a:A list) = TL b`,
  QSPEC_THEN "b" STRUCT_CASES_TAC list_CASES THEN
  REWRITE_TAC[HD; TL; NOT_CONS_NIL; GSYM NOT_CONS_NIL; CONS_11] THEN MESON_TAC[]);;

(* HOL4: val _ = hide "abs" (the variable abs is a here) *)

(* Theorems used as rewrites for the refinement invariants *)
(* HOL4: eqtype_unicity_thm_tac (an SML tactic) *)

let EQTYPE_UNICITY_R = prove
 (`!a x (y1:v) y2. EqualityType (a:A->v->bool) ==> a x y1 ==> (a x y2 <=> y2 = y1)`,
  REWRITE_TAC[EqualityType_def] THEN MESON_TAC[]);;

let EQTYPE_UNICITY_L = prove
 (`!a x1 x2 (y:v). EqualityType (a:A->v->bool) ==> a x1 y ==> (a x2 y <=> x2 = x1)`,
  REWRITE_TAC[EqualityType_def] THEN MESON_TAC[]);;

(* Theorems to use LIST_REL A "as a" refinement invariant *)
let InjectiveRel_def = cake_def
  `InjectiveRel (A:B->C->bool) <=>
     !x1 y1 x2 y2. A x1 y1 /\ A x2 y2 ==> (x1 = x2 <=> y1 = y2)`;;

let EQTYPE_INJECTIVEREL = prove
 (`EqualityType (A:B->v->bool) ==> InjectiveRel A`,
  REWRITE_TAC[InjectiveRel_def; EqualityType_def] THEN MESON_TAC[]);;

let LIST_REL_INJECTIVE_REL = prove
 (`!A:B->C->bool. InjectiveRel A ==> InjectiveRel (ALL2 A)`,
  GEN_TAC THEN REWRITE_TAC[InjectiveRel_def] THEN DISCH_TAC THEN
  LIST_INDUCT_TAC THEN X_GEN_TAC `y1:C list` THEN
  QSPEC_THEN "y1" STRUCT_CASES_TAC list_CASES THEN REWRITE_TAC[ALL2] THEN
  X_GEN_TAC `x2:B list` THEN X_GEN_TAC `y2:C list` THEN
  QSPEC_THEN "x2" STRUCT_CASES_TAC list_CASES THEN
  QSPEC_THEN "y2" STRUCT_CASES_TAC list_CASES THEN
  REWRITE_TAC[ALL2; CONS_11; NOT_CONS_NIL; GSYM NOT_CONS_NIL] THEN
  ASM_MESON_TAC[]);;

let LIST_REL_INJECTIVE_EQTYPE = prove
 (`!A:B->v->bool. EqualityType A ==> InjectiveRel (ALL2 A)`,
  MESON_TAC[EQTYPE_INJECTIVEREL; LIST_REL_INJECTIVE_REL]);;

let LIST_REL_UNICITY_RIGHT = prove
 (`EqualityType (A:B->v->bool) ==> ALL2 A a b ==> (ALL2 A a b' <=> b' = b)`,
  MESON_TAC[EQTYPE_INJECTIVEREL; LIST_REL_INJECTIVE_EQTYPE; InjectiveRel_def]);;

let LIST_REL_UNICITY_LEFT = prove
 (`EqualityType (A:B->v->bool) ==> ALL2 A a b ==> (ALL2 A a' b <=> a' = a)`,
  MESON_TAC[EQTYPE_INJECTIVEREL; LIST_REL_INJECTIVE_EQTYPE; InjectiveRel_def]);;

(* EqualityType proofs *)
let EqualityType_PAIR_TYPE = prove
 (`EqualityType (A:C->v->bool) ==> EqualityType (B:D->v->bool) ==>
   EqualityType (PAIR_TYPE A B)`,
  REWRITE_TAC[EqualityType_def; FORALL_PAIR_THM; PAIR_TYPE_def] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SIMP[no_closures_def; ALL; types_match_def; ctor_same_type_def; CONS_11; PAIR_EQ] THEN
  TRY(MATCH_MP_TAC(TAUT `(a <=> b) /\ (c <=> d) ==> (a /\ c <=> b /\ d)`)) THEN
  ASM_MESON_TAC[]);;

let LIST_TYPE_no_closure = prove
 (`!A x xv. EqualityType (A:B->v->bool) ==> LIST_TYPE A x xv ==> no_closures xv`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  SIMP[LIST_TYPE_def; no_closures_def; ALL] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[no_closures_def; ALL] THEN CONJ_TAC THENL
   [UNDISCH_TAC `EqualityType (A:B->v->bool)` THEN REWRITE_TAC[EqualityType_def] THEN
    ASM_MESON_TAC[];
    ASM_MESON_TAC[]]);;

let LIST_TYPE_inj = prove
 (`!A x1 x2 v1 v2.
     EqualityType (A:B->v->bool) ==> LIST_TYPE A x1 v1 ==> LIST_TYPE A x2 v2 ==>
     (v1 = v2 <=> x1 = x2)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN GEN_TAC THEN
  QSPEC_THEN "x2" STRUCT_CASES_TAC list_CASES THEN
  SIMP[LIST_TYPE_def] THEN REPEAT STRIP_TAC THEN GVS[injectivity "char"] THEN
  MATCH_MP_TAC(TAUT `(a <=> b) /\ (c <=> d) ==> (a /\ c <=> b /\ d)`) THEN
  CONJ_TAC THENL [ASM_MESON_TAC[EqualityType_def]; ASM_MESON_TAC[]]);;

(* HOL4: types_match_tac (an SML tactic) *)
let LIST_TYPE_types_match = prove
 (`!A x1 x2 v1 v2.
     EqualityType (A:B->v->bool) ==> LIST_TYPE A x1 v1 ==> LIST_TYPE A x2 v2 ==>
     types_match v1 v2`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN GEN_TAC THEN
  QSPEC_THEN "x2" STRUCT_CASES_TAC list_CASES THEN
  SIMP[LIST_TYPE_def] THEN REPEAT STRIP_TAC THEN
  GVS[types_match_def; ctor_same_type_def; same_type_def; injectivity "char"] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[EqualityType_def]; ASM_MESON_TAC[]]);;

let EqualityType_LIST_TYPE = prove
 (`EqualityType (A:B->v->bool) ==> EqualityType (LIST_TYPE A)`,
  DISCH_TAC THEN GEN_REWRITE_TAC I [EqualityType_def] THEN
  ASM_MESON_TAC[LIST_TYPE_no_closure; LIST_TYPE_inj; LIST_TYPE_types_match]);;

(* Some theorems for rewrite rules with the refinement invariants *)

(* Need to write the expand and retract theorems for UNIT_TYPE by hand -     *)
(* otherwise the retract theorem might introduce a variable, for example    *)
let UNIT_TYPE_RETRACT = prove
 (`!v. v = Conv NONE [] <=> UNIT_TYPE one v`,
  REWRITE_TAC[UNIT_TYPE_def]);;

let UNIT_TYPE_EXPAND = prove
 (`!u v. UNIT_TYPE u v <=> u = one /\ v = Conv NONE []`,
  REWRITE_TAC[UNIT_TYPE_def] THEN MESON_TAC[one]);;

let NUM_INT_EQ = prove
 (`(!x y v. ml_INT x v ==> (ml_NUM y v <=> x = &y)) /\
   (!x y v. ml_NUM y v ==> (ml_INT x v <=> x = &y)) /\
   (!x v w. ml_INT (&x) v ==> (ml_NUM x w <=> w = v)) /\
   (!x v w. ml_NUM x v ==> (ml_INT (&x) w <=> w = v))`,
  REWRITE_TAC[ml_NUM_def; ml_INT_def] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[injectivity "v"; injectivity "lit"] THEN MESON_TAC[]);;

(* Some rules used to simplify arithmetic equations (not happy with that:   *)
(* write a conversion instead?                                               *)

let NUM_EQ_lem = prove
 (`!(a1:num) (a2:num) (b:num). b <= a1 ==> b <= a2 ==> (a1 = a2 <=> a1 - b = a2 - b)`,
  ARITH_TAC);;

(* the NUM_EQ_SIMP theorems: the variables NUMERAL n1 and NUMERAL n2 are    *)
(* generalised, MIN is split, and the products with b are atoms for ARITH  *)
let CF1AUX_NUM_EQ_TAC =
  SPEC_TAC(`NUMERAL n1`,`m1:num`) THEN SPEC_TAC(`NUMERAL n2`,`m2:num`) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[MIN] THEN COND_CASES_TAC THENL
   [FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP LE_MULT2 (CONJ th (SPEC `b:num` LE_REFL))));
    FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP LE_MULT2
      (CONJ (MATCH_MP LT_IMP_LE (REWRITE_RULE[NOT_LE] th)) (SPEC `b:num` LE_REFL))))] THEN
  REWRITE_TAC[RIGHT_SUB_DISTRIB; MULT_CLAUSES] THEN ARITH_TAC;;

let NUM_EQ_SIMP1 = prove
 (`a1 + (NUMERAL n1) * b = a2 + (NUMERAL n2) * b <=>
   a1 + (NUMERAL n1 - (MIN (NUMERAL n1) (NUMERAL n2))) * b =
   a2 + (NUMERAL n2 - (MIN (NUMERAL n1) (NUMERAL n2))) * b`,
  CF1AUX_NUM_EQ_TAC);;

let NUM_EQ_SIMP2 = prove
 (`(NUMERAL n1) * b + a1 = (NUMERAL n2) * b + a2 <=>
   (NUMERAL n1 - (MIN (NUMERAL n1) (NUMERAL n2))) * b + a1 =
   (NUMERAL n2 - (MIN (NUMERAL n1) (NUMERAL n2))) * b + a2`,
  CF1AUX_NUM_EQ_TAC);;

let NUM_EQ_SIMP3 = prove
 (`a1 + (NUMERAL n1) * b = (NUMERAL n2) * b + a2 <=>
   a1 + (NUMERAL n1 - (MIN (NUMERAL n1) (NUMERAL n2))) * b =
   (NUMERAL n2 - (MIN (NUMERAL n1) (NUMERAL n2))) * b + a2`,
  CF1AUX_NUM_EQ_TAC);;

let NUM_EQ_SIMP4 = prove
 (`(NUMERAL n1) * b + a1 = a2 + (NUMERAL n2) * b <=>
   (NUMERAL n1 - (MIN (NUMERAL n1) (NUMERAL n2))) * b + a1 =
   (NUMERAL n2 - (MIN (NUMERAL n1) (NUMERAL n2))) * b + a2`,
  CF1AUX_NUM_EQ_TAC);;

let NUM_EQ_SIMP5 = prove
 (`a1 + b = a2 + (NUMERAL n2) * b <=>
   a1 + (1 - (MIN 1 (NUMERAL n2))) * b = a2 + (NUMERAL n2 - (MIN 1 (NUMERAL n2))) * b`,
  CF1AUX_NUM_EQ_TAC);;

let NUM_EQ_SIMP6 = prove
 (`a1 + (NUMERAL n1) * b = a2 + b <=>
   a1 + (NUMERAL n1 - (MIN 1 (NUMERAL n1))) * b = a2 + (1 - (MIN 1 (NUMERAL n1))) * b`,
  CF1AUX_NUM_EQ_TAC);;

let NUM_EQ_SIMP7 = prove
 (`b + a1 = (NUMERAL n2) * b + a2 <=>
   (1 - (MIN 1 (NUMERAL n2))) * b + a1 = (NUMERAL n2 - (MIN 1 (NUMERAL n2))) * b + a2`,
  CF1AUX_NUM_EQ_TAC);;

let NUM_EQ_SIMP8 = prove
 (`(NUMERAL n1) * b + a1 = b + a2 <=>
   (NUMERAL n1 - (MIN 1 (NUMERAL n1))) * b + a1 = (1 - (MIN 1 (NUMERAL n1))) * b + a2`,
  CF1AUX_NUM_EQ_TAC);;

let NUM_EQ_SIMP9 = prove
 (`a1 + b = (NUMERAL n2) * b + a2 <=>
   a1 + (1 - (MIN 1 (NUMERAL n2))) * b = (NUMERAL n2 - (MIN 1 (NUMERAL n2))) * b + a2`,
  CF1AUX_NUM_EQ_TAC);;

let NUM_EQ_SIMP10 = prove
 (`b + a1 = a2 + (NUMERAL n2) * b <=>
   (1 - (MIN 1 (NUMERAL n2))) * b + a1 = a2 + (NUMERAL n2 - (MIN 1 (NUMERAL n2))) * b`,
  CF1AUX_NUM_EQ_TAC);;

let NUM_EQ_SIMP11 = prove
 (`a1 + (NUMERAL n1) * b = b + a2 <=>
   a1 + (NUMERAL n1 - (MIN 1 (NUMERAL n1))) * b = (1 - (MIN 1 (NUMERAL n1))) * b + a2`,
  CF1AUX_NUM_EQ_TAC);;

let NUM_EQ_SIMP12 = prove
 (`(NUMERAL n1) * b + a1 = a2 + b <=>
   (NUMERAL n1 - (MIN 1 (NUMERAL n1))) * b + a1 = a2 + (1 - (MIN 1 (NUMERAL n1))) * b`,
  CF1AUX_NUM_EQ_TAC);;
