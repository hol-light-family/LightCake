(* ========================================================================= *)
(* ml_monad_translatorBase: port of HOL4                                     *)
(* translator/monadic/ml_monad_translatorBaseScript.sml (CakeML v3479).      *)
(* Assertions about references and arrays are defined.  Lemmas for these    *)
(* are proved, including reasoning in separation logic.                     *)
(* ========================================================================= *)

needs "hol4/set_sep.ml";;
needs "translator/ml_prog.ml";;
needs "translator/ml_translator.ml";;
needs "translator/monadic/monad_base/ml_monadBase.ml";;
needs "characteristic/cfHeapsBase.ml";;
needs "characteristic/cfStore.ml";;
needs "characteristic/cfLetAuto.ml";;

type_invention_error := true;;

(* HOL4: Type state = ``:'ffi semanticPrimitives$state`` (names.tsv         *)
(* ml_monad_translatorBase_state), written (FFI)state.                       *)

(* a few basics *)

let with_same_refs = prove
 (`state_refs_fupd (K (state_refs s)) (s:(FFI)state) = s`,
  REWRITE_TAC[state_component_equality] THEN SIMP[]);;

let with_same_ffi = prove
 (`state_ffi_fupd (K (state_ffi s)) (s:(FFI)state) = s`,
  REWRITE_TAC[state_component_equality] THEN SIMP[]);;

let ml_monad_translatorBase_with_same_clock = prove
 (`state_clock_fupd (K (state_clock s)) (s:(FFI)state) = s`,
  REWRITE_TAC[state_component_equality] THEN SIMP[]);;

(* REF_REL *)

let REF_REL_def = cake_def
  `REF_REL (TYPE:A->v->bool) r x =
     SEP_EXISTS v. cf_REF r v STAR set_sep_cond (TYPE x v)`;;

(* REFS_PRED *)

let REFS_PRED_def = cake_def
  `REFS_PRED (h:A->hprop,p) (refs:A) (s:(FFI)state) <=>
     (h refs STAR cf_GC) (st2heap p s)`;;

let VALID_REFS_PRED_def = cake_def
  `VALID_REFS_PRED H <=> ?(s:(FFI)state) (refs:A). REFS_PRED H refs s`;;

(* Frame rule for EvalM *)

let REFS_PRED_FRAME_def = cake_def
  `REFS_PRED_FRAME ro (h:A->hprop,p) (refs1,(s1:(FFI)state)) (refs2,s2) <=>
     (ro ==> ?refs. s2 = state_refs_fupd (K refs) s1) /\
     state_next_type_stamp s2 = state_next_type_stamp s1 /\
     state_next_exn_stamp s2 = state_next_exn_stamp s1 /\
     !F'. (h refs1 STAR F') (st2heap p s1) ==>
          (h refs2 STAR F' STAR cf_GC) (st2heap p s2)`;;

let EMP_STAR_GC = prove
 (`!H:(A->bool)->bool. set_sep_emp STAR H = H`,
  REWRITE_TAC[SEP_CLAUSES]);;

let SAT_GC = prove
 (`!h. cf_GC h`,
  REWRITE_TAC[cf_GC_def; SEP_EXISTS_THM] THEN GEN_TAC THEN
  EXISTS_TAC `\s:heap. T` THEN REWRITE_TAC[]);;

let REFS_PRED_FRAME_imp = prove
 (`!(refs1:A) (s1:(FFI)state) H refs2 s2.
     REFS_PRED H refs1 s1 ==>
     REFS_PRED_FRAME ro H (refs1,s1) (refs2,s2) ==> REFS_PRED H refs2 s2`,
  REWRITE_TAC[FORALL_PAIR_THM; REFS_PRED_def; REFS_PRED_FRAME_def] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `cf_GC`) THEN
  REWRITE_TAC[GSYM STAR_ASSOC; GC_STAR_GC] THEN ASM_MESON_TAC[]);;

let REFS_PRED_FRAME_trans = prove
 (`REFS_PRED_FRAME ro H ((refs1:A),(s1:(FFI)state)) (refs2,s2) ==>
   REFS_PRED_FRAME ro H (refs2,s2) (refs3,s3) ==>
   REFS_PRED_FRAME ro H (refs1,s1) (refs3,s3)`,
  QCASES_ON "H" THEN REWRITE_TAC[REFS_PRED_FRAME_def] THEN
  REPEAT STRIP_TAC THENL
   [RES_TAC THEN ASM_REWRITE_TAC[] THEN SIMP[] THEN MESON_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPEC `F' STAR cf_GC`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `F':hprop`) THEN
    ASM_REWRITE_TAC[STAR_ASSOC] THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[GSYM STAR_ASSOC; GC_STAR_GC]]);;

let ml_monad_translatorBase_H_STAR_GC_SAT_IMP = prove
 (`H s ==> (H STAR cf_GC) s`,
  REWRITE_TAC[STAR_def] THEN DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC [`s:heap`; `{}:heap`] THEN
  ASM_REWRITE_TAC[SPLIT_emp2; SAT_GC]);;

let REFS_PRED_FRAME_same = prove
 (`!H (st:A) (s:(FFI)state). REFS_PRED_FRAME ro H (st,s) (st,s)`,
  REWRITE_TAC[FORALL_PAIR_THM; REFS_PRED_FRAME_def] THEN REPEAT STRIP_TAC THENL
   [EXISTS_TAC `state_refs (s:(FFI)state)` THEN REWRITE_TAC[with_same_refs];
    MATCH_MP_TAC ml_monad_translatorBase_H_STAR_GC_SAT_IMP THEN
    ASM_REWRITE_TAC[]]);;

(* Proof of REFS_PRED_APPEND:                                                *)
(* REFS_PRED H refs s ==> REFS_PRED H refs (s with refs := s.refs ++ junk)   *)

let store2heap_aux_Mem = prove
 (`!s n x. x IN (store2heap_aux n s) ==> ?n' v. x = cf_Mem n' v`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[store2heap_aux_def; NOT_IN_EMPTY; IN_INSERT] THEN
  ASM_MESON_TAC[]);;

let store2heap_aux_IN_LENGTH = prove
 (`!s r x n. cf_Mem r x IN (store2heap_aux n s) ==> r < n + LENGTH s`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[store2heap_aux_def; NOT_IN_EMPTY; IN_INSERT; injectivity "heap_part";
    LENGTH] THEN
  REPEAT STRIP_TAC THENL [ASM_ARITH_TAC; RES_TAC THEN ASM_ARITH_TAC]);;

let NEG_DISJ_TO_IMP = prove
 (`!A B. ~A \/ ~B <=> A /\ B ==> F`,
  CONV_TAC TAUT);;

let store2heap_aux_DISJOINT = prove
 (`!n s1 s2. DISJOINT (store2heap_aux n s1) (store2heap_aux (n + LENGTH s1) s2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_DISJOINT] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:heap_part` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP store2heap_aux_Mem) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `w:v store_v` SUBST_ALL_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP store2heap_aux_IN_bound) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP store2heap_aux_IN_LENGTH) THEN
  ARITH_TAC);;

(* HOL4 cfApp's store2heap_aux_append_many and store2heap_append_many (cfApp *)
(* is in M10)                                                                *)

let MON1AUX_store2heap_aux_append_many = prove
 (`!s n x. store2heap_aux n (APPEND s x) =
           store2heap_aux (n + LENGTH s) x UNION store2heap_aux n s`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND; store2heap_aux_def; LENGTH; ADD_0; UNION_EMPTY] THEN
  REWRITE_TAC[ARITH_RULE `n + SUC m = (n + 1) + m`] THEN SET_TAC[]);;

let MON1AUX_store2heap_append_many = prove
 (`!s x. store2heap (APPEND s x) = store2heap s UNION store2heap_aux (LENGTH s) x`,
  REWRITE_TAC[store2heap_def; MON1AUX_store2heap_aux_append_many; ADD_CLAUSES] THEN
  SET_TAC[]);;

let store2heap_aux_SPLIT = prove
 (`!s1 s2 n. SPLIT (store2heap_aux n (APPEND s1 s2))
                   (store2heap_aux n s1, store2heap_aux (n + LENGTH s1) s2)`,
  REWRITE_TAC[SPLIT_def; MON1AUX_store2heap_aux_append_many;
    store2heap_aux_DISJOINT] THEN
  SET_TAC[]);;

let store2heap_DISJOINT = prove
 (`DISJOINT (store2heap s1) (store2heap_aux (LENGTH s1) s2)`,
  REWRITE_TAC[store2heap_def] THEN
  MESON_TAC[store2heap_aux_DISJOINT; ADD_CLAUSES]);;

let store2heap_SPLIT = prove
 (`!s1 s2. SPLIT (store2heap (APPEND s1 s2))
                 (store2heap s1, store2heap_aux (LENGTH s1) s2)`,
  REWRITE_TAC[store2heap_def] THEN
  MESON_TAC[store2heap_aux_SPLIT; ADD_CLAUSES]);;

let SPLIT_DECOMPOSWAP = prove
 (`SPLIT (s1:A->bool) (s2,s3) ==> SPLIT s2 (u,v) ==> SPLIT s1 (u,v UNION s3)`,
  REWRITE_TAC[SPLIT_def] THEN SET_TAC[]);;

let STORE_APPEND_JUNK = prove
 (`!H s junk. H (store2heap s) ==> (H STAR cf_GC) (store2heap (APPEND s junk))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[STAR_def] THEN
  MAP_EVERY EXISTS_TAC [`store2heap s`;
    `store2heap_aux (LENGTH (s:(v store_v)list)) junk`] THEN
  ASM_REWRITE_TAC[store2heap_SPLIT; SAT_GC]);;

let st2heap_SPLIT_FFI = prove
 (`!f (st:(FFI)state).
     SPLIT (store2heap (state_refs st) UNION ffi2heap f (state_ffi st))
           (store2heap (state_refs st), ffi2heap f (state_ffi st))`,
  REWRITE_TAC[SPLIT_def; IN_DISJOINT; store2heap_def] THEN
  MESON_TAC[store2heap_aux_Mem; Mem_NOT_IN_ffi2heap]);;

let SPLIT3_swap12 = prove
 (`!h h1 h2 h3:A->bool. SPLIT3 h (h1,h2,h3) <=> SPLIT3 h (h2,h1,h3)`,
  REWRITE_TAC[SPLIT3_def] THEN SET_TAC[]);;

let SPLIT_of_SPLIT3_1u3 = prove
 (`!h h1 h2 h3:A->bool. SPLIT3 h (h1,h2,h3) ==> SPLIT h (h2,h1 UNION h3)`,
  MESON_TAC[SPLIT3_swap12; SPLIT_of_SPLIT3_2u3]);;

let SPLIT2_SPLIT3 = prove
 (`SPLIT (s1:A->bool) (s2,t3) /\ SPLIT s2 (t1,t2) ==> SPLIT3 s1 (t1,t2,t3)`,
  REWRITE_TAC[SPLIT_def; SPLIT3_def] THEN SET_TAC[]);;

let SPLIT_SYM = prove
 (`SPLIT (s:A->bool) (s1,s2) <=> SPLIT s (s2,s1)`,
  REWRITE_TAC[SPLIT_def] THEN SET_TAC[]);;

let MON1AUX_ffi2heap_DISJOINT = prove
 (`!p (s:(FFI)ffi_state) n l. DISJOINT (ffi2heap p s) (store2heap_aux n l)`,
  REWRITE_TAC[IN_DISJOINT] THEN MESON_TAC[store2heap_aux_Mem; Mem_NOT_IN_ffi2heap]);;

let STATE_APPEND_JUNK = prove
 (`!H p (s:(FFI)state) refs junk.
     H (st2heap p (state_refs_fupd (K refs) s)) ==>
     (H STAR cf_GC) (st2heap p (state_refs_fupd (K (APPEND refs junk)) s))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[STAR_def] THEN
  MAP_EVERY EXISTS_TAC [`st2heap p (state_refs_fupd (K refs) (s:(FFI)state))`;
    `store2heap_aux (LENGTH (refs:(v store_v)list)) junk`] THEN
  ASM_REWRITE_TAC[SAT_GC] THEN
  SIMP[st2heap_def; SPLIT_def; MON1AUX_store2heap_append_many; DISJOINT_UNION;
    store2heap_DISJOINT; MON1AUX_ffi2heap_DISJOINT] THEN
  SET_TAC[]);;

let STATE_SPLIT_REFS = prove
 (`!a b p (s:(FFI)state).
     SPLIT (st2heap p (state_refs_fupd (K (APPEND a b)) s))
           (st2heap p (state_refs_fupd (K a) s), store2heap_aux (LENGTH a) b)`,
  SIMP[st2heap_def; SPLIT_def; MON1AUX_store2heap_append_many; DISJOINT_UNION;
    store2heap_DISJOINT; MON1AUX_ffi2heap_DISJOINT] THEN
  SET_TAC[]);;

let REFS_PRED_append = prove
 (`!H (refs:A) (s:(FFI)state).
     REFS_PRED H refs s ==>
     REFS_PRED H refs (state_refs_fupd (K (APPEND (state_refs s) junk)) s)`,
  REWRITE_TAC[FORALL_PAIR_THM; REFS_PRED_def] THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM GC_STAR_GC] THEN REWRITE_TAC[STAR_ASSOC] THEN
  MATCH_MP_TAC STATE_APPEND_JUNK THEN ASM_REWRITE_TAC[with_same_refs]);;

let REFS_PRED_qappend = prove
 (`!H (refs:A) (s:(FFI)state).
     REFS_PRED H refs s ==>
     !junk. REFS_PRED H refs (state_refs_fupd (K (APPEND (state_refs s) junk)) s)`,
  MESON_TAC[REFS_PRED_append]);;

let REFS_PRED_FRAME_append = prove
 (`!H (refs:A) (s:(FFI)state).
     REFS_PRED_FRAME ro H (refs,s)
       (refs,state_refs_fupd (K (APPEND (state_refs s) junk)) s)`,
  REWRITE_TAC[FORALL_PAIR_THM; REFS_PRED_FRAME_def] THEN REPEAT STRIP_TAC THEN
  SIMP[] THENL
   [MESON_TAC[];
    MATCH_MP_TAC STATE_APPEND_JUNK THEN ASM_REWRITE_TAC[with_same_refs]]);;

(* Proof of STORE_EXTRACT_FROM_HPROP:                                        *)
(* !l xv H s. (REF (Loc T l) xv * H) (store2heap s) ==>                      *)
(*   ?ps. ((ps ++ [Refv xv]) <<= s) /\ LENGTH ps = l                         *)

let HEAP_LOC_MEM = prove
 (`(cf_cell l rv STAR H) h ==> cf_Mem l rv IN h`,
  REWRITE_TAC[STAR_def; cf_cell_def; set_sep_one_def; SPLIT_def] THEN
  SET_TAC[]);;

let st2heap_CELL_MEM = prove
 (`(cf_cell l rv STAR H) (st2heap p (s:(FFI)state)) ==>
   cf_Mem l rv IN store2heap (state_refs s)`,
  DISCH_THEN(MP_TAC o MATCH_MP HEAP_LOC_MEM) THEN
  REWRITE_TAC[st2heap_def; IN_UNION; Mem_NOT_IN_ffi2heap]);;

let st2heap_REF_MEM = prove
 (`(cf_REF (Loc T l) xv STAR H) (st2heap p (s:(FFI)state)) ==>
   cf_Mem l (Refv xv) IN store2heap (state_refs s)`,
  REWRITE_TAC[cf_REF_def; SEP_CLAUSES; SEP_EXISTS_THM] THEN
  REWRITE_TAC[GSYM STAR_ASSOC; cf_HCOND_EXTRACT] THEN
  SIMP[] THEN MESON_TAC[st2heap_CELL_MEM]);;

let st2heap_ARRAY_MEM = prove
 (`(cf_ARRAY (Loc T l) av STAR H) (st2heap p (s:(FFI)state)) ==>
   cf_Mem l (Varray av) IN store2heap (state_refs s)`,
  REWRITE_TAC[cf_ARRAY_def; SEP_CLAUSES; SEP_EXISTS_THM] THEN
  REWRITE_TAC[GSYM STAR_ASSOC; cf_HCOND_EXTRACT] THEN
  SIMP[] THEN MESON_TAC[st2heap_CELL_MEM]);;

let store2heap_aux_LOC_MEM = prove
 (`!l rv H n s. (cf_cell l rv STAR H) (store2heap_aux n s) ==>
                cf_Mem l rv IN store2heap_aux n s`,
  REWRITE_TAC[HEAP_LOC_MEM]);;

let store2heap_LOC_MEM = prove
 (`!l rv H s. (cf_cell l rv STAR H) (store2heap s) ==> cf_Mem l rv IN store2heap s`,
  REWRITE_TAC[HEAP_LOC_MEM]);;

let isPREFIX_TAKE = prove
 (`!l (s:A list). TAKE l s <<= s`,
  MESON_TAC[IS_PREFIX_APPEND; TAKE_DROP]);;

let isPREFIX_APPEND_EQ = prove
 (`!a1 a2 (b1:A list) b2.
     LENGTH a1 = LENGTH a2 ==>
     (APPEND a1 b1 <<= APPEND a2 b2 <=> a2 = a1 /\ b1 <<= b2)`,
  LIST_INDUCT_TAC THENL
   [MESON_TAC[LENGTH_NIL_SYM; APPEND];
    GEN_TAC THEN QCASES_ON "a2" THEN
    ASM_REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ; APPEND; isPREFIX_THM; CONS_11] THEN
    ASM_MESON_TAC[]]);;

let STATE_DECOMPOS_FROM_HPROP = prove
 (`!l rv H p (s:(FFI)state).
     (cf_cell l rv STAR H) (st2heap p s) ==>
     ?ps. APPEND ps [rv] <<= state_refs s /\ LENGTH ps = l`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP st2heap_CELL_MEM) THEN
  DISCH_THEN(fun th -> MP_TAC(MATCH_MP store2heap_IN_EL th) THEN
                       MP_TAC(MATCH_MP store2heap_IN_LENGTH th)) THEN
  DISCH_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  EXISTS_TAC `TAKE l (state_refs (s:(FFI)state))` THEN
  ASM_SIMP_TAC[LENGTH_TAKE; LT_IMP_LE] THEN
  REWRITE_TAC[IS_PREFIX_APPEND] THEN
  EXISTS_TAC `DROP (l + 1) (state_refs (s:(FFI)state))` THEN
  ASM_SIMP_TAC[GSYM APPEND_ASSOC; APPEND; GSYM DROP_EL_CONS; TAKE_DROP]);;

let STATE_DECOMPOS_FROM_HPROP_REF = prove
 (`!l xv H p (s:(FFI)state).
     (cf_REF (Loc T l) xv STAR H) (st2heap p s) ==>
     ?ps. APPEND ps [Refv xv] <<= state_refs s /\ LENGTH ps = l`,
  REWRITE_TAC[cf_REF_def; SEP_CLAUSES; SEP_EXISTS_THM] THEN
  REWRITE_TAC[GSYM STAR_ASSOC; cf_HCOND_EXTRACT] THEN SIMP[] THEN
  MESON_TAC[STATE_DECOMPOS_FROM_HPROP]);;

let STATE_DECOMPOS_FROM_HPROP_ARRAY = prove
 (`!l av H p (s:(FFI)state).
     (cf_ARRAY (Loc T l) av STAR H) (st2heap p s) ==>
     ?ps. APPEND ps [Varray av] <<= state_refs s /\ LENGTH ps = l`,
  REWRITE_TAC[cf_ARRAY_def; SEP_CLAUSES; SEP_EXISTS_THM] THEN
  REWRITE_TAC[GSYM STAR_ASSOC; cf_HCOND_EXTRACT] THEN SIMP[] THEN
  MESON_TAC[STATE_DECOMPOS_FROM_HPROP]);;

let STATE_EXTRACT_FROM_HPROP = prove
 (`!l rv H p (s:(FFI)state).
     (cf_cell l rv STAR H) (st2heap p s) ==>
     !junk. EL l (APPEND (state_refs s) junk) = rv`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP st2heap_CELL_MEM) THEN
  DISCH_THEN(fun th -> MP_TAC(MATCH_MP store2heap_IN_EL th) THEN
                       MP_TAC(MATCH_MP store2heap_IN_LENGTH th)) THEN
  SIMP[EL_APPEND1]);;

let STATE_EXTRACT_FROM_HPROP_REF = prove
 (`!l xv H p (s:(FFI)state).
     (cf_REF (Loc T l) xv STAR H) (st2heap p s) ==>
     !junk. EL l (APPEND (state_refs s) junk) = Refv xv`,
  REWRITE_TAC[cf_REF_def; SEP_CLAUSES; SEP_EXISTS_THM] THEN
  REWRITE_TAC[GSYM STAR_ASSOC; cf_HCOND_EXTRACT] THEN SIMP[] THEN
  MESON_TAC[STATE_EXTRACT_FROM_HPROP]);;

let STATE_EXTRACT_FROM_HPROP_ARRAY = prove
 (`!l av H p (s:(FFI)state).
     (cf_ARRAY (Loc T l) av STAR H) (st2heap p s) ==>
     !junk. EL l (APPEND (state_refs s) junk) = Varray av`,
  REWRITE_TAC[cf_ARRAY_def; SEP_CLAUSES; SEP_EXISTS_THM] THEN
  REWRITE_TAC[GSYM STAR_ASSOC; cf_HCOND_EXTRACT] THEN SIMP[] THEN
  MESON_TAC[STATE_EXTRACT_FROM_HPROP]);;

let MON1AUX_NOT_IN_store2heap = prove
 (`!s0 x. ~(cf_Mem (LENGTH s0) x IN store2heap s0)`,
  MESON_TAC[store2heap_IN_LENGTH; LT_REFL]);;

let MON1AUX_NOT_IN_store2heap_aux = prove
 (`!n s x. ~(cf_Mem n x IN store2heap_aux (n + 1) s)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP store2heap_aux_IN_bound) THEN
  ARITH_TAC);;

let SEPARATE_STORE_ELEM_IN_HEAP = prove
 (`!s0 x s1.
     SPLIT3 (store2heap (APPEND (APPEND s0 [x]) s1))
            (store2heap s0, {cf_Mem (LENGTH s0) x},
             store2heap_aux (LENGTH s0 + 1) s1)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM APPEND_ASSOC; APPEND; MON1AUX_store2heap_append_many;
    store2heap_aux_def; SPLIT3_def] THEN
  MP_TAC(SPECL [`LENGTH (s0:(v store_v)list)`; `s1:(v store_v)list`; `x:v store_v`]
    MON1AUX_NOT_IN_store2heap_aux) THEN
  MP_TAC(SPECL [`0`; `s0:(v store_v)list`; `CONS (x:v store_v) s1`]
    store2heap_aux_DISJOINT) THEN
  REWRITE_TAC[GSYM store2heap_def; store2heap_aux_def; ADD_CLAUSES; LENGTH_APPEND;
    LENGTH; GSYM ONE] THEN SET_TAC[]);;

let CELL_HPROP_SAT_EQ = prove
 (`!l xv s. cf_cell l xv s <=> s = {cf_Mem l xv}`,
  REWRITE_TAC[cf_cell_def; set_sep_one_def]);;

let REF_HPROP_SAT_EQ = prove
 (`!l xv s. cf_REF (Loc T l) xv s <=> s = {cf_Mem l (Refv xv)}`,
  REWRITE_TAC[cf_REF_def; SEP_EXISTS_THM; cf_HCOND_EXTRACT; cf_cell_def;
    set_sep_one_def] THEN
  SIMP[]);;

let ARRAY_HPROP_SAT_EQ = prove
 (`!l av s. cf_ARRAY (Loc T l) av s <=> s = {cf_Mem l (Varray av)}`,
  REWRITE_TAC[cf_ARRAY_def; SEP_EXISTS_THM; cf_HCOND_EXTRACT; cf_cell_def;
    set_sep_one_def] THEN
  SIMP[]);;

let SPLIT_UNICITY_R = prove
 (`SPLIT (s:A->bool) (u,v) ==> (SPLIT s (u,v') <=> v' = v)`,
  SIMP[SPLIT_EQ]);;

let DIFF_UNION_COMM = prove
 (`DISJOINT s2 (s3:A->bool) ==> (s1 UNION s2) DIFF s3 = (s1 DIFF s3) UNION s2`,
  SET_TAC[]);;

let MON1AUX_DELETE_UNION3 = prove
 (`!m (a:A->bool) b c.
     ~(m IN a) /\ ~(m IN b) /\ ~(m IN c) ==>
     (((a UNION {m}) UNION b) UNION c) DELETE m = (a UNION b) UNION c`,
  SET_TAC[]);;

let STATE_SAT_CELL_STAR_H_EQ = prove
 (`!p (s:(FFI)state) s0 rv s1 H.
     (cf_cell (LENGTH s0) rv STAR H)
       (st2heap p (state_refs_fupd (K (APPEND (APPEND s0 [rv]) s1)) s)) <=>
     H ((store2heap s0 UNION store2heap_aux (LENGTH s0 + 1) s1) UNION
        ffi2heap p (state_ffi s))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cf_cell_def; one_STAR; st2heap_def] THEN SIMP[] THEN
  REWRITE_TAC[GSYM APPEND_ASSOC; APPEND; MON1AUX_store2heap_append_many;
    store2heap_aux_def; LENGTH_APPEND; LENGTH; GSYM ONE] THEN
  SIMP[MON1AUX_DELETE_UNION3; Mem_NOT_IN_ffi2heap; MON1AUX_NOT_IN_store2heap;
    MON1AUX_NOT_IN_store2heap_aux; IN_UNION; IN_SING]);;

let STATE_SAT_REF_STAR_H_EQ = prove
 (`!p (s:(FFI)state) s0 xv s1 H.
     (cf_REF (Loc T (LENGTH s0)) xv STAR H)
       (st2heap p (state_refs_fupd (K (APPEND (APPEND s0 [Refv xv]) s1)) s)) <=>
     H ((store2heap s0 UNION store2heap_aux (LENGTH s0 + 1) s1) UNION
        ffi2heap p (state_ffi s))`,
  REWRITE_TAC[cf_REF_def; SEP_CLAUSES; SEP_EXISTS_THM] THEN
  REWRITE_TAC[GSYM STAR_ASSOC; cf_HCOND_EXTRACT] THEN SIMP[] THEN
  REWRITE_TAC[UNWIND_THM1; STATE_SAT_CELL_STAR_H_EQ]);;

let STATE_SAT_ARRAY_STAR_H_EQ = prove
 (`!p (s:(FFI)state) s0 av s1 H.
     (cf_ARRAY (Loc T (LENGTH s0)) av STAR H)
       (st2heap p (state_refs_fupd (K (APPEND (APPEND s0 [Varray av]) s1)) s)) <=>
     H ((store2heap s0 UNION store2heap_aux (LENGTH s0 + 1) s1) UNION
        ffi2heap p (state_ffi s))`,
  REWRITE_TAC[cf_ARRAY_def; SEP_CLAUSES; SEP_EXISTS_THM] THEN
  REWRITE_TAC[GSYM STAR_ASSOC; cf_HCOND_EXTRACT] THEN SIMP[] THEN
  REWRITE_TAC[UNWIND_THM1; STATE_SAT_CELL_STAR_H_EQ]);;

let STATE_UPDATE_HPROP_CELL = prove
 (`(cf_cell l rv STAR H) (st2heap p (s:(FFI)state)) ==>
   (cf_cell l rv' STAR H)
     (st2heap p (state_refs_fupd (K (LUPDATE rv' l (state_refs s))) s))`,
  DISCH_TAC THEN
  SUBGOAL_THEN `?s0 s1. state_refs (s:(FFI)state) = APPEND (APPEND s0 [rv]) s1 /\
                        LENGTH s0 = l` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP STATE_DECOMPOS_FROM_HPROP) THEN
    REWRITE_TAC[IS_PREFIX_APPEND] THEN MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  SUBGOAL_THEN `st2heap p (s:(FFI)state) =
                st2heap p (state_refs_fupd (K (APPEND (APPEND s0 [rv]) s1)) s)`
    SUBST_ALL_TAC THENL
   [REWRITE_TAC[st2heap_def] THEN ASM_REWRITE_TAC[] THEN SIMP[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[lupdate_append2] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[STATE_SAT_CELL_STAR_H_EQ]) THEN
  ASM_REWRITE_TAC[STATE_SAT_CELL_STAR_H_EQ]);;

let STATE_UPDATE_HPROP_REF = prove
 (`(cf_REF (Loc T l) xv STAR H) (st2heap p (s:(FFI)state)) ==>
   (cf_REF (Loc T l) xv' STAR H)
     (st2heap p (state_refs_fupd (K (LUPDATE (Refv xv') l (state_refs s))) s))`,
  REWRITE_TAC[cf_REF_def; SEP_CLAUSES; SEP_EXISTS_THM] THEN
  REWRITE_TAC[GSYM STAR_ASSOC; cf_HCOND_EXTRACT] THEN SIMP[] THEN
  REWRITE_TAC[UNWIND_THM1; STATE_UPDATE_HPROP_CELL]);;

let STATE_UPDATE_HPROP_ARRAY = prove
 (`(cf_ARRAY (Loc T l) av STAR H) (st2heap p (s:(FFI)state)) ==>
   (cf_ARRAY (Loc T l) av' STAR H)
     (st2heap p (state_refs_fupd (K (LUPDATE (Varray av') l (state_refs s))) s))`,
  REWRITE_TAC[cf_ARRAY_def; SEP_CLAUSES; SEP_EXISTS_THM] THEN
  REWRITE_TAC[GSYM STAR_ASSOC; cf_HCOND_EXTRACT] THEN SIMP[] THEN
  REWRITE_TAC[UNWIND_THM1; STATE_UPDATE_HPROP_CELL]);;

(* Fixed-size arrays *)

let ARRAY_REL_def = cake_def
  `ARRAY_REL (TYPE:A->v->bool) rv l =
     SEP_EXISTS av. cf_ARRAY rv av STAR set_sep_cond (ALL2 TYPE l av)`;;

(* Resizable arrays *)

let RARRAY_def = cake_def
  `RARRAY rv av = SEP_EXISTS arv. cf_REF rv arv STAR cf_ARRAY arv av`;;

let RARRAY_REL_def = cake_def
  `RARRAY_REL (TYPE:A->v->bool) rv l =
     SEP_EXISTS av. RARRAY rv av STAR set_sep_cond (ALL2 TYPE l av)`;;

let MON1AUX_one_STAR_one = prove
 (`!a b (s:A->bool). (set_sep_one a STAR set_sep_one b) s <=> s = {a,b} /\ ~(a = b)`,
  REWRITE_TAC[one_STAR; set_sep_one_def] THEN SET_TAC[]);;

let RARRAY_HPROP_SAT_EQ = prove
 (`RARRAY (Loc T l) av s <=>
   ?l'. s = {cf_Mem l' (Varray av), cf_Mem l (Refv (Loc T l'))}`,
  REWRITE_TAC[RARRAY_def; cf_REF_def; cf_ARRAY_def; SEP_CLAUSES; SEP_EXISTS_THM] THEN
  REWRITE_TAC[STAR_ASSOC; cf_HCOND_EXTRACT] THEN
  REWRITE_TAC[GSYM STAR_ASSOC; cf_HCOND_EXTRACT; cf_cell_def; MON1AUX_one_STAR_one] THEN
  SIMP[] THEN REWRITE_TAC[UNWIND_THM1; GSYM CONJ_ASSOC] THEN
  SIMP[RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
  REWRITE_TAC[INSERT_COMM] THEN MESON_TAC[]);;

let ml_monad_translatorBase_GC_ABSORB_L = prove
 (`!A B s. (A STAR B STAR cf_GC) s ==> (A STAR cf_GC) s`,
  REWRITE_TAC[GSYM STAR_ASSOC] THEN REWRITE_TAC[STAR_def] THEN
  MESON_TAC[SAT_GC]);;

let st2heap_SPLIT = prove
 (`SPLIT (st2heap ffi (state_refs_fupd (K (APPEND (state_refs s) junk)) (s:(FFI)state)))
         (st2heap ffi s, store2heap_aux (LENGTH (state_refs s)) junk)`,
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o RAND_CONV) [GSYM with_same_refs] THEN
  MATCH_ACCEPT_TAC STATE_SPLIT_REFS);;

let MON1AUX_STAR_I = prove
 (`!p q (s:A->bool) u v. SPLIT s (u,v) /\ p u /\ q v ==> (p STAR q) s`,
  REWRITE_TAC[STAR_def] THEN MESON_TAC[]);;

let REFS_PRED_FRAME_remove_junk = prove
 (`REFS_PRED_FRAME ro H (n_st,state_refs_fupd (K (APPEND (state_refs s1) junk)) s1)
     (st2,s2) ==>
   REFS_PRED_FRAME ro H ((n_st:A),(s1:(FFI)state)) (st2,s2)`,
  QCASES_ON "H" THEN REWRITE_TAC[REFS_PRED_FRAME_def] THEN SIMP[] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `F' STAR
    (\h:heap. h = store2heap_aux (LENGTH (state_refs (s1:(FFI)state))) junk)`) THEN
  REWRITE_TAC[STAR_ASSOC] THEN ANTS_TAC THENL
   [MATCH_MP_TAC MON1AUX_STAR_I THEN
    MAP_EVERY EXISTS_TAC [`st2heap y (s1:(FFI)state)`;
      `store2heap_aux (LENGTH (state_refs (s1:(FFI)state))) junk`] THEN
    ASM_REWRITE_TAC[st2heap_SPLIT];
    MATCH_ACCEPT_TAC ml_monad_translatorBase_GC_ABSORB_L]);;

