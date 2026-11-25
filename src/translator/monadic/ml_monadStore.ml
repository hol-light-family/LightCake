(* ========================================================================= *)
(* ml_monadStore: port of HOL4 translator/monadic/ml_monadStoreScript.sml    *)
(* (CakeML v3479).  Theorems and lemmas used in ml_monadStoreLib.           *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - HOL4's HCOND_EXTRACT here is cfLetAuto's theorem (an alias,            *)
(*   ml_monadStore_HCOND_EXTRACT); HOL4's local overloads are written out:   *)
(*   * is STAR, & is set_sep_cond, ~~> is cf_REF, ARRAY is cf_ARRAY, GC is   *)
(*   cf_GC, emp is set_sep_emp; s.refs is state_refs s.                      *)
(* - HOL4's variable C (GC_DUPLICATE_1) is C' (C is a HOL Light constant).   *)
(* - HOL4 cfApp's store2heap_aux_append_many is                              *)
(*   MON1AUX_store2heap_aux_append_many of ml_monad_translatorBase.ml.       *)
(* ========================================================================= *)

needs "hol4/set_sep.ml";;
needs "translator/ml_prog.ml";;
needs "characteristic/cfHeapsBase.ml";;
needs "characteristic/cfStore.ml";;
needs "characteristic/cfLetAuto.ml";;
needs "translator/monadic/ml_monad_translatorBase.ml";;

type_invention_error := true;;

let ml_monadStore_HCOND_EXTRACT = cf_HCOND_EXTRACT;;

let SEP_EXISTS_SEPARATE = GEN_ALL(GSYM(hd(CONJUNCTS(SPEC_ALL SEP_CLAUSES))));;

let SEP_EXISTS_INWARD = GEN_ALL(GSYM(el 1 (CONJUNCTS(SPEC_ALL SEP_CLAUSES))));;

let ALLOCATE_ARRAY_evaluate = prove
 (`!(env:v sem_env) (s:(FFI)state) n xname xv.
     nsLookup (sem_env_v env) (Short xname) = SOME xv ==>
     eval_rel s env (App Aalloc [Lit (IntLit (&n)); Var (Short xname)])
       (state_refs_fupd (K (APPEND (state_refs s) [Varray (REPLICATE n xv)])) s)
       (Loc T (LENGTH (state_refs s)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[eval_rel_def] THEN SIMP[] THEN
  MAP_EVERY EXISTS_TAC [`state_clock (s:(FFI)state)`; `state_clock (s:(FFI)state)`] THEN
  FS[evaluate_def; REVERSE; APPEND; getOpClass_def; do_app_def; store_alloc_def; LT;
    list_result_def; state_component_equality]);;

let ALLOCATE_EMPTY_RARRAY_evaluate = prove
 (`!(env:v sem_env) (s:(FFI)state).
     eval_rel s env (App Opref [App AallocEmpty [Con NONE []]])
       (state_refs_fupd
         (K (APPEND (APPEND (state_refs s) [Varray []])
                    [Refv (Loc T (LENGTH (state_refs s)))])) s)
       (Loc T (LENGTH (state_refs s) + 1))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[eval_rel_def] THEN SIMP[] THEN
  MAP_EVERY EXISTS_TAC [`state_clock (s:(FFI)state)`; `state_clock (s:(FFI)state)`] THEN
  FS[evaluate_def; REVERSE; APPEND; getOpClass_def; do_app_def; store_alloc_def;
    do_opapp_def; do_con_check_def; build_conv_def; list_result_def;
    state_component_equality; LENGTH_APPEND; LENGTH; GSYM ONE]);;

let LIST_REL_REPLICATE = prove
 (`!n (TYPE:A->B->bool) x v. TYPE x v ==> ALL2 TYPE (REPLICATE n x) (REPLICATE n v)`,
  INDUCT_TAC THEN ASM_SIMP_TAC[REPLICATE; ALL2]);;

let GC_INWARDS = prove
 (`cf_GC STAR A = A STAR cf_GC`,
  REWRITE_TAC[STAR_COMM]);;

let GC_DUPLICATE_0 = prove
 (`H STAR cf_GC = H STAR cf_GC STAR cf_GC`,
  REWRITE_TAC[GSYM STAR_ASSOC; GC_STAR_GC]);;

let GC_DUPLICATE_1 = prove
 (`A STAR (B STAR cf_GC STAR C') = A STAR cf_GC STAR (B STAR cf_GC STAR C')`,
  GEN_REWRITE_TAC RAND_CONV [AC LSORTAUX_STAR_AC
    `A STAR cf_GC STAR (B STAR cf_GC STAR C') =
     A STAR ((B STAR (cf_GC STAR cf_GC)) STAR C')`] THEN
  REWRITE_TAC[GC_STAR_GC]);;

let GC_DUPLICATE_2 = prove
 (`A STAR (B STAR cf_GC) = A STAR cf_GC STAR (B STAR cf_GC)`,
  MP_TAC(INST [`set_sep_emp:hprop`,`C':hprop`] GC_DUPLICATE_1) THEN
  REWRITE_TAC[SEP_CLAUSES]);;

let GC_DUPLICATE_3 = prove
 (`A STAR cf_GC STAR B = cf_GC STAR (A STAR cf_GC STAR B)`,
  GEN_REWRITE_TAC RAND_CONV [AC LSORTAUX_STAR_AC
    `cf_GC STAR (A STAR cf_GC STAR B) = (A STAR (cf_GC STAR cf_GC)) STAR B`] THEN
  REWRITE_TAC[GC_STAR_GC]);;

let store2heap_aux_decompose_store1 = prove
 (`A (store2heap_aux n a) ==>
   B (store2heap_aux (n + LENGTH a) b) ==>
   (A STAR B) (store2heap_aux n (APPEND a b))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MON1AUX_STAR_I THEN
  MAP_EVERY EXISTS_TAC [`store2heap_aux n a`;
    `store2heap_aux (n + LENGTH (a:(v store_v)list)) b`] THEN
  ASM_REWRITE_TAC[store2heap_aux_SPLIT]);;

let store2heap_aux_decompose_store2 = prove
 (`A (store2heap_aux n [a]) ==>
   B (store2heap_aux (n + 1) b) ==>
   (A STAR B) (store2heap_aux n (CONS a b))`,
  MP_TAC(INST [`[a:v store_v]`,`a:(v store_v)list`] store2heap_aux_decompose_store1) THEN
  REWRITE_TAC[APPEND; LENGTH; GSYM ONE]);;

let cons_to_append = prove
 (`CONS (a:A) (CONS b c) = APPEND [a; b] c`,
  REWRITE_TAC[APPEND]);;

let append_empty = prove
 (`(a:A list) = APPEND a []`,
  REWRITE_TAC[APPEND_NIL]);;

let ml_monadStore_H_STAR_GC_SAT_IMP = prove
 (`H s ==> (H STAR cf_GC) s`,
  REWRITE_TAC[ml_monad_translatorBase_H_STAR_GC_SAT_IMP]);;

let store2heap_REF_SAT = prove
 (`cf_REF (Loc T l) v (store2heap_aux l [Refv v])`,
  REWRITE_TAC[store2heap_aux_def; REF_HPROP_SAT_EQ]);;

let store2heap_eliminate_ffi_thm = prove
 (`H (store2heap (state_refs s)) ==> (cf_GC STAR H) (st2heap p (s:(FFI)state))`,
  DISCH_TAC THEN MATCH_MP_TAC MON1AUX_STAR_I THEN
  MAP_EVERY EXISTS_TAC [`ffi2heap p (state_ffi (s:(FFI)state))`;
    `store2heap (state_refs (s:(FFI)state))`] THEN
  ASM_REWRITE_TAC[SAT_GC; st2heap_def] THEN
  ONCE_REWRITE_TAC[SPLIT_SYM] THEN REWRITE_TAC[st2heap_SPLIT_FFI]);;

let rarray_exact_thm = prove
 (`(l = l' + 1) /\ (n = l') ==>
   RARRAY (Loc T l) av (store2heap_aux n [Varray av; Refv (Loc T l')])`,
  STRIP_TAC THEN ASM_REWRITE_TAC[RARRAY_HPROP_SAT_EQ; store2heap_aux_def] THEN
  EXISTS_TAC `l':num` THEN REWRITE_TAC[]);;

let farray_exact_thm = prove
 (`(n = l) ==> cf_ARRAY (Loc T l) av (store2heap_aux n [Varray av])`,
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[store2heap_aux_def; ARRAY_HPROP_SAT_EQ]);;

let eliminate_inherited_references_thm = prove
 (`!a b. H (store2heap_aux (LENGTH a) b) ==>
         (cf_GC STAR H) (store2heap_aux 0 (APPEND a b))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MON1AUX_STAR_I THEN
  MAP_EVERY EXISTS_TAC [`store2heap_aux 0 a`;
    `store2heap_aux (LENGTH (a:(v store_v)list)) b`] THEN
  ASM_REWRITE_TAC[SAT_GC] THEN
  MP_TAC(SPECL [`a:(v store_v)list`; `b:(v store_v)list`; `0`] store2heap_aux_SPLIT) THEN
  REWRITE_TAC[ADD_CLAUSES]);;

let eliminate_substore_thm = prove
 (`(H1 STAR cf_GC STAR H2) (store2heap_aux (n + LENGTH a) b) ==>
   (H1 STAR cf_GC STAR H2) (store2heap_aux n (APPEND a b))`,
  DISCH_TAC THEN ONCE_REWRITE_TAC[GC_DUPLICATE_3] THEN MATCH_MP_TAC MON1AUX_STAR_I THEN
  MAP_EVERY EXISTS_TAC [`store2heap_aux n a`;
    `store2heap_aux (n + LENGTH (a:(v store_v)list)) b`] THEN
  ASM_REWRITE_TAC[SAT_GC; store2heap_aux_SPLIT]);;

let eliminate_store_elem_thm = prove
 (`(H1 STAR cf_GC STAR H2) (store2heap_aux (n + 1) b) ==>
   (H1 STAR cf_GC STAR H2) (store2heap_aux n (CONS a b))`,
  MP_TAC(INST [`[a:v store_v]`,`a:(v store_v)list`] eliminate_substore_thm) THEN
  REWRITE_TAC[APPEND; LENGTH; GSYM ONE]);;

let H_STAR_empty = prove
 (`(H:(A->bool)->bool) STAR set_sep_emp = H`,
  REWRITE_TAC[SEP_CLAUSES]);;

let ml_monadStore_H_STAR_TRUE = prove
 (`((H:(A->bool)->bool) STAR set_sep_cond T = H) /\ (set_sep_cond T STAR H = H)`,
  REWRITE_TAC[SEP_CLAUSES]);;

