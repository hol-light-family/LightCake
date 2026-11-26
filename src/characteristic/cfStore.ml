(* ========================================================================= *)
(* cfStore: port of HOL4 characteristic/cfStoreScript.sml (CakeML v3479).    *)
(* Conversion from semantic stores to heaps.                                 *)
(*                                                                           *)
(* Notation as in characteristic/cfHeapsBase.ml; HOL4's 'ffi ffi_proj is     *)
(* written out as (FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list) *)
(* and 'ffi semanticPrimitives$state as (FFI)state.  HOL4's Ancestors list   *)
(* ml_translator, which the theory does not use: it is not loaded here.     *)
(* The lemmas about store2heap_aux are proved from one characterisation of   *)
(* its members (CF1AUX_store2heap_aux_IN) instead of HOL4's inductions.     *)
(* Helper lemmas that are not HOL4 theorems are CF1AUX_.                     *)
(* ========================================================================= *)

needs "characteristic/cfHeaps.ml";;
needs "hol4/set_sep.ml";;
needs "semantics/semanticPrimitives.ml";;

type_invention_error := true;;

(* Definitions *)

let store2heap_aux_def = cake_def
  `(store2heap_aux n [] = ({}:heap)) /\
   (store2heap_aux n (CONS v t) = (cf_Mem n v) INSERT (store2heap_aux (n + 1:num) t))`;;

(* store2heap: v store -> heap *)
let store2heap_def = cake_def
  `store2heap l = store2heap_aux (0:num) l`;;

let ffi_has_index_in_def = cake_def
  `(ffi_has_index_in ns (IO_event (ExtCall i) conf ws) <=> MEM i ns) /\
   (ffi_has_index_in _ _ <=> F)`;;

let parts_ok_def = cake_def
  `parts_ok (st:(FFI)ffi_state)
            ((proj,parts):(FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)) <=>
     ALL_DISTINCT (FLAT (MAP FST parts)) /\
     ALL (ffi_has_index_in (FLAT (MAP FST parts))) (ffi_state_io_events st) /\
     (!ns u.
        MEM (ns,u) parts ==>
        ?s. !n. MEM n ns ==> FLOOKUP (proj (ffi_state_ffi_state st)) n = SOME s) /\
     (!x conf bytes m ns u.
        MEM (ns,u) parts /\ MEM m ns /\
        u m conf bytes (FAPPLY (proj x) m) = SOME FFIdiverge ==>
        ffi_state_oracle st (ExtCall m) x conf bytes = Oracle_final FFI_diverged) /\
     !x conf bytes w new_bytes m ns u.
       MEM (ns,u) parts /\ MEM m ns /\
       u m conf bytes (FAPPLY (proj x) m) = SOME (FFIreturn new_bytes w) ==>
       LENGTH new_bytes = LENGTH bytes /\
       ?y.
         ffi_state_oracle st (ExtCall m) x conf bytes = Oracle_return y new_bytes /\
         proj x |++ (MAP (\n. (n,w)) ns) = proj y`;;

let ffi2heap_def = cake_def
  `ffi2heap ((proj,parts):(FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list))
            (st:(FFI)ffi_state) =
     if parts_ok st (proj,parts) then
       cf_FFI_split INSERT
       { cf_FFI_part s u ns ts | s,u,ns,ts |
         MEM (ns,u) parts /\ ~(ns = []) /\
         ts = FILTER (ffi_has_index_in ns) (ffi_state_io_events st) /\
         !n. MEM n ns ==> FLOOKUP (proj (ffi_state_ffi_state st)) n = SOME s }
     else
       { cf_FFI_full (ffi_state_io_events st) }`;;

(* st2heap: 'ffi state -> heap *)
let st2heap_def = cake_def
  `st2heap (f:(FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list))
           (st:(FFI)state) =
     store2heap (state_refs st) UNION ffi2heap f (state_ffi st)`;;

(* Lemmas *)

(* helper: the members cf_Mem u v of store2heap_aux n s *)
let CF1AUX_store2heap_aux_IN = prove
 (`!s n u v. cf_Mem u v IN store2heap_aux n s <=>
             n <= u /\ u < n + LENGTH s /\ EL (u - n) s = v`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[store2heap_aux_def; NOT_IN_EMPTY; IN_INSERT; LENGTH] THENL
   [ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN SIMP[] THEN ASM_CASES_TAC `u:num = n` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REWRITE_TAC[SUB_REFL; EL; HD; LE_REFL; ARITH_RULE `~(n + 1 <= n) /\ n <= n + l`] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_CASES_TAC `n <= u` THENL
   [SUBGOAL_THEN `u - n = SUC (u - (n + 1))` SUBST1_TAC THENL
     [ASM_ARITH_TAC; REWRITE_TAC[EL; TL]] THEN
    ASM_SIMP_TAC[ARITH_RULE `n <= u /\ ~(u = n)
                   ==> (n + 1 <= u <=> T) /\ (u < (n + 1) + l <=> u <= n + l)`];
    ASM_SIMP_TAC[ARITH_RULE `~(n <= u) ==> ~(n + 1 <= u)`]]);;

let store2heap_aux_append = prove
 (`!s n x.
     store2heap_aux n (APPEND s [x]) =
     (cf_Mem (LENGTH s + n) x) INSERT store2heap_aux n s`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[store2heap_aux_def; APPEND; LENGTH; ADD_CLAUSES] THEN
  REWRITE_TAC[ARITH_RULE `l + n + 1 = SUC (l + n)`] THEN SET_TAC[]);;

let store2heap_append = prove
 (`!s x. store2heap (APPEND s [x]) = cf_Mem (LENGTH s) x INSERT store2heap s`,
  REWRITE_TAC[store2heap_def; store2heap_aux_append; ADD_CLAUSES]);;

let store2heap_aux_suc = prove
 (`!s n u v.
     (cf_Mem u v IN store2heap_aux n s) <=>
     (cf_Mem (SUC u) v IN store2heap_aux (SUC n) s)`,
  REWRITE_TAC[CF1AUX_store2heap_aux_IN; LE_SUC; SUB_SUC; ADD_CLAUSES; LT_SUC]);;

let store2heap_aux_IN_bound = prove
 (`!s n u v. cf_Mem u v IN store2heap_aux n s ==> (u >= n)`,
  SIMP[CF1AUX_store2heap_aux_IN; GE]);;

let store2heap_alloc_disjoint = prove
 (`!s x. ~(cf_Mem (LENGTH s) x IN (store2heap s))`,
  REWRITE_TAC[store2heap_def; CF1AUX_store2heap_aux_IN; ADD_CLAUSES; LT_REFL]);;

let store2heap_IN_LENGTH = prove
 (`!s r x. cf_Mem r x IN (store2heap s) ==> r < LENGTH s`,
  SIMP[store2heap_def; CF1AUX_store2heap_aux_IN; ADD_CLAUSES]);;

(* HOL4's tac_store2heap_IN (an SML tactic) proves the next two *)

let store2heap_IN_EL = prove
 (`!s r x. cf_Mem r x IN (store2heap s) ==> EL r s = x`,
  SIMP[store2heap_def; CF1AUX_store2heap_aux_IN; SUB_0]);;

let store2heap_IN_unique_key = prove
 (`!s r x.
     cf_Mem r x IN (store2heap s) ==>
     !x'. cf_Mem r x' IN (store2heap s) ==> x = x'`,
  MESON_TAC[store2heap_IN_EL]);;

let Mem_NOT_IN_ffi2heap = prove
 (`~(cf_Mem rv x IN
     ffi2heap (p:(FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)) f)`,
  PAIR_CASES_ON `p:(FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)` THEN
  REWRITE_TAC[ffi2heap_def] THEN COND_CASES_TAC THEN
  SIMP[IN_INSERT; IN_ELIM_THM; IN_SING]);;

let FFI_split_NOT_IN_store2heap_aux = prove
 (`!n s. ~(cf_FFI_split IN store2heap_aux n s)`,
  QINDUCT_ON "s" THEN SIMP[store2heap_aux_def; NOT_IN_EMPTY; IN_INSERT]);;

let FFI_part_NOT_IN_store2heap_aux = prove
 (`!n s. ~(cf_FFI_part x1 x2 x3 x4 IN store2heap_aux n s)`,
  QINDUCT_ON "s" THEN SIMP[store2heap_aux_def; NOT_IN_EMPTY; IN_INSERT]);;

let FFI_full_NOT_IN_store2heap_aux = prove
 (`!n s. ~(cf_FFI_full x1 IN store2heap_aux n s)`,
  QINDUCT_ON "s" THEN SIMP[store2heap_aux_def; NOT_IN_EMPTY; IN_INSERT]);;

let cf_FFI_part_NOT_IN_store2heap = prove
 (`!s. ~(cf_FFI_split IN store2heap s) /\
       ~(cf_FFI_part x1 x2 x3 x4 IN store2heap s) /\
       ~(cf_FFI_full y2 IN store2heap s)`,
  REWRITE_TAC[store2heap_def; FFI_part_NOT_IN_store2heap_aux;
              FFI_full_NOT_IN_store2heap_aux; FFI_split_NOT_IN_store2heap_aux]);;

let store2heap_LUPDATE = prove
 (`!s r x y.
     cf_Mem r y IN (store2heap s) ==>
     store2heap (LUPDATE x r s) = cf_Mem r x INSERT ((store2heap s) DELETE cf_Mem r y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_INSERT; IN_DELETE] THEN
  X_GEN_TAC `z:heap_part` THEN QCASES_ON "z" THEN
  SIMP[cf_FFI_part_NOT_IN_store2heap] THEN
  RENAME1 "cf_Mem u w IN store2heap (LUPDATE x r s)" THEN
  POP_ASSUM MP_TAC THEN
  REWRITE_TAC[store2heap_def; CF1AUX_store2heap_aux_IN; LENGTH_LUPDATE; EL_LUPDATE;
              SUB_0; LE_0; ADD_CLAUSES] THEN
  ASM_CASES_TAC `u:num = r` THEN ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let st2heap_clock = prove
 (`!st ck.
     st2heap (p:(FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list))
             (state_clock_fupd (combin_K ck) st) =
     st2heap p st`,
  SIMP[st2heap_def]);;
