(* ========================================================================= *)
(* mergesort: port of HOL4 src/sort/mergesortScript.sml (HOL4 library used  *)
(* by CakeML v3479): merge sort (mergesort, via mergesortN) and its tail-    *)
(* recursive version (mergesort_tail, via mergesortN_tail and merge_tail,    *)
(* as in OCaml's library), with permutation, sortedness, stability and the   *)
(* equivalence of the two versions.                                          *)
(*                                                                           *)
(* Names: HOL4 merge is mergesort_merge (clos_known has its own merge), with *)
(* mergesort_merge_def and mergesort_merge_ind.  HOL4 mergesortN_def and     *)
(* mergesortN_tail_def (overlapping literal patterns) are stated as HOL4     *)
(* states them: the clauses for 0..3 and a catch-all equation with the       *)
(* if-cascade; mergesortN_ind and mergesortN_tail_ind have one case per      *)
(* clause.  The single-equation definitions and the kit's one-case           *)
(* induction theorems are LSORTAUX_mergesortN_eqn, LSORTAUX_mergesortN_ind   *)
(* (and _tail_).  HOL4 x <> neg (bool) is ~(x <=> neg); l1 ++ l2 is APPEND.  *)
(* Not ported: mergesort_STABLE_SORT (sorting's STABLE is not ported).       *)
(* REV, REV_REVERSE_LEM and MEM_REVERSE come from list.ml.                   *)
(* ========================================================================= *)

needs "hol4/vocab.ml";;
needs "hol4/list.ml";;
needs "hol4/sorting.ml";;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Definitions.                                                              *)
(* ------------------------------------------------------------------------- *)

let stable_def = new_definition
  `stable (R:A->A->bool) l1 l2 <=>
     !p. (!x y. p x /\ p y ==> R x y) ==> FILTER p l1 = FILTER p l2`;;

let sort2_def = new_definition
  `sort2 (R:A->A->bool) x y = if R x y then [x; y] else [y; x]`;;

let sort3_def = new_definition
  `sort3 (R:A->A->bool) x y z =
     if R x y then
       if R y z then [x; y; z] else if R x z then [x; z; y] else [z; x; y]
     else if R y z then
       if R x z then [y; x; z] else [y; z; x]
     else [z; y; x]`;;

let mergesort_merge_def = cake_def_wf
  `measure (\p:(A->A->bool)#A list#A list.
              LENGTH (FST (SND p)) + LENGTH (SND (SND p)))`
  (REWRITE_TAC[measure_THM; FST; SND; LENGTH] THEN ARITH_TAC)
  `(mergesort_merge R ([]:A list) [] = []) /\
   (mergesort_merge R (CONS v4 v5) [] = CONS v4 v5) /\
   (mergesort_merge R [] (CONS v8 v9) = CONS v8 v9) /\
   (mergesort_merge R (CONS x l1) (CONS y l2) =
      if R x y then CONS x (mergesort_merge R l1 (CONS y l2))
      else CONS y (mergesort_merge R (CONS x l1) l2))`;;

let mergesort_merge_ind = cake_ind "mergesort_merge";;

let LSORTAUX_mergesortN_eqn = cake_def_wf
  `measure (\p:(A->A->bool)#num#A list. FST (SND p))`
  (REWRITE_TAC[measure_THM; FST; SND; DIV2_DEF] THEN REPEAT STRIP_TAC THEN
   ASM_ARITH_TAC)
  `mergesortN R n (l:A list) =
     if n = 0 then [] else
     if n = 1 then (match l with [] -> [] | CONS x l' -> [x]) else
     if n = 2 then (match l with [] -> [] | [x] -> [x]
                                | CONS x (CONS y l') -> sort2 R x y) else
     if n = 3 then (match l with [] -> [] | [x] -> [x]
                                | [x; y] -> sort2 R x y
                                | CONS x (CONS y (CONS z l')) -> sort3 R x y z)
     else
     let len1 = DIV2 n in
       mergesort_merge R (mergesortN R (DIV2 n) l)
                         (mergesortN R (n - len1) (DROP len1 l))`;;

let LSORTAUX_mergesortN_ind = cake_ind "mergesortN";;

let mergesort_def = new_definition
  `mergesort (R:A->A->bool) l = mergesortN R (LENGTH l) l`;;

let sort2_tail_def = new_definition
  `sort2_tail (neg:bool) (R:A->A->bool) x y =
     if ~(R x y <=> neg) then [x; y] else [y; x]`;;

let sort3_tail_def = new_definition
  `sort3_tail (neg:bool) (R:A->A->bool) x y z =
     if ~(R x y <=> neg) then
       if ~(R y z <=> neg) then [x; y; z]
       else if ~(R x z <=> neg) then [x; z; y] else [z; x; y]
     else if ~(R y z <=> neg) then
       if ~(R x z <=> neg) then [y; x; z] else [y; z; x]
     else [z; y; x]`;;

let merge_tail_def = cake_def_wf
  `measure (\p:bool#(A->A->bool)#A list#A list#A list.
              LENGTH (FST (SND (SND p))) + LENGTH (FST (SND (SND (SND p)))))`
  (REWRITE_TAC[measure_THM; FST; SND; LENGTH] THEN ARITH_TAC)
  `(merge_tail (negate:bool) R ([]:A list) [] acc = acc) /\
   (merge_tail negate R (CONS v4 v5) [] acc = REV (CONS v4 v5) acc) /\
   (merge_tail negate R [] (CONS v8 v9) acc = REV (CONS v8 v9) acc) /\
   (merge_tail negate R (CONS x l1) (CONS y l2) acc =
      if ~(R x y <=> negate) then merge_tail negate R l1 (CONS y l2) (CONS x acc)
      else merge_tail negate R (CONS x l1) l2 (CONS y acc))`;;

let merge_tail_ind = cake_ind "merge_tail";;

let LSORTAUX_mergesortN_tail_eqn = cake_def_wf
  `measure (\p:bool#(A->A->bool)#num#A list. FST (SND (SND p)))`
  (REWRITE_TAC[measure_THM; FST; SND; DIV2_DEF] THEN REPEAT STRIP_TAC THEN
   ASM_ARITH_TAC)
  `mergesortN_tail (negate:bool) R n (l:A list) =
     if n = 0 then [] else
     if n = 1 then (match l with [] -> [] | CONS x l' -> [x]) else
     if n = 2 then (match l with [] -> [] | [x] -> [x]
                                | CONS x (CONS y l') -> sort2_tail negate R x y)
     else
     if n = 3 then (match l with [] -> [] | [x] -> [x]
                                | [x; y] -> sort2_tail negate R x y
                                | CONS x (CONS y (CONS z l')) ->
                                    sort3_tail negate R x y z)
     else
     let len1 = DIV2 n in
     let neg = ~negate in
       merge_tail neg R (mergesortN_tail neg R (DIV2 n) l)
                        (mergesortN_tail neg R (n - len1) (DROP len1 l)) []`;;

let LSORTAUX_mergesortN_tail_ind = cake_ind "mergesortN_tail";;

let mergesort_tail_def = new_definition
  `mergesort_tail (R:A->A->bool) l = mergesortN_tail F R (LENGTH l) l`;;

(* ------------------------------------------------------------------------- *)
(* HOL4 forms of the definitions and induction theorems.                     *)
(* ------------------------------------------------------------------------- *)

let LSORTAUX_LIST_CASES2 = prove
 (`!l:A list. l = [] \/ (?x. l = [x]) \/ ?x y t. l = CONS x (CONS y t)`,
  MESON_TAC[list_CASES]);;

let LSORTAUX_LIST_CASES3 = prove
 (`!l:A list. l = [] \/ (?x. l = [x]) \/ (?x y. l = [x; y]) \/
              ?x y z t. l = CONS x (CONS y (CONS z t))`,
  GEN_TAC THEN
  REPEAT_TCL STRIP_THM_THEN SUBST1_TAC (ISPEC `l:A list` list_CASES) THEN
  REWRITE_TAC[NOT_CONS_NIL; CONS_11] THEN
  REPEAT_TCL STRIP_THM_THEN SUBST1_TAC (ISPEC `t:A list` list_CASES) THEN
  REWRITE_TAC[NOT_CONS_NIL; CONS_11; GSYM CONJ_ASSOC; UNWIND_THM1;
              RIGHT_EXISTS_AND_THM; EXISTS_REFL] THEN
  REPEAT_TCL STRIP_THM_THEN SUBST1_TAC (ISPEC `t':A list` list_CASES) THEN
  REWRITE_TAC[NOT_CONS_NIL; CONS_11] THEN MESON_TAC[]);;

let mergesortN_def =
  let th = prove
   (`(!R (l:A list). mergesortN R 0 l = []) /\
     (!R (x:A) l. mergesortN R 1 (CONS x l) = [x]) /\
     (!R. mergesortN R 1 ([]:A list) = []) /\
     (!R (x:A) y l. mergesortN R 2 (CONS x (CONS y l)) = sort2 R x y) /\
     (!R (x:A). mergesortN R 2 [x] = [x]) /\
     (!R. mergesortN R 2 ([]:A list) = []) /\
     (!R (x:A) y z l.
        mergesortN R 3 (CONS x (CONS y (CONS z l))) = sort3 R x y z) /\
     (!R (x:A) y. mergesortN R 3 [x; y] = sort2 R x y) /\
     (!R (x:A). mergesortN R 3 [x] = [x]) /\
     (!R. mergesortN R 3 ([]:A list) = [])`,
    REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [LSORTAUX_mergesortN_eqn] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[list_CASE]) in
  end_itlist CONJ (CONJUNCTS th @ [LSORTAUX_mergesortN_eqn]);;

let mergesortN_ind = prove
 (`!P:(A->A->bool)->num->A list->bool.
     (!R l. P R 0 l) /\
     (!R x l. P R 1 (CONS x l)) /\
     (!R. P R 1 []) /\
     (!R x y l. P R 2 (CONS x (CONS y l))) /\
     (!R x. P R 2 [x]) /\
     (!R. P R 2 []) /\
     (!R x y z l. P R 3 (CONS x (CONS y (CONS z l)))) /\
     (!R x y. P R 3 [x; y]) /\
     (!R x. P R 3 [x]) /\
     (!R. P R 3 []) /\
     (!R n l.
        (~(n = 0) /\ ~(n = 1) /\ ~(n = 2) /\ ~(n = 3) ==> P R (DIV2 n) l) /\
        (~(n = 0) /\ ~(n = 1) /\ ~(n = 2) /\ ~(n = 3)
         ==> P R (n - DIV2 n) (DROP (DIV2 n) l))
        ==> P R n l)
     ==> !v v1 v2. P v v1 v2`,
  GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC LSORTAUX_mergesortN_ind THEN
  MAP_EVERY X_GEN_TAC [`R:A->A->bool`; `n:num`; `l:A list`] THEN DISCH_TAC THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `n = 1` THENL
   [ASM_REWRITE_TAC[] THEN
    REPEAT_TCL STRIP_THM_THEN SUBST1_TAC (ISPEC `l:A list` list_CASES) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `n = 2` THENL
   [ASM_REWRITE_TAC[] THEN
    REPEAT_TCL STRIP_THM_THEN SUBST1_TAC (ISPEC `l:A list` LSORTAUX_LIST_CASES2) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `n = 3` THENL
   [ASM_REWRITE_TAC[] THEN
    REPEAT_TCL STRIP_THM_THEN SUBST1_TAC (ISPEC `l:A list` LSORTAUX_LIST_CASES3) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "DIV2")) (concl th))) THEN
  ASM_REWRITE_TAC[]);;

let mergesortN_tail_def =
  let th = prove
   (`(!negate R (l:A list). mergesortN_tail negate R 0 l = []) /\
     (!negate R (x:A) l. mergesortN_tail negate R 1 (CONS x l) = [x]) /\
     (!negate R. mergesortN_tail negate R 1 ([]:A list) = []) /\
     (!negate R (x:A) y l.
        mergesortN_tail negate R 2 (CONS x (CONS y l)) = sort2_tail negate R x y) /\
     (!negate R (x:A). mergesortN_tail negate R 2 [x] = [x]) /\
     (!negate R. mergesortN_tail negate R 2 ([]:A list) = []) /\
     (!negate R (x:A) y z l.
        mergesortN_tail negate R 3 (CONS x (CONS y (CONS z l))) =
        sort3_tail negate R x y z) /\
     (!negate R (x:A) y.
        mergesortN_tail negate R 3 [x; y] = sort2_tail negate R x y) /\
     (!negate R (x:A). mergesortN_tail negate R 3 [x] = [x]) /\
     (!negate R. mergesortN_tail negate R 3 ([]:A list) = [])`,
    REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [LSORTAUX_mergesortN_tail_eqn] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[list_CASE]) in
  end_itlist CONJ (CONJUNCTS th @ [LSORTAUX_mergesortN_tail_eqn]);;

let mergesortN_tail_ind = prove
 (`!P:bool->(A->A->bool)->num->A list->bool.
     (!negate R l. P negate R 0 l) /\
     (!negate R x l. P negate R 1 (CONS x l)) /\
     (!negate R. P negate R 1 []) /\
     (!negate R x y l. P negate R 2 (CONS x (CONS y l))) /\
     (!negate R x. P negate R 2 [x]) /\
     (!negate R. P negate R 2 []) /\
     (!negate R x y z l. P negate R 3 (CONS x (CONS y (CONS z l)))) /\
     (!negate R x y. P negate R 3 [x; y]) /\
     (!negate R x. P negate R 3 [x]) /\
     (!negate R. P negate R 3 []) /\
     (!negate R n l.
        (~(n = 0) /\ ~(n = 1) /\ ~(n = 2) /\ ~(n = 3)
         ==> P (~negate) R (DIV2 n) l) /\
        (~(n = 0) /\ ~(n = 1) /\ ~(n = 2) /\ ~(n = 3)
         ==> P (~negate) R (n - DIV2 n) (DROP (DIV2 n) l))
        ==> P negate R n l)
     ==> !v v1 v2 v3. P v v1 v2 v3`,
  GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC LSORTAUX_mergesortN_tail_ind THEN
  MAP_EVERY X_GEN_TAC [`negate:bool`; `R:A->A->bool`; `n:num`; `l:A list`] THEN
  DISCH_TAC THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `n = 1` THENL
   [ASM_REWRITE_TAC[] THEN
    REPEAT_TCL STRIP_THM_THEN SUBST1_TAC (ISPEC `l:A list` list_CASES) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `n = 2` THENL
   [ASM_REWRITE_TAC[] THEN
    REPEAT_TCL STRIP_THM_THEN SUBST1_TAC (ISPEC `l:A list` LSORTAUX_LIST_CASES2) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `n = 3` THENL
   [ASM_REWRITE_TAC[] THEN
    REPEAT_TCL STRIP_THM_THEN SUBST1_TAC (ISPEC `l:A list` LSORTAUX_LIST_CASES3) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "DIV2")) (concl th))) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Permutation.                                                              *)
(* ------------------------------------------------------------------------- *)

let LSORTAUX_LENGTH_FILTER_CONS = prove
 (`!P (h:A) t. LENGTH (FILTER P (CONS h t)) = (if P h then 1 else 0) + LENGTH (FILTER P t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FILTER] THEN COND_CASES_TAC THEN
  REWRITE_TAC[LENGTH] THEN ARITH_TAC);;

let LSORTAUX_PERM_ARITH_TAC =
  REWRITE_TAC[PERM_alt; LSORTAUX_LENGTH_FILTER_CONS; FILTER_APPEND; LENGTH_APPEND;
              CONJUNCT1 FILTER; LENGTH] THEN ARITH_TAC;;

let LSORTAUX_PERM_MOVE = prove
 (`!(y:A) A B. PERM (APPEND A (CONS y B)) (CONS y (APPEND A B))`,
  LSORTAUX_PERM_ARITH_TAC);;

let sort2_perm = prove
 (`!R (x:A) y. PERM [x; y] (sort2 R x y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sort2_def] THEN COND_CASES_TAC THEN
  LSORTAUX_PERM_ARITH_TAC);;

let sort3_perm = prove
 (`!R (x:A) y z. PERM [x; y; z] (sort3 R x y z)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sort3_def] THEN REPEAT COND_CASES_TAC THEN
  LSORTAUX_PERM_ARITH_TAC);;

let merge_perm = prove
 (`!R (l1:A list) l2. PERM (APPEND l1 l2) (mergesort_merge R l1 l2)`,
  MATCH_MP_TAC mergesort_merge_ind THEN
  REWRITE_TAC[mergesort_merge_def; APPEND; APPEND_NIL; PERM_REFL] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[PERM_CONS_IFF] THEN
  MATCH_MP_TAC PERM_TRANS THEN
  EXISTS_TAC `CONS (y:A) (CONS x (APPEND l1 l2))` THEN CONJ_TAC THENL
   [LSORTAUX_PERM_ARITH_TAC; ASM_SIMP_TAC[PERM_CONS_IFF]]);;

let LSORTAUX_TAKE_0 = prove
 (`!l:A list. TAKE 0 l = []`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[TAKE_DEF]);;

let LSORTAUX_DROP_0 = prove
 (`!l:A list. DROP 0 l = l`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[DROP_DEF]);;

let LSORTAUX_take_drop_partition = prove
 (`!(l:A list) n m.
     m <= n ==> APPEND (TAKE m l) (TAKE (n - m) (DROP m l)) = TAKE n l`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[TAKE_DEF; DROP_DEF; APPEND] THEN
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `m = 0` THEN
  ASM_REWRITE_TAC[APPEND; SUB_0; TAKE_DEF] THEN
  SUBGOAL_THEN `~(n = 0) /\ n - m = (n - 1) - (m - 1) /\ m - 1 <= n - 1`
    STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[APPEND; CONS_11] THEN ASM_SIMP_TAC[]);;

let LSORTAUX_MSN_CASES_TAC (fin:tactic) : tactic =
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[] THENL [fin; ALL_TAC] THEN
  ASM_CASES_TAC `n = 1` THEN ASM_REWRITE_TAC[] THENL
   [REPEAT_TCL STRIP_THM_THEN SUBST1_TAC (ISPEC `l:A list` list_CASES) THEN
    REWRITE_TAC[list_CASE] THEN fin; ALL_TAC] THEN
  ASM_CASES_TAC `n = 2` THEN ASM_REWRITE_TAC[] THENL
   [REPEAT_TCL STRIP_THM_THEN SUBST1_TAC (ISPEC `l:A list` LSORTAUX_LIST_CASES2) THEN
    REWRITE_TAC[list_CASE] THEN fin; ALL_TAC] THEN
  ASM_CASES_TAC `n = 3` THEN ASM_REWRITE_TAC[] THENL
   [REPEAT_TCL STRIP_THM_THEN SUBST1_TAC (ISPEC `l:A list` LSORTAUX_LIST_CASES3) THEN
    REWRITE_TAC[list_CASE] THEN fin; ALL_TAC] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_conj o concl)) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC;;

let LSORTAUX_TAKE_TAC =
  REWRITE_TAC[TAKE_DEF] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[LSORTAUX_TAKE_0];;

let mergesortN_perm = prove
 (`!R n (l:A list). PERM (TAKE n l) (mergesortN R n l)`,
  MATCH_MP_TAC LSORTAUX_mergesortN_ind THEN
  MAP_EVERY X_GEN_TAC [`R:A->A->bool`; `n:num`; `l:A list`] THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[LSORTAUX_mergesortN_eqn] THEN
  LSORTAUX_MSN_CASES_TAC
   (LSORTAUX_TAKE_TAC THEN REWRITE_TAC[PERM_REFL; sort2_perm; sort3_perm]) THEN
  MP_TAC(ISPECL [`l:A list`; `n:num`; `DIV2 n`] LSORTAUX_take_drop_partition) THEN
  REWRITE_TAC[DIV2_DEF] THEN ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DIV2_DEF]) THEN
  MATCH_MP_TAC PERM_TRANS THEN
  EXISTS_TAC `APPEND (mergesortN R (n DIV 2) (l:A list))
                     (mergesortN R (n - n DIV 2) (DROP (n DIV 2) l))` THEN
  ASM_SIMP_TAC[PERM_CONG; merge_perm]);;

(* ------------------------------------------------------------------------- *)
(* Sortedness.                                                               *)
(* ------------------------------------------------------------------------- *)

let LSORTAUX_TAKE_LENGTH_ID = prove
 (`!l:A list. TAKE (LENGTH l) l = l`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[TAKE_DEF; LENGTH; NOT_SUC; SUC_SUB1]);;

let mergesort_perm = prove
 (`!R (l:A list). PERM l (mergesort R l)`,
  REWRITE_TAC[mergesort_def] THEN
  MESON_TAC[mergesortN_perm; LSORTAUX_TAKE_LENGTH_ID]);;

let sort2_sorted = prove
 (`!R (x:A) y. total R ==> SORTED R (sort2 R x y)`,
  REWRITE_TAC[sort2_def; total_DEF] THEN REPEAT STRIP_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[SORTED_DEF] THEN ASM_MESON_TAC[]);;

let sort3_sorted = prove
 (`!R (x:A) y z. total R ==> SORTED R (sort3 R x y z)`,
  REWRITE_TAC[sort3_def; total_DEF] THEN REPEAT STRIP_TAC THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[SORTED_DEF] THEN ASM_MESON_TAC[]);;

let merge_sorted = prove
 (`!R (l1:A list) l2.
     transitive R /\ total R /\ SORTED R l1 /\ SORTED R l2
     ==> SORTED R (mergesort_merge R l1 l2)`,
  MATCH_MP_TAC mergesort_merge_ind THEN
  REWRITE_TAC[mergesort_merge_def] THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  TRY(SIMP_TAC[SORTED_DEF] THEN NO_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih2") (LABEL_TAC "ih1")) THEN STRIP_TAC THEN
  SUBGOAL_THEN `!z:A. MEM z (mergesort_merge R l1 (CONS y l2)) <=>
                      MEM z (APPEND l1 (CONS y l2))` ASSUME_TAC THENL
   [MESON_TAC[merge_perm; PERM_MEM_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `!z:A. MEM z (mergesort_merge R (CONS x l1) l2) <=>
                      MEM z (APPEND (CONS x l1) l2)` ASSUME_TAC THENL
   [MESON_TAC[merge_perm; PERM_MEM_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `SORTED R (l1:A list) /\ (!z. MEM z l1 ==> R x z) /\
                SORTED R (l2:A list) /\ (!z. MEM z l2 ==> R y z)`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[SORTED_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `(!a b c:A. R a b /\ R b c ==> R a c) /\ (!a b:A. R a b \/ R b a)`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[transitive_DEF; total_DEF]; ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[SORTED_EQ] THEN
  REWRITE_TAC[MEM_APPEND; MEM] THEN ASM_MESON_TAC[]);;

let mergesortN_sorted = prove
 (`!R n (l:A list). total R /\ transitive R ==> SORTED R (mergesortN R n l)`,
  MATCH_MP_TAC LSORTAUX_mergesortN_ind THEN
  MAP_EVERY X_GEN_TAC [`R:A->A->bool`; `n:num`; `l:A list`] THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[LSORTAUX_mergesortN_eqn] THEN
  LSORTAUX_MSN_CASES_TAC
   (REWRITE_TAC[SORTED_DEF] THEN SIMP_TAC[sort2_sorted; sort3_sorted]) THEN
  STRIP_TAC THEN MATCH_MP_TAC merge_sorted THEN ASM_SIMP_TAC[]);;

let mergesort_sorted = prove
 (`!R (l:A list). transitive R /\ total R ==> SORTED R (mergesort R l)`,
  MESON_TAC[mergesort_def; mergesortN_sorted]);;

let mergesort_mem = prove
 (`!R (L:A list) x. MEM x (mergesort R L) <=> MEM x L`,
  MESON_TAC[mergesort_perm; PERM_MEM_EQ]);;

(* ------------------------------------------------------------------------- *)
(* Stability.                                                                *)
(* ------------------------------------------------------------------------- *)

let stable_cong = prove
 (`!R (l1:A list) l2 l3 l4.
     stable R l1 l2 /\ stable R l3 l4
     ==> stable R (APPEND l1 l3) (APPEND l2 l4)`,
  REWRITE_TAC[stable_def; FILTER_APPEND] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[]);;

let stable_trans = prove
 (`!R (l1:A list) l2 l3. stable R l1 l2 /\ stable R l2 l3 ==> stable R l1 l3`,
  REWRITE_TAC[stable_def] THEN MESON_TAC[]);;

let LSORTAUX_stable_refl = prove
 (`!R (l:A list). stable R l l`,
  REWRITE_TAC[stable_def]);;

let sort2_stable = prove
 (`!R (x:A) y. stable R [x; y] (sort2 R x y)`,
  REWRITE_TAC[stable_def; sort2_def] THEN REPEAT STRIP_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[FILTER] THEN
  MAP_EVERY ASM_CASES_TAC [`(p:A->bool) x`; `(p:A->bool) y`] THEN
  ASM_REWRITE_TAC[CONS_11] THEN ASM_MESON_TAC[]);;

let sort3_stable = prove
 (`!R (x:A) y z.
     total R /\ transitive R ==> stable R [x; y; z] (sort3 R x y z)`,
  REWRITE_TAC[stable_def; sort3_def; total_DEF; transitive_DEF] THEN
  REPEAT STRIP_TAC THEN REPEAT COND_CASES_TAC THEN REWRITE_TAC[FILTER] THEN
  MAP_EVERY ASM_CASES_TAC [`(p:A->bool) x`; `(p:A->bool) y`; `(p:A->bool) z`] THEN
  ASM_REWRITE_TAC[CONS_11] THEN ASM_MESON_TAC[]);;

let LSORTAUX_FILTER_NIL = prove
 (`!P (l:A list). (!z. MEM z l ==> ~P z) ==> FILTER P l = []`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[FILTER; MEM] THEN
  STRIP_TAC THEN COND_CASES_TAC THEN ASM_MESON_TAC[]);;

let filter_merge = prove
 (`!P R (l1:A list) l2.
     transitive R /\ (!x y. P x /\ P y ==> R x y) /\ SORTED R l1
     ==> FILTER P (mergesort_merge R l1 l2) = FILTER P (APPEND l1 l2)`,
  GEN_TAC THEN MATCH_MP_TAC mergesort_merge_ind THEN
  REWRITE_TAC[mergesort_merge_def; APPEND; APPEND_NIL] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `SORTED R (l1:A list) /\ (!z. MEM z l1 ==> R x z)`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[SORTED_EQ]; ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[FILTER; FILTER_APPEND] THEN
  ASM_CASES_TAC `(P:A->bool) y` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `(P:A->bool) x` THENL [ASM_MESON_TAC[]; ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `FILTER (P:A->bool) l1 = []` (fun th -> REWRITE_TAC[th; APPEND]) THEN
  MATCH_MP_TAC LSORTAUX_FILTER_NIL THEN
  RULE_ASSUM_TAC(REWRITE_RULE[transitive_DEF]) THEN ASM_MESON_TAC[]);;

let merge_stable = prove
 (`!R (l1:A list) l2.
     transitive R /\ SORTED R l1 ==> stable R (APPEND l1 l2) (mergesort_merge R l1 l2)`,
  REWRITE_TAC[stable_def] THEN REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC filter_merge THEN ASM_REWRITE_TAC[]);;

let mergesortN_stable = prove
 (`!R n (l:A list).
     total R /\ transitive R ==> stable R (TAKE n l) (mergesortN R n l)`,
  MATCH_MP_TAC LSORTAUX_mergesortN_ind THEN
  MAP_EVERY X_GEN_TAC [`R:A->A->bool`; `n:num`; `l:A list`] THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[LSORTAUX_mergesortN_eqn] THEN
  LSORTAUX_MSN_CASES_TAC
   (LSORTAUX_TAKE_TAC THEN
    SIMP_TAC[LSORTAUX_stable_refl; sort2_stable; sort3_stable]) THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`l:A list`; `n:num`; `DIV2 n`] LSORTAUX_take_drop_partition) THEN
  REWRITE_TAC[DIV2_DEF] THEN ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DIV2_DEF]) THEN
  MATCH_MP_TAC stable_trans THEN
  EXISTS_TAC `APPEND (mergesortN R (n DIV 2) (l:A list))
                     (mergesortN R (n - n DIV 2) (DROP (n DIV 2) l))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC stable_cong THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC merge_stable THEN ASM_SIMP_TAC[mergesortN_sorted]]);;

let mergesort_stable = prove
 (`!R (l:A list). transitive R /\ total R ==> stable R l (mergesort R l)`,
  MESON_TAC[mergesortN_stable; mergesort_def; LSORTAUX_TAKE_LENGTH_ID]);;

(* ------------------------------------------------------------------------- *)
(* The tail-recursive version.                                               *)
(* ------------------------------------------------------------------------- *)

let sort2_tail_correct = prove
 (`!neg R (x:A) y.
     sort2_tail neg R x y = if neg then REVERSE (sort2 R x y) else sort2 R x y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sort2_tail_def; sort2_def] THEN
  BOOL_CASES_TAC `neg:bool` THEN ASM_CASES_TAC `(R:A->A->bool) x y` THEN
  ASM_REWRITE_TAC[REVERSE; APPEND]);;

let sort3_tail_correct = prove
 (`!neg R (x:A) y z.
     sort3_tail neg R x y z =
     if neg then REVERSE (sort3 R x y z) else sort3 R x y z`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sort3_tail_def; sort3_def] THEN
  BOOL_CASES_TAC `neg:bool` THEN
  MAP_EVERY ASM_CASES_TAC [`(R:A->A->bool) x y`; `(R:A->A->bool) y z`;
                           `(R:A->A->bool) x z`] THEN
  ASM_REWRITE_TAC[REVERSE; APPEND]);;

let merge_tail_correct1 = prove
 (`!neg R (l1:A list) l2 acc.
     neg = F
     ==> merge_tail neg R l1 l2 acc = APPEND (REVERSE (mergesort_merge R l1 l2)) acc`,
  MATCH_MP_TAC merge_tail_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
   [DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[merge_tail_def; mergesort_merge_def; REVERSE; APPEND];
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[merge_tail_def; mergesort_merge_def; REV_REVERSE_LEM];
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[merge_tail_def; mergesort_merge_def; REV_REVERSE_LEM];
    DISCH_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN POP_ASSUM MP_TAC THEN
    REWRITE_TAC[merge_tail_def; mergesort_merge_def] THEN STRIP_TAC THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[REVERSE; GSYM APPEND_ASSOC; APPEND]]);;

let merge_empty = prove
 (`!R (l:A list) (acc:A list).
     mergesort_merge R l [] = l /\ mergesort_merge R [] l = l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[mergesort_merge_def]);;

let LSORTAUX_merge_sing_left = prove
 (`!R (x:A) l. (!y. MEM y l ==> ~R x y)
               ==> mergesort_merge R [x] l = APPEND l [x]`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[mergesort_merge_def; APPEND; MEM] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]);;

let LSORTAUX_merge_sing_right = prove
 (`!R (y:A) l. (!x. MEM x l ==> R x y)
               ==> mergesort_merge R l [y] = APPEND l [y]`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[mergesort_merge_def; APPEND; MEM] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]);;

let LSORTAUX_merge_last_lem1 = prove
 (`!x:A R (l1:A list) l2.
     (!y. MEM y l2 ==> ~R x y)
     ==> mergesort_merge R (APPEND l1 [x]) l2 =
         APPEND (mergesort_merge R l1 l2) [x]`,
  GEN_TAC THEN MATCH_MP_TAC mergesort_merge_ind THEN REPEAT CONJ_TAC THEN
  REPEAT GEN_TAC THENL
   [REWRITE_TAC[APPEND; mergesort_merge_def];
    REWRITE_TAC[APPEND; mergesort_merge_def; merge_empty];
    DISCH_TAC THEN REWRITE_TAC[APPEND] THEN
    ASM_SIMP_TAC[LSORTAUX_merge_sing_left] THEN REWRITE_TAC[mergesort_merge_def];
    STRIP_TAC THEN DISCH_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[APPEND]) THEN
    REWRITE_TAC[APPEND; mergesort_merge_def] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[APPEND; CONS_11] THEN ASM_MESON_TAC[MEM]]);;

let LSORTAUX_merge_last_lem2 = prove
 (`!y:A R (l1:A list) l2.
     (!x. MEM x l1 ==> R x y)
     ==> mergesort_merge R l1 (APPEND l2 [y]) =
         APPEND (mergesort_merge R l1 l2) [y]`,
  GEN_TAC THEN MATCH_MP_TAC mergesort_merge_ind THEN REPEAT CONJ_TAC THEN
  REPEAT GEN_TAC THENL
   [REWRITE_TAC[APPEND; mergesort_merge_def];
    DISCH_TAC THEN REWRITE_TAC[APPEND] THEN
    ASM_SIMP_TAC[LSORTAUX_merge_sing_right] THEN REWRITE_TAC[mergesort_merge_def];
    REWRITE_TAC[APPEND; mergesort_merge_def; merge_empty];
    STRIP_TAC THEN DISCH_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[APPEND]) THEN
    REWRITE_TAC[APPEND; mergesort_merge_def] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[APPEND; CONS_11] THEN ASM_MESON_TAC[MEM]]);;

let merge_tail_correct2 = prove
 (`!neg R (l1:A list) l2 acc.
     neg = T /\ transitive R /\ SORTED R (REVERSE l1) /\ SORTED R (REVERSE l2)
     ==> merge_tail neg R l1 l2 acc =
         APPEND (mergesort_merge R (REVERSE l1) (REVERSE l2)) acc`,
  MATCH_MP_TAC merge_tail_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
   [STRIP_TAC THEN ASM_REWRITE_TAC[merge_tail_def; mergesort_merge_def; REVERSE; APPEND];
    STRIP_TAC THEN ASM_REWRITE_TAC[merge_tail_def; REV_REVERSE_LEM; merge_empty; REVERSE];
    STRIP_TAC THEN ASM_REWRITE_TAC[merge_tail_def; REV_REVERSE_LEM; merge_empty; REVERSE];
    ALL_TAC] THEN
  DISCH_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_conj o concl)) THEN
  REWRITE_TAC[merge_tail_def; REVERSE] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REVERSE]) THEN
  SUBGOAL_THEN `(!a b c:A. R a b /\ R b c ==> R a c)` ASSUME_TAC THENL
   [ASM_MESON_TAC[transitive_DEF]; ALL_TAC] THEN
  SUBGOAL_THEN `SORTED R (REVERSE (l1:A list)) /\ (!z. MEM z l1 ==> R z (x:A)) /\
                SORTED R (REVERSE (l2:A list)) /\ (!z. MEM z l2 ==> R z (y:A))`
    STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`R:A->A->bool`; `REVERSE (l1:A list)`; `[x:A]`] SORTED_APPEND) THEN
    MP_TAC(ISPECL [`R:A->A->bool`; `REVERSE (l2:A list)`; `[y:A]`] SORTED_APPEND) THEN
    ASM_REWRITE_TAC[MEM; MEM_REVERSE] THEN MESON_TAC[];
    ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[] THENL
   [MP_TAC(ISPECL [`x:A`; `R:A->A->bool`; `REVERSE (l1:A list)`;
                   `APPEND (REVERSE l2) [y:A]`] LSORTAUX_merge_last_lem1);
    MP_TAC(ISPECL [`y:A`; `R:A->A->bool`; `APPEND (REVERSE l1) [x:A]`;
                   `REVERSE (l2:A list)`] LSORTAUX_merge_last_lem2)] THEN
  REWRITE_TAC[MEM_APPEND; MEM; MEM_REVERSE] THEN
  (ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC]) THEN
  REWRITE_TAC[GSYM APPEND_ASSOC; APPEND]);;

let mergesortN_correct = prove
 (`!negate R n (l:A list).
     total R /\ transitive R
     ==> mergesortN_tail negate R n l =
         if negate then REVERSE (mergesortN R n l) else mergesortN R n l`,
  MATCH_MP_TAC LSORTAUX_mergesortN_tail_ind THEN
  MAP_EVERY X_GEN_TAC [`negate:bool`; `R:A->A->bool`; `n:num`; `l:A list`] THEN
  DISCH_TAC THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [LSORTAUX_mergesortN_tail_eqn] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o ONCE_DEPTH_CONV)
    [LSORTAUX_mergesortN_eqn] THEN
  LSORTAUX_MSN_CASES_TAC
   (REWRITE_TAC[sort2_tail_correct; sort3_tail_correct; REVERSE; APPEND;
                COND_ID]) THEN
  STRIP_TAC THEN ASM_SIMP_TAC[] THEN BOOL_CASES_TAC `negate:bool` THEN
  REWRITE_TAC[] THENL
   [SIMP_TAC[merge_tail_correct1; APPEND_NIL];
    ASM_SIMP_TAC[merge_tail_correct2; REVERSE_REVERSE; APPEND_NIL;
                 mergesortN_sorted]]);;

let mergesort_tail_correct = prove
 (`!R (l:A list).
     total R /\ transitive R ==> mergesort_tail R l = mergesort R l`,
  REWRITE_TAC[mergesort_tail_def; mergesort_def] THEN
  SIMP_TAC[mergesortN_correct]);;
