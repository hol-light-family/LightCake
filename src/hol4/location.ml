(* ========================================================================= *)
(* location: port of HOL4 examples/formal-languages/context-free/           *)
(* locationScript.sml (HOL4 library used by CakeML v3479).                   *)
(* Source locations: positions (row, column) with an unknown point and an    *)
(* end-of-file point, and location ranges.                                   *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - HOL4's record-field syntax l.row and l.col is locnrow l and locncol l;  *)
(*   l with row updated_by f is locn_rowupdate f l (likewise for col).       *)
(* - HOL4's local overloads end_locn and unknown_locn are expanded to EOFpt  *)
(*   and UNKNOWNpt.                                                          *)
(* - HOL4's overlapping clauses of merge_list_locs are given in the         *)
(*   disjoint form HOL4 stores (merge_list_locs_def).                       *)
(* - Lemmas named LPARSEAUX_... are helpers of this unit (not HOL4 names).   *)
(* ========================================================================= *)

needs "hol4/vocab.ml";;

(* ------------------------------------------------------------------------- *)
(* Points.                                                                   *)
(* ------------------------------------------------------------------------- *)

let locn_INDUCT,locn_RECURSION = cake_type
  "locn = UNKNOWNpt | EOFpt | POSN num num";;

let locn_distinct = distinctness "locn";;
let locn_inject = injectivity "locn";;
let locn_CASE = case_def "locn";;
let locn_case_eq = case_eq "locn";;
let locn_nchotomy = cases "locn";;

let locnrow_def = cake_def
  `locnrow (POSN r c) = r`;;

let locn_rowupdate_def = cake_def
  `locn_rowupdate f (POSN r c) = POSN (f r) c`;;

let locncol_def = cake_def
  `locncol (POSN r c) = c`;;

let locn_colupdate_def = cake_def
  `locn_colupdate f (POSN r c) = POSN r (f c)`;;

(* ------------------------------------------------------------------------- *)
(* Ranges.                                                                   *)
(* ------------------------------------------------------------------------- *)

let locs_INDUCT,locs_RECURSION = cake_type
  "locs = Locs locn locn";;

let locs_inject = injectivity "locs";;
let locs_CASE = case_def "locs";;
let locs_case_eq = case_eq "locs";;
let locs_nchotomy = cases "locs";;

let default_loc_def = new_definition
  `default_loc = POSN 0 0`;;

let start_locs_def = new_definition
  `start_locs = Locs default_loc default_loc`;;

let unknown_loc_def = new_definition
  `unknown_loc = Locs UNKNOWNpt UNKNOWNpt`;;

(* ------------------------------------------------------------------------- *)
(* The order on points: UNKNOWNpt is minimal, EOFpt maximal, the others are  *)
(* compared lexicographically by row and column.                            *)
(* ------------------------------------------------------------------------- *)

let locnle_def = new_definition
  `locnle l1 l2 <=>
     l1 = l2 \/ l1 = UNKNOWNpt \/ l2 = EOFpt \/
     ~(l2 = UNKNOWNpt) /\ ~(l1 = EOFpt) /\
     (locnrow l1 < locnrow l2 \/
      locnrow l1 = locnrow l2 /\ locncol l1 < locncol l2)`;;

let LPARSEAUX_LOCN_CASES_TAC (tms:term list) =
  MAP_EVERY (fun t -> STRUCT_CASES_TAC (SPEC t locn_nchotomy)) tms THEN
  REWRITE_TAC[locnle_def; locnrow_def; locncol_def; locn_distinct;
              locn_inject];;

let locnle_REFL = prove
 (`!l. locnle l l`,
  REWRITE_TAC[locnle_def]);;

let locnle_total = prove
 (`!l1 l2. locnle l1 l2 \/ locnle l2 l1`,
  REPEAT GEN_TAC THEN LPARSEAUX_LOCN_CASES_TAC [`l1:locn`; `l2:locn`] THEN
  ARITH_TAC);;

let locnle_ANTISYM = prove
 (`!l1 l2. locnle l1 l2 /\ locnle l2 l1 ==> l1 = l2`,
  REPEAT GEN_TAC THEN LPARSEAUX_LOCN_CASES_TAC [`l1:locn`; `l2:locn`] THEN
  ARITH_TAC);;

let locnle_TRANS = prove
 (`!l1 l2 l3. locnle l1 l2 /\ locnle l2 l3 ==> locnle l1 l3`,
  REPEAT GEN_TAC THEN
  LPARSEAUX_LOCN_CASES_TAC [`l1:locn`; `l2:locn`; `l3:locn`] THEN
  ARITH_TAC);;

let locnle_end = prove
 (`!l. locnle EOFpt l <=> l = EOFpt`,
  GEN_TAC THEN LPARSEAUX_LOCN_CASES_TAC [`l:locn`]);;

let locnle_unknown = prove
 (`!l. locnle l UNKNOWNpt <=> l = UNKNOWNpt`,
  GEN_TAC THEN LPARSEAUX_LOCN_CASES_TAC [`l:locn`]);;

(* HOL4: locsle (Locs l1 _) (Locs l2 _) <=> locnle l1 l2 *)

let locsle_def = cake_def
  `locsle (Locs l1 e1) (Locs l2 e2) <=> locnle l1 l2`;;

let LPARSEAUX_LOCS_CASES_TAC (tms:term list) =
  MAP_EVERY (fun t -> STRUCT_CASES_TAC (SPEC t locs_nchotomy)) tms THEN
  REWRITE_TAC[locsle_def];;

let locsle_REFL = prove
 (`!l. locsle l l`,
  GEN_TAC THEN LPARSEAUX_LOCS_CASES_TAC [`l:locs`] THEN
  REWRITE_TAC[locnle_REFL]);;

let locsle_total = prove
 (`!l1 l2. locsle l1 l2 \/ locsle l2 l1`,
  REPEAT GEN_TAC THEN LPARSEAUX_LOCS_CASES_TAC [`l1:locs`; `l2:locs`] THEN
  REWRITE_TAC[locnle_total]);;

let locsle_TRANS = prove
 (`!l1 l2 l3. locsle l1 l2 /\ locsle l2 l3 ==> locsle l1 l3`,
  REPEAT GEN_TAC THEN
  LPARSEAUX_LOCS_CASES_TAC [`l1:locs`; `l2:locs`; `l3:locs`] THEN
  MESON_TAC[locnle_TRANS]);;

(* ------------------------------------------------------------------------- *)
(* Merging ranges.                                                           *)
(* ------------------------------------------------------------------------- *)

let merge_locs_def = cake_def
  `merge_locs (Locs l1 l2) (Locs l3 l4) = Locs l1 l4`;;

let merge_list_locs_def = cake_def_wf `measure (LENGTH:locs list->num)`
  (REWRITE_TAC[measure_THM; LENGTH] THEN ARITH_TAC)
  `(merge_list_locs [] = unknown_loc) /\
   (merge_list_locs [h] = h) /\
   (merge_list_locs [h1; h2] = merge_locs h1 h2) /\
   (merge_list_locs (CONS h1 (CONS h2 (CONS h3 t))) =
      merge_list_locs (CONS h1 (CONS h3 t)))`;;

let merge_list_locs_ind = cake_ind "merge_list_locs";;

(* for debugging *)

let map_loc_def = cake_def
  `(map_loc [] (n:num) = ([]:(A#locs)list)) /\
   (map_loc (CONS (h:A) t) n =
      CONS (h, Locs (POSN 0 n) (POSN 0 n)) (map_loc t (n + 1)))`;;

let merge_locs_assoc = prove
 (`!l1 l2 l3.
     merge_locs (merge_locs l1 l2) l3 = merge_locs l1 l3 /\
     merge_locs l1 (merge_locs l2 l3) = merge_locs l1 l3`,
  REPEAT GEN_TAC THEN
  MAP_EVERY (fun t -> STRUCT_CASES_TAC (SPEC t locs_nchotomy))
    [`l1:locs`; `l2:locs`; `l3:locs`] THEN
  REWRITE_TAC[merge_locs_def]);;

let merge_list_locs_2 = prove
 (`!h1 h2 t.
     merge_list_locs (CONS h1 (CONS h2 t)) =
     merge_list_locs (CONS (merge_locs h1 h2) t)`,
  SUBGOAL_THEN
   `!t h1 h2. merge_list_locs (CONS h1 (CONS h2 t)) =
              merge_list_locs (CONS (merge_locs h1 h2) t)`
   (fun th -> MESON_TAC[th]) THEN
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[merge_list_locs_def; merge_locs_assoc]);;

let merge_list_locs_nested = prove
 (`!h t1 t2.
     merge_list_locs (CONS (merge_list_locs (CONS h t1)) t2) =
     merge_list_locs (CONS h (APPEND t1 t2))`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[merge_list_locs_def; APPEND];
    ASM_REWRITE_TAC[merge_list_locs_2; APPEND]]);;

let merge_list_locs_sing = prove
 (`!h. merge_list_locs [h] = h`,
  REWRITE_TAC[merge_list_locs_def]);;

let merge_locs_idem = prove
 (`!l. merge_locs l l = l`,
  GEN_TAC THEN STRUCT_CASES_TAC (SPEC `l:locs` locs_nchotomy) THEN
  REWRITE_TAC[merge_locs_def]);;

(* ------------------------------------------------------------------------- *)
(* The HOL4 [simp] theorems of this theory, for the project simpset.         *)
(* ------------------------------------------------------------------------- *)

let _ = cake_add_simps
  [locnle_REFL; locnle_end; locnle_unknown; locsle_def; locsle_REFL;
   map_loc_def; merge_locs_assoc; merge_list_locs_2; merge_list_locs_nested;
   merge_list_locs_sing; merge_locs_idem];;
