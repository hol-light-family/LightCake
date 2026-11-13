(* ========================================================================= *)
(* mlvector: port of HOL4 basis/pure/mlvectorScript.sml (CakeML v3479).      *)
(* Pure functions for the Vector module.                                     *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - The type A vector, Vector, sub, length and fromList come from           *)
(*   hol4/regexp_compiler.ml (HOL4 fromList is regexp_compiler_fromList).    *)
(* - Names (notes/naming/names.tsv): HOL4 tabulate, concat, mapi,            *)
(*   foldli_aux, foldli, foldl, exists, collate_aux and collate are          *)
(*   mlvector_tabulate, mlvector_concat, ...  Not in the table: HOL4 toList, *)
(*   map and findi are mlvector_toList, mlvector_map and mlvector_findi      *)
(*   (hol4/sptree.ml has the constants toList and map, hol4/list.ml has      *)
(*   findi), HOL4 all is mlvector_all (all is a variable of later files,     *)
(*   docs/CONVENTIONS.md section 3), with the theorems mlvector_toList_def,  *)
(*   mlvector_map_def, mlvector_findi_def and mlvector_all_def; HOL4         *)
(*   exists_thm is mlvector_exists_thm (hol4/llist.ml binds exists_thm).     *)
(* - HOL4 GENLIST f n is list_of_seq f n, EVERY is ALL, EXISTS is EX,        *)
(*   FOLDR f e l is ITLIST f l e, Less/Equal/Greater are LESS/EQUAL/GREATER; *)
(*   the free variables of a HOL4 statement are universally quantified.      *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "basis/pure/mllist.ml";;
needs "hol4/regexp_compiler.ml";;

type_invention_error := true;;

(* HOL4 re-exports three theorems of regexp_compiler under the same names: *)
(* vector_nchotomy, sub_def and length_def are those of                    *)
(* hol4/regexp_compiler.ml                                                 *)

let vector_nchotomy = vector_nchotomy;;

let sub_def = sub_def;;

(* same as sub_def, but translator targets Vsub_unsafe *)

let sub_unsafe_def = cake_def
  `sub_unsafe (Vector (l:A list)) n = EL n l`;;

let length_def = length_def;;

let mlvector_tabulate_def = cake_def
  `mlvector_tabulate n (f:num->A) = Vector (list_of_seq f n)`;;

let toList_aux_def = cake_def_wf
  `measure (\p:A vector#num. length (FST p) - SND p)`
  (REWRITE_TAC[measure_THM] THEN ARITH_TAC)
  `toList_aux (vec:A vector) n =
     if length vec <= n then []
     else CONS (sub vec n) (toList_aux vec (n + 1))`;;

let toList_aux_ind = cake_ind "toList_aux";;

(* HOL4: toList_def *)

let mlvector_toList_def = cake_def
  `mlvector_toList (vec:A vector) = toList_aux vec 0`;;

let toList_aux_thm = prove
 (CASE_TERM `!(vec:A vector) n. toList_aux vec n = match vec with Vector vs -> DROP n vs`,
  MATCH_MP_TAC toList_aux_ind THEN RW[] THEN
  ONCE_REWRITE_TAC[toList_aux_def] THEN
  COND_CASES_TAC THENL
   [CASES_ON `vec:A vector` THEN FS[length_def; DROP_LENGTH_TOO_LONG];
    FS[] THEN CASES_ON `vec:A vector` THEN
    FS[sub_def; length_def; NOT_LE; DROP_EL_CONS]]);;

let toList_thm = prove
 (`!ls:A list. mlvector_toList (Vector ls) = ls`,
  RW[mlvector_toList_def; toList_aux_thm; DROP_0]);;

let length_toList = prove
 (`!vec:A vector. LENGTH (mlvector_toList vec) = length vec`,
  GEN_TAC THEN CASES_ON `vec:A vector` THEN RW[length_def; toList_thm]);;

let toList_11 = prove
 (`!l l':A vector. (mlvector_toList l = mlvector_toList l') <=> (l = l')`,
  REPEAT GEN_TAC THEN CASES_ON `l:A vector` THEN CASES_ON `l':A vector` THEN
  FS[toList_thm]);;
let _ = cake_add_simps [toList_11];;

let EL_toList = prove
 (`!n (l:A vector). EL n (mlvector_toList l) = sub l n`,
  REPEAT GEN_TAC THEN CASES_ON `l:A vector` THEN FS[sub_def; toList_thm]);;

let toList_fromList = prove
 (`(!l:A list. mlvector_toList (regexp_compiler_fromList l) = l) /\
   (!v:A vector. regexp_compiler_fromList (mlvector_toList v) = v)`,
  CONJ_TAC THEN GEN_TAC THENL
   [ALL_TAC; CASES_ON `v:A vector`] THEN
  FS[toList_thm; regexp_compiler_fromList_def]);;
let _ = cake_add_simps [toList_fromList];;

let update_def = cake_def
  `update (vec:A vector) i x = Vector (LUPDATE x i (mlvector_toList vec))`;;

let update_thm = prove
 (`!(vec:A vector) i x.
     sub (update vec i x) i = if i < length vec then x else sub vec i`,
  GEN_TAC THEN CASES_ON `vec:A vector` THEN
  RW[update_def; toList_thm; EL_LUPDATE; length_def; sub_def]);;

let mlvector_concat_def = cake_def
  `mlvector_concat (l:(A vector) list) = Vector (FLAT (MAP mlvector_toList l))`;;

(* HOL4: map_def *)

let mlvector_map_def = cake_def
  `mlvector_map (vec:A vector) (f:A->B) = Vector (MAP f (mlvector_toList vec))`;;

let mlvector_mapi_def = cake_def
  `mlvector_mapi (vec:A vector) (f:num->A->B) =
     Vector (MAPi f (mlvector_toList vec))`;;

let less_than_length_thm = prove
 (`!(xs:A list) n.
     n < LENGTH xs ==> ?ys z zs. xs = APPEND ys (CONS z zs) /\ LENGTH ys = n`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `TAKE n (xs:A list)` THEN
  ASM_SIMP_TAC[LENGTH_TAKE; LT_IMP_LE] THEN
  EXISTS_TAC `HD (DROP n (xs:A list))` THEN
  EXISTS_TAC `TL (DROP n (xs:A list))` THEN
  CASES_ON `DROP n (xs:A list)` THENL
   [FIRST_X_ASSUM(MP_TAC o AP_TERM `LENGTH:A list->num`) THEN
    REWRITE_TAC[LENGTH_DROP; LENGTH] THEN ASM_ARITH_TAC;
    REWRITE_TAC[HD; TL] THEN ASM_MESON_TAC[TAKE_DROP]]);;

let mlvector_foldli_aux_def = cake_def
  `(mlvector_foldli_aux (f:num->A->B->B) e (vec:A vector) n 0 = e) /\
   (mlvector_foldli_aux f e vec n (SUC len) =
      mlvector_foldli_aux f (f n (sub vec n) e) vec (n + 1) len)`;;

let mlvector_foldli_def = cake_def
  `mlvector_foldli (f:num->A->B->B) e (vec:A vector) =
     mlvector_foldli_aux f e vec 0 (length vec)`;;

let mlvector_foldli_aux_thm = prove
 (`!(f:num->A->B->B) e (vec:A vector) n len.
     n + len = length vec ==>
     mlvector_foldli_aux f e vec n len =
     mllist_foldli_aux f e n (DROP n (mlvector_toList vec))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM length_toList] THEN
  MAP_EVERY (fun t -> SPEC_TAC(t,t)) [`e:B`; `n:num`; `len:num`] THEN
  INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[mlvector_foldli_aux_def; GSYM EL_toList] THEN DISCH_TAC THENL
   [SUBGOAL_THEN `DROP n (mlvector_toList (vec:A vector)) = []` SUBST1_TAC THENL
     [MATCH_MP_TAC DROP_LENGTH_TOO_LONG THEN ASM_ARITH_TAC;
      REWRITE_TAC[mllist_foldli_aux_def]];
    SUBGOAL_THEN `n < LENGTH (mlvector_toList (vec:A vector)) /\
                  (n + 1) + len = LENGTH (mlvector_toList vec)`
     STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[DROP_EL_CONS; mllist_foldli_aux_def; ADD1]]);;

let mlvector_foldli_thm = prove
 (`!(f:num->A->B->B) e (vec:A vector).
     mlvector_foldli f e vec = mllist_foldli f e (mlvector_toList vec)`,
  SIMP_TAC[mlvector_foldli_def; mllist_foldli_def; mlvector_foldli_aux_thm;
           ADD_CLAUSES; DROP_0]);;

let foldl_aux_def = cake_def
  `(foldl_aux (f:B->A->B) e (vec:A vector) n 0 = e) /\
   (foldl_aux f e vec n (SUC len) = foldl_aux f (f e (sub vec n)) vec (n + 1) len)`;;

let mlvector_foldl_def = cake_def
  `mlvector_foldl (f:B->A->B) e (vec:A vector) = foldl_aux f e vec 0 (length vec)`;;

let foldl_aux_thm = prove
 (`!(f:B->A->B) e (vec:A vector) x len.
     x + len = length vec ==>
     foldl_aux f e vec x len = FOLDL f e (DROP x (mlvector_toList vec))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM length_toList] THEN
  MAP_EVERY (fun t -> SPEC_TAC(t,t)) [`e:B`; `x:num`; `len:num`] THEN
  INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[foldl_aux_def; GSYM EL_toList] THEN DISCH_TAC THENL
   [SUBGOAL_THEN `DROP x (mlvector_toList (vec:A vector)) = []` SUBST1_TAC THENL
     [MATCH_MP_TAC DROP_LENGTH_TOO_LONG THEN ASM_ARITH_TAC;
      REWRITE_TAC[FOLDL]];
    SUBGOAL_THEN `x < LENGTH (mlvector_toList (vec:A vector)) /\
                  (x + 1) + len = LENGTH (mlvector_toList vec)`
     STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[DROP_EL_CONS; FOLDL]]);;

let foldl_thm = prove
 (`!(f:B->A->B) e (vec:A vector).
     mlvector_foldl f e vec = FOLDL f e (mlvector_toList vec)`,
  SIMP_TAC[foldl_aux_thm; mlvector_foldl_def; ADD_CLAUSES; DROP_0]);;

let foldri_aux_def = cake_def
  `(foldri_aux (f:num->A->B->B) e (vec:A vector) 0 = e) /\
   (foldri_aux f e vec (SUC len) = foldri_aux f (f len (sub vec len) e) vec len)`;;

let foldri_def = cake_def
  `foldri (f:num->A->B->B) e (vec:A vector) = foldri_aux f e vec (length vec)`;;

let foldri_aux_thm = prove
 (`!(f:num->A->B->B) e (vec:A vector) len.
     len <= length vec ==>
     foldri_aux f e vec len = FOLDRi f e (TAKE len (mlvector_toList vec))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM length_toList] THEN
  MAP_EVERY (fun t -> SPEC_TAC(t,t)) [`e:B`; `len:num`] THEN
  INDUCT_TAC THEN REWRITE_TAC[foldri_aux_def; TAKE_0; FOLDRi_def] THEN
  REWRITE_TAC[GSYM EL_toList] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `len < LENGTH (mlvector_toList (vec:A vector)) /\
                len <= LENGTH (mlvector_toList vec)`
   STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[ADD1; TAKE_SUM; TAKE1_DROP; FOLDRi_APPEND; LENGTH_TAKE;
               FOLDRi_def; o_THM; ADD_CLAUSES]);;

let foldri_thm = prove
 (`!(f:num->A->B->B) e (vec:A vector).
     foldri f e vec = FOLDRi f e (mlvector_toList vec)`,
  SIMP_TAC[foldri_def; foldri_aux_thm; GSYM length_toList; LE_REFL;
           TAKE_LENGTH_ID]);;

let foldr_aux_def = cake_def
  `(foldr_aux (f:A->B->B) e (vec:A vector) 0 = e) /\
   (foldr_aux f e vec (SUC len) = foldr_aux f (f (sub vec len) e) vec len)`;;

let foldr_def = cake_def
  `foldr (f:A->B->B) e (vec:A vector) = foldr_aux f e vec (length vec)`;;

let foldr_aux_thm = prove
 (`!(f:A->B->B) e (vec:A vector) len.
     len <= length vec ==>
     foldr_aux f e vec len = ITLIST f (TAKE len (mlvector_toList vec)) e`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM length_toList] THEN
  MAP_EVERY (fun t -> SPEC_TAC(t,t)) [`e:B`; `len:num`] THEN
  INDUCT_TAC THEN REWRITE_TAC[foldr_aux_def; TAKE_0; ITLIST] THEN
  REWRITE_TAC[GSYM EL_toList] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `len < LENGTH (mlvector_toList (vec:A vector)) /\
                len <= LENGTH (mlvector_toList vec)`
   STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[ADD1; TAKE_SUM; TAKE1_DROP; ITLIST_APPEND; ITLIST]);;

let foldr_thm = prove
 (`!(f:A->B->B) e (vec:A vector).
     foldr f e vec = ITLIST f (mlvector_toList vec) e`,
  SIMP_TAC[foldr_def; foldr_aux_thm; GSYM length_toList; LE_REFL;
           TAKE_LENGTH_ID]);;

let findi_aux_def = cake_def
  `(findi_aux (f:num->A->bool) (vec:A vector) n 0 = NONE) /\
   (findi_aux f vec n (SUC len) =
      if f n (sub vec n) then SOME (n, sub vec n)
      else findi_aux f vec (n + 1) len)`;;

(* HOL4: findi_def *)

let mlvector_findi_def = cake_def
  `mlvector_findi (f:num->A->bool) (vec:A vector) =
     findi_aux f vec 0 (length vec)`;;

let find_aux_def = cake_def
  `(find_aux (f:A->bool) (vec:A vector) n 0 = NONE) /\
   (find_aux f vec n (SUC len) =
      if f (sub vec n) then SOME (sub vec n)
      else find_aux f vec (n + 1) len)`;;

let find_def = cake_def
  `find (f:A->bool) (vec:A vector) = find_aux f vec 0 (length vec)`;;

let find_aux_thm = prove
 (`!(f:A->bool) (vec:A vector) n len.
     n + len = length vec ==>
     find_aux f vec n len = FIND f (DROP n (mlvector_toList vec))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM length_toList] THEN
  MAP_EVERY (fun t -> SPEC_TAC(t,t)) [`n:num`; `len:num`] THEN
  INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[find_aux_def; GSYM EL_toList] THEN DISCH_TAC THENL
   [SUBGOAL_THEN `DROP n (mlvector_toList (vec:A vector)) = []` SUBST1_TAC THENL
     [MATCH_MP_TAC DROP_LENGTH_TOO_LONG THEN ASM_ARITH_TAC;
      REWRITE_TAC[FIND_thm]];
    SUBGOAL_THEN `n < LENGTH (mlvector_toList (vec:A vector)) /\
                  (n + 1) + len = LENGTH (mlvector_toList vec)`
     STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[DROP_EL_CONS; FIND_thm]]);;

let find_thm = prove
 (`!(f:A->bool) (vec:A vector). find f vec = FIND f (mlvector_toList vec)`,
  SIMP_TAC[find_aux_thm; find_def; ADD_CLAUSES; DROP_0]);;

let exists_aux_def = cake_def
  `(exists_aux (f:A->bool) (vec:A vector) n 0 <=> F) /\
   (exists_aux f vec n (SUC len) <=>
      if f (sub vec n) then T else exists_aux f vec (n + 1) len)`;;

(* HOL4: exists_def *)

let mlvector_exists_def = cake_def
  `mlvector_exists (f:A->bool) (vec:A vector) <=>
     exists_aux f vec 0 (length vec)`;;

let exists_aux_thm = prove
 (`!(f:A->bool) (vec:A vector) n len.
     n + len = length vec ==>
     (exists_aux f vec n len <=> EX f (DROP n (mlvector_toList vec)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM length_toList] THEN
  MAP_EVERY (fun t -> SPEC_TAC(t,t)) [`n:num`; `len:num`] THEN
  INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[exists_aux_def; GSYM EL_toList] THEN DISCH_TAC THENL
   [SUBGOAL_THEN `DROP n (mlvector_toList (vec:A vector)) = []` SUBST1_TAC THENL
     [MATCH_MP_TAC DROP_LENGTH_TOO_LONG THEN ASM_ARITH_TAC;
      REWRITE_TAC[EX]];
    SUBGOAL_THEN `n < LENGTH (mlvector_toList (vec:A vector)) /\
                  (n + 1) + len = LENGTH (mlvector_toList vec)`
     STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[DROP_EL_CONS; EX] THEN MESON_TAC[]]);;

(* HOL4: exists_thm *)

let mlvector_exists_thm = prove
 (`!(f:A->bool) (vec:A vector).
     mlvector_exists f vec <=> EX f (mlvector_toList vec)`,
  REPEAT GEN_TAC THEN CASES_ON `vec:A vector` THEN
  SIMP_TAC[mlvector_exists_def; exists_aux_thm; ADD_CLAUSES; DROP_0]);;

let all_aux_def = cake_def
  `(all_aux (f:A->bool) (vec:A vector) n 0 <=> T) /\
   (all_aux f vec n (SUC len) <=>
      if f (sub vec n) then all_aux f vec (n + 1) len else F)`;;

(* HOL4: all_def *)

let mlvector_all_def = cake_def
  `mlvector_all (f:A->bool) (vec:A vector) <=> all_aux f vec 0 (length vec)`;;

let all_aux_thm = prove
 (`!(f:A->bool) (vec:A vector) n len.
     n + len = length vec ==>
     (all_aux f vec n len <=> ALL f (DROP n (mlvector_toList vec)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM length_toList] THEN
  MAP_EVERY (fun t -> SPEC_TAC(t,t)) [`n:num`; `len:num`] THEN
  INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[all_aux_def; GSYM EL_toList] THEN DISCH_TAC THENL
   [SUBGOAL_THEN `DROP n (mlvector_toList (vec:A vector)) = []` SUBST1_TAC THENL
     [MATCH_MP_TAC DROP_LENGTH_TOO_LONG THEN ASM_ARITH_TAC;
      REWRITE_TAC[ALL]];
    SUBGOAL_THEN `n < LENGTH (mlvector_toList (vec:A vector)) /\
                  (n + 1) + len = LENGTH (mlvector_toList vec)`
     STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[DROP_EL_CONS; ALL] THEN MESON_TAC[]]);;

let all_thm = prove
 (`!(f:A->bool) (vec:A vector).
     mlvector_all f vec <=> ALL f (mlvector_toList vec)`,
  REPEAT GEN_TAC THEN CASES_ON `vec:A vector` THEN
  SIMP_TAC[mlvector_all_def; all_aux_thm; ADD_CLAUSES; DROP_0]);;

let mlvector_collate_aux_def = cake_def
  `(mlvector_collate_aux (f:A->B->ordering) (vec1:A vector) (vec2:B vector) n
      ord 0 = ord) /\
   (mlvector_collate_aux f vec1 vec2 n ord (SUC len) =
      if f (sub vec1 n) (sub vec2 n) = EQUAL
      then mlvector_collate_aux f vec1 vec2 (n + 1) ord len
      else f (sub vec1 n) (sub vec2 n))`;;

let mlvector_collate_def = cake_def
  `mlvector_collate (f:A->B->ordering) (vec1:A vector) (vec2:B vector) =
     if length vec1 < length vec2
     then mlvector_collate_aux f vec1 vec2 0 LESS (length vec1)
     else if length vec2 < length vec1
     then mlvector_collate_aux f vec1 vec2 0 GREATER (length vec2)
     else mlvector_collate_aux f vec1 vec2 0 EQUAL (length vec2)`;;

let mlvector_collate_aux_less_thm = prove
 (`!(f:A->B->ordering) (vec1:A vector) (vec2:B vector) n len.
     n + len = length vec1 /\ length vec1 < length vec2 ==>
     mlvector_collate_aux f vec1 vec2 n LESS len =
     mllist_collate f (DROP n (mlvector_toList vec1))
                      (DROP n (mlvector_toList vec2))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM length_toList] THEN
  MAP_EVERY (fun t -> SPEC_TAC(t,t)) [`n:num`; `len:num`] THEN
  INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[mlvector_collate_aux_def; GSYM EL_toList] THEN STRIP_TAC THENL
   [SUBGOAL_THEN `DROP n (mlvector_toList (vec1:A vector)) = [] /\
                  n < LENGTH (mlvector_toList (vec2:B vector))`
     STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [MATCH_MP_TAC DROP_LENGTH_TOO_LONG; ALL_TAC] THEN
      ASM_ARITH_TAC;
      ASM_SIMP_TAC[DROP_EL_CONS; mllist_collate_def]];
    SUBGOAL_THEN `n < LENGTH (mlvector_toList (vec1:A vector)) /\
                  n < LENGTH (mlvector_toList (vec2:B vector)) /\
                  (n + 1) + len = LENGTH (mlvector_toList vec1)`
     STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[DROP_EL_CONS; mllist_collate_def]]);;

let mlvector_collate_aux_equal_thm = prove
 (`!(f:A->B->ordering) (vec1:A vector) (vec2:B vector) n len.
     n + len = length vec2 /\ length vec1 = length vec2 ==>
     mlvector_collate_aux f vec1 vec2 n EQUAL len =
     mllist_collate f (DROP n (mlvector_toList vec1))
                      (DROP n (mlvector_toList vec2))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM length_toList] THEN
  MAP_EVERY (fun t -> SPEC_TAC(t,t)) [`n:num`; `len:num`] THEN
  INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[mlvector_collate_aux_def; GSYM EL_toList] THEN STRIP_TAC THENL
   [SUBGOAL_THEN `DROP n (mlvector_toList (vec1:A vector)) = [] /\
                  DROP n (mlvector_toList (vec2:B vector)) = []`
     STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC DROP_LENGTH_TOO_LONG THEN ASM_ARITH_TAC;
      ASM_SIMP_TAC[mllist_collate_def]];
    SUBGOAL_THEN `n < LENGTH (mlvector_toList (vec1:A vector)) /\
                  n < LENGTH (mlvector_toList (vec2:B vector)) /\
                  (n + 1) + len = LENGTH (mlvector_toList vec2)`
     STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[DROP_EL_CONS; mllist_collate_def]]);;

let mlvector_collate_aux_greater_thm = prove
 (`!(f:A->B->ordering) (vec1:A vector) (vec2:B vector) n len.
     n + len = length vec2 /\ length vec2 < length vec1 ==>
     mlvector_collate_aux f vec1 vec2 n GREATER len =
     mllist_collate f (DROP n (mlvector_toList vec1))
                      (DROP n (mlvector_toList vec2))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM length_toList] THEN
  MAP_EVERY (fun t -> SPEC_TAC(t,t)) [`n:num`; `len:num`] THEN
  INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[mlvector_collate_aux_def; GSYM EL_toList] THEN STRIP_TAC THENL
   [SUBGOAL_THEN `DROP n (mlvector_toList (vec2:B vector)) = [] /\
                  n < LENGTH (mlvector_toList (vec1:A vector))`
     STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [MATCH_MP_TAC DROP_LENGTH_TOO_LONG; ALL_TAC] THEN
      ASM_ARITH_TAC;
      ASM_SIMP_TAC[DROP_EL_CONS; mllist_collate_def]];
    SUBGOAL_THEN `n < LENGTH (mlvector_toList (vec1:A vector)) /\
                  n < LENGTH (mlvector_toList (vec2:B vector)) /\
                  (n + 1) + len = LENGTH (mlvector_toList vec2)`
     STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[DROP_EL_CONS; mllist_collate_def]]);;

let mlvector_collate_thm = prove
 (`!(f:A->B->ordering) (vec1:A vector) (vec2:B vector).
     mlvector_collate f vec1 vec2 =
     mllist_collate f (mlvector_toList vec1) (mlvector_toList vec2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mlvector_collate_def] THEN
  REPEAT COND_CASES_TAC THEN
  TRY (SUBGOAL_THEN `length (vec1:A vector) = length (vec2:B vector)`
         ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
  ASM_SIMP_TAC[mlvector_collate_aux_greater_thm; mlvector_collate_aux_equal_thm;
               mlvector_collate_aux_less_thm; ADD_CLAUSES; DROP_0]);;
