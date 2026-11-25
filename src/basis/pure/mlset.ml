(* ========================================================================= *)
(* mlset: port of HOL4 basis/pure/mlsetScript.sml (CakeML v3479).            *)
(* Pure functions for the Set module.  This file defines a wrapper around    *)
(* the balanced_map type.                                                    *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - The type is A mlset with the constructor mlset_Set (HOL4 'a mlset and   *)
(*   Set); HOL4 unit is HOL Light 1 and () is one.                           *)
(* - Names (doc/names.tsv): empty, singleton, member, insert,                *)
(*   delete, union, isSubset, compare, all, exists, translate, map, filter,  *)
(*   fromList, null, toList and fold are mlset_empty, ...; HOL4 size is      *)
(*   mlset_size' (cake_type makes mlset_size the size function of the type,  *)
(*   as HOL4's Datatype does).                                               *)
(* - The balanced_map functions are those of hol4/balanced_map.ml and        *)
(*   hol4/balanced_map_part2.ml: HOL4 empty, member, insert, delete, union,  *)
(*   every, exists and size are balanced_map_empty, balanced_map_member,     *)
(*   balanced_map_insert, balanced_map_delete, balanced_map_union,           *)
(*   balanced_map_every, balanced_map_exists and balanced_map_size';         *)
(*   singleton, isSubmapOf, compare, foldrWithKey, filterWithKey and null    *)
(*   keep their names.  Less/Equal/Greater are LESS/EQUAL/GREATER.           *)
(* - HOL4 lambda \k (). f k binds a variable named () of type unit; it is    *)
(*   written \k (u:1). f k (the same term up to the bound name).             *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "hol4/balanced_map.ml";;
needs "hol4/balanced_map_part2.ml";;

type_invention_error := true;;

(* The type :set would collide with :pred_set$set *)

let mlset_INDUCT,mlset_RECURSION = cake_type
  "mlset = mlset_Set (A->A->ordering) ((A,1)balanced_map)";;

let mlset_empty_def = cake_def
  `mlset_empty cmp = mlset_Set cmp (balanced_map_empty:(A,1)balanced_map)`;;

let mlset_singleton_def = cake_def
  `mlset_singleton cmp (x:A) = mlset_Set cmp (singleton x one)`;;

let mlset_member_def = cake_def
  `mlset_member (x:A) (mlset_Set cmp s) <=> balanced_map_member cmp x s`;;

let mlset_insert_def = cake_def
  `mlset_insert (x:A) (mlset_Set cmp s) =
     mlset_Set cmp (balanced_map_insert cmp x one s)`;;

let mlset_delete_def = cake_def
  `mlset_delete (x:A) (mlset_Set cmp s) =
     mlset_Set cmp (balanced_map_delete cmp x s)`;;

let mlset_union_def = cake_def
  `mlset_union (mlset_Set cmp s:A mlset) (mlset_Set _ t) =
     mlset_Set cmp (balanced_map_union cmp s t)`;;

let mlset_isSubset_def = cake_def
  `mlset_isSubset (mlset_Set cmp s:A mlset) (mlset_Set _ t) <=>
     isSubmapOf cmp s t`;;

let mlset_compare_def = cake_def
  `mlset_compare (mlset_Set cmp s:A mlset) (mlset_Set _ t) =
     compare cmp (\x y. EQUAL) s t`;;

let mlset_all_def = cake_def
  `mlset_all f (mlset_Set cmp s:A mlset) <=>
     balanced_map_every (\k (v:1). f k) s`;;

let mlset_exists_def = cake_def
  `mlset_exists f (mlset_Set cmp s:A mlset) <=>
     balanced_map_exists (\k (v:1). f k) s`;;

let mlset_translate_def = cake_def
  `mlset_translate (f:A->B) cmp (mlset_Set _ s) =
     mlset_Set cmp (foldrWithKey
                      (\k (v:1) t. balanced_map_insert cmp (f k) one t)
                      balanced_map_empty s)`;;

let mlset_map_def = cake_def
  `mlset_map (f:A->A) (mlset_Set cmp s) =
     mlset_translate f cmp (mlset_Set cmp s)`;;

let mlset_filter_def = cake_def
  `mlset_filter f (mlset_Set cmp s:A mlset) =
     mlset_Set cmp (filterWithKey (\k (u:1). f k) s)`;;

let mlset_fromList_def = cake_def
  `mlset_fromList cmp (xs:A list) =
     mlset_Set cmp (FOLDL (\t k. balanced_map_insert cmp k one t)
                          balanced_map_empty xs)`;;

let mlset_null_def = cake_def
  `mlset_null (mlset_Set cmp s:A mlset) <=> null s`;;

(* HOL4 size: mlset_size' (names.tsv says mlset_size, but cake_type has     *)
(* made mlset_size the size function of the type, which is HOL4's           *)
(* mlset_size too; as balanced_map_size' in hol4/balanced_map.ml)           *)

let mlset_size'_def = cake_def
  `mlset_size' (mlset_Set cmp s:A mlset) = balanced_map_size' s`;;

let mlset_toList_def = cake_def
  `mlset_toList (mlset_Set cmp s:A mlset) =
     foldrWithKey (\k (v:1) xs. CONS k xs) [] s`;;

let mlset_fold_def = cake_def
  `mlset_fold (f:A->B->B) e (mlset_Set cmp s) =
     foldrWithKey (\k (v:1) t. f k t) e s`;;
