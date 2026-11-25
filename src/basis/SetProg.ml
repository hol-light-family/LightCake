(* ========================================================================= *)
(* SetProg: port of HOL4 basis/SetProgScript.sml (CakeML v3479).             *)
(* This module contains CakeML code implementing a functional set type      *)
(* using a self-balancing binary tree.                                       *)
(*                                                                           *)
(* The balanced_map functions are translated again (MapProg's are local),   *)
(* as in HOL4; their side conditions are SetProg_deletefindmax_side,         *)
(* SetProg_deletefindmin_side and SetProg_glue_side here (MapProg has the    *)
(* unprefixed names).  The mlset functions are basis/pure/mlset.ml's         *)
(* (mlset_singleton, ...; HOL4 size is mlset_size').  HOL4's last command,  *)
(* the removal of the overloads of mlset, has no counterpart (the port       *)
(* defines no overloads for mlset).                                          *)
(* ========================================================================= *)

needs "basis/MapProg.ml";;
needs "translator/ml_translator.ml";;
needs "hol4/balanced_map.ml";;
needs "hol4/balanced_map_part2.ml";;
needs "basis/pure/mlset.ml";;
needs "basis/basisFunctionsLib.ml";;

type_invention_error := true;;

translation_extends "MapProg";;

ml_prog_update ml_prog_open_local_block;;

use_full_type_names := false;;
register_type `:A mlset`;;
use_full_type_names := true;;

next_ml_names := ["size"; "singleton"];;
let _ = translate balanced_map_size'_def;;
let _ = translate singleton_def;;

(* Helpers *)

let _ = translate FOLDL;;
let _ = translate ratio_def;;
let _ = translate balanced_map_delta_def;;
let _ = translate balanceL_def;;
let _ = translate balanceR_def;;
let _ = translate deleteFindMax_def;;

let SetProg_deleteFindmax_side_thm = prove
 (`!m:(K,V)balanced_map. ~(m = Tip) ==> SetProg_deletefindmax_side m`,
  BAS1AUX_DELETEFIND_SIDE_TAC deleteFindMax_ind (tr_fetch "deletefindmax_side_def"));;
let _ = update_precondition SetProg_deleteFindmax_side_thm;;

let _ = translate deleteFindMin_def;;

let SetProg_deleteFindmin_side_thm = prove
 (`!m:(K,V)balanced_map. ~(m = Tip) ==> SetProg_deletefindmin_side m`,
  BAS1AUX_DELETEFIND_SIDE_TAC deleteFindMin_ind (tr_fetch "deletefindmin_side_def"));;
let _ = update_precondition SetProg_deleteFindmin_side_thm;;

let _ = translate balanced_map_glue_def;;

let SetProg_glue_side_thm = prove
 (`!(m:(K,V)balanced_map) n. SetProg_glue_side m n`,
  REWRITE_TAC[tr_fetch "glue_side_def"] THEN
  MESON_TAC[SetProg_deleteFindmin_side_thm; SetProg_deleteFindmax_side_thm;
            distinctness "balanced_map"]);;
let _ = update_precondition SetProg_glue_side_thm;;

let _ = translate trim_help_greater_def;;
let _ = translate trim_help_lesser_def;;
let _ = translate trim_help_middle_def;;
let _ = translate balanced_map_trim_def;;
let _ = translate insertMin_def;;
let _ = translate insertMax_def;;
let _ = translate bin_def;;
let _ = translate balanced_map_link_def;;
let _ = translate balanced_map_link2_def;;
let _ = translate filterLt_help_def;;
let _ = translate filterLt_def;;
let _ = translate filterGt_help_def;;
let _ = translate filterGt_def;;
let _ = translate insertR_def;;
let _ = translate hedgeUnion_def;;
next_ml_names := ["lookup"];;
let _ = translate balanced_map_lookup_def;;
let _ = translate hedgeUnionWithKey_def;;
let _ = translate splitLookup_def;;
let _ = translate submap'_def;;

(* Exported functions *)
next_ml_names :=
  ["null"; "member"; "empty"; "insert"; "delete"; "union"; "foldrWithKey";
   "toAscList"; "compare"; "isSubmapOfBy"; "isSubmapOf"; "fromList";
   "filterWithKey"; "all"; "exists"];;
let _ = translate null_def;;
let _ = translate balanced_map_member_def;;
let _ = translate balanced_map_empty_def;;
let _ = translate balanced_map_insert_def;;
let _ = translate balanced_map_delete_def;;
let _ = translate balanced_map_union_def;;
let _ = translate foldrWithKey_def;;
let _ = translate toAscList_def;;
let _ = translate compare_def;;
let _ = translate isSubmapOfBy_def;;
let _ = translate isSubmapOf_def;;
let _ = translate balanced_map_fromList_def;;
let _ = translate filterWithKey_def;;
let _ = translate balanced_map_every_def;;
let _ = translate balanced_map_exists_def;;

ml_prog_update ml_prog_open_local_in_block;;

ml_prog_update (ml_prog_open_module "Set");;

(* provides the Set.set name for the set type *)
ml_prog_update (ml_prog_add_dec
  `Dtabbrev unknown_loc [implode "'a"] (implode "set")
     (Atapp [Atvar (implode "'a")] (Short (implode "mlset")))` I);;

next_ml_names := ["singleton"];;
let _ = translate mlset_singleton_def;;
next_ml_names := ["member"];;
let _ = translate mlset_member_def;;
next_ml_names := ["delete"];;
let _ = translate mlset_delete_def;;
next_ml_names := ["union"];;
let _ = translate mlset_union_def;;
next_ml_names := ["isSubset"];;
let _ = translate mlset_isSubset_def;;
next_ml_names := ["compare"];;
let _ = translate mlset_compare_def;;
next_ml_names := ["all"];;
let _ = translate mlset_all_def;;
next_ml_names := ["exists"];;
let _ = translate mlset_exists_def;;
next_ml_names := ["translate"];;
let _ = translate mlset_translate_def;;
next_ml_names := ["map"];;
let _ = translate mlset_map_def;;
next_ml_names := ["filter"];;
let _ = translate mlset_filter_def;;
next_ml_names := ["fromList"];;
let _ = translate mlset_fromList_def;;
next_ml_names := ["toList"];;
let _ = translate mlset_toList_def;;
next_ml_names := ["null"];;
let _ = translate mlset_null_def;;
next_ml_names := ["size"];;
let _ = translate mlset_size'_def;;
next_ml_names := ["fold"];;
let _ = translate mlset_fold_def;;
next_ml_names := ["empty"];;
let _ = translate mlset_empty_def;;
next_ml_names := ["insert"];;
let _ = translate mlset_insert_def;;

ml_prog_update (ml_prog_close_module None);;

ml_prog_update (ml_prog_add_dec
  `Dtabbrev unknown_loc [implode "'a"] (implode "set")
     (Atapp [Atvar (implode "'a")] (Short (implode "mlset")))` I);;

ml_prog_update ml_prog_close_local_block;;

finalise_translation ();;
