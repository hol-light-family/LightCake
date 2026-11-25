(* ========================================================================= *)
(* MapProg: port of HOL4 basis/MapProgScript.sml (CakeML v3479).             *)
(* This module contains CakeML code implementing a functional map type      *)
(* using a self-balancing binary tree.                                       *)
(*                                                                           *)
(* The balanced_map functions are hol4/balanced_map.ml's and                 *)
(* hol4/balanced_map_part2.ml's (HOL4 size, delta, lookup, member, empty,    *)
(* insert, delete, glue, union, trim, link, link2, map, filter, fromList,    *)
(* every, exists are balanced_map_size', balanced_map_delta, ...); the       *)
(* mlmap functions are basis/pure/mlmap.ml's (mlmap_lookup, ...).  HOL4's    *)
(* f |+ (k,v) of fmap_update is misc's fmap_update; $\\ is fdomsub.         *)
(* ========================================================================= *)

needs "translator/ml_translator.ml";;
needs "hol4/balanced_map.ml";;
needs "hol4/balanced_map_part2.ml";;
needs "basis/pure/mlmap.ml";;
needs "basis/ArrayProg.ml";;
needs "basis/basisFunctionsLib.ml";;

type_invention_error := true;;

translation_extends "ArrayProg";;

use_full_type_names := false;;
register_type `:(A,B)balanced_map`;;
use_full_type_names := true;;

use_full_type_names := false;;
register_type `:(A,B)map`;;
use_full_type_names := true;;

ml_prog_update ml_prog_open_local_block;;

next_ml_names := ["size"; "singleton"];;
let _ = translate balanced_map_size'_def;;
let _ = translate singleton_def;;

(* Helpers *)
let _ = translate ratio_def;;
let _ = translate balanced_map_delta_def;;
let _ = translate balanceL_def;;
let _ = translate balanceR_def;;
let _ = translate deleteFindMax_def;;

(* HOL4: ho_match_mp_tac deleteFindMax_ind, then the side definition twice *)
let BAS1AUX_DELETEFIND_SIDE_TAC ind side_def =
  MATCH_MP_TAC ind THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[side_def] THEN
  REWRITE_TAC[distinctness "balanced_map"; injectivity "balanced_map"] THEN
  REPEAT STRIP_TAC THEN ASM_MESON_TAC[distinctness "balanced_map"];;

let MapProg_deleteFindmax_side_thm = prove
 (`!m:(K,V)balanced_map. ~(m = Tip) ==> deletefindmax_side m`,
  BAS1AUX_DELETEFIND_SIDE_TAC deleteFindMax_ind (tr_fetch "deletefindmax_side_def"));;
let _ = update_precondition MapProg_deleteFindmax_side_thm;;

let _ = translate deleteFindMin_def;;

let MapProg_deleteFindmin_side_thm = prove
 (`!m:(K,V)balanced_map. ~(m = Tip) ==> deletefindmin_side m`,
  BAS1AUX_DELETEFIND_SIDE_TAC deleteFindMin_ind (tr_fetch "deletefindmin_side_def"));;
let _ = update_precondition MapProg_deleteFindmin_side_thm;;

let _ = translate balanced_map_glue_def;;

let MapProg_glue_side_thm = prove
 (`!(m:(K,V)balanced_map) n. glue_side m n`,
  REWRITE_TAC[tr_fetch "glue_side_def"] THEN
  MESON_TAC[MapProg_deleteFindmin_side_thm; MapProg_deleteFindmax_side_thm;
            distinctness "balanced_map"]);;
let _ = update_precondition MapProg_glue_side_thm;;

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
  ["null"; "member"; "empty"; "insert"; "delete";
   "union"; "unionWithKey"; "unionWith"; "foldrWithKey";
   "toAscList"; "compare"; "mapWithKey"; "map"; "isSubmapOfBy";
   "isSubmapOf"; "fromList"; "filterWithKey"; "filter"; "all";
   "exists"];;
let _ = translate null_def;;
let _ = translate balanced_map_member_def;;
let _ = translate balanced_map_empty_def;;
let _ = translate balanced_map_insert_def;;
let _ = translate balanced_map_delete_def;;
let _ = translate balanced_map_union_def;;
let _ = translate unionWithKey_def;;
let _ = translate unionWith_def;;
let _ = translate foldrWithKey_def;;
let _ = translate toAscList_def;;
let _ = translate compare_def;;
let _ = translate mapWithKey_def;;
let _ = translate balanced_map_map_def;;
let _ = translate isSubmapOfBy_def;;
let _ = translate isSubmapOf_def;;
let _ = translate balanced_map_fromList_def;;
let _ = translate filterWithKey_def;;
let _ = translate balanced_map_filter_def;;
let _ = translate balanced_map_every_def;;
let _ = translate balanced_map_exists_def;;

ml_prog_update ml_prog_open_local_in_block;;

ml_prog_update (ml_prog_open_module "Map");;

(* provides the Map.map name for the map type *)
ml_prog_update (ml_prog_add_dec
  `Dtabbrev unknown_loc [implode "'a"; implode "'b"] (implode "map")
     (Atapp [Atvar (implode "'a"); Atvar (implode "'b")] (Short (implode "map")))` I);;

next_ml_names := ["lookup"];;
let mlmap_lookup_v_thm = translate mlmap_lookup_def;;
next_ml_names := ["member"];;
let _ = translate mlmap_member_def;;
next_ml_names := ["insert"];;
let mlmap_insert_v_thm = translate mlmap_insert_def;;
next_ml_names := ["delete"];;
let mlmap_delete_v_thm = translate mlmap_delete_def;;
next_ml_names := ["null"];;
let _ = translate mlmap_null_def;;
next_ml_names := ["size"];;
let _ = translate mlmap_size_def;;
next_ml_names := ["empty"];;
let _ = translate mlmap_empty_def;;
next_ml_names := ["singleton"];;
let _ = translate mlmap_singleton_def;;
next_ml_names := ["union"];;
let mlmap_union_v_thm = translate mlmap_union_def;;
next_ml_names := ["unionWith"];;
let _ = translate mlmap_unionWith_def;;
next_ml_names := ["unionWithKey"];;
let _ = translate mlmap_unionWithKey_def;;
next_ml_names := ["foldrWithKey"];;
let _ = translate mlmap_foldrWithKey_def;;
next_ml_names := ["map"];;
let _ = translate mlmap_map_def;;
next_ml_names := ["mapWithKey"];;
let _ = translate mlmap_mapWithKey_def;;
next_ml_names := ["toAscList"];;
let _ = translate mlmap_toAscList_def;;
next_ml_names := ["fromList"];;
let _ = translate mlmap_fromList_def;;
next_ml_names := ["isSubmapBy"];;
let _ = translate isSubmapBy_def;;
next_ml_names := ["isSubmap"];;
let _ = translate isSubmap_def;;
next_ml_names := ["all"];;
let _ = translate mlmap_all_def;;
next_ml_names := ["exists"];;
let _ = translate mlmap_exists_def;;
next_ml_names := ["filterWithKey"];;
let _ = translate mlmap_filterWithKey_def;;
next_ml_names := ["filter"];;
let _ = translate mlmap_filter_def;;
next_ml_names := ["compare"];;
let _ = translate mlmap_compare_def;;

ml_prog_update (ml_prog_close_module None);;

(* this is here so that the type name is accessible without the full name *)
ml_prog_update (ml_prog_add_dec
  `Dtabbrev unknown_loc [implode "'a"; implode "'b"] (implode "map")
     (Atapp [Atvar (implode "'a"); Atvar (implode "'b")] (Short (implode "map")))` I);;

ml_prog_update ml_prog_close_local_block;;

(* ----------------------------------------------------------------------- *)
(* general tooling for adding mlmap support for fmaps                       *)
(* ----------------------------------------------------------------------- *)

let MapProg_FMAP_TYPE_def = new_definition
  `MapProg_FMAP_TYPE cmp (a:K->v->bool) (b:V->v->bool) (f:(K,V)fmap) v <=>
     ?m. map_ok m /\ mlmap_to_fmap m = f /\ MAP_TYPE a b m v /\ cmp_of m = cmp`;;

let MAP_TYPE_empty_IMP_FMAP_TYPE = prove
 (`!a b cmp v.
     MAP_TYPE (a:K->v->bool) (b:V->v->bool) (mlmap_empty cmp) v /\ TotOrd cmp
     ==> MapProg_FMAP_TYPE cmp a b FEMPTY v`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MapProg_FMAP_TYPE_def] THEN
  EXISTS_TAC `mlmap_empty cmp:(K,V)map` THEN
  ASM_SIMP_TAC[mlmap_empty_thm; cmp_of_empty]);;

(* HOL4's proofs unfold Arrow and AppReturns and chase the nested results; *)
(* here a refinement lemma for one Arrow at a time: an argument related by *)
(* the new invariant has a counterpart related by the old one, and the     *)
(* results of the two functions are related accordingly                     *)
let BAS1AUX_ARROW_REFINE = prove
 (`!(a:A->v->bool) (a':C->v->bool) (b:B->v->bool) (b':D->v->bool) f g v.
     (!x w. a' x w ==> ?y. a y w /\ (!u. b (f y) u ==> b' (g x) u))
     ==> (a --> b) f v ==> (a' --> b') g v`,
  REWRITE_TAC[ml_Arrow_def; ml_AppReturns_def] THEN CONV_TAC (DEPTH_CONV BETA_CONV) THEN
  MESON_TAC[]);;

(* the first argument: a finite map of an mlmap m *)
let BAS1AUX_FMAP_ARG_TAC =
  MATCH_MP_TAC BAS1AUX_ARROW_REFINE THEN
  MAP_EVERY X_GEN_TAC [`f:(K,V)fmap`; `w:v`] THEN REWRITE_TAC[MapProg_FMAP_TYPE_def] THEN
  DISCH_THEN (X_CHOOSE_THEN `m:(K,V)map` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `m:(K,V)map` THEN ASM_REWRITE_TAC[] THEN GEN_TAC;;

(* a further argument related by the same invariant *)
let BAS1AUX_SAME_ARG_TAC x w =
  MATCH_MP_TAC BAS1AUX_ARROW_REFINE THEN
  X_GEN_TAC x THEN X_GEN_TAC w THEN DISCH_TAC THEN EXISTS_TAC x THEN
  ASM_REWRITE_TAC[] THEN GEN_TAC;;

let IMP_FMAP_TYPE_FLOOKUP = prove
 (`!v cmp b a.
     (MAP_TYPE (b:K->v->bool) (a:V->v->bool) --> b --> OPTION_TYPE a) mlmap_lookup v
     ==> (MapProg_FMAP_TYPE cmp b a --> b --> OPTION_TYPE a) FLOOKUP v`,
  REPEAT GEN_TAC THEN BAS1AUX_FMAP_ARG_TAC THEN BAS1AUX_SAME_ARG_TAC `k:K` `w2:v` THEN
  EXPAND_TAC "f" THEN ASM_SIMP_TAC[mlmap_lookup_thm]);;

let IMP_FMAP_TYPE_FUPDATE = prove
 (`!v cmp b a.
     (MAP_TYPE (b:K->v->bool) (a:V->v->bool) --> b --> a --> MAP_TYPE b a) mlmap_insert v
     ==> (MapProg_FMAP_TYPE cmp b a --> b --> a --> MapProg_FMAP_TYPE cmp b a) fmap_update v`,
  REPEAT GEN_TAC THEN BAS1AUX_FMAP_ARG_TAC THEN BAS1AUX_SAME_ARG_TAC `k:K` `w2:v` THEN
  BAS1AUX_SAME_ARG_TAC `x:V` `w3:v` THEN DISCH_TAC THEN REWRITE_TAC[MapProg_FMAP_TYPE_def] THEN
  EXISTS_TAC `mlmap_insert (m:(K,V)map) (k:K) (x:V)` THEN EXPAND_TAC "f" THEN
  ASM_SIMP_TAC[mlmap_insert_thm; cmp_of_insert; fmap_update_def]);;

let IMP_FMAP_TYPE_DOMSUB = prove
 (`!v cmp b a.
     (MAP_TYPE (b:K->v->bool) (a:V->v->bool) --> b --> MAP_TYPE b a) mlmap_delete v
     ==> (MapProg_FMAP_TYPE cmp b a --> b --> MapProg_FMAP_TYPE cmp b a) fdomsub v`,
  REPEAT GEN_TAC THEN BAS1AUX_FMAP_ARG_TAC THEN BAS1AUX_SAME_ARG_TAC `k:K` `w2:v` THEN
  DISCH_TAC THEN REWRITE_TAC[MapProg_FMAP_TYPE_def] THEN
  EXISTS_TAC `mlmap_delete (m:(K,V)map) (k:K)` THEN EXPAND_TAC "f" THEN
  ASM_SIMP_TAC[mlmap_delete_thm; cmp_of_delete]);;

let IMP_FMAP_TYPE_FUNION = prove
 (`!v cmp b a.
     (MAP_TYPE (b:K->v->bool) (a:V->v->bool) --> MAP_TYPE b a --> MAP_TYPE b a) mlmap_union v
     ==> (MapProg_FMAP_TYPE cmp b a --> MapProg_FMAP_TYPE cmp b a -->
          MapProg_FMAP_TYPE cmp b a) FUNION v`,
  REPEAT GEN_TAC THEN BAS1AUX_FMAP_ARG_TAC THEN
  MATCH_MP_TAC BAS1AUX_ARROW_REFINE THEN
  MAP_EVERY X_GEN_TAC [`f2:(K,V)fmap`; `w2:v`] THEN REWRITE_TAC[MapProg_FMAP_TYPE_def] THEN
  DISCH_THEN (X_CHOOSE_THEN `m2:(K,V)map` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `m2:(K,V)map` THEN ASM_REWRITE_TAC[] THEN GEN_TAC THEN DISCH_TAC THEN
  EXISTS_TAC `mlmap_union (m:(K,V)map) (m2:(K,V)map)` THEN MAP_EVERY EXPAND_TAC ["f"; "f2"] THEN
  MP_TAC (ISPECL [`m:(K,V)map`; `m2:(K,V)map`] mlmap_union_thm) THEN
  ASM_SIMP_TAC[]);;

let IMP_FMAP_TYPE_ops = prove
 (`!key a cmp v v1.
     MAP_TYPE (key:K->v->bool) (a:V->v->bool) (mlmap_empty cmp) v /\ TotOrd cmp
     ==> MapProg_FMAP_TYPE cmp key a FEMPTY v /\
         ((MAP_TYPE key a --> key --> OPTION_TYPE a) mlmap_lookup v1
          ==> (MapProg_FMAP_TYPE cmp key a --> key --> OPTION_TYPE a) FLOOKUP v1) /\
         ((MAP_TYPE key a --> key --> a --> MAP_TYPE key a) mlmap_insert v1
          ==> (MapProg_FMAP_TYPE cmp key a --> key --> a --> MapProg_FMAP_TYPE cmp key a)
              fmap_update v1) /\
         ((MAP_TYPE key a --> key --> MAP_TYPE key a) mlmap_delete v1
          ==> (MapProg_FMAP_TYPE cmp key a --> key --> MapProg_FMAP_TYPE cmp key a)
              fdomsub v1) /\
         ((MAP_TYPE key a --> MAP_TYPE key a --> MAP_TYPE key a) mlmap_union v1
          ==> (MapProg_FMAP_TYPE cmp key a --> MapProg_FMAP_TYPE cmp key a -->
               MapProg_FMAP_TYPE cmp key a) FUNION v1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MAP_TYPE_empty_IMP_FMAP_TYPE THEN ASM_REWRITE_TAC[];
    MATCH_ACCEPT_TAC (SPECL [`v1:v`; `cmp:K->K->ordering`] IMP_FMAP_TYPE_FLOOKUP);
    MATCH_ACCEPT_TAC (SPECL [`v1:v`; `cmp:K->K->ordering`] IMP_FMAP_TYPE_FUPDATE);
    MATCH_ACCEPT_TAC (SPECL [`v1:v`; `cmp:K->K->ordering`] IMP_FMAP_TYPE_DOMSUB);
    MATCH_ACCEPT_TAC (SPECL [`v1:v`; `cmp:K->K->ordering`] IMP_FMAP_TYPE_FUNION)]);;

let mlmap_op_v_thms =
  end_itlist CONJ [mlmap_lookup_v_thm;
             mlmap_union_v_thm;
             mlmap_delete_v_thm;
             mlmap_insert_v_thm];;

finalise_translation ();;
