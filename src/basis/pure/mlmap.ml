(* ========================================================================= *)
(* mlmap: port of HOL4 basis/pure/mlmapScript.sml (CakeML v3479).            *)
(* Pure functions for the Map module: a wrapper around the balanced_map      *)
(* type, essentially a pair that carries the compare function next to the   *)
(* tree, so that users need not give it as an argument everywhere.          *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - The type is (K,V)map with the constructor Map (HOL4 ('a,'b) map).       *)
(* - Names as doc/names.tsv says: lookup, insert, delete, null,              *)
(*   size, empty, union, unionWith, unionWithKey, foldrWithKey, filter,      *)
(*   filterWithKey, map, mapWithKey, toAscList, fromList, all, exists,       *)
(*   member, singleton, compare and to_fmap are mlmap_lookup, ...; the       *)
(*   theorems lookup_insert, lookup_delete, empty_thm, size_thm, insert_thm, *)
(*   delete_thm, union_thm, unionWithKey_thm, all_thm, exists_thm,           *)
(*   filterWithKey_thm, lookup_thm, MAP_FST_toAscList, MEM_toAscList are     *)
(*   mlmap_lookup_insert, ...  The balanced_map functions are those of       *)
(*   hol4/balanced_map.ml and hol4/balanced_map_part2.ml (HOL4 lookup,      *)
(*   insert, delete, union, filter, map, fromList, every, exists, size,      *)
(*   empty, invariant are balanced_map_lookup, ..., balanced_map_size',      *)
(*   balanced_map_empty, balanced_map_invariant).                            *)
(* - HOL4's ordering constructors Less, Equal, Greater are LESS, EQUAL,      *)
(*   GREATER; f1 UNION-plus f2 (FUNION) is FUNION f1 f2; BIGUNION is        *)
(*   UNIONS; set is set_of_list; () is one; HOL4's {k | (k,v) | P} is        *)
(*   written {k | k,v | P}.                                                  *)
(* - Helpers that are not HOL4 names have the prefix PPARSEAUX_.             *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "hol4/sorting.ml";;
needs "hol4/balanced_map.ml";;
needs "hol4/libext.ml";;
needs "hol4/balanced_map_part2.ml";;

type_invention_error := true;;

(* implementation definitions *)

let map_INDUCT,map_RECURSION = cake_type
  "map = Map (K->K->ordering) ((K,V)balanced_map)";;

let mlmap_lookup_def = cake_def
  `mlmap_lookup (Map cmp t:(K,V)map) k = balanced_map_lookup cmp k t`;;

let mlmap_insert_def = cake_def
  `mlmap_insert (Map cmp t:(K,V)map) k v = Map cmp (balanced_map_insert cmp k v t)`;;

let mlmap_delete_def = cake_def
  `mlmap_delete (Map cmp t:(K,V)map) k = Map cmp (balanced_map_delete cmp k t)`;;

let mlmap_null_def = cake_def
  `mlmap_null (Map cmp t:(K,V)map) <=> null t`;;

let mlmap_size_def = cake_def
  `mlmap_size (Map cmp t:(K,V)map) = balanced_map_size' t`;;

let mlmap_empty_def = cake_def
  `mlmap_empty cmp = Map cmp balanced_map_empty:(K,V)map`;;

let mlmap_union_def = cake_def
  `mlmap_union (Map cmp t1:(K,V)map) (Map _ t2) =
     Map cmp (balanced_map_union cmp t1 t2)`;;

let mlmap_unionWith_def = cake_def
  `mlmap_unionWith f (Map cmp t1:(K,V)map) (Map _ t2) =
     Map cmp (unionWith cmp f t1 t2)`;;

let mlmap_unionWithKey_def = cake_def
  `mlmap_unionWithKey f (Map cmp t1:(K,V)map) (Map _ t2) =
     Map cmp (unionWithKey cmp f t1 t2)`;;

let mlmap_foldrWithKey_def = cake_def
  `mlmap_foldrWithKey (f:K->V->A->A) x (Map cmp t) = foldrWithKey f x t`;;

let mlmap_filter_def = cake_def
  `mlmap_filter p (Map cmp t:(K,V)map) = Map cmp (balanced_map_filter p t)`;;

let mlmap_filterWithKey_def = cake_def
  `mlmap_filterWithKey p (Map cmp t:(K,V)map) = Map cmp (filterWithKey p t)`;;

let mlmap_map_def = cake_def
  `mlmap_map (f:V->W) (Map cmp t:(K,V)map) = Map cmp (balanced_map_map f t)`;;

let mlmap_mapWithKey_def = cake_def
  `mlmap_mapWithKey (f:K->V->W) (Map cmp t:(K,V)map) = Map cmp (mapWithKey f t)`;;

let mlmap_toAscList_def = cake_def
  `mlmap_toAscList (Map cmp t:(K,V)map) = toAscList t`;;

let mlmap_fromList_def = cake_def
  `mlmap_fromList cmp (l:(K#V)list) = Map cmp (balanced_map_fromList cmp l)`;;

let isSubmapBy_def = cake_def
  `isSubmapBy (f:V->W->bool) (Map cmp t1:(K,V)map) (Map _ t2:(K,W)map) <=>
     isSubmapOfBy cmp f t1 t2`;;

let isSubmap_def = cake_def
  `isSubmap (m1:(K,V)map) m2 <=> isSubmapBy (=) m1 m2`;;

let mlmap_all_def = cake_def
  `mlmap_all f (Map cmp t:(K,V)map) <=> balanced_map_every f t`;;

let mlmap_exists_def = cake_def
  `mlmap_exists f (Map cmp t:(K,V)map) <=> balanced_map_exists f t`;;

let mlmap_member_def = cake_def
  `mlmap_member k (Map cmp t:(K,V)map) <=> balanced_map_member cmp k t`;;

let mlmap_singleton_def = cake_def
  `mlmap_singleton cmp (k:K) (v:V) = Map cmp (singleton k v)`;;

let mlmap_compare_def = cake_def
  `mlmap_compare vcmp (Map cmp m1:(K,V)map) (Map _ m2:(K,V)map) =
     compare cmp vcmp m1 m2`;;

(* definitions for proofs *)

let map_ok_def = cake_def
  `map_ok (Map cmp t:(K,V)map) <=> balanced_map_invariant cmp t /\ TotOrd cmp`;;

let cmp_of_def = cake_def
  `cmp_of (Map cmp t:(K,V)map) = cmp`;;

let mlmap_to_fmap_def = cake_def
  `(mlmap_to_fmap (Map cmp Tip:(K,V)map) = FEMPTY) /\
   (mlmap_to_fmap (Map cmp (Bin s k v l r)) =
      FUNION (mlmap_to_fmap (Map cmp l)) (mlmap_to_fmap (Map cmp r)) |+ (k,v))`;;

(* theorems *)

let mlmap_lookup_insert = prove
 (`!(t:(K,V)map) k1 v k2.
     map_ok t
     ==> mlmap_lookup (mlmap_insert t k1 v) k2 =
         if k1 = k2 then SOME v else mlmap_lookup t k2`,
  GEN_TAC THEN CASES_ON `t:(K,V)map` THEN
  REWRITE_TAC[map_ok_def; mlmap_lookup_def; mlmap_insert_def] THEN
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP TotOrder_imp_good_cmp) THEN
  ASM_SIMP_TAC[balanced_map_lookup_insert] THEN
  ASM_MESON_TAC[TotOrd]);;

let PPARSEAUX_TotOrd_EQUAL = prove
 (`!(cmp:K->K->ordering) x y. TotOrd cmp ==> (cmp x y = EQUAL <=> x = y)`,
  REWRITE_TAC[TotOrd] THEN MESON_TAC[]);;

let mlmap_lookup_delete = prove
 (`!(t:(K,V)map) k1 k2.
     map_ok t
     ==> mlmap_lookup (mlmap_delete t k1) k2 =
         if k1 = k2 then NONE else mlmap_lookup t k2`,
  MATCH_MP_TAC map_INDUCT THEN
  MAP_EVERY X_GEN_TAC [`cmp:K->K->ordering`; `t:(K,V)balanced_map`] THEN
  REWRITE_TAC[map_ok_def; mlmap_lookup_def; mlmap_delete_def] THEN
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP TotOrder_imp_good_cmp) THEN
  ASM_SIMP_TAC[lookup_thm; delete_thm; FLOOKUP_DRESTRICT; IN_DELETE; key_set_eq;
               PPARSEAUX_TotOrd_EQUAL] THEN
  ASM_CASES_TAC `k1:K = k2` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[FLOOKUP_DEF] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

let cmp_of_insert = prove
 (`!(t:(K,V)map) k v. cmp_of (mlmap_insert t k v) = cmp_of t`,
  GEN_TAC THEN CASES_ON `t:(K,V)map` THEN
  REWRITE_TAC[mlmap_insert_def; cmp_of_def]);;
let _ = cake_add_simps [cmp_of_insert];;

let cmp_of_delete = prove
 (`!(t:(K,V)map) k. cmp_of (mlmap_delete t k) = cmp_of t`,
  GEN_TAC THEN CASES_ON `t:(K,V)map` THEN
  REWRITE_TAC[mlmap_delete_def; cmp_of_def]);;
let _ = cake_add_simps [cmp_of_delete];;

let cmp_of_empty = prove
 (`!cmp. cmp_of (mlmap_empty cmp:(K,V)map) = cmp`,
  REWRITE_TAC[mlmap_empty_def; cmp_of_def]);;
let _ = cake_add_simps [cmp_of_empty];;

(* HOL4 fmap_FLOOKUP_EQ (local) *)

let fmap_FLOOKUP_EQ = prove
 (`!(f1:(A,B)fmap) f2. f1 = f2 <=> FLOOKUP f1 = FLOOKUP f2`,
  REPEAT GEN_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN
  REWRITE_TAC[GSYM fmap_eq_flookup; FUN_EQ_THM]);;

let TotOrd_key_set = prove
 (`!(cmp:K->K->ordering) k. TotOrd cmp ==> key_set cmp k = {k}`,
  REWRITE_TAC[key_set_def; EXTENSION; IN_ELIM_THM; IN_SING] THEN
  MESON_TAC[TotOrd]);;
let _ = cake_add_simps [TotOrd_key_set];;

(* lookups in MAP_KEYS (\x. {x}) m: at a singleton {y} the lookup of y in m, *)
(* elsewhere nothing (the HOL4 proofs abbreviate (\x. {x}) as ff and use     *)
(* INJ ff x UNIV with FLOOKUP_MAP_KEYS); PPARSEAUX_SING_CASES_TAC thl proves *)
(* an equation of finite maps with singleton keys by these cases             *)

let PPARSEAUX_SING_EQ = prove
 (`!x y:A. {x} = {y} <=> x = y`,
  SET_TAC[]);;

let PPARSEAUX_FLOOKUP_sing = prove
 (`!(m:(A,B)fmap) y. FLOOKUP (MAP_KEYS (\x. {x}) m) {y} = FLOOKUP m y`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`\x:A. {x}`; `m:(A,B)fmap`; `y:A`] FLOOKUP_MAP_KEYS_MAPPED) THEN
  REWRITE_TAC[INJ; IN_UNIV; PPARSEAUX_SING_EQ] THEN MESON_TAC[]);;

let PPARSEAUX_FLOOKUP_not_sing = prove
 (`!(m:(A,B)fmap) k.
     ~(?y. k = {y}) ==> FLOOKUP (MAP_KEYS (\x. {x}) m) k = NONE`,
  REWRITE_TAC[FLOOKUP_DEF; MAP_KEYS_def; IN_IMAGE] THEN MESON_TAC[]);;

let PPARSEAUX_SING_CASES_TAC (thl:thm list) =
  GEN_REWRITE_TAC I [fmap_eq_flookup] THEN GEN_TAC THEN
  W(fun (_,w) ->
      let k = rand(lhs w) in
      let ety = hd(snd(dest_type(type_of k))) in
      let y = mk_var("y",ety) in
      ASM_CASES_TAC (mk_exists(y,mk_eq(k,mk_setenum([y],ety)))) THENL
       [FIRST_X_ASSUM(CHOOSE_THEN SUBST1_TAC) THEN
        REWRITE_TAC(thl @ [PPARSEAUX_FLOOKUP_sing; PPARSEAUX_SING_EQ]);
        SUBGOAL_THEN (mk_forall(y,mk_neg(mk_eq(mk_setenum([y],ety),k))))
          ASSUME_TAC THENL
         [ASM_MESON_TAC[];
          ASM_SIMP_TAC(thl @ [PPARSEAUX_FLOOKUP_not_sing; case_def "option"])]]);;

let to_fmap_thm = prove
 (`!(t:(K,V)balanced_map) cmp.
     TotOrd cmp
     ==> to_fmap cmp t = MAP_KEYS (\x. {x}) (mlmap_to_fmap (Map cmp t))`,
  MATCH_MP_TAC balanced_map_INDUCT THEN
  REWRITE_TAC[to_fmap_def; mlmap_to_fmap_def; MAP_KEYS_FEMPTY] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[TotOrd_key_set] THEN
  PPARSEAUX_SING_CASES_TAC[FLOOKUP_UPDATE; FLOOKUP_FUNION]);;

let mlmap_empty_thm = prove
 (`!cmp. (map_ok (mlmap_empty cmp:(K,V)map) <=> TotOrd cmp) /\
         mlmap_to_fmap (mlmap_empty cmp:(K,V)map) = FEMPTY`,
  REWRITE_TAC[mlmap_empty_def; map_ok_def; balanced_map_empty_def;
              balanced_map_invariant_def; mlmap_to_fmap_def]);;

let mlmap_size_thm = prove
 (`!t:(K,V)map. map_ok t ==> mlmap_size t = FCARD (mlmap_to_fmap t)`,
  MATCH_MP_TAC map_INDUCT THEN
  MAP_EVERY X_GEN_TAC [`cmp:K->K->ordering`; `t:(K,V)balanced_map`] THEN
  REWRITE_TAC[map_ok_def; mlmap_size_def] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP TotOrder_imp_good_cmp) THEN
  ASM_SIMP_TAC[size_thm; to_fmap_thm; FCARD_DEF; MAP_KEYS_def] THEN
  MATCH_MP_TAC CARD_IMAGE_INJ THEN SIMP_TAC[FDOM_FINITE; PPARSEAUX_SING_EQ]);;

let MAP_KEYS_sing_set = prove
 (`!(f1:(A,B)fmap) f2.
     MAP_KEYS (\x. {x}) f1 = MAP_KEYS (\x. {x}) f2 <=> f1 = f2`,
  REPEAT GEN_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN
  REWRITE_TAC[fmap_eq_flookup] THEN DISCH_TAC THEN X_GEN_TAC `x:A` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `{x:A}`) THEN REWRITE_TAC[PPARSEAUX_FLOOKUP_sing]);;

let MAP_KEYS_sing_set_UPDATE = prove
 (`!(f:(A,B)fmap) k v.
     MAP_KEYS (\x. {x}) f |+ ({k},v) = MAP_KEYS (\x. {x}) (f |+ (k,v))`,
  REPEAT GEN_TAC THEN PPARSEAUX_SING_CASES_TAC[FLOOKUP_UPDATE]);;

let MAP_KEYS_sing_set_DOMSUB = prove
 (`!(f:(A,B)fmap) k.
     MAP_KEYS (\x. {x}) f \\ {k} = MAP_KEYS (\x. {x}) (f \\ k)`,
  REPEAT GEN_TAC THEN PPARSEAUX_SING_CASES_TAC[DOMSUB_FLOOKUP_THM]);;

let MAP_KEYS_sing_set_FUNION = prove
 (`!(f1:(A,B)fmap) f2.
     FUNION (MAP_KEYS (\x. {x}) f1) (MAP_KEYS (\x. {x}) f2) =
     MAP_KEYS (\x. {x}) (FUNION f1 f2)`,
  REPEAT GEN_TAC THEN PPARSEAUX_SING_CASES_TAC[FLOOKUP_FUNION]);;

let mlmap_insert_thm = prove
 (`!(t:(K,V)map) k v.
     map_ok t
     ==> map_ok (mlmap_insert t k v) /\
         mlmap_to_fmap (mlmap_insert t k v) = mlmap_to_fmap t |+ (k,v)`,
  MATCH_MP_TAC map_INDUCT THEN
  MAP_EVERY X_GEN_TAC [`cmp:K->K->ordering`; `t:(K,V)balanced_map`] THEN
  REWRITE_TAC[map_ok_def; mlmap_insert_def] THEN REPEAT GEN_TAC THEN
  STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP TotOrder_imp_good_cmp) THEN
  MP_TAC(ISPECL [`t:(K,V)balanced_map`; `cmp:K->K->ordering`; `k:K`; `v:V`]
                insert_thm) THEN
  ASM_SIMP_TAC[to_fmap_thm; TotOrd_key_set; MAP_KEYS_sing_set_UPDATE;
               MAP_KEYS_sing_set]);;

let mlmap_delete_thm = prove
 (`!(t:(K,V)map) k.
     map_ok t
     ==> map_ok (mlmap_delete t k) /\
         mlmap_to_fmap (mlmap_delete t k) = mlmap_to_fmap t \\ k`,
  MATCH_MP_TAC map_INDUCT THEN
  MAP_EVERY X_GEN_TAC [`cmp:K->K->ordering`; `t:(K,V)balanced_map`] THEN
  REWRITE_TAC[map_ok_def; mlmap_delete_def] THEN REPEAT GEN_TAC THEN
  STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP TotOrder_imp_good_cmp) THEN
  ASM_SIMP_TAC[delete_thm] THEN
  ONCE_REWRITE_TAC[GSYM MAP_KEYS_sing_set] THEN
  ASM_SIMP_TAC[GSYM to_fmap_thm; delete_thm; TotOrd_key_set] THEN
  REWRITE_TAC[GSYM DRESTRICT_DOMSUB; DRESTRICT_FDOM] THEN
  ASM_SIMP_TAC[to_fmap_thm; MAP_KEYS_sing_set_DOMSUB]);;

let mlmap_union_thm = prove
 (`!(t1:(K,V)map) t2.
     map_ok t1 /\ map_ok t2 /\ cmp_of t1 = cmp_of t2
     ==> map_ok (mlmap_union t1 t2) /\
         cmp_of (mlmap_union t1 t2) = cmp_of t1 /\
         mlmap_to_fmap (mlmap_union t1 t2) =
         FUNION (mlmap_to_fmap t1) (mlmap_to_fmap t2)`,
  MATCH_MP_TAC map_INDUCT THEN
  MAP_EVERY X_GEN_TAC [`cmp:K->K->ordering`; `b1:(K,V)balanced_map`] THEN
  MATCH_MP_TAC map_INDUCT THEN
  MAP_EVERY X_GEN_TAC [`cmp2:K->K->ordering`; `b2:(K,V)balanced_map`] THEN
  REWRITE_TAC[map_ok_def; mlmap_union_def; cmp_of_def] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP TotOrder_imp_good_cmp) THEN
  ASM_SIMP_TAC[union_thm] THEN
  ONCE_REWRITE_TAC[GSYM MAP_KEYS_sing_set] THEN
  ASM_SIMP_TAC[GSYM to_fmap_thm; union_thm; GSYM MAP_KEYS_sing_set_FUNION]);;

let FMERGE_WITH_KEY_MAP_KEYS = prove
 (`!(g:(A->bool)->B->B->B) m1 m2.
     FMERGE_WITH_KEY g (MAP_KEYS (\x. {x}) m1) (MAP_KEYS (\x. {x}) m2) =
     MAP_KEYS (\x. {x}) (FMERGE_WITH_KEY (\k x y. g {k} x y) m1 m2)`,
  REPEAT GEN_TAC THEN PPARSEAUX_SING_CASES_TAC[FLOOKUP_FMERGE_WITH_KEY]);;

(* HOL4 CHOICE_SING (pred_set), proved here *)

let PPARSEAUX_CHOICE_SING = prove
 (`!x:A. CHOICE {x} = x`,
  GEN_TAC THEN MP_TAC(ISPEC `{x:A}` CHOICE_DEF) THEN
  REWRITE_TAC[NOT_INSERT_EMPTY; IN_SING]);;

let mlmap_unionWithKey_thm = prove
 (`!(f:K->V->V->V) (t1:(K,V)map) t2.
     map_ok t1 /\ map_ok t2 /\ cmp_of t1 = cmp_of t2
     ==> map_ok (mlmap_unionWithKey f t1 t2) /\
         cmp_of (mlmap_unionWithKey f t1 t2) = cmp_of t1 /\
         mlmap_to_fmap (mlmap_unionWithKey f t1 t2) =
         FMERGE_WITH_KEY f (mlmap_to_fmap t1) (mlmap_to_fmap t2)`,
  GEN_TAC THEN MATCH_MP_TAC map_INDUCT THEN
  MAP_EVERY X_GEN_TAC [`cmp:K->K->ordering`; `b1:(K,V)balanced_map`] THEN
  MATCH_MP_TAC map_INDUCT THEN
  MAP_EVERY X_GEN_TAC [`cmp2:K->K->ordering`; `b2:(K,V)balanced_map`] THEN
  REWRITE_TAC[map_ok_def; mlmap_unionWithKey_def; cmp_of_def] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP TotOrder_imp_good_cmp) THEN
  SUBGOAL_THEN `!k1 k2 x y. cmp k1 k2 = EQUAL ==> (f:K->V->V->V) k1 x y = f k2 x y`
    ASSUME_TAC THENL [ASM_SIMP_TAC[PPARSEAUX_TotOrd_EQUAL]; ALL_TAC] THEN
  MP_TAC(PART_MATCH (lhand o rand o rand) unionWithKey_thm
           `to_fmap cmp (unionWithKey cmp (f:K->V->V->V) b1 b2)`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[GSYM MAP_KEYS_sing_set] THEN
  ASM_SIMP_TAC[GSYM to_fmap_thm] THEN
  ASM_SIMP_TAC[to_fmap_thm; FMERGE_WITH_KEY_MAP_KEYS; PPARSEAUX_CHOICE_SING;
               ETA_AX]);;

let unionWith_lemma = prove
 (`!(f:V->V->V) (t1:(K,V)map) t2.
     mlmap_unionWith f t1 t2 = mlmap_unionWithKey (\k. f) t1 t2`,
  REPEAT GEN_TAC THEN CASES_ON `t1:(K,V)map` THEN CASES_ON `t2:(K,V)map` THEN
  REWRITE_TAC[mlmap_unionWith_def; mlmap_unionWithKey_def; unionWith_def;
              ETA_AX]);;

let unionWith_thm = prove
 (`!(f:V->V->V) (t1:(K,V)map) t2.
     map_ok t1 /\ map_ok t2 /\ cmp_of t1 = cmp_of t2
     ==> map_ok (mlmap_unionWith f t1 t2) /\
         cmp_of (mlmap_unionWith f t1 t2) = cmp_of t1 /\
         mlmap_to_fmap (mlmap_unionWith f t1 t2) =
         FMERGE_WITH_KEY (\k x y. f x y) (mlmap_to_fmap t1) (mlmap_to_fmap t2)`,
  REWRITE_TAC[unionWith_lemma; ETA_AX] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_SIMP_TAC[mlmap_unionWithKey_thm]);;

let mlmap_all_thm = prove
 (`!(f:K->V->bool) (t:(K,V)map).
     map_ok t ==> (mlmap_all f t <=> !k v. mlmap_lookup t k = SOME v ==> f k v)`,
  GEN_TAC THEN MATCH_MP_TAC map_INDUCT THEN
  MAP_EVERY X_GEN_TAC [`cmp:K->K->ordering`; `b:(K,V)balanced_map`] THEN
  REWRITE_TAC[map_ok_def; mlmap_all_def; mlmap_lookup_def] THEN STRIP_TAC THEN
  MATCH_MP_TAC balanced_map_every_thm THEN
  ASM_SIMP_TAC[TotOrder_imp_good_cmp; resp_equiv_def; PPARSEAUX_TotOrd_EQUAL]);;

let mlmap_exists_thm = prove
 (`!(f:K->V->bool) (t:(K,V)map).
     map_ok t ==> (mlmap_exists f t <=> ?k v. mlmap_lookup t k = SOME v /\ f k v)`,
  GEN_TAC THEN MATCH_MP_TAC map_INDUCT THEN
  MAP_EVERY X_GEN_TAC [`cmp:K->K->ordering`; `b:(K,V)balanced_map`] THEN
  REWRITE_TAC[map_ok_def; mlmap_exists_def; mlmap_lookup_def] THEN STRIP_TAC THEN
  MATCH_MP_TAC balanced_map_exists_thm THEN
  ASM_SIMP_TAC[TotOrder_imp_good_cmp; resp_equiv_def; PPARSEAUX_TotOrd_EQUAL]);;

let FDIFF_MAP_KEYS = prove
 (`!(ks:(A->bool)->bool) (m:(A,B)fmap).
     (!x. x IN ks ==> SING x)
     ==> FDIFF (MAP_KEYS (\x. {x}) m) ks =
         MAP_KEYS (\x. {x}) (FDIFF m (UNIONS ks))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!y:A. {y} IN ks <=> y IN UNIONS ks` ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN RULE_ASSUM_TAC(REWRITE_RULE[SING]) THEN
    GEN_TAC THEN EQ_TAC THENL
     [DISCH_TAC THEN EXISTS_TAC `{y:A}` THEN ASM_REWRITE_TAC[IN_SING];
      DISCH_THEN(X_CHOOSE_THEN `s:A->bool` STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `s:A->bool`) THEN ASM_REWRITE_TAC[] THEN
      STRIP_TAC THEN UNDISCH_TAC `(y:A) IN s` THEN ASM_REWRITE_TAC[IN_SING] THEN
      DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[]];
    PPARSEAUX_SING_CASES_TAC[FLOOKUP_FDIFF] THEN ASM_REWRITE_TAC[COND_ID]]);;

(* the set of keys that filterWithKey removes, on singleton keys (for       *)
(* filterWithKey_thm; HOL4 does this with FDIFF_MAP_KEYS and some_intro)    *)

let PPARSEAUX_FDIFF_sing = prove
 (`!(M:(A,B)fmap) (P:A->B->bool).
     FDIFF (MAP_KEYS (\x. {x}) M)
           {k | k,v | FLOOKUP (MAP_KEYS (\x. {x}) M) k = SOME v /\ P (CHOICE k) v} =
     MAP_KEYS (\x. {x}) (FDIFF M {k | k,v | FLOOKUP M k = SOME v /\ P k v})`,
  REPEAT GEN_TAC THEN PPARSEAUX_SING_CASES_TAC[FLOOKUP_FDIFF] THENL
   [AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    MESON_TAC[PPARSEAUX_FLOOKUP_sing; PPARSEAUX_CHOICE_SING];
    REWRITE_TAC[COND_ID]]);;

let mlmap_filterWithKey_thm = prove
 (`!(f:K->V->bool) (t:(K,V)map).
     map_ok t
     ==> map_ok (mlmap_filterWithKey f t) /\
         mlmap_to_fmap (mlmap_filterWithKey f t) =
         FDIFF (mlmap_to_fmap t)
               {k | k,v | FLOOKUP (mlmap_to_fmap t) k = SOME v /\ ~f k v}`,
  GEN_TAC THEN MATCH_MP_TAC map_INDUCT THEN
  MAP_EVERY X_GEN_TAC [`cmp:K->K->ordering`; `b:(K,V)balanced_map`] THEN
  REWRITE_TAC[map_ok_def; mlmap_filterWithKey_def] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP TotOrder_imp_good_cmp) THEN
  SUBGOAL_THEN `!k1 k2 x. cmp k1 k2 = EQUAL ==> (f:K->V->bool) k1 x = f k2 x`
    ASSUME_TAC THENL [ASM_SIMP_TAC[PPARSEAUX_TotOrd_EQUAL]; ALL_TAC] THEN
  MP_TAC(PART_MATCH (lhand o rand o rand) filterWithKey_thm
           `to_fmap cmp (filterWithKey (f:K->V->bool) b)`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[GSYM MAP_KEYS_sing_set] THEN
  ASM_SIMP_TAC[GSYM to_fmap_thm] THEN
  ASM_SIMP_TAC[to_fmap_thm; PPARSEAUX_FDIFF_sing]);;

let filter_lemma = prove
 (`!(f:V->bool) (t:(K,V)map).
     mlmap_filter f t = mlmap_filterWithKey (\k. f) t`,
  GEN_TAC THEN MATCH_MP_TAC map_INDUCT THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[mlmap_filter_def; mlmap_filterWithKey_def;
              balanced_map_filter_def; ETA_AX]);;

let filter_thm = prove
 (`!(f:V->bool) (t:(K,V)map).
     map_ok t
     ==> map_ok (mlmap_filter f t) /\
         mlmap_to_fmap (mlmap_filter f t) =
         FDIFF (mlmap_to_fmap t)
               {k | k,v | FLOOKUP (mlmap_to_fmap t) k = SOME v /\ ~f v}`,
  REWRITE_TAC[filter_lemma] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_SIMP_TAC[mlmap_filterWithKey_thm]);;

let mlmap_lookup_thm = prove
 (`!(t:(K,V)map) k. map_ok t ==> mlmap_lookup t k = FLOOKUP (mlmap_to_fmap t) k`,
  MATCH_MP_TAC map_INDUCT THEN
  MAP_EVERY X_GEN_TAC [`cmp:K->K->ordering`; `t:(K,V)balanced_map`] THEN
  REWRITE_TAC[map_ok_def; mlmap_lookup_def] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP TotOrder_imp_good_cmp) THEN
  ASM_SIMP_TAC[lookup_thm; to_fmap_thm; TotOrd_key_set; PPARSEAUX_FLOOKUP_sing]);;

let filterWithKey_all = prove
 (`!(f:K->V->bool) (t:(K,V)map). map_ok t ==> mlmap_all f (mlmap_filterWithKey f t)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC `f:K->V->bool` o
              MATCH_MP (ONCE_REWRITE_RULE[SWAP_FORALL_THM] mlmap_filterWithKey_thm)) THEN
  ASM_SIMP_TAC[mlmap_all_thm; mlmap_lookup_thm; FLOOKUP_FDIFF] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[option_DISTINCT]);;

let mlmap_MAP_FST_toAscList = prove
 (`!t:(K,V)map.
     map_ok t
     ==> SORTED (\x y. cmp_of t x y = LESS) (MAP FST (mlmap_toAscList t)) /\
         ALL_DISTINCT (MAP FST (mlmap_toAscList t)) /\
         FDOM (mlmap_to_fmap t) = set_of_list (MAP FST (mlmap_toAscList t))`,
  MATCH_MP_TAC map_INDUCT THEN
  MAP_EVERY X_GEN_TAC [`cmp:K->K->ordering`; `b:(K,V)balanced_map`] THEN
  REWRITE_TAC[map_ok_def; cmp_of_def; mlmap_toAscList_def] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP TotOrder_imp_good_cmp) THEN
  MP_TAC(PART_MATCH (lhand o rand o rand) MAP_FST_toAscList
           `FDOM (to_fmap cmp (b:(K,V)balanced_map))`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPEC `\x y. (cmp:K->K->ordering) x y = LESS` SORTED_ALL_DISTINCT) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[irreflexive_def; transitive_def] THEN
      UNDISCH_TAC `TotOrd (cmp:K->K->ordering)` THEN REWRITE_TAC[TotOrd] THEN
      MESON_TAC[ordering_distinct];
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    SUBGOAL_THEN `key_set (cmp:K->K->ordering) = (\x. {x})` ASSUME_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN ASM_SIMP_TAC[TotOrd_key_set]; ALL_TAC] THEN
    UNDISCH_TAC `FDOM (to_fmap cmp (b:(K,V)balanced_map)) =
                 IMAGE (key_set cmp) (set_of_list (MAP FST (toAscList b)))` THEN
    ASM_SIMP_TAC[to_fmap_thm; MAP_KEYS_def] THEN
    MATCH_MP_TAC(TAUT `(a <=> b) ==> a ==> b`) THEN
    MATCH_MP_TAC IMAGE_11 THEN REWRITE_TAC[PPARSEAUX_SING_EQ]]);;

let mlmap_MEM_toAscList = prove
 (`!(t:(K,V)map) k v.
     map_ok t /\ MEM (k,v) (mlmap_toAscList t)
     ==> FLOOKUP (mlmap_to_fmap t) k = SOME v`,
  MATCH_MP_TAC map_INDUCT THEN
  MAP_EVERY X_GEN_TAC [`cmp:K->K->ordering`; `b:(K,V)balanced_map`] THEN
  REWRITE_TAC[map_ok_def; mlmap_toAscList_def] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP TotOrder_imp_good_cmp) THEN
  MP_TAC(PART_MATCH (lhand o rand) MEM_toAscList
           `FLOOKUP (to_fmap cmp (b:(K,V)balanced_map)) (key_set cmp k)`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[to_fmap_thm; TotOrd_key_set; PPARSEAUX_FLOOKUP_sing]);;
