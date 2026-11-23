(* ========================================================================= *)
(* balanced_map_part2: the rest of the HOL4 library theory balanced_map,     *)
(* examples/data-structures/balanced_bst/balanced_mapScript.sml (the file    *)
(* hol4/balanced_map.ml has the theory up to insert_thm and lookup_insert).  *)
(* Every section of this file comes from that theory, in its order (HOL4     *)
(* line numbers):                                                            *)
(* - the definitions from insertR on (551-813), then the definitions of the  *)
(*   proof part (restrict_set, restrict_domain, bounded_root, bounded_all,   *)
(*   lift_key, map_keys, every, exists);                                     *)
(* - insertR_thm, insertMax_thm, insertMin_thm (1590-1702);                  *)
(* - deleteFindMin, deleteFindMax, glue_thm, delete_thm, lookup_delete       *)
(*   (1703-2126);                                                            *)
(* - trim_thm (2127-2215);                                                   *)
(* - link_thm, link2_thm (2216-2439);                                        *)
(* - filterLt_thm, filterGt_thm (2440-2546);                                 *)
(* - hedgeUnion_thm, union_thm, lookup_union (2547-2863);                    *)
(* - hedgeUnionWithKey_thm, unionWithKey_thm, unionWith_thm,                 *)
(*   lookup_unionWithKey, lookup_unionWith (2864-3057);                      *)
(* - toAscList_thm, MAP_FST_toAscList, MEM_toAscList, ALOOKUP_toAscList      *)
(*   (3058-3227);                                                            *)
(* - every_thm, exists_thm (3895-4066);                                      *)
(* - filterWithKey_thm, every_filter, filter_thm (4067-4165).                *)
(*                                                                           *)
(* Not ported (no new theory uses them): compare_good_cmp, compare_thm,      *)
(* mapWithKey_thm, map_thm, splitLookup_thm, isSubmapOfBy_thm,               *)
(* isSubmapOf_thm, fromList_thm (3228-3894) and their local lemmas.  The     *)
(* local lemmas of the HOL4 proofs are replaced by helpers; most of the      *)
(* proofs compare the finite maps of two trees pointwise, at the key sets of *)
(* keys (LIBXAUX_FMAP_EXT_KEYS).                                             *)
(*                                                                           *)
(* Names: HOL4 delete, glue, union, trim, link, link2, filter, map,          *)
(* fromList, every and exists are balanced_map_delete, balanced_map_glue,    *)
(* ..., balanced_map_exists (taken elsewhere in the port, common words, or   *)
(* the binder keyword exists), with their _def and _ind theorems.  The       *)
(* theorems lookup_delete and lookup_union (sptree has them) are             *)
(* balanced_map_lookup_delete and balanced_map_lookup_union; unionWith_thm   *)
(* and filter_thm (mlmap has them) are balanced_map_unionWith_thm and        *)
(* balanced_map_filter_thm; every_thm and exists_thm (llist has them) are    *)
(* balanced_map_every_thm and balanced_map_exists_thm.  The other names are  *)
(* HOL4's.  HOL4 size is balanced_map_size' (hol4/balanced_map.ml), list_cmp *)
(* and pair_cmp are list_compare and pair_compare, option_cmp is             *)
(* option_compare, FOLDR f e l is ITLIST f l e.                              *)
(*                                                                           *)
(* Statements: HOL4's, with its free variables (cmp, k, v, ...) quantified   *)
(* too; the vacuous blo and bhi of union_thm have type K option.             *)
(*                                                                           *)
(* Helpers of this file are named LIBXAUX_... (LIBXAUX_B_... in the delete   *)
(* section, LIBXAUX_A_... in the toAscList, every and exists sections;       *)
(* HOL4's local EXT2 and toAscList_helper are LIBXAUX_A_EXT2 and             *)
(* LIBXAUX_A_toAscList_helper).                                              *)
(* ========================================================================= *)

needs "hol4/balanced_map.ml";;
needs "hol4/libext.ml";;
needs "hol4/alist.ml";;
needs "hol4/sorting.ml";;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The definitions (HOL4 balanced_mapScript.sml lines 551-813, then the      *)
(* definitions of its proof part: restrict_set, restrict_domain,             *)
(* bounded_root, bounded_all, lift_key, map_keys, every, exists).            *)
(* ------------------------------------------------------------------------- *)

let insertR_def = cake_def
  `(insertR (cmp:K->K->ordering) k (v:V) Tip = singleton k v) /\
   (insertR cmp k v (Bin s k' v' l r) =
      match cmp k k' with
        LESS -> balanceL k' v' (insertR cmp k v l) r
      | GREATER -> balanceR k' v' l (insertR cmp k v r)
      | EQUAL -> Bin s k' v' l r)`;;

let insertMax_def = cake_def
  `(insertMax (k:K) (v:V) Tip = singleton k v) /\
   (insertMax k v (Bin s k' v' l r) = balanceR k' v' l (insertMax k v r))`;;

let insertMin_def = cake_def
  `(insertMin (k:K) (v:V) Tip = singleton k v) /\
   (insertMin k v (Bin s k' v' l r) = balanceL k' v' (insertMin k v l) r)`;;

let deleteFindMax_def = cake_def
  `(deleteFindMax (Bin s (k:K) (x:V) l Tip) = ((k,x),l)) /\
   (deleteFindMax (Bin s k x l r) =
      let (km,r') = deleteFindMax r in (km,balanceL k x l r')) /\
   (deleteFindMax Tip = (ARB,Tip))`;;

let deleteFindMax_ind = cake_ind "deleteFindMax";;

let deleteFindMin_def = cake_def
  `(deleteFindMin (Bin s (k:K) (x:V) Tip r) = ((k,x),r)) /\
   (deleteFindMin (Bin s k x l r) =
      let (km,l') = deleteFindMin l in (km,balanceR k x l' r)) /\
   (deleteFindMin Tip = (ARB,Tip))`;;

let deleteFindMin_ind = cake_ind "deleteFindMin";;

let balanced_map_glue_def = cake_def
  `(balanced_map_glue Tip (r:(K,V)balanced_map) = r) /\
   (balanced_map_glue l Tip = l) /\
   (balanced_map_glue l r =
      if balanced_map_size' l > balanced_map_size' r then
        match deleteFindMax l with ((km,m),l') -> balanceR km m l' r
      else
        match deleteFindMin r with ((km,m),r') -> balanceL km m l r')`;;

let balanced_map_delete_def = cake_def
  `(balanced_map_delete (cmp:K->K->ordering) k (Tip:(K,V)balanced_map) = Tip) /\
   (balanced_map_delete cmp k (Bin s k' v l r) =
      match cmp k k' with
        LESS -> balanceR k' v (balanced_map_delete cmp k l) r
      | GREATER -> balanceL k' v l (balanced_map_delete cmp k r)
      | EQUAL -> balanced_map_glue l r)`;;

let trim_help_greater_def = cake_def
  `(trim_help_greater (cmp:K->K->ordering) lo (Bin s' k (v':V) l' r) =
      if cmp k lo = LESS \/ cmp k lo = EQUAL then trim_help_greater cmp lo r
      else Bin s' k v' l' r) /\
   (trim_help_greater cmp lo Tip = Tip)`;;

let trim_help_lesser_def = cake_def
  `(trim_help_lesser (cmp:K->K->ordering) hi (Bin s' k (v':V) l r') =
      if cmp k hi = GREATER \/ cmp k hi = EQUAL then trim_help_lesser cmp hi l
      else Bin s' k v' l r') /\
   (trim_help_lesser cmp lo Tip = Tip)`;;

(* HOL4's second clause reads trim_help_middle lo cmp hi Tip = Tip (its     *)
(* variables are named in another order; the clause is the same)            *)

let trim_help_middle_def = cake_def
  `(trim_help_middle (cmp:K->K->ordering) lo hi (Bin s' k (v':V) l r) =
      if cmp k lo = LESS \/ cmp k lo = EQUAL then trim_help_middle cmp lo hi r
      else if cmp k hi = GREATER \/ cmp k hi = EQUAL
      then trim_help_middle cmp lo hi l
      else Bin s' k v' l r) /\
   (trim_help_middle cmp lo hi Tip = Tip)`;;

let balanced_map_trim_def = cake_def
  `(balanced_map_trim (cmp:K->K->ordering) NONE NONE (t:(K,V)balanced_map) = t) /\
   (balanced_map_trim cmp (SOME lk) NONE t = trim_help_greater cmp lk t) /\
   (balanced_map_trim cmp NONE (SOME hk) t = trim_help_lesser cmp hk t) /\
   (balanced_map_trim cmp (SOME lk) (SOME hk) t = trim_help_middle cmp lk hk t)`;;

let balanced_map_link_def = cake_def
  `(balanced_map_link (k:K) (v:V) Tip r = insertMin k v r) /\
   (balanced_map_link k v l Tip = insertMax k v l) /\
   (balanced_map_link k v (Bin sizeL ky y ly ry) (Bin sizeR kz z lz rz) =
      if balanced_map_delta * sizeL < sizeR then
        balanceL kz z (balanced_map_link k v (Bin sizeL ky y ly ry) lz) rz
      else if balanced_map_delta * sizeR < sizeL then
        balanceR ky y ly (balanced_map_link k v ry (Bin sizeR kz z lz rz))
      else bin k v (Bin sizeL ky y ly ry) (Bin sizeR kz z lz rz))`;;

let balanced_map_link_ind = cake_ind "balanced_map_link";;

let balanced_map_link2_def = cake_def
  `(balanced_map_link2 (l:(K,V)balanced_map) Tip = l) /\
   (balanced_map_link2 Tip r = r) /\
   (balanced_map_link2 (Bin sizeL kx x lx rx) (Bin sizeR ky y ly ry) =
      if balanced_map_delta * sizeL < sizeR then
        balanceL ky y (balanced_map_link2 (Bin sizeL kx x lx rx) ly) ry
      else if balanced_map_delta * sizeR < sizeL then
        balanceR kx x lx (balanced_map_link2 rx (Bin sizeR ky y ly ry))
      else balanced_map_glue (Bin sizeL kx x lx rx) (Bin sizeR ky y ly ry))`;;

let balanced_map_link2_ind = cake_ind "balanced_map_link2";;

let filterLt_help_def = cake_def
  `(filterLt_help (cmp:K->K->ordering) b (Tip:(K,V)balanced_map) = Tip) /\
   (filterLt_help cmp b' (Bin s kx x l r) =
      match cmp kx b' with
        LESS -> balanced_map_link kx x l (filterLt_help cmp b' r)
      | EQUAL -> l
      | GREATER -> filterLt_help cmp b' l)`;;

let filterLt_def = cake_def
  `(filterLt (cmp:K->K->ordering) NONE (t:(K,V)balanced_map) = t) /\
   (filterLt cmp (SOME b) t = filterLt_help cmp b t)`;;

let filterGt_help_def = cake_def
  `(filterGt_help (cmp:K->K->ordering) b (Tip:(K,V)balanced_map) = Tip) /\
   (filterGt_help cmp b' (Bin s kx x l r) =
      match cmp b' kx with
        LESS -> balanced_map_link kx x (filterGt_help cmp b' l) r
      | EQUAL -> r
      | GREATER -> filterGt_help cmp b' r)`;;

let filterGt_def = cake_def
  `(filterGt (cmp:K->K->ordering) NONE (t:(K,V)balanced_map) = t) /\
   (filterGt cmp (SOME b) t = filterGt_help cmp b t)`;;

let hedgeUnion_def = cake_def
  `(hedgeUnion (cmp:K->K->ordering) blo bhi (t1:(K,V)balanced_map) Tip = t1) /\
   (hedgeUnion cmp blo bhi Tip (Bin _ kx x l r) =
      balanced_map_link kx x (filterGt cmp blo l) (filterLt cmp bhi r)) /\
   (hedgeUnion cmp blo bhi t1 (Bin _ kx x Tip Tip) = insertR cmp kx x t1) /\
   (hedgeUnion cmp blo bhi (Bin s kx x l r) t2 =
      balanced_map_link kx x
        (hedgeUnion cmp blo (SOME kx) l (balanced_map_trim cmp blo (SOME kx) t2))
        (hedgeUnion cmp (SOME kx) bhi r (balanced_map_trim cmp (SOME kx) bhi t2)))`;;

let hedgeUnion_ind = cake_ind "hedgeUnion";;

let balanced_map_union_def = cake_def
  `(balanced_map_union (cmp:K->K->ordering) Tip (t2:(K,V)balanced_map) = t2) /\
   (balanced_map_union cmp t1 Tip = t1) /\
   (balanced_map_union cmp t1 t2 = hedgeUnion cmp NONE NONE t1 t2)`;;

let hedgeUnionWithKey_def = cake_def
  `(hedgeUnionWithKey (_:K->K->ordering) (_:K->V->V->V) _ _
                      (t1:(K,V)balanced_map) Tip = t1) /\
   (hedgeUnionWithKey cmp _ blo bhi Tip (Bin _ kx x l r) =
      balanced_map_link kx x (filterGt cmp blo l) (filterLt cmp bhi r)) /\
   (hedgeUnionWithKey cmp f blo bhi (Bin _ kx x l r) t2 =
      let newx = (match balanced_map_lookup cmp kx t2 with
                    NONE -> x
                  | SOME y -> f kx x y) in
      balanced_map_link kx newx
        (hedgeUnionWithKey cmp f blo (SOME kx) l
           (balanced_map_trim cmp blo (SOME kx) t2))
        (hedgeUnionWithKey cmp f (SOME kx) bhi r
           (balanced_map_trim cmp (SOME kx) bhi t2)))`;;

let hedgeUnionWithKey_ind = cake_ind "hedgeUnionWithKey";;

let unionWithKey_def = cake_def
  `(unionWithKey (_:K->K->ordering) (_:K->V->V->V) Tip
                 (t2:(K,V)balanced_map) = t2) /\
   (unionWithKey _ _ t1 Tip = t1) /\
   (unionWithKey cmp f t1 t2 = hedgeUnionWithKey cmp f NONE NONE t1 t2)`;;

let unionWith_def = cake_def
  `unionWith (cmp:K->K->ordering) (f:V->V->V) (t1:(K,V)balanced_map) t2 =
     unionWithKey cmp (\k x y. f x y) t1 t2`;;

let filterWithKey_def = cake_def
  `(filterWithKey (f:K->V->bool) Tip = Tip) /\
   (filterWithKey f (Bin s kx x l r) =
      let l' = filterWithKey f l in
      let r' = filterWithKey f r in
      if f kx x then balanced_map_link kx x l' r' else balanced_map_link2 l' r')`;;

let balanced_map_filter_def = cake_def
  `balanced_map_filter (f:V->bool) (t:(K,V)balanced_map) =
     filterWithKey (\k x. f x) t`;;

let foldrWithKey_def = cake_def
  `(foldrWithKey (f:K->V->A->A) z' Tip = z') /\
   (foldrWithKey f z' (Bin _ kx x l r) =
      foldrWithKey f (f kx x (foldrWithKey f z' r)) l)`;;

let toAscList_def = cake_def
  `toAscList (t:(K,V)balanced_map) = foldrWithKey (\k x xs. CONS (k,x) xs) [] t`;;

(* HOL4 list_cmp and pair_cmp are list_compare and pair_compare *)

let compare_def = cake_def
  `compare (cmp1:K->K->ordering) (cmp2:V->V->ordering) t1 t2 =
     list_compare (pair_compare cmp1 cmp2) (toAscList t1) (toAscList t2)`;;

let mapWithKey_def = cake_def
  `(mapWithKey (f:K->V->W) Tip = Tip) /\
   (mapWithKey f (Bin sx kx x l r) =
      Bin sx kx (f kx x) (mapWithKey f l) (mapWithKey f r))`;;

let balanced_map_map_def = cake_def
  `balanced_map_map (f:V->W) (t:(K,V)balanced_map) = mapWithKey (\k x. f x) t`;;

let splitLookup_def = cake_def
  `(splitLookup (cmp:K->K->ordering) k (Tip:(K,V)balanced_map) = (Tip,NONE,Tip)) /\
   (splitLookup cmp k (Bin _ kx x l r) =
      match cmp k kx with
        LESS -> (let (lt,z,gt) = splitLookup cmp k l in
                 let gt' = balanced_map_link kx x gt r in (lt,z,gt'))
      | GREATER -> (let (lt,z,gt) = splitLookup cmp k r in
                    let lt' = balanced_map_link kx x l lt in (lt',z,gt))
      | EQUAL -> (l,SOME x,r))`;;

let submap'_def = cake_def
  `(submap' (cmp:K->K->ordering) (_:V->W->bool) (Tip:(K,V)balanced_map)
            (_:(K,W)balanced_map) <=> T) /\
   (submap' cmp _ _ Tip <=> F) /\
   (submap' cmp f (Bin _ kx x l r) t <=>
      match splitLookup cmp kx t with
        (lt,NONE,gt) -> F
      | (lt,SOME y,gt) -> f x y /\ submap' cmp f l lt /\ submap' cmp f r gt)`;;

let submap'_ind = cake_ind "submap'";;

let isSubmapOfBy_def = cake_def
  `isSubmapOfBy (cmp:K->K->ordering) (f:V->W->bool) t1 t2 <=>
     balanced_map_size' t1 <= balanced_map_size' t2 /\ submap' cmp f t1 t2`;;

let isSubmapOf_def = cake_def
  `isSubmapOf (cmp:K->K->ordering) (t1:(K,V)balanced_map) t2 <=>
     isSubmapOfBy cmp (=) t1 t2`;;

(* HOL4 FOLDR f e l is ITLIST f l e *)

let balanced_map_fromList_def = cake_def
  `balanced_map_fromList (cmp:K->K->ordering) (l:(K#V)list) =
     ITLIST (\(k,v) t. balanced_map_insert cmp k v t) l balanced_map_empty`;;

(* HOL4 option_cmp is option_compare (hol4/comparison.ml) *)

let restrict_set_def = new_definition
  `restrict_set (cmp:K->K->ordering) lo hi =
     {k | option_compare cmp lo (SOME k) = LESS /\
          option_cmp2 cmp (SOME k) hi = LESS}`;;

let restrict_domain_def = new_definition
  `restrict_domain (cmp:K->K->ordering) lo hi (m:(K->bool,V)fmap) =
     DRESTRICT m (IMAGE (key_set cmp) (restrict_set cmp lo hi))`;;

let bounded_root_def = new_definition
  `bounded_root (cmp:K->K->ordering) lk hk (t:(K,V)balanced_map) <=>
     !s k v l r. t = Bin s k v l r ==> k IN restrict_set cmp lk hk`;;

let bounded_all_def = cake_def
  `(bounded_all (cmp:K->K->ordering) lk hk (Tip:(K,V)balanced_map) <=> T) /\
   (bounded_all cmp lk hk (Bin s k v t1 t2) <=>
      k IN restrict_set cmp lk hk /\
      bounded_all cmp lk hk t1 /\ bounded_all cmp lk hk t2)`;;

let lift_key_def = new_definition
  `lift_key (cmp:K->K->ordering) (kvs:K#V->bool) =
     IMAGE (\(k,v). (key_set cmp k,v)) kvs`;;

let map_keys_def = new_definition
  `map_keys (cmp:K2->K2->ordering) (f:K->K2) (t:(K,V)balanced_map) =
     balanced_map_fromList cmp (MAP (\(k,v). (f k,v)) (toAscList t))`;;

let balanced_map_every_def = cake_def
  `(balanced_map_every (f:K->V->bool) Tip <=> T) /\
   (balanced_map_every f (Bin _ kx x l r) <=>
      if f kx x then
        if balanced_map_every f l then
          if balanced_map_every f r then T else F
        else F
      else F)`;;

(* HOL4 exists: balanced_map_exists (exists is a binder keyword) *)

let balanced_map_exists_def = cake_def
  `(balanced_map_exists (f:K->V->bool) Tip <=> F) /\
   (balanced_map_exists f (Bin _ kx x l r) <=>
      if f kx x then T
      else if balanced_map_exists f l then T
      else if balanced_map_exists f r then T
      else F)`;;

(* ========================================================================= *)
(* HOL4 balanced_mapScript.sml lines 1590-1702: insertR_thm, insertMax_thm,  *)
(* insertMin_thm.                                                            *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Helpers: the key ordering of a changed subtree, and balancing after an    *)
(* insertion into (or a deletion from) one side.                             *)
(* ------------------------------------------------------------------------- *)

let LIBXAUX_ko_insert = prove
 (`!(cmp:K->K->ordering) a kk (t:(K,V)balanced_map) (t':(K,V)balanced_map) res.
     good_cmp cmp /\
     FDOM (to_fmap cmp t') SUBSET key_set cmp kk INSERT FDOM (to_fmap cmp t) /\
     key_ordered cmp a t res /\ cmp a kk = res
     ==> key_ordered cmp a t' res`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `key_ordered (cmp:K->K->ordering) a (t:(K,V)balanced_map) res` THEN
  ASM_SIMP_TAC[key_ordered_to_fmap] THEN
  UNDISCH_TAC `FDOM (to_fmap (cmp:K->K->ordering) (t':(K,V)balanced_map)) SUBSET
               key_set cmp kk INSERT FDOM (to_fmap cmp (t:(K,V)balanced_map))` THEN
  REWRITE_TAC[SUBSET; IN_INSERT] THEN ASM_MESON_TAC[key_set_cmp_thm]);;

let LIBXAUX_ko_sub = prove
 (`!(cmp:K->K->ordering) a (t:(K,V)balanced_map) (t':(K,V)balanced_map) res.
     good_cmp cmp /\ FDOM (to_fmap cmp t') SUBSET FDOM (to_fmap cmp t) /\
     key_ordered cmp a t res
     ==> key_ordered cmp a t' res`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `key_ordered (cmp:K->K->ordering) a (t:(K,V)balanced_map) res` THEN
  ASM_SIMP_TAC[key_ordered_to_fmap] THEN ASM SET_TAC[]);;

let LIBXAUX_balanceL_ins = prove
 (`!(cmp:K->K->ordering) s k' (v':V) l r l'.
     good_cmp cmp /\ balanced_map_invariant cmp (Bin s k' v' l r) /\
     balanced_map_invariant cmp l' /\ key_ordered cmp k' l' GREATER /\
     FCARD (to_fmap cmp l) <= FCARD (to_fmap cmp l') /\
     FCARD (to_fmap cmp l') <= FCARD (to_fmap cmp l) + 1
     ==> balanced_map_invariant cmp (balanceL k' v' l' r) /\
         to_fmap cmp (balanceL k' v' l' r) =
         FUNION (to_fmap cmp l') (to_fmap cmp r) |+ (key_set cmp k',v')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[balanced_map_invariant_def] THEN STRIP_TAC THEN
  MATCH_MP_TAC balanceL_thm THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`cmp:K->K->ordering`; `l:(K,V)balanced_map`] size_thm) THEN
  MP_TAC(ISPECL [`cmp:K->K->ordering`; `l':(K,V)balanced_map`] size_thm) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP almost_balancedL_thm) THEN
  SUBGOAL_THEN
   `balanced_map_size' (l':(K,V)balanced_map) = balanced_map_size' l \/
    balanced_map_size' l' = balanced_map_size' (l:(K,V)balanced_map) + 1`
  (DISJ_CASES_THEN SUBST1_TAC) THENL [ASM_ARITH_TAC; MESON_TAC[]; MESON_TAC[]]);;

let LIBXAUX_balanceR_ins = prove
 (`!(cmp:K->K->ordering) s k' (v':V) l r r'.
     good_cmp cmp /\ balanced_map_invariant cmp (Bin s k' v' l r) /\
     balanced_map_invariant cmp r' /\ key_ordered cmp k' r' LESS /\
     FCARD (to_fmap cmp r) <= FCARD (to_fmap cmp r') /\
     FCARD (to_fmap cmp r') <= FCARD (to_fmap cmp r) + 1
     ==> balanced_map_invariant cmp (balanceR k' v' l r') /\
         to_fmap cmp (balanceR k' v' l r') =
         FUNION (to_fmap cmp l) (to_fmap cmp r') |+ (key_set cmp k',v')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[balanced_map_invariant_def] THEN STRIP_TAC THEN
  MATCH_MP_TAC balanceR_thm THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`cmp:K->K->ordering`; `r:(K,V)balanced_map`] size_thm) THEN
  MP_TAC(ISPECL [`cmp:K->K->ordering`; `r':(K,V)balanced_map`] size_thm) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP almost_balancedR_thm) THEN
  SUBGOAL_THEN
   `balanced_map_size' (r':(K,V)balanced_map) = balanced_map_size' r \/
    balanced_map_size' r' = balanced_map_size' (r:(K,V)balanced_map) + 1`
  (DISJ_CASES_THEN SUBST1_TAC) THENL [ASM_ARITH_TAC; MESON_TAC[]; MESON_TAC[]]);;

let LIBXAUX_balanceR_del = prove
 (`!(cmp:K->K->ordering) s k' (v':V) l r l'.
     good_cmp cmp /\ balanced_map_invariant cmp (Bin s k' v' l r) /\
     balanced_map_invariant cmp l' /\ key_ordered cmp k' l' GREATER /\
     FCARD (to_fmap cmp l') <= FCARD (to_fmap cmp l) /\
     FCARD (to_fmap cmp l) <= FCARD (to_fmap cmp l') + 1
     ==> balanced_map_invariant cmp (balanceR k' v' l' r) /\
         to_fmap cmp (balanceR k' v' l' r) =
         FUNION (to_fmap cmp l') (to_fmap cmp r) |+ (key_set cmp k',v')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[balanced_map_invariant_def] THEN STRIP_TAC THEN
  MATCH_MP_TAC balanceR_thm THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`cmp:K->K->ordering`; `l:(K,V)balanced_map`] size_thm) THEN
  MP_TAC(ISPECL [`cmp:K->K->ordering`; `l':(K,V)balanced_map`] size_thm) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP almost_balancedR_thm) THEN
  SUBGOAL_THEN
   `balanced_map_size' (l':(K,V)balanced_map) = balanced_map_size' l \/
    balanced_map_size' l' = balanced_map_size' (l:(K,V)balanced_map) - 1`
  (DISJ_CASES_THEN SUBST1_TAC) THENL [ASM_ARITH_TAC; MESON_TAC[]; MESON_TAC[]]);;

let LIBXAUX_balanceL_del = prove
 (`!(cmp:K->K->ordering) s k' (v':V) l r r'.
     good_cmp cmp /\ balanced_map_invariant cmp (Bin s k' v' l r) /\
     balanced_map_invariant cmp r' /\ key_ordered cmp k' r' LESS /\
     FCARD (to_fmap cmp r') <= FCARD (to_fmap cmp r) /\
     FCARD (to_fmap cmp r) <= FCARD (to_fmap cmp r') + 1
     ==> balanced_map_invariant cmp (balanceL k' v' l r') /\
         to_fmap cmp (balanceL k' v' l r') =
         FUNION (to_fmap cmp l) (to_fmap cmp r') |+ (key_set cmp k',v')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[balanced_map_invariant_def] THEN STRIP_TAC THEN
  MATCH_MP_TAC balanceL_thm THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`cmp:K->K->ordering`; `r:(K,V)balanced_map`] size_thm) THEN
  MP_TAC(ISPECL [`cmp:K->K->ordering`; `r':(K,V)balanced_map`] size_thm) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP almost_balancedL_thm) THEN
  SUBGOAL_THEN
   `balanced_map_size' (r':(K,V)balanced_map) = balanced_map_size' r \/
    balanced_map_size' r' = balanced_map_size' (r:(K,V)balanced_map) - 1`
  (DISJ_CASES_THEN SUBST1_TAC) THENL [ASM_ARITH_TAC; MESON_TAC[]; MESON_TAC[]]);;
(* HOL4: insertR_thm, insertMax_thm, insertMin_thm *)

let LIBXAUX_INV_BIN_TAC =
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [balanced_map_invariant_def]);;

let insertR_thm = prove
 (`!(t:(K,V)balanced_map) (cmp:K->K->ordering) k v.
     good_cmp cmp /\ balanced_map_invariant cmp t
     ==> balanced_map_invariant cmp (insertR cmp k v t) /\
         to_fmap cmp (insertR cmp k v t) =
         (if key_set cmp k IN FDOM (to_fmap cmp t) then to_fmap cmp t
          else to_fmap cmp t |+ (key_set cmp k,v))`,
  MATCH_MP_TAC balanced_map_INDUCT THEN CONJ_TAC THENL
   [REWRITE_TAC[insertR_def; singleton_thm; to_fmap_def; FDOM_FEMPTY; NOT_IN_EMPTY];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:num`; `k':K`; `v':V`; `l:(K,V)balanced_map`;
                       `r:(K,V)balanced_map`] THEN
  DISCH_TAC THEN REPEAT GEN_TAC THEN
  POP_ASSUM(CONJUNCTS_THEN (MP_TAC o SPECL [`cmp:K->K->ordering`; `k:K`; `v:V`])) THEN
  DISCH_THEN(LABEL_TAC "ihr") THEN DISCH_THEN(LABEL_TAC "ihl") THEN
  STRIP_TAC THEN LIBXAUX_INV_BIN_TAC THEN
  MP_TAC(ISPECL [`cmp:K->K->ordering`; `s:num`; `k':K`; `v':V`;
                 `l:(K,V)balanced_map`; `r:(K,V)balanced_map`] inv_props) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REMOVE_THEN "ihl" MP_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REMOVE_THEN "ihr" MP_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[insertR_def; to_fmap_def; FDOM_FUPDATE; FDOM_FUNION; IN_INSERT;
              IN_UNION] THEN
  MP_TAC(ISPECL [`cmp:K->K->ordering`; `k:K`; `k':K`] LBMAPAUX_cmp_cases) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[ordering_case_def] THENL
   [(* LESS *)
    SUBGOAL_THEN `~(key_set (cmp:K->K->ordering) k = key_set cmp k') /\
                  ~(key_set cmp k IN FDOM (to_fmap cmp (r:(K,V)balanced_map)))`
      STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[key_set_eq] THEN
      ASM_MESON_TAC[LBMAPAUX_good_cmp; distinctness "ordering"];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`cmp:K->K->ordering`; `s:num`; `k':K`; `v':V`;
                   `l:(K,V)balanced_map`; `r:(K,V)balanced_map`;
                   `insertR (cmp:K->K->ordering) k (v:V) l`] LIBXAUX_balanceL_ins) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC LIBXAUX_ko_insert THEN
        MAP_EVERY EXISTS_TAC [`k:K`; `l:(K,V)balanced_map`] THEN
        ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN
        REWRITE_TAC[FDOM_FUPDATE] THEN SET_TAC[];
        COND_CASES_TAC THEN ASM_REWRITE_TAC[FCARD_FUPDATE] THEN ARITH_TAC];
      ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[FUNION_FUPDATE_1] THEN
    MATCH_MP_TAC FUPDATE_COMMUTES THEN ASM_MESON_TAC[];
    (* EQUAL *)
    SUBGOAL_THEN `key_set (cmp:K->K->ordering) k = key_set cmp k'` ASSUME_TAC THENL
     [ASM_SIMP_TAC[key_set_eq]; ALL_TAC] THEN
    ASM_REWRITE_TAC[to_fmap_def; balanced_map_invariant_def];
    (* GREATER *)
    SUBGOAL_THEN `~(key_set (cmp:K->K->ordering) k = key_set cmp k') /\
                  ~(key_set cmp k IN FDOM (to_fmap cmp (l:(K,V)balanced_map)))`
      STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[key_set_eq] THEN
      ASM_MESON_TAC[LBMAPAUX_good_cmp; distinctness "ordering"];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`cmp:K->K->ordering`; `s:num`; `k':K`; `v':V`;
                   `l:(K,V)balanced_map`; `r:(K,V)balanced_map`;
                   `insertR (cmp:K->K->ordering) k (v:V) r`] LIBXAUX_balanceR_ins) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC LIBXAUX_ko_insert THEN
        MAP_EVERY EXISTS_TAC [`k:K`; `r:(K,V)balanced_map`] THEN
        ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN
        REWRITE_TAC[FDOM_FUPDATE] THEN SET_TAC[];
        COND_CASES_TAC THEN ASM_REWRITE_TAC[FCARD_FUPDATE] THEN ARITH_TAC];
      ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[FUNION_FUPDATE_2] THEN
    MATCH_MP_TAC FUPDATE_COMMUTES THEN ASM_MESON_TAC[]]);;
let insertMax_thm = prove
 (`!(t:(K,V)balanced_map) (cmp:K->K->ordering) k v.
     good_cmp cmp /\ balanced_map_invariant cmp t /\
     (!k1. k1 IN FDOM (to_fmap cmp t) ==> key_set_cmp cmp k k1 GREATER)
     ==> balanced_map_invariant cmp (insertMax k v t) /\
         to_fmap cmp (insertMax k v t) = to_fmap cmp t |+ (key_set cmp k,v)`,
  MATCH_MP_TAC balanced_map_INDUCT THEN CONJ_TAC THENL
   [REWRITE_TAC[insertMax_def; singleton_thm; to_fmap_def]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:num`; `k':K`; `v':V`; `l:(K,V)balanced_map`;
                       `r:(K,V)balanced_map`] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[to_fmap_def; FDOM_FUPDATE; FDOM_FUNION; FORALL_IN_INSERT;
              FORALL_IN_UNION] THEN
  STRIP_TAC THEN LIBXAUX_INV_BIN_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`cmp:K->K->ordering`; `k:K`; `v:V`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(cmp:K->K->ordering) k' k = LESS` ASSUME_TAC THENL
   [ASM_MESON_TAC[key_set_cmp_thm; LBMAPAUX_good_cmp]; ALL_TAC] THEN
  SUBGOAL_THEN
   `~(key_set (cmp:K->K->ordering) k IN FDOM (to_fmap cmp (l:(K,V)balanced_map))) /\
    ~(key_set cmp k IN FDOM (to_fmap cmp (r:(K,V)balanced_map))) /\
    ~(key_set cmp k = key_set cmp k')`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[key_set_eq] THEN
    ASM_MESON_TAC[key_set_cmp_thm; LBMAPAUX_good_cmp; distinctness "ordering"];
    ALL_TAC] THEN
  REWRITE_TAC[insertMax_def] THEN
  MP_TAC(ISPECL [`cmp:K->K->ordering`; `s:num`; `k':K`; `v':V`;
                 `l:(K,V)balanced_map`; `r:(K,V)balanced_map`;
                 `insertMax (k:K) (v:V) r`] LIBXAUX_balanceR_ins) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[FCARD_FUPDATE] THEN CONJ_TAC THENL [ALL_TAC; ARITH_TAC] THEN
    MATCH_MP_TAC LIBXAUX_ko_insert THEN
    MAP_EVERY EXISTS_TAC [`k:K`; `r:(K,V)balanced_map`] THEN
    ASM_REWRITE_TAC[FDOM_FUPDATE; SUBSET_REFL];
    ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  ASM_REWRITE_TAC[FUNION_FUPDATE_2] THEN
  MATCH_MP_TAC FUPDATE_COMMUTES THEN ASM_MESON_TAC[]);;

let insertMin_thm = prove
 (`!(t:(K,V)balanced_map) (cmp:K->K->ordering) k v.
     good_cmp cmp /\ balanced_map_invariant cmp t /\
     (!k1. k1 IN FDOM (to_fmap cmp t) ==> key_set_cmp cmp k k1 LESS)
     ==> balanced_map_invariant cmp (insertMin k v t) /\
         to_fmap cmp (insertMin k v t) = to_fmap cmp t |+ (key_set cmp k,v)`,
  MATCH_MP_TAC balanced_map_INDUCT THEN CONJ_TAC THENL
   [REWRITE_TAC[insertMin_def; singleton_thm; to_fmap_def]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:num`; `k':K`; `v':V`; `l:(K,V)balanced_map`;
                       `r:(K,V)balanced_map`] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[to_fmap_def; FDOM_FUPDATE; FDOM_FUNION; FORALL_IN_INSERT;
              FORALL_IN_UNION] THEN
  STRIP_TAC THEN LIBXAUX_INV_BIN_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`cmp:K->K->ordering`; `k:K`; `v:V`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(cmp:K->K->ordering) k' k = GREATER` ASSUME_TAC THENL
   [ASM_MESON_TAC[key_set_cmp_thm; LBMAPAUX_good_cmp]; ALL_TAC] THEN
  SUBGOAL_THEN
   `~(key_set (cmp:K->K->ordering) k IN FDOM (to_fmap cmp (l:(K,V)balanced_map))) /\
    ~(key_set cmp k IN FDOM (to_fmap cmp (r:(K,V)balanced_map))) /\
    ~(key_set cmp k = key_set cmp k')`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[key_set_eq] THEN
    ASM_MESON_TAC[key_set_cmp_thm; LBMAPAUX_good_cmp; distinctness "ordering"];
    ALL_TAC] THEN
  REWRITE_TAC[insertMin_def] THEN
  MP_TAC(ISPECL [`cmp:K->K->ordering`; `s:num`; `k':K`; `v':V`;
                 `l:(K,V)balanced_map`; `r:(K,V)balanced_map`;
                 `insertMin (k:K) (v:V) l`] LIBXAUX_balanceL_ins) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[FCARD_FUPDATE] THEN CONJ_TAC THENL [ALL_TAC; ARITH_TAC] THEN
    MATCH_MP_TAC LIBXAUX_ko_insert THEN
    MAP_EVERY EXISTS_TAC [`k:K`; `l:(K,V)balanced_map`] THEN
    ASM_REWRITE_TAC[FDOM_FUPDATE; SUBSET_REFL];
    ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  ASM_REWRITE_TAC[FUNION_FUPDATE_1] THEN
  MATCH_MP_TAC FUPDATE_COMMUTES THEN ASM_MESON_TAC[]);;

(* ========================================================================= *)
(* HOL4 balanced_mapScript.sml lines 1703-2126: deleteFindMin,               *)
(* deleteFindMax, glue_thm, delete_thm and lookup_delete                     *)
(* (balanced_map_lookup_delete).  Proof route: the restriction DRESTRICT m   *)
(* (FDOM m DELETE ks) of the HOL4 statements is the domain subtraction m \\  *)
(* ks (LIBXAUX_B_DRESTRICT_DELETE), and the finite map facts are proved once *)
(* for any maps (the LIBXAUX_B_FUNION_DOMSUB lemmas) instead of pointwise in *)
(* each case as the HOL4 proofs do.  Removing a key from the left or right   *)
(* subtree and rebalancing is LIBXAUX_B_del_left and LIBXAUX_B_del_right;    *)
(* the two branches of glue are LIBXAUX_B_glue_max and LIBXAUX_B_glue_min.   *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Finite maps: restriction to the domain minus a key is domain subtraction; *)
(* the size and the union with one side keyless.                             *)
(* ------------------------------------------------------------------------- *)

let LIBXAUX_B_DRESTRICT_DELETE = prove
 (`!(f:(A,B)fmap) k. DRESTRICT f (FDOM f DELETE k) = f \\ k`,
  REWRITE_TAC[GSYM DRESTRICT_DOMSUB; DRESTRICT_FDOM]);;

let LIBXAUX_B_FCARD_DOMSUB = prove
 (`!(f:(A,B)fmap) k.
     FCARD (f \\ k) = if k IN FDOM f then FCARD f - 1 else FCARD f`,
  SIMP_TAC[FCARD_DEF; FDOM_DOMSUB; CARD_DELETE; FDOM_FINITE]);;

let LIBXAUX_B_FUNION_DOMSUB_1 = prove
 (`!(f:(A,B)fmap) g k.
     ~(k IN FDOM g) ==> FUNION (f \\ k) g = FUNION f g \\ k`,
  REWRITE_TAC[fmap_eq_flookup; FLOOKUP_FUNION; DOMSUB_FLOOKUP_THM;
              FDOM_FLOOKUP] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `x:A` THEN
  ASM_CASES_TAC `x:A = k` THEN ASM_REWRITE_TAC[option_CASE]);;

let LIBXAUX_B_FUNION_DOMSUB_2 = prove
 (`!(f:(A,B)fmap) g k.
     ~(k IN FDOM f) ==> FUNION f (g \\ k) = FUNION f g \\ k`,
  REWRITE_TAC[fmap_eq_flookup; FLOOKUP_FUNION; DOMSUB_FLOOKUP_THM;
              FDOM_FLOOKUP] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `x:A` THEN
  ASM_CASES_TAC `x:A = k` THEN ASM_REWRITE_TAC[option_CASE]);;

(* ------------------------------------------------------------------------- *)
(* Trees: facts from the invariant of a node, sizes after a domain           *)
(* subtraction, key ordering of subsets and of rebalanced nodes.             *)
(* ------------------------------------------------------------------------- *)

let LIBXAUX_B_inv_sub = prove
 (`!(cmp:K->K->ordering) s k (v:V) l r.
     balanced_map_invariant cmp (Bin s k v l r)
     ==> balanced_map_invariant cmp l /\ balanced_map_invariant cmp r`,
  SIMP_TAC[balanced_map_invariant_def]);;

let LIBXAUX_B_inv_bin = prove
 (`!(cmp:K->K->ordering) s k (v:V) l r.
     good_cmp cmp /\ balanced_map_invariant cmp (Bin s k v l r)
     ==> balanced_map_invariant cmp l /\ balanced_map_invariant cmp r /\
         key_ordered cmp k l GREATER /\ key_ordered cmp k r LESS /\
         balanced (balanced_map_size' l) (balanced_map_size' r) /\
         ~(key_set cmp k IN FDOM (to_fmap cmp l)) /\
         ~(key_set cmp k IN FDOM (to_fmap cmp r)) /\
         DISJOINT (FDOM (to_fmap cmp l)) (FDOM (to_fmap cmp r))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[invariant_eq]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let LIBXAUX_B_size_domsub = prove
 (`!(cmp:K->K->ordering) (t:(K,V)balanced_map) (t':(K,V)balanced_map) ks.
     good_cmp cmp /\ balanced_map_invariant cmp t /\
     balanced_map_invariant cmp t' /\ to_fmap cmp t' = to_fmap cmp t \\ ks
     ==> balanced_map_size' t' =
         if ks IN FDOM (to_fmap cmp t) then balanced_map_size' t - 1
         else balanced_map_size' t`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[size_thm; LIBXAUX_B_FCARD_DOMSUB]);;

let LIBXAUX_B_ko_bin = prove
 (`!(cmp:K->K->ordering) k k0 (x:V) (t:(K,V)balanced_map) l r res.
     good_cmp cmp /\
     to_fmap cmp t = FUNION (to_fmap cmp l) (to_fmap cmp r) |+ (key_set cmp k0,x) /\
     cmp k k0 = res /\ key_ordered cmp k l res /\ key_ordered cmp k r res
     ==> key_ordered cmp k t res`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY UNDISCH_TAC
   [`key_ordered (cmp:K->K->ordering) k (l:(K,V)balanced_map) res`;
    `key_ordered (cmp:K->K->ordering) k (r:(K,V)balanced_map) res`] THEN
  ASM_SIMP_TAC[key_ordered_to_fmap; FDOM_FUPDATE; FDOM_FUNION;
               FORALL_IN_INSERT; FORALL_IN_UNION; key_set_cmp_thm]);;

(* ------------------------------------------------------------------------- *)
(* Removing a key from the left or the right subtree of a node and           *)
(* rebalancing with balanceR or balanceL.                                    *)
(* ------------------------------------------------------------------------- *)

let LIBXAUX_B_del_left = prove
 (`!(cmp:K->K->ordering) s k0 (x:V) l r k l'.
     good_cmp cmp /\ balanced_map_invariant cmp (Bin s k0 x l r) /\
     balanced_map_invariant cmp l' /\
     to_fmap cmp l' = to_fmap cmp l \\ key_set cmp k /\
     cmp k k0 = LESS
     ==> balanced_map_invariant cmp (balanceR k0 x l' r) /\
         to_fmap cmp (balanceR k0 x l' r) =
         FUNION (to_fmap cmp l') (to_fmap cmp r) |+ (key_set cmp k0,x) /\
         to_fmap cmp (Bin s k0 x l r) \\ key_set cmp k =
         FUNION (to_fmap cmp l') (to_fmap cmp r) |+ (key_set cmp k0,x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`cmp:K->K->ordering`; `s:num`; `k0:K`; `x:V`;
                 `l:(K,V)balanced_map`; `r:(K,V)balanced_map`]
                LIBXAUX_B_inv_bin) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(cmp:K->K->ordering) k0 k = GREATER` ASSUME_TAC THENL
   [ASM_MESON_TAC[LBMAPAUX_good_cmp]; ALL_TAC] THEN
  SUBGOAL_THEN `~(key_set (cmp:K->K->ordering) k0 = key_set cmp k)`
    ASSUME_TAC THENL
   [ASM_SIMP_TAC[key_set_eq; ordering_eq_dec]; ALL_TAC] THEN
  SUBGOAL_THEN
   `~(key_set (cmp:K->K->ordering) k IN FDOM (to_fmap cmp (r:(K,V)balanced_map)))`
    ASSUME_TAC THENL
   [ASM_MESON_TAC[LBMAPAUX_key_ordered_FDOM; ordering_distinct]; ALL_TAC] THEN
  SUBGOAL_THEN `key_ordered (cmp:K->K->ordering) k0 (l':(K,V)balanced_map) GREATER`
    ASSUME_TAC THENL
   [MATCH_MP_TAC LIBXAUX_ko_sub THEN EXISTS_TAC `l:(K,V)balanced_map` THEN
    ASM_REWRITE_TAC[FDOM_DOMSUB; DELETE_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `almost_balancedR (balanced_map_size' (l':(K,V)balanced_map))
                                 (balanced_map_size' (r:(K,V)balanced_map))`
    ASSUME_TAC THENL
   [MP_TAC(ISPECL [`cmp:K->K->ordering`; `l:(K,V)balanced_map`;
                   `l':(K,V)balanced_map`; `key_set (cmp:K->K->ordering) k`]
                  LIBXAUX_B_size_domsub) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    COND_CASES_TAC THEN ASM_MESON_TAC[almost_balancedR_thm]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k0:K`; `x:V`; `l':(K,V)balanced_map`; `r:(K,V)balanced_map`;
                 `cmp:K->K->ordering`] balanceR_thm) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[to_fmap_def] THEN
  ASM_SIMP_TAC[DOMSUB_FUPDATE_NEQ; LIBXAUX_B_FUNION_DOMSUB_1]);;

let LIBXAUX_B_del_right = prove
 (`!(cmp:K->K->ordering) s k0 (x:V) l r k r'.
     good_cmp cmp /\ balanced_map_invariant cmp (Bin s k0 x l r) /\
     balanced_map_invariant cmp r' /\
     to_fmap cmp r' = to_fmap cmp r \\ key_set cmp k /\
     cmp k k0 = GREATER
     ==> balanced_map_invariant cmp (balanceL k0 x l r') /\
         to_fmap cmp (balanceL k0 x l r') =
         FUNION (to_fmap cmp l) (to_fmap cmp r') |+ (key_set cmp k0,x) /\
         to_fmap cmp (Bin s k0 x l r) \\ key_set cmp k =
         FUNION (to_fmap cmp l) (to_fmap cmp r') |+ (key_set cmp k0,x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`cmp:K->K->ordering`; `s:num`; `k0:K`; `x:V`;
                 `l:(K,V)balanced_map`; `r:(K,V)balanced_map`]
                LIBXAUX_B_inv_bin) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(cmp:K->K->ordering) k0 k = LESS` ASSUME_TAC THENL
   [ASM_MESON_TAC[LBMAPAUX_good_cmp]; ALL_TAC] THEN
  SUBGOAL_THEN `~(key_set (cmp:K->K->ordering) k0 = key_set cmp k)`
    ASSUME_TAC THENL
   [ASM_SIMP_TAC[key_set_eq; ordering_eq_dec]; ALL_TAC] THEN
  SUBGOAL_THEN
   `~(key_set (cmp:K->K->ordering) k IN FDOM (to_fmap cmp (l:(K,V)balanced_map)))`
    ASSUME_TAC THENL
   [ASM_MESON_TAC[LBMAPAUX_key_ordered_FDOM; ordering_distinct]; ALL_TAC] THEN
  SUBGOAL_THEN `key_ordered (cmp:K->K->ordering) k0 (r':(K,V)balanced_map) LESS`
    ASSUME_TAC THENL
   [MATCH_MP_TAC LIBXAUX_ko_sub THEN EXISTS_TAC `r:(K,V)balanced_map` THEN
    ASM_REWRITE_TAC[FDOM_DOMSUB; DELETE_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `almost_balancedL (balanced_map_size' (l:(K,V)balanced_map))
                                 (balanced_map_size' (r':(K,V)balanced_map))`
    ASSUME_TAC THENL
   [MP_TAC(ISPECL [`cmp:K->K->ordering`; `r:(K,V)balanced_map`;
                   `r':(K,V)balanced_map`; `key_set (cmp:K->K->ordering) k`]
                  LIBXAUX_B_size_domsub) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    COND_CASES_TAC THEN ASM_MESON_TAC[almost_balancedL_thm]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k0:K`; `x:V`; `l:(K,V)balanced_map`; `r':(K,V)balanced_map`;
                 `cmp:K->K->ordering`] balanceL_thm) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[to_fmap_def] THEN
  ASM_SIMP_TAC[DOMSUB_FUPDATE_NEQ; LIBXAUX_B_FUNION_DOMSUB_2]);;

let LIBXAUX_B_deleteFindMin_step = prove
 (`!(cmp:K->K->ordering) s k0 (x:V) l r k v l'.
     good_cmp cmp /\ balanced_map_invariant cmp (Bin s k0 x l r) /\
     balanced_map_invariant cmp l' /\ key_ordered cmp k l' LESS /\
     FLOOKUP (to_fmap cmp l) (key_set cmp k) = SOME v /\
     to_fmap cmp l' = to_fmap cmp l \\ key_set cmp k
     ==> balanced_map_invariant cmp (balanceR k0 x l' r) /\
         key_ordered cmp k (balanceR k0 x l' r) LESS /\
         FLOOKUP (to_fmap cmp (Bin s k0 x l r)) (key_set cmp k) = SOME v /\
         to_fmap cmp (balanceR k0 x l' r) =
         to_fmap cmp (Bin s k0 x l r) \\ key_set cmp k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`cmp:K->K->ordering`; `s:num`; `k0:K`; `x:V`;
                 `l:(K,V)balanced_map`; `r:(K,V)balanced_map`]
                LIBXAUX_B_inv_bin) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `key_set (cmp:K->K->ordering) k IN FDOM (to_fmap cmp (l:(K,V)balanced_map))`
    ASSUME_TAC THENL
   [ASM_REWRITE_TAC[FDOM_FLOOKUP; option_DISTINCT]; ALL_TAC] THEN
  SUBGOAL_THEN `(cmp:K->K->ordering) k0 k = GREATER` ASSUME_TAC THENL
   [ASM_MESON_TAC[LBMAPAUX_key_ordered_FDOM]; ALL_TAC] THEN
  SUBGOAL_THEN `(cmp:K->K->ordering) k k0 = LESS` ASSUME_TAC THENL
   [ASM_MESON_TAC[LBMAPAUX_good_cmp]; ALL_TAC] THEN
  SUBGOAL_THEN `~(key_set (cmp:K->K->ordering) k0 = key_set cmp k)`
    ASSUME_TAC THENL
   [ASM_SIMP_TAC[key_set_eq; ordering_eq_dec]; ALL_TAC] THEN
  MP_TAC(ISPECL [`cmp:K->K->ordering`; `s:num`; `k0:K`; `x:V`;
                 `l:(K,V)balanced_map`; `r:(K,V)balanced_map`; `k:K`;
                 `l':(K,V)balanced_map`] LIBXAUX_B_del_left) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LIBXAUX_B_ko_bin THEN
    MAP_EVERY EXISTS_TAC [`k0:K`; `x:V`; `l':(K,V)balanced_map`;
                          `r:(K,V)balanced_map`] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LBMAPAUX_key_ordered_trans THEN EXISTS_TAC `k0:K` THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[to_fmap_def; FLOOKUP_UPDATE; FLOOKUP_FUNION; option_CASE]]);;

let LIBXAUX_B_deleteFindMax_step = prove
 (`!(cmp:K->K->ordering) s k0 (x:V) l r k v r'.
     good_cmp cmp /\ balanced_map_invariant cmp (Bin s k0 x l r) /\
     balanced_map_invariant cmp r' /\ key_ordered cmp k r' GREATER /\
     FLOOKUP (to_fmap cmp r) (key_set cmp k) = SOME v /\
     to_fmap cmp r' = to_fmap cmp r \\ key_set cmp k
     ==> balanced_map_invariant cmp (balanceL k0 x l r') /\
         key_ordered cmp k (balanceL k0 x l r') GREATER /\
         FLOOKUP (to_fmap cmp (Bin s k0 x l r)) (key_set cmp k) = SOME v /\
         to_fmap cmp (balanceL k0 x l r') =
         to_fmap cmp (Bin s k0 x l r) \\ key_set cmp k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`cmp:K->K->ordering`; `s:num`; `k0:K`; `x:V`;
                 `l:(K,V)balanced_map`; `r:(K,V)balanced_map`]
                LIBXAUX_B_inv_bin) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `key_set (cmp:K->K->ordering) k IN FDOM (to_fmap cmp (r:(K,V)balanced_map))`
    ASSUME_TAC THENL
   [ASM_REWRITE_TAC[FDOM_FLOOKUP; option_DISTINCT]; ALL_TAC] THEN
  SUBGOAL_THEN `(cmp:K->K->ordering) k0 k = LESS` ASSUME_TAC THENL
   [ASM_MESON_TAC[LBMAPAUX_key_ordered_FDOM]; ALL_TAC] THEN
  SUBGOAL_THEN `(cmp:K->K->ordering) k k0 = GREATER` ASSUME_TAC THENL
   [ASM_MESON_TAC[LBMAPAUX_good_cmp]; ALL_TAC] THEN
  SUBGOAL_THEN `~(key_set (cmp:K->K->ordering) k0 = key_set cmp k)`
    ASSUME_TAC THENL
   [ASM_SIMP_TAC[key_set_eq; ordering_eq_dec]; ALL_TAC] THEN
  SUBGOAL_THEN `FLOOKUP (to_fmap (cmp:K->K->ordering) (l:(K,V)balanced_map))
                        (key_set cmp k) = NONE`
    ASSUME_TAC THENL
   [MATCH_MP_TAC LBMAPAUX_ko_NONE THEN
    MAP_EVERY EXISTS_TAC [`k0:K`; `GREATER`] THEN
    ASM_REWRITE_TAC[ordering_eq_dec]; ALL_TAC] THEN
  MP_TAC(ISPECL [`cmp:K->K->ordering`; `s:num`; `k0:K`; `x:V`;
                 `l:(K,V)balanced_map`; `r:(K,V)balanced_map`; `k:K`;
                 `r':(K,V)balanced_map`] LIBXAUX_B_del_right) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LIBXAUX_B_ko_bin THEN
    MAP_EVERY EXISTS_TAC [`k0:K`; `x:V`; `l:(K,V)balanced_map`;
                          `r':(K,V)balanced_map`] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LBMAPAUX_key_ordered_trans THEN EXISTS_TAC `k0:K` THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[to_fmap_def; FLOOKUP_UPDATE; FLOOKUP_FUNION; option_CASE]]);;

let LIBXAUX_B_SUBST_VAR_TAC =
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (is_var o rhs o concl)));;

(* ------------------------------------------------------------------------- *)
(* HOL4 deleteFindMin and deleteFindMax.                                     *)
(* ------------------------------------------------------------------------- *)

let deleteFindMin = prove
 (`!(cmp:K->K->ordering) (t:(K,V)balanced_map) t' k v.
     good_cmp cmp /\ balanced_map_invariant cmp t /\ ~null t /\
     deleteFindMin t = ((k,v),t')
     ==> balanced_map_invariant cmp t' /\
         key_ordered cmp k t' LESS /\
         FLOOKUP (to_fmap cmp t) (key_set cmp k) = SOME v /\
         to_fmap cmp t' =
         DRESTRICT (to_fmap cmp t) (FDOM (to_fmap cmp t) DELETE key_set cmp k)`,
  GEN_TAC THEN REWRITE_TAC[LIBXAUX_B_DRESTRICT_DELETE] THEN
  MATCH_MP_TAC deleteFindMin_ind THEN REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`s:num`; `k0:K`; `x:V`; `r:(K,V)balanced_map`;
                         `t':(K,V)balanced_map`; `k:K`; `v:V`] THEN
    REWRITE_TAC[deleteFindMin_def; PAIR_EQ] THEN STRIP_TAC THEN
    LIBXAUX_B_SUBST_VAR_TAC THEN
    MP_TAC(ISPECL [`cmp:K->K->ordering`; `s:num`; `k0:K`; `x:V`;
                   `Tip:(K,V)balanced_map`; `r:(K,V)balanced_map`]
                  LIBXAUX_B_inv_bin) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[to_fmap_def; FUNION_FEMPTY_1; FLOOKUP_UPDATE; DOMSUB_FUPDATE;
                 DOMSUB_NOT_IN_DOM];
    MAP_EVERY X_GEN_TAC [`s:num`; `k0:K`; `x:V`; `s1:num`; `k1:K`; `x1:V`;
                         `l1:(K,V)balanced_map`; `r1:(K,V)balanced_map`;
                         `r:(K,V)balanced_map`] THEN
    DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`t':(K,V)balanced_map`; `k:K`; `v:V`] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `?k2 (v2:V) (l':(K,V)balanced_map).
                    deleteFindMin (Bin s1 k1 (x1:V) l1 r1) = ((k2:K,v2),l')`
      STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR_SURJECTIVE]; ALL_TAC] THEN
    UNDISCH_TAC
     `deleteFindMin (Bin s k0 (x:V) (Bin s1 k1 x1 l1 r1) r) = ((k:K,v),t')` THEN
    ASM_REWRITE_TAC[deleteFindMin_def; pair_CASE; PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN SUBST_ALL_TAC)
                               (SUBST_ALL_TAC o SYM)) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`l':(K,V)balanced_map`; `k:K`; `v:V`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[null_def] THEN ASM_MESON_TAC[LIBXAUX_B_inv_sub];
      ALL_TAC] THEN
    STRIP_TAC THEN MATCH_MP_TAC LIBXAUX_B_deleteFindMin_step THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[null_def]]);;

let deleteFindMax = prove
 (`!(cmp:K->K->ordering) (t:(K,V)balanced_map) t' k v.
     good_cmp cmp /\ balanced_map_invariant cmp t /\ ~null t /\
     deleteFindMax t = ((k,v),t')
     ==> balanced_map_invariant cmp t' /\
         key_ordered cmp k t' GREATER /\
         FLOOKUP (to_fmap cmp t) (key_set cmp k) = SOME v /\
         to_fmap cmp t' =
         DRESTRICT (to_fmap cmp t) (FDOM (to_fmap cmp t) DELETE key_set cmp k)`,
  GEN_TAC THEN REWRITE_TAC[LIBXAUX_B_DRESTRICT_DELETE] THEN
  MATCH_MP_TAC deleteFindMax_ind THEN REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`s:num`; `k0:K`; `x:V`; `l:(K,V)balanced_map`;
                         `t':(K,V)balanced_map`; `k:K`; `v:V`] THEN
    REWRITE_TAC[deleteFindMax_def; PAIR_EQ] THEN STRIP_TAC THEN
    LIBXAUX_B_SUBST_VAR_TAC THEN
    MP_TAC(ISPECL [`cmp:K->K->ordering`; `s:num`; `k0:K`; `x:V`;
                   `l:(K,V)balanced_map`; `Tip:(K,V)balanced_map`]
                  LIBXAUX_B_inv_bin) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[to_fmap_def; FUNION_FEMPTY_2; FLOOKUP_UPDATE; DOMSUB_FUPDATE;
                 DOMSUB_NOT_IN_DOM];
    MAP_EVERY X_GEN_TAC [`s:num`; `k0:K`; `x:V`; `l:(K,V)balanced_map`;
                         `s1:num`; `k1:K`; `x1:V`;
                         `l1:(K,V)balanced_map`; `r1:(K,V)balanced_map`] THEN
    DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`t':(K,V)balanced_map`; `k:K`; `v:V`] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `?k2 (v2:V) (r':(K,V)balanced_map).
                    deleteFindMax (Bin s1 k1 (x1:V) l1 r1) = ((k2:K,v2),r')`
      STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR_SURJECTIVE]; ALL_TAC] THEN
    UNDISCH_TAC
     `deleteFindMax (Bin s k0 (x:V) l (Bin s1 k1 x1 l1 r1)) = ((k:K,v),t')` THEN
    ASM_REWRITE_TAC[deleteFindMax_def; pair_CASE; PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN SUBST_ALL_TAC)
                               (SUBST_ALL_TAC o SYM)) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`r':(K,V)balanced_map`; `k:K`; `v:V`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[null_def] THEN ASM_MESON_TAC[LIBXAUX_B_inv_sub];
      ALL_TAC] THEN
    STRIP_TAC THEN MATCH_MP_TAC LIBXAUX_B_deleteFindMax_step THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[null_def]]);;

(* ------------------------------------------------------------------------- *)
(* HOL4 glue_thm (HOL4 glue is balanced_map_glue).                           *)
(* ------------------------------------------------------------------------- *)

let LIBXAUX_B_FUNION_DOMSUB_FUPDATE_1 = prove
 (`!(f:(A,B)fmap) g k v.
     FLOOKUP f k = SOME v ==> FUNION (f \\ k) g |+ (k,v) = FUNION f g`,
  REWRITE_TAC[fmap_eq_flookup; FLOOKUP_UPDATE; FLOOKUP_FUNION;
              DOMSUB_FLOOKUP_THM] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `x:A` THEN
  ASM_CASES_TAC `x:A = k` THEN ASM_REWRITE_TAC[option_CASE]);;

let LIBXAUX_B_FUNION_DOMSUB_FUPDATE_2 = prove
 (`!(f:(A,B)fmap) g k v.
     FLOOKUP g k = SOME v /\ ~(k IN FDOM f)
     ==> FUNION f (g \\ k) |+ (k,v) = FUNION f g`,
  REWRITE_TAC[fmap_eq_flookup; FLOOKUP_UPDATE; FLOOKUP_FUNION;
              DOMSUB_FLOOKUP_THM; FDOM_FLOOKUP] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `x:A` THEN
  ASM_CASES_TAC `x:A = k` THEN ASM_REWRITE_TAC[option_CASE]);;

let LIBXAUX_B_ko_cmp2_l = prove
 (`!(cmp:K->K->ordering) k (l:(K,V)balanced_map) (r:(K,V)balanced_map).
     good_cmp cmp /\
     (!ks ks'. ks IN FDOM (to_fmap cmp l) /\ ks' IN FDOM (to_fmap cmp r)
               ==> key_set_cmp2 cmp ks ks' LESS) /\
     key_set cmp k IN FDOM (to_fmap cmp l)
     ==> key_ordered cmp k r LESS`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[key_ordered_to_fmap] THEN
  X_GEN_TAC `ks:K->bool` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP to_fmap_key_set) THEN
  DISCH_THEN(X_CHOOSE_THEN `k2:K` SUBST_ALL_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`key_set (cmp:K->K->ordering) k`;
                                `key_set (cmp:K->K->ordering) k2`]) THEN
  ASM_SIMP_TAC[key_set_cmp_thm; key_set_cmp2_thm]);;

let LIBXAUX_B_ko_cmp2_r = prove
 (`!(cmp:K->K->ordering) k (l:(K,V)balanced_map) (r:(K,V)balanced_map).
     good_cmp cmp /\
     (!ks ks'. ks IN FDOM (to_fmap cmp l) /\ ks' IN FDOM (to_fmap cmp r)
               ==> key_set_cmp2 cmp ks ks' LESS) /\
     key_set cmp k IN FDOM (to_fmap cmp r)
     ==> key_ordered cmp k l GREATER`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[key_ordered_to_fmap] THEN
  X_GEN_TAC `ks:K->bool` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP to_fmap_key_set) THEN
  DISCH_THEN(X_CHOOSE_THEN `k1:K` SUBST_ALL_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`key_set (cmp:K->K->ordering) k1`;
                                `key_set (cmp:K->K->ordering) k`]) THEN
  ASM_SIMP_TAC[key_set_cmp_thm; key_set_cmp2_thm] THEN
  ASM_MESON_TAC[LBMAPAUX_good_cmp]);;

let LIBXAUX_B_glue_max = prove
 (`!(cmp:K->K->ordering) (l:(K,V)balanced_map) r km m l'.
     good_cmp cmp /\ balanced_map_invariant cmp l /\
     balanced_map_invariant cmp r /\
     (!ks ks'. ks IN FDOM (to_fmap cmp l) /\ ks' IN FDOM (to_fmap cmp r)
               ==> key_set_cmp2 cmp ks ks' LESS) /\
     balanced (balanced_map_size' l) (balanced_map_size' r) /\
     ~null l /\ deleteFindMax l = ((km,m),l')
     ==> balanced_map_invariant cmp (balanceR km m l' r) /\
         to_fmap cmp (balanceR km m l' r) =
         FUNION (to_fmap cmp l) (to_fmap cmp r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`cmp:K->K->ordering`; `l:(K,V)balanced_map`;
                 `l':(K,V)balanced_map`; `km:K`; `m:V`] deleteFindMax) THEN
  ASM_REWRITE_TAC[LIBXAUX_B_DRESTRICT_DELETE] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `key_set (cmp:K->K->ordering) km IN FDOM (to_fmap cmp (l:(K,V)balanced_map))`
    ASSUME_TAC THENL
   [ASM_REWRITE_TAC[FDOM_FLOOKUP; option_DISTINCT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`km:K`; `m:V`; `l':(K,V)balanced_map`; `r:(K,V)balanced_map`;
                 `cmp:K->K->ordering`] balanceR_thm) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC LIBXAUX_B_ko_cmp2_l THEN EXISTS_TAC `l:(K,V)balanced_map` THEN
      ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`cmp:K->K->ordering`; `l:(K,V)balanced_map`;
                     `l':(K,V)balanced_map`; `key_set (cmp:K->K->ordering) km`]
                    LIBXAUX_B_size_domsub) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      ASM_MESON_TAC[almost_balancedR_thm]];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC LIBXAUX_B_FUNION_DOMSUB_FUPDATE_1 THEN ASM_REWRITE_TAC[]);;

let LIBXAUX_B_glue_min = prove
 (`!(cmp:K->K->ordering) (l:(K,V)balanced_map) r km m r'.
     good_cmp cmp /\ balanced_map_invariant cmp l /\
     balanced_map_invariant cmp r /\
     (!ks ks'. ks IN FDOM (to_fmap cmp l) /\ ks' IN FDOM (to_fmap cmp r)
               ==> key_set_cmp2 cmp ks ks' LESS) /\
     balanced (balanced_map_size' l) (balanced_map_size' r) /\
     ~null r /\ deleteFindMin r = ((km,m),r')
     ==> balanced_map_invariant cmp (balanceL km m l r') /\
         to_fmap cmp (balanceL km m l r') =
         FUNION (to_fmap cmp l) (to_fmap cmp r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`cmp:K->K->ordering`; `r:(K,V)balanced_map`;
                 `r':(K,V)balanced_map`; `km:K`; `m:V`] deleteFindMin) THEN
  ASM_REWRITE_TAC[LIBXAUX_B_DRESTRICT_DELETE] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `key_set (cmp:K->K->ordering) km IN FDOM (to_fmap cmp (r:(K,V)balanced_map))`
    ASSUME_TAC THENL
   [ASM_REWRITE_TAC[FDOM_FLOOKUP; option_DISTINCT]; ALL_TAC] THEN
  SUBGOAL_THEN `key_ordered (cmp:K->K->ordering) km (l:(K,V)balanced_map) GREATER`
    ASSUME_TAC THENL
   [MATCH_MP_TAC LIBXAUX_B_ko_cmp2_r THEN EXISTS_TAC `r:(K,V)balanced_map` THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`km:K`; `m:V`; `l:(K,V)balanced_map`; `r':(K,V)balanced_map`;
                 `cmp:K->K->ordering`] balanceL_thm) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`cmp:K->K->ordering`; `r:(K,V)balanced_map`;
                   `r':(K,V)balanced_map`; `key_set (cmp:K->K->ordering) km`]
                  LIBXAUX_B_size_domsub) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_MESON_TAC[almost_balancedL_thm];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC LIBXAUX_B_FUNION_DOMSUB_FUPDATE_2 THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[LBMAPAUX_key_ordered_FDOM; LBMAPAUX_good_cmp; ordering_distinct]);;

let glue_thm = prove
 (`!(cmp:K->K->ordering) (l:(K,V)balanced_map) r.
     good_cmp cmp /\ balanced_map_invariant cmp l /\
     balanced_map_invariant cmp r /\
     (!ks ks'. ks IN FDOM (to_fmap cmp l) /\ ks' IN FDOM (to_fmap cmp r)
               ==> key_set_cmp2 cmp ks ks' LESS) /\
     balanced (balanced_map_size' l) (balanced_map_size' r)
     ==> balanced_map_invariant cmp (balanced_map_glue l r) /\
         to_fmap cmp (balanced_map_glue l r) =
         FUNION (to_fmap cmp l) (to_fmap cmp r)`,
  REPEAT GEN_TAC THEN
  LBMAPAUX_BM_CASES_TAC `l:(K,V)balanced_map`
    [`n:num`; `k:K`; `v:V`; `b:(K,V)balanced_map`; `b0:(K,V)balanced_map`] THEN
  LBMAPAUX_BM_CASES_TAC `r:(K,V)balanced_map`
    [`n':num`; `k':K`; `v':V`; `b':(K,V)balanced_map`;
     `b0':(K,V)balanced_map`] THEN
  REWRITE_TAC[balanced_map_glue_def] THENL
   [REWRITE_TAC[to_fmap_def; FUNION_FEMPTY_1; balanced_map_invariant_def];
    REWRITE_TAC[to_fmap_def; FUNION_FEMPTY_1] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[to_fmap_def; FUNION_FEMPTY_2] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN COND_CASES_TAC THENL
   [SUBGOAL_THEN `?km (m:V) (l':(K,V)balanced_map).
                    deleteFindMax (Bin n k (v:V) b b0) = ((km:K,m),l')`
      STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR_SURJECTIVE]; ALL_TAC] THEN
    ASM_REWRITE_TAC[pair_CASE] THEN MATCH_MP_TAC LIBXAUX_B_glue_max THEN
    ASM_REWRITE_TAC[null_def];
    SUBGOAL_THEN `?km (m:V) (r':(K,V)balanced_map).
                    deleteFindMin (Bin n' k' (v':V) b' b0') = ((km:K,m),r')`
      STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR_SURJECTIVE]; ALL_TAC] THEN
    ASM_REWRITE_TAC[pair_CASE] THEN MATCH_MP_TAC LIBXAUX_B_glue_min THEN
    ASM_REWRITE_TAC[null_def]]);;

(* ------------------------------------------------------------------------- *)
(* HOL4 delete_thm and lookup_delete (HOL4 delete is balanced_map_delete).   *)
(* ------------------------------------------------------------------------- *)

let LIBXAUX_B_inv_cmp2 = prove
 (`!(cmp:K->K->ordering) s k (v:V) l r.
     good_cmp cmp /\ balanced_map_invariant cmp (Bin s k v l r)
     ==> !ks ks'. ks IN FDOM (to_fmap cmp l) /\ ks' IN FDOM (to_fmap cmp r)
                  ==> key_set_cmp2 cmp ks ks' LESS`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP inv_props) THEN
  MAP_EVERY X_GEN_TAC [`ks1:K->bool`; `ks2:K->bool`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`cmp:K->K->ordering`; `ks1:K->bool`; `l:(K,V)balanced_map`]
                to_fmap_key_set) THEN
  MP_TAC(ISPECL [`cmp:K->K->ordering`; `ks2:K->bool`; `r:(K,V)balanced_map`]
                to_fmap_key_set) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k2:K` SUBST_ALL_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `k1:K` SUBST_ALL_TAC) THEN
  ASM_SIMP_TAC[key_set_cmp2_thm] THEN
  SUBGOAL_THEN `(cmp:K->K->ordering) k k1 = GREATER /\ cmp k k2 = LESS`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_MESON_TAC[LBMAPAUX_good_cmp]);;

let delete_thm = prove
 (`!(cmp:K->K->ordering) k (t:(K,V)balanced_map).
     good_cmp cmp /\ balanced_map_invariant cmp t
     ==> balanced_map_invariant cmp (balanced_map_delete cmp k t) /\
         to_fmap cmp (balanced_map_delete cmp k t) =
         DRESTRICT (to_fmap cmp t) (FDOM (to_fmap cmp t) DELETE key_set cmp k)`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[LIBXAUX_B_DRESTRICT_DELETE] THEN
  MATCH_MP_TAC balanced_map_INDUCT THEN CONJ_TAC THENL
   [REWRITE_TAC[balanced_map_delete_def; to_fmap_def; DOMSUB_FEMPTY;
                balanced_map_invariant_def];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:num`; `k':K`; `v:V`; `l:(K,V)balanced_map`;
                       `r:(K,V)balanced_map`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ihl") (LABEL_TAC "ihr")) THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`cmp:K->K->ordering`; `s:num`; `k':K`; `v:V`;
                 `l:(K,V)balanced_map`; `r:(K,V)balanced_map`]
                LIBXAUX_B_inv_bin) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REMOVE_THEN "ihl" MP_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REMOVE_THEN "ihr" MP_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[balanced_map_delete_def] THEN
  MP_TAC(ISPECL [`cmp:K->K->ordering`; `k:K`; `k':K`] LBMAPAUX_cmp_cases) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[ordering_case_def] THENL
   [MP_TAC(ISPECL [`cmp:K->K->ordering`; `s:num`; `k':K`; `v:V`;
                   `l:(K,V)balanced_map`; `r:(K,V)balanced_map`; `k:K`;
                   `balanced_map_delete (cmp:K->K->ordering) k
                      (l:(K,V)balanced_map)`] LIBXAUX_B_del_left) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`cmp:K->K->ordering`; `l:(K,V)balanced_map`;
                   `r:(K,V)balanced_map`] glue_thm) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LIBXAUX_B_inv_cmp2 THEN
      MAP_EVERY EXISTS_TAC [`s:num`; `k':K`; `v:V`] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `key_set (cmp:K->K->ordering) k = key_set cmp k'`
      SUBST1_TAC THENL [ASM_SIMP_TAC[key_set_eq]; ALL_TAC] THEN
    REWRITE_TAC[to_fmap_def; DOMSUB_FUPDATE] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC DOMSUB_NOT_IN_DOM THEN
    ASM_REWRITE_TAC[FDOM_FUNION; IN_UNION];
    MP_TAC(ISPECL [`cmp:K->K->ordering`; `s:num`; `k':K`; `v:V`;
                   `l:(K,V)balanced_map`; `r:(K,V)balanced_map`; `k:K`;
                   `balanced_map_delete (cmp:K->K->ordering) k
                      (r:(K,V)balanced_map)`] LIBXAUX_B_del_right) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]]);;

(* HOL4: lookup_delete (sptree has lookup_delete) *)

let balanced_map_lookup_delete = prove
 (`!(cmp:K->K->ordering) (t:(K,V)balanced_map) k k'.
     good_cmp cmp /\ balanced_map_invariant cmp t
     ==> balanced_map_lookup cmp k (balanced_map_delete cmp k' t) =
         if cmp k k' = EQUAL then NONE else balanced_map_lookup cmp k t`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`cmp:K->K->ordering`; `k':K`; `t:(K,V)balanced_map`]
                delete_thm) THEN
  ASM_REWRITE_TAC[LIBXAUX_B_DRESTRICT_DELETE] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[lookup_thm; DOMSUB_FLOOKUP_THM; key_set_eq] THEN
  SUBGOAL_THEN `(cmp:K->K->ordering) k' k = EQUAL <=> cmp k k' = EQUAL`
    SUBST1_TAC THENL [ASM_MESON_TAC[LBMAPAUX_good_cmp]; REWRITE_TAC[]]);;

(* ========================================================================= *)
(* HOL4 balanced_mapScript.sml lines 2127-2215: restrict_set,                *)
(* restrict_domain (defined above) and trim_thm, with the pointwise helpers  *)
(* used from here on (they replace the local lemmas restrict_domain_union,   *)
(* restrict_domain_update and restrict_domain_FMERGE_WITH_KEY).              *)
(* ========================================================================= *)

let LIBXAUX_to_fmap_Bin = prove
 (`!(cmp:K->K->ordering) s k (v:V) l r.
     to_fmap cmp (Bin s k v l r) =
     FUNION (to_fmap cmp l) (to_fmap cmp r) |+ (key_set cmp k,v)`,
  REWRITE_TAC[to_fmap_def]);;

(* ------------------------------------------------------------------------- *)
(* Helpers for pointwise reasoning: the finite maps of trees are equal when *)
(* their lookups at every key_set cmp k agree (their domains hold only key  *)
(* sets), and the lookups of to_fmap, restrict_domain, FUNION and |+ at a    *)
(* key_set are balanced_map_lookup, a range test, and so on.                 *)
(* ------------------------------------------------------------------------- *)

let LIBXAUX_FMAP_EXT_KEYS = prove
 (`!(cmp:K->K->ordering) (m1:(K->bool,V)fmap) m2.
     (!x. x IN FDOM m1 ==> ?k. x = key_set cmp k) /\
     (!x. x IN FDOM m2 ==> ?k. x = key_set cmp k) /\
     (!k. FLOOKUP m1 (key_set cmp k) = FLOOKUP m2 (key_set cmp k))
     ==> m1 = m2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fmap_eq_flookup] THEN X_GEN_TAC `x:K->bool` THEN
  ASM_CASES_TAC `?k. (x:K->bool) = key_set cmp k` THENL
   [FIRST_X_ASSUM(CHOOSE_THEN SUBST1_TAC) THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `~((x:K->bool) IN FDOM (m1:(K->bool,V)fmap)) /\ ~(x IN FDOM (m2:(K->bool,V)fmap))`
      MP_TAC THENL [ASM_MESON_TAC[]; REWRITE_TAC[GSYM flookup_thm]] THEN
    SIMP_TAC[]]);;

let LIBXAUX_restrict_set_cmp = prove
 (`!(cmp:K->K->ordering) lo hi k1 k2.
     good_cmp cmp /\ cmp k1 k2 = EQUAL
     ==> (k1 IN restrict_set cmp lo hi <=> k2 IN restrict_set cmp lo hi)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[restrict_set_def; IN_ELIM_THM] THEN
  MAP_EVERY (fun t -> STRUCT_CASES_TAC(ISPEC t (cases "option")))
    [`lo:K option`; `hi:K option`] THEN
  REWRITE_TAC[option_compare_def; option_cmp2_def] THEN
  ASM_MESON_TAC[LBMAPAUX_good_cmp]);;

let LIBXAUX_FLOOKUP_restrict = prove
 (`!(cmp:K->K->ordering) lo hi (m:(K->bool,V)fmap) k.
     good_cmp cmp
     ==> FLOOKUP (restrict_domain cmp lo hi m) (key_set cmp k) =
         if k IN restrict_set cmp lo hi then FLOOKUP m (key_set cmp k) else NONE`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[restrict_domain_def; FLOOKUP_DRESTRICT] THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
  EQ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  DISCH_THEN(X_CHOOSE_THEN `k2:K` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`cmp:K->K->ordering`; `lo:K option`; `hi:K option`; `k:K`; `k2:K`]
         LIBXAUX_restrict_set_cmp) THEN
  ASM_MESON_TAC[key_set_eq]);;

let LIBXAUX_FLOOKUP_UPDATE_key = prove
 (`!(cmp:K->K->ordering) (m:(K->bool,V)fmap) k1 v k.
     good_cmp cmp
     ==> FLOOKUP (m |+ (key_set cmp k1,v)) (key_set cmp k) =
         if cmp k1 k = EQUAL then SOME v else FLOOKUP m (key_set cmp k)`,
  SIMP_TAC[FLOOKUP_UPDATE; key_set_eq]);;

let LIBXAUX_FLOOKUP_to_fmap = prove
 (`!(cmp:K->K->ordering) (t:(K,V)balanced_map) k.
     good_cmp cmp /\ balanced_map_invariant cmp t
     ==> FLOOKUP (to_fmap cmp t) (key_set cmp k) = balanced_map_lookup cmp k t`,
  SIMP_TAC[lookup_thm]);;

let LIBXAUX_FDOM_restrict = prove
 (`!(cmp:K->K->ordering) lo hi (m:(K->bool,V)fmap).
     FDOM (restrict_domain cmp lo hi m) =
     FDOM m INTER IMAGE (key_set cmp) (restrict_set cmp lo hi)`,
  REWRITE_TAC[restrict_domain_def; FDOM_DRESTRICT]);;

(* lookups outside the keys a tree holds *)

let LIBXAUX_lookup_ko = prove
 (`!(cmp:K->K->ordering) a (t:(K,V)balanced_map) res k.
     good_cmp cmp /\ balanced_map_invariant cmp t /\ key_ordered cmp a t res /\
     ~(cmp a k = res)
     ==> balanced_map_lookup cmp k t = NONE`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[lookup_thm] THEN
  MATCH_MP_TAC LBMAPAUX_ko_NONE THEN ASM_MESON_TAC[]);;

let LIBXAUX_lookup_bounded = prove
 (`!(t:(K,V)balanced_map) (cmp:K->K->ordering) lo hi k.
     good_cmp cmp /\ bounded_all cmp lo hi t /\ ~(k IN restrict_set cmp lo hi)
     ==> balanced_map_lookup cmp k t = NONE`,
  MATCH_MP_TAC balanced_map_INDUCT THEN
  REWRITE_TAC[balanced_map_lookup_def; bounded_all_def] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`cmp:K->K->ordering`; `k:K`; `a1:K`] LBMAPAUX_cmp_cases) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[ordering_case_def] THEN
  TRY(FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[] THEN NO_TAC) THEN
  ASM_MESON_TAC[LIBXAUX_restrict_set_cmp]);;

(* the ranges of restrict_set *)

let LIBXAUX_IN_restrict_set = prove
 (`(!(cmp:K->K->ordering) k. k IN restrict_set cmp NONE NONE) /\
   (!(cmp:K->K->ordering) lo k.
      k IN restrict_set cmp (SOME lo) NONE <=> cmp lo k = LESS) /\
   (!(cmp:K->K->ordering) hi k.
      k IN restrict_set cmp NONE (SOME hi) <=> cmp k hi = LESS) /\
   (!(cmp:K->K->ordering) lo hi k.
      k IN restrict_set cmp (SOME lo) (SOME hi) <=>
      cmp lo k = LESS /\ cmp k hi = LESS)`,
  REWRITE_TAC[restrict_set_def; IN_ELIM_THM; option_compare_def; option_cmp2_def]);;

let LIBXAUX_range_lt = prove
 (`!(cmp:K->K->ordering) blo bhi kx k.
     good_cmp cmp /\ kx IN restrict_set cmp blo bhi /\ cmp k kx = LESS
     ==> (k IN restrict_set cmp blo (SOME kx) <=> k IN restrict_set cmp blo bhi)`,
  REPEAT GEN_TAC THEN
  MAP_EVERY (fun t -> STRUCT_CASES_TAC(ISPEC t (cases "option")))
    [`blo:K option`; `bhi:K option`] THEN
  REWRITE_TAC[LIBXAUX_IN_restrict_set] THEN ASM_MESON_TAC[LBMAPAUX_good_cmp]);;

let LIBXAUX_range_gt = prove
 (`!(cmp:K->K->ordering) blo bhi kx k.
     good_cmp cmp /\ kx IN restrict_set cmp blo bhi /\ cmp kx k = LESS
     ==> (k IN restrict_set cmp (SOME kx) bhi <=> k IN restrict_set cmp blo bhi)`,
  REPEAT GEN_TAC THEN
  MAP_EVERY (fun t -> STRUCT_CASES_TAC(ISPEC t (cases "option")))
    [`blo:K option`; `bhi:K option`] THEN
  REWRITE_TAC[LIBXAUX_IN_restrict_set] THEN ASM_MESON_TAC[LBMAPAUX_good_cmp]);;

let LIBXAUX_range_bound = prove
 (`(!(cmp:K->K->ordering) lo hi k.
      k IN restrict_set cmp lo (SOME hi) ==> cmp k hi = LESS) /\
   (!(cmp:K->K->ordering) lo hi k.
      k IN restrict_set cmp (SOME lo) hi ==> cmp lo k = LESS)`,
  CONJ_TAC THEN REPEAT GEN_TAC THENL
   [STRUCT_CASES_TAC(ISPEC `lo:K option` (cases "option"));
    STRUCT_CASES_TAC(ISPEC `hi:K option` (cases "option"))] THEN
  REWRITE_TAC[LIBXAUX_IN_restrict_set] THEN SIMP_TAC[]);;
let LIBXAUX_bounded_root = prove
 (`(!(cmp:K->K->ordering) lk hk.
      bounded_root cmp lk hk (Tip:(K,V)balanced_map) <=> T) /\
   (!(cmp:K->K->ordering) lk hk s k (v:V) l r.
      bounded_root cmp lk hk (Bin s k v l r) <=> k IN restrict_set cmp lk hk)`,
  REWRITE_TAC[bounded_root_def; distinctness "balanced_map";
              injectivity "balanced_map"] THEN
  MESON_TAC[]);;

let LIBXAUX_SUBMAP_Bin = prove
 (`!(cmp:K->K->ordering) s k (v:V) l r.
     good_cmp cmp /\ balanced_map_invariant cmp (Bin s k v l r)
     ==> to_fmap cmp l SUBMAP to_fmap cmp (Bin s k v l r) /\
         to_fmap cmp r SUBMAP to_fmap cmp (Bin s k v l r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`cmp:K->K->ordering`; `s:num`; `k:K`; `v:V`;
                 `l:(K,V)balanced_map`; `r:(K,V)balanced_map`]
                (CONJUNCT2 invariant_eq)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[SUBMAP_FLOOKUP_EQN; LIBXAUX_to_fmap_Bin; FLOOKUP_UPDATE;
              FLOOKUP_FUNION] THEN
  CONJ_TAC THEN MAP_EVERY X_GEN_TAC [`x:K->bool`; `y:V`] THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FMAPAUX_FLOOKUP_SOME_FDOM) THEN
  SUBGOAL_THEN `~(key_set (cmp:K->K->ordering) k = x)` (fun th -> REWRITE_TAC[th]) THENL
   [DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[];
    ASM_REWRITE_TAC[option_CASE];
    DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[];
    SUBGOAL_THEN `FLOOKUP (to_fmap (cmp:K->K->ordering) (l:(K,V)balanced_map)) x = NONE`
      SUBST1_TAC THENL
     [REWRITE_TAC[flookup_thm] THEN ASM SET_TAC[]; ASM_REWRITE_TAC[option_CASE]]]);;
let LIBXAUX_INV_BIN2_TAC =
  FIRST_ASSUM(fun th ->
    let th' = GEN_REWRITE_RULE I [balanced_map_invariant_def] th in
    let c1,c2 = CONJ_PAIR th' in
    ASSUME_TAC (SYM c1) THEN STRIP_ASSUME_TAC c2);;

(* reasoning with the laws of a good comparison, from the facts given       *)

let LIBXAUX_GC_TAC : tactic =
  let rec is_ord tm =
    if is_neg tm then is_ord (dest_neg tm)
    else if is_conj tm then let a,b = dest_conj tm in is_ord a && is_ord b
    else if is_disj tm then let a,b = dest_disj tm in is_ord a && is_ord b
    else is_eq tm && type_of (lhs tm) = `:ordering` in
  FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP LBMAPAUX_good_cmp th)) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_ord (concl th) then MP_TAC th else NO_TAC)) THEN
  MESON_TAC[distinctness "ordering"; ordering_nchotomy];;

(* the subtrees that trim_help_greater, trim_help_lesser, trim_help_middle   *)
(* return                                                                     *)

let LIBXAUX_trim_help_greater = prove
 (`!(t:(K,V)balanced_map) (cmp:K->K->ordering) lo.
     good_cmp cmp /\ balanced_map_invariant cmp t
     ==> balanced_map_invariant cmp (trim_help_greater cmp lo t) /\
         bounded_root cmp (SOME lo) NONE (trim_help_greater cmp lo t) /\
         to_fmap cmp (trim_help_greater cmp lo t) SUBMAP to_fmap cmp t /\
         (!k. cmp lo k = LESS
              ==> balanced_map_lookup cmp k (trim_help_greater cmp lo t) =
                  balanced_map_lookup cmp k t)`,
  MATCH_MP_TAC balanced_map_INDUCT THEN
  REWRITE_TAC[trim_help_greater_def; LIBXAUX_bounded_root; SUBMAP_REFL;
              CONJUNCT1 invariant_eq] THEN
  MAP_EVERY X_GEN_TAC [`s:num`; `k:K`; `v:V`; `l:(K,V)balanced_map`;
                       `r:(K,V)balanced_map`] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`cmp:K->K->ordering`; `lo:K`] THEN STRIP_TAC THEN
  LIBXAUX_INV_BIN2_TAC THEN
  MP_TAC(ISPECL [`cmp:K->K->ordering`; `s:num`; `k:K`; `v:V`;
                 `l:(K,V)balanced_map`; `r:(K,V)balanced_map`] LIBXAUX_SUBMAP_Bin) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  COND_CASES_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`cmp:K->K->ordering`; `lo:K`]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBMAP_TRANS THEN
      EXISTS_TAC `to_fmap (cmp:K->K->ordering) (r:(K,V)balanced_map)` THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `k0:K` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
      REWRITE_TAC[balanced_map_lookup_def] THEN
      SUBGOAL_THEN `(cmp:K->K->ordering) k0 k = GREATER`
        (fun th -> REWRITE_TAC[th; ordering_case_def]) THEN
      LIBXAUX_GC_TAC];
    ASM_REWRITE_TAC[LIBXAUX_bounded_root; SUBMAP_REFL; LIBXAUX_IN_restrict_set] THEN
    LIBXAUX_GC_TAC]);;

let LIBXAUX_trim_help_lesser = prove
 (`!(t:(K,V)balanced_map) (cmp:K->K->ordering) hi.
     good_cmp cmp /\ balanced_map_invariant cmp t
     ==> balanced_map_invariant cmp (trim_help_lesser cmp hi t) /\
         bounded_root cmp NONE (SOME hi) (trim_help_lesser cmp hi t) /\
         to_fmap cmp (trim_help_lesser cmp hi t) SUBMAP to_fmap cmp t /\
         (!k. cmp k hi = LESS
              ==> balanced_map_lookup cmp k (trim_help_lesser cmp hi t) =
                  balanced_map_lookup cmp k t)`,
  MATCH_MP_TAC balanced_map_INDUCT THEN
  REWRITE_TAC[trim_help_lesser_def; LIBXAUX_bounded_root; SUBMAP_REFL;
              CONJUNCT1 invariant_eq] THEN
  MAP_EVERY X_GEN_TAC [`s:num`; `k:K`; `v:V`; `l:(K,V)balanced_map`;
                       `r:(K,V)balanced_map`] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`cmp:K->K->ordering`; `hi:K`] THEN STRIP_TAC THEN
  LIBXAUX_INV_BIN2_TAC THEN
  MP_TAC(ISPECL [`cmp:K->K->ordering`; `s:num`; `k:K`; `v:V`;
                 `l:(K,V)balanced_map`; `r:(K,V)balanced_map`] LIBXAUX_SUBMAP_Bin) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  COND_CASES_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`cmp:K->K->ordering`; `hi:K`]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBMAP_TRANS THEN
      EXISTS_TAC `to_fmap (cmp:K->K->ordering) (l:(K,V)balanced_map)` THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `k0:K` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
      REWRITE_TAC[balanced_map_lookup_def] THEN
      SUBGOAL_THEN `(cmp:K->K->ordering) k0 k = LESS`
        (fun th -> REWRITE_TAC[th; ordering_case_def]) THEN
      LIBXAUX_GC_TAC];
    ASM_REWRITE_TAC[LIBXAUX_bounded_root; SUBMAP_REFL; LIBXAUX_IN_restrict_set] THEN
    LIBXAUX_GC_TAC]);;
let LIBXAUX_trim_help_middle = prove
 (`!(t:(K,V)balanced_map) (cmp:K->K->ordering) lo hi.
     good_cmp cmp /\ balanced_map_invariant cmp t
     ==> balanced_map_invariant cmp (trim_help_middle cmp lo hi t) /\
         bounded_root cmp (SOME lo) (SOME hi) (trim_help_middle cmp lo hi t) /\
         to_fmap cmp (trim_help_middle cmp lo hi t) SUBMAP to_fmap cmp t /\
         (!k. cmp lo k = LESS /\ cmp k hi = LESS
              ==> balanced_map_lookup cmp k (trim_help_middle cmp lo hi t) =
                  balanced_map_lookup cmp k t)`,
  MATCH_MP_TAC balanced_map_INDUCT THEN
  REWRITE_TAC[trim_help_middle_def; LIBXAUX_bounded_root; SUBMAP_REFL;
              CONJUNCT1 invariant_eq] THEN
  MAP_EVERY X_GEN_TAC [`s:num`; `k:K`; `v:V`; `l:(K,V)balanced_map`;
                       `r:(K,V)balanced_map`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ihl") (LABEL_TAC "ihr")) THEN
  MAP_EVERY X_GEN_TAC [`cmp:K->K->ordering`; `lo:K`; `hi:K`] THEN STRIP_TAC THEN
  LIBXAUX_INV_BIN2_TAC THEN
  MP_TAC(ISPECL [`cmp:K->K->ordering`; `s:num`; `k:K`; `v:V`;
                 `l:(K,V)balanced_map`; `r:(K,V)balanced_map`] LIBXAUX_SUBMAP_Bin) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  COND_CASES_TAC THENL
   [REMOVE_THEN "ihr" (MP_TAC o SPECL [`cmp:K->K->ordering`; `lo:K`; `hi:K`]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBMAP_TRANS THEN
      EXISTS_TAC `to_fmap (cmp:K->K->ordering) (r:(K,V)balanced_map)` THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `k0:K` THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
      REWRITE_TAC[balanced_map_lookup_def] THEN
      SUBGOAL_THEN `(cmp:K->K->ordering) k0 k = GREATER`
        (fun th -> REWRITE_TAC[th; ordering_case_def]) THEN
      LIBXAUX_GC_TAC];
    ALL_TAC] THEN
  COND_CASES_TAC THENL
   [REMOVE_THEN "ihl" (MP_TAC o SPECL [`cmp:K->K->ordering`; `lo:K`; `hi:K`]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBMAP_TRANS THEN
      EXISTS_TAC `to_fmap (cmp:K->K->ordering) (l:(K,V)balanced_map)` THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `k0:K` THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
      REWRITE_TAC[balanced_map_lookup_def] THEN
      SUBGOAL_THEN `(cmp:K->K->ordering) k0 k = LESS`
        (fun th -> REWRITE_TAC[th; ordering_case_def]) THEN
      LIBXAUX_GC_TAC];
    ASM_REWRITE_TAC[LIBXAUX_bounded_root; SUBMAP_REFL; LIBXAUX_IN_restrict_set] THEN
    CONJ_TAC THEN LIBXAUX_GC_TAC]);;

(* HOL4: trim_thm (local there) *)

let trim_thm = prove
 (`!(t:(K,V)balanced_map) lk hk (cmp:K->K->ordering).
     good_cmp cmp /\ balanced_map_invariant cmp t
     ==> balanced_map_invariant cmp (balanced_map_trim cmp lk hk t) /\
         bounded_root cmp lk hk (balanced_map_trim cmp lk hk t) /\
         to_fmap cmp (balanced_map_trim cmp lk hk t) SUBMAP to_fmap cmp t /\
         restrict_domain cmp lk hk (to_fmap cmp (balanced_map_trim cmp lk hk t)) =
         restrict_domain cmp lk hk (to_fmap cmp t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `balanced_map_invariant cmp (balanced_map_trim cmp lk hk t) /\
    bounded_root cmp lk hk (balanced_map_trim cmp lk hk t) /\
    to_fmap cmp (balanced_map_trim cmp lk hk t) SUBMAP to_fmap cmp t /\
    (!k. k IN restrict_set cmp lk hk
         ==> balanced_map_lookup cmp k (balanced_map_trim cmp lk hk t) =
             balanced_map_lookup (cmp:K->K->ordering) k (t:(K,V)balanced_map))`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY (fun t -> STRUCT_CASES_TAC(ISPEC t (cases "option")))
      [`lk:K option`; `hk:K option`] THEN
    REWRITE_TAC[balanced_map_trim_def; LIBXAUX_IN_restrict_set] THEN
    ASM_SIMP_TAC[LIBXAUX_trim_help_greater; LIBXAUX_trim_help_lesser;
                 LIBXAUX_trim_help_middle; SUBMAP_REFL] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN
    SPEC_TAC(`t:(K,V)balanced_map`,`t:(K,V)balanced_map`) THEN
    MATCH_MP_TAC balanced_map_INDUCT THEN
    REWRITE_TAC[LIBXAUX_bounded_root; LIBXAUX_IN_restrict_set];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LIBXAUX_FMAP_EXT_KEYS THEN
  EXISTS_TAC `cmp:K->K->ordering` THEN
  REWRITE_TAC[LIBXAUX_FDOM_restrict; IN_INTER] THEN
  REPEAT CONJ_TAC THENL [MESON_TAC[to_fmap_key_set]; MESON_TAC[to_fmap_key_set]; ALL_TAC] THEN
  X_GEN_TAC `k0:K` THEN
  ASM_SIMP_TAC[LIBXAUX_FLOOKUP_restrict; LIBXAUX_FLOOKUP_to_fmap] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[]);;

(* ========================================================================= *)
(* HOL4 balanced_mapScript.sml lines 2216-2439: link_thm and link2_thm       *)
(* (local there), with the size facts of the local link_balanced_lem1-3 and  *)
(* link2_balanced_lem(2).                                                    *)
(* ========================================================================= *)

(* HOL4: link_balanced_lem1, link_balanced_lem2, link_balanced_lem3,       *)
(* link2_balanced_lem, link2_balanced_lem2 (local there): the size facts    *)
(* used below, stated with the sizes of the trees                            *)

let LIBXAUX_link_bal1 = prove
 (`!sL slz srz.
     balanced slz srz /\ balanced_map_delta * sL < slz + srz + 1
     ==> almost_balancedL (sL + slz + 1) srz`,
  LBMAPAUX_BAL_TAC);;

let LIBXAUX_link_bal2 = prove
 (`!sR sly sry.
     balanced sly sry /\ ~(balanced_map_delta * (sly + sry + 1) < sR) /\
     balanced_map_delta * sR < sly + sry + 1
     ==> almost_balancedR sly (sry + sR + 1)`,
  LBMAPAUX_BAL_TAC);;

let LIBXAUX_link_bal3 = prove
 (`!sL sR. ~(balanced_map_delta * sL < sR) /\ ~(balanced_map_delta * sR < sL) ==> balanced sL sR`,
  LBMAPAUX_BAL_TAC);;

let LIBXAUX_link2_bal1 = prove
 (`!sL sR slx srx sly sry.
     balanced slx srx /\ balanced sly sry /\ 1 + slx + srx = sL /\
     1 + sly + sry = sR /\ balanced_map_delta * sL < sR
     ==> almost_balancedL (sL + sly) sry`,
  LBMAPAUX_BAL_TAC);;

let LIBXAUX_link2_bal2 = prove
 (`!sL sR slx srx sly sry.
     balanced slx srx /\ balanced sly sry /\ 1 + slx + srx = sL /\
     1 + sly + sry = sR /\ ~(balanced_map_delta * sL < sR) /\ balanced_map_delta * sR < sL
     ==> almost_balancedR slx (srx + sR)`,
  LBMAPAUX_BAL_TAC);;

(* the finite map of a tree rebuilt by link and link2 *)

let LIBXAUX_FUNION_LINK_L = prove
 (`!(L:(K->bool,V)fmap) lz rz k v kz z.
     ~(k = kz) /\ FLOOKUP L kz = NONE
     ==> FUNION (FUNION L lz |+ (k,v)) rz |+ (kz,z) =
         FUNION L (FUNION lz rz |+ (kz,z)) |+ (k,v)`,
  REPEAT STRIP_TAC THEN
  LBMAPAUX_FMAP_TAC [`kz:K->bool`; `k:K->bool`] [ASSUME `~(k:K->bool = kz)`] []);;

let LIBXAUX_FUNION_LINK_R = prove
 (`!(ly:(K->bool,V)fmap) ry R k v ky y.
     ~(k = ky) /\ FLOOKUP ly k = NONE
     ==> FUNION ly (FUNION ry R |+ (k,v)) |+ (ky,y) =
         FUNION (FUNION ly ry |+ (ky,y)) R |+ (k,v)`,
  REPEAT STRIP_TAC THEN
  LBMAPAUX_FMAP_TAC [`ky:K->bool`; `k:K->bool`] [ASSUME `~(k:K->bool = ky)`] []);;
(* key ordering, disjointness and sizes of trees joined at a key *)

let LIBXAUX_ko_NOTIN = prove
 (`!(cmp:K->K->ordering) k (t:(K,V)balanced_map) res.
     good_cmp cmp /\ key_ordered cmp k t res /\ ~(res = EQUAL)
     ==> ~(key_set cmp k IN FDOM (to_fmap cmp t))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`cmp:K->K->ordering`; `k:K`; `k:K`; `t:(K,V)balanced_map`; `res:ordering`]
         LBMAPAUX_key_ordered_FDOM) THEN
  ASM_MESON_TAC[LBMAPAUX_good_cmp]);;

let LIBXAUX_ko_DISJOINT = prove
 (`!(cmp:K->K->ordering) k (l:(K,V)balanced_map) (r:(K,V)balanced_map).
     good_cmp cmp /\ key_ordered cmp k l GREATER /\ key_ordered cmp k r LESS
     ==> DISJOINT (FDOM (to_fmap cmp l)) (FDOM (to_fmap cmp r))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
  X_GEN_TAC `ks:K->bool` THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP to_fmap_key_set) THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:K` SUBST_ALL_TAC) THEN
  MP_TAC(ISPECL [`cmp:K->K->ordering`; `k:K`; `k0:K`; `l:(K,V)balanced_map`; `GREATER`]
         LBMAPAUX_key_ordered_FDOM) THEN
  MP_TAC(ISPECL [`cmp:K->K->ordering`; `k:K`; `k0:K`; `r:(K,V)balanced_map`; `LESS`]
         LBMAPAUX_key_ordered_FDOM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[distinctness "ordering"]);;

let LIBXAUX_FCARD_JOIN = prove
 (`!(cmp:K->K->ordering) k (l:(K,V)balanced_map) (r:(K,V)balanced_map) (v:V).
     good_cmp cmp /\ key_ordered cmp k l GREATER /\ key_ordered cmp k r LESS
     ==> FCARD (FUNION (to_fmap cmp l) (to_fmap cmp r) |+ (key_set cmp k,v)) =
         FCARD (to_fmap cmp l) + FCARD (to_fmap cmp r) + 1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(key_set (cmp:K->K->ordering) k IN FDOM (to_fmap cmp (l:(K,V)balanced_map))) /\
                ~(key_set cmp k IN FDOM (to_fmap cmp (r:(K,V)balanced_map)))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC LIBXAUX_ko_NOTIN THENL
     [EXISTS_TAC `GREATER`; EXISTS_TAC `LESS`] THEN
    ASM_REWRITE_TAC[distinctness "ordering"];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[FCARD_FUPDATE; FDOM_FUNION; IN_UNION] THEN
  MP_TAC(ISPECL [`to_fmap (cmp:K->K->ordering) (l:(K,V)balanced_map)`;
                 `to_fmap (cmp:K->K->ordering) (r:(K,V)balanced_map)`]
         LBMAPAUX_FCARD_DISJOINT_UNION) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[LIBXAUX_ko_DISJOINT]; ARITH_TAC]);;

let LIBXAUX_ko_JOIN = prove
 (`!(cmp:K->K->ordering) a k (l:(K,V)balanced_map) (r:(K,V)balanced_map)
    (t:(K,V)balanced_map) res.
     good_cmp cmp /\ key_ordered cmp a l res /\ key_ordered cmp a r res /\
     cmp a k = res /\
     FDOM (to_fmap cmp t) =
     key_set cmp k INSERT (FDOM (to_fmap cmp l) UNION FDOM (to_fmap cmp r))
     ==> key_ordered cmp a t res`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `key_ordered (cmp:K->K->ordering) a (l:(K,V)balanced_map) res` THEN
  UNDISCH_TAC `key_ordered (cmp:K->K->ordering) a (r:(K,V)balanced_map) res` THEN
  ASM_SIMP_TAC[key_ordered_to_fmap; FORALL_IN_INSERT; FORALL_IN_UNION;
               key_set_cmp_thm]);;

let link_thm = prove
 (`!(k:K) (v:V) l r (cmp:K->K->ordering).
     good_cmp cmp /\ balanced_map_invariant cmp l /\
     balanced_map_invariant cmp r /\
     key_ordered cmp k l GREATER /\ key_ordered cmp k r LESS
     ==> balanced_map_invariant cmp (balanced_map_link k v l r) /\
         to_fmap cmp (balanced_map_link k v l r) =
         FUNION (to_fmap cmp l) (to_fmap cmp r) |+ (key_set cmp k,v)`,
  MATCH_MP_TAC balanced_map_link_ind THEN REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    REWRITE_TAC[balanced_map_link_def; CONJUNCT1 to_fmap_def; FUNION_FEMPTY_1] THEN
    MATCH_MP_TAC insertMin_thm THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `key_ordered (cmp:K->K->ordering) k (r:(K,V)balanced_map) LESS` THEN
    ASM_SIMP_TAC[key_ordered_to_fmap];
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    REWRITE_TAC[balanced_map_link_def; CONJUNCT1 to_fmap_def; FUNION_FEMPTY_2] THEN
    MATCH_MP_TAC insertMax_thm THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `key_ordered (cmp:K->K->ordering) k
                   (Bin v5 v6 v7 v8 v9:(K,V)balanced_map) GREATER` THEN
    ASM_SIMP_TAC[key_ordered_to_fmap];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC
   [`k:K`; `v:V`; `sL:num`; `ky:K`; `y:V`; `ly:(K,V)balanced_map`;
    `ry:(K,V)balanced_map`; `sR:num`; `kz:K`; `z:V`; `lz:(K,V)balanced_map`;
    `rz:(K,V)balanced_map`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ihl") (LABEL_TAC "ihr")) THEN
  X_GEN_TAC `cmp:K->K->ordering` THEN STRIP_TAC THEN
  MP_TAC(ASSUME `balanced_map_invariant (cmp:K->K->ordering)
                   (Bin sL ky y ly ry:(K,V)balanced_map)`) THEN
  MP_TAC(ASSUME `balanced_map_invariant (cmp:K->K->ordering)
                   (Bin sR kz z lz rz:(K,V)balanced_map)`) THEN
  REWRITE_TAC[balanced_map_invariant_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) STRIP_ASSUME_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) STRIP_ASSUME_TAC) THEN
  MP_TAC(ASSUME `key_ordered (cmp:K->K->ordering) k
                   (Bin sL ky y ly ry:(K,V)balanced_map) GREATER`) THEN
  MP_TAC(ASSUME `key_ordered (cmp:K->K->ordering) k
                   (Bin sR kz z lz rz:(K,V)balanced_map) LESS`) THEN
  REWRITE_TAC[key_ordered_def] THEN STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(cmp:K->K->ordering) kz k = GREATER /\ cmp ky k = LESS`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[LBMAPAUX_good_cmp]; ALL_TAC] THEN
  MAP_EVERY (fun t -> MP_TAC(MATCH_MP structure_size_thm
     (ASSUME (mk_comb(`balanced_map_invariant (cmp:K->K->ordering):(K,V)balanced_map->bool`, t)))))
   [`ly:(K,V)balanced_map`; `ry:(K,V)balanced_map`;
    `lz:(K,V)balanced_map`; `rz:(K,V)balanced_map`] THEN
  REPEAT DISCH_TAC THEN
  REWRITE_TAC[balanced_map_link_def] THEN
  COND_CASES_TAC THENL
   [REMOVE_THEN "ihl" MP_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `cmp:K->K->ordering`) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`kz:K`; `z:V`;
                   `balanced_map_link (k:K) (v:V) (Bin sL ky y ly ry) lz`;
                   `rz:(K,V)balanced_map`; `cmp:K->K->ordering`] balanceL_thm) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC LIBXAUX_ko_JOIN THEN
        MAP_EVERY EXISTS_TAC [`k:K`; `Bin sL ky y ly ry:(K,V)balanced_map`;
                              `lz:(K,V)balanced_map`] THEN
        ASM_REWRITE_TAC[FDOM_FUPDATE; FDOM_FUNION] THEN
        MATCH_MP_TAC LBMAPAUX_key_ordered_trans THEN EXISTS_TAC `k:K` THEN
        ASM_REWRITE_TAC[key_ordered_def];
        MP_TAC(ISPECL [`cmp:K->K->ordering`;
                       `balanced_map_link (k:K) (v:V) (Bin sL ky y ly ry) lz`] size_thm) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
        MP_TAC(ISPECL [`cmp:K->K->ordering`; `k:K`; `Bin sL ky y ly ry:(K,V)balanced_map`;
                       `lz:(K,V)balanced_map`; `v:V`] LIBXAUX_FCARD_JOIN) THEN
        ASM_REWRITE_TAC[key_ordered_def] THEN DISCH_THEN SUBST1_TAC THEN
        MP_TAC(ISPECL [`cmp:K->K->ordering`; `Bin sL ky y ly ry:(K,V)balanced_map`] size_thm) THEN
        MP_TAC(ISPECL [`cmp:K->K->ordering`; `lz:(K,V)balanced_map`] size_thm) THEN
        ASM_REWRITE_TAC[balanced_map_size'_def] THEN
        REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN
        MATCH_MP_TAC LIBXAUX_link_bal1 THEN CONJ_TAC THENL
         [UNDISCH_TAC `balanced (balanced_map_size' (lz:(K,V)balanced_map))
                                (balanced_map_size' (rz:(K,V)balanced_map))` THEN
          ASM_REWRITE_TAC[];
          UNDISCH_TAC `balanced_map_delta * sL < sR` THEN
          UNDISCH_TAC `1 + structure_size (lz:(K,V)balanced_map) +
                       structure_size (rz:(K,V)balanced_map) = sR` THEN
          ARITH_TAC]];
      ALL_TAC] THEN
    SUBGOAL_THEN `FLOOKUP (to_fmap (cmp:K->K->ordering)
                    (Bin sL ky y ly ry:(K,V)balanced_map)) (key_set cmp kz) = NONE`
    MP_TAC THENL
     [MATCH_MP_TAC LBMAPAUX_ko_NONE THEN
      MAP_EVERY EXISTS_TAC [`k:K`; `GREATER`] THEN
      ASM_REWRITE_TAC[distinctness "ordering"];
      ALL_TAC] THEN
    REWRITE_TAC[LIBXAUX_to_fmap_Bin] THEN DISCH_TAC THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[LIBXAUX_to_fmap_Bin] THEN
    MATCH_MP_TAC LIBXAUX_FUNION_LINK_L THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[key_set_eq] THEN ASM_REWRITE_TAC[distinctness "ordering"];
    ALL_TAC] THEN
  COND_CASES_TAC THENL
   [REMOVE_THEN "ihr" MP_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `cmp:K->K->ordering`) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`ky:K`; `y:V`; `ly:(K,V)balanced_map`;
                   `balanced_map_link (k:K) (v:V) ry (Bin sR kz z lz rz)`;
                   `cmp:K->K->ordering`] balanceR_thm) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC LIBXAUX_ko_JOIN THEN
        MAP_EVERY EXISTS_TAC [`k:K`; `ry:(K,V)balanced_map`;
                              `Bin sR kz z lz rz:(K,V)balanced_map`] THEN
        ASM_REWRITE_TAC[FDOM_FUPDATE; FDOM_FUNION] THEN
        MATCH_MP_TAC LBMAPAUX_key_ordered_trans THEN EXISTS_TAC `k:K` THEN
        ASM_REWRITE_TAC[key_ordered_def];
        MP_TAC(ISPECL [`cmp:K->K->ordering`;
                       `balanced_map_link (k:K) (v:V) ry (Bin sR kz z lz rz)`] size_thm) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
        MP_TAC(ISPECL [`cmp:K->K->ordering`; `k:K`; `ry:(K,V)balanced_map`;
                       `Bin sR kz z lz rz:(K,V)balanced_map`; `v:V`] LIBXAUX_FCARD_JOIN) THEN
        ASM_REWRITE_TAC[key_ordered_def] THEN DISCH_THEN SUBST1_TAC THEN
        MP_TAC(ISPECL [`cmp:K->K->ordering`; `Bin sR kz z lz rz:(K,V)balanced_map`] size_thm) THEN
        MP_TAC(ISPECL [`cmp:K->K->ordering`; `ry:(K,V)balanced_map`] size_thm) THEN
        ASM_REWRITE_TAC[balanced_map_size'_def] THEN
        REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN
        MATCH_MP_TAC LIBXAUX_link_bal2 THEN CONJ_TAC THENL
         [UNDISCH_TAC `balanced (balanced_map_size' (ly:(K,V)balanced_map))
                                (balanced_map_size' (ry:(K,V)balanced_map))` THEN
          ASM_REWRITE_TAC[];
          UNDISCH_TAC `~(balanced_map_delta * sL < sR)` THEN UNDISCH_TAC `balanced_map_delta * sR < sL` THEN
          UNDISCH_TAC `1 + structure_size (ly:(K,V)balanced_map) +
                       structure_size (ry:(K,V)balanced_map) = sL` THEN
          REWRITE_TAC[balanced_map_delta_def] THEN ARITH_TAC]];
      ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[LIBXAUX_to_fmap_Bin] THEN
    MATCH_MP_TAC LIBXAUX_FUNION_LINK_R THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[key_set_eq] THEN ASM_MESON_TAC[LBMAPAUX_good_cmp; distinctness "ordering"];
      MATCH_MP_TAC LBMAPAUX_ko_NONE THEN
      MAP_EVERY EXISTS_TAC [`ky:K`; `GREATER`] THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[LBMAPAUX_good_cmp; distinctness "ordering"]];
    ALL_TAC] THEN
  REWRITE_TAC[bin_def; balanced_map_invariant_def; to_fmap_def; key_ordered_def;
              balanced_map_size'_def; structure_size_def] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC LIBXAUX_link_bal3 THEN ASM_REWRITE_TAC[]);;
let LIBXAUX_ko_UNION = prove
 (`!(cmp:K->K->ordering) a (l:(K,V)balanced_map) (r:(K,V)balanced_map)
    (t:(K,V)balanced_map) res.
     good_cmp cmp /\ key_ordered cmp a l res /\ key_ordered cmp a r res /\
     FDOM (to_fmap cmp t) = FDOM (to_fmap cmp l) UNION FDOM (to_fmap cmp r)
     ==> key_ordered cmp a t res`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `key_ordered (cmp:K->K->ordering) a (l:(K,V)balanced_map) res` THEN
  UNDISCH_TAC `key_ordered (cmp:K->K->ordering) a (r:(K,V)balanced_map) res` THEN
  ASM_SIMP_TAC[key_ordered_to_fmap; FORALL_IN_UNION]);;

let LIBXAUX_FUNION_LINK2_L = prove
 (`!(A:(K->bool,V)fmap) B C k v.
     FLOOKUP A k = NONE
     ==> FUNION (FUNION A B) C |+ (k,v) = FUNION A (FUNION B C |+ (k,v))`,
  REPEAT STRIP_TAC THEN LBMAPAUX_FMAP_TAC [`k:K->bool`] [] []);;

let LIBXAUX_FUNION_LINK2_R = prove
 (`!(A:(K->bool,V)fmap) B C k v.
     FUNION A (FUNION B C) |+ (k,v) = FUNION (FUNION A B |+ (k,v)) C`,
  REPEAT STRIP_TAC THEN LBMAPAUX_FMAP_TAC [`k:K->bool`] [] []);;

let LIBXAUX_FCARD_UNION = prove
 (`!(cmp:K->K->ordering) k (l:(K,V)balanced_map) (r:(K,V)balanced_map).
     good_cmp cmp /\ key_ordered cmp k l GREATER /\ key_ordered cmp k r LESS
     ==> FCARD (FUNION (to_fmap cmp l) (to_fmap cmp r)) =
         FCARD (to_fmap cmp l) + FCARD (to_fmap cmp r)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LBMAPAUX_FCARD_DISJOINT_UNION THEN
  ASM_MESON_TAC[LIBXAUX_ko_DISJOINT]);;

let link2_thm = prove
 (`!l r (cmp:K->K->ordering) (k:K).
     good_cmp cmp /\ balanced_map_invariant cmp l /\
     balanced_map_invariant cmp r /\
     key_ordered cmp k l GREATER /\ key_ordered cmp k r LESS
     ==> balanced_map_invariant cmp (balanced_map_link2 l r) /\
         to_fmap cmp (balanced_map_link2 l (r:(K,V)balanced_map)) =
         FUNION (to_fmap cmp l) (to_fmap cmp r)`,
  MATCH_MP_TAC balanced_map_link2_ind THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[balanced_map_link2_def; CONJUNCT1 to_fmap_def; FUNION_FEMPTY_2] THEN
    MESON_TAC[];
    REWRITE_TAC[balanced_map_link2_def; CONJUNCT1 to_fmap_def; FUNION_FEMPTY_1] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC
   [`sL:num`; `kx:K`; `x:V`; `lx:(K,V)balanced_map`; `rx:(K,V)balanced_map`;
    `sR:num`; `ky:K`; `y:V`; `ly:(K,V)balanced_map`; `ry:(K,V)balanced_map`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ihl") (LABEL_TAC "ihr")) THEN
  MAP_EVERY X_GEN_TAC [`cmp:K->K->ordering`; `k:K`] THEN STRIP_TAC THEN
  MP_TAC(ASSUME `balanced_map_invariant (cmp:K->K->ordering)
                   (Bin sL kx x lx rx:(K,V)balanced_map)`) THEN
  MP_TAC(ASSUME `balanced_map_invariant (cmp:K->K->ordering)
                   (Bin sR ky y ly ry:(K,V)balanced_map)`) THEN
  REWRITE_TAC[balanced_map_invariant_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) STRIP_ASSUME_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) STRIP_ASSUME_TAC) THEN
  MP_TAC(ASSUME `key_ordered (cmp:K->K->ordering) k
                   (Bin sL kx x lx rx:(K,V)balanced_map) GREATER`) THEN
  MP_TAC(ASSUME `key_ordered (cmp:K->K->ordering) k
                   (Bin sR ky y ly ry:(K,V)balanced_map) LESS`) THEN
  REWRITE_TAC[key_ordered_def] THEN STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(cmp:K->K->ordering) ky k = GREATER /\ cmp kx k = LESS`
    STRIP_ASSUME_TAC THENL [CONJ_TAC THEN LIBXAUX_GC_TAC; ALL_TAC] THEN
  MAP_EVERY (fun t -> MP_TAC(MATCH_MP structure_size_thm
     (ASSUME (mk_comb(`balanced_map_invariant (cmp:K->K->ordering):(K,V)balanced_map->bool`, t)))))
   [`lx:(K,V)balanced_map`; `rx:(K,V)balanced_map`;
    `ly:(K,V)balanced_map`; `ry:(K,V)balanced_map`] THEN
  REPEAT DISCH_TAC THEN
  REWRITE_TAC[balanced_map_link2_def] THEN
  COND_CASES_TAC THENL
   [REMOVE_THEN "ihl" MP_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`cmp:K->K->ordering`; `k:K`]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`ky:K`; `y:V`;
                   `balanced_map_link2 (Bin sL kx x lx rx) (ly:(K,V)balanced_map)`;
                   `ry:(K,V)balanced_map`; `cmp:K->K->ordering`] balanceL_thm) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC LIBXAUX_ko_UNION THEN
        MAP_EVERY EXISTS_TAC [`Bin sL kx x lx rx:(K,V)balanced_map`;
                              `ly:(K,V)balanced_map`] THEN
        ASM_REWRITE_TAC[FDOM_FUNION] THEN
        MATCH_MP_TAC LBMAPAUX_key_ordered_trans THEN EXISTS_TAC `k:K` THEN
        ASM_REWRITE_TAC[key_ordered_def];
        MP_TAC(ISPECL [`cmp:K->K->ordering`;
                       `balanced_map_link2 (Bin sL kx x lx rx) (ly:(K,V)balanced_map)`]
                      size_thm) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
        MP_TAC(ISPECL [`cmp:K->K->ordering`; `k:K`; `Bin sL kx x lx rx:(K,V)balanced_map`;
                       `ly:(K,V)balanced_map`] LIBXAUX_FCARD_UNION) THEN
        ASM_REWRITE_TAC[key_ordered_def] THEN DISCH_THEN SUBST1_TAC THEN
        MP_TAC(ISPECL [`cmp:K->K->ordering`; `Bin sL kx x lx rx:(K,V)balanced_map`] size_thm) THEN
        MP_TAC(ISPECL [`cmp:K->K->ordering`; `ly:(K,V)balanced_map`] size_thm) THEN
        ASM_REWRITE_TAC[balanced_map_size'_def] THEN
        REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN
        MATCH_MP_TAC LIBXAUX_link2_bal1 THEN
        MAP_EVERY EXISTS_TAC [`sR:num`; `balanced_map_size' (lx:(K,V)balanced_map)`;
                              `balanced_map_size' (rx:(K,V)balanced_map)`] THEN
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `balanced (balanced_map_size' (ly:(K,V)balanced_map))
                              (balanced_map_size' (ry:(K,V)balanced_map))` THEN
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `FLOOKUP (to_fmap (cmp:K->K->ordering)
                    (Bin sL kx x lx rx:(K,V)balanced_map)) (key_set cmp ky) = NONE`
    MP_TAC THENL
     [MATCH_MP_TAC LBMAPAUX_ko_NONE THEN
      MAP_EVERY EXISTS_TAC [`k:K`; `GREATER`] THEN
      ASM_REWRITE_TAC[distinctness "ordering"];
      ALL_TAC] THEN
    REWRITE_TAC[LIBXAUX_to_fmap_Bin] THEN DISCH_TAC THEN
    MATCH_MP_TAC LIBXAUX_FUNION_LINK2_L THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  COND_CASES_TAC THENL
   [REMOVE_THEN "ihr" MP_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`cmp:K->K->ordering`; `k:K`]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`kx:K`; `x:V`; `lx:(K,V)balanced_map`;
                   `balanced_map_link2 rx (Bin sR ky y ly (ry:(K,V)balanced_map))`;
                   `cmp:K->K->ordering`] balanceR_thm) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC LIBXAUX_ko_UNION THEN
        MAP_EVERY EXISTS_TAC [`rx:(K,V)balanced_map`;
                              `Bin sR ky y ly ry:(K,V)balanced_map`] THEN
        ASM_REWRITE_TAC[FDOM_FUNION] THEN
        MATCH_MP_TAC LBMAPAUX_key_ordered_trans THEN EXISTS_TAC `k:K` THEN
        ASM_REWRITE_TAC[key_ordered_def];
        MP_TAC(ISPECL [`cmp:K->K->ordering`;
                       `balanced_map_link2 rx (Bin sR ky y ly (ry:(K,V)balanced_map))`]
                      size_thm) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
        MP_TAC(ISPECL [`cmp:K->K->ordering`; `k:K`; `rx:(K,V)balanced_map`;
                       `Bin sR ky y ly ry:(K,V)balanced_map`] LIBXAUX_FCARD_UNION) THEN
        ASM_REWRITE_TAC[key_ordered_def] THEN DISCH_THEN SUBST1_TAC THEN
        MP_TAC(ISPECL [`cmp:K->K->ordering`; `Bin sR ky y ly ry:(K,V)balanced_map`] size_thm) THEN
        MP_TAC(ISPECL [`cmp:K->K->ordering`; `rx:(K,V)balanced_map`] size_thm) THEN
        ASM_REWRITE_TAC[balanced_map_size'_def] THEN
        REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN
        MATCH_MP_TAC LIBXAUX_link2_bal2 THEN
        MAP_EVERY EXISTS_TAC [`sL:num`; `balanced_map_size' (ly:(K,V)balanced_map)`;
                              `balanced_map_size' (ry:(K,V)balanced_map)`] THEN
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `balanced (balanced_map_size' (lx:(K,V)balanced_map))
                              (balanced_map_size' (rx:(K,V)balanced_map))` THEN
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[LIBXAUX_to_fmap_Bin; LIBXAUX_FUNION_LINK2_R];
    ALL_TAC] THEN
  MATCH_MP_TAC glue_thm THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`ks:K->bool`; `ks':K->bool`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`cmp:K->K->ordering`; `ks:K->bool`;
                   `Bin sL kx x lx rx:(K,V)balanced_map`] to_fmap_key_set) THEN
    MP_TAC(ISPECL [`cmp:K->K->ordering`; `ks':K->bool`;
                   `Bin sR ky y ly ry:(K,V)balanced_map`] to_fmap_key_set) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `b:K` SUBST_ALL_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `a:K` SUBST_ALL_TAC) THEN
    ASM_SIMP_TAC[key_set_cmp2_thm] THEN
    MP_TAC(ISPECL [`cmp:K->K->ordering`; `k:K`; `a:K`;
                   `Bin sL kx x lx rx:(K,V)balanced_map`; `GREATER`]
                  LBMAPAUX_key_ordered_FDOM) THEN
    MP_TAC(ISPECL [`cmp:K->K->ordering`; `k:K`; `b:K`;
                   `Bin sR ky y ly ry:(K,V)balanced_map`; `LESS`]
                  LBMAPAUX_key_ordered_FDOM) THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN LIBXAUX_GC_TAC;
    REWRITE_TAC[balanced_map_size'_def] THEN
    MATCH_MP_TAC LIBXAUX_link_bal3 THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* HOL4 balanced_mapScript.sml lines 2440-2546: filter_lt_help_thm,          *)
(* filterLt_thm, filter_gt_help_thm, filterGt_thm (local there).             *)
(* ========================================================================= *)

let LIBXAUX_PW_TAC : tactic =
  MATCH_MP_TAC LIBXAUX_FMAP_EXT_KEYS THEN EXISTS_TAC `cmp:K->K->ordering` THEN
  REWRITE_TAC[LIBXAUX_FDOM_restrict; FDOM_FUNION; FDOM_FUPDATE; FDOM_FEMPTY;
              IN_INTER; IN_UNION; IN_INSERT; NOT_IN_EMPTY] THEN
  REPEAT CONJ_TAC THENL
   [MESON_TAC[to_fmap_key_set]; MESON_TAC[to_fmap_key_set]; ALL_TAC] THEN
  X_GEN_TAC `k0:K`;;

let LIBXAUX_PW_REWRITE_TAC : tactic =
  ASM_SIMP_TAC[LIBXAUX_FLOOKUP_UPDATE_key; FLOOKUP_FUNION; LIBXAUX_FLOOKUP_restrict;
               LIBXAUX_FLOOKUP_to_fmap; LIBXAUX_IN_restrict_set;
               balanced_map_lookup_def; FLOOKUP_EMPTY];;

let LIBXAUX_LKNONE_TAC (a:term) (res:term) : tactic =
  MATCH_MP_TAC LIBXAUX_lookup_ko THEN MAP_EVERY EXISTS_TAC [a; res] THEN
  ASM_REWRITE_TAC[distinctness "ordering"];;

let LIBXAUX_KCASES_TAC (k0:term) (kx:term) : tactic =
  MP_TAC(ISPECL [`cmp:K->K->ordering`; k0; kx] LBMAPAUX_cmp_cases) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[ordering_case_def; distinctness "ordering"];;

(* HOL4: filter_lt_help_thm, filterLt_thm, filter_gt_help_thm, filterGt_thm *)
(* (local there)                                                             *)

let filter_lt_help_thm = prove
 (`!(cmp:K->K->ordering) bound (t:(K,V)balanced_map).
     good_cmp cmp /\ balanced_map_invariant cmp t
     ==> balanced_map_invariant cmp (filterLt_help cmp bound t) /\
         to_fmap cmp (filterLt_help cmp bound t) =
         restrict_domain cmp NONE (SOME bound) (to_fmap cmp t)`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC balanced_map_INDUCT THEN CONJ_TAC THENL
   [REWRITE_TAC[filterLt_help_def; CONJUNCT1 to_fmap_def; CONJUNCT1 invariant_eq;
                restrict_domain_def; DRESTRICT_FEMPTY];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:num`; `kx:K`; `x:V`; `l:(K,V)balanced_map`;
                       `r:(K,V)balanced_map`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ihl") (LABEL_TAC "ihr")) THEN STRIP_TAC THEN
  LIBXAUX_INV_BIN2_TAC THEN
  REMOVE_THEN "ihl" MP_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REMOVE_THEN "ihr" MP_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[filterLt_help_def] THEN
  LIBXAUX_KCASES_TAC `kx:K` `bound:K` THENL
   [MP_TAC(ISPECL [`kx:K`; `x:V`; `l:(K,V)balanced_map`;
                   `filterLt_help cmp bound (r:(K,V)balanced_map)`;
                   `cmp:K->K->ordering`] link_thm) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LIBXAUX_ko_sub THEN
      EXISTS_TAC `r:(K,V)balanced_map` THEN
      ASM_REWRITE_TAC[LIBXAUX_FDOM_restrict; INTER_SUBSET];
      ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN LIBXAUX_PW_TAC THEN LIBXAUX_PW_REWRITE_TAC THEN
    LIBXAUX_KCASES_TAC `k0:K` `kx:K` THENL
     [SUBGOAL_THEN `(cmp:K->K->ordering) k0 bound = LESS /\
                    balanced_map_lookup cmp k0 (r:(K,V)balanced_map) = NONE`
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL [LIBXAUX_GC_TAC; LIBXAUX_LKNONE_TAC `kx:K` `LESS`]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      QCASES_ON "balanced_map_lookup (cmp:K->K->ordering) k0 (l:(K,V)balanced_map)" THEN
      ASM_REWRITE_TAC[option_CASE];
      SUBGOAL_THEN `(cmp:K->K->ordering) k0 bound = LESS` SUBST1_TAC THENL
       [LIBXAUX_GC_TAC; REWRITE_TAC[]];
      SUBGOAL_THEN `balanced_map_lookup (cmp:K->K->ordering) k0 (l:(K,V)balanced_map) = NONE`
        SUBST1_TAC THENL [LIBXAUX_LKNONE_TAC `kx:K` `GREATER`; REWRITE_TAC[option_CASE]]];
    LIBXAUX_PW_TAC THEN LIBXAUX_PW_REWRITE_TAC THEN
    LIBXAUX_KCASES_TAC `k0:K` `kx:K` THENL
     [SUBGOAL_THEN `(cmp:K->K->ordering) k0 bound = LESS` SUBST1_TAC THENL
       [LIBXAUX_GC_TAC; REWRITE_TAC[]];
      SUBGOAL_THEN `~((cmp:K->K->ordering) k0 bound = LESS) /\
                    balanced_map_lookup cmp k0 (l:(K,V)balanced_map) = NONE`
        (fun th -> REWRITE_TAC[th]) THEN
      CONJ_TAC THENL [LIBXAUX_GC_TAC; LIBXAUX_LKNONE_TAC `kx:K` `GREATER`];
      SUBGOAL_THEN `~((cmp:K->K->ordering) k0 bound = LESS) /\
                    balanced_map_lookup cmp k0 (l:(K,V)balanced_map) = NONE`
        (fun th -> REWRITE_TAC[th]) THEN
      CONJ_TAC THENL [LIBXAUX_GC_TAC; LIBXAUX_LKNONE_TAC `kx:K` `GREATER`]];
    ASM_REWRITE_TAC[] THEN LIBXAUX_PW_TAC THEN LIBXAUX_PW_REWRITE_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `(cmp:K->K->ordering) k0 kx = LESS` (fun th -> REWRITE_TAC[th; ordering_case_def]) THEN
    LIBXAUX_GC_TAC]);;
let filterLt_thm = prove
 (`!(cmp:K->K->ordering) bound (t:(K,V)balanced_map).
     good_cmp cmp /\ balanced_map_invariant cmp t
     ==> balanced_map_invariant cmp (filterLt cmp bound t) /\
         to_fmap cmp (filterLt cmp bound t) =
         restrict_domain cmp NONE bound (to_fmap cmp t)`,
  GEN_TAC THEN MATCH_MP_TAC option_INDUCT THEN
  SIMP_TAC[filterLt_def; filter_lt_help_thm] THEN REPEAT STRIP_TAC THEN
  CONV_TAC SYM_CONV THEN LIBXAUX_PW_TAC THEN LIBXAUX_PW_REWRITE_TAC);;

let filter_gt_help_thm = prove
 (`!(cmp:K->K->ordering) bound (t:(K,V)balanced_map).
     good_cmp cmp /\ balanced_map_invariant cmp t
     ==> balanced_map_invariant cmp (filterGt_help cmp bound t) /\
         to_fmap cmp (filterGt_help cmp bound t) =
         restrict_domain cmp (SOME bound) NONE (to_fmap cmp t)`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC balanced_map_INDUCT THEN CONJ_TAC THENL
   [REWRITE_TAC[filterGt_help_def; CONJUNCT1 to_fmap_def; CONJUNCT1 invariant_eq;
                restrict_domain_def; DRESTRICT_FEMPTY];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:num`; `kx:K`; `x:V`; `l:(K,V)balanced_map`;
                       `r:(K,V)balanced_map`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ihl") (LABEL_TAC "ihr")) THEN STRIP_TAC THEN
  LIBXAUX_INV_BIN2_TAC THEN
  REMOVE_THEN "ihl" MP_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REMOVE_THEN "ihr" MP_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[filterGt_help_def] THEN
  LIBXAUX_KCASES_TAC `bound:K` `kx:K` THENL
   [MP_TAC(ISPECL [`kx:K`; `x:V`; `filterGt_help cmp bound (l:(K,V)balanced_map)`;
                   `r:(K,V)balanced_map`; `cmp:K->K->ordering`] link_thm) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LIBXAUX_ko_sub THEN
      EXISTS_TAC `l:(K,V)balanced_map` THEN
      ASM_REWRITE_TAC[LIBXAUX_FDOM_restrict; INTER_SUBSET];
      ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN LIBXAUX_PW_TAC THEN LIBXAUX_PW_REWRITE_TAC THEN
    LIBXAUX_KCASES_TAC `k0:K` `kx:K` THENL
     [SUBGOAL_THEN `balanced_map_lookup (cmp:K->K->ordering) k0 (r:(K,V)balanced_map) = NONE`
        SUBST1_TAC THENL [LIBXAUX_LKNONE_TAC `kx:K` `LESS`; ALL_TAC] THEN
      COND_CASES_TAC THEN REWRITE_TAC[option_CASE] THEN
      QCASES_ON "balanced_map_lookup (cmp:K->K->ordering) k0 (l:(K,V)balanced_map)" THEN
      ASM_REWRITE_TAC[option_CASE];
      SUBGOAL_THEN `(cmp:K->K->ordering) bound k0 = LESS` SUBST1_TAC THENL
       [LIBXAUX_GC_TAC; REWRITE_TAC[]];
      SUBGOAL_THEN `(cmp:K->K->ordering) bound k0 = LESS /\
                    balanced_map_lookup cmp k0 (l:(K,V)balanced_map) = NONE`
        (fun th -> REWRITE_TAC[th; option_CASE]) THEN
      CONJ_TAC THENL [LIBXAUX_GC_TAC; LIBXAUX_LKNONE_TAC `kx:K` `GREATER`]];
    LIBXAUX_PW_TAC THEN LIBXAUX_PW_REWRITE_TAC THEN
    LIBXAUX_KCASES_TAC `k0:K` `kx:K` THENL
     [SUBGOAL_THEN `~((cmp:K->K->ordering) bound k0 = LESS) /\
                    balanced_map_lookup cmp k0 (r:(K,V)balanced_map) = NONE`
        (fun th -> REWRITE_TAC[th]) THEN
      CONJ_TAC THENL [LIBXAUX_GC_TAC; LIBXAUX_LKNONE_TAC `kx:K` `LESS`];
      SUBGOAL_THEN `~((cmp:K->K->ordering) bound k0 = LESS) /\
                    balanced_map_lookup cmp k0 (r:(K,V)balanced_map) = NONE`
        (fun th -> REWRITE_TAC[th]) THEN
      CONJ_TAC THENL [LIBXAUX_GC_TAC; LIBXAUX_LKNONE_TAC `kx:K` `LESS`];
      SUBGOAL_THEN `(cmp:K->K->ordering) bound k0 = LESS` SUBST1_TAC THENL
       [LIBXAUX_GC_TAC; REWRITE_TAC[]]];
    ASM_REWRITE_TAC[] THEN LIBXAUX_PW_TAC THEN LIBXAUX_PW_REWRITE_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `(cmp:K->K->ordering) k0 kx = GREATER`
      (fun th -> REWRITE_TAC[th; ordering_case_def]) THEN
    LIBXAUX_GC_TAC]);;

let filterGt_thm = prove
 (`!(cmp:K->K->ordering) bound (t:(K,V)balanced_map).
     good_cmp cmp /\ balanced_map_invariant cmp t
     ==> balanced_map_invariant cmp (filterGt cmp bound t) /\
         to_fmap cmp (filterGt cmp bound t) =
         restrict_domain cmp bound NONE (to_fmap cmp t)`,
  GEN_TAC THEN MATCH_MP_TAC option_INDUCT THEN
  SIMP_TAC[filterGt_def; filter_gt_help_thm] THEN REPEAT STRIP_TAC THEN
  CONV_TAC SYM_CONV THEN LIBXAUX_PW_TAC THEN LIBXAUX_PW_REWRITE_TAC);;

(* ========================================================================= *)
(* HOL4 balanced_mapScript.sml lines 2547-2863: bounded_all (defined above), *)
(* hedgeUnion_thm (local there), bounded_all_NONE, union_thm and             *)
(* lookup_union (balanced_map_lookup_union).  The local lemmas               *)
(* if_some_none_eq, restrict_domain_partition, restrict_domain_union_swap,   *)
(* restrict_domain_extend, restrict_domain_combine and restrict_domain_empty *)
(* are replaced by pointwise reasoning; bounded_all_shrink1,                 *)
(* bounded_all_shrink2 and bounded_restrict_id are                           *)
(* LIBXAUX_bounded_all_shrink1, ... .                                        *)
(* ========================================================================= *)

(* bounded_all, and more pointwise facts                                     *)

let LIBXAUX_bounded_all_shrink1 = prove
 (`!(t:(K,V)balanced_map) (cmp:K->K->ordering) blo bhi kx.
     good_cmp cmp /\ bounded_all cmp blo bhi t /\ key_ordered cmp kx t GREATER
     ==> bounded_all cmp blo (SOME kx) t`,
  MATCH_MP_TAC balanced_map_INDUCT THEN
  REWRITE_TAC[bounded_all_def; key_ordered_def] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[] THEN
  UNDISCH_TAC `(a1:K) IN restrict_set (cmp:K->K->ordering) blo bhi` THEN
  STRUCT_CASES_TAC(ISPEC `blo:K option` (cases "option")) THEN
  STRUCT_CASES_TAC(ISPEC `bhi:K option` (cases "option")) THEN
  REWRITE_TAC[LIBXAUX_IN_restrict_set] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN LIBXAUX_GC_TAC);;

let LIBXAUX_bounded_all_shrink2 = prove
 (`!(t:(K,V)balanced_map) (cmp:K->K->ordering) blo bhi kx.
     good_cmp cmp /\ bounded_all cmp blo bhi t /\ key_ordered cmp kx t LESS
     ==> bounded_all cmp (SOME kx) bhi t`,
  MATCH_MP_TAC balanced_map_INDUCT THEN
  REWRITE_TAC[bounded_all_def; key_ordered_def] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[] THEN
  UNDISCH_TAC `(a1:K) IN restrict_set (cmp:K->K->ordering) blo bhi` THEN
  STRUCT_CASES_TAC(ISPEC `blo:K option` (cases "option")) THEN
  STRUCT_CASES_TAC(ISPEC `bhi:K option` (cases "option")) THEN
  REWRITE_TAC[LIBXAUX_IN_restrict_set] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN LIBXAUX_GC_TAC);;

let LIBXAUX_bounded_restrict_id = prove
 (`!(cmp:K->K->ordering) blo bhi (t:(K,V)balanced_map).
     good_cmp cmp /\ balanced_map_invariant cmp t /\ bounded_all cmp blo bhi t
     ==> restrict_domain cmp blo bhi (to_fmap cmp t) = to_fmap cmp t`,
  REPEAT STRIP_TAC THEN LIBXAUX_PW_TAC THEN LIBXAUX_PW_REWRITE_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC LIBXAUX_lookup_bounded THEN ASM_MESON_TAC[]);;

let LIBXAUX_ko_restrict_lt = prove
 (`!(cmp:K->K->ordering) lo kx (t:(K,V)balanced_map) m.
     good_cmp cmp /\ to_fmap cmp t = restrict_domain cmp lo (SOME kx) m
     ==> key_ordered cmp kx t GREATER`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[key_ordered_to_fmap; LIBXAUX_FDOM_restrict] THEN
  REWRITE_TAC[IN_INTER; IN_IMAGE] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[key_set_cmp_thm] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (CONJUNCT1 LIBXAUX_range_bound)) THEN
  DISCH_TAC THEN LIBXAUX_GC_TAC);;

let LIBXAUX_ko_restrict_gt = prove
 (`!(cmp:K->K->ordering) kx hi (t:(K,V)balanced_map) m.
     good_cmp cmp /\ to_fmap cmp t = restrict_domain cmp (SOME kx) hi m
     ==> key_ordered cmp kx t LESS`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[key_ordered_to_fmap; LIBXAUX_FDOM_restrict] THEN
  REWRITE_TAC[IN_INTER; IN_IMAGE] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[key_set_cmp_thm] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (CONJUNCT2 LIBXAUX_range_bound)) THEN
  SIMP_TAC[]);;

let LIBXAUX_restrict_eq_lookup = prove
 (`!(cmp:K->K->ordering) lo hi (t:(K,V)balanced_map) t'.
     good_cmp cmp /\ balanced_map_invariant cmp t /\ balanced_map_invariant cmp t' /\
     restrict_domain cmp lo hi (to_fmap cmp t) =
     restrict_domain cmp lo hi (to_fmap cmp t')
     ==> !k. k IN restrict_set cmp lo hi
             ==> balanced_map_lookup cmp k t = balanced_map_lookup cmp k t'`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o C AP_THM `key_set (cmp:K->K->ordering) k` o
                AP_TERM `FLOOKUP:(K->bool,V)fmap->(K->bool)->V option`) THEN
  ASM_SIMP_TAC[LIBXAUX_FLOOKUP_restrict; LIBXAUX_FLOOKUP_to_fmap]);;

let LIBXAUX_range_lt2 = prove
 (`!(cmp:K->K->ordering) blo bhi kx k.
     good_cmp cmp /\ kx IN restrict_set cmp blo bhi /\ cmp k kx = LESS
     ==> (k IN restrict_set cmp blo NONE <=> k IN restrict_set cmp blo bhi)`,
  REPEAT GEN_TAC THEN
  MAP_EVERY (fun t -> STRUCT_CASES_TAC(ISPEC t (cases "option")))
    [`blo:K option`; `bhi:K option`] THEN
  REWRITE_TAC[LIBXAUX_IN_restrict_set] THEN ASM_MESON_TAC[LBMAPAUX_good_cmp]);;

let LIBXAUX_range_gt2 = prove
 (`!(cmp:K->K->ordering) blo bhi kx k.
     good_cmp cmp /\ kx IN restrict_set cmp blo bhi /\ cmp kx k = LESS
     ==> (k IN restrict_set cmp NONE bhi <=> k IN restrict_set cmp blo bhi)`,
  REPEAT GEN_TAC THEN
  MAP_EVERY (fun t -> STRUCT_CASES_TAC(ISPEC t (cases "option")))
    [`blo:K option`; `bhi:K option`] THEN
  REWRITE_TAC[LIBXAUX_IN_restrict_set] THEN ASM_MESON_TAC[LBMAPAUX_good_cmp]);;

let LIBXAUX_lookup_EQUAL = prove
 (`!(cmp:K->K->ordering) (t:(K,V)balanced_map) k1 k2.
     good_cmp cmp /\ balanced_map_invariant cmp t /\ cmp k1 k2 = EQUAL
     ==> balanced_map_lookup cmp k1 t = balanced_map_lookup cmp k2 t`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[lookup_thm] THEN
  AP_TERM_TAC THEN ASM_SIMP_TAC[key_set_eq]);;

let LIBXAUX_FDOM_lookup = prove
 (`!(cmp:K->K->ordering) (t:(K,V)balanced_map) k.
     good_cmp cmp /\ balanced_map_invariant cmp t
     ==> (key_set cmp k IN FDOM (to_fmap cmp t) <=>
          ~(balanced_map_lookup cmp k t = NONE))`,
  SIMP_TAC[lookup_thm; flookup_thm]);;
(* the recursive case of hedgeUnion, for both of its clauses                 *)

let LIBXAUX_hedgeUnion_step = prove
 (`!(cmp:K->K->ordering) blo bhi s kx (x:V) l r (t2:(K,V)balanced_map).
     (good_cmp cmp /\ balanced_map_invariant cmp l /\
      balanced_map_invariant cmp (balanced_map_trim cmp blo (SOME kx) t2) /\
      bounded_all cmp blo (SOME kx) l /\
      bounded_root cmp blo (SOME kx) (balanced_map_trim cmp blo (SOME kx) t2)
      ==> balanced_map_invariant cmp
            (hedgeUnion cmp blo (SOME kx) l (balanced_map_trim cmp blo (SOME kx) t2)) /\
          to_fmap cmp
            (hedgeUnion cmp blo (SOME kx) l (balanced_map_trim cmp blo (SOME kx) t2)) =
          restrict_domain cmp blo (SOME kx)
            (FUNION (to_fmap cmp l)
                    (to_fmap cmp (balanced_map_trim cmp blo (SOME kx) t2)))) /\
     (good_cmp cmp /\ balanced_map_invariant cmp r /\
      balanced_map_invariant cmp (balanced_map_trim cmp (SOME kx) bhi t2) /\
      bounded_all cmp (SOME kx) bhi r /\
      bounded_root cmp (SOME kx) bhi (balanced_map_trim cmp (SOME kx) bhi t2)
      ==> balanced_map_invariant cmp
            (hedgeUnion cmp (SOME kx) bhi r (balanced_map_trim cmp (SOME kx) bhi t2)) /\
          to_fmap cmp
            (hedgeUnion cmp (SOME kx) bhi r (balanced_map_trim cmp (SOME kx) bhi t2)) =
          restrict_domain cmp (SOME kx) bhi
            (FUNION (to_fmap cmp r)
                    (to_fmap cmp (balanced_map_trim cmp (SOME kx) bhi t2)))) /\
     good_cmp cmp /\ balanced_map_invariant cmp (Bin s kx x l r) /\
     balanced_map_invariant cmp t2 /\
     bounded_all cmp blo bhi (Bin s kx x l r) /\ bounded_root cmp blo bhi t2
     ==> balanced_map_invariant cmp
           (balanced_map_link kx x
              (hedgeUnion cmp blo (SOME kx) l (balanced_map_trim cmp blo (SOME kx) t2))
              (hedgeUnion cmp (SOME kx) bhi r (balanced_map_trim cmp (SOME kx) bhi t2))) /\
         to_fmap cmp
           (balanced_map_link kx x
              (hedgeUnion cmp blo (SOME kx) l (balanced_map_trim cmp blo (SOME kx) t2))
              (hedgeUnion cmp (SOME kx) bhi r (balanced_map_trim cmp (SOME kx) bhi t2))) =
         restrict_domain cmp blo bhi
           (FUNION (to_fmap cmp (Bin s kx x l r)) (to_fmap cmp t2))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1")
    (CONJUNCTS_THEN2 (LABEL_TAC "ih2") STRIP_ASSUME_TAC)) THEN
  LIBXAUX_INV_BIN2_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [CONJUNCT2 bounded_all_def]) THEN
  MP_TAC(ISPECL [`t2:(K,V)balanced_map`; `blo:K option`; `SOME (kx:K)`;
                 `cmp:K->K->ordering`] trim_thm) THEN
  MP_TAC(ISPECL [`t2:(K,V)balanced_map`; `SOME (kx:K)`; `bhi:K option`;
                 `cmp:K->K->ordering`] trim_thm) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `bounded_all (cmp:K->K->ordering) blo (SOME kx) (l:(K,V)balanced_map) /\
                bounded_all cmp (SOME kx) bhi (r:(K,V)balanced_map)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC LIBXAUX_bounded_all_shrink1 THEN EXISTS_TAC `bhi:K option`;
      MATCH_MP_TAC LIBXAUX_bounded_all_shrink2 THEN EXISTS_TAC `blo:K option`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "ih1" MP_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REMOVE_THEN "ih2" MP_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`kx:K`; `x:V`;
     `hedgeUnion cmp blo (SOME kx) l (balanced_map_trim cmp blo (SOME kx) t2):
        (K,V)balanced_map`;
     `hedgeUnion cmp (SOME kx) bhi r (balanced_map_trim cmp (SOME kx) bhi t2):
        (K,V)balanced_map`;
     `cmp:K->K->ordering`] link_thm) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC LIBXAUX_ko_restrict_lt THEN
      MAP_EVERY EXISTS_TAC [`blo:K option`;
        `FUNION (to_fmap cmp (l:(K,V)balanced_map))
                (to_fmap cmp (balanced_map_trim cmp blo (SOME kx) (t2:(K,V)balanced_map)))`];
      MATCH_MP_TAC LIBXAUX_ko_restrict_gt THEN
      MAP_EVERY EXISTS_TAC [`bhi:K option`;
        `FUNION (to_fmap cmp (r:(K,V)balanced_map))
                (to_fmap cmp (balanced_map_trim cmp (SOME kx) bhi (t2:(K,V)balanced_map)))`]] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`cmp:K->K->ordering`; `blo:K option`; `SOME (kx:K)`;
                 `balanced_map_trim cmp blo (SOME kx) (t2:(K,V)balanced_map)`;
                 `t2:(K,V)balanced_map`] LIBXAUX_restrict_eq_lookup) THEN
  MP_TAC(ISPECL [`cmp:K->K->ordering`; `SOME (kx:K)`; `bhi:K option`;
                 `balanced_map_trim cmp (SOME kx) bhi (t2:(K,V)balanced_map)`;
                 `t2:(K,V)balanced_map`] LIBXAUX_restrict_eq_lookup) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "tr2") THEN DISCH_THEN(LABEL_TAC "tr1") THEN
  LIBXAUX_PW_TAC THEN LIBXAUX_PW_REWRITE_TAC THEN
  LIBXAUX_KCASES_TAC `k0:K` `kx:K` THENL
   [MP_TAC(ISPECL [`cmp:K->K->ordering`; `blo:K option`; `bhi:K option`; `kx:K`; `k0:K`]
           LIBXAUX_range_lt) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `~((k0:K) IN restrict_set (cmp:K->K->ordering) (SOME kx) bhi)`
      (fun th -> REWRITE_TAC[th]) THENL
     [DISCH_THEN(MP_TAC o MATCH_MP (CONJUNCT2 LIBXAUX_range_bound)) THEN LIBXAUX_GC_TAC;
      ALL_TAC] THEN
    COND_CASES_TAC THEN REWRITE_TAC[option_CASE] THEN
    QCASES_ON "balanced_map_lookup (cmp:K->K->ordering) k0 (l:(K,V)balanced_map)" THEN
    ASM_REWRITE_TAC[option_CASE] THEN
    QCASES_ON "balanced_map_lookup (cmp:K->K->ordering) k0 (t2:(K,V)balanced_map)" THEN
    ASM_REWRITE_TAC[option_CASE];
    SUBGOAL_THEN `(k0:K) IN restrict_set (cmp:K->K->ordering) blo bhi`
      (fun th -> REWRITE_TAC[th; option_CASE]) THEN
    ASM_MESON_TAC[LIBXAUX_restrict_set_cmp];
    MP_TAC(ISPECL [`cmp:K->K->ordering`; `blo:K option`; `bhi:K option`; `kx:K`; `k0:K`]
           LIBXAUX_range_gt) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN LIBXAUX_GC_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `~((k0:K) IN restrict_set (cmp:K->K->ordering) blo (SOME kx))`
      (fun th -> REWRITE_TAC[th; option_CASE]) THEN
    DISCH_THEN(MP_TAC o MATCH_MP (CONJUNCT1 LIBXAUX_range_bound)) THEN LIBXAUX_GC_TAC]);;
(* HOL4: hedgeUnion_thm (local there) *)

let hedgeUnion_thm = prove
 (`!(cmp:K->K->ordering) blo bhi (t1:(K,V)balanced_map) t2.
     good_cmp cmp /\ balanced_map_invariant cmp t1 /\
     balanced_map_invariant cmp t2 /\
     bounded_all cmp blo bhi t1 /\ bounded_root cmp blo bhi t2
     ==> balanced_map_invariant cmp (hedgeUnion cmp blo bhi t1 t2) /\
         to_fmap cmp (hedgeUnion cmp blo bhi t1 t2) =
         restrict_domain cmp blo bhi (FUNION (to_fmap cmp t1) (to_fmap cmp t2))`,
  MATCH_MP_TAC hedgeUnion_ind THEN REPEAT CONJ_TAC THENL
   [(* t2 = Tip *)
    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[hedgeUnion_def; CONJUNCT1 to_fmap_def; FUNION_FEMPTY_2;
                 LIBXAUX_bounded_restrict_id];
    (* t1 = Tip *)
    MAP_EVERY X_GEN_TAC [`cmp:K->K->ordering`; `blo:K option`; `bhi:K option`;
                         `s:num`; `kx:K`; `x:V`; `l:(K,V)balanced_map`;
                         `r:(K,V)balanced_map`] THEN
    STRIP_TAC THEN LIBXAUX_INV_BIN2_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[LIBXAUX_bounded_root]) THEN
    REWRITE_TAC[hedgeUnion_def; CONJUNCT1 to_fmap_def; FUNION_FEMPTY_1] THEN
    MP_TAC(ISPECL [`cmp:K->K->ordering`; `blo:K option`; `l:(K,V)balanced_map`]
                  filterGt_thm) THEN
    MP_TAC(ISPECL [`cmp:K->K->ordering`; `bhi:K option`; `r:(K,V)balanced_map`]
                  filterLt_thm) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`kx:K`; `x:V`; `filterGt cmp blo (l:(K,V)balanced_map)`;
                   `filterLt cmp bhi (r:(K,V)balanced_map)`;
                   `cmp:K->K->ordering`] link_thm) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC LIBXAUX_ko_sub THENL
       [EXISTS_TAC `l:(K,V)balanced_map`; EXISTS_TAC `r:(K,V)balanced_map`] THEN
      ASM_REWRITE_TAC[LIBXAUX_FDOM_restrict; INTER_SUBSET];
      ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    LIBXAUX_PW_TAC THEN LIBXAUX_PW_REWRITE_TAC THEN
    LIBXAUX_KCASES_TAC `k0:K` `kx:K` THENL
     [MP_TAC(ISPECL [`cmp:K->K->ordering`; `blo:K option`; `bhi:K option`; `kx:K`;
                     `k0:K`] LIBXAUX_range_lt2) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      SUBGOAL_THEN `balanced_map_lookup (cmp:K->K->ordering) k0 (r:(K,V)balanced_map) = NONE`
        SUBST1_TAC THENL [LIBXAUX_LKNONE_TAC `kx:K` `LESS`; ALL_TAC] THEN
      REWRITE_TAC[COND_ID] THEN COND_CASES_TAC THEN REWRITE_TAC[option_CASE] THEN
      QCASES_ON "balanced_map_lookup (cmp:K->K->ordering) k0 (l:(K,V)balanced_map)" THEN
      ASM_REWRITE_TAC[option_CASE];
      SUBGOAL_THEN `(k0:K) IN restrict_set (cmp:K->K->ordering) blo bhi`
        (fun th -> REWRITE_TAC[th; option_CASE]) THEN
      ASM_MESON_TAC[LIBXAUX_restrict_set_cmp];
      MP_TAC(ISPECL [`cmp:K->K->ordering`; `blo:K option`; `bhi:K option`; `kx:K`;
                     `k0:K`] LIBXAUX_range_gt2) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN LIBXAUX_GC_TAC; ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN
      SUBGOAL_THEN `balanced_map_lookup (cmp:K->K->ordering) k0 (l:(K,V)balanced_map) = NONE`
        SUBST1_TAC THENL [LIBXAUX_LKNONE_TAC `kx:K` `GREATER`; ALL_TAC] THEN
      REWRITE_TAC[COND_ID; option_CASE] THEN
      COND_CASES_TAC THEN REWRITE_TAC[option_CASE] THEN
      QCASES_ON "balanced_map_lookup (cmp:K->K->ordering) k0 (r:(K,V)balanced_map)" THEN
      ASM_REWRITE_TAC[option_CASE]];
    (* t2 a single node *)
    MAP_EVERY X_GEN_TAC [`cmp:K->K->ordering`; `blo:K option`; `bhi:K option`;
                         `s1:num`; `k1:K`; `v1:V`; `l1:(K,V)balanced_map`;
                         `r1:(K,V)balanced_map`; `s:num`; `kx:K`; `x:V`] THEN
    STRIP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[LIBXAUX_bounded_root]) THEN
    REWRITE_TAC[hedgeUnion_def] THEN
    MP_TAC(ISPECL [`Bin s1 k1 v1 l1 r1:(K,V)balanced_map`; `cmp:K->K->ordering`;
                   `kx:K`; `x:V`] insertR_thm) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[LIBXAUX_FDOM_lookup] THEN
    REWRITE_TAC[ISPECL [`cmp:K->K->ordering`; `s:num`; `kx:K`; `x:V`;
                        `Tip:(K,V)balanced_map`; `Tip:(K,V)balanced_map`]
                       LIBXAUX_to_fmap_Bin; CONJUNCT1 to_fmap_def; FUNION_FEMPTY_1] THEN
    SUBGOAL_THEN
     `!k. ~(k IN restrict_set cmp blo bhi)
          ==> balanced_map_lookup cmp k (Bin s1 k1 v1 l1 r1:(K,V)balanced_map) = NONE`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC LIBXAUX_lookup_bounded THEN
      MAP_EVERY EXISTS_TAC [`blo:K option`; `bhi:K option`] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `balanced_map_lookup (cmp:K->K->ordering) kx
                     (Bin s1 k1 v1 l1 r1:(K,V)balanced_map) = NONE` THEN
    ASM_REWRITE_TAC[] THEN LIBXAUX_PW_TAC THEN
    ASM_SIMP_TAC[LIBXAUX_FLOOKUP_UPDATE_key; FLOOKUP_FUNION; LIBXAUX_FLOOKUP_restrict;
                 LIBXAUX_FLOOKUP_to_fmap; FLOOKUP_EMPTY] THENL
     [ASM_CASES_TAC `(cmp:K->K->ordering) kx k0 = EQUAL` THEN ASM_REWRITE_TAC[] THENL
       [SUBGOAL_THEN `(k0:K) IN restrict_set (cmp:K->K->ordering) blo bhi`
          (fun th -> REWRITE_TAC[th]) THENL
         [MP_TAC(ISPECL [`cmp:K->K->ordering`; `blo:K option`; `bhi:K option`;
                         `kx:K`; `k0:K`] LIBXAUX_restrict_set_cmp) THEN
          ASM_SIMP_TAC[];
          ALL_TAC] THEN
        MP_TAC(ISPECL [`cmp:K->K->ordering`; `Bin s1 k1 v1 l1 r1:(K,V)balanced_map`;
                       `k0:K`; `kx:K`] LIBXAUX_lookup_EQUAL) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN LIBXAUX_GC_TAC; ALL_TAC] THEN
        DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[option_CASE];
        ASM_CASES_TAC `(k0:K) IN restrict_set (cmp:K->K->ordering) blo bhi` THEN
        ASM_SIMP_TAC[] THEN
        QCASES_ON "balanced_map_lookup (cmp:K->K->ordering) k0
                     (Bin s1 k1 v1 l1 r1:(K,V)balanced_map)" THEN
        ASM_REWRITE_TAC[option_CASE]];
      ASM_CASES_TAC `(k0:K) IN restrict_set (cmp:K->K->ordering) blo bhi` THEN
      ASM_SIMP_TAC[] THEN
      QCASES_ON "balanced_map_lookup (cmp:K->K->ordering) k0
                   (Bin s1 k1 v1 l1 r1:(K,V)balanced_map)" THEN
      ASM_REWRITE_TAC[option_CASE] THEN
      COND_CASES_TAC THEN REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`cmp:K->K->ordering`; `Bin s1 k1 v1 l1 r1:(K,V)balanced_map`;
                     `k0:K`; `kx:K`] LIBXAUX_lookup_EQUAL) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN LIBXAUX_GC_TAC; ALL_TAC] THEN
      DISCH_THEN(fun th ->
        UNDISCH_TAC `~(balanced_map_lookup (cmp:K->K->ordering) kx
                         (Bin s1 k1 v1 l1 r1:(K,V)balanced_map) = NONE)` THEN
        REWRITE_TAC[GSYM th] THEN ASM_REWRITE_TAC[])];
    (* the recursive cases *)
    REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
    STRIP_TAC THEN REWRITE_TAC[hedgeUnion_def] THEN
    MATCH_MP_TAC LIBXAUX_hedgeUnion_step THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
    STRIP_TAC THEN REWRITE_TAC[hedgeUnion_def] THEN
    MATCH_MP_TAC LIBXAUX_hedgeUnion_step THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC]);;
(* HOL4: bounded_all_NONE (local there) *)

let bounded_all_NONE = prove
 (`!(cmp:K->K->ordering) (t:(K,V)balanced_map). bounded_all cmp NONE NONE t`,
  GEN_TAC THEN MATCH_MP_TAC balanced_map_INDUCT THEN
  ASM_REWRITE_TAC[bounded_all_def; LIBXAUX_IN_restrict_set]);;

(* HOL4 union_thm quantifies blo and bhi, which it does not use *)

let union_thm = prove
 (`!(cmp:K->K->ordering) (blo:K option) (bhi:K option) (t1:(K,V)balanced_map) t2.
     good_cmp cmp /\ balanced_map_invariant cmp t1 /\ balanced_map_invariant cmp t2
     ==> balanced_map_invariant cmp (balanced_map_union cmp t1 t2) /\
         to_fmap cmp (balanced_map_union cmp t1 t2) =
         FUNION (to_fmap cmp t1) (to_fmap cmp t2)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `t1:(K,V)balanced_map` (cases "balanced_map")) THEN
  STRUCT_CASES_TAC(ISPEC `t2:(K,V)balanced_map` (cases "balanced_map")) THEN
  REWRITE_TAC[balanced_map_union_def; CONJUNCT1 to_fmap_def; FUNION_FEMPTY_1;
              FUNION_FEMPTY_2] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`cmp:K->K->ordering`; `NONE:K option`; `NONE:K option`;
                 `Bin a0 a1 a2 a3 a4:(K,V)balanced_map`;
                 `Bin a0' a1' a2' a3' a4':(K,V)balanced_map`] hedgeUnion_thm) THEN
  ASM_REWRITE_TAC[bounded_all_NONE; LIBXAUX_bounded_root; LIBXAUX_IN_restrict_set] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  LIBXAUX_PW_TAC THEN
  ASM_SIMP_TAC[LIBXAUX_FLOOKUP_restrict; LIBXAUX_IN_restrict_set]);;

(* HOL4: lookup_union (sptree has lookup_union) *)

let balanced_map_lookup_union = prove
 (CASE_TERM
  `!(cmp:K->K->ordering) (t1:(K,V)balanced_map) t2 k.
     good_cmp cmp /\ balanced_map_invariant cmp t1 /\ balanced_map_invariant cmp t2
     ==> balanced_map_lookup cmp k (balanced_map_union cmp t1 t2) =
         match balanced_map_lookup cmp k t1 with
           NONE -> balanced_map_lookup cmp k t2
         | SOME v -> SOME v`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`cmp:K->K->ordering`; `NONE:K option`; `NONE:K option`;
                 `t1:(K,V)balanced_map`; `t2:(K,V)balanced_map`] union_thm) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[lookup_thm; FLOOKUP_FUNION]);;

(* ========================================================================= *)
(* HOL4 balanced_mapScript.sml lines 2864-3057: hedgeUnionWithKey_thm (local *)
(* there), unionWithKey_thm, unionWith_thm (balanced_map_unionWith_thm),     *)
(* lookup_unionWithKey, lookup_unionWith.                                    *)
(* ========================================================================= *)

let LIBXAUX_CHOICE_key_set = prove
 (`!(cmp:K->K->ordering) (f:K->V->V->V) k x y.
     good_cmp cmp /\ (!k1 k2 x y. cmp k1 k2 = EQUAL ==> f k1 x y = f k2 x y)
     ==> f (CHOICE (key_set cmp k)) x y = f k x y`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  MP_TAC(ISPECL [`cmp:K->K->ordering`; `k:K`] key_set_nonempty) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP CHOICE_DEF) THEN
  REWRITE_TAC[key_set_def; IN_ELIM_THM] THEN DISCH_TAC THEN LIBXAUX_GC_TAC);;

let LIBXAUX_FDOM_FMERGE_WITH_KEY = prove
 (`!(f:A->B->B->B) m1 m2.
     FDOM (FMERGE_WITH_KEY f m1 m2) = FDOM m1 UNION FDOM m2`,
  REWRITE_TAC[FMERGE_WITH_KEY_DEF]);;

let LIBXAUX_PW2_TAC : tactic =
  MATCH_MP_TAC LIBXAUX_FMAP_EXT_KEYS THEN EXISTS_TAC `cmp:K->K->ordering` THEN
  REWRITE_TAC[LIBXAUX_FDOM_restrict; FDOM_FUNION; FDOM_FUPDATE; FDOM_FEMPTY;
              LIBXAUX_FDOM_FMERGE_WITH_KEY;
              IN_INTER; IN_UNION; IN_INSERT; NOT_IN_EMPTY] THEN
  REPEAT CONJ_TAC THENL
   [MESON_TAC[to_fmap_key_set]; MESON_TAC[to_fmap_key_set]; ALL_TAC] THEN
  X_GEN_TAC `k0:K`;;

let LIBXAUX_PW_REWRITE2_TAC : tactic =
  ASM_SIMP_TAC[LIBXAUX_FLOOKUP_UPDATE_key; FLOOKUP_FUNION; LIBXAUX_FLOOKUP_restrict;
               LIBXAUX_FLOOKUP_to_fmap; LIBXAUX_IN_restrict_set; FLOOKUP_FMERGE_WITH_KEY;
               balanced_map_lookup_def; FLOOKUP_EMPTY; LIBXAUX_CHOICE_key_set];;

(* the tree a leaf merged with t2 gives in hedgeUnion and hedgeUnionWithKey *)

let LIBXAUX_hedge_tip = prove
 (`!(cmp:K->K->ordering) blo bhi s kx (x:V) l r.
     good_cmp cmp /\ balanced_map_invariant cmp (Bin s kx x l r) /\
     kx IN restrict_set cmp blo bhi
     ==> balanced_map_invariant cmp
           (balanced_map_link kx x (filterGt cmp blo l) (filterLt cmp bhi r)) /\
         to_fmap cmp (balanced_map_link kx x (filterGt cmp blo l) (filterLt cmp bhi r)) =
         restrict_domain cmp blo bhi (to_fmap cmp (Bin s kx x l r))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN LIBXAUX_INV_BIN2_TAC THEN
  MP_TAC(ISPECL [`cmp:K->K->ordering`; `blo:K option`; `l:(K,V)balanced_map`]
                filterGt_thm) THEN
  MP_TAC(ISPECL [`cmp:K->K->ordering`; `bhi:K option`; `r:(K,V)balanced_map`]
                filterLt_thm) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`kx:K`; `x:V`; `filterGt cmp blo (l:(K,V)balanced_map)`;
                 `filterLt cmp bhi (r:(K,V)balanced_map)`;
                 `cmp:K->K->ordering`] link_thm) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC LIBXAUX_ko_sub THENL
     [EXISTS_TAC `l:(K,V)balanced_map`; EXISTS_TAC `r:(K,V)balanced_map`] THEN
    ASM_REWRITE_TAC[LIBXAUX_FDOM_restrict; INTER_SUBSET];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  LIBXAUX_PW_TAC THEN LIBXAUX_PW_REWRITE_TAC THEN
  LIBXAUX_KCASES_TAC `k0:K` `kx:K` THENL
   [MP_TAC(ISPECL [`cmp:K->K->ordering`; `blo:K option`; `bhi:K option`; `kx:K`;
                   `k0:K`] LIBXAUX_range_lt2) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `balanced_map_lookup (cmp:K->K->ordering) k0 (r:(K,V)balanced_map) = NONE`
      SUBST1_TAC THENL [LIBXAUX_LKNONE_TAC `kx:K` `LESS`; ALL_TAC] THEN
    REWRITE_TAC[COND_ID] THEN COND_CASES_TAC THEN REWRITE_TAC[option_CASE] THEN
    QCASES_ON "balanced_map_lookup (cmp:K->K->ordering) k0 (l:(K,V)balanced_map)" THEN
    ASM_REWRITE_TAC[option_CASE];
    SUBGOAL_THEN `(k0:K) IN restrict_set (cmp:K->K->ordering) blo bhi`
      (fun th -> REWRITE_TAC[th; option_CASE]) THEN
    ASM_MESON_TAC[LIBXAUX_restrict_set_cmp];
    MP_TAC(ISPECL [`cmp:K->K->ordering`; `blo:K option`; `bhi:K option`; `kx:K`;
                   `k0:K`] LIBXAUX_range_gt2) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN LIBXAUX_GC_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `balanced_map_lookup (cmp:K->K->ordering) k0 (l:(K,V)balanced_map) = NONE`
      SUBST1_TAC THENL [LIBXAUX_LKNONE_TAC `kx:K` `GREATER`; ALL_TAC] THEN
    REWRITE_TAC[COND_ID; option_CASE] THEN
    COND_CASES_TAC THEN REWRITE_TAC[option_CASE] THEN
    QCASES_ON "balanced_map_lookup (cmp:K->K->ordering) k0 (r:(K,V)balanced_map)" THEN
    ASM_REWRITE_TAC[option_CASE]]);;
(* the recursive case of hedgeUnionWithKey *)

let LIBXAUX_hedgeUnionWithKey_step = prove
 (`!(cmp:K->K->ordering) (f:K->V->V->V) blo bhi s kx (x:V) l r
    (t2:(K,V)balanced_map).
     (good_cmp cmp /\ balanced_map_invariant cmp l /\
      balanced_map_invariant cmp (balanced_map_trim cmp blo (SOME kx) t2) /\
      bounded_all cmp blo (SOME kx) l /\
      bounded_root cmp blo (SOME kx) (balanced_map_trim cmp blo (SOME kx) t2) /\
      (!k1 k2 x y. cmp k1 k2 = EQUAL ==> f k1 x y = f k2 x y)
      ==> balanced_map_invariant cmp
            (hedgeUnionWithKey cmp f blo (SOME kx) l
               (balanced_map_trim cmp blo (SOME kx) t2)) /\
          to_fmap cmp
            (hedgeUnionWithKey cmp f blo (SOME kx) l
               (balanced_map_trim cmp blo (SOME kx) t2)) =
          restrict_domain cmp blo (SOME kx)
            (FMERGE_WITH_KEY (\ks x y. f (CHOICE ks) x y) (to_fmap cmp l)
               (to_fmap cmp (balanced_map_trim cmp blo (SOME kx) t2)))) /\
     (good_cmp cmp /\ balanced_map_invariant cmp r /\
      balanced_map_invariant cmp (balanced_map_trim cmp (SOME kx) bhi t2) /\
      bounded_all cmp (SOME kx) bhi r /\
      bounded_root cmp (SOME kx) bhi (balanced_map_trim cmp (SOME kx) bhi t2) /\
      (!k1 k2 x y. cmp k1 k2 = EQUAL ==> f k1 x y = f k2 x y)
      ==> balanced_map_invariant cmp
            (hedgeUnionWithKey cmp f (SOME kx) bhi r
               (balanced_map_trim cmp (SOME kx) bhi t2)) /\
          to_fmap cmp
            (hedgeUnionWithKey cmp f (SOME kx) bhi r
               (balanced_map_trim cmp (SOME kx) bhi t2)) =
          restrict_domain cmp (SOME kx) bhi
            (FMERGE_WITH_KEY (\ks x y. f (CHOICE ks) x y) (to_fmap cmp r)
               (to_fmap cmp (balanced_map_trim cmp (SOME kx) bhi t2)))) /\
     good_cmp cmp /\ balanced_map_invariant cmp (Bin s kx x l r) /\
     balanced_map_invariant cmp t2 /\
     bounded_all cmp blo bhi (Bin s kx x l r) /\ bounded_root cmp blo bhi t2 /\
     (!k1 k2 x y. cmp k1 k2 = EQUAL ==> f k1 x y = f k2 x y)
     ==> balanced_map_invariant cmp
           (balanced_map_link kx
              (option_CASE (balanced_map_lookup cmp kx t2) x (\y. f kx x y))
              (hedgeUnionWithKey cmp f blo (SOME kx) l
                 (balanced_map_trim cmp blo (SOME kx) t2))
              (hedgeUnionWithKey cmp f (SOME kx) bhi r
                 (balanced_map_trim cmp (SOME kx) bhi t2))) /\
         to_fmap cmp
           (balanced_map_link kx
              (option_CASE (balanced_map_lookup cmp kx t2) x (\y. f kx x y))
              (hedgeUnionWithKey cmp f blo (SOME kx) l
                 (balanced_map_trim cmp blo (SOME kx) t2))
              (hedgeUnionWithKey cmp f (SOME kx) bhi r
                 (balanced_map_trim cmp (SOME kx) bhi t2))) =
         restrict_domain cmp blo bhi
           (FMERGE_WITH_KEY (\ks x y. f (CHOICE ks) x y)
              (to_fmap cmp (Bin s kx x l r)) (to_fmap cmp t2))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1")
    (CONJUNCTS_THEN2 (LABEL_TAC "ih2") STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `!k x y. (f:K->V->V->V) (CHOICE (key_set cmp k)) x y = f k x y`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC LIBXAUX_CHOICE_key_set THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  LIBXAUX_INV_BIN2_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [CONJUNCT2 bounded_all_def]) THEN
  MP_TAC(ISPECL [`t2:(K,V)balanced_map`; `blo:K option`; `SOME (kx:K)`;
                 `cmp:K->K->ordering`] trim_thm) THEN
  MP_TAC(ISPECL [`t2:(K,V)balanced_map`; `SOME (kx:K)`; `bhi:K option`;
                 `cmp:K->K->ordering`] trim_thm) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `bounded_all (cmp:K->K->ordering) blo (SOME kx) (l:(K,V)balanced_map) /\
                bounded_all cmp (SOME kx) bhi (r:(K,V)balanced_map)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC LIBXAUX_bounded_all_shrink1 THEN EXISTS_TAC `bhi:K option`;
      MATCH_MP_TAC LIBXAUX_bounded_all_shrink2 THEN EXISTS_TAC `blo:K option`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "ih1" MP_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REMOVE_THEN "ih2" MP_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`kx:K`;
     `option_CASE (balanced_map_lookup cmp kx (t2:(K,V)balanced_map)) (x:V)
        (\y. (f:K->V->V->V) kx x y)`;
     `hedgeUnionWithKey cmp f blo (SOME kx) l
        (balanced_map_trim cmp blo (SOME kx) t2):(K,V)balanced_map`;
     `hedgeUnionWithKey cmp f (SOME kx) bhi r
        (balanced_map_trim cmp (SOME kx) bhi t2):(K,V)balanced_map`;
     `cmp:K->K->ordering`] link_thm) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC LIBXAUX_ko_restrict_lt THEN
      MAP_EVERY EXISTS_TAC [`blo:K option`;
        `FMERGE_WITH_KEY (\ks x y. (f:K->V->V->V) (CHOICE ks) x y)
           (to_fmap cmp (l:(K,V)balanced_map))
           (to_fmap cmp (balanced_map_trim cmp blo (SOME kx) (t2:(K,V)balanced_map)))`];
      MATCH_MP_TAC LIBXAUX_ko_restrict_gt THEN
      MAP_EVERY EXISTS_TAC [`bhi:K option`;
        `FMERGE_WITH_KEY (\ks x y. (f:K->V->V->V) (CHOICE ks) x y)
           (to_fmap cmp (r:(K,V)balanced_map))
           (to_fmap cmp (balanced_map_trim cmp (SOME kx) bhi (t2:(K,V)balanced_map)))`]] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`cmp:K->K->ordering`; `blo:K option`; `SOME (kx:K)`;
                 `balanced_map_trim cmp blo (SOME kx) (t2:(K,V)balanced_map)`;
                 `t2:(K,V)balanced_map`] LIBXAUX_restrict_eq_lookup) THEN
  MP_TAC(ISPECL [`cmp:K->K->ordering`; `SOME (kx:K)`; `bhi:K option`;
                 `balanced_map_trim cmp (SOME kx) bhi (t2:(K,V)balanced_map)`;
                 `t2:(K,V)balanced_map`] LIBXAUX_restrict_eq_lookup) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "tr2") THEN DISCH_THEN(LABEL_TAC "tr1") THEN
  LIBXAUX_PW2_TAC THEN LIBXAUX_PW_REWRITE2_TAC THEN
  LIBXAUX_KCASES_TAC `k0:K` `kx:K` THENL
   [MP_TAC(ISPECL [`cmp:K->K->ordering`; `blo:K option`; `bhi:K option`; `kx:K`; `k0:K`]
           LIBXAUX_range_lt) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `~((k0:K) IN restrict_set (cmp:K->K->ordering) (SOME kx) bhi)`
      (fun th -> REWRITE_TAC[th]) THENL
     [DISCH_THEN(MP_TAC o MATCH_MP (CONJUNCT2 LIBXAUX_range_bound)) THEN LIBXAUX_GC_TAC;
      ALL_TAC] THEN
    COND_CASES_TAC THEN REWRITE_TAC[option_CASE] THEN
    QCASES_ON "balanced_map_lookup (cmp:K->K->ordering) k0 (l:(K,V)balanced_map)" THEN
    ASM_REWRITE_TAC[option_CASE] THEN
    QCASES_ON "balanced_map_lookup (cmp:K->K->ordering) k0 (t2:(K,V)balanced_map)" THEN
    ASM_REWRITE_TAC[option_CASE];
    SUBGOAL_THEN `(k0:K) IN restrict_set (cmp:K->K->ordering) blo bhi`
      (fun th -> REWRITE_TAC[th; option_CASE]) THENL
     [MP_TAC(ISPECL [`cmp:K->K->ordering`; `blo:K option`; `bhi:K option`;
                     `kx:K`; `k0:K`] LIBXAUX_restrict_set_cmp) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`cmp:K->K->ordering`; `t2:(K,V)balanced_map`; `k0:K`; `kx:K`]
           LIBXAUX_lookup_EQUAL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
    QCASES_ON "balanced_map_lookup (cmp:K->K->ordering) kx (t2:(K,V)balanced_map)" THEN
    ASM_REWRITE_TAC[option_CASE];
    MP_TAC(ISPECL [`cmp:K->K->ordering`; `blo:K option`; `bhi:K option`; `kx:K`; `k0:K`]
           LIBXAUX_range_gt) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN LIBXAUX_GC_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `~((k0:K) IN restrict_set (cmp:K->K->ordering) blo (SOME kx))`
      MP_TAC THENL
     [DISCH_THEN(MP_TAC o MATCH_MP (CONJUNCT1 LIBXAUX_range_bound)) THEN LIBXAUX_GC_TAC;
      DISCH_THEN(fun th -> REWRITE_TAC[th; option_CASE])] THEN
    COND_CASES_TAC THEN REWRITE_TAC[option_CASE] THEN
    QCASES_ON "balanced_map_lookup (cmp:K->K->ordering) k0 (r:(K,V)balanced_map)" THEN
    ASM_REWRITE_TAC[option_CASE] THEN
    QCASES_ON "balanced_map_lookup (cmp:K->K->ordering) k0 (t2:(K,V)balanced_map)" THEN
    ASM_REWRITE_TAC[option_CASE]]);;
(* HOL4: hedgeUnionWithKey_thm (local there) *)

let hedgeUnionWithKey_thm = prove
 (`!(cmp:K->K->ordering) (f:K->V->V->V) blo bhi (t1:(K,V)balanced_map) t2.
     good_cmp cmp /\ balanced_map_invariant cmp t1 /\
     balanced_map_invariant cmp t2 /\
     bounded_all cmp blo bhi t1 /\ bounded_root cmp blo bhi t2 /\
     (!k1 k2 x y. cmp k1 k2 = EQUAL ==> f k1 x y = f k2 x y)
     ==> balanced_map_invariant cmp (hedgeUnionWithKey cmp f blo bhi t1 t2) /\
         to_fmap cmp (hedgeUnionWithKey cmp f blo bhi t1 t2) =
         restrict_domain cmp blo bhi
           (FMERGE_WITH_KEY (\ks x y. f (CHOICE ks) x y)
              (to_fmap cmp t1) (to_fmap cmp t2))`,
  MATCH_MP_TAC hedgeUnionWithKey_ind THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[hedgeUnionWithKey_def; CONJUNCT1 to_fmap_def;
                 FMERGE_WITH_KEY_FEMPTY; LIBXAUX_bounded_restrict_id];
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[LIBXAUX_bounded_root]) THEN
    ASM_SIMP_TAC[hedgeUnionWithKey_def; CONJUNCT1 to_fmap_def;
                 FMERGE_WITH_KEY_FEMPTY; LIBXAUX_hedge_tip];
    REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
    STRIP_TAC THEN REWRITE_TAC[hedgeUnionWithKey_def; LET_DEF; LET_END_DEF] THEN
    MATCH_MP_TAC LIBXAUX_hedgeUnionWithKey_step THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC]);;

let unionWithKey_thm = prove
 (`!(cmp:K->K->ordering) (f:K->V->V->V) (t1:(K,V)balanced_map) t2.
     good_cmp cmp /\ balanced_map_invariant cmp t1 /\
     balanced_map_invariant cmp t2 /\
     (!k1 k2 x y. cmp k1 k2 = EQUAL ==> f k1 x y = f k2 x y)
     ==> balanced_map_invariant cmp (unionWithKey cmp f t1 t2) /\
         to_fmap cmp (unionWithKey cmp f t1 t2) =
         FMERGE_WITH_KEY (\ks x y. f (CHOICE ks) x y)
           (to_fmap cmp t1) (to_fmap cmp t2)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `t1:(K,V)balanced_map` (cases "balanced_map")) THEN
  STRUCT_CASES_TAC(ISPEC `t2:(K,V)balanced_map` (cases "balanced_map")) THEN
  REWRITE_TAC[unionWithKey_def; CONJUNCT1 to_fmap_def; FMERGE_WITH_KEY_FEMPTY] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`cmp:K->K->ordering`; `f:K->V->V->V`; `NONE:K option`; `NONE:K option`;
                 `Bin a0 a1 a2 a3 a4:(K,V)balanced_map`;
                 `Bin a0' a1' a2' a3' a4':(K,V)balanced_map`] hedgeUnionWithKey_thm) THEN
  ASM_REWRITE_TAC[bounded_all_NONE; LIBXAUX_bounded_root; LIBXAUX_IN_restrict_set] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  LIBXAUX_PW2_TAC THEN
  ASM_SIMP_TAC[LIBXAUX_FLOOKUP_restrict; LIBXAUX_IN_restrict_set]);;

(* HOL4: unionWith_thm (mlmap has unionWith_thm) *)

let balanced_map_unionWith_thm = prove
 (`!(cmp:K->K->ordering) (f:V->V->V) (t1:(K,V)balanced_map) t2.
     good_cmp cmp /\ balanced_map_invariant cmp t1 /\ balanced_map_invariant cmp t2
     ==> balanced_map_invariant cmp (unionWith cmp f t1 t2) /\
         to_fmap cmp (unionWith cmp f t1 t2) =
         FMERGE_WITH_KEY (\ks x y. f x y) (to_fmap cmp t1) (to_fmap cmp t2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[unionWith_def] THEN
  MP_TAC(ISPECL [`cmp:K->K->ordering`; `\(k:K) (x:V) (y:V). (f:V->V->V) x y`;
                 `t1:(K,V)balanced_map`; `t2:(K,V)balanced_map`] unionWithKey_thm) THEN
  ASM_REWRITE_TAC[]);;

let lookup_unionWithKey = prove
 (CASE_TERM
  `!(cmp:K->K->ordering) (f:K->V->V->V) (t1:(K,V)balanced_map) t2 k.
     good_cmp cmp /\ balanced_map_invariant cmp t1 /\
     balanced_map_invariant cmp t2 /\
     (!k1 k2 x y. cmp k1 k2 = EQUAL ==> f k1 x y = f k2 x y)
     ==> balanced_map_lookup cmp k (unionWithKey cmp f t1 t2) =
         match balanced_map_lookup cmp k t1 with
           NONE -> balanced_map_lookup cmp k t2
         | SOME v1 -> (match balanced_map_lookup cmp k t2 with
                         NONE -> SOME v1
                       | SOME v2 -> SOME (f k v1 v2))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`cmp:K->K->ordering`; `f:K->V->V->V`; `t1:(K,V)balanced_map`;
                 `t2:(K,V)balanced_map`] unionWithKey_thm) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[lookup_thm; FLOOKUP_FMERGE_WITH_KEY] THEN
  ASM_SIMP_TAC[GSYM lookup_thm] THEN
  QCASES_ON "balanced_map_lookup (cmp:K->K->ordering) k (t1:(K,V)balanced_map)" THEN
  ASM_REWRITE_TAC[option_CASE] THEN
  QCASES_ON "balanced_map_lookup (cmp:K->K->ordering) k (t2:(K,V)balanced_map)" THEN
  ASM_REWRITE_TAC[option_CASE; option_INJ] THEN
  MATCH_MP_TAC LIBXAUX_CHOICE_key_set THEN ASM_REWRITE_TAC[]);;

let lookup_unionWith = prove
 (CASE_TERM
  `!(cmp:K->K->ordering) (f:V->V->V) (t1:(K,V)balanced_map) t2 k.
     good_cmp cmp /\ balanced_map_invariant cmp t1 /\
     balanced_map_invariant cmp t2
     ==> balanced_map_lookup cmp k (unionWith cmp f t1 t2) =
         match balanced_map_lookup cmp k t1 with
           NONE -> balanced_map_lookup cmp k t2
         | SOME v1 -> (match balanced_map_lookup cmp k t2 with
                         NONE -> SOME v1
                       | SOME v2 -> SOME (f v1 v2))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[unionWith_def] THEN
  MP_TAC(ISPECL [`cmp:K->K->ordering`; `\(k:K) (x:V) (y:V). (f:V->V->V) x y`;
                 `t1:(K,V)balanced_map`; `t2:(K,V)balanced_map`; `k:K`]
                lookup_unionWithKey) THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* HOL4 balanced_mapScript.sml lines 3058-3227 and 3895-4066: EXT2 and       *)
(* toAscList_helper (local there; LIBXAUX_A_EXT2,                            *)
(* LIBXAUX_A_toAscList_helper), toAscList_thm, MAP_FST_toAscList,            *)
(* MEM_toAscList, ALOOKUP_toAscList; map_keys and lift_key (defined above)   *)
(* with the local in_lift_key, bigunion_key_sets and image_lem as helpers;   *)
(* every_thm and exists_thm (balanced_map_every_thm,                         *)
(* balanced_map_exists_thm).                                                 *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Small tactics: reasoning with the laws of a good comparison, and          *)
(* rewriting key_set equations into comparisons.                             *)
(* ------------------------------------------------------------------------- *)

let LIBXAUX_A_GC_TAC (ths:thm list) : tactic =
  FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP LBMAPAUX_good_cmp th)) THEN
  MESON_TAC ths;;

let LIBXAUX_A_KSE_TAC : tactic =
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP key_set_eq th]);;

(* ------------------------------------------------------------------------- *)
(* Helpers.                                                                  *)
(* ------------------------------------------------------------------------- *)

(* HOL4 EXT2 (local) *)

let LIBXAUX_A_EXT2 = prove
 (`!(s1:A#B->bool) s2. s1 = s2 <=> (!k v. (k,v) IN s1 <=> (k,v) IN s2)`,
  REWRITE_TAC[EXTENSION; FORALL_PAIR_THM]);;

let LIBXAUX_A_IN_lift_key = prove
 (`!(cmp:K->K->ordering) (s:K#V->bool) ks v.
     (ks,v) IN lift_key cmp s <=> ?k. (k,v) IN s /\ ks = key_set cmp k`,
  REWRITE_TAC[lift_key_def; IN_IMAGE; EXISTS_PAIR_THM] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[]);;

let LIBXAUX_A_lift_key_INSERT = prove
 (`!(cmp:K->K->ordering) k (v:V) s.
     lift_key cmp ((k,v) INSERT s) = (key_set cmp k,v) INSERT lift_key cmp s`,
  REWRITE_TAC[lift_key_def; IMAGE_CLAUSES] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[]);;

let LIBXAUX_A_ko_FLOOKUP = prove
 (`!(cmp:K->K->ordering) k (t:(K,V)balanced_map) res k' v.
     good_cmp cmp /\ key_ordered cmp k t res /\
     FLOOKUP (to_fmap cmp t) (key_set cmp k') = SOME v
     ==> cmp k k' = res`,
  MESON_TAC[LBMAPAUX_key_ordered_FDOM; flookup_thm]);;

(* The finite map of a tree with the invariant, entry by entry. *)

let LIBXAUX_A_FLOOKUP_Bin = prove
 (`!(cmp:K->K->ordering) s k (v:V) l r.
     good_cmp cmp /\ balanced_map_invariant cmp (Bin s k v l r)
     ==> !x y. FLOOKUP (to_fmap cmp (Bin s k v l r)) x = SOME y <=>
               FLOOKUP (to_fmap cmp l) x = SOME y \/
               (x = key_set cmp k /\ y = v) \/
               FLOOKUP (to_fmap cmp r) x = SOME y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[invariant_eq] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[to_fmap_def; FLOOKUP_UPDATE; FLOOKUP_FUNION] THEN
  ASM_CASES_TAC `key_set (cmp:K->K->ordering) k = x` THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM flookup_thm]) THEN
    ASM_REWRITE_TAC[option_DISTINCT; option_INJ; EQ_SYM_EQ];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `~(FLOOKUP (to_fmap cmp (l:(K,V)balanced_map)) x = NONE)
    ==> FLOOKUP (to_fmap cmp (r:(K,V)balanced_map)) x = NONE`
  MP_TAC THENL
   [UNDISCH_TAC `DISJOINT (FDOM (to_fmap cmp (l:(K,V)balanced_map)))
                          (FDOM (to_fmap cmp (r:(K,V)balanced_map)))` THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; FDOM_FLOOKUP] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `FLOOKUP (to_fmap cmp (l:(K,V)balanced_map)) x`
           (cases "option")) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[option_CASE; option_DISTINCT] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[option_DISTINCT]);;

(* ------------------------------------------------------------------------- *)
(* toAscList.                                                                *)
(* ------------------------------------------------------------------------- *)

(* HOL4 toAscList_helper (local) *)

let LIBXAUX_A_toAscList_helper = prove
 (`!(cmp:K->K->ordering) (l:(K#V)list) (t:(K,V)balanced_map).
     good_cmp cmp /\
     balanced_map_invariant cmp t /\
     SORTED (\(x:K,y:V) (x':K,y':V). cmp x x' = LESS) l /\
     (!k1 v1 k2 v2.
        MEM (k1,v1) l /\ FLOOKUP (to_fmap cmp t) (key_set cmp k2) = SOME v2
        ==> cmp k2 k1 = LESS)
     ==> SORTED (\(x:K,y:V) (x':K,y':V). cmp x x' = LESS)
                (foldrWithKey (\k x xs. CONS (k,x) xs) l t) /\
         lift_key cmp (set_of_list (foldrWithKey (\k x xs. CONS (k,x) xs) l t)) =
         set_of_list (fmap_to_alist (to_fmap cmp t)) UNION
         lift_key cmp (set_of_list l)`,
  GEN_TAC THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  MATCH_MP_TAC balanced_map_INDUCT THEN CONJ_TAC THENL
   [SIMP_TAC[foldrWithKey_def; to_fmap_def; fmap_to_alist_FEMPTY; set_of_list;
             UNION_EMPTY];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:num`; `k:K`; `v:V`; `t1:(K,V)balanced_map`;
                       `t2:(K,V)balanced_map`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
  X_GEN_TAC `l:(K#V)list` THEN REWRITE_TAC[foldrWithKey_def] THEN
  STRIP_TAC THEN POP_ASSUM(LABEL_TAC "H") THEN
  (* the facts of the invariant *)
  SUBGOAL_THEN
   `!x y. FLOOKUP (to_fmap (cmp:K->K->ordering) (Bin s k v t1 t2)) x = SOME y <=>
          FLOOKUP (to_fmap cmp t1) x = SOME y \/
          (x = key_set cmp k /\ y = (v:V)) \/
          FLOOKUP (to_fmap cmp t2) x = SOME y`
  (LABEL_TAC "fb") THENL
   [MATCH_MP_TAC LIBXAUX_A_FLOOKUP_Bin THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `balanced_map_invariant (cmp:K->K->ordering) (t1:(K,V)balanced_map) /\
    balanced_map_invariant cmp (t2:(K,V)balanced_map) /\
    key_ordered cmp (k:K) t1 GREATER /\ key_ordered cmp k t2 LESS`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC
     `balanced_map_invariant (cmp:K->K->ordering) (Bin s k (v:V) t1 t2)` THEN
    REWRITE_TAC[balanced_map_invariant_def] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the hypothesis on l, for each part of the tree *)
  SUBGOAL_THEN
   `(!k1 (v1:V) k2 v2.
       MEM (k1,v1) (l:(K#V)list) /\
       FLOOKUP (to_fmap (cmp:K->K->ordering) (t1:(K,V)balanced_map))
               (key_set cmp k2) = SOME v2
       ==> cmp k2 k1 = LESS) /\
    (!k1 (v1:V). MEM (k1,v1) l ==> cmp (k:K) k1 = LESS) /\
    (!k1 (v1:V) k2 v2.
       MEM (k1,v1) l /\
       FLOOKUP (to_fmap cmp (t2:(K,V)balanced_map)) (key_set cmp k2) = SOME v2
       ==> cmp k2 k1 = LESS)`
  STRIP_ASSUME_TAC THENL
   [REMOVE_THEN "H" MP_TAC THEN USE_THEN "fb" (fun th -> REWRITE_TAC[th]) THEN
    MESON_TAC[];
    ALL_TAC] THEN
  (* the right subtree, onto l *)
  REMOVE_THEN "ih2" (MP_TAC o SPEC `l:(K#V)list`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!k1 (v1:V).
      MEM (k1,v1) (foldrWithKey (\k x xs. CONS (k,x) xs) (l:(K#V)list)
                     (t2:(K,V)balanced_map))
      ==> FLOOKUP (to_fmap (cmp:K->K->ordering) t2) (key_set cmp k1) = SOME v1 \/
          ?k1'. MEM (k1',v1) l /\ cmp k1' k1 = EQUAL`
  (LABEL_TAC "m2") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `(key_set (cmp:K->K->ordering) k1,(v1:V)) IN
      lift_key cmp (set_of_list (foldrWithKey (\k x xs. CONS (k,x) xs)
                                   (l:(K#V)list) (t2:(K,V)balanced_map)))`
    MP_TAC THENL
     [REWRITE_TAC[LIBXAUX_A_IN_lift_key; IN_SET_OF_LIST] THEN
      EXISTS_TAC `k1:K` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IN_UNION; IN_SET_OF_LIST; MEM_pair_fmap_to_alist_FLOOKUP;
                LIBXAUX_A_IN_lift_key] THEN
    LIBXAUX_A_KSE_TAC THEN LIBXAUX_A_GC_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k1 (v1:V).
      MEM (k1,v1) (foldrWithKey (\k x xs. CONS (k,x) xs) (l:(K#V)list)
                     (t2:(K,V)balanced_map))
      ==> (cmp:K->K->ordering) k k1 = LESS`
  (LABEL_TAC "k2") THENL
   [REPEAT GEN_TAC THEN
    DISCH_THEN(fun th ->
      USE_THEN "m2" (fun m2 -> DISJ_CASES_TAC(MATCH_MP m2 th))) THENL
     [MATCH_MP_TAC LIBXAUX_A_ko_FLOOKUP THEN
      MAP_EVERY EXISTS_TAC [`t2:(K,V)balanced_map`; `v1:V`] THEN
      ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(X_CHOOSE_THEN `k1':K` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(cmp:K->K->ordering) k k1' = LESS` MP_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(cmp:K->K->ordering) k1' k1 = EQUAL` THEN
      LIBXAUX_A_GC_TAC[]];
    ALL_TAC] THEN
  (* the left subtree, onto (k,v) and the list of the right subtree *)
  REMOVE_THEN "ih1" (MP_TAC o SPEC
    `CONS (k:K,v:V) (foldrWithKey (\k x xs. CONS (k,x) xs) (l:(K#V)list)
                       (t2:(K,V)balanced_map))`) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [FIRST_ASSUM(fun th -> SIMP_TAC[SORTED_EQ; INST_TYPE [`:K`,`:A`; `:V`,`:B`]
        (MATCH_MP good_cmp_trans th)]) THEN
      REWRITE_TAC[FORALL_PAIR_THM] THEN
      CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[MEM; PAIR_EQ] THEN REPEAT GEN_TAC THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
      SUBGOAL_THEN `(cmp:K->K->ordering) k k2 = GREATER` MP_TAC THENL
       [MATCH_MP_TAC LIBXAUX_A_ko_FLOOKUP THEN
        MAP_EVERY EXISTS_TAC [`t1:(K,V)balanced_map`; `v2:V`] THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(cmp:K->K->ordering) k k1 = LESS \/ k1 = k` MP_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      LIBXAUX_A_GC_TAC[]];
    ALL_TAC] THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC[set_of_list; LIBXAUX_A_lift_key_INSERT] THEN
  REWRITE_TAC[LIBXAUX_A_EXT2; IN_UNION; IN_INSERT; IN_SET_OF_LIST;
              MEM_pair_fmap_to_alist_FLOOKUP; PAIR_EQ] THEN
  USE_THEN "fb" (fun th -> REWRITE_TAC[th]) THEN
  REPEAT GEN_TAC THEN CONV_TAC TAUT);;

let toAscList_thm = prove
 (`!(cmp:K->K->ordering) (t:(K,V)balanced_map).
     good_cmp cmp /\ balanced_map_invariant cmp t
     ==> SORTED (\(x:K,y:V) (x':K,y':V). cmp x x' = LESS) (toAscList t) /\
         lift_key cmp (set_of_list (toAscList t)) =
         set_of_list (fmap_to_alist (to_fmap cmp t))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`cmp:K->K->ordering`; `[]:(K#V)list`; `t:(K,V)balanced_map`]
                LIBXAUX_A_toAscList_helper) THEN
  ASM_REWRITE_TAC[toAscList_def; MEM; SORTED_DEF; set_of_list; lift_key_def;
                  IMAGE_CLAUSES; UNION_EMPTY]);;

(* ------------------------------------------------------------------------- *)
(* Specialisations of toAscList_thm.                                         *)
(* ------------------------------------------------------------------------- *)

let MAP_FST_toAscList = prove
 (`!(cmp:K->K->ordering) (t:(K,V)balanced_map).
     good_cmp cmp /\ balanced_map_invariant cmp t
     ==> SORTED (\x y. cmp x y = LESS) (MAP FST (toAscList t)) /\
         FDOM (to_fmap cmp t) =
         IMAGE (key_set cmp) (set_of_list (MAP FST (toAscList t)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP toAscList_thm) THEN CONJ_TAC THENL
   [SUBGOAL_THEN
     `inv_image (\x y. (cmp:K->K->ordering) x y = LESS) (FST:K#V->K) =
      (\(x:K,y:V) (x':K,y':V). cmp x x' = LESS)`
     (fun th -> ASM_REWRITE_TAC[sorted_map; th]) THEN
    REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; inv_image_THM] THEN
    CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[FST];
    ALL_TAC] THEN
  REWRITE_TAC[EXTENSION] THEN X_GEN_TAC `ks:K->bool` THEN
  SUBGOAL_THEN
   `ks IN FDOM (to_fmap (cmp:K->K->ordering) (t:(K,V)balanced_map)) <=>
    ?v:V. (ks,v) IN lift_key cmp (set_of_list (toAscList t))`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[IN_SET_OF_LIST; MEM_pair_fmap_to_alist_FLOOKUP] THEN
    MESON_TAC[flookup_thm];
    ALL_TAC] THEN
  REWRITE_TAC[LIBXAUX_A_IN_lift_key; IN_IMAGE; IN_SET_OF_LIST; MEM_MAP;
              EXISTS_PAIR_THM; FST] THEN
  MESON_TAC[]);;

let MEM_toAscList = prove
 (`!(cmp:K->K->ordering) (t:(K,V)balanced_map) k v.
     good_cmp cmp /\ balanced_map_invariant cmp t /\ MEM (k,v) (toAscList t)
     ==> FLOOKUP (to_fmap cmp t) (key_set cmp k) = SOME v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`cmp:K->K->ordering`; `t:(K,V)balanced_map`] toAscList_thm) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `(key_set (cmp:K->K->ordering) k,(v:V))` o
             REWRITE_RULE[EXTENSION] o CONJUNCT2) THEN
  REWRITE_TAC[LIBXAUX_A_IN_lift_key; IN_SET_OF_LIST;
              MEM_pair_fmap_to_alist_FLOOKUP] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN EXISTS_TAC `k:K` THEN ASM_REWRITE_TAC[]);;

let ALOOKUP_toAscList = prove
 (`!(cmp:K->K->ordering) (t:(K,V)balanced_map) k.
     good_cmp cmp /\ balanced_map_invariant cmp t /\
     (!x y. cmp x y = EQUAL <=> x = y)
     ==> ALOOKUP (toAscList t) k = balanced_map_lookup cmp k t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[lookup_thm] THEN
  SUBGOAL_THEN `ALL_DISTINCT (MAP FST (toAscList (t:(K,V)balanced_map)))`
  ASSUME_TAC THENL
   [MP_TAC(ISPEC `\x y. (cmp:K->K->ordering) x y = LESS` SORTED_ALL_DISTINCT) THEN
    ASM_SIMP_TAC[good_cmp_Less_irrefl_trans] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[MAP_FST_toAscList];
    ALL_TAC] THEN
  MP_TAC(ISPEC `FLOOKUP (to_fmap cmp (t:(K,V)balanced_map)) (key_set cmp k)`
           (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_TAC `w:V`)) THEN
  ASM_REWRITE_TAC[] THENL
   [MP_TAC(ISPEC `ALOOKUP (toAscList (t:(K,V)balanced_map)) (k:K)`
             (cases "option")) THEN
    DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_TAC `u:V`)) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP ALOOKUP_MEM) THEN
    MP_TAC(ISPECL [`cmp:K->K->ordering`; `t:(K,V)balanced_map`; `k:K`; `u:V`]
                  MEM_toAscList) THEN
    ASM_REWRITE_TAC[option_DISTINCT];
    ALL_TAC] THEN
  MATCH_MP_TAC ALOOKUP_ALL_DISTINCT_MEM THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`cmp:K->K->ordering`; `t:(K,V)balanced_map`] toAscList_thm) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `(key_set (cmp:K->K->ordering) k,(w:V))` o
             REWRITE_RULE[EXTENSION] o CONJUNCT2) THEN
  ASM_REWRITE_TAC[LIBXAUX_A_IN_lift_key; IN_SET_OF_LIST;
                  MEM_pair_fmap_to_alist_FLOOKUP] THEN
  LIBXAUX_A_KSE_TAC THEN ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* every and exists (HOL4 every_thm and exists_thm).                         *)
(* ------------------------------------------------------------------------- *)

let balanced_map_every_thm = prove
 (`!(f:K->V->bool) (t:(K,V)balanced_map) (cmp:K->K->ordering).
     good_cmp cmp /\ balanced_map_invariant cmp t /\ resp_equiv cmp f
     ==> (balanced_map_every f t <=>
          !k v. balanced_map_lookup cmp k t = SOME v ==> f k v)`,
  GEN_TAC THEN MATCH_MP_TAC balanced_map_INDUCT THEN CONJ_TAC THENL
   [REWRITE_TAC[balanced_map_every_def; balanced_map_lookup_def;
                option_DISTINCT];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:num`; `kx:K`; `x:V`; `l:(K,V)balanced_map`;
                       `r:(K,V)balanced_map`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ihl") (LABEL_TAC "ihr")) THEN
  X_GEN_TAC `cmp:K->K->ordering` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `balanced_map_invariant (cmp:K->K->ordering) (l:(K,V)balanced_map) /\
    balanced_map_invariant cmp (r:(K,V)balanced_map)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC
     `balanced_map_invariant (cmp:K->K->ordering) (Bin s kx (x:V) l r)` THEN
    REWRITE_TAC[balanced_map_invariant_def] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[balanced_map_every_def;
    TAUT `(if a then if b then if c then T else F else F else F) <=>
          a /\ b /\ c`] THEN
  REMOVE_THEN "ihl" (MP_TAC o SPEC `cmp:K->K->ordering`) THEN
  REMOVE_THEN "ihr" (MP_TAC o SPEC `cmp:K->K->ordering`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[lookup_thm; LIBXAUX_A_FLOOKUP_Bin] THEN
  LIBXAUX_A_KSE_TAC THEN
  REWRITE_TAC[TAUT `(a \/ b \/ c ==> d) <=> (a ==> d) /\ (b ==> d) /\ (c ==> d)`;
              FORALL_AND_THM] THEN
  SUBGOAL_THEN
   `(!k v. (cmp:K->K->ordering) k kx = EQUAL /\ v = x ==> (f:K->V->bool) k v)
    <=> f kx x`
  SUBST1_TAC THENL
   [UNDISCH_TAC `resp_equiv (cmp:K->K->ordering) (f:K->V->bool)` THEN
    REWRITE_TAC[resp_equiv_def] THEN LIBXAUX_A_GC_TAC[];
    ALL_TAC] THEN
  CONV_TAC TAUT);;

let balanced_map_exists_thm = prove
 (`!(f:K->V->bool) (t:(K,V)balanced_map) (cmp:K->K->ordering).
     good_cmp cmp /\ balanced_map_invariant cmp t /\ resp_equiv cmp f
     ==> (balanced_map_exists f t <=>
          ?k v. balanced_map_lookup cmp k t = SOME v /\ f k v)`,
  GEN_TAC THEN MATCH_MP_TAC balanced_map_INDUCT THEN CONJ_TAC THENL
   [REWRITE_TAC[balanced_map_exists_def; balanced_map_lookup_def;
                option_DISTINCT];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:num`; `kx:K`; `x:V`; `l:(K,V)balanced_map`;
                       `r:(K,V)balanced_map`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ihl") (LABEL_TAC "ihr")) THEN
  X_GEN_TAC `cmp:K->K->ordering` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `balanced_map_invariant (cmp:K->K->ordering) (l:(K,V)balanced_map) /\
    balanced_map_invariant cmp (r:(K,V)balanced_map)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC
     `balanced_map_invariant (cmp:K->K->ordering) (Bin s kx (x:V) l r)` THEN
    REWRITE_TAC[balanced_map_invariant_def] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[balanced_map_exists_def;
    TAUT `(if a then T else if b then T else if c then T else F) <=>
          a \/ b \/ c`] THEN
  REMOVE_THEN "ihl" (MP_TAC o SPEC `cmp:K->K->ordering`) THEN
  REMOVE_THEN "ihr" (MP_TAC o SPEC `cmp:K->K->ordering`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[lookup_thm; LIBXAUX_A_FLOOKUP_Bin] THEN
  LIBXAUX_A_KSE_TAC THEN
  REWRITE_TAC[TAUT `(a \/ b \/ c) /\ d <=> a /\ d \/ b /\ d \/ c /\ d`;
              EXISTS_OR_THM] THEN
  SUBGOAL_THEN
   `(?k v. ((cmp:K->K->ordering) k kx = EQUAL /\ v = x) /\ (f:K->V->bool) k v)
    <=> f kx x`
  SUBST1_TAC THENL
   [UNDISCH_TAC `resp_equiv (cmp:K->K->ordering) (f:K->V->bool)` THEN
    REWRITE_TAC[resp_equiv_def] THEN LIBXAUX_A_GC_TAC[];
    ALL_TAC] THEN
  CONV_TAC TAUT);;

(* ========================================================================= *)
(* HOL4 balanced_mapScript.sml lines 4067-4165: filterWithKey_thm,           *)
(* every_filter, filter_thm (balanced_map_filter_thm).                       *)
(* ========================================================================= *)

(* filterWithKey keeps the entries whose key and value satisfy f *)

let LIBXAUX_lookup_ko_SUB = prove
 (`!(cmp:K->K->ordering) a (t:(K,V)balanced_map) t' res.
     good_cmp cmp /\ balanced_map_invariant cmp t /\
     balanced_map_invariant cmp t' /\ key_ordered cmp a t res /\
     (!k. balanced_map_lookup cmp k t' = NONE \/
          balanced_map_lookup cmp k t' = balanced_map_lookup cmp k t)
     ==> key_ordered cmp a t' res`,
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC `key_ordered (cmp:K->K->ordering) a (t:(K,V)balanced_map) res` THEN
  ASM_SIMP_TAC[key_ordered_to_fmap] THEN DISCH_TAC THEN
  X_GEN_TAC `ks:K->bool` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP to_fmap_key_set) THEN
  DISCH_THEN(X_CHOOSE_THEN `k1:K` SUBST_ALL_TAC) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  UNDISCH_TAC `key_set (cmp:K->K->ordering) k1 IN FDOM (to_fmap cmp (t':(K,V)balanced_map))` THEN
  ASM_SIMP_TAC[LIBXAUX_FDOM_lookup] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o SPEC `k1:K`) THEN ASM_REWRITE_TAC[]);;

let LIBXAUX_filterWithKey = prove
 (`!(t:(K,V)balanced_map) (cmp:K->K->ordering) (f:K->V->bool).
     good_cmp cmp /\ balanced_map_invariant cmp t /\
     (!k1 k2 x. cmp k1 k2 = EQUAL ==> f k1 x = f k2 x)
     ==> balanced_map_invariant cmp (filterWithKey f t) /\
         (!k. balanced_map_lookup cmp k (filterWithKey f t) =
              option_CASE (balanced_map_lookup cmp k t) NONE
                (\v. if f k v then SOME v else NONE))`,
  MATCH_MP_TAC balanced_map_INDUCT THEN
  REWRITE_TAC[filterWithKey_def; CONJUNCT1 invariant_eq; balanced_map_lookup_def;
              option_CASE] THEN
  MAP_EVERY X_GEN_TAC [`s:num`; `kx:K`; `x:V`; `l:(K,V)balanced_map`;
                       `r:(K,V)balanced_map`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ihl") (LABEL_TAC "ihr")) THEN
  MAP_EVERY X_GEN_TAC [`cmp:K->K->ordering`; `f:K->V->bool`] THEN STRIP_TAC THEN
  LIBXAUX_INV_BIN2_TAC THEN
  REMOVE_THEN "ihl" (MP_TAC o SPECL [`cmp:K->K->ordering`; `f:K->V->bool`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REMOVE_THEN "ihr" (MP_TAC o SPECL [`cmp:K->K->ordering`; `f:K->V->bool`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  SUBGOAL_THEN
   `key_ordered cmp kx (filterWithKey f l) GREATER /\
    key_ordered cmp kx (filterWithKey (f:K->V->bool) (r:(K,V)balanced_map)) LESS`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC LIBXAUX_lookup_ko_SUB THENL
     [EXISTS_TAC `l:(K,V)balanced_map`; EXISTS_TAC `r:(K,V)balanced_map`] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `k0:K` THEN
    QCASES_ON "balanced_map_lookup (cmp:K->K->ordering) k0 (l:(K,V)balanced_map)" THEN
    QCASES_ON "balanced_map_lookup (cmp:K->K->ordering) k0 (r:(K,V)balanced_map)" THEN
    ASM_REWRITE_TAC[option_CASE] THEN COND_CASES_TAC THEN REWRITE_TAC[];
    ALL_TAC] THEN
  COND_CASES_TAC THENL
   [MP_TAC(ISPECL [`kx:K`; `x:V`; `filterWithKey (f:K->V->bool) (l:(K,V)balanced_map)`;
                   `filterWithKey (f:K->V->bool) (r:(K,V)balanced_map)`;
                   `cmp:K->K->ordering`] link_thm);
    MP_TAC(ISPECL [`filterWithKey (f:K->V->bool) (l:(K,V)balanced_map)`;
                   `filterWithKey (f:K->V->bool) (r:(K,V)balanced_map)`;
                   `cmp:K->K->ordering`; `kx:K`] link2_thm)] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  (X_GEN_TAC `k0:K` THEN
  W(fun (_,w) -> MP_TAC(ISPECL [`cmp:K->K->ordering`; `k0:K`; rand(lhs w)] lookup_thm)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
  LIBXAUX_PW_REWRITE_TAC THEN
  LIBXAUX_KCASES_TAC `k0:K` `kx:K` THENL
   [SUBGOAL_THEN `balanced_map_lookup (cmp:K->K->ordering) k0 (r:(K,V)balanced_map) = NONE`
      SUBST1_TAC THENL [LIBXAUX_LKNONE_TAC `kx:K` `LESS`; ALL_TAC] THEN
    REWRITE_TAC[option_CASE] THEN
    QCASES_ON "balanced_map_lookup (cmp:K->K->ordering) k0 (l:(K,V)balanced_map)" THEN
    ASM_REWRITE_TAC[option_CASE] THEN COND_CASES_TAC THEN REWRITE_TAC[option_CASE];
    SUBGOAL_THEN `balanced_map_lookup (cmp:K->K->ordering) k0 (l:(K,V)balanced_map) = NONE /\
                  balanced_map_lookup (cmp:K->K->ordering) k0 (r:(K,V)balanced_map) = NONE`
      MP_TAC THENL
     [CONJ_TAC THENL [LIBXAUX_LKNONE_TAC `kx:K` `GREATER`; LIBXAUX_LKNONE_TAC `kx:K` `LESS`];
      DISCH_THEN(fun th -> REWRITE_TAC[th; option_CASE])] THEN
    SUBGOAL_THEN `(f:K->V->bool) k0 x <=> f kx x` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      DISCH_THEN(fun th -> ASM_REWRITE_TAC[th])];
    SUBGOAL_THEN `balanced_map_lookup (cmp:K->K->ordering) k0 (l:(K,V)balanced_map) = NONE`
      SUBST1_TAC THENL [LIBXAUX_LKNONE_TAC `kx:K` `GREATER`; ALL_TAC] THEN
    REWRITE_TAC[option_CASE] THEN
    QCASES_ON "balanced_map_lookup (cmp:K->K->ordering) k0 (r:(K,V)balanced_map)" THEN
    ASM_REWRITE_TAC[option_CASE] THEN COND_CASES_TAC THEN REWRITE_TAC[option_CASE]]));;
let LIBXAUX_CHOICE_key_set1 = prove
 (`!(cmp:K->K->ordering) (f:K->V->bool) k x.
     good_cmp cmp /\ (!k1 k2 x. cmp k1 k2 = EQUAL ==> (f k1 x <=> f k2 x))
     ==> (f (CHOICE (key_set cmp k)) x <=> f k x)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  MP_TAC(ISPECL [`cmp:K->K->ordering`; `k:K`] key_set_nonempty) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP CHOICE_DEF) THEN
  REWRITE_TAC[key_set_def; IN_ELIM_THM] THEN DISCH_TAC THEN LIBXAUX_GC_TAC);;

let filterWithKey_thm = prove
 (`!(f:K->V->bool) (t:(K,V)balanced_map) (cmp:K->K->ordering).
     good_cmp cmp /\ balanced_map_invariant cmp t /\
     (!k1 k2 x. cmp k1 k2 = EQUAL ==> (f k1 x <=> f k2 x))
     ==> balanced_map_invariant cmp (filterWithKey f t) /\
         to_fmap cmp (filterWithKey f t) =
         FDIFF (to_fmap cmp t)
           {k | k,v | FLOOKUP (to_fmap cmp t) k = SOME v /\ ~f (CHOICE k) v}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!k x. (f:K->V->bool) (CHOICE (key_set cmp k)) x <=> f k x`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC LIBXAUX_CHOICE_key_set1 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(K,V)balanced_map`; `cmp:K->K->ordering`; `f:K->V->bool`]
                LIBXAUX_filterWithKey) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC LIBXAUX_FMAP_EXT_KEYS THEN EXISTS_TAC `cmp:K->K->ordering` THEN
  REWRITE_TAC[FDOM_FDIFF] THEN
  REPEAT CONJ_TAC THENL [MESON_TAC[to_fmap_key_set]; MESON_TAC[to_fmap_key_set]; ALL_TAC] THEN
  X_GEN_TAC `k0:K` THEN ASM_SIMP_TAC[LIBXAUX_FLOOKUP_to_fmap; FLOOKUP_FDIFF] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  SUBGOAL_THEN
   `(?k v. (FLOOKUP (to_fmap cmp t) k = SOME v /\ ~f (CHOICE k) v) /\
           key_set cmp k0 = k) <=>
    (?v. balanced_map_lookup cmp k0 (t:(K,V)balanced_map) = SOME v /\
         ~(f:K->V->bool) k0 v)`
  SUBST1_TAC THENL
   [EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `kk:K->bool` (X_CHOOSE_THEN `v:V` STRIP_ASSUME_TAC)) THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN EXISTS_TAC `v:V` THEN
      UNDISCH_TAC `FLOOKUP (to_fmap (cmp:K->K->ordering) (t:(K,V)balanced_map))
                     (key_set cmp k0) = SOME (v:V)` THEN
      UNDISCH_TAC `~(f:K->V->bool) (CHOICE (key_set (cmp:K->K->ordering) k0)) v` THEN
      ASM_SIMP_TAC[LIBXAUX_FLOOKUP_to_fmap];
      DISCH_THEN(X_CHOOSE_THEN `v:V` STRIP_ASSUME_TAC) THEN
      MAP_EVERY EXISTS_TAC [`key_set (cmp:K->K->ordering) k0`; `v:V`] THEN
      ASM_SIMP_TAC[LIBXAUX_FLOOKUP_to_fmap; LIBXAUX_CHOICE_key_set1]];
    ALL_TAC] THEN
  QCASES_ON "balanced_map_lookup (cmp:K->K->ordering) k0 (t:(K,V)balanced_map)" THEN
  ASM_REWRITE_TAC[option_CASE; option_INJ; option_DISTINCT; UNWIND_THM1] THEN
  COND_CASES_TAC THEN REWRITE_TAC[]);;

(* HOL4: every_filter, filter_thm (mlmap has filter_thm) *)

let every_filter = prove
 (`!(cmp:K->K->ordering) (t:(K,V)balanced_map) (f:K->V->bool).
     good_cmp cmp /\ balanced_map_invariant cmp t /\
     (!k1 k2 x. cmp k1 k2 = EQUAL ==> (f k1 x <=> f k2 x))
     ==> balanced_map_every f (filterWithKey f t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!k x. (f:K->V->bool) (CHOICE (key_set cmp k)) x <=> f k x`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC LIBXAUX_CHOICE_key_set1 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:K->V->bool`; `t:(K,V)balanced_map`; `cmp:K->K->ordering`]
                filterWithKey_thm) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:K->V->bool`; `filterWithKey (f:K->V->bool) (t:(K,V)balanced_map)`;
                 `cmp:K->K->ordering`] balanced_map_every_thm) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[resp_equiv_def]; DISCH_THEN SUBST1_TAC] THEN
  MAP_EVERY X_GEN_TAC [`k:K`; `v:V`] THEN
  ASM_SIMP_TAC[lookup_thm; FLOOKUP_FDIFF] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`key_set (cmp:K->K->ordering) k`; `v:V`] o
                REWRITE_RULE[NOT_EXISTS_THM]) THEN
  ASM_REWRITE_TAC[]);;

let balanced_map_filter_thm = prove
 (`!(f:V->bool) (t:(K,V)balanced_map) (cmp:K->K->ordering).
     good_cmp cmp /\ balanced_map_invariant cmp t
     ==> balanced_map_invariant cmp (balanced_map_filter f t) /\
         to_fmap cmp (balanced_map_filter f t) =
         FDIFF (to_fmap cmp t) {k | k,v | FLOOKUP (to_fmap cmp t) k = SOME v /\ ~f v}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[balanced_map_filter_def] THEN
  MP_TAC(ISPECL [`\(k:K) (x:V). (f:V->bool) x`; `t:(K,V)balanced_map`;
                 `cmp:K->K->ordering`] filterWithKey_thm) THEN
  ASM_REWRITE_TAC[]);;
