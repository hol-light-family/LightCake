(* ========================================================================= *)
(* balanced_map: port of HOL4 examples/data-structures/balanced_bst/        *)
(* balanced_mapScript.sml (HOL4 library used by CakeML v3479).              *)
(* Maps based on balanced binary trees, copied from ghc-7.8.3                *)
(* libraries/containers/Data/Map/Base.hs (Adams' size balanced trees).      *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - the type is (K,V)balanced_map (HOL4 ('k,'v) balanced_map).             *)
(* - names taken elsewhere get the prefix balanced_map_: lookup (sptree),    *)
(*   insert (sptree), empty (peg), invariant (source_to_flatProof), with     *)
(*   their definition theorems; HOL4 lookup_insert is                        *)
(*   balanced_map_lookup_insert (sptree has lookup_insert).                  *)
(* - HOL4 size (the stored size of a tree) is balanced_map_size': the name   *)
(*   balanced_map_size is the datatype size function (as in HOL4).           *)
(* - HOL4 FUNION is prefix here (HOL4 also writes it as an infix).           *)
(* - balanceL and balanceR are defined by one equation with a match (the     *)
(*   body of HOL4 balanceL' and balanceR'); balanceL_def and balanceR_def    *)
(*   are the HOL4 clauses, proved from it.                                   *)
(* - Only the part of the theory that CakeML uses is ported: the            *)
(*   definitions up to insert, the invariant, to_fmap, and the theorems      *)
(*   leading to insert_thm and lookup_thm.                                   *)
(* - Lemmas named LBMAPAUX_... are helpers of this file (not HOL4 names).   *)
(* - HOL4 delta and member are balanced_map_delta and balanced_map_member    *)
(*   (short or common words), with the theorems renamed alike (delta_def is  *)
(*   balanced_map_delta_def, ...).                                           *)
(* ========================================================================= *)

needs "hol4/vocab.ml";;
needs "hol4/comparison.ml";;
needs "hol4/finite_map.ml";;

type_invention_error := true;;

let LBMAPAUX_GEN_CONJ th = end_itlist CONJ (map GEN_ALL (CONJUNCTS th));;

(* ------------------------------------------------------------------------- *)
(* Finite maps up to key equivalence.                                        *)
(* ------------------------------------------------------------------------- *)

let key_set_def = new_definition
  `key_set (cmp:A->A->ordering) k = {k' | cmp k k' = EQUAL}`;;

let key_set_equiv = prove
 (`!cmp:A->A->ordering.
     good_cmp cmp
     ==> (!k. k IN key_set cmp k) /\
         (!k1 k2. k1 IN key_set cmp k2 ==> k2 IN key_set cmp k1) /\
         (!k1 k2 k3. k1 IN key_set cmp k2 /\ k2 IN key_set cmp k3
                     ==> k1 IN key_set cmp k3)`,
  REWRITE_TAC[key_set_def; IN_ELIM_THM; good_cmp_def] THEN MESON_TAC[]);;

let key_set_nonempty = prove
 (`!(cmp:A->A->ordering) k. good_cmp cmp ==> ~(key_set cmp k = {})`,
  REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; NOT_FORALL_THM] THEN
  MESON_TAC[key_set_equiv]);;

let key_set_partition = prove
 (`!(cmp:A->A->ordering) k1 k2.
     good_cmp cmp /\ ~(key_set cmp k1 = key_set cmp k2)
     ==> DISJOINT (key_set cmp k1) (key_set cmp k2)`,
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
  MESON_TAC[key_set_equiv]);;

let key_set_eq = prove
 (`!(cmp:A->A->ordering) k1 k2.
     good_cmp cmp ==> (key_set cmp k1 = key_set cmp k2 <=> cmp k1 k2 = EQUAL)`,
  REWRITE_TAC[key_set_def; EXTENSION; IN_ELIM_THM; good_cmp_def] THEN
  MESON_TAC[]);;

let key_set_cmp_def = new_definition
  `key_set_cmp (cmp:A->A->ordering) k ks res <=>
     !k'. k' IN ks ==> cmp k k' = res`;;

let key_set_cmp_thm = prove
 (`!(cmp:A->A->ordering) k k' res.
     good_cmp cmp
     ==> (key_set_cmp cmp k (key_set cmp k') res <=> cmp k k' = res)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[key_set_cmp_def; key_set_def; IN_ELIM_THM] THEN
  REWRITE_TAC[good_cmp_def] THEN STRIP_TAC THEN EQ_TAC THENL
   [DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN X_GEN_TAC `k'':A` THEN DISCH_TAC THEN
  MP_TAC(ISPEC `(cmp:A->A->ordering) k k'` ordering_nchotomy) THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let key_set_cmp2_def = new_definition
  `key_set_cmp2 (cmp:A->A->ordering) ks1 ks2 res <=>
     !k1 k2. k1 IN ks1 /\ k2 IN ks2 ==> cmp k1 k2 = res`;;

let key_set_cmp2_thm = prove
 (`!(cmp:A->A->ordering) k k' res.
     good_cmp cmp
     ==> (key_set_cmp2 cmp (key_set cmp k) (key_set cmp k') res <=>
          cmp k k' = res)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[key_set_cmp2_def; key_set_def; IN_ELIM_THM] THEN
  REWRITE_TAC[good_cmp_def] THEN STRIP_TAC THEN EQ_TAC THENL
   [DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MAP_EVERY X_GEN_TAC [`k1:A`; `k2:A`] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `(cmp:A->A->ordering) k k'` ordering_nchotomy) THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The datatype and the operations.                                          *)
(* ------------------------------------------------------------------------- *)

let balanced_map_INDUCT,balanced_map_RECURSION =
  cake_type "balanced_map = Tip | Bin num K V balanced_map balanced_map";;

let ratio_def = new_definition `ratio = 2:num`;;

let balanced_map_delta_def = new_definition `balanced_map_delta = 3:num`;;

(* HOL4: size_def *)

let balanced_map_size'_def = new_recursive_definition balanced_map_RECURSION (CASE_TERM
  `(balanced_map_size' (Tip:(K,V)balanced_map) = 0) /\
   (balanced_map_size' (Bin s (k:K) (v:V) l r) = s)`);;

let bin_def = new_definition
  `bin (k:K) (x:V) l r =
     Bin (balanced_map_size' l + balanced_map_size' r + 1) k x l r`;;

let null_def = new_recursive_definition balanced_map_RECURSION (CASE_TERM
  `(null (Tip:(K,V)balanced_map) <=> T) /\
   (null (Bin s (k:K) (v:V) m1 m2) <=> F)`);;

let balanced_map_lookup_def = new_recursive_definition balanced_map_RECURSION (CASE_TERM
  `(balanced_map_lookup (cmp:K->K->ordering) k (Tip:(K,V)balanced_map) =
      NONE) /\
   (balanced_map_lookup cmp k (Bin s k' v l r) =
      match cmp k k' with
        LESS -> balanced_map_lookup cmp k l
      | GREATER -> balanced_map_lookup cmp k r
      | EQUAL -> SOME v)`);;

let balanced_map_member_def = new_recursive_definition balanced_map_RECURSION (CASE_TERM
  `(balanced_map_member (cmp:K->K->ordering) k (Tip:(K,V)balanced_map) <=> F) /\
   (balanced_map_member cmp k (Bin s k' v l r) <=>
      match cmp k k' with
        LESS -> balanced_map_member cmp k l
      | GREATER -> balanced_map_member cmp k r
      | EQUAL -> T)`);;

let balanced_map_empty_def = new_definition
  `balanced_map_empty = (Tip:(K,V)balanced_map)`;;

let singleton_def = new_definition
  `singleton (k:K) (x:V) = Bin 1 k x Tip Tip`;;

(* The body of HOL4 balanceL' (just like the Haskell, but without @        *)
(* patterns); balanceL_def below gives HOL4's defining clauses.             *)

let LBMAPAUX_balanceL_DEF = new_definition (CASE_TERM
  `balanceL (k:K) (x:V) (l:(K,V)balanced_map) (r:(K,V)balanced_map) =
     match r with
       Tip ->
         (match l with
            Tip -> Bin 1 k x Tip Tip
          | Bin s1 k1 v1 Tip Tip -> Bin 2 k x l Tip
          | Bin s1 lk lx Tip (Bin s2 lrk lrx t1 t2) ->
              Bin 3 lrk lrx (Bin 1 lk lx Tip Tip) (Bin 1 k x Tip Tip)
          | Bin s1 lk lx (Bin s' k' v' l' r') Tip ->
              Bin 3 lk lx (Bin s' k' v' l' r') (Bin 1 k x Tip Tip)
          | Bin ls lk lx (Bin lls k' v' l' r') (Bin lrs lrk lrx lrl lrr) ->
              if lrs < ratio * lls then
                Bin (1 + ls) lk lx (Bin lls k' v' l' r')
                  (Bin (1 + lrs) k x (Bin lrs lrk lrx lrl lrr) Tip)
              else
                Bin (1 + ls) lrk lrx
                  (Bin (1 + lls + balanced_map_size' lrl) lk lx
                     (Bin lls k' v' l' r') lrl)
                  (Bin (1 + balanced_map_size' lrr) k x lrr Tip))
     | Bin rs k1 v1 t1 t2 ->
         (match l with
            Tip -> Bin (1 + rs) k x Tip r
          | Bin ls lk lx ll lr ->
              if ls > balanced_map_delta * rs then
                (match (ll, lr) with
                   (Bin lls k2 v2 t3 t4, Bin lrs lrk lrx lrl lrr) ->
                     if lrs < ratio * lls then
                       Bin (1 + ls + rs) lk lx ll (Bin (1 + rs + lrs) k x lr r)
                     else
                       Bin (1 + ls + rs) lrk lrx
                         (Bin (1 + lls + balanced_map_size' lrl) lk lx ll lrl)
                         (Bin (1 + rs + balanced_map_size' lrr) k x lrr r)
                 | (t5, t6) -> Tip)
              else Bin (1 + ls + rs) k x l r)`);;

let balanceL_def = LBMAPAUX_GEN_CONJ (prove (CASE_TERM
  `(balanceL (k:K) (x:V) Tip Tip = Bin 1 k x Tip Tip) /\
   (balanceL k x (Bin s' k' v' Tip Tip) Tip =
      Bin 2 k x (Bin s' k' v' Tip Tip) Tip) /\
   (balanceL k x (Bin s1 lk lx Tip (Bin s2 lrk lrx l2 r2)) Tip =
      Bin 3 lrk lrx (Bin 1 lk lx Tip Tip) (Bin 1 k x Tip Tip)) /\
   (balanceL k x (Bin s1 lk lx (Bin s' k' v' l' r') Tip) Tip =
      Bin 3 lk lx (Bin s' k' v' l' r') (Bin 1 k x Tip Tip)) /\
   (balanceL k x (Bin ls lk lx (Bin lls k' v' l' r') (Bin lrs lrk lrx lrl lrr))
      Tip =
      if lrs < ratio * lls then
        Bin (1 + ls) lk lx (Bin lls k' v' l' r')
          (Bin (1 + lrs) k x (Bin lrs lrk lrx lrl lrr) Tip)
      else
        Bin (1 + ls) lrk lrx
          (Bin (1 + lls + balanced_map_size' lrl) lk lx (Bin lls k' v' l' r') lrl)
          (Bin (1 + balanced_map_size' lrr) k x lrr Tip)) /\
   (balanceL k x Tip (Bin rs k' v' l' r') =
      Bin (1 + rs) k x Tip (Bin rs k' v' l' r')) /\
   (balanceL k x (Bin ls lk lx ll lr) (Bin rs k' v' l' r') =
      if ls > balanced_map_delta * rs then
        match (ll, lr) with
          (Bin lls k2 v2 l2 r2, Bin lrs lrk lrx lrl lrr) ->
            if lrs < ratio * lls then
              Bin (1 + ls + rs) lk lx ll
                (Bin (1 + rs + lrs) k x lr (Bin rs k' v' l' r'))
            else
              Bin (1 + ls + rs) lrk lrx
                (Bin (1 + lls + balanced_map_size' lrl) lk lx ll lrl)
                (Bin (1 + rs + balanced_map_size' lrr) k x lrr
                   (Bin rs k' v' l' r'))
        | (t1, t2) -> Tip
      else
        Bin (1 + ls + rs) k x (Bin ls lk lx ll lr) (Bin rs k' v' l' r'))`,
  REWRITE_TAC[LBMAPAUX_balanceL_DEF; case_def "balanced_map"]));;

(* The body of HOL4 balanceR'; balanceR_def below gives HOL4's clauses.     *)

let LBMAPAUX_balanceR_DEF = new_definition (CASE_TERM
  `balanceR (k:K) (x:V) (l:(K,V)balanced_map) (r:(K,V)balanced_map) =
     match l with
       Tip ->
         (match r with
            Tip -> Bin 1 k x Tip Tip
          | Bin s1 k1 v1 Tip Tip -> Bin 2 k x Tip r
          | Bin s1 rk rx Tip (Bin s' k' v' l' r') ->
              Bin 3 rk rx (Bin 1 k x Tip Tip) (Bin s' k' v' l' r')
          | Bin s1 rk rx (Bin s2 rlk rlx t1 t2) Tip ->
              Bin 3 rlk rlx (Bin 1 k x Tip Tip) (Bin 1 rk rx Tip Tip)
          | Bin rs rk rx (Bin rls rlk rlx rll rlr) (Bin rrs k' v' l' r') ->
              if rls < ratio * rrs then
                Bin (1 + rs) rk rx (Bin (1 + rls) k x Tip (Bin rls rlk rlx rll rlr))
                  (Bin rrs k' v' l' r')
              else
                Bin (1 + rs) rlk rlx (Bin (1 + balanced_map_size' rll) k x Tip rll)
                  (Bin (1 + rrs + balanced_map_size' rlr) rk rx rlr
                     (Bin rrs k' v' l' r')))
     | Bin ls k1 v1 t1 t2 ->
         (match r with
            Tip -> Bin (1 + ls) k x l Tip
          | Bin rs rk rx rl rr ->
              if rs > balanced_map_delta * ls then
                (match (rl, rr) with
                   (Bin rls rlk rlx rll rlr, Bin rrs k2 v2 t3 t4) ->
                     if rls < ratio * rrs then
                       Bin (1 + ls + rs) rk rx (Bin (1 + ls + rls) k x l rl) rr
                     else
                       Bin (1 + ls + rs) rlk rlx
                         (Bin (1 + ls + balanced_map_size' rll) k x l rll)
                         (Bin (1 + rrs + balanced_map_size' rlr) rk rx rlr rr)
                 | (t5, t6) -> Tip)
              else Bin (1 + ls + rs) k x l r)`);;

let balanceR_def = LBMAPAUX_GEN_CONJ (prove (CASE_TERM
  `(balanceR (k:K) (x:V) Tip Tip = Bin 1 k x Tip Tip) /\
   (balanceR k x Tip (Bin s' k' v' Tip Tip) =
      Bin 2 k x Tip (Bin s' k' v' Tip Tip)) /\
   (balanceR k x Tip (Bin s1 rk rx Tip (Bin s' k' v' l' r')) =
      Bin 3 rk rx (Bin 1 k x Tip Tip) (Bin s' k' v' l' r')) /\
   (balanceR k x Tip (Bin s1 rk rx (Bin s2 rlk rlx l2 r2) Tip) =
      Bin 3 rlk rlx (Bin 1 k x Tip Tip) (Bin 1 rk rx Tip Tip)) /\
   (balanceR k x Tip (Bin rs rk rx (Bin rls rlk rlx rll rlr) (Bin rrs k' v' l' r')) =
      if rls < ratio * rrs then
        Bin (1 + rs) rk rx (Bin (1 + rls) k x Tip (Bin rls rlk rlx rll rlr))
          (Bin rrs k' v' l' r')
      else
        Bin (1 + rs) rlk rlx (Bin (1 + balanced_map_size' rll) k x Tip rll)
          (Bin (1 + rrs + balanced_map_size' rlr) rk rx rlr (Bin rrs k' v' l' r'))) /\
   (balanceR k x (Bin ls k' v' l' r') Tip =
      Bin (1 + ls) k x (Bin ls k' v' l' r') Tip) /\
   (balanceR k x (Bin ls k' v' l' r') (Bin rs rk rx rl rr) =
      if rs > balanced_map_delta * ls then
        match (rl, rr) with
          (Bin rls rlk rlx rll rlr, Bin rrs k2 v2 l2 r2) ->
            if rls < ratio * rrs then
              Bin (1 + ls + rs) rk rx (Bin (1 + ls + rls) k x (Bin ls k' v' l' r') rl) rr
            else
              Bin (1 + ls + rs) rlk rlx
                (Bin (1 + ls + balanced_map_size' rll) k x (Bin ls k' v' l' r') rll)
                (Bin (1 + rrs + balanced_map_size' rlr) rk rx rlr rr)
        | (t1, t2) -> Tip
      else
        Bin (1 + ls + rs) k x (Bin ls k' v' l' r') (Bin rs rk rx rl rr))`,
  REWRITE_TAC[LBMAPAUX_balanceR_DEF; case_def "balanced_map"]));;

(* HOL4: insert_def *)

let balanced_map_insert_def = new_recursive_definition balanced_map_RECURSION (CASE_TERM
  `(balanced_map_insert (cmp:K->K->ordering) k (v:V) Tip = singleton k v) /\
   (balanced_map_insert cmp k v (Bin s k' v' l r) =
      match cmp k k' with
        LESS -> balanceL k' v' (balanced_map_insert cmp k v l) r
      | GREATER -> balanceR k' v' l (balanced_map_insert cmp k v r)
      | EQUAL -> Bin s k v l r)`);;

(* ------------------------------------------------------------------------- *)
(* The abstraction to finite maps and the invariant.                         *)
(* ------------------------------------------------------------------------- *)

let to_fmap_def = new_recursive_definition balanced_map_RECURSION (CASE_TERM
  `(to_fmap (cmp:K->K->ordering) (Tip:(K,V)balanced_map) = FEMPTY) /\
   (to_fmap cmp (Bin s k v l r) =
      FUNION (to_fmap cmp l) (to_fmap cmp r) |+ (key_set cmp k,v))`);;

let balanced_def = new_definition
  `balanced l r <=> l + r <= 1 \/ MAX l r <= balanced_map_delta * MIN l r`;;

let structure_size_def = new_recursive_definition balanced_map_RECURSION (CASE_TERM
  `(structure_size (Tip:(K,V)balanced_map) = 0) /\
   (structure_size (Bin n (k:K) (v:V) l r) =
      1 + structure_size l + structure_size r)`);;

let key_ordered_def = new_recursive_definition balanced_map_RECURSION (CASE_TERM
  `(key_ordered (cmp:K->K->ordering) k (Tip:(K,V)balanced_map) res <=> T) /\
   (key_ordered cmp k (Bin n k' v l r) res <=>
      cmp k k' = res /\ key_ordered cmp k l res /\ key_ordered cmp k r res)`);;

(* HOL4: invariant_def *)

let balanced_map_invariant_def = new_recursive_definition balanced_map_RECURSION (CASE_TERM
  `(balanced_map_invariant (cmp:K->K->ordering) (Tip:(K,V)balanced_map) <=> T) /\
   (balanced_map_invariant cmp (Bin s k v l r) <=>
      s = 1 + structure_size l + structure_size r /\
      key_ordered cmp k l GREATER /\
      key_ordered cmp k r LESS /\
      balanced (balanced_map_size' l) (balanced_map_size' r) /\
      balanced_map_invariant cmp l /\
      balanced_map_invariant cmp r)`);;

(* ------------------------------------------------------------------------- *)
(* Properties of to_fmap and the invariant.                                   *)
(* ------------------------------------------------------------------------- *)

let LBMAPAUX_good_cmp = prove
 (`!cmp:A->A->ordering.
     good_cmp cmp
     ==> (!x. cmp x x = EQUAL) /\
         (!x y. cmp x y = EQUAL <=> cmp y x = EQUAL) /\
         (!x y. cmp x y = GREATER <=> cmp y x = LESS) /\
         (!x y. cmp x y = LESS <=> cmp y x = GREATER) /\
         (!x y z. cmp x y = EQUAL /\ cmp y z = LESS ==> cmp x z = LESS) /\
         (!x y z. cmp x y = LESS /\ cmp y z = EQUAL ==> cmp x z = LESS) /\
         (!x y z. cmp x y = EQUAL /\ cmp y z = EQUAL ==> cmp x z = EQUAL) /\
         (!x y z. cmp x y = LESS /\ cmp y z = LESS ==> cmp x z = LESS) /\
         (!x y z. cmp x y = EQUAL /\ cmp y z = GREATER ==> cmp x z = GREATER) /\
         (!x y z. cmp x y = GREATER /\ cmp y z = EQUAL ==> cmp x z = GREATER) /\
         (!x y z. cmp x y = GREATER /\ cmp y z = GREATER ==> cmp x z = GREATER)`,
  GEN_TAC THEN REWRITE_TAC[good_cmp_def] THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(a /\ b /\ c) /\ (a /\ b /\ c ==> d) ==> a /\ b /\ c /\ d`) THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let to_fmap_key_set = prove
 (`!(cmp:K->K->ordering) ks (t:(K,V)balanced_map).
     ks IN FDOM (to_fmap cmp t) ==> ?k. ks = key_set cmp k`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC balanced_map_INDUCT THEN
  REWRITE_TAC[to_fmap_def; FDOM_FEMPTY; NOT_IN_EMPTY; FDOM_FUPDATE;
              FDOM_FUNION; IN_INSERT; IN_UNION] THEN
  MESON_TAC[]);;

let key_ordered_to_fmap = prove
 (`!(cmp:K->K->ordering) k (t:(K,V)balanced_map) res.
     good_cmp cmp
     ==> (key_ordered cmp k t res <=>
          !ks. ks IN FDOM (to_fmap cmp t) ==> key_set_cmp cmp k ks res)`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC balanced_map_INDUCT THEN
  REWRITE_TAC[key_ordered_def; to_fmap_def; FDOM_FEMPTY; NOT_IN_EMPTY;
              FDOM_FUPDATE; FDOM_FUNION; FORALL_IN_INSERT; FORALL_IN_UNION] THEN
  SIMP_TAC[key_set_cmp_thm] THEN MESON_TAC[]);;

let LBMAPAUX_key_ordered_FDOM = prove
 (`!(cmp:K->K->ordering) k k' (t:(K,V)balanced_map) res.
     good_cmp cmp /\ key_ordered cmp k t res /\
     key_set cmp k' IN FDOM (to_fmap cmp t)
     ==> cmp k k' = res`,
  MESON_TAC[key_ordered_to_fmap; key_set_cmp_thm]);;

let invariant_eq = prove
 (`(!cmp:K->K->ordering.
      balanced_map_invariant cmp (Tip:(K,V)balanced_map) <=> T) /\
   (!(cmp:K->K->ordering) s k (v:V) l r.
      balanced_map_invariant cmp (Bin s k v l r) <=>
      (good_cmp cmp
       ==> DISJOINT (FDOM (to_fmap cmp l)) (FDOM (to_fmap cmp r))) /\
      (good_cmp cmp ==> ~(key_set cmp k IN FDOM (to_fmap cmp l))) /\
      (good_cmp cmp ==> ~(key_set cmp k IN FDOM (to_fmap cmp r))) /\
      s = 1 + structure_size l + structure_size r /\
      key_ordered cmp k l GREATER /\
      key_ordered cmp k r LESS /\
      balanced (balanced_map_size' l) (balanced_map_size' r) /\
      balanced_map_invariant cmp l /\
      balanced_map_invariant cmp r)`,
  REWRITE_TAC[balanced_map_invariant_def] THEN REPEAT GEN_TAC THEN
  ASM_CASES_TAC `good_cmp (cmp:K->K->ordering)` THEN ASM_REWRITE_TAC[] THEN
  EQ_TAC THEN SIMP_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [good_cmp_def]) THEN
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `ks:K->bool` THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP to_fmap_key_set) THEN
    DISCH_THEN(X_CHOOSE_THEN `k0:K` SUBST_ALL_TAC) THEN
    MP_TAC(ISPECL [`cmp:K->K->ordering`; `k:K`; `k0:K`; `l:(K,V)balanced_map`;
                   `GREATER`] LBMAPAUX_key_ordered_FDOM) THEN
    MP_TAC(ISPECL [`cmp:K->K->ordering`; `k:K`; `k0:K`; `r:(K,V)balanced_map`;
                   `LESS`] LBMAPAUX_key_ordered_FDOM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[ordering_eq_dec];
    DISCH_TAC THEN
    MP_TAC(ISPECL [`cmp:K->K->ordering`; `k:K`; `k:K`; `l:(K,V)balanced_map`;
                   `GREATER`] LBMAPAUX_key_ordered_FDOM) THEN
    ASM_REWRITE_TAC[ordering_eq_dec];
    DISCH_TAC THEN
    MP_TAC(ISPECL [`cmp:K->K->ordering`; `k:K`; `k:K`; `r:(K,V)balanced_map`;
                   `LESS`] LBMAPAUX_key_ordered_FDOM) THEN
    ASM_REWRITE_TAC[ordering_eq_dec]]);;

let inv_props = prove
 (`!(cmp:K->K->ordering) s k (v:V) l r.
     good_cmp cmp /\ balanced_map_invariant cmp (Bin s k v l r)
     ==> DISJOINT (FDOM (to_fmap cmp l)) (FDOM (to_fmap cmp r)) /\
         (!x. key_set cmp x IN FDOM (to_fmap cmp l) ==> cmp k x = GREATER) /\
         (!x. key_set cmp x IN FDOM (to_fmap cmp r) ==> cmp k x = LESS)`,
  REWRITE_TAC[invariant_eq] THEN MESON_TAC[LBMAPAUX_key_ordered_FDOM]);;

let structure_size_thm = prove
 (`!(cmp:K->K->ordering) (t:(K,V)balanced_map).
     balanced_map_invariant cmp t
     ==> balanced_map_size' t = structure_size t`,
  GEN_TAC THEN MATCH_MP_TAC balanced_map_INDUCT THEN
  SIMP_TAC[balanced_map_invariant_def; balanced_map_size'_def;
           structure_size_def]);;

let LBMAPAUX_FCARD_DISJOINT_UNION = prove
 (`!m1 m2:(A,B)fmap.
     DISJOINT (FDOM m1) (FDOM m2) \/ DISJOINT (FDOM m2) (FDOM m1)
     ==> FCARD (FUNION m1 m2) = FCARD m1 + FCARD m2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[DISJOINT; FCARD_DEF; FDOM_FUNION] THEN
  REWRITE_TAC[INTER_COMM] THEN DISCH_TAC THEN MATCH_MP_TAC CARD_UNION THEN
  ASM_REWRITE_TAC[FDOM_FINITE]);;

let structure_size_to_fmap = prove
 (`!(cmp:K->K->ordering) (t:(K,V)balanced_map).
     good_cmp cmp /\ balanced_map_invariant cmp t
     ==> FCARD (to_fmap cmp t) = structure_size t`,
  GEN_TAC THEN MATCH_MP_TAC balanced_map_INDUCT THEN
  REWRITE_TAC[to_fmap_def; structure_size_def; FCARD_FEMPTY] THEN
  MAP_EVERY X_GEN_TAC [`s:num`; `k:K`; `v:V`; `l:(K,V)balanced_map`;
                       `r:(K,V)balanced_map`] THEN
  REWRITE_TAC[invariant_eq] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[FCARD_FUPDATE; FDOM_FUNION; IN_UNION;
               LBMAPAUX_FCARD_DISJOINT_UNION] THEN
  ARITH_TAC);;

let size_thm = prove
 (`!(cmp:K->K->ordering) (t:(K,V)balanced_map).
     good_cmp cmp /\ balanced_map_invariant cmp t
     ==> balanced_map_size' t = FCARD (to_fmap cmp t)`,
  MESON_TAC[structure_size_thm; structure_size_to_fmap]);;

let null_thm = prove
 (`!(cmp:K->K->ordering) (t:(K,V)balanced_map).
     null t <=> to_fmap cmp t = FEMPTY`,
  GEN_TAC THEN MATCH_MP_TAC balanced_map_INDUCT THEN
  REWRITE_TAC[null_def; to_fmap_def; NOT_EQ_FEMPTY_FUPDATE]);;

let LBMAPAUX_cmp_cases = prove
 (`!(cmp:A->A->ordering) x y.
     good_cmp cmp
     ==> (cmp x y = LESS /\ cmp y x = GREATER) \/
         (cmp x y = EQUAL /\ cmp y x = EQUAL) \/
         (cmp x y = GREATER /\ cmp y x = LESS)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPEC `(cmp:A->A->ordering) x y` ordering_nchotomy) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[ordering_eq_dec] THEN
  ASM_MESON_TAC[LBMAPAUX_good_cmp]);;

let lookup_thm = prove
 (`!(cmp:K->K->ordering) k (t:(K,V)balanced_map).
     good_cmp cmp /\ balanced_map_invariant cmp t
     ==> balanced_map_lookup cmp k t = FLOOKUP (to_fmap cmp t) (key_set cmp k)`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC balanced_map_INDUCT THEN
  REWRITE_TAC[balanced_map_lookup_def; to_fmap_def; FLOOKUP_EMPTY] THEN
  MAP_EVERY X_GEN_TAC [`s:num`; `k':K`; `v:V`; `l:(K,V)balanced_map`;
                       `r:(K,V)balanced_map`] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`cmp:K->K->ordering`; `s:num`; `k':K`; `v:V`;
                 `l:(K,V)balanced_map`; `r:(K,V)balanced_map`] inv_props) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (MP_TAC o SPEC `k:K`) (MP_TAC o SPEC `k:K`))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[balanced_map_invariant_def]) THEN
  ASM_SIMP_TAC[FLOOKUP_UPDATE; FLOOKUP_FUNION; key_set_eq; FDOM_FLOOKUP] THEN
  MP_TAC(ISPECL [`cmp:K->K->ordering`; `k:K`; `k':K`] LBMAPAUX_cmp_cases) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[ordering_case_def; ordering_eq_dec] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  STRUCT_CASES_TAC(ISPEC `FLOOKUP (to_fmap cmp (l:(K,V)balanced_map)) (key_set cmp k)`
                     (cases "option")) THEN
  ASM_REWRITE_TAC[option_CASE]);;

let member_eq_lookup = prove
 (`!(cmp:K->K->ordering) k (t:(K,V)balanced_map).
     balanced_map_member cmp k t <=> IS_SOME (balanced_map_lookup cmp k t)`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC balanced_map_INDUCT THEN
  REWRITE_TAC[balanced_map_member_def; balanced_map_lookup_def; IS_SOME_DEF] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `(cmp:K->K->ordering) k a1` ordering_nchotomy) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[ordering_case_def; IS_SOME_DEF]);;

let member_thm = prove
 (`!(cmp:K->K->ordering) k (t:(K,V)balanced_map).
     good_cmp cmp /\ balanced_map_invariant cmp t
     ==> (balanced_map_member cmp k t <=> key_set cmp k IN FDOM (to_fmap cmp t))`,
  SIMP_TAC[member_eq_lookup; lookup_thm; FDOM_FLOOKUP] THEN
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `FLOOKUP (to_fmap cmp (t:(K,V)balanced_map)) (key_set cmp k)`
                     (cases "option")) THEN
  REWRITE_TAC[IS_SOME_DEF; option_DISTINCT]);;

let empty_thm = prove
 (`!cmp:K->K->ordering.
     balanced_map_invariant cmp (balanced_map_empty:(K,V)balanced_map) /\
     to_fmap cmp (balanced_map_empty:(K,V)balanced_map) = FEMPTY`,
  REWRITE_TAC[balanced_map_invariant_def; balanced_map_empty_def; to_fmap_def]);;

let singleton_thm = prove
 (`!(cmp:K->K->ordering) k (v:V).
     balanced_map_invariant cmp (singleton k v) /\
     to_fmap cmp (singleton k v) = FEMPTY |+ (key_set cmp k,v)`,
  REWRITE_TAC[balanced_def; balanced_map_invariant_def; singleton_def; to_fmap_def;
              balanced_map_size'_def; structure_size_def; key_ordered_def;
              FUNION_FEMPTY_1] THEN
  ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The balance routine from the comments in the Haskell file.               *)
(* ------------------------------------------------------------------------- *)

let singleL_def = cake_def
  `singleL (k1:K) (x1:V) t1 (Bin s k2 x2 t2 t3) =
     bin k2 x2 (bin k1 x1 t1 t2) t3`;;

let singleR_def = cake_def
  `singleR (k1:K) (x1:V) (Bin s k2 x2 t1 t2) t3 =
     bin k2 x2 t1 (bin k1 x1 t2 t3)`;;

let doubleL_def = cake_def
  `doubleL (k1:K) (x1:V) t1 (Bin s k2 x2 (Bin s' k3 x3 t2 t3) t4) =
     bin k3 x3 (bin k1 x1 t1 t2) (bin k2 x2 t3 t4)`;;

let doubleR_def = cake_def
  `doubleR (k1:K) (x1:V) (Bin s k2 x2 t1 (Bin s' k3 x3 t2 t3)) t4 =
     bin k3 x3 (bin k2 x2 t1 t2) (bin k1 x1 t3 t4)`;;

let rotateL_def = cake_def
  `(rotateL (k:K) (x:V) l (Bin s' k' x' ly ry) =
      if balanced_map_size' ly < ratio * balanced_map_size' ry then
        singleL k x l (Bin s' k' x' ly ry)
      else
        doubleL k x l (Bin s' k' x' ly ry)) /\
   (rotateL k x l Tip = doubleL k x l Tip)`;;

let rotateR_def = cake_def
  `(rotateR (k:K) (x:V) (Bin s' k' x' ly ry) r =
      if balanced_map_size' ry < ratio * balanced_map_size' ly then
        singleR k x (Bin s' k' x' ly ry) r
      else
        doubleR k x (Bin s' k' x' ly ry) r) /\
   (rotateR k x Tip r = doubleR k x Tip r)`;;

let balL_def = new_definition
  `balL (k:K) (x:V) l r =
     if balanced_map_size' l + balanced_map_size' r <= 1 then
       Bin (balanced_map_size' l + balanced_map_size' r + 1) k x l r
     else if balanced_map_size' l > balanced_map_delta * balanced_map_size' r then
       rotateR k x l r
     else
       Bin (balanced_map_size' l + balanced_map_size' r + 1) k x l r`;;

let balR_def = new_definition
  `balR (k:K) (x:V) l r =
     if balanced_map_size' l + balanced_map_size' r <= 1 then
       Bin (balanced_map_size' l + balanced_map_size' r + 1) k x l r
     else if balanced_map_size' r > balanced_map_delta * balanced_map_size' l then
       rotateL k x l r
     else
       Bin (balanced_map_size' l + balanced_map_size' r + 1) k x l r`;;

let almost_balancedL_def = new_definition
  `almost_balancedL l r <=>
     if l + r <= 1 \/ l <= balanced_map_delta * r then balanced l r
     else if r = 0 then l < 5
     else if r = 1 then l < 8
     else 2 * l < (2 * balanced_map_delta + 3) * r + 2`;;

let almost_balancedR_def = new_definition
  `almost_balancedR l r <=>
     if l + r <= 1 \/ r <= balanced_map_delta * l then balanced l r
     else if l = 0 then r < 5
     else if l = 1 then r < 8
     else 2 * r < (2 * balanced_map_delta + 3) * l + 2`;;

let LBMAPAUX_balanced_alt = prove
 (`!l r. balanced l r <=> l + r <= 1 \/ l <= 3 * r /\ r <= 3 * l`,
  REWRITE_TAC[balanced_def; balanced_map_delta_def; MAX; MIN] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_ARITH_TAC);;

let LBMAPAUX_BAL_TAC =
  REWRITE_TAC[LBMAPAUX_balanced_alt; almost_balancedL_def; almost_balancedR_def;
              balanced_map_delta_def; ratio_def; GT; COND_EXPAND] THEN
  ARITH_TAC;;

let balanced_lem1 = prove
 (`!l r. l + r <= 1 ==> balanced l r`,
  LBMAPAUX_BAL_TAC);;

let balanced_lem2 = prove
 (`!l r. ~(l > balanced_map_delta * r) /\ almost_balancedL l r /\ ~(l + r <= 1)
         ==> balanced l r`,
  LBMAPAUX_BAL_TAC);;

let balanced_lem3 = prove
 (`!b b0 r.
     almost_balancedL (b + b0 + 1) r /\ b + b0 + 1 > balanced_map_delta * r /\
     b0 < ratio * b /\ balanced b b0
     ==> balanced b (b0 + r + 1) /\ balanced b0 r`,
  LBMAPAUX_BAL_TAC);;

let balanced_lem4 = prove
 (`!b b' b0' r.
     almost_balancedL (b + b' + b0' + 2) r /\ b + b' + b0' + 2 > balanced_map_delta * r /\
     ~(b' + b0' + 1 < ratio * b) /\ balanced b (b' + b0' + 1) /\
     balanced b' b0'
     ==> balanced (b + b' + 1) (b0' + r + 1) /\ balanced b b' /\
         balanced b0' r`,
  LBMAPAUX_BAL_TAC);;

let balanced_lem5 = prove
 (`!l r. ~(r > balanced_map_delta * l) /\ almost_balancedR l r ==> balanced l r`,
  LBMAPAUX_BAL_TAC);;

let balanced_lem6 = prove
 (`!b b0 l.
     almost_balancedR l (b + b0 + 1) /\ b + b0 + 1 > balanced_map_delta * l /\
     b < ratio * b0 /\ balanced b b0
     ==> balanced (b + l + 1) b0 /\ balanced l b`,
  LBMAPAUX_BAL_TAC);;

let balanced_lem7 = prove
 (`!(b:num) (b0:num) (b0':num) (l:num) (b':num).
     almost_balancedR l (b' + b0 + b0' + 2) /\ b' + b0 + b0' + 2 > balanced_map_delta * l /\
     ~(b' + b0' + 1 < ratio * b0) /\ balanced (b' + b0' + 1) b0 /\
     balanced b' b0'
     ==> balanced (b' + l + 1) (b0 + b0' + 1) /\ balanced l b' /\
         balanced b0' b0`,
  LBMAPAUX_BAL_TAC);;

let almost_balancedL_thm = prove
 (`!l r. balanced l r
         ==> almost_balancedL l r /\ almost_balancedL (l + 1) r /\
             almost_balancedL l (r - 1)`,
  LBMAPAUX_BAL_TAC);;

let almost_balancedR_thm = prove
 (`!l r. balanced l r
         ==> almost_balancedR l r /\ almost_balancedR l (r + 1) /\
             almost_balancedR (l - 1) r`,
  LBMAPAUX_BAL_TAC);;

(* ------------------------------------------------------------------------- *)
(* Rotations and balancing preserve the invariant and the finite map.         *)
(* ------------------------------------------------------------------------- *)

let LBMAPAUX_cmp_trans = prove
 (`!(cmp:A->A->ordering) x y z res.
     good_cmp cmp /\ cmp x y = res /\ cmp y z = res ==> cmp x z = res`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `res:ordering` ordering_nchotomy) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[LBMAPAUX_good_cmp]);;

let LBMAPAUX_key_ordered_trans = prove
 (`!(cmp:K->K->ordering) k1 k2 (t:(K,V)balanced_map) res.
     good_cmp cmp /\ cmp k1 k2 = res /\ key_ordered cmp k2 t res
     ==> key_ordered cmp k1 t res`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC balanced_map_INDUCT THEN
  REWRITE_TAC[key_ordered_def] THEN MESON_TAC[LBMAPAUX_cmp_trans]);;

let LBMAPAUX_ko_NONE = prove
 (`!(cmp:K->K->ordering) a (t:(K,V)balanced_map) res c.
     good_cmp cmp /\ key_ordered cmp a t res /\ ~(cmp a c = res)
     ==> FLOOKUP (to_fmap cmp t) (key_set cmp c) = NONE`,
  REWRITE_TAC[flookup_thm] THEN MESON_TAC[LBMAPAUX_key_ordered_FDOM]);;

let LBMAPAUX_FMAP_TAC (keys:term list) (neqs:thm list) (ths:thm list) : tactic =
  let rws = option_CASE :: neqs @ map GSYM neqs @ ths in
  let is_split t =
    let h,args = strip_comb t in
    is_const h && fst(dest_const h) = "option_CASE" && length args = 3 &&
    (let h',_ = strip_comb (hd args) in
     is_const h' && fst(dest_const h') = "FLOOKUP") in
  let fin =
    ASM_REWRITE_TAC rws THEN
    REPEAT(W(fun (_,w) ->
      let t = find_term is_split w in
      let sc = hd(snd(strip_comb t)) in
      STRUCT_CASES_TAC(ISPEC sc (cases "option")) THEN
      ASM_REWRITE_TAC rws)) in
  let rec keys_tac ks =
    match ks with
      [] -> fin
    | ky::rest ->
        ASM_CASES_TAC (mk_eq(ky,`x:K->bool`)) THENL
         [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN fin; keys_tac rest] in
  REWRITE_TAC[fmap_eq_flookup; FLOOKUP_UPDATE; FLOOKUP_FUNION] THEN
  X_GEN_TAC `x:K->bool` THEN keys_tac keys;;

let LBMAPAUX_SS_TAC (ts:term list) : tactic =
  MAP_EVERY (fun t ->
    let itm = mk_comb(mk_comb(`balanced_map_invariant:(K->K->ordering)->(K,V)balanced_map->bool`,
                              `cmp:K->K->ordering`), t) in
    MP_TAC(MATCH_MP structure_size_thm (ASSUME itm)) THEN
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) THEN
                         REWRITE_TAC[GSYM th])) ts;;

let singleR_thm = prove
 (`!k (v:V) r (cmp:K->K->ordering) n k' v' b b0.
     good_cmp cmp /\
     key_ordered cmp k (Bin n k' v' b b0) GREATER /\
     key_ordered cmp k r LESS /\
     almost_balancedL n (balanced_map_size' r) /\
     ~(balanced_map_size' r + n <= 1) /\
     n > balanced_map_delta * balanced_map_size' r /\
     balanced_map_size' b0 < ratio * balanced_map_size' b /\
     balanced_map_invariant cmp (Bin n k' v' b b0) /\
     balanced_map_invariant cmp r
     ==> balanced_map_invariant cmp (singleR k v (Bin n k' v' b b0) r) /\
         to_fmap cmp (singleR k v (Bin n k' v' b b0) r) =
         FUNION (to_fmap cmp (Bin n k' v' b b0)) (to_fmap cmp r) |+
         (key_set cmp k,v)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[key_ordered_def; balanced_map_invariant_def] THEN
  STRIP_TAC THEN
  REWRITE_TAC[singleR_def; bin_def; balanced_map_invariant_def; key_ordered_def;
              balanced_map_size'_def; structure_size_def; to_fmap_def] THEN
  LBMAPAUX_SS_TAC [`b:(K,V)balanced_map`; `b0:(K,V)balanced_map`;
                   `r:(K,V)balanced_map`] THEN
  SUBGOAL_THEN `n = balanced_map_size' (b:(K,V)balanced_map) +
                    balanced_map_size' (b0:(K,V)balanced_map) + 1`
    SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(cmp:K->K->ordering) k' k = LESS` ASSUME_TAC THENL
   [ASM_MESON_TAC[LBMAPAUX_good_cmp]; ALL_TAC] THEN
  MP_TAC(ISPECL [`balanced_map_size' (b:(K,V)balanced_map)`;
                 `balanced_map_size' (b0:(K,V)balanced_map)`;
                 `balanced_map_size' (r:(K,V)balanced_map)`] balanced_lem3) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    ASM_MESON_TAC[LBMAPAUX_key_ordered_trans];
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(key_set (cmp:K->K->ordering) k = key_set cmp k')` ASSUME_TAC THENL
   [ASM_SIMP_TAC[key_set_eq; ordering_eq_dec]; ALL_TAC] THEN
  SUBGOAL_THEN `FLOOKUP (to_fmap (cmp:K->K->ordering) (b:(K,V)balanced_map))
                  (key_set cmp k) = NONE` ASSUME_TAC THENL
   [MATCH_MP_TAC LBMAPAUX_ko_NONE THEN
    MAP_EVERY EXISTS_TAC [`k:K`; `GREATER`] THEN
    ASM_MESON_TAC[LBMAPAUX_good_cmp; ordering_eq_dec]; ALL_TAC] THEN
  LBMAPAUX_FMAP_TAC [`key_set (cmp:K->K->ordering) k'`;
                     `key_set (cmp:K->K->ordering) k`]
    [ASSUME `~(key_set (cmp:K->K->ordering) k = key_set cmp k')`] []);;

let doubleR_thm = prove
 (`!k (v:V) r (cmp:K->K->ordering) n k' v' b b0.
     good_cmp cmp /\
     key_ordered cmp k (Bin n k' v' b b0) GREATER /\
     key_ordered cmp k r LESS /\
     almost_balancedL n (balanced_map_size' r) /\
     ~(balanced_map_size' r + n <= 1) /\
     n > balanced_map_delta * balanced_map_size' r /\
     ~(balanced_map_size' b0 < ratio * balanced_map_size' b) /\
     balanced_map_invariant cmp (Bin n k' v' b b0) /\
     balanced_map_invariant cmp r
     ==> balanced_map_invariant cmp (doubleR k v (Bin n k' v' b b0) r) /\
         to_fmap cmp (doubleR k v (Bin n k' v' b b0) r) =
         FUNION (to_fmap cmp (Bin n k' v' b b0)) (to_fmap cmp r) |+
         (key_set cmp k,v)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `b0:(K,V)balanced_map` (cases "balanced_map")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC
    (X_CHOOSE_THEN `s3:num` (X_CHOOSE_THEN `k3:K` (X_CHOOSE_THEN `v3:V`
      (X_CHOOSE_THEN `b1:(K,V)balanced_map`
        (X_CHOOSE_THEN `b2:(K,V)balanced_map` SUBST1_TAC)))))) THENL
   [REWRITE_TAC[key_ordered_def; balanced_map_invariant_def;
                balanced_map_size'_def; structure_size_def] THEN
    STRIP_TAC THEN LBMAPAUX_SS_TAC [`b:(K,V)balanced_map`; `r:(K,V)balanced_map`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ratio_def; balanced_map_delta_def]) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[key_ordered_def; balanced_map_invariant_def;
              balanced_map_size'_def; structure_size_def] THEN
  STRIP_TAC THEN
  REWRITE_TAC[doubleR_def; bin_def; balanced_map_invariant_def; key_ordered_def;
              balanced_map_size'_def; structure_size_def; to_fmap_def] THEN
  LBMAPAUX_SS_TAC [`b:(K,V)balanced_map`; `b1:(K,V)balanced_map`;
                   `b2:(K,V)balanced_map`; `r:(K,V)balanced_map`] THEN
  SUBGOAL_THEN `n = balanced_map_size' (b:(K,V)balanced_map) +
                    balanced_map_size' (b1:(K,V)balanced_map) +
                    balanced_map_size' (b2:(K,V)balanced_map) + 2`
    SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `s3 = balanced_map_size' (b1:(K,V)balanced_map) +
                     balanced_map_size' (b2:(K,V)balanced_map) + 1`
    SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(cmp:K->K->ordering) k3 k' = GREATER /\ cmp k3 k = LESS /\
                cmp k' k = LESS` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[LBMAPAUX_good_cmp]; ALL_TAC] THEN
  MP_TAC(ISPECL [`balanced_map_size' (b:(K,V)balanced_map)`;
                 `balanced_map_size' (b1:(K,V)balanced_map)`;
                 `balanced_map_size' (b2:(K,V)balanced_map)`;
                 `balanced_map_size' (r:(K,V)balanced_map)`] balanced_lem4) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    ASM_MESON_TAC[LBMAPAUX_key_ordered_trans];
    ASM_MESON_TAC[LBMAPAUX_key_ordered_trans];
    ARITH_TAC;
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(key_set (cmp:K->K->ordering) k = key_set cmp k') /\
                ~(key_set cmp k = key_set cmp k3) /\
                ~(key_set cmp k' = key_set cmp k3)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[key_set_eq] THEN ASM_MESON_TAC[LBMAPAUX_good_cmp; ordering_eq_dec];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `FLOOKUP (to_fmap (cmp:K->K->ordering) (b:(K,V)balanced_map)) (key_set cmp k3) = NONE /\
    FLOOKUP (to_fmap cmp b) (key_set cmp k) = NONE /\
    FLOOKUP (to_fmap cmp (b1:(K,V)balanced_map)) (key_set cmp k) = NONE`
    STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC LBMAPAUX_ko_NONE THENL
     [MAP_EVERY EXISTS_TAC [`k':K`; `GREATER`];
      MAP_EVERY EXISTS_TAC [`k:K`; `GREATER`];
      MAP_EVERY EXISTS_TAC [`k:K`; `GREATER`]] THEN
    ASM_MESON_TAC[LBMAPAUX_good_cmp; ordering_eq_dec]; ALL_TAC] THEN
  LBMAPAUX_FMAP_TAC [`key_set (cmp:K->K->ordering) k3`;
                     `key_set (cmp:K->K->ordering) k'`;
                     `key_set (cmp:K->K->ordering) k`]
    [ASSUME `~(key_set (cmp:K->K->ordering) k = key_set cmp k')`;
     ASSUME `~(key_set (cmp:K->K->ordering) k = key_set cmp k3)`;
     ASSUME `~(key_set (cmp:K->K->ordering) k' = key_set cmp k3)`] []);;

let rotateR_thm = prove
 (`!k (v:V) l r (cmp:K->K->ordering).
     good_cmp cmp /\
     key_ordered cmp k l GREATER /\
     key_ordered cmp k r LESS /\
     ~(balanced_map_size' l + balanced_map_size' r <= 1) /\
     balanced_map_size' l > balanced_map_delta * balanced_map_size' r /\
     almost_balancedL (balanced_map_size' l) (balanced_map_size' r) /\
     balanced_map_invariant cmp l /\
     balanced_map_invariant cmp r
     ==> balanced_map_invariant cmp (rotateR k v l r) /\
         to_fmap cmp (rotateR k v l r) =
         FUNION (to_fmap cmp l) (to_fmap cmp r) |+ (key_set cmp k,v)`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC balanced_map_INDUCT THEN CONJ_TAC THENL
   [REWRITE_TAC[balanced_map_size'_def; GT] THEN ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s':num`; `k':K`; `x':V`; `ly:(K,V)balanced_map`;
                       `ry:(K,V)balanced_map`] THEN
  DISCH_THEN(K ALL_TAC) THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[rotateR_def] THEN COND_CASES_TAC THEN STRIP_TAC THENL
   [MATCH_MP_TAC singleR_thm; MATCH_MP_TAC doubleR_thm] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[balanced_map_size'_def]) THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let LBMAPAUX_BM_CASES_TAC (t:term) (names:term list) : tactic =
  MP_TAC(ISPEC t (cases "balanced_map")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC
    (EVERY_TCL (map X_CHOOSE_THEN names) SUBST_ALL_TAC));;

let LBMAPAUX_ALL_SS_TAC : tactic =
  fun (asl,w as g) ->
    let eqs = mapfilter (fun (_,th) ->
                let f,args = strip_comb (concl th) in
                if is_const f && fst(dest_const f) = "balanced_map_invariant" &&
                   length args = 2 && is_var (el 1 args)
                then MATCH_MP structure_size_thm th else fail()) asl in
    (RULE_ASSUM_TAC(REWRITE_RULE(map GSYM eqs)) THEN REWRITE_TAC(map GSYM eqs)) g;;

let LBMAPAUX_BAL_LEAF_TAC (defs:thm list) : tactic =
  RULE_ASSUM_TAC(REWRITE_RULE[structure_size_def; balanced_map_size'_def]) THEN
  LBMAPAUX_ALL_SS_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LBMAPAUX_balanced_alt]) THEN
  REWRITE_TAC(defs @ [bin_def; balanced_map_size'_def; structure_size_def;
                      ratio_def; balanced_map_delta_def; GT; case_def "balanced_map"]) THEN
  REPEAT COND_CASES_TAC THEN
  REWRITE_TAC[injectivity "balanced_map"; distinctness "balanced_map"] THEN
  (ASM_ARITH_TAC ORELSE (MATCH_MP_TAC(TAUT `F ==> p`) THEN ASM_ARITH_TAC));;

let balanceL_balL = prove
 (`!k (x:V) l r (cmp:K->K->ordering).
     good_cmp cmp /\ balanced_map_invariant cmp l /\ balanced_map_invariant cmp r
     ==> balanceL k x l r = balL k x l r`,
  let leaf = LBMAPAUX_BAL_LEAF_TAC
               [balanceL_def; balL_def; rotateR_def; singleR_def; doubleR_def] in
  let split_lr =
    LBMAPAUX_BM_CASES_TAC `ll:(K,V)balanced_map`
      [`lls:num`; `k1:K`; `v1:V`; `l1:(K,V)balanced_map`; `r1:(K,V)balanced_map`] THEN
    LBMAPAUX_BM_CASES_TAC `lr:(K,V)balanced_map`
      [`lrs:num`; `k2:K`; `v2:V`; `l2:(K,V)balanced_map`; `r2:(K,V)balanced_map`] THEN
    REWRITE_TAC[balanced_map_invariant_def] THEN STRIP_TAC in
  REPEAT GEN_TAC THEN
  LBMAPAUX_BM_CASES_TAC `r:(K,V)balanced_map`
    [`rs:num`; `rk:K`; `rx:V`; `rl:(K,V)balanced_map`; `rr:(K,V)balanced_map`] THEN
  LBMAPAUX_BM_CASES_TAC `l:(K,V)balanced_map`
    [`ls:num`; `lk:K`; `lx:V`; `ll:(K,V)balanced_map`; `lr:(K,V)balanced_map`] THENL
   [REWRITE_TAC[balanced_map_invariant_def] THEN STRIP_TAC THEN leaf;
    split_lr THENL
     [leaf;
      UNDISCH_TAC `balanced_map_invariant (cmp:K->K->ordering) (l2:(K,V)balanced_map)` THEN
      UNDISCH_TAC `balanced_map_invariant (cmp:K->K->ordering) (r2:(K,V)balanced_map)` THEN
      LBMAPAUX_BM_CASES_TAC `l2:(K,V)balanced_map`
        [`s5:num`; `k5:K`; `v5:V`; `l5:(K,V)balanced_map`; `r5:(K,V)balanced_map`] THEN
      LBMAPAUX_BM_CASES_TAC `r2:(K,V)balanced_map`
        [`s6:num`; `k6:K`; `v6:V`; `l6:(K,V)balanced_map`; `r6:(K,V)balanced_map`] THEN
      REWRITE_TAC[balanced_map_invariant_def] THEN REPEAT STRIP_TAC THEN leaf;
      leaf;
      leaf];
    REWRITE_TAC[balanced_map_invariant_def] THEN STRIP_TAC THEN leaf;
    split_lr THEN leaf]);;

let balanceL_thm = prove
 (`!k (v:V) l r (cmp:K->K->ordering).
     good_cmp cmp /\
     key_ordered cmp k l GREATER /\
     key_ordered cmp k r LESS /\
     almost_balancedL (balanced_map_size' l) (balanced_map_size' r) /\
     balanced_map_invariant cmp l /\
     balanced_map_invariant cmp r
     ==> balanced_map_invariant cmp (balanceL k v l r) /\
         to_fmap cmp (balanceL k v l r) =
         FUNION (to_fmap cmp l) (to_fmap cmp r) |+ (key_set cmp k,v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:K`; `v:V`; `l:(K,V)balanced_map`; `r:(K,V)balanced_map`;
                 `cmp:K->K->ordering`] balanceL_balL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[balL_def] THEN
  REPEAT COND_CASES_TAC THEN
  ASM_SIMP_TAC[rotateR_thm; balanced_map_invariant_def; to_fmap_def] THEN
  LBMAPAUX_ALL_SS_TAC THEN
  REWRITE_TAC[CONJ_ASSOC] THEN (CONJ_TAC THENL [ARITH_TAC; ALL_TAC]) THEN
  ASM_MESON_TAC[balanced_lem1; balanced_lem2]);;

let singleL_thm = prove
 (`!k (v:V) l (cmp:K->K->ordering) n k' v' b b0.
     good_cmp cmp /\
     key_ordered cmp k (Bin n k' v' b b0) LESS /\
     key_ordered cmp k l GREATER /\
     almost_balancedR (balanced_map_size' l) n /\
     ~(balanced_map_size' l + n <= 1) /\
     n > balanced_map_delta * balanced_map_size' l /\
     balanced_map_size' b < ratio * balanced_map_size' b0 /\
     balanced_map_invariant cmp (Bin n k' v' b b0) /\
     balanced_map_invariant cmp l
     ==> balanced_map_invariant cmp (singleL k v l (Bin n k' v' b b0)) /\
         to_fmap cmp (singleL k v l (Bin n k' v' b b0)) =
         FUNION (to_fmap cmp l) (to_fmap cmp (Bin n k' v' b b0)) |+
         (key_set cmp k,v)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[key_ordered_def; balanced_map_invariant_def] THEN
  STRIP_TAC THEN
  REWRITE_TAC[singleL_def; bin_def; balanced_map_invariant_def; key_ordered_def;
              balanced_map_size'_def; structure_size_def; to_fmap_def] THEN
  LBMAPAUX_SS_TAC [`b:(K,V)balanced_map`; `b0:(K,V)balanced_map`;
                   `l:(K,V)balanced_map`] THEN
  SUBGOAL_THEN `n = balanced_map_size' (b:(K,V)balanced_map) +
                    balanced_map_size' (b0:(K,V)balanced_map) + 1`
    SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(cmp:K->K->ordering) k' k = GREATER` ASSUME_TAC THENL
   [ASM_MESON_TAC[LBMAPAUX_good_cmp]; ALL_TAC] THEN
  MP_TAC(ISPECL [`balanced_map_size' (b:(K,V)balanced_map)`;
                 `balanced_map_size' (b0:(K,V)balanced_map)`;
                 `balanced_map_size' (l:(K,V)balanced_map)`] balanced_lem6) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `balanced_map_size' (b:(K,V)balanced_map) +
                balanced_map_size' (l:(K,V)balanced_map) + 1 =
                balanced_map_size' l + balanced_map_size' b + 1` SUBST1_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    ASM_MESON_TAC[LBMAPAUX_key_ordered_trans];
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(key_set (cmp:K->K->ordering) k = key_set cmp k')` ASSUME_TAC THENL
   [ASM_SIMP_TAC[key_set_eq; ordering_eq_dec]; ALL_TAC] THEN
  SUBGOAL_THEN `FLOOKUP (to_fmap (cmp:K->K->ordering) (l:(K,V)balanced_map))
                  (key_set cmp k') = NONE` ASSUME_TAC THENL
   [MATCH_MP_TAC LBMAPAUX_ko_NONE THEN
    MAP_EVERY EXISTS_TAC [`k:K`; `GREATER`] THEN
    ASM_REWRITE_TAC[ordering_eq_dec]; ALL_TAC] THEN
  LBMAPAUX_FMAP_TAC [`key_set (cmp:K->K->ordering) k'`;
                     `key_set (cmp:K->K->ordering) k`]
    [ASSUME `~(key_set (cmp:K->K->ordering) k = key_set cmp k')`] []);;

let doubleL_thm = prove
 (`!k (v:V) l (cmp:K->K->ordering) n k' v' b b0.
     good_cmp cmp /\
     key_ordered cmp k (Bin n k' v' b b0) LESS /\
     key_ordered cmp k l GREATER /\
     almost_balancedR (balanced_map_size' l) n /\
     ~(n + balanced_map_size' l <= 1) /\
     n > balanced_map_delta * balanced_map_size' l /\
     ~(balanced_map_size' b < ratio * balanced_map_size' b0) /\
     balanced_map_invariant cmp (Bin n k' v' b b0) /\
     balanced_map_invariant cmp l
     ==> balanced_map_invariant cmp (doubleL k v l (Bin n k' v' b b0)) /\
         to_fmap cmp (doubleL k v l (Bin n k' v' b b0)) =
         FUNION (to_fmap cmp l) (to_fmap cmp (Bin n k' v' b b0)) |+
         (key_set cmp k,v)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `b:(K,V)balanced_map` (cases "balanced_map")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC
    (X_CHOOSE_THEN `s3:num` (X_CHOOSE_THEN `k3:K` (X_CHOOSE_THEN `v3:V`
      (X_CHOOSE_THEN `b1:(K,V)balanced_map`
        (X_CHOOSE_THEN `b2:(K,V)balanced_map` SUBST1_TAC)))))) THENL
   [REWRITE_TAC[key_ordered_def; balanced_map_invariant_def;
                balanced_map_size'_def; structure_size_def] THEN
    STRIP_TAC THEN LBMAPAUX_SS_TAC [`b0:(K,V)balanced_map`; `l:(K,V)balanced_map`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ratio_def; balanced_map_delta_def]) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[key_ordered_def; balanced_map_invariant_def;
              balanced_map_size'_def; structure_size_def] THEN
  STRIP_TAC THEN
  REWRITE_TAC[doubleL_def; bin_def; balanced_map_invariant_def; key_ordered_def;
              balanced_map_size'_def; structure_size_def; to_fmap_def] THEN
  LBMAPAUX_SS_TAC [`b0:(K,V)balanced_map`; `b1:(K,V)balanced_map`;
                   `b2:(K,V)balanced_map`; `l:(K,V)balanced_map`] THEN
  SUBGOAL_THEN `n = balanced_map_size' (b1:(K,V)balanced_map) +
                    balanced_map_size' (b0:(K,V)balanced_map) +
                    balanced_map_size' (b2:(K,V)balanced_map) + 2`
    SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `s3 = balanced_map_size' (b1:(K,V)balanced_map) +
                     balanced_map_size' (b2:(K,V)balanced_map) + 1`
    SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(cmp:K->K->ordering) k3 k = GREATER /\ cmp k3 k' = LESS /\
                cmp k' k = GREATER` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[LBMAPAUX_good_cmp]; ALL_TAC] THEN
  MP_TAC(ISPECL [`balanced_map_size' (b:(K,V)balanced_map)`;
                 `balanced_map_size' (b0:(K,V)balanced_map)`;
                 `balanced_map_size' (b2:(K,V)balanced_map)`;
                 `balanced_map_size' (l:(K,V)balanced_map)`;
                 `balanced_map_size' (b1:(K,V)balanced_map)`] balanced_lem7) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `balanced_map_size' (b1:(K,V)balanced_map) +
                balanced_map_size' (l:(K,V)balanced_map) + 1 =
                balanced_map_size' l + balanced_map_size' b1 + 1 /\
                balanced_map_size' (b0:(K,V)balanced_map) +
                balanced_map_size' (b2:(K,V)balanced_map) + 1 =
                balanced_map_size' b2 + balanced_map_size' b0 + 1`
    (CONJUNCTS_THEN SUBST1_TAC) THENL [ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    ASM_MESON_TAC[LBMAPAUX_key_ordered_trans];
    ASM_MESON_TAC[LBMAPAUX_key_ordered_trans];
    ARITH_TAC;
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(key_set (cmp:K->K->ordering) k = key_set cmp k') /\
                ~(key_set cmp k = key_set cmp k3) /\
                ~(key_set cmp k' = key_set cmp k3)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[key_set_eq] THEN ASM_MESON_TAC[LBMAPAUX_good_cmp; ordering_eq_dec];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `FLOOKUP (to_fmap (cmp:K->K->ordering) (l:(K,V)balanced_map)) (key_set cmp k3) = NONE /\
    FLOOKUP (to_fmap cmp l) (key_set cmp k') = NONE /\
    FLOOKUP (to_fmap cmp (b1:(K,V)balanced_map)) (key_set cmp k') = NONE`
    STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC LBMAPAUX_ko_NONE THENL
     [MAP_EVERY EXISTS_TAC [`k:K`; `GREATER`];
      MAP_EVERY EXISTS_TAC [`k:K`; `GREATER`];
      MAP_EVERY EXISTS_TAC [`k':K`; `GREATER`]] THEN
    ASM_MESON_TAC[LBMAPAUX_good_cmp; ordering_eq_dec]; ALL_TAC] THEN
  LBMAPAUX_FMAP_TAC [`key_set (cmp:K->K->ordering) k3`;
                     `key_set (cmp:K->K->ordering) k'`;
                     `key_set (cmp:K->K->ordering) k`]
    [ASSUME `~(key_set (cmp:K->K->ordering) k = key_set cmp k')`;
     ASSUME `~(key_set (cmp:K->K->ordering) k = key_set cmp k3)`;
     ASSUME `~(key_set (cmp:K->K->ordering) k' = key_set cmp k3)`] []);;

let rotateL_thm = prove
 (`!k (v:V) l r (cmp:K->K->ordering).
     good_cmp cmp /\
     key_ordered cmp k r LESS /\
     key_ordered cmp k l GREATER /\
     ~(balanced_map_size' l + balanced_map_size' r <= 1) /\
     balanced_map_size' r > balanced_map_delta * balanced_map_size' l /\
     almost_balancedR (balanced_map_size' l) (balanced_map_size' r) /\
     balanced_map_invariant cmp l /\
     balanced_map_invariant cmp r
     ==> balanced_map_invariant cmp (rotateL k v l r) /\
         to_fmap cmp (rotateL k v l r) =
         FUNION (to_fmap cmp l) (to_fmap cmp r) |+ (key_set cmp k,v)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  MATCH_MP_TAC balanced_map_INDUCT THEN CONJ_TAC THENL
   [REWRITE_TAC[balanced_map_size'_def; GT] THEN ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s':num`; `k':K`; `x':V`; `ly:(K,V)balanced_map`;
                       `ry:(K,V)balanced_map`] THEN
  DISCH_THEN(K ALL_TAC) THEN GEN_TAC THEN
  REWRITE_TAC[rotateL_def] THEN COND_CASES_TAC THEN STRIP_TAC THENL
   [MATCH_MP_TAC singleL_thm; MATCH_MP_TAC doubleL_thm] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[balanced_map_size'_def]) THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let balanceR_balR = prove
 (`!k (x:V) l r (cmp:K->K->ordering).
     good_cmp cmp /\ balanced_map_invariant cmp l /\ balanced_map_invariant cmp r
     ==> balanceR k x l r = balR k x l r`,
  let leaf = LBMAPAUX_BAL_LEAF_TAC
               [balanceR_def; balR_def; rotateL_def; singleL_def; doubleL_def] in
  let split_rlr =
    LBMAPAUX_BM_CASES_TAC `rl:(K,V)balanced_map`
      [`rls:num`; `k1:K`; `v1:V`; `l1:(K,V)balanced_map`; `r1:(K,V)balanced_map`] THEN
    LBMAPAUX_BM_CASES_TAC `rr:(K,V)balanced_map`
      [`rrs:num`; `k2:K`; `v2:V`; `l2:(K,V)balanced_map`; `r2:(K,V)balanced_map`] THEN
    REWRITE_TAC[balanced_map_invariant_def] THEN STRIP_TAC in
  REPEAT GEN_TAC THEN
  LBMAPAUX_BM_CASES_TAC `l:(K,V)balanced_map`
    [`ls:num`; `lk:K`; `lx:V`; `ll:(K,V)balanced_map`; `lr:(K,V)balanced_map`] THEN
  LBMAPAUX_BM_CASES_TAC `r:(K,V)balanced_map`
    [`rs:num`; `rk:K`; `rx:V`; `rl:(K,V)balanced_map`; `rr:(K,V)balanced_map`] THENL
   [REWRITE_TAC[balanced_map_invariant_def] THEN STRIP_TAC THEN leaf;
    split_rlr THENL
     [leaf;
      leaf;
      UNDISCH_TAC `balanced_map_invariant (cmp:K->K->ordering) (l1:(K,V)balanced_map)` THEN
      UNDISCH_TAC `balanced_map_invariant (cmp:K->K->ordering) (r1:(K,V)balanced_map)` THEN
      LBMAPAUX_BM_CASES_TAC `l1:(K,V)balanced_map`
        [`s5:num`; `k5:K`; `v5:V`; `l5:(K,V)balanced_map`; `r5:(K,V)balanced_map`] THEN
      LBMAPAUX_BM_CASES_TAC `r1:(K,V)balanced_map`
        [`s6:num`; `k6:K`; `v6:V`; `l6:(K,V)balanced_map`; `r6:(K,V)balanced_map`] THEN
      REWRITE_TAC[balanced_map_invariant_def] THEN REPEAT STRIP_TAC THEN leaf;
      leaf];
    REWRITE_TAC[balanced_map_invariant_def] THEN STRIP_TAC THEN leaf;
    split_rlr THEN leaf]);;

let balanceR_thm = prove
 (`!k (v:V) l r (cmp:K->K->ordering).
     good_cmp cmp /\
     key_ordered cmp k r LESS /\
     key_ordered cmp k l GREATER /\
     almost_balancedR (balanced_map_size' l) (balanced_map_size' r) /\
     balanced_map_invariant cmp l /\
     balanced_map_invariant cmp r
     ==> balanced_map_invariant cmp (balanceR k v l r) /\
         to_fmap cmp (balanceR k v l r) =
         FUNION (to_fmap cmp l) (to_fmap cmp r) |+ (key_set cmp k,v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:K`; `v:V`; `l:(K,V)balanced_map`; `r:(K,V)balanced_map`;
                 `cmp:K->K->ordering`] balanceR_balR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[balR_def] THEN
  REPEAT COND_CASES_TAC THEN
  ASM_SIMP_TAC[rotateL_thm; balanced_map_invariant_def; to_fmap_def] THEN
  LBMAPAUX_ALL_SS_TAC THEN
  REWRITE_TAC[CONJ_ASSOC] THEN (CONJ_TAC THENL [ARITH_TAC; ALL_TAC]) THEN
  ASM_MESON_TAC[balanced_lem1; balanced_lem5]);;

let LBMAPAUX_key_ordered_eq = prove
 (`!(cmp:K->K->ordering) k1 k2 (t:(K,V)balanced_map) res.
     good_cmp cmp /\ cmp k1 k2 = EQUAL /\ key_ordered cmp k2 t res
     ==> key_ordered cmp k1 t res`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC balanced_map_INDUCT THEN
  REWRITE_TAC[key_ordered_def] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[] THEN
  MP_TAC(ISPEC `res:ordering` ordering_nchotomy) THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_MESON_TAC[LBMAPAUX_good_cmp]);;

let LBMAPAUX_ko_update = prove
 (`!(cmp:K->K->ordering) a k (t:(K,V)balanced_map) (t':(K,V)balanced_map) res.
     good_cmp cmp /\
     FDOM (to_fmap cmp t') = key_set cmp k INSERT FDOM (to_fmap cmp t) /\
     key_ordered cmp a t res /\ cmp a k = res
     ==> key_ordered cmp a t' res`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `key_ordered (cmp:K->K->ordering) a (t:(K,V)balanced_map) res` THEN
  ASM_SIMP_TAC[key_ordered_to_fmap; FORALL_IN_INSERT; key_set_cmp_thm]);;

let insert_thm = prove
 (`!(t:(K,V)balanced_map) (cmp:K->K->ordering) k (v:V).
     good_cmp cmp /\ balanced_map_invariant cmp t
     ==> balanced_map_invariant cmp (balanced_map_insert cmp k v t) /\
         to_fmap cmp (balanced_map_insert cmp k v t) =
         to_fmap cmp t |+ (key_set cmp k,v)`,
  MATCH_MP_TAC balanced_map_INDUCT THEN CONJ_TAC THENL
   [REWRITE_TAC[balanced_map_insert_def; singleton_thm; to_fmap_def]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:num`; `k':K`; `v':V`; `l:(K,V)balanced_map`;
                       `r:(K,V)balanced_map`] THEN
  DISCH_TAC THEN REPEAT GEN_TAC THEN
  POP_ASSUM(CONJUNCTS_THEN (MP_TAC o SPECL [`cmp:K->K->ordering`; `k:K`; `v:V`])) THEN
  DISCH_THEN(LABEL_TAC "ihr") THEN DISCH_THEN(LABEL_TAC "ihl") THEN
  REWRITE_TAC[balanced_map_insert_def; balanced_map_invariant_def] THEN
  STRIP_TAC THEN
  REMOVE_THEN "ihl" MP_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REMOVE_THEN "ihr" MP_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`cmp:K->K->ordering`; `l:(K,V)balanced_map`] size_thm) THEN
  MP_TAC(ISPECL [`cmp:K->K->ordering`; `r:(K,V)balanced_map`] size_thm) THEN
  MP_TAC(ISPECL [`cmp:K->K->ordering`; `balanced_map_insert (cmp:K->K->ordering) k (v:V) l`]
                size_thm) THEN
  MP_TAC(ISPECL [`cmp:K->K->ordering`; `balanced_map_insert (cmp:K->K->ordering) k (v:V) r`]
                size_thm) THEN
  ASM_REWRITE_TAC[FCARD_FUPDATE] THEN REPEAT DISCH_TAC THEN
  MP_TAC(ISPECL [`cmp:K->K->ordering`; `k:K`; `k':K`] LBMAPAUX_cmp_cases) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[ordering_case_def] THENL
   [(* LESS *)
    MP_TAC(ISPECL [`k':K`; `v':V`; `balanced_map_insert (cmp:K->K->ordering) k (v:V) l`;
                   `r:(K,V)balanced_map`; `cmp:K->K->ordering`] balanceL_thm) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC LBMAPAUX_ko_update THEN
        MAP_EVERY EXISTS_TAC [`k:K`; `l:(K,V)balanced_map`] THEN
        ASM_REWRITE_TAC[FDOM_FUPDATE];
        COND_CASES_TAC THEN ASM_MESON_TAC[almost_balancedL_thm; ADD_SYM]];
      ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[to_fmap_def; FUNION_FUPDATE_1] THEN
    MATCH_MP_TAC FUPDATE_COMMUTES THEN ASM_SIMP_TAC[key_set_eq; ordering_eq_dec];
    (* EQUAL *)
    REWRITE_TAC[balanced_map_invariant_def; to_fmap_def] THEN
    SUBGOAL_THEN `key_set (cmp:K->K->ordering) k' = key_set cmp k` SUBST1_TAC THENL
     [ASM_SIMP_TAC[key_set_eq]; ALL_TAC] THEN
    ASM_REWRITE_TAC[FUPDATE_EQ] THEN
    ASM_MESON_TAC[LBMAPAUX_key_ordered_eq];
    (* GREATER *)
    MP_TAC(ISPECL [`k':K`; `v':V`; `l:(K,V)balanced_map`;
                   `balanced_map_insert (cmp:K->K->ordering) k (v:V) r`;
                   `cmp:K->K->ordering`] balanceR_thm) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC LBMAPAUX_ko_update THEN
        MAP_EVERY EXISTS_TAC [`k:K`; `r:(K,V)balanced_map`] THEN
        ASM_REWRITE_TAC[FDOM_FUPDATE];
        COND_CASES_TAC THEN ASM_MESON_TAC[almost_balancedR_thm; ADD_SYM]];
      ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    SUBGOAL_THEN `~(key_set (cmp:K->K->ordering) k IN FDOM (to_fmap cmp (l:(K,V)balanced_map)))`
      ASSUME_TAC THENL
     [REWRITE_TAC[GSYM flookup_thm] THEN MATCH_MP_TAC LBMAPAUX_ko_NONE THEN
      MAP_EVERY EXISTS_TAC [`k':K`; `GREATER`] THEN
      ASM_REWRITE_TAC[ordering_eq_dec]; ALL_TAC] THEN
    ASM_REWRITE_TAC[to_fmap_def; FUNION_FUPDATE_2] THEN
    MATCH_MP_TAC FUPDATE_COMMUTES THEN ASM_SIMP_TAC[key_set_eq; ordering_eq_dec]]);;

(* HOL4: lookup_insert *)

let balanced_map_lookup_insert = prove
 (`!(cmp:K->K->ordering) (t:(K,V)balanced_map) k k' v.
     good_cmp cmp /\ balanced_map_invariant cmp t
     ==> balanced_map_lookup cmp k (balanced_map_insert cmp k' v t) =
         if cmp k k' = EQUAL then SOME v else balanced_map_lookup cmp k t`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(K,V)balanced_map`; `cmp:K->K->ordering`; `k':K`; `v:V`]
                insert_thm) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[lookup_thm; FLOOKUP_UPDATE; key_set_eq] THEN
  ASM_MESON_TAC[LBMAPAUX_good_cmp]);;
