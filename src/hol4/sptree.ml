(* ========================================================================= *)
(* sptree: port of HOL4 src/finite_maps/sptreeScript.sml (HOL4 library used *)
(* by CakeML v3479), and of examples/algorithms/spt_closureScript.sml.       *)
(* A log-time random-access, extensible array implementation with union:    *)
(* num-indexed finite maps as binary tries.                                  *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - num_map is :A spt (HOL Light type abbreviations take no parameters);   *)
(*   num_set is the abbreviation :1 spt (HOL4 unit = HOL Light 1, () = one). *)
(* - HOL4's isEmpty is an overload of \t. t = LN: the theorems below are     *)
(*   stated with t = LN (the term HOL4 really has); the constant isEmpty     *)
(*   (isEmpty_def, a simp rule) is there for definitions that use the name.  *)
(* - HOL4 size_def is sptree_size_def (size_def is the kit function).       *)
(* - case expressions are case constants (spt_CASE, option_CASE, ...); the   *)
(*   case of a pair of lookups in lookup_inter is the nested option_CASE.    *)
(* - Lemmas named SPTAUX_... are helpers of this file (not HOL4 names).     *)
(* - HOL4 size, map, wf, union and inter are sptree_size, sptree_map,        *)
(*   sptree_wf, sptree_union and sptree_inter (short or common words), with  *)
(*   the theorems renamed alike (map_def is sptree_map_def, ...).            *)
(* ========================================================================= *)

needs "hol4/vocab.ml";;

(* ------------------------------------------------------------------------- *)
(* The datatype.                                                             *)
(* ------------------------------------------------------------------------- *)

let spt_INDUCT,spt_RECURSION = cake_type
  "spt = LN | LS A | BN spt spt | BS spt A spt";;

(* Leaf-None, Leaf-Some, Branch-None, Branch-Some *)

let spt_distinct = distinctness "spt";;
let spt_inject = injectivity "spt";;
let spt_CASE = case_def "spt";;
let spt_case_eq = case_eq "spt";;
let spt_size_def = size_def "spt";;

new_type_abbrev("num_set",`:1 spt`);;

let isEmpty_def = new_definition
  `isEmpty (t:A spt) <=> t = LN`;;

let sptree_wf_def = cake_def
  `(sptree_wf LN <=> T) /\
   (sptree_wf (LS (a:A)) <=> T) /\
   (sptree_wf (BN t1 t2) <=> sptree_wf t1 /\ sptree_wf t2 /\ ~(t1 = LN /\ t2 = LN)) /\
   (sptree_wf (BS t1 a t2) <=> sptree_wf t1 /\ sptree_wf t2 /\ ~(t1 = LN /\ t2 = LN))`;;

(* ------------------------------------------------------------------------- *)
(* Keys: 0 is the root, key 2m+2 is key m of the left subtree, key 2m+1 is  *)
(* key m of the right subtree.  Helpers for this view of the numbers.       *)
(* ------------------------------------------------------------------------- *)

let SPTAUX_DIV2_LT = prove
 (`!k. ~(k = 0) ==> (k - 1) DIV 2 < k`,
  ARITH_TAC);;

let SPTAUX_TC_TAC =
  REWRITE_TAC(FST::SND::WF_REL_THMS) THEN REPEAT STRIP_TAC THEN ASM_ARITH_TAC;;

let SPTAUX_bit_cases = prove
 (`!n. n = 0 \/ (?m. n = 2 * m + 1) \/ (?m. n = 2 * m + 2)`,
  INDUCT_TAC THEN REWRITE_TAC[NOT_SUC] THEN
  FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THENL
   [DISJ1_TAC THEN EXISTS_TAC `0` THEN ARITH_TAC;
    DISJ2_TAC THEN EXISTS_TAC `m:num` THEN ARITH_TAC;
    DISJ1_TAC THEN EXISTS_TAC `m + 1` THEN ARITH_TAC]);;

let SPTAUX_bit_induction = prove
 (`!P. P 0 /\ (!n. P n ==> P (2 * n + 1)) /\ (!n. P n ==> P (2 * n + 2))
       ==> !n. P n`,
  GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN
  REPEAT_TCL STRIP_THM_THEN SUBST1_TAC (SPEC `n:num` SPTAUX_bit_cases) THEN
  ASM_MESON_TAC[ARITH_RULE `m < 2 * m + 1 /\ m < 2 * m + 2`]);;

let SPTAUX_BIT_RW = prove
 (`(!m. ~(2 * m + 1 = 0)) /\ (!m. ~(2 * m + 2 = 0)) /\
   (!m. ~(0 = 2 * m + 1)) /\ (!m. ~(0 = 2 * m + 2)) /\
   (!m. EVEN (2 * m + 1) <=> F) /\ (!m. EVEN (2 * m + 2) <=> T) /\
   (!m. ODD (2 * m + 1) <=> T) /\ (!m. ODD (2 * m + 2) <=> F) /\
   (!m. ((2 * m + 1) - 1) DIV 2 = m) /\ (!m. ((2 * m + 2) - 1) DIV 2 = m) /\
   (!m n. 2 * m + 1 = 2 * n + 1 <=> m = n) /\
   (!m n. 2 * m + 2 = 2 * n + 2 <=> m = n) /\
   (!m n. ~(2 * m + 1 = 2 * n + 2)) /\ (!m n. ~(2 * m + 2 = 2 * n + 1))`,
  REWRITE_TAC[EVEN_ADD; EVEN_MULT; ODD_ADD; ODD_MULT; ARITH] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN TRY ARITH_TAC THEN
  DISCH_THEN(MP_TAC o AP_TERM `EVEN`) THEN
  REWRITE_TAC[EVEN_ADD; EVEN_MULT; ARITH]);;

(* split a key k into the cases 0, 2m+1, 2m+2 *)

let SPTAUX_BITS_TAC (k:term) : tactic =
  REPEAT_TCL STRIP_THM_THEN SUBST_ALL_TAC (SPEC k SPTAUX_bit_cases);;

let SPTAUX_CASES_TAC (t:term) : tactic = CASES_ON t;;

(* ------------------------------------------------------------------------- *)
(* lookup and insert.                                                        *)
(* ------------------------------------------------------------------------- *)

let lookup_def = cake_def_wf `MEASURE (FST:num#A spt->num)` SPTAUX_TC_TAC
  `(lookup k LN = NONE) /\
   (lookup k (LS (a:A)) = if k = 0 then SOME a else NONE) /\
   (lookup k (BN t1 t2) =
      if k = 0 then NONE
      else lookup ((k - 1) DIV 2) (if EVEN k then t1 else t2)) /\
   (lookup k (BS t1 a t2) =
      if k = 0 then SOME a
      else lookup ((k - 1) DIV 2) (if EVEN k then t1 else t2))`;;

(* lookup_ind is proved directly (independent of the kit derivation) *)

let lookup_ind = prove
 (`!P. (!k. P k (LN:A spt)) /\ (!k (a:A). P k (LS a)) /\
       (!k t1 t2. (~(k = 0) ==> P ((k - 1) DIV 2) (if EVEN k then t1 else t2))
                  ==> P k (BN t1 t2)) /\
       (!k t1 (a:A) t2.
          (~(k = 0) ==> P ((k - 1) DIV 2) (if EVEN k then t1 else t2))
          ==> P k (BS t1 a t2))
       ==> !k t. P k t`,
  GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC num_WF THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN MATCH_MP_TAC spt_INDUCT THEN
  ASM_MESON_TAC[SPTAUX_DIV2_LT]);;

let lookup_rwts = prove
 (`lookup k (LN:A spt) = NONE /\
   lookup 0 (LS (a:A)) = SOME a /\
   lookup 0 (BN t1 t2) = NONE:A option /\
   lookup 0 (BS t1 (a:A) t2) = SOME a`,
  REWRITE_TAC[lookup_def]);;

let SPTAUX_lookup_bits = prove
 (`(!m. lookup (2 * m + 1) (LN:A spt) = NONE) /\
   (!m (a:A). lookup (2 * m + 1) (LS a) = NONE) /\
   (!m t1 (t2:A spt). lookup (2 * m + 1) (BN t1 t2) = lookup m t2) /\
   (!m t1 (a:A) t2. lookup (2 * m + 1) (BS t1 a t2) = lookup m t2) /\
   (!m. lookup (2 * m + 2) (LN:A spt) = NONE) /\
   (!m (a:A). lookup (2 * m + 2) (LS a) = NONE) /\
   (!m t1 (t2:A spt). lookup (2 * m + 2) (BN t1 t2) = lookup m t1) /\
   (!m t1 (a:A) t2. lookup (2 * m + 2) (BS t1 a t2) = lookup m t1)`,
  REWRITE_TAC[lookup_def; SPTAUX_BIT_RW]);;

let insert_def = cake_def_wf `MEASURE (FST:num#A#A spt->num)` SPTAUX_TC_TAC
  `(insert k (a:A) LN = if k = 0 then LS a
                     else if EVEN k then BN (insert ((k-1) DIV 2) a LN) LN
                     else BN LN (insert ((k-1) DIV 2) a LN)) /\
   (insert k a (LS a') =
     if k = 0 then LS a
     else if EVEN k then BS (insert ((k-1) DIV 2) a LN) a' LN
     else BS LN a' (insert ((k-1) DIV 2) a LN)) /\
   (insert k a (BN t1 t2) =
     if k = 0 then BS t1 a t2
     else if EVEN k then BN (insert ((k - 1) DIV 2) a t1) t2
     else BN t1 (insert ((k - 1) DIV 2) a t2)) /\
   (insert k a (BS t1 a' t2) =
     if k = 0 then BS t1 a t2
     else if EVEN k then BS (insert ((k - 1) DIV 2) a t1) a' t2
     else BS t1 a' (insert ((k - 1) DIV 2) a t2))`;;

let insert_ind = cake_ind "insert";;

(* insert_def at the keys 0, 2m+1, 2m+2 (safe rewrites: insert_def          *)
(* itself loops on insert k a LN)                                            *)

let SPTAUX_insert_bits = prove
 (`(!a:A. insert 0 a LN = LS a) /\
   (!a a':A. insert 0 a (LS a') = LS a) /\
   (!(a:A) t1 t2. insert 0 a (BN t1 t2) = BS t1 a t2) /\
   (!(a:A) a' t1 t2. insert 0 a (BS t1 a' t2) = BS t1 a t2) /\
   (!m (a:A). insert (2 * m + 1) a LN = BN LN (insert m a LN)) /\
   (!m (a:A) a'. insert (2 * m + 1) a (LS a') = BS LN a' (insert m a LN)) /\
   (!m (a:A) t1 t2. insert (2 * m + 1) a (BN t1 t2) = BN t1 (insert m a t2)) /\
   (!m (a:A) a' t1 t2.
      insert (2 * m + 1) a (BS t1 a' t2) = BS t1 a' (insert m a t2)) /\
   (!m (a:A). insert (2 * m + 2) a LN = BN (insert m a LN) LN) /\
   (!m (a:A) a'. insert (2 * m + 2) a (LS a') = BS (insert m a LN) a' LN) /\
   (!m (a:A) t1 t2. insert (2 * m + 2) a (BN t1 t2) = BN (insert m a t1) t2) /\
   (!m (a:A) a' t1 t2.
      insert (2 * m + 2) a (BS t1 a' t2) = BS (insert m a t1) a' t2)`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [insert_def] THEN REWRITE_TAC[SPTAUX_BIT_RW]);;

let mk_BN_def = cake_def
  `(mk_BN LN LN = LN:A spt) /\
   (mk_BN LN (LS v6) = BN LN (LS (v6:A))) /\
   (mk_BN LN (BN v7 v8) = BN LN (BN v7 v8)) /\
   (mk_BN LN (BS v9 v10 v11) = BN LN (BS v9 v10 v11)) /\
   (mk_BN (LS v) t2 = BN (LS v) t2) /\
   (mk_BN (BN v1 v2) t2 = BN (BN v1 v2) t2) /\
   (mk_BN (BS v3 v4 v5) t2 = BN (BS v3 v4 v5) t2)`;;

let mk_BS_def = cake_def
  `(mk_BS LN x LN = LS (x:A)) /\
   (mk_BS LN x (LS v6) = BS LN x (LS v6)) /\
   (mk_BS LN x (BN v7 v8) = BS LN x (BN v7 v8)) /\
   (mk_BS LN x (BS v9 v10 v11) = BS LN x (BS v9 v10 v11)) /\
   (mk_BS (LS v) x t2 = BS (LS v) x t2) /\
   (mk_BS (BN v1 v2) x t2 = BS (BN v1 v2) x t2) /\
   (mk_BS (BS v3 v4 v5) x t2 = BS (BS v3 v4 v5) x t2)`;;

let delete_def = cake_def
  `(delete k LN = LN:A spt) /\
   (delete k (LS (a:A)) = if k = 0 then LN else LS a) /\
   (delete k (BN t1 t2) =
      if k = 0 then BN t1 t2
      else if EVEN k then mk_BN (delete ((k - 1) DIV 2) t1) t2
      else mk_BN t1 (delete ((k - 1) DIV 2) t2)) /\
   (delete k (BS t1 a t2) =
      if k = 0 then BN t1 t2
      else if EVEN k then mk_BS (delete ((k - 1) DIV 2) t1) a t2
      else mk_BS t1 a (delete ((k - 1) DIV 2) t2))`;;

let fromList_def = new_definition
  `fromList (l:A list) =
     SND (FOLDL (\(i,t) a. (i + 1,insert i a t)) (0,LN) l)`;;

(* HOL4: size_def (the name is the kit function size_def) *)

let sptree_size_def = cake_def
  `(sptree_size (LN:A spt) = 0) /\
   (sptree_size (LS (a:A)) = 1) /\
   (sptree_size (BN t1 t2) = sptree_size t1 + sptree_size t2) /\
   (sptree_size (BS t1 a t2) = sptree_size t1 + sptree_size t2 + 1)`;;

let insert_notEmpty = prove
 (`~(insert k (a:A) t = LN)`,
  SPTAUX_CASES_TAC `t:A spt` THEN ONCE_REWRITE_TAC[insert_def] THEN
  REPEAT COND_CASES_TAC THEN REWRITE_TAC[spt_distinct]);;

let wf_insert = prove
 (`!k (a:A) t. sptree_wf t ==> sptree_wf (insert k a t)`,
  MATCH_MP_TAC SPTAUX_bit_induction THEN REPEAT STRIP_TAC THEN
  SPTAUX_CASES_TAC `t:A spt` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[sptree_wf_def]) THEN
  ASM_SIMP_TAC[SPTAUX_insert_bits; sptree_wf_def; insert_notEmpty]);;

let mk_BN_thm = prove
 (`!t1 t2:A spt. mk_BN t1 t2 = if t1 = LN /\ t2 = LN then LN else BN t1 t2`,
  REPEAT GEN_TAC THEN SPTAUX_CASES_TAC `t1:A spt` THEN
  SPTAUX_CASES_TAC `t2:A spt` THEN REWRITE_TAC[mk_BN_def; spt_distinct]);;

let mk_BS_thm = prove
 (`!t1 t2:A spt. mk_BS t1 x t2 = if t1 = LN /\ t2 = LN then LS x else BS t1 x t2`,
  REPEAT GEN_TAC THEN SPTAUX_CASES_TAC `t1:A spt` THEN
  SPTAUX_CASES_TAC `t2:A spt` THEN REWRITE_TAC[mk_BS_def; spt_distinct]);;

let wf_delete = prove
 (`!t k. sptree_wf (t:A spt) ==> sptree_wf (delete k t)`,
  MATCH_MP_TAC spt_INDUCT THEN REWRITE_TAC[sptree_wf_def; delete_def] THEN
  REPEAT STRIP_TAC THEN REPEAT COND_CASES_TAC THEN
  ASM_SIMP_TAC[sptree_wf_def; mk_BN_thm; mk_BS_thm] THEN
  REPEAT COND_CASES_TAC THEN ASM_SIMP_TAC[sptree_wf_def]);;

(* HOL4 proves lookup_insert1 first; here it follows from lookup_insert *)

let lookup_insert = prove
 (`!k2 (v:A) t k1. lookup k1 (insert k2 v t) =
                   if k1 = k2 then SOME v else lookup k1 t`,
  MATCH_MP_TAC SPTAUX_bit_induction THEN REPEAT STRIP_TAC THEN
  SPTAUX_BITS_TAC `k1:num` THEN SPTAUX_CASES_TAC `t:A spt` THEN
  ASM_REWRITE_TAC[SPTAUX_insert_bits; SPTAUX_lookup_bits; lookup_rwts;
                  SPTAUX_BIT_RW]);;

let lookup_insert1 = prove
 (`!k (a:A) t. lookup k (insert k a t) = SOME a`,
  REWRITE_TAC[lookup_insert]);;

(* ------------------------------------------------------------------------- *)
(* union                                                                     *)
(* ------------------------------------------------------------------------- *)

let sptree_union_def = cake_def
  `(sptree_union LN t = t:A spt) /\
   (sptree_union (LS (a:A)) t =
      spt_CASE t (LS a) (\b. LS a) (\t1 t2. BS t1 a t2)
                 (\t1 b t2. BS t1 a t2)) /\
   (sptree_union (BN t1 t2) t =
      spt_CASE t (BN t1 t2) (\a. BS t1 a t2)
                 (\t1' t2'. BN (sptree_union t1 t1') (sptree_union t2 t2'))
                 (\t1' a t2'. BS (sptree_union t1 t1') a (sptree_union t2 t2'))) /\
   (sptree_union (BS t1 a t2) t =
      spt_CASE t (BS t1 a t2) (\a'. BS t1 a t2)
                 (\t1' t2'. BS (sptree_union t1 t1') a (sptree_union t2 t2'))
                 (\t1' a' t2'. BS (sptree_union t1 t1') a (sptree_union t2 t2')))`;;

(* HOL4: isEmpty_union *)

let isEmpty_union = prove
 (`sptree_union m1 m2 = LN <=> m1 = LN /\ m2 = (LN:A spt)`,
  SPTAUX_CASES_TAC `m1:A spt` THEN SPTAUX_CASES_TAC `m2:A spt` THEN
  REWRITE_TAC[sptree_union_def; spt_CASE; spt_distinct]);;

let wf_union = prove
 (`!m1 m2:A spt. sptree_wf m1 /\ sptree_wf m2 ==> sptree_wf (sptree_union m1 m2)`,
  MATCH_MP_TAC spt_INDUCT THEN REPEAT STRIP_TAC THEN
  SPTAUX_CASES_TAC `m2:A spt` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[sptree_wf_def]) THEN
  ASM_SIMP_TAC[sptree_union_def; spt_CASE; sptree_wf_def; isEmpty_union] THEN
  ASM_MESON_TAC[]);;

(* HOL4: optcase_lemma *)

let SPTAUX_optcase_lemma = prove
 (`!opt. option_CASE opt NONE (\v:A. SOME v) = opt`,
  GEN_TAC THEN SPTAUX_CASES_TAC `opt:A option` THEN REWRITE_TAC[option_CASE]);;

let lookup_union = prove
 (`!m1 m2 k. lookup k (sptree_union m1 m2) =
             option_CASE (lookup k m1) (lookup k m2) (\v:A. SOME v)`,
  MATCH_MP_TAC spt_INDUCT THEN REPEAT STRIP_TAC THEN
  SPTAUX_CASES_TAC `m2:A spt` THEN SPTAUX_BITS_TAC `k:num` THEN
  ASM_REWRITE_TAC[sptree_union_def; spt_CASE; lookup_rwts; SPTAUX_lookup_bits;
                  option_CASE; SPTAUX_optcase_lemma]);;

(* ------------------------------------------------------------------------- *)
(* inter, inter_eq, difference                                               *)
(* ------------------------------------------------------------------------- *)

let sptree_inter_def = cake_def
  `(sptree_inter LN (t:B spt) = LN:A spt) /\
   (sptree_inter (LS (a:A)) t =
      spt_CASE t LN (\b. LS a) (\t1 t2. LN) (\t1 b t2. LS a)) /\
   (sptree_inter (BN t1 t2) t =
      spt_CASE t LN (\a. LN)
                 (\t1' t2'. mk_BN (sptree_inter t1 t1') (sptree_inter t2 t2'))
                 (\t1' a t2'. mk_BN (sptree_inter t1 t1') (sptree_inter t2 t2'))) /\
   (sptree_inter (BS t1 a t2) t =
      spt_CASE t LN (\a'. LS a)
                 (\t1' t2'. mk_BN (sptree_inter t1 t1') (sptree_inter t2 t2'))
                 (\t1' a' t2'. mk_BS (sptree_inter t1 t1') a (sptree_inter t2 t2')))`;;

let inter_eq_def = cake_def
  `(inter_eq LN t = LN:A spt) /\
   (inter_eq (LS (a:A)) t =
      spt_CASE t LN (\b. if a = b then LS a else LN) (\t1 t2. LN)
                 (\t1 b t2. if a = b then LS a else LN)) /\
   (inter_eq (BN t1 t2) t =
      spt_CASE t LN (\a. LN)
                 (\t1' t2'. mk_BN (inter_eq t1 t1') (inter_eq t2 t2'))
                 (\t1' a t2'. mk_BN (inter_eq t1 t1') (inter_eq t2 t2'))) /\
   (inter_eq (BS t1 a t2) t =
      spt_CASE t LN (\a'. if a' = a then LS a else LN)
                 (\t1' t2'. mk_BN (inter_eq t1 t1') (inter_eq t2 t2'))
                 (\t1' a' t2'.
                    if a' = a then mk_BS (inter_eq t1 t1') a (inter_eq t2 t2')
                    else mk_BN (inter_eq t1 t1') (inter_eq t2 t2')))`;;

let difference_def = cake_def
  `(difference LN (t:B spt) = LN:A spt) /\
   (difference (LS (a:A)) t =
      spt_CASE t (LS a) (\b. LN) (\t1 t2. LS a) (\t1 b t2. LN)) /\
   (difference (BN t1 t2) t =
      spt_CASE t (BN t1 t2) (\a. BN t1 t2)
                 (\t1' t2'. mk_BN (difference t1 t1') (difference t2 t2'))
                 (\t1' a t2'. mk_BN (difference t1 t1') (difference t2 t2'))) /\
   (difference (BS t1 a t2) t =
      spt_CASE t (BS t1 a t2) (\a'. BN t1 t2)
                 (\t1' t2'. mk_BS (difference t1 t1') a (difference t2 t2'))
                 (\t1' a' t2'. mk_BN (difference t1 t1') (difference t2 t2')))`;;

(* HOL4: wf_mk_BN, wf_mk_BS (local iff forms) *)

let SPTAUX_wf_mk_BN = prove
 (`!t1 t2:A spt. sptree_wf (mk_BN t1 t2) <=> sptree_wf t1 /\ sptree_wf t2`,
  REPEAT GEN_TAC THEN SPTAUX_CASES_TAC `t1:A spt` THEN
  SPTAUX_CASES_TAC `t2:A spt` THEN REWRITE_TAC[mk_BN_def; sptree_wf_def; spt_distinct]);;

let SPTAUX_wf_mk_BS = prove
 (`!t1 (x:A) t2. sptree_wf (mk_BS t1 x t2) <=> sptree_wf t1 /\ sptree_wf t2`,
  REPEAT GEN_TAC THEN SPTAUX_CASES_TAC `t1:A spt` THEN
  SPTAUX_CASES_TAC `t2:A spt` THEN REWRITE_TAC[mk_BS_def; sptree_wf_def; spt_distinct]);;

let wf_inter = prove
 (`!m1:A spt m2:B spt. sptree_wf (sptree_inter m1 m2)`,
  MATCH_MP_TAC spt_INDUCT THEN REPEAT STRIP_TAC THEN
  SPTAUX_CASES_TAC `m2:B spt` THEN
  ASM_REWRITE_TAC[sptree_inter_def; spt_CASE; sptree_wf_def; SPTAUX_wf_mk_BN;
                  SPTAUX_wf_mk_BS]);;

(* HOL4: lookup_mk_BN, lookup_mk_BS (local) *)

let SPTAUX_lookup_mk_BN = prove
 (`lookup k (mk_BN t1 t2) = lookup k (BN t1 t2:A spt)`,
  SPTAUX_CASES_TAC `t1:A spt` THEN SPTAUX_CASES_TAC `t2:A spt` THEN
  REWRITE_TAC[mk_BN_def; lookup_def] THEN COND_CASES_TAC THEN
  REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[lookup_def]);;

let SPTAUX_lookup_mk_BS = prove
 (`lookup k (mk_BS t1 x t2) = lookup k (BS t1 (x:A) t2)`,
  SPTAUX_CASES_TAC `t1:A spt` THEN SPTAUX_CASES_TAC `t2:A spt` THEN
  REWRITE_TAC[mk_BS_def; lookup_def] THEN COND_CASES_TAC THEN
  REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[lookup_def]);;

let SPTAUX_optcase_NONE = prove
 (`!x:A option. option_CASE x NONE (\v. NONE:B option) = NONE`,
  GEN_TAC THEN SPTAUX_CASES_TAC `x:A option` THEN REWRITE_TAC[option_CASE]);;

let lookup_inter = prove
 (`!m1:A spt m2:B spt k.
     lookup k (sptree_inter m1 m2) =
     option_CASE (lookup k m1) NONE
       (\v. option_CASE (lookup k m2) NONE (\w. SOME v))`,
  MATCH_MP_TAC spt_INDUCT THEN REPEAT STRIP_TAC THEN
  SPTAUX_CASES_TAC `m2:B spt` THEN SPTAUX_BITS_TAC `k:num` THEN
  ASM_REWRITE_TAC[sptree_inter_def; spt_CASE; lookup_rwts; SPTAUX_lookup_bits;
                  SPTAUX_lookup_mk_BN; SPTAUX_lookup_mk_BS; option_CASE;
                  SPTAUX_optcase_NONE]);;

let SPTAUX_lookup_cond = prove
 (`!k c (t1:A spt) t2. lookup k (if c then t1 else t2) =
                       if c then lookup k t1 else lookup k t2`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[]);;

let lookup_inter_eq = prove
 (`!m1 m2:A spt k.
     lookup k (inter_eq m1 m2) =
     option_CASE (lookup k m1) NONE
       (\v. if lookup k m2 = SOME v then SOME v else NONE)`,
  MATCH_MP_TAC spt_INDUCT THEN REPEAT STRIP_TAC THEN
  SPTAUX_CASES_TAC `m2:A spt` THEN SPTAUX_BITS_TAC `k:num` THEN
  ASM_REWRITE_TAC[inter_eq_def; spt_CASE; lookup_rwts; SPTAUX_lookup_bits;
                  SPTAUX_lookup_mk_BN; SPTAUX_lookup_mk_BS; option_CASE;
                  SPTAUX_optcase_NONE; option_DISTINCT; SPTAUX_lookup_cond;
                  option_INJ; COND_ID] THEN
  REPEAT COND_CASES_TAC THEN ASM_MESON_TAC[]);;

let lookup_inter_EQ = prove
 (`((lookup x (sptree_inter t1 t2) = SOME (y:A)) <=>
      (lookup x t1 = SOME y) /\ ~(lookup x (t2:B spt) = NONE)) /\
   ((lookup x (sptree_inter t1 t2) = NONE) <=>
      (lookup x t1 = NONE) \/ (lookup x t2 = NONE))`,
  REWRITE_TAC[lookup_inter] THEN
  SPTAUX_CASES_TAC `lookup x (t1:A spt)` THEN
  SPTAUX_CASES_TAC `lookup x (t2:B spt)` THEN
  REWRITE_TAC[option_CASE; option_DISTINCT; option_INJ]);;

let lookup_inter_assoc = prove
 (`lookup x (sptree_inter t1 (sptree_inter t2 t3)) =
   lookup x (sptree_inter (sptree_inter (t1:A spt) (t2:B spt)) (t3:C spt))`,
  REWRITE_TAC[lookup_inter] THEN
  SPTAUX_CASES_TAC `lookup x (t1:A spt)` THEN
  SPTAUX_CASES_TAC `lookup x (t2:B spt)` THEN
  SPTAUX_CASES_TAC `lookup x (t3:C spt)` THEN
  REWRITE_TAC[option_CASE]);;

let lookup_difference = prove
 (`!m1:A spt m2:B spt k.
     lookup k (difference m1 m2) =
     if lookup k m2 = NONE then lookup k m1 else NONE`,
  MATCH_MP_TAC spt_INDUCT THEN REPEAT STRIP_TAC THEN
  SPTAUX_CASES_TAC `m2:B spt` THEN SPTAUX_BITS_TAC `k:num` THEN
  ASM_REWRITE_TAC[difference_def; spt_CASE; lookup_rwts; SPTAUX_lookup_bits;
                  SPTAUX_lookup_mk_BN; SPTAUX_lookup_mk_BS; option_DISTINCT;
                  COND_ID]);;

(* ------------------------------------------------------------------------- *)
(* lrnext and domain                                                         *)
(* ------------------------------------------------------------------------- *)

let lrnext_def = cake_def_wf `MEASURE (I:num->num)`
  (REWRITE_TAC(I_THM::WF_REL_THMS) THEN REPEAT STRIP_TAC THEN ASM_ARITH_TAC)
  `lrnext n = if n = 0 then 1 else 2 * lrnext ((n - 1) DIV 2)`;;

(* HOL4: lrnext_thm (numeral forms, for EVAL) and lrnext_eq (via LOG) are   *)
(* not ported; SPTAUX_lrnext_bits gives lrnext at 0, 2m+1, 2m+2.            *)

let domain_def = cake_def
  `(domain (LN:A spt) = {}) /\
   (domain (LS (a:A)) = {0}) /\
   (domain (BN t1 t2) =
      IMAGE (\n. 2 * n + 2) (domain t1) UNION
      IMAGE (\n. 2 * n + 1) (domain t2)) /\
   (domain (BS t1 a t2) =
      ({0} UNION IMAGE (\n. 2 * n + 2) (domain t1)) UNION
      IMAGE (\n. 2 * n + 1) (domain t2))`;;

let SPTAUX_domain_bits = prove
 (`(0 IN domain (LN:A spt) <=> F) /\
   (!a:A. 0 IN domain (LS a) <=> T) /\
   (!t1 t2:A spt. 0 IN domain (BN t1 t2) <=> F) /\
   (!t1 (a:A) t2. 0 IN domain (BS t1 a t2) <=> T) /\
   (!m. (2 * m + 1) IN domain (LN:A spt) <=> F) /\
   (!m (a:A). (2 * m + 1) IN domain (LS a) <=> F) /\
   (!m t1 t2:A spt. (2 * m + 1) IN domain (BN t1 t2) <=> m IN domain t2) /\
   (!m t1 (a:A) t2. (2 * m + 1) IN domain (BS t1 a t2) <=> m IN domain t2) /\
   (!m. (2 * m + 2) IN domain (LN:A spt) <=> F) /\
   (!m (a:A). (2 * m + 2) IN domain (LS a) <=> F) /\
   (!m t1 t2:A spt. (2 * m + 2) IN domain (BN t1 t2) <=> m IN domain t1) /\
   (!m t1 (a:A) t2. (2 * m + 2) IN domain (BS t1 a t2) <=> m IN domain t1)`,
  REWRITE_TAC[domain_def; IN_UNION; IN_IMAGE; IN_INSERT; NOT_IN_EMPTY] THEN
  REWRITE_TAC[SPTAUX_BIT_RW; UNWIND_THM1; UNWIND_THM2] THEN
  REWRITE_TAC[ARITH_RULE `2 * m + 1 = 2 * x + 1 <=> x = m`;
              ARITH_RULE `2 * m + 2 = 2 * x + 2 <=> x = m`;
              UNWIND_THM2]);;

(* Enumerate keys directly, without constructing key/value pairs. *)

let domain_list_def = cake_def
  `(domain_list (LN:A spt) = []) /\
   (domain_list (LS (a:A)) = [0]) /\
   (domain_list (BN t1 t2) =
      APPEND (MAP (\n. 2 * n + 2) (domain_list t1))
             (MAP (\n. 2 * n + 1) (domain_list t2))) /\
   (domain_list (BS t1 v t2) =
      CONS 0 (APPEND (MAP (\n. 2 * n + 2) (domain_list t1))
                     (MAP (\n. 2 * n + 1) (domain_list t2))))`;;

let set_domain_list = prove
 (`set_of_list (domain_list t) = domain (t:A spt)`,
  SPEC_TAC(`t:A spt`,`t:A spt`) THEN MATCH_MP_TAC spt_INDUCT THEN
  ASM_REWRITE_TAC[domain_list_def; domain_def; set_of_list; SET_OF_LIST_APPEND;
                  SET_OF_LIST_MAP] THEN
  SET_TAC[]);;

let FINITE_domain = prove
 (`FINITE (domain (t:A spt))`,
  SPEC_TAC(`t:A spt`,`t:A spt`) THEN MATCH_MP_TAC spt_INDUCT THEN
  ASM_SIMP_TAC[domain_def; FINITE_UNION; FINITE_IMAGE; FINITE_INSERT;
               FINITE_EMPTY]);;

let IN_domain = prove
 (`!n (x:A) t1 t2.
     (n IN domain (LN:A spt) <=> F) /\
     (n IN domain (LS x) <=> (n = 0)) /\
     (n IN domain (BN t1 t2) <=>
        ~(n = 0) /\ (if EVEN n then ((n - 1) DIV 2) IN domain t1
                     else ((n - 1) DIV 2) IN domain t2)) /\
     (n IN domain (BS t1 x t2) <=>
        (n = 0) \/ (if EVEN n then ((n - 1) DIV 2) IN domain t1
                    else ((n - 1) DIV 2) IN domain t2))`,
  REPEAT GEN_TAC THEN SPTAUX_BITS_TAC `n:num` THEN
  REWRITE_TAC[SPTAUX_domain_bits; SPTAUX_BIT_RW]);;

let size_insert = prove
 (`!k (v:A) m. sptree_size (insert k v m) =
               if k IN domain m then sptree_size m else sptree_size m + 1`,
  MATCH_MP_TAC SPTAUX_bit_induction THEN REPEAT STRIP_TAC THEN
  SPTAUX_CASES_TAC `m:A spt` THEN
  ASM_REWRITE_TAC[SPTAUX_insert_bits; sptree_size_def; SPTAUX_domain_bits;
                  CONJUNCT1 domain_def; NOT_IN_EMPTY] THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let SPTAUX_lookup_fromList_gen = prove
 (`!l:A list i n t.
     lookup n (SND (FOLDL (\(i,t) a. (i + 1,insert i a t)) (i,t) l)) =
     if n < i then lookup n t
     else if n < LENGTH l + i then SOME (EL (n - i) l)
     else lookup n t`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[FOLDL; LENGTH; ADD_CLAUSES] THENL
   [REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[lookup_insert] THEN REPEAT GEN_TAC THEN
  ASM_CASES_TAC `n:num < i` THENL
   [ASM_SIMP_TAC[ARITH_RULE `n < i ==> n < i + 1 /\ ~(n = i)`]; ALL_TAC] THEN
  ASM_CASES_TAC `n:num = i` THENL
   [ASM_REWRITE_TAC[ARITH_RULE `i < i + 1 /\ i < SUC (m + i) /\ i - i = 0`;
                    EL; HD];
    ALL_TAC] THEN
  ASM_SIMP_TAC[ARITH_RULE `~(n < i) /\ ~(n = i) ==> ~(n < i + 1)`;
               ARITH_RULE `n < SUC (m + i) <=> n < m + i + 1`] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `n - i = SUC (n - (i + 1))` SUBST1_TAC THENL
   [ASM_ARITH_TAC; REWRITE_TAC[EL; TL]]);;

let lookup_fromList = prove
 (`lookup n (fromList l) =
   if n < LENGTH l then SOME (EL n (l:A list)) else NONE`,
  REWRITE_TAC[fromList_def; SPTAUX_lookup_fromList_gen; ADD_CLAUSES; LT;
              SUB_0; lookup_rwts]);;

let domain_lookup = prove
 (`!t:A spt k. k IN domain t <=> ?v. lookup k t = SOME v`,
  MATCH_MP_TAC spt_INDUCT THEN REPEAT STRIP_TAC THEN
  SPTAUX_BITS_TAC `k:num` THEN
  ASM_REWRITE_TAC[SPTAUX_domain_bits; lookup_rwts; SPTAUX_lookup_bits;
                  option_DISTINCT; option_INJ] THEN
  MESON_TAC[]);;
let lookup_inter_alt = prove
 (`lookup x (sptree_inter t1 t2) =
   if x IN domain (t2:B spt) then lookup x (t1:A spt) else NONE`,
  REWRITE_TAC[lookup_inter; domain_lookup] THEN
  SPTAUX_CASES_TAC `lookup x (t2:B spt)` THEN
  SPTAUX_CASES_TAC `lookup x (t1:A spt)` THEN
  REWRITE_TAC[option_CASE; option_DISTINCT; option_INJ] THEN MESON_TAC[]);;

let lookup_NONE_domain = prove
 (`(lookup k t = NONE) <=> ~(k IN domain (t:A spt))`,
  REWRITE_TAC[domain_lookup] THEN SPTAUX_CASES_TAC `lookup k (t:A spt)` THEN
  REWRITE_TAC[option_DISTINCT; option_INJ] THEN MESON_TAC[]);;

let domain_union = prove
 (`domain (sptree_union t1 t2) = domain t1 UNION domain (t2:A spt)`,
  REWRITE_TAC[EXTENSION; domain_lookup; lookup_union; IN_UNION] THEN
  X_GEN_TAC `k:num` THEN SPTAUX_CASES_TAC `lookup k (t1:A spt)` THEN
  REWRITE_TAC[option_CASE; option_DISTINCT; option_INJ] THEN MESON_TAC[]);;

let domain_inter = prove
 (`domain (sptree_inter t1 t2) = domain (t1:A spt) INTER domain (t2:B spt)`,
  REWRITE_TAC[EXTENSION; domain_lookup; lookup_inter; IN_INTER] THEN
  X_GEN_TAC `k:num` THEN SPTAUX_CASES_TAC `lookup k (t1:A spt)` THEN
  SPTAUX_CASES_TAC `lookup k (t2:B spt)` THEN
  REWRITE_TAC[option_CASE; option_DISTINCT; option_INJ] THEN MESON_TAC[]);;

let domain_insert = prove
 (`domain (insert k (v:A) t) = k INSERT domain t`,
  REWRITE_TAC[EXTENSION; domain_lookup; lookup_insert; IN_INSERT] THEN
  MESON_TAC[]);;

let domain_difference = prove
 (`!t1 t2. domain (difference t1 t2) =
           domain (t1:A spt) DIFF domain (t2:B spt)`,
  REWRITE_TAC[EXTENSION; domain_lookup; lookup_difference; IN_DIFF] THEN
  REPEAT GEN_TAC THEN SPTAUX_CASES_TAC `lookup x (t2:B spt)` THEN
  REWRITE_TAC[option_DISTINCT; option_INJ] THEN MESON_TAC[]);;

let domain_sing = prove
 (`domain (insert k (v:A) LN) = {k}`,
  REWRITE_TAC[domain_insert; domain_def]);;

let domain_fromList = prove
 (`domain (fromList l) = pred_set_count (LENGTH (l:A list))`,
  REWRITE_TAC[EXTENSION; domain_lookup; lookup_fromList; pred_set_count_DEF;
              IN_ELIM_THM] THEN
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT] THEN
  MESON_TAC[]);;
let SPTAUX_card_images = prove
 (`!s t. FINITE s /\ FINITE t
         ==> CARD (IMAGE (\n. 2 * n + 2) s UNION IMAGE (\n. 2 * n + 1) t) =
             CARD s + CARD t /\
             CARD (({0} UNION IMAGE (\n. 2 * n + 2) s) UNION
                   IMAGE (\n. 2 * n + 1) t) =
             CARD s + CARD t + 1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `CARD (IMAGE (\n. 2 * n + 2) s) = CARD (s:num->bool) /\
                CARD (IMAGE (\n. 2 * n + 1) t) = CARD (t:num->bool)`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_REWRITE_TAC[] THEN
    ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (\n. 2 * n + 2) s INTER IMAGE (\n. 2 * n + 1) t = {} /\
                ({0} UNION IMAGE (\n. 2 * n + 2) s) INTER
                IMAGE (\n. 2 * n + 1) t = {} /\
                {0} INTER IMAGE (\n. 2 * n + 2) s = {}`
    STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; IN_UNION; IN_IMAGE; IN_INSERT;
                NOT_IN_EMPTY] THEN
    MESON_TAC[SPTAUX_BIT_RW]; ALL_TAC] THEN
  ASM_SIMP_TAC[CARD_UNION; FINITE_UNION; FINITE_IMAGE; FINITE_INSERT;
               FINITE_EMPTY; CARD_SING] THEN
  ARITH_TAC);;

let size_domain = prove
 (`!t:A spt. sptree_size t = CARD (domain t)`,
  MATCH_MP_TAC spt_INDUCT THEN
  ASM_SIMP_TAC[sptree_size_def; domain_def; SPTAUX_card_images; FINITE_domain;
               CARD_CLAUSES; CARD_SING] THEN ARITH_TAC);;

let lookup_delete = prove
 (`!t:A spt k1 k2.
     lookup k1 (delete k2 t) = if k1 = k2 then NONE else lookup k1 t`,
  MATCH_MP_TAC spt_INDUCT THEN REPEAT STRIP_TAC THEN
  SPTAUX_BITS_TAC `k1:num` THEN SPTAUX_BITS_TAC `k2:num` THEN
  ASM_REWRITE_TAC[delete_def; SPTAUX_BIT_RW; lookup_rwts; SPTAUX_lookup_bits;
                  SPTAUX_lookup_mk_BN; SPTAUX_lookup_mk_BS; COND_ID]);;

let domain_delete = prove
 (`domain (delete k (t:A spt)) = domain t DELETE k`,
  REWRITE_TAC[EXTENSION; domain_lookup; lookup_delete; IN_DELETE] THEN
  MESON_TAC[option_DISTINCT]);;

(* ------------------------------------------------------------------------- *)
(* foldi, spt_acc, mapi                                                      *)
(* ------------------------------------------------------------------------- *)

let SPTAUX_lrnext_bits = prove
 (`lrnext 0 = 1 /\ lrnext 1 = 2 /\ lrnext 2 = 2 /\
   (!m. lrnext (2 * m + 1) = 2 * lrnext m) /\
   (!m. lrnext (2 * m + 2) = 2 * lrnext m)`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [lrnext_def] THEN
  REWRITE_TAC[SPTAUX_BIT_RW] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ONCE_REWRITE_TAC[lrnext_def] THEN CONV_TAC NUM_REDUCE_CONV);;

(* HOL4: lrlemma1, lrlemma2 (local) *)

let SPTAUX_lrlemma1 = prove
 (`!i. lrnext (i + lrnext i) = 2 * lrnext i`,
  MATCH_MP_TAC SPTAUX_bit_induction THEN
  REWRITE_TAC[SPTAUX_lrnext_bits; ADD_CLAUSES; ARITH] THEN
  REWRITE_TAC[ARITH_RULE `(2 * m + 1) + 2 * x = 2 * (m + x) + 1 /\
                          (2 * m + 2) + 2 * x = 2 * (m + x) + 2`] THEN
  SIMP_TAC[SPTAUX_lrnext_bits]);;

let SPTAUX_lrlemma2 = prove
 (`!i. lrnext (i + 2 * lrnext i) = 2 * lrnext i`,
  MATCH_MP_TAC SPTAUX_bit_induction THEN
  REWRITE_TAC[SPTAUX_lrnext_bits; ADD_CLAUSES; ARITH] THEN
  REWRITE_TAC[ARITH_RULE `(2 * m + 1) + 2 * 2 * x = 2 * (m + 2 * x) + 1 /\
                          (2 * m + 2) + 2 * 2 * x = 2 * (m + 2 * x) + 2`] THEN
  SIMP_TAC[SPTAUX_lrnext_bits]);;

let SPTAUX_lrnext_pos = prove
 (`!i. ~(lrnext i = 0)`,
  MATCH_MP_TAC SPTAUX_bit_induction THEN
  ASM_REWRITE_TAC[SPTAUX_lrnext_bits; MULT_EQ_0; ARITH]);;

let foldi_def = cake_def
  `(foldi (f:num->A->B->B) i acc LN = acc) /\
   (foldi f i acc (LS a) = f i a acc) /\
   (foldi f i acc (BN t1 t2) =
      let inc = lrnext i in
      foldi f (i + inc) (foldi f (i + 2 * inc) acc t1) t2) /\
   (foldi f i acc (BS t1 a t2) =
      let inc = lrnext i in
      foldi f (i + inc) (f i a (foldi f (i + 2 * inc) acc t1)) t2)`;;

let spt_acc_def = cake_def_wf `MEASURE (SND:num#num->num)` SPTAUX_TC_TAC
  `(spt_acc i 0 = i) /\
   (spt_acc i (SUC k) =
      spt_acc (i + if EVEN (SUC k) then 2 * lrnext i else lrnext i) (k DIV 2))`;;

let spt_acc_thm = prove
 (`spt_acc i k =
   if k = 0 then i
   else spt_acc (i + if EVEN k then 2 * lrnext i else lrnext i) ((k - 1) DIV 2)`,
  SPTAUX_CASES_TAC `k:num` THEN REWRITE_TAC[spt_acc_def; NOT_SUC; SUC_SUB1]);;

let spt_acc_eqn = prove
 (`!k i. spt_acc i k = lrnext i * k + i`,
  MATCH_MP_TAC SPTAUX_bit_induction THEN
  CONJ_TAC THENL [REWRITE_TAC[spt_acc_def] THEN ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN GEN_TAC THEN
  ONCE_REWRITE_TAC[spt_acc_thm] THEN
  ASM_REWRITE_TAC[SPTAUX_BIT_RW; SPTAUX_lrlemma1; SPTAUX_lrlemma2] THEN
  ARITH_TAC);;

let spt_acc_0 = prove
 (`!k. spt_acc 0 k = k`,
  REWRITE_TAC[spt_acc_eqn; SPTAUX_lrnext_bits] THEN ARITH_TAC);;

let SPTAUX_foldi_thm = REWRITE_RULE[LET_DEF; LET_END_DEF] foldi_def;;

let SPTAUX_EXISTS_BITS = prove
 (`!P. (?n. P n) <=> P 0 \/ (?m. P (2 * m + 1)) \/ (?m. P (2 * m + 2))`,
  GEN_TAC THEN EQ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` MP_TAC) THEN
  REPEAT_TCL STRIP_THM_THEN SUBST1_TAC (SPEC `n:num` SPTAUX_bit_cases) THEN
  MESON_TAC[]);;

let SPTAUX_OFFSET_RW = prove
 (`(!i c. i + c * 0 = i) /\
   (!i c m. i + c * (2 * m + 1) = (i + c) + (2 * c) * m) /\
   (!i c m. i + c * (2 * m + 2) = (i + 2 * c) + (2 * c) * m)`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN CONV_TAC NUM_RING);;

let SPTAUX_offset_lookup = prove
 (`(!i c k (v:A). (?n. k = i + c * n /\ lookup n (LN:A spt) = SOME v) <=> F) /\
   (!i c k (v:A) a.
      (?n. k = i + c * n /\ lookup n (LS a) = SOME v) <=> k = i /\ a = v) /\
   (!i c k (v:A) t1 t2.
      (?n. k = i + c * n /\ lookup n (BN t1 t2) = SOME v) <=>
      (?n. k = (i + 2 * c) + (2 * c) * n /\ lookup n t1 = SOME v) \/
      (?n. k = (i + c) + (2 * c) * n /\ lookup n t2 = SOME v)) /\
   (!i c k (v:A) a t1 t2.
      (?n. k = i + c * n /\ lookup n (BS t1 a t2) = SOME v) <=>
      (k = i /\ a = v) \/
      (?n. k = (i + 2 * c) + (2 * c) * n /\ lookup n t1 = SOME v) \/
      (?n. k = (i + c) + (2 * c) * n /\ lookup n t2 = SOME v))`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [SPTAUX_EXISTS_BITS] THEN
  REWRITE_TAC[lookup_rwts; SPTAUX_lookup_bits; SPTAUX_OFFSET_RW;
              option_DISTINCT; option_INJ] THEN
  MESON_TAC[]);;

let SPTAUX_offset_domain = prove
 (`(!i c. IMAGE (\n. i + c * n) (domain (LN:A spt)) = {}) /\
   (!i c a:A. IMAGE (\n. i + c * n) (domain (LS a)) = {i}) /\
   (!i c t1 t2:A spt.
      IMAGE (\n. i + c * n) (domain (BN t1 t2)) =
      IMAGE (\n. (i + 2 * c) + (2 * c) * n) (domain t1) UNION
      IMAGE (\n. (i + c) + (2 * c) * n) (domain t2)) /\
   (!i c (a:A) t1 t2.
      IMAGE (\n. i + c * n) (domain (BS t1 a t2)) =
      (i INSERT IMAGE (\n. (i + 2 * c) + (2 * c) * n) (domain t1)) UNION
      IMAGE (\n. (i + c) + (2 * c) * n) (domain t2))`,
  REWRITE_TAC[CONJUNCT1 domain_def; IMAGE_CLAUSES] THEN CONJ_TAC THENL
   [REWRITE_TAC[domain_def; IMAGE_CLAUSES; SPTAUX_OFFSET_RW]; ALL_TAC] THEN
  CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNION; IN_INSERT] THEN
  X_GEN_TAC `k:num` THEN
  GEN_REWRITE_TAC LAND_CONV [SPTAUX_EXISTS_BITS] THEN
  REWRITE_TAC[SPTAUX_domain_bits; SPTAUX_OFFSET_RW] THEN
  MESON_TAC[]);;

let SPTAUX_UNION_RW = prove
 (`(!a s1 s2:num->bool. (a UNION s1) UNION s2 = a UNION (s1 UNION s2)) /\
   (!i a s1 s2:num->bool.
      (i INSERT (a UNION s1)) UNION s2 = a UNION ((i INSERT s1) UNION s2)) /\
   (!i a:num->bool. a UNION {i} = i INSERT a)`,
  SET_TAC[]);;

let set_foldi_keys = prove
 (`!t:A spt a i. foldi (\k v a. k INSERT a) i a t =
                 a UNION IMAGE (\n. i + lrnext i * n) (domain t)`,
  MATCH_MP_TAC spt_INDUCT THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[SPTAUX_foldi_thm; SPTAUX_offset_domain; SPTAUX_lrlemma1;
                  SPTAUX_lrlemma2; UNION_EMPTY; SPTAUX_UNION_RW]);;

let domain_foldi = prove
 (`domain t = foldi (\k (v:A) a. k INSERT a) 0 {} t`,
  REWRITE_TAC[set_foldi_keys; UNION_EMPTY; SPTAUX_lrnext_bits; ADD_CLAUSES;
              MULT_CLAUSES; IMAGE_ID]);;

let mapi0_def = cake_def
  `(mapi0 (f:num->A->B) i LN = LN) /\
   (mapi0 f i (LS a) = LS (f i a)) /\
   (mapi0 f i (BN t1 t2) =
      let inc = lrnext i in
      mk_BN (mapi0 f (i + 2 * inc) t1) (mapi0 f (i + inc) t2)) /\
   (mapi0 f i (BS t1 a t2) =
      let inc = lrnext i in
      mk_BS (mapi0 f (i + 2 * inc) t1) (f i a) (mapi0 f (i + inc) t2))`;;

let mapi_def = new_definition
  `mapi (f:num->A->B) pt = mapi0 f 0 pt`;;

let SPTAUX_ACC_RW = prove
 (`(!c i. c * 0 + i = i) /\
   (!c i m. c * (2 * m + 1) + i = (2 * c) * m + (i + c)) /\
   (!c i m. c * (2 * m + 2) + i = (2 * c) * m + (i + 2 * c))`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN CONV_TAC NUM_RING);;

let lookup_mapi0 = prove
 (`!pt:A spt i k.
     lookup k (mapi0 (f:num->A->B) i pt) =
     option_CASE (lookup k pt) NONE (\v. SOME (f (spt_acc i k) v))`,
  MATCH_MP_TAC spt_INDUCT THEN REPEAT STRIP_TAC THEN
  SPTAUX_BITS_TAC `k:num` THEN
  ASM_REWRITE_TAC[mapi0_def; LET_DEF; LET_END_DEF; lookup_rwts;
                  SPTAUX_lookup_bits; SPTAUX_lookup_mk_BN; SPTAUX_lookup_mk_BS;
                  option_CASE; spt_acc_eqn; SPTAUX_lrlemma1; SPTAUX_lrlemma2;
                  SPTAUX_ACC_RW]);;

let lookup_mapi = prove
 (`lookup k (mapi (f:num->A->B) pt) = OPTION_MAP (f k) (lookup k pt)`,
  REWRITE_TAC[mapi_def; lookup_mapi0; spt_acc_0] THEN
  SPTAUX_CASES_TAC `lookup k (pt:A spt)` THEN
  REWRITE_TAC[option_CASE; OPTION_MAP_DEF]);;

(* ------------------------------------------------------------------------- *)
(* toAList                                                                   *)
(* ------------------------------------------------------------------------- *)

let toAList_def = new_definition
  `(toAList:A spt->(num#A)list) = foldi (\k v a. CONS (k,v) a) 0 []`;;

(* HOL4: set_toAList_lemma (local) *)

let SPTAUX_MEM_foldi = prove
 (`!t:A spt i acc k v.
     MEM (k,v) (foldi (\k v a. CONS (k,v) a) i acc t) <=>
     MEM (k,v) acc \/ ?n. k = i + lrnext i * n /\ lookup n t = SOME v`,
  MATCH_MP_TAC spt_INDUCT THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[SPTAUX_foldi_thm; MEM; SPTAUX_offset_lookup; SPTAUX_lrlemma1;
                  SPTAUX_lrlemma2; PAIR_EQ] THEN
  MESON_TAC[]);;

let MEM_toAList = prove
 (`!t:A spt k v. MEM (k,v) (toAList t) <=> (lookup k t = SOME v)`,
  REWRITE_TAC[toAList_def; SPTAUX_MEM_foldi; MEM; SPTAUX_lrnext_bits;
              ADD_CLAUSES; MULT_CLAUSES; UNWIND_THM1; UNWIND_THM2]);;

(* alist lemmas (alist unit), proved here for local use *)

let SPTAUX_ALOOKUP_MEM = prove
 (`!l:(A#B)list k v. ALOOKUP l k = SOME v ==> MEM (k,v) l`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALOOKUP_DEF; MEM; option_DISTINCT] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[option_INJ] THENL
   [ASM_MESON_TAC[PAIR]; ASM_MESON_TAC[]]);;

let SPTAUX_ALOOKUP_FAILS = prove
 (`!l:(A#B)list x. ALOOKUP l x = NONE <=> !y. ~MEM (x,y) l`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALOOKUP_DEF; MEM] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT] THENL
   [ASM_MESON_TAC[PAIR]; ALL_TAC] THEN
  EQ_TAC THEN REPEAT STRIP_TAC THEN ASM_MESON_TAC[FST]);;

let ALOOKUP_toAList = prove
 (`!t:A spt x. ALOOKUP (toAList t) x = lookup x t`,
  REPEAT GEN_TAC THEN SPTAUX_CASES_TAC `lookup x (t:A spt)` THENL
   [ASM_REWRITE_TAC[SPTAUX_ALOOKUP_FAILS; MEM_toAList; option_DISTINCT];
    ALL_TAC] THEN
  SPTAUX_CASES_TAC `ALOOKUP (toAList (t:A spt)) x` THENL
   [ASM_MESON_TAC[SPTAUX_ALOOKUP_FAILS; MEM_toAList];
    ASM_MESON_TAC[SPTAUX_ALOOKUP_MEM; MEM_toAList]]);;

let insert_union = prove
 (`!k (v:A) s. insert k v s = sptree_union (insert k v LN) s`,
  MATCH_MP_TAC SPTAUX_bit_induction THEN REPEAT STRIP_TAC THEN
  TRY (FIRST_X_ASSUM (ASSUME_TAC o GSYM)) THEN
  SPTAUX_CASES_TAC `s:A spt` THEN
  ASM_REWRITE_TAC[SPTAUX_insert_bits; sptree_union_def; spt_CASE]);;

let domain_empty = prove
 (`!t:A spt. sptree_wf t ==> ((t = LN) <=> (domain t = EMPTY))`,
  MATCH_MP_TAC spt_INDUCT THEN
  REWRITE_TAC[sptree_wf_def; domain_def; spt_distinct; NOT_INSERT_EMPTY;
              EMPTY_UNION; IMAGE_EQ_EMPTY] THEN
  MESON_TAC[]);;

(* HOL4 derives LENGTH_toAList from ALL_DISTINCT_MAP_FST_toAList; here the  *)
(* length comes first and the distinctness follows by counting.             *)

let SPTAUX_LENGTH_foldi = prove
 (`!t:A spt i acc.
     LENGTH (foldi (\k v a. CONS (k,v) a) i acc t) = sptree_size t + LENGTH acc`,
  MATCH_MP_TAC spt_INDUCT THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[SPTAUX_foldi_thm; sptree_size_def; LENGTH] THEN ARITH_TAC);;

let LENGTH_toAList = prove
 (`LENGTH (toAList t) = sptree_size (t:A spt)`,
  REWRITE_TAC[toAList_def; SPTAUX_LENGTH_foldi; LENGTH; ADD_CLAUSES]);;

(* list lemma (list unit), proved here for local use *)

let SPTAUX_ALL_DISTINCT_CARD = prove
 (`!l:A list. ALL_DISTINCT l <=> CARD (set_of_list l) = LENGTH l`,
  LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC[ALL_DISTINCT; set_of_list; LENGTH; CARD_CLAUSES;
               FINITE_SET_OF_LIST; IN_SET_OF_LIST] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[SUC_INJ] THEN
  MP_TAC(ISPEC `t:A list` CARD_SET_OF_LIST_LE) THEN ARITH_TAC);;

let set_MAP_FST_toAList_domain = prove
 (`set_of_list (MAP FST (toAList t)) = domain (t:A spt)`,
  REWRITE_TAC[EXTENSION; IN_SET_OF_LIST; MEM_MAP; EXISTS_PAIR_THM;
              MEM_toAList; domain_lookup] THEN
  MESON_TAC[FST]);;

let ALL_DISTINCT_MAP_FST_toAList = prove
 (`!t:A spt. ALL_DISTINCT (MAP FST (toAList t))`,
  REWRITE_TAC[SPTAUX_ALL_DISTINCT_CARD; set_MAP_FST_toAList_domain;
              LENGTH_MAP; LENGTH_toAList; size_domain]);;

(* HOL4: foldi_FOLDR_toAList_lemma (local) *)

let SPTAUX_ITLIST_UNCURRY = prove
 (`!(f:num->A->B->B) n v X a.
     f n v (ITLIST (UNCURRY f) X a) = ITLIST (UNCURRY f) (CONS (n,v) X) a`,
  REWRITE_TAC[ITLIST; UNCURRY_DEF]);;

let SPTAUX_foldi_FOLDR_toAList_lemma = prove
 (`!t:A spt n (a:B) ls.
     foldi f n (ITLIST (UNCURRY f) ls a) t =
     ITLIST (UNCURRY f) (foldi (\k v a. CONS (k,v) a) n ls t) a`,
  MATCH_MP_TAC spt_INDUCT THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[SPTAUX_foldi_thm; SPTAUX_ITLIST_UNCURRY]);;

let foldi_FOLDR_toAList = prove
 (`!f (a:B) t:A spt. foldi f 0 a t = ITLIST (UNCURRY f) (toAList t) a`,
  REWRITE_TAC[toAList_def; GSYM SPTAUX_foldi_FOLDR_toAList_lemma; ITLIST]);;

let toListA_def = cake_def
  `(toListA acc (LN:A spt) = acc) /\
   (toListA acc (LS (a:A)) = CONS a acc) /\
   (toListA acc (BN t1 t2) = toListA (toListA acc t2) t1) /\
   (toListA acc (BS t1 a t2) = toListA (CONS a (toListA acc t2)) t1)`;;

let SPTAUX_toListA_APPEND = prove
 (`!t:A spt acc acc'.
     toListA (APPEND acc acc') t = APPEND (toListA acc t) acc'`,
  MATCH_MP_TAC spt_INDUCT THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[toListA_def; APPEND] THEN
  ASM_REWRITE_TAC[GSYM(CONJUNCT2 APPEND)]);;

let toListA_append = prove
 (`!t:A spt acc. toListA acc t = APPEND (toListA [] t) acc`,
  REWRITE_TAC[GSYM SPTAUX_toListA_APPEND; APPEND]);;

let SPTAUX_LENGTH_toListA = prove
 (`!t:A spt acc. LENGTH (toListA acc t) = sptree_size t + LENGTH acc`,
  MATCH_MP_TAC spt_INDUCT THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[toListA_def; sptree_size_def; LENGTH] THEN ARITH_TAC);;

(* HOL4: size_zero_empty (later in the HOL4 script) *)

let size_zero_empty = prove
 (`!x:A spt. sptree_size x = 0 <=> domain x = EMPTY`,
  MATCH_MP_TAC spt_INDUCT THEN
  ASM_REWRITE_TAC[sptree_size_def; domain_def; ADD_EQ_0; ARITH;
                  NOT_INSERT_EMPTY; EMPTY_UNION; IMAGE_EQ_EMPTY] THEN
  MESON_TAC[]);;

let isEmpty_toListA = prove
 (`!t:A spt acc. sptree_wf t ==> ((t = LN) <=> (toListA acc t = acc))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[toListA_def]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o AP_TERM `LENGTH:A list->num`) THEN
  REWRITE_TAC[SPTAUX_LENGTH_toListA; ARITH_RULE `a + b = b <=> a = 0`] THEN
  ASM_SIMP_TAC[size_zero_empty; domain_empty]);;

let toList_def = new_definition
  `toList (m:A spt) = toListA [] m`;;

let isEmpty_toList = prove
 (`!t:A spt. sptree_wf t ==> ((t = LN) <=> (toList t = []))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[toList_def] THEN
  MATCH_MP_TAC isEmpty_toListA THEN ASM_REWRITE_TAC[]);;

let SPTAUX_EXISTS_lookup = prove
 (`(!x:A. (?k. lookup k (LN:A spt) = SOME x) <=> F) /\
   (!(x:A) a. (?k. lookup k (LS a) = SOME x) <=> a = x) /\
   (!(x:A) t1 t2. (?k. lookup k (BN t1 t2) = SOME x) <=>
                  (?k. lookup k t1 = SOME x) \/ (?k. lookup k t2 = SOME x)) /\
   (!(x:A) a t1 t2. (?k. lookup k (BS t1 a t2) = SOME x) <=>
                  a = x \/ (?k. lookup k t1 = SOME x) \/
                  (?k. lookup k t2 = SOME x))`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [SPTAUX_EXISTS_BITS] THEN
  REWRITE_TAC[lookup_rwts; SPTAUX_lookup_bits; option_DISTINCT; option_INJ] THEN
  MESON_TAC[]);;

(* HOL4: MEM_toListA (local) *)

let SPTAUX_MEM_toListA = prove
 (`!t:A spt acc x. MEM x (toListA acc t) <=>
                   (MEM x acc \/ ?k. lookup k t = SOME x)`,
  MATCH_MP_TAC spt_INDUCT THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[toListA_def; MEM; SPTAUX_EXISTS_lookup] THEN
  MESON_TAC[]);;

let MEM_toList = prove
 (`!x (t:A spt). MEM x (toList t) <=> ?k. lookup k t = SOME x`,
  REWRITE_TAC[toList_def; SPTAUX_MEM_toListA; MEM]);;

(* ------------------------------------------------------------------------- *)
(* Extensionality                                                            *)
(* ------------------------------------------------------------------------- *)

let SPTAUX_FORALL_BITS = prove
 (`!P. (!n. P n) <=> P 0 /\ (!m. P (2 * m + 1)) /\ (!m. P (2 * m + 2))`,
  GEN_TAC THEN EQ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN X_GEN_TAC `n:num` THEN
  REPEAT_TCL STRIP_THM_THEN SUBST1_TAC (SPEC `n:num` SPTAUX_bit_cases) THEN
  ASM_REWRITE_TAC[]);;

let SPTAUX_lookup_NONE_LN = prove
 (`!t:A spt. sptree_wf t ==> (((!n. lookup n t = NONE) <=> t = LN) /\
                      ((!n. NONE = lookup n t) <=> t = LN))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[domain_empty] THEN
  REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; GSYM lookup_NONE_domain] THEN
  MESON_TAC[]);;

let spt_eq_thm = prove
 (`!t1 t2:A spt. sptree_wf t1 /\ sptree_wf t2 ==>
                 ((t1 = t2) <=> !n. lookup n t1 = lookup n t2)`,
  MATCH_MP_TAC spt_INDUCT THEN REPEAT STRIP_TAC THEN
  SPTAUX_CASES_TAC `t2:A spt` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[sptree_wf_def]) THEN
  REWRITE_TAC[spt_distinct; spt_inject] THEN
  ONCE_REWRITE_TAC[SPTAUX_FORALL_BITS] THEN
  REWRITE_TAC[lookup_rwts; SPTAUX_lookup_bits; option_DISTINCT; option_INJ] THEN
  ASM_SIMP_TAC[SPTAUX_lookup_NONE_LN] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* mk_wf                                                                     *)
(* ------------------------------------------------------------------------- *)

let mk_wf_def = cake_def
  `(mk_wf (LN:A spt) = LN) /\
   (mk_wf (LS (x:A)) = LS x) /\
   (mk_wf (BN t1 t2) = mk_BN (mk_wf t1) (mk_wf t2)) /\
   (mk_wf (BS t1 x t2) = mk_BS (mk_wf t1) x (mk_wf t2))`;;

let wf_mk_wf = prove
 (`!t:A spt. sptree_wf (mk_wf t)`,
  MATCH_MP_TAC spt_INDUCT THEN
  ASM_SIMP_TAC[sptree_wf_def; mk_wf_def; SPTAUX_wf_mk_BS; SPTAUX_wf_mk_BN]);;

let wf_mk_id = prove
 (`!t:A spt. sptree_wf t ==> (mk_wf t = t)`,
  MATCH_MP_TAC spt_INDUCT THEN REWRITE_TAC[sptree_wf_def; mk_wf_def] THEN
  SIMP_TAC[mk_BS_thm; mk_BN_thm]);;

let lookup_mk_wf = prove
 (`!x t:A spt. lookup x (mk_wf t) = lookup x t`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  MATCH_MP_TAC spt_INDUCT THEN REPEAT STRIP_TAC THEN
  SPTAUX_BITS_TAC `x:num` THEN
  ASM_REWRITE_TAC[mk_wf_def; SPTAUX_lookup_mk_BS; SPTAUX_lookup_mk_BN;
                  lookup_rwts; SPTAUX_lookup_bits]);;

let domain_mk_wf = prove
 (`!t:A spt. domain (mk_wf t) = domain t`,
  REWRITE_TAC[EXTENSION; domain_lookup; lookup_mk_wf]);;

let mk_wf_eq = prove
 (`!t1 t2:A spt. (mk_wf t1 = mk_wf t2) <=> !x. lookup x t1 = lookup x t2`,
  MESON_TAC[spt_eq_thm; wf_mk_wf; lookup_mk_wf]);;

(* the theorem inter_eq (the constant inter_eq is inter_eq_def) *)

let inter_eq = prove
 (`!t1:A spt t2:B spt t3 t4:C spt.
     (sptree_inter t1 t2 = sptree_inter t3 t4) <=>
     !x. lookup x (sptree_inter t1 t2) = lookup x (sptree_inter t3 t4)`,
  MESON_TAC[spt_eq_thm; wf_inter]);;

let union_mk_wf = prove
 (`!t1 t2:A spt. sptree_union (mk_wf t1) (mk_wf t2) = mk_wf (sptree_union t1 t2)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `sptree_union (mk_wf t1) (mk_wf t2) =
                mk_wf (sptree_union (mk_wf t1) (mk_wf (t2:A spt)))` SUBST1_TAC THENL
   [MESON_TAC[wf_union; wf_mk_wf; wf_mk_id]; ALL_TAC] THEN
  REWRITE_TAC[mk_wf_eq; lookup_union; lookup_mk_wf]);;

let inter_mk_wf = prove
 (`!t1:A spt t2:B spt. sptree_inter (mk_wf t1) (mk_wf t2) = mk_wf (sptree_inter t1 t2)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `sptree_inter (mk_wf t1) (mk_wf t2) =
                mk_wf (sptree_inter (mk_wf (t1:A spt)) (mk_wf (t2:B spt)))`
    SUBST1_TAC THENL
   [MESON_TAC[wf_inter; wf_mk_wf; wf_mk_id]; ALL_TAC] THEN
  REWRITE_TAC[mk_wf_eq; lookup_inter; lookup_mk_wf]);;

let insert_mk_wf = prove
 (`!x (v:A) t. insert x v (mk_wf t) = mk_wf (insert x v t)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `insert x v (mk_wf t) = mk_wf (insert x (v:A) (mk_wf t))`
    SUBST1_TAC THENL
   [MESON_TAC[wf_insert; wf_mk_wf; wf_mk_id]; ALL_TAC] THEN
  REWRITE_TAC[mk_wf_eq; lookup_insert; lookup_mk_wf]);;

let delete_mk_wf = prove
 (`!x t:A spt. delete x (mk_wf t) = mk_wf (delete x t)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `delete x (mk_wf t) = mk_wf (delete x (mk_wf (t:A spt)))`
    SUBST1_TAC THENL
   [MESON_TAC[wf_delete; wf_mk_wf; wf_mk_id]; ALL_TAC] THEN
  REWRITE_TAC[mk_wf_eq; lookup_delete; lookup_mk_wf]);;

let union_LN = prove
 (`!t:A spt. (sptree_union t LN = t) /\ (sptree_union LN t = t)`,
  GEN_TAC THEN SPTAUX_CASES_TAC `t:A spt` THEN
  REWRITE_TAC[sptree_union_def; spt_CASE]);;

let inter_LN = prove
 (`!t:A spt. (sptree_inter t (LN:B spt) = LN) /\ (sptree_inter (LN:C spt) t = LN)`,
  REWRITE_TAC[sptree_inter_def] THEN GEN_TAC THEN SPTAUX_CASES_TAC `t:A spt` THEN
  REWRITE_TAC[sptree_inter_def; spt_CASE]);;

let union_assoc = prove
 (`!t1 t2 t3:A spt. sptree_union t1 (sptree_union t2 t3) = sptree_union (sptree_union t1 t2) t3`,
  MATCH_MP_TAC spt_INDUCT THEN REPEAT STRIP_TAC THEN
  SPTAUX_CASES_TAC `t2:A spt` THEN SPTAUX_CASES_TAC `t3:A spt` THEN
  ASM_REWRITE_TAC[sptree_union_def; spt_CASE]);;

let inter_assoc = prove
 (`!t1:A spt t2:B spt t3:C spt.
     sptree_inter t1 (sptree_inter t2 t3) = sptree_inter (sptree_inter t1 t2) t3`,
  REWRITE_TAC[inter_eq; lookup_inter] THEN REPEAT GEN_TAC THEN
  SPTAUX_CASES_TAC `lookup x (t1:A spt)` THEN
  SPTAUX_CASES_TAC `lookup x (t2:B spt)` THEN
  SPTAUX_CASES_TAC `lookup x (t3:C spt)` THEN
  REWRITE_TAC[option_CASE]);;

(* HOL4: lookup_compute, insert_compute, delete_compute (numeral forms for  *)
(* EVAL) are not ported.                                                     *)

(* ------------------------------------------------------------------------- *)
(* fromAList                                                                 *)
(* ------------------------------------------------------------------------- *)

let fromAList_def = cake_def
  `(fromAList [] = LN:A spt) /\
   (fromAList (CONS (x,y) xs) = insert x (y:A) (fromAList xs))`;;

let lookup_fromAList = prove
 (`!ls:(num#A)list x. lookup x (fromAList ls) = ALOOKUP ls x`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[fromAList_def; ALOOKUP_DEF; lookup_rwts] THEN
  SPTAUX_CASES_TAC `h:num#A` THEN
  ASM_REWRITE_TAC[fromAList_def; ALOOKUP_THM; lookup_insert] THEN
  MESON_TAC[]);;

let domain_fromAList = prove
 (`!ls:(num#A)list. domain (fromAList ls) = set_of_list (MAP FST ls)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[fromAList_def; domain_def; MAP; set_of_list] THEN
  SPTAUX_CASES_TAC `h:num#A` THEN
  ASM_REWRITE_TAC[fromAList_def; domain_insert; FST]);;

let lookup_fromAList_toAList = prove
 (`!t:A spt x. lookup x (fromAList (toAList t)) = lookup x t`,
  REWRITE_TAC[lookup_fromAList; ALOOKUP_toAList]);;

let wf_fromAList = prove
 (`!ls:(num#A)list. sptree_wf (fromAList ls)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[fromAList_def; sptree_wf_def] THEN
  SPTAUX_CASES_TAC `h:num#A` THEN
  ASM_SIMP_TAC[fromAList_def; wf_insert]);;

let fromAList_toAList = prove
 (`!t:A spt. sptree_wf t ==> (fromAList (toAList t) = t)`,
  MESON_TAC[wf_fromAList; lookup_fromAList_toAList; spt_eq_thm]);;

let union_insert_LN = prove
 (`!x (y:A) t2. sptree_union (insert x y LN) t2 = insert x y t2`,
  REWRITE_TAC[GSYM insert_union]);;

let fromAList_append = prove
 (`!l1 l2:(num#A)list.
     fromAList (APPEND l1 l2) = sptree_union (fromAList l1) (fromAList l2)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND; fromAList_def; union_LN] THEN
  SPTAUX_CASES_TAC `h:num#A` THEN ASM_REWRITE_TAC[fromAList_def] THEN
  GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [insert_union] THEN
  ONCE_REWRITE_TAC[union_assoc] THEN REWRITE_TAC[union_insert_LN]);;

(* ------------------------------------------------------------------------- *)
(* map                                                                       *)
(* ------------------------------------------------------------------------- *)

let sptree_map_def = cake_def
  `(sptree_map (f:A->B) LN = LN) /\
   (sptree_map f (LS a) = LS (f a)) /\
   (sptree_map f (BN t1 t2) = BN (sptree_map f t1) (sptree_map f t2)) /\
   (sptree_map f (BS t1 a t2) = BS (sptree_map f t1) (f a) (sptree_map f t2))`;;

let SPTAUX_toListA_map = prove
 (`!s:A spt acc. toListA (MAP (f:A->B) acc) (sptree_map f s) = MAP f (toListA acc s)`,
  MATCH_MP_TAC spt_INDUCT THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[sptree_map_def; toListA_def; MAP] THEN
  ASM_REWRITE_TAC[GSYM(CONJUNCT2 MAP)]);;

let toList_map = prove
 (`!s:A spt. toList (sptree_map (f:A->B) s) = MAP f (toList s)`,
  REWRITE_TAC[toList_def; GSYM SPTAUX_toListA_map; MAP]);;

let domain_map = prove
 (`!s:A spt. domain (sptree_map (f:A->B) s) = domain s`,
  MATCH_MP_TAC spt_INDUCT THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[sptree_map_def; domain_def]);;

let lookup_map = prove
 (`!s:A spt x. lookup x (sptree_map (f:A->B) s) = OPTION_MAP f (lookup x s)`,
  MATCH_MP_TAC spt_INDUCT THEN REPEAT STRIP_TAC THEN
  SPTAUX_BITS_TAC `x:num` THEN
  ASM_REWRITE_TAC[sptree_map_def; lookup_rwts; SPTAUX_lookup_bits; OPTION_MAP_DEF]);;

let map_LN = prove
 (`!t:A spt. (sptree_map (f:A->B) t = LN) <=> (t = LN)`,
  GEN_TAC THEN SPTAUX_CASES_TAC `t:A spt` THEN
  REWRITE_TAC[sptree_map_def; spt_distinct]);;

let wf_map = prove
 (`!t:A spt (f:A->B). sptree_wf (sptree_map f t) = sptree_wf t`,
  MATCH_MP_TAC spt_INDUCT THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[sptree_map_def; sptree_wf_def; map_LN]);;

let map_map_o = prove
 (`!t:A spt (f:B->C) (g:A->B). sptree_map f (sptree_map g t) = sptree_map (f o g) t`,
  MATCH_MP_TAC spt_INDUCT THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[sptree_map_def; o_THM]);;

let map_insert = prove
 (`!(f:A->B) x y z. sptree_map f (insert x y z) = insert x (f y) (sptree_map f z)`,
  GEN_TAC THEN MATCH_MP_TAC SPTAUX_bit_induction THEN REPEAT STRIP_TAC THEN
  SPTAUX_CASES_TAC `z:A spt` THEN
  ASM_REWRITE_TAC[SPTAUX_insert_bits; sptree_map_def]);;

let map_fromAList = prove
 (`sptree_map (f:A->B) (fromAList ls) = fromAList (MAP (\(k,v). (k,f v)) ls)`,
  SPEC_TAC(`ls:(num#A)list`,`ls:(num#A)list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[fromAList_def; sptree_map_def; MAP] THEN
  SPTAUX_CASES_TAC `h:num#A` THEN
  ASM_REWRITE_TAC[fromAList_def; map_insert]);;

let insert_insert = prove
 (`!x1 x2 (v1:A) v2 t.
     insert x1 v1 (insert x2 v2 t) =
     if x1 = x2 then insert x1 v1 t else insert x2 v2 (insert x1 v1 t)`,
  MATCH_MP_TAC SPTAUX_bit_induction THEN REPEAT STRIP_TAC THEN
  SPTAUX_BITS_TAC `x2:num` THEN SPTAUX_CASES_TAC `t:A spt` THEN
  ASM_REWRITE_TAC[SPTAUX_insert_bits; SPTAUX_BIT_RW] THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[SPTAUX_insert_bits] THEN
  ASM_MESON_TAC[]);;

let insert_shadow = prove
 (`!t a (b:A) c. insert a b (insert a c t) = insert a b t`,
  ONCE_REWRITE_TAC[insert_insert] THEN REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The sub-map relation, a partial order.                                    *)
(* ------------------------------------------------------------------------- *)

let spt_left_def = cake_def
  `(spt_left (LN:A spt) = LN) /\
   (spt_left (LS (x:A)) = LN) /\
   (spt_left (BN t1 t2) = t1) /\
   (spt_left (BS t1 x t2) = t1)`;;

let spt_right_def = cake_def
  `(spt_right (LN:A spt) = LN) /\
   (spt_right (LS (x:A)) = LN) /\
   (spt_right (BN t1 t2) = t2) /\
   (spt_right (BS t1 x t2) = t2)`;;

let spt_center_def = cake_def
  `(spt_center (LS (x:A)) = SOME x) /\
   (spt_center (BS t1 x t2) = SOME x) /\
   (spt_center LN = NONE) /\
   (spt_center (BN t1 t2) = NONE)`;;

(* HOL4: lookup_0_spt_center, lookup_spt_right, lookup_spt_left (proved     *)
(* later in the HOL4 script); SPTAUX_lookup_gen_bits in key form 2m+c      *)

let lookup_0_spt_center = prove
 (`!spt:A spt. lookup 0 spt = spt_center spt`,
  GEN_TAC THEN SPTAUX_CASES_TAC `spt:A spt` THEN
  REWRITE_TAC[lookup_rwts; spt_center_def]);;

let SPTAUX_lookup_gen_bits = prove
 (`(!t:A spt. lookup 0 t = spt_center t) /\
   (!m t:A spt. lookup (2 * m + 1) t = lookup m (spt_right t)) /\
   (!m t:A spt. lookup (2 * m + 2) t = lookup m (spt_left t))`,
  REWRITE_TAC[lookup_0_spt_center] THEN CONJ_TAC THEN REPEAT GEN_TAC THEN
  SPTAUX_CASES_TAC `t:A spt` THEN
  REWRITE_TAC[SPTAUX_lookup_bits; spt_right_def; spt_left_def; lookup_rwts]);;

let lookup_spt_right = prove
 (`lookup i (spt_right spt) = lookup ((i * 2) + 1) (spt:A spt)`,
  REWRITE_TAC[ONCE_REWRITE_RULE[MULT_SYM] SPTAUX_lookup_gen_bits]);;

let lookup_spt_left = prove
 (`lookup i (spt_left spt) = lookup ((i * 2) + 2) (spt:A spt)`,
  REWRITE_TAC[ONCE_REWRITE_RULE[MULT_SYM] SPTAUX_lookup_gen_bits]);;

(* HOL4: subspt_eq is the definition *)

let subspt_eq = cake_def
  `(subspt (LN:A spt) t <=> T) /\
   (subspt (LS x) t <=> (spt_center t = SOME x)) /\
   (subspt (BN t1 t2) t <=>
      subspt t1 (spt_left t) /\ subspt t2 (spt_right t)) /\
   (subspt (BS t1 x t2) t <=>
      (spt_center t = SOME x) /\
      subspt t1 (spt_left t) /\ subspt t2 (spt_right t))`;;

let subspt_lookup = prove
 (`!t1 t2:A spt.
     subspt t1 t2 <=>
     !x y. (lookup x t1 = SOME y) ==> (lookup x t2 = SOME y)`,
  MATCH_MP_TAC spt_INDUCT THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[subspt_eq] THEN ONCE_REWRITE_TAC[SPTAUX_FORALL_BITS] THEN
  ASM_REWRITE_TAC[lookup_rwts; SPTAUX_lookup_bits; SPTAUX_lookup_gen_bits;
                  option_DISTINCT; option_INJ; spt_center_def;
                  FORALL_UNWIND_THM1; FORALL_UNWIND_THM2] THEN
  MESON_TAC[]);;

let subspt_domain = prove
 (`!t1 (t2:1 spt). subspt t1 t2 <=> domain t1 SUBSET domain t2`,
  REWRITE_TAC[subspt_lookup; domain_lookup; SUBSET; FORALL_ONE_THM;
              EXISTS_ONE_THM] THEN
  MESON_TAC[]);;

let subspt_def = prove
 (`!sp1 sp2:A spt.
     subspt sp1 sp2 <=>
     !k. k IN domain sp1 ==> k IN domain sp2 /\
         (lookup k sp2 = lookup k sp1)`,
  REWRITE_TAC[subspt_lookup; domain_lookup] THEN
  MESON_TAC[option_INJ]);;

let subspt_refl = prove
 (`subspt sp (sp:A spt)`,
  REWRITE_TAC[subspt_lookup]);;

let subspt_trans = prove
 (`subspt sp1 sp2 /\ subspt sp2 sp3 ==> subspt sp1 (sp3:A spt)`,
  REWRITE_TAC[subspt_lookup] THEN MESON_TAC[]);;

let subspt_LN = prove
 (`(subspt LN (sp:A spt) <=> T) /\ (subspt sp (LN:A spt) <=> (domain sp = {}))`,
  REWRITE_TAC[subspt_def; EXTENSION; domain_def; NOT_IN_EMPTY] THEN
  MESON_TAC[]);;

let subspt_union = prove
 (`subspt s (sptree_union s (t:A spt))`,
  REWRITE_TAC[subspt_lookup; lookup_union] THEN REPEAT GEN_TAC THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[option_CASE]);;

let subspt_FOLDL_union = prove
 (`!ls t:A spt. subspt t (FOLDL sptree_union t ls)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[FOLDL; subspt_refl] THEN
  ASM_MESON_TAC[subspt_union; subspt_trans]);;

let domain_mapi = prove
 (`domain (mapi (f:num->A->B) x) = domain x`,
  REWRITE_TAC[domain_lookup; EXTENSION; lookup_mapi] THEN GEN_TAC THEN
  SPTAUX_CASES_TAC `lookup x' (x:A spt)` THEN
  REWRITE_TAC[OPTION_MAP_DEF; option_DISTINCT; option_INJ] THEN MESON_TAC[]);;

let lookup_FOLDL_union = prove
 (`lookup k (FOLDL sptree_union t ls) =
   FOLDL OPTION_CHOICE (lookup k (t:A spt)) (MAP (lookup k) ls)`,
  SPEC_TAC(`t:A spt`,`t:A spt`) THEN SPEC_TAC(`ls:(A spt)list`,`ls:(A spt)list`) THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[FOLDL; MAP; lookup_union] THEN
  X_GEN_TAC `t0:A spt` THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  SPTAUX_CASES_TAC `lookup k (t0:A spt)` THEN
  REWRITE_TAC[option_CASE; OPTION_CHOICE_DEF]);;

let map_union = prove
 (`!t1 t2:A spt. sptree_map (f:A->B) (sptree_union t1 t2) = sptree_union (sptree_map f t1) (sptree_map f t2)`,
  MATCH_MP_TAC spt_INDUCT THEN REPEAT STRIP_TAC THEN
  SPTAUX_CASES_TAC `t2:A spt` THEN
  ASM_REWRITE_TAC[sptree_map_def; sptree_union_def; spt_CASE]);;

let domain_eq = prove
 (`!t1:A spt t2:B spt.
     (domain t1 = domain t2) <=>
     !k. (lookup k t1 = NONE) <=> (lookup k t2 = NONE)`,
  REWRITE_TAC[EXTENSION; lookup_NONE_domain] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* filter_v, mapi, and further lemmas                                        *)
(* ------------------------------------------------------------------------- *)

(* filter values stored in sptree *)

let filter_v_def = cake_def
  `(filter_v (f:A->bool) LN = LN) /\
   (filter_v f (LS x) = if f x then LS x else LN) /\
   (filter_v f (BN l r) = mk_BN (filter_v f l) (filter_v f r)) /\
   (filter_v f (BS l x r) =
      if f x then mk_BS (filter_v f l) x (filter_v f r)
      else mk_BN (filter_v f l) (filter_v f r))`;;

let lookup_filter_v = prove
 (`!k t:A spt f.
     lookup k (filter_v f t) =
     option_CASE (lookup k t) NONE (\v. if f v then SOME v else NONE)`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  MATCH_MP_TAC spt_INDUCT THEN REPEAT STRIP_TAC THEN
  SPTAUX_BITS_TAC `k:num` THEN
  REWRITE_TAC[filter_v_def] THEN
  REPEAT COND_CASES_TAC THEN
  ASM_REWRITE_TAC[lookup_rwts; SPTAUX_lookup_bits; SPTAUX_lookup_mk_BN;
                  SPTAUX_lookup_mk_BS; option_CASE]);;

let wf_filter_v = prove
 (`!t:A spt f. sptree_wf t ==> sptree_wf (filter_v f t)`,
  MATCH_MP_TAC spt_INDUCT THEN REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[sptree_wf_def]) THEN
  REWRITE_TAC[filter_v_def] THEN REPEAT COND_CASES_TAC THEN
  ASM_SIMP_TAC[sptree_wf_def; SPTAUX_wf_mk_BN; SPTAUX_wf_mk_BS]);;

let wf_mk_BN = prove
 (`sptree_wf t1 /\ sptree_wf t2 ==> sptree_wf (mk_BN t1 (t2:A spt))`,
  REWRITE_TAC[SPTAUX_wf_mk_BN]);;

let wf_mk_BS = prove
 (`sptree_wf t1 /\ sptree_wf t2 ==> sptree_wf (mk_BS t1 (a:A) t2)`,
  REWRITE_TAC[SPTAUX_wf_mk_BS]);;

let wf_mapi = prove
 (`sptree_wf (mapi (f:num->A->B) pt)`,
  REWRITE_TAC[mapi_def] THEN
  SUBGOAL_THEN `!pt:A spt n. sptree_wf (mapi0 (f:num->A->B) n pt)`
    (fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC spt_INDUCT THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[mapi0_def; LET_DEF; LET_END_DEF; sptree_wf_def; SPTAUX_wf_mk_BN;
                  SPTAUX_wf_mk_BS]);;

(* HOL4: ALOOKUP_MAP_lemma (local) *)

let SPTAUX_ALOOKUP_MAP_lemma = prove
 (`ALOOKUP (MAP (\kv. (FST kv, (f:num->A->B) (FST kv) (SND kv))) al) n =
   OPTION_MAP (\v. f n v) (ALOOKUP (al:(num#A)list) n)`,
  SPEC_TAC(`al:(num#A)list`,`al:(num#A)list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; ALOOKUP_DEF; OPTION_MAP_DEF] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[OPTION_MAP_DEF]);;

let lookup_mk_BN = prove
 (`lookup i (mk_BN t1 t2) =
   if i = 0 then NONE
   else lookup ((i - 1) DIV 2) (if EVEN i then t1 else t2:A spt)`,
  REWRITE_TAC[SPTAUX_lookup_mk_BN; lookup_def]);;

let MAP_foldi = prove
 (`!pt:A spt n acc.
     MAP (f:num#A->B) (foldi (\k v a. CONS (k,v) a) n acc pt) =
     foldi (\k v a. CONS (f (k,v)) a) n (MAP f acc) pt`,
  MATCH_MP_TAC spt_INDUCT THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[SPTAUX_foldi_thm; MAP]);;

let mapi_Alist = prove
 (`mapi (f:num->A->B) pt =
   fromAList (MAP (\kv. (FST kv,f (FST kv) (SND kv))) (toAList pt))`,
  SIMP_TAC[spt_eq_thm; wf_mapi; wf_fromAList] THEN
  REWRITE_TAC[lookup_fromAList; lookup_mapi; SPTAUX_ALOOKUP_MAP_lemma;
              ALOOKUP_toAList] THEN
  GEN_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[ETA_AX]);;

let num_set_domain_eq = prove
 (`!t1 t2:1 spt. sptree_wf t1 /\ sptree_wf t2 ==> ((domain t1 = domain t2) <=> (t1 = t2))`,
  SIMP_TAC[spt_eq_thm] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[EXTENSION; domain_lookup; EXISTS_ONE_THM] THEN
  EQ_TAC THEN DISCH_TAC THEN X_GEN_TAC `n:num` THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
    SPTAUX_CASES_TAC `lookup n (t1:1 spt)` THEN
    SPTAUX_CASES_TAC `lookup n (t2:1 spt)` THEN
    REWRITE_TAC[option_DISTINCT; option_INJ] THEN MESON_TAC[one];
    ASM_REWRITE_TAC[]]);;

let union_num_set_sym = prove
 (`!(t1:1 spt) t2. sptree_union t1 t2 = sptree_union t2 t1`,
  MATCH_MP_TAC spt_INDUCT THEN REPEAT STRIP_TAC THEN
  SPTAUX_CASES_TAC `t2:1 spt` THEN
  ASM_REWRITE_TAC[sptree_union_def; spt_CASE; spt_inject] THEN MESON_TAC[one]);;

let union_disjoint_sym = prove
 (`!t1 t2:A spt.
     sptree_wf t1 /\ sptree_wf t2 /\ DISJOINT (domain t1) (domain t2) ==>
     sptree_union t1 t2 = sptree_union t2 t1`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[spt_eq_thm; wf_union; lookup_union] THEN
  X_GEN_TAC `n:num` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o REWRITE_RULE[DISJOINT; EXTENSION;
    IN_INTER; NOT_IN_EMPTY; domain_lookup]) THEN
  SPTAUX_CASES_TAC `lookup n (t1:A spt)` THEN
  SPTAUX_CASES_TAC `lookup n (t2:A spt)` THEN
  REWRITE_TAC[option_CASE; option_DISTINCT; option_INJ] THEN MESON_TAC[]);;

let difference_sub = prove
 (`(difference a b = LN) ==> (domain (a:A spt) SUBSET domain (b:B spt))`,
  DISCH_THEN(MP_TAC o AP_TERM `domain:A spt->num->bool`) THEN
  REWRITE_TAC[domain_difference; domain_def] THEN SET_TAC[]);;

let wf_difference = prove
 (`!t1:A spt t2:B spt. sptree_wf t1 /\ sptree_wf t2 ==> sptree_wf (difference t1 t2)`,
  MATCH_MP_TAC spt_INDUCT THEN REPEAT STRIP_TAC THEN
  SPTAUX_CASES_TAC `t2:B spt` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[sptree_wf_def]) THEN
  ASM_SIMP_TAC[difference_def; spt_CASE; sptree_wf_def; SPTAUX_wf_mk_BN;
               SPTAUX_wf_mk_BS]);;

let delete_fail = prove
 (`!n t:A spt. sptree_wf t ==> (~(n IN domain t) <=> (delete n t = t))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN ASM_SIMP_TAC[spt_eq_thm; wf_delete; lookup_delete] THEN
    GEN_TAC THEN COND_CASES_TAC THEN ASM_MESON_TAC[lookup_NONE_domain];
    DISCH_THEN(MP_TAC o AP_TERM `domain:A spt->num->bool`) THEN
    REWRITE_TAC[domain_delete] THEN SET_TAC[]]);;

let size_delete = prove
 (`!n t:A spt. sptree_size (delete n t) =
               if lookup n t = NONE then sptree_size t else sptree_size t - 1`,
  REWRITE_TAC[size_domain; domain_delete; lookup_NONE_domain] THEN
  SIMP_TAC[CARD_DELETE; FINITE_domain] THEN MESON_TAC[]);;

let lookup_fromList_outside = prove
 (`!k. LENGTH args <= k ==> (lookup k (fromList (args:A list)) = NONE)`,
  SIMP_TAC[lookup_fromList; GSYM NOT_LT]);;

let spt_fold_def = cake_def
  `(spt_fold (f:A->B->B) acc LN = acc) /\
   (spt_fold f acc (LS a) = f a acc) /\
   (spt_fold f acc (BN t1 t2) = spt_fold f (spt_fold f acc t1) t2) /\
   (spt_fold f acc (BS t1 a t2) = spt_fold f (f a (spt_fold f acc t1)) t2)`;;

let IMP_size_LESS_size = prove
 (`!x y:A spt. subspt x y /\ ~(domain x = domain y) ==> sptree_size x < sptree_size y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[size_domain] THEN
  MATCH_MP_TAC CARD_PSUBSET THEN REWRITE_TAC[FINITE_domain; PSUBSET] THEN
  ASM_REWRITE_TAC[] THEN UNDISCH_TAC `subspt (x:A spt) y` THEN
  REWRITE_TAC[subspt_def; SUBSET] THEN MESON_TAC[]);;

let size_diff_less = prove
 (`!x:A spt y:B spt z:C spt t.
     domain z SUBSET domain y /\ t IN domain y /\
     ~(t IN domain z) /\ t IN domain x ==>
     sptree_size (difference x y) < sptree_size (difference x z)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC IMP_size_LESS_size THEN CONJ_TAC THENL
   [REWRITE_TAC[subspt_lookup; lookup_difference] THEN REPEAT GEN_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
    SUBGOAL_THEN `lookup x' (z:C spt) = NONE` (fun th -> REWRITE_TAC[th]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[lookup_NONE_domain]) THEN
    REWRITE_TAC[lookup_NONE_domain] THEN ASM SET_TAC[];
    REWRITE_TAC[domain_difference; EXTENSION; IN_DIFF] THEN
    DISCH_THEN(MP_TAC o SPEC `t:num`) THEN ASM_REWRITE_TAC[]]);;

let inter_eq_LN = prove
 (`!x:A spt y:B spt. (sptree_inter x y = LN) <=> DISJOINT (domain x) (domain y)`,
  SIMP_TAC[domain_empty; wf_inter; domain_inter; DISJOINT]);;

(* ------------------------------------------------------------------------- *)
(* list_to_num_set, list_insert, alist_insert                               *)
(* ------------------------------------------------------------------------- *)

let list_to_num_set_def = cake_def
  `(list_to_num_set [] = LN:1 spt) /\
   (list_to_num_set (CONS n ns) = insert n one (list_to_num_set ns))`;;

let list_insert_def = cake_def
  `(list_insert [] (t:1 spt) = t) /\
   (list_insert (CONS n ns) t = list_insert ns (insert n one t))`;;

let domain_list_to_num_set = prove
 (`!xs. x IN domain (list_to_num_set xs) <=> MEM x xs`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[list_to_num_set_def; domain_def; NOT_IN_EMPTY; MEM;
                  domain_insert; IN_INSERT]);;

let domain_list_insert = prove
 (`!xs x t. x IN domain (list_insert xs t) <=> MEM x xs \/ x IN domain t`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[list_insert_def; MEM; domain_insert; IN_INSERT] THEN
  MESON_TAC[]);;

let domain_FOLDR_delete = prove
 (`!ls live:A spt.
     domain (ITLIST delete ls live) = (domain live) DIFF (set_of_list ls)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[ITLIST; set_of_list; DIFF_EMPTY; domain_delete] THEN
  SET_TAC[]);;

let lookup_list_to_num_set = prove
 (`!xs. lookup x (list_to_num_set xs) = if MEM x xs then SOME one else NONE`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[list_to_num_set_def; lookup_rwts; MEM; lookup_insert] THEN
  MESON_TAC[]);;

let list_to_num_set_append = prove
 (`!l1 l2. list_to_num_set (APPEND l1 l2) =
           sptree_union (list_to_num_set l1) (list_to_num_set l2)`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND; list_to_num_set_def; union_LN] THEN
  GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [insert_union] THEN
  ONCE_REWRITE_TAC[union_assoc] THEN REWRITE_TAC[union_insert_LN]);;

let map_map_K = prove
 (`!t:A spt. sptree_map (combin_K (a:C)) (sptree_map (f:A->B) t) = sptree_map (combin_K a) t`,
  MATCH_MP_TAC spt_INDUCT THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[sptree_map_def; K_THM]);;

let lookup_map_K = prove
 (`!t:A spt n. lookup n (sptree_map (combin_K (x:B)) t) =
               if n IN domain t then SOME x else NONE`,
  REWRITE_TAC[lookup_map; domain_lookup] THEN REPEAT GEN_TAC THEN
  SPTAUX_CASES_TAC `lookup n (t:A spt)` THEN
  REWRITE_TAC[OPTION_MAP_DEF; K_THM; option_DISTINCT; option_INJ] THEN
  MESON_TAC[]);;

let alist_insert_def = cake_def
  `(alist_insert [] xs t = t:A spt) /\
   (alist_insert (CONS v4 v5) [] t = t) /\
   (alist_insert (CONS v vs) (CONS (x:A) xs) t =
      insert v x (alist_insert vs xs t))`;;

let alist_insert_ind = prove
 (`!P. (!(xs:A list) (t:A spt). P [] xs t) /\
       (!(v:num) vs (t:A spt). P (CONS v vs) [] t) /\
       (!v vs x xs t. P vs xs t ==> P (CONS v vs) (CONS x xs) t)
       ==> !v v1 v2. P v v1 v2`,
  GEN_TAC THEN STRIP_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[] THEN
  LIST_INDUCT_TAC THEN ASM_SIMP_TAC[]);;

let lookup_alist_insert = prove
 (`!x y (t:A spt) z.
     (LENGTH x = LENGTH y) ==>
     (lookup z (alist_insert x y t) =
      option_CASE (ALOOKUP (ZIP x y) z) (lookup z t) (\a. SOME a))`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ; alist_insert_def; ZIP; ALOOKUP_DEF;
              option_CASE] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[lookup_insert; FST; SND] THEN
  ASM_CASES_TAC `h = (z:num)` THEN ASM_REWRITE_TAC[option_CASE]);;

let domain_alist_insert = prove
 (`!a b (locs:A spt). (LENGTH a = LENGTH b) ==>
                      (domain (alist_insert a b locs) =
                       domain locs UNION set_of_list a)`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ; alist_insert_def; set_of_list;
              UNION_EMPTY] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[domain_insert] THEN SET_TAC[]);;

let alist_insert_append = prove
 (`!a1 a2 (s:A spt) b1 b2.
     (LENGTH a1 = LENGTH a2) ==>
     (alist_insert (APPEND a1 b1) (APPEND a2 b2) s =
      alist_insert a1 a2 (alist_insert b1 b2 s))`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ; alist_insert_def; APPEND] THEN
  ASM_SIMP_TAC[alist_insert_def]);;

let wf_LN = prove
 (`sptree_wf (LN:A spt)`,
  REWRITE_TAC[sptree_wf_def]);;

let wf_fromList = prove
 (`sptree_wf (fromList (ls:A list))`,
  REWRITE_TAC[fromList_def] THEN
  SUBGOAL_THEN `!ls:A list i t. sptree_wf t ==>
     sptree_wf (SND (FOLDL (\(i,t) a. (i + 1,insert i a t)) (i,t) ls))`
    (fun th -> MATCH_MP_TAC th THEN REWRITE_TAC[wf_LN]) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[FOLDL] THEN
  ASM_SIMP_TAC[wf_insert]);;

let wf_list_to_num_set = prove
 (`!ls. sptree_wf (list_to_num_set ls)`,
  LIST_INDUCT_TAC THEN ASM_SIMP_TAC[list_to_num_set_def; wf_insert; wf_LN]);;

let size_list_to_num_set = prove
 (`sptree_size (list_to_num_set ls) = LENGTH (list_nub ls)`,
  SPEC_TAC(`ls:num list`,`ls:num list`) THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[list_to_num_set_def; list_nub_DEF; sptree_size_def; LENGTH;
                  size_insert; domain_list_to_num_set] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[LENGTH; ADD1]);;

(* list lemmas (MAPi), proved here for local use *)

let SPTAUX_LENGTH_MAPi = prove
 (`!(f:num->A->B) l. LENGTH (MAPi f l) = LENGTH l`,
  GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAPi_DEF; LENGTH]);;

let SPTAUX_EL_MAPi = prove
 (`!l (f:num->A->B) n. n < LENGTH l ==> EL n (MAPi f l) = f n (EL n l)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; CONJUNCT1 LT] THEN
  GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[MAPi_DEF; EL; HD; TL; LT_SUC] THEN
  ASM_SIMP_TAC[o_THM]);;

let mapi_fromList = prove
 (`mapi (f:num->A->B) (fromList ls) = fromList (MAPi f ls)`,
  SIMP_TAC[spt_eq_thm; wf_mapi; wf_fromList] THEN
  REWRITE_TAC[lookup_fromList; lookup_mapi] THEN
  GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[OPTION_MAP_DEF; SPTAUX_LENGTH_MAPi] THEN
  ASM_SIMP_TAC[SPTAUX_EL_MAPi]);;

(* list lemmas (TAKE, DROP), proved here for local use *)

let SPTAUX_DROP_0 = prove
 (`!l:A list. DROP 0 l = l`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[DROP_DEF]);;

let SPTAUX_TAKE_DROP_UPDATE = prove
 (`!ls:A list k v. k < LENGTH ls ==>
     LENGTH (APPEND (APPEND (TAKE k ls) [v]) (DROP (SUC k) ls)) = LENGTH ls /\
     !n. n < LENGTH ls ==>
         EL n (APPEND (APPEND (TAKE k ls) [v]) (DROP (SUC k) ls)) =
         if n = k then v else EL n ls`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; CONJUNCT1 LT] THEN
  INDUCT_TAC THEN
  REWRITE_TAC[TAKE_DEF; DROP_DEF; NOT_SUC; SUC_SUB1; APPEND; LENGTH; LT_SUC;
              SPTAUX_DROP_0] THEN
  GEN_TAC THEN DISCH_TAC THENL
   [INDUCT_TAC THEN REWRITE_TAC[EL; HD; TL; NOT_SUC]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`; `v:A`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  INDUCT_TAC THEN
  REWRITE_TAC[EL; HD; TL; ARITH_RULE `~(0 = SUC n)`; SUC_INJ; LT_SUC] THEN
  ASM_SIMP_TAC[]);;

let insert_fromList_IN_domain = prove
 (`!ls k (v:A).
     k < LENGTH ls ==>
     insert k v (fromList ls) =
     fromList (APPEND (APPEND (TAKE k ls) [v]) (DROP (SUC k) ls))`,
  REPEAT STRIP_TAC THEN
  SIMP_TAC[spt_eq_thm; wf_insert; wf_fromList] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC `v:A` o MATCH_MP SPTAUX_TAKE_DROP_UPDATE) THEN
  ASM_REWRITE_TAC[lookup_insert; lookup_fromList] THEN
  X_GEN_TAC `n:num` THEN ASM_CASES_TAC `n:num = k` THEN ASM_SIMP_TAC[]);;


let insert_swap = prove
 (`!t a (b:A) c d.
     ~(a = c) ==> (insert a b (insert c d t) = insert c d (insert a b t))`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [insert_insert] THEN
  ASM_REWRITE_TAC[]);;

let alist_insert_pull_insert = prove
 (`!xs ys (z:A spt).
     ~MEM x xs ==>
     (alist_insert xs ys (insert x y z) = insert x y (alist_insert xs ys z))`,
  MATCH_MP_TAC alist_insert_ind THEN
  REWRITE_TAC[alist_insert_def; MEM; DE_MORGAN_THM] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC insert_swap THEN ASM_MESON_TAC[]);;

let alist_insert_REVERSE = prove
 (`!xs ys (s:A spt).
     ALL_DISTINCT xs /\ (LENGTH xs = LENGTH ys) ==>
     (alist_insert (REVERSE xs) (REVERSE ys) s = alist_insert xs ys s)`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ; REVERSE; alist_insert_def;
              ALL_DISTINCT] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[alist_insert_append; LENGTH_REVERSE; alist_insert_def] THEN
  ASM_SIMP_TAC[alist_insert_pull_insert]);;

let insert_unchanged = prove
 (`!t x. (lookup x t = SOME (y:A)) ==> (insert x y t = t)`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  MATCH_MP_TAC SPTAUX_bit_induction THEN REPEAT STRIP_TAC THEN
  SPTAUX_CASES_TAC `t:A spt` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[lookup_rwts; SPTAUX_lookup_bits;
                              option_DISTINCT; option_INJ]) THEN
  TRY(FIRST_ASSUM CONTR_TAC) THEN ASM_SIMP_TAC[SPTAUX_insert_bits]);;

(* HOL4: delete_mk_BN, delete_mk_BS (local), in key form *)

let SPTAUX_delete_mk_BN = prove
 (`(!t1 t2:A spt. delete 0 (mk_BN t1 t2) = mk_BN t1 t2) /\
   (!m t1 t2:A spt. delete (2 * m + 1) (mk_BN t1 t2) = mk_BN t1 (delete m t2)) /\
   (!m t1 t2:A spt. delete (2 * m + 2) (mk_BN t1 t2) = mk_BN (delete m t1) t2)`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  SPTAUX_CASES_TAC `t1:A spt` THEN SPTAUX_CASES_TAC `t2:A spt` THEN
  REWRITE_TAC[mk_BN_def; delete_def; SPTAUX_BIT_RW]);;

let SPTAUX_delete_mk_BS = prove
 (`(!t1 (s:A) t2. delete 0 (mk_BS t1 s t2) = mk_BN t1 t2) /\
   (!m t1 (s:A) t2.
      delete (2 * m + 1) (mk_BS t1 s t2) = mk_BS t1 s (delete m t2)) /\
   (!m t1 (s:A) t2.
      delete (2 * m + 2) (mk_BS t1 s t2) = mk_BS (delete m t1) s t2)`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  SPTAUX_CASES_TAC `t1:A spt` THEN SPTAUX_CASES_TAC `t2:A spt` THEN
  REWRITE_TAC[mk_BS_def; mk_BN_def; delete_def; SPTAUX_BIT_RW]);;

let SPTAUX_BIT_LT = prove
 (`(!p q. 2 * p + 1 < 2 * q + 1 <=> p < q) /\
   (!p q. 2 * p + 2 < 2 * q + 2 <=> p < q)`,
  ARITH_TAC);;

let SPTAUX_delete_delete_same = prove
 (`!f:A spt n. delete n (delete n f) = delete n f`,
  MATCH_MP_TAC spt_INDUCT THEN REPEAT STRIP_TAC THEN
  SPTAUX_BITS_TAC `n:num` THEN
  ASM_REWRITE_TAC[delete_def; SPTAUX_BIT_RW; SPTAUX_delete_mk_BN;
                  SPTAUX_delete_mk_BS]);;

let SPTAUX_delete_delete_lt = prove
 (`!f:A spt n k. n < k ==> delete n (delete k f) = delete k (delete n f)`,
  MATCH_MP_TAC spt_INDUCT THEN REPEAT STRIP_TAC THEN
  SPTAUX_BITS_TAC `n:num` THEN SPTAUX_BITS_TAC `k:num` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPTAUX_BIT_LT; LT_REFL]) THEN
  TRY(FIRST_ASSUM CONTR_TAC) THEN
  ASM_SIMP_TAC[delete_def; SPTAUX_BIT_RW; SPTAUX_delete_mk_BN;
               SPTAUX_delete_mk_BS] THEN
  ASM_MESON_TAC[]);;

let delete_delete = prove
 (`!f:A spt n k.
     delete n (delete k f) =
     if n = k then delete n f else delete k (delete n f)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[SPTAUX_delete_delete_same] THEN
  REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
    (ARITH_RULE `n < k \/ k < (n:num) \/ n = k`) THENL
   [MATCH_MP_TAC SPTAUX_delete_delete_lt THEN ASM_REWRITE_TAC[];
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC SPTAUX_delete_delete_lt THEN
    ASM_REWRITE_TAC[];
    ASM_MESON_TAC[]]);;

let list_size_APPEND = prove
 (`list_size (f:A->num) (APPEND xs ys) = list_size f xs + list_size f ys`,
  SPEC_TAC(`xs:A list`,`xs:A list`) THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND; list_size] THEN ARITH_TAC);;

let size_map = prove
 (`sptree_size (sptree_map (f:A->B) t) = sptree_size t`,
  REWRITE_TAC[size_domain; domain_map]);;

let size_mapi = prove
 (`sptree_size (mapi (f:num->A->B) t) = sptree_size t`,
  REWRITE_TAC[size_domain; domain_mapi]);;

let SUM_MAP_same_LE = prove
 (`ALL (\x. (f:A->num) x <= g x) xs ==> SUM (MAP f xs) <= SUM (MAP g xs)`,
  SPEC_TAC(`xs:A list`,`xs:A list`) THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[ALL; MAP; SUM; LE_REFL] THEN STRIP_TAC THEN
  MATCH_MP_TAC LE_ADD2 THEN ASM_SIMP_TAC[]);;

let SUM_MAP_same_LESS = prove
 (`ALL (\x. (f:A->num) x <= g x) xs /\ EX (\x. f x < g x) xs
   ==> SUM (MAP f xs) < SUM (MAP g xs)`,
  SPEC_TAC(`xs:A list`,`xs:A list`) THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[ALL; EX; MAP; SUM] THEN STRIP_TAC THENL
   [MATCH_MP_TAC LTE_ADD2 THEN ASM_SIMP_TAC[SUM_MAP_same_LE];
    MATCH_MP_TAC LET_ADD2 THEN ASM_SIMP_TAC[]]);;

let size_fromList = prove
 (`sptree_size (fromList (ls:A list)) = LENGTH ls`,
  REWRITE_TAC[size_domain; domain_fromList; pred_set_count_DEF; CARD_NUMSEG_LT]);;

(* ------------------------------------------------------------------------- *)
(* toSortedAList: the association list in key order (breadth-first walk).   *)
(* HOL4's add_pause is an overload of spts_to_alist_add_pause.               *)
(* ------------------------------------------------------------------------- *)

let spts_to_alist_add_pause_def = new_definition
  `spts_to_alist_add_pause j (q:(num#A spt)list) =
     list_CASE q [(j,LN)] (\h q. pair_CASE h (\i spt. CONS (i + j,spt) q))`;;

(* termination by the length of xs, given explicitly (HOL4 finds it; the   *)
(* measure search of cake_def took a minute here)                           *)
let spts_to_alist_aux_def = cake_def_wf
  `MEASURE (\t:num#(num#A spt)list#(num#A)list#(num#A spt)list#(num#A spt)list#bool.
              LENGTH (FST (SND t)))`
  (REWRITE_TAC WF_REL_THMS THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
   REWRITE_TAC[FST; SND] THEN REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC[LENGTH] THEN ARITH_TAC)
  `spts_to_alist_aux i (xs:(num#A spt)list) (acc_cent:(num#A)list)
                     acc_right acc_left repeat =
     list_CASE xs
       (i,APPEND (REVERSE acc_right) (REVERSE acc_left),acc_cent,repeat)
       (\h ys. pair_CASE h (\j spt.
          if spt = LN
          then spts_to_alist_aux (i + j) ys acc_cent
                 (spts_to_alist_add_pause j acc_right)
                 (spts_to_alist_add_pause j acc_left) repeat
          else spts_to_alist_aux (i + j) ys
                 (APPEND (option_CASE (spt_center spt) [] (\c. [(i,c)]))
                         acc_cent)
                 (CONS (j,spt_right spt) acc_right)
                 (CONS (j,spt_left spt) acc_left) T))`;;

let SPTAUX_spts_to_alist_aux_thm = prove
 (`(!i (acc_cent:(num#A)list) acc_right acc_left repeat.
      spts_to_alist_aux i [] acc_cent acc_right acc_left repeat =
      (i,APPEND (REVERSE acc_right) (REVERSE acc_left),acc_cent,repeat)) /\
   (!i j (spt:A spt) ys acc_cent acc_right acc_left repeat.
      spts_to_alist_aux i (CONS (j,spt) ys) acc_cent acc_right acc_left repeat =
      if spt = LN
      then spts_to_alist_aux (i + j) ys acc_cent
             (spts_to_alist_add_pause j acc_right)
             (spts_to_alist_add_pause j acc_left) repeat
      else spts_to_alist_aux (i + j) ys
             (APPEND (option_CASE (spt_center spt) [] (\c. [(i,c)])) acc_cent)
             (CONS (j,spt_right spt) acc_right)
             (CONS (j,spt_left spt) acc_left) T)`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [spts_to_alist_aux_def] THEN
  REWRITE_TAC[list_CASE; pair_CASE]);;

let SPTAUX_SUM_add_pause = prove
 (`!j q:(num#A spt)list.
     SUM (MAP (spt_size (combin_K 0) o SND) (spts_to_alist_add_pause j q)) =
     SUM (MAP (spt_size (combin_K 0) o SND) q)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[spts_to_alist_add_pause_def; list_CASE; MAP; SUM; o_THM;
              spt_size_def; SND; ADD_CLAUSES] THEN
  SPTAUX_CASES_TAC `h:num#A spt` THEN
  REWRITE_TAC[pair_CASE; MAP; SUM; o_THM; SND]);;

let SPTAUX_SUM_MAP_APPEND = prove
 (`!f l1 l2:B list. SUM (MAP f (APPEND l1 l2)) = SUM (MAP f l1) + SUM (MAP f l2)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND; MAP; SUM] THEN
  ARITH_TAC);;

let SPTAUX_SUM_MAP_REVERSE = prove
 (`!f l:B list. SUM (MAP f (REVERSE l)) = SUM (MAP f l)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[REVERSE; MAP; SUM; SPTAUX_SUM_MAP_APPEND] THEN ARITH_TAC);;

let SPTAUX_spt_size_left_right = prove
 (`!spt:A spt. ~(spt = LN) ==>
     spt_size (combin_K 0) (spt_left spt) + spt_size (combin_K 0) (spt_right spt) <
     spt_size (combin_K 0) spt`,
  GEN_TAC THEN SPTAUX_CASES_TAC `spt:A spt` THEN
  REWRITE_TAC[spt_left_def; spt_right_def; spt_size_def; K_THM; spt_distinct] THEN
  ARITH_TAC);;

let spts_to_alist_aux_size = prove
 (`!i (xs:(num#A spt)list) acc_cent acc_right acc_left repeat.
   !j ys acc2 repeat2.
     spts_to_alist_aux i xs acc_cent acc_right acc_left repeat =
       (j,ys,acc2,repeat2) ==>
     let sz = (SUM o MAP (spt_size (combin_K 0) o SND)) in
       sz ys <= sz (APPEND (APPEND xs acc_right) acc_left) /\
       (repeat2 ==> ~repeat ==>
        sz ys < sz (APPEND (APPEND xs acc_right) acc_left))`,
  REWRITE_TAC[LET_DEF; LET_END_DEF; o_THM; SPTAUX_SUM_MAP_APPEND] THEN
  X_GEN_TAC `i:num` THEN X_GEN_TAC `xs:(num#A spt)list` THEN
  SPEC_TAC(`i:num`,`i:num`) THEN SPEC_TAC(`xs:(num#A spt)list`,`xs:(num#A spt)list`) THEN
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[SPTAUX_spts_to_alist_aux_thm; PAIR_EQ] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN RVEQ_TAC THEN
    REWRITE_TAC[SPTAUX_SUM_MAP_APPEND; SPTAUX_SUM_MAP_REVERSE; MAP; SUM] THEN
    CONJ_TAC THENL [ARITH_TAC; MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `h:num#A spt` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:num` (X_CHOOSE_THEN `b:A spt` SUBST1_TAC)) THEN
  REWRITE_TAC[SPTAUX_spts_to_alist_aux_thm] THEN REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN
  DISCH_THEN(fun th -> FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN
  ASM_REWRITE_TAC[SPTAUX_SUM_add_pause; MAP; SUM; o_THM; SND; spt_size_def] THEN
  (SUBGOAL_THEN `spt_size (combin_K 0) (spt_left (b:A spt)) +
                 spt_size (combin_K 0) (spt_right b) < spt_size (combin_K 0) b \/ b = LN`
     MP_TAC THENL [ASM_MESON_TAC[SPTAUX_spt_size_left_right]; ALL_TAC]) THEN
  ASM_CASES_TAC `repeat2:bool` THEN ASM_CASES_TAC `repeat:bool` THEN
  ASM_REWRITE_TAC[spt_distinct] THEN ARITH_TAC);;

(* The kit loses the if-condition of the HOL4 form (a let-tuple over the    *)
(* call of spts_to_alist_aux) in the termination condition, so the function *)
(* is defined with projections and the HOL4 equation is derived below.      *)

let SPTAUX_spts_to_alist_eqn = cake_def_wf
  `MEASURE (\p:num#(num#A spt)list#(num#A)list.
              SUM (MAP (spt_size (combin_K 0) o SND) (FST (SND p))))`
  (REWRITE_TAC(FST::SND::WF_REL_THMS) THEN REPEAT GEN_TAC THEN
   STRIP_TAC THEN TRY GEN_TAC THEN
   MP_TAC(ISPECL [`i:num`; `xs:(num#A spt)list`; `acc_cent:(num#A)list`;
                  `[]:(num#A spt)list`; `[]:(num#A spt)list`; `F`]
          spts_to_alist_aux_size) THEN
   REWRITE_TAC[LET_DEF; LET_END_DEF; o_THM; APPEND_NIL] THEN
   DISCH_THEN(MP_TAC o SPECL
     [`FST (spts_to_alist_aux i (xs:(num#A spt)list) acc_cent [] [] F)`;
      `FST (SND (spts_to_alist_aux i (xs:(num#A spt)list) acc_cent [] [] F))`;
      `FST (SND (SND (spts_to_alist_aux i (xs:(num#A spt)list) acc_cent
                        [] [] F)))`;
      `SND (SND (SND (spts_to_alist_aux i (xs:(num#A spt)list) acc_cent
                        [] [] F)))`]) THEN
   ASM_REWRITE_TAC[PAIR] THEN ARITH_TAC)
  `spts_to_alist i (xs:(num#A spt)list) (acc_cent:(num#A)list) =
     if SND (SND (SND (spts_to_alist_aux i xs acc_cent [] [] F)))
     then spts_to_alist (FST (spts_to_alist_aux i xs acc_cent [] [] F))
            (FST (SND (spts_to_alist_aux i xs acc_cent [] [] F)))
            (FST (SND (SND (spts_to_alist_aux i xs acc_cent [] [] F))))
     else REVERSE (FST (SND (SND (spts_to_alist_aux i xs acc_cent [] [] F))))`;;

let spts_to_alist_def = prove
 (`spts_to_alist i (xs:(num#A spt)list) (acc_cent:(num#A)list) =
     pair_CASE (spts_to_alist_aux i xs acc_cent [] [] F)
       (\i r. pair_CASE r (\xs r. pair_CASE r (\acc_cent repeat.
          if repeat then spts_to_alist i xs acc_cent
          else REVERSE acc_cent)))`,
  GEN_REWRITE_TAC LAND_CONV [SPTAUX_spts_to_alist_eqn] THEN
  SPEC_TAC(`spts_to_alist_aux i (xs:(num#A spt)list) acc_cent [] [] F`,
           `p:num#(num#A spt)list#(num#A)list#bool`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; pair_CASE; FST; SND]);;

let toSortedAList_def = new_definition
  `toSortedAList (spt:A spt) = spts_to_alist 0 [(1,spt)] []`;;

(* list lemmas (COUNT_LIST, ZIP, ALOOKUP), proved here for local use *)

let SPTAUX_LENGTH_COUNT_LIST = prove
 (`!n. LENGTH (COUNT_LIST n) = n`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[COUNT_LIST_DEF; LENGTH; LENGTH_MAP]);;

let SPTAUX_ALOOKUP_ZIP_MAP_SUC = prove
 (`!c (t:A list). LENGTH c = LENGTH t ==>
     ALOOKUP (ZIP (MAP SUC c) t) 0 = NONE /\
     !n. ALOOKUP (ZIP (MAP SUC c) t) (SUC n) = ALOOKUP (ZIP c t) n`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ; MAP; ZIP; ALOOKUP_DEF; NOT_SUC] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `t':A list`) THEN
  ASM_SIMP_TAC[FST; SND; SUC_INJ]);;

let SPTAUX_ALOOKUP_ZIP_COUNT_LIST = prove
 (`!l:A list n.
     ALOOKUP (ZIP (COUNT_LIST (LENGTH l)) l) n =
     if n < LENGTH l then SOME (EL n l) else NONE`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; COUNT_LIST_DEF; ZIP; ALOOKUP_DEF; CONJUNCT1 LT] THEN
  INDUCT_TAC THEN
  ASM_SIMP_TAC[FST; SND; ARITH_RULE `~(0 = SUC n)`; EL; HD; TL;
               SPTAUX_ALOOKUP_ZIP_MAP_SUC; LENGTH_MAP; SPTAUX_LENGTH_COUNT_LIST;
               LT_SUC; LT_0]);;

let fromList_fromAList = prove
 (`!l:A list. fromList l = fromAList (ZIP (COUNT_LIST (LENGTH l)) l)`,
  GEN_TAC THEN SIMP_TAC[spt_eq_thm; wf_fromList; wf_fromAList] THEN
  REWRITE_TAC[lookup_fromList; lookup_fromAList; SPTAUX_ALOOKUP_ZIP_COUNT_LIST]);;

(* ========================================================================= *)
(* spt_closure: port of HOL4 examples/algorithms/spt_closureScript.sml:     *)
(* the closure of a set of nodes under the edges of a num_set num_map.       *)
(* ========================================================================= *)

let num_set_tree_union_def = cake_def
  `(num_set_tree_union LN t2 = t2:(1 spt)spt) /\
   (num_set_tree_union (LS a) t =
      spt_CASE t (LS a) (\b. LS (sptree_union a b)) (\t1 t2. BS t1 a t2)
                 (\t1 b t2. BS t1 (sptree_union a b) t2)) /\
   (num_set_tree_union (BN t1 t2) t =
      spt_CASE t (BN t1 t2) (\a. BS t1 a t2)
        (\t1' t2'. BN (num_set_tree_union t1 t1') (num_set_tree_union t2 t2'))
        (\t1' a t2'.
           BS (num_set_tree_union t1 t1') a (num_set_tree_union t2 t2'))) /\
   (num_set_tree_union (BS t1 a t2) t =
      spt_CASE t (BS t1 a t2) (\b. BS t1 (sptree_union a b) t2)
        (\t1' t2'.
           BS (num_set_tree_union t1 t1') a (num_set_tree_union t2 t2'))
        (\t1' b t2'.
           BS (num_set_tree_union t1 t1') (sptree_union a b)
              (num_set_tree_union t2 t2')))`;;

let SPTAUX_EXISTS_lookup_P = prove
 (`(!P. (?k v. lookup k (LN:A spt) = SOME v /\ P v) <=> F) /\
   (!P (a:A). (?k v. lookup k (LS a) = SOME v /\ P v) <=> P a) /\
   (!P t1 t2:A spt. (?k v. lookup k (BN t1 t2) = SOME v /\ P v) <=>
                    (?k v. lookup k t1 = SOME v /\ P v) \/
                    (?k v. lookup k t2 = SOME v /\ P v)) /\
   (!P (a:A) t1 t2. (?k v. lookup k (BS t1 a t2) = SOME v /\ P v) <=>
                    P a \/ (?k v. lookup k t1 = SOME v /\ P v) \/
                    (?k v. lookup k t2 = SOME v /\ P v))`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [SPTAUX_EXISTS_BITS] THEN
  REWRITE_TAC[lookup_rwts; SPTAUX_lookup_bits; option_DISTINCT; option_INJ;
              UNWIND_THM1; UNWIND_THM2] THEN
  MESON_TAC[]);;

let domain_spt_fold_union = prove
 (`!tree:(A spt)spt y.
     domain (spt_fold sptree_union y tree) =
     domain y UNION
     {n | ?k aSet. lookup k tree = SOME aSet /\ n IN domain aSet}`,
  MATCH_MP_TAC spt_INDUCT THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[spt_fold_def; domain_union] THEN
  REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM] THEN X_GEN_TAC `n:num` THEN
  REWRITE_TAC[SPTAUX_EXISTS_lookup_P] THEN MESON_TAC[]);;

let SPTAUX_closure_spt_size = prove
 (`!(reachable:1 spt) (tree:(1 spt)spt).
     ~subspt (spt_fold sptree_union LN (sptree_inter tree reachable)) reachable
     ==> sptree_size (difference (spt_fold sptree_union LN tree)
                (sptree_union reachable (spt_fold sptree_union LN (sptree_inter tree reachable)))) <
         sptree_size (difference (spt_fold sptree_union LN tree) reachable)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[subspt_domain; SUBSET; NOT_FORALL_THM; NOT_IMP] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:num` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC size_diff_less THEN EXISTS_TAC `t:num` THEN
  ASM_REWRITE_TAC[domain_union; IN_UNION; SUBSET] THEN
  UNDISCH_TAC
   `t IN domain (spt_fold sptree_union LN (sptree_inter (tree:(1 spt)spt) (reachable:1 spt)))` THEN
  REWRITE_TAC[domain_spt_fold_union; domain_def; IN_UNION; NOT_IN_EMPTY;
              IN_ELIM_THM; lookup_inter_EQ] THEN
  MESON_TAC[]);;

let closure_spt_def = cake_def_wf
  `MEASURE (\p:(1 spt)#((1 spt)spt).
              sptree_size (difference (spt_fold sptree_union LN (SND p)) (FST p)))`
  (REWRITE_TAC(FST::SND::WF_REL_THMS) THEN REPEAT GEN_TAC THEN
   DISCH_THEN(ASSUME_TAC o MATCH_MP SPTAUX_closure_spt_size) THEN
   GEN_TAC THEN POP_ASSUM MP_TAC THEN ARITH_TAC)
  `closure_spt (reachable:1 spt) (tree:(1 spt)spt) =
     let sets = sptree_inter tree reachable in
     let nodes = spt_fold sptree_union LN sets in
     if subspt nodes reachable then reachable
     else closure_spt (sptree_union reachable nodes) tree`;;


(* the kit stores no induction theorem for closure_spt: proved directly *)

let closure_spt_ind = prove
 (`!P. (!(reachable:1 spt) (tree:(1 spt)spt).
          (!sets nodes. sets = sptree_inter tree reachable /\
                        nodes = spt_fold sptree_union LN sets /\
                        ~subspt nodes reachable
                        ==> P (sptree_union reachable nodes) tree)
          ==> P reachable tree)
       ==> !v v1. P v v1`,
  GEN_TAC THEN DISCH_THEN(LABEL_TAC "H") THEN
  SUBGOAL_THEN `!p:(1 spt)#((1 spt)spt). P (FST p) (SND p)`
    (fun th -> REPEAT GEN_TAC THEN
               MP_TAC(ISPEC `(v:1 spt,v1:(1 spt)spt)` th) THEN
               REWRITE_TAC[]) THEN
  MATCH_MP_TAC(REWRITE_RULE[WF_IND]
    (ISPEC `\p:(1 spt)#((1 spt)spt).
              sptree_size (difference (spt_fold sptree_union LN (SND p)) (FST p))`
           WF_MEASURE)) THEN
  X_GEN_TAC `p:(1 spt)#((1 spt)spt)` THEN DISCH_THEN(LABEL_TAC "IH") THEN
  USE_THEN "H" MATCH_MP_TAC THEN REPEAT STRIP_TAC THEN
  USE_THEN "IH" (MP_TAC o SPEC `(sptree_union (FST (p:(1 spt)#((1 spt)spt))) nodes,
                                SND p)`) THEN
  REWRITE_TAC[MEASURE] THEN DISCH_THEN MATCH_MP_TAC THEN RVEQ_TAC THEN
  ASM_SIMP_TAC[SPTAUX_closure_spt_size]);;

let is_adjacent_def = new_definition
  `is_adjacent (tree:(1 spt)spt) x y <=>
     ?aSetx. (lookup x tree = SOME aSetx) /\ (lookup y aSetx = SOME one)`;;

let is_reachable_def = new_definition
  `is_reachable (tree:(1 spt)spt) = RTC (is_adjacent tree)`;;

let num_set_tree_union_empty = prove
 (`!t1 t2. (num_set_tree_union t1 t2 = LN) <=> (t1 = LN /\ t2 = LN)`,
  REPEAT GEN_TAC THEN
  SPTAUX_CASES_TAC `t1:(1 spt)spt` THEN SPTAUX_CASES_TAC `t2:(1 spt)spt` THEN
  REWRITE_TAC[num_set_tree_union_def; spt_CASE; spt_distinct]);;

let wf_num_set_tree_union = prove
 (`!t1 t2 (result:(1 spt)spt). sptree_wf t1 /\ sptree_wf t2 ==> sptree_wf (num_set_tree_union t1 t2)`,
  MATCH_MP_TAC spt_INDUCT THEN REPEAT STRIP_TAC THEN
  SPTAUX_CASES_TAC `t2:(1 spt)spt` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[sptree_wf_def]) THEN
  ASM_SIMP_TAC[num_set_tree_union_def; spt_CASE; sptree_wf_def;
               num_set_tree_union_empty] THEN
  ASM_MESON_TAC[]);;

let domain_num_set_tree_union = prove
 (`!t1 t2. domain (num_set_tree_union t1 t2) = domain t1 UNION domain t2`,
  MATCH_MP_TAC spt_INDUCT THEN REPEAT STRIP_TAC THEN
  SPTAUX_CASES_TAC `t2:(1 spt)spt` THEN
  ASM_REWRITE_TAC[num_set_tree_union_def; spt_CASE; domain_def] THEN
  SET_TAC[]);;

let num_set_tree_union_sym = prove
 (`!t1 t2. num_set_tree_union t1 t2 = num_set_tree_union t2 t1`,
  MATCH_MP_TAC spt_INDUCT THEN REPEAT STRIP_TAC THEN
  SPTAUX_CASES_TAC `t2:(1 spt)spt` THEN
  ASM_REWRITE_TAC[num_set_tree_union_def; spt_CASE] THEN
  MESON_TAC[union_num_set_sym]);;

let lookup_num_set_tree_union = prove
 (`!t1 t2 n.
     lookup n (num_set_tree_union t1 t2) =
     option_CASE (lookup n t1) (lookup n t2)
       (\x. option_CASE (lookup n t2) (SOME x) (\y. SOME (sptree_union x y)))`,
  MATCH_MP_TAC spt_INDUCT THEN REPEAT STRIP_TAC THEN
  SPTAUX_CASES_TAC `t2:(1 spt)spt` THEN SPTAUX_BITS_TAC `n:num` THEN
  ASM_REWRITE_TAC[num_set_tree_union_def; spt_CASE; lookup_rwts;
                  SPTAUX_lookup_bits; option_CASE; SPTAUX_optcase_lemma]);;

let SPTAUX_FORALL_lookup_P = prove
 (`(!P. (!k v. lookup k (LN:A spt) = SOME v ==> P v) <=> T) /\
   (!P (a:A). (!k v. lookup k (LS a) = SOME v ==> P v) <=> P a) /\
   (!P t1 t2:A spt. (!k v. lookup k (BN t1 t2) = SOME v ==> P v) <=>
                    (!k v. lookup k t1 = SOME v ==> P v) /\
                    (!k v. lookup k t2 = SOME v ==> P v)) /\
   (!P (a:A) t1 t2. (!k v. lookup k (BS t1 a t2) = SOME v ==> P v) <=>
                    P a /\ (!k v. lookup k t1 = SOME v ==> P v) /\
                    (!k v. lookup k t2 = SOME v ==> P v))`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [SPTAUX_FORALL_BITS] THEN
  REWRITE_TAC[lookup_rwts; SPTAUX_lookup_bits; option_DISTINCT; option_INJ;
              FORALL_UNWIND_THM1; FORALL_UNWIND_THM2] THEN
  MESON_TAC[]);;

let wf_spt_fold_union = prove
 (`!tree:(A spt)spt y.
     (!n x. (lookup n tree = SOME x) ==> sptree_wf x) /\ sptree_wf y
     ==> sptree_wf (spt_fold sptree_union y tree)`,
  MATCH_MP_TAC spt_INDUCT THEN
  REWRITE_TAC[spt_fold_def; SPTAUX_FORALL_lookup_P] THEN
  REPEAT STRIP_TAC THEN ASM_MESON_TAC[wf_union]);;

let wf_closure_spt = prove
 (`!reachable tree.
     sptree_wf reachable /\ (!n x. lookup n tree = SOME x ==> sptree_wf x)
     ==> sptree_wf (closure_spt reachable tree)`,
  MATCH_MP_TAC closure_spt_ind THEN REPEAT GEN_TAC THEN
  DISCH_TAC THEN STRIP_TAC THEN ONCE_REWRITE_TAC[closure_spt_def] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
    [`sptree_inter (tree:(1 spt)spt) (reachable:1 spt)`;
     `spt_fold sptree_union LN (sptree_inter (tree:(1 spt)spt) (reachable:1 spt))`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC wf_union THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC wf_spt_fold_union THEN REWRITE_TAC[wf_LN; lookup_inter_EQ] THEN
  ASM_MESON_TAC[]);;

let adjacent_domain = prove
 (`!tree x y. is_adjacent tree x y ==> x IN domain tree`,
  REWRITE_TAC[is_adjacent_def; domain_lookup] THEN MESON_TAC[]);;

let reachable_domain = prove
 (`!tree x y. is_reachable tree x y ==> (x = y \/ x IN domain tree)`,
  GEN_TAC THEN REWRITE_TAC[is_reachable_def] THEN
  MATCH_MP_TAC RTC_INDUCT_L THEN MESON_TAC[adjacent_domain]);;

let reachable_LHS_NOTIN = prove
 (`!tree n x. is_reachable tree n x /\ ~(n IN domain tree) ==> n = x`,
  REWRITE_TAC[is_reachable_def] THEN ONCE_REWRITE_TAC[RTC_CASES_R] THEN
  MESON_TAC[adjacent_domain]);;

let rtc_is_adjacent = prove
 (`(!k. k IN t ==> !n. (is_adjacent fullTree k n ==> n IN t)) ==>
   !x y. RTC (is_adjacent fullTree) x y ==> x IN t ==> y IN t`,
  DISCH_TAC THEN MATCH_MP_TAC RTC_INDUCT_L THEN ASM_MESON_TAC[]);;

let is_adjacent_num_set_tree_union = prove
 (`!t1 t2 n m. is_adjacent t1 n m ==> is_adjacent (num_set_tree_union t1 t2) n m`,
  REWRITE_TAC[is_adjacent_def; lookup_num_set_tree_union] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[option_CASE] THEN
  SPTAUX_CASES_TAC `lookup n (t2:(1 spt)spt)` THEN
  REWRITE_TAC[option_CASE; option_INJ; UNWIND_THM1] THEN
  ASM_REWRITE_TAC[lookup_union; option_CASE]);;

let is_reachable_num_set_tree_union = prove
 (`!t1 t2 n m. is_reachable t1 n m
               ==> is_reachable (num_set_tree_union t1 t2) n m`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[is_reachable_def] THEN
  MATCH_MP_TAC RTC_MONO THEN REWRITE_TAC[is_adjacent_num_set_tree_union]);;

let closure_spt_lemma = prove
 (`!reachable tree closure (roots:num->bool).
     closure_spt reachable tree = closure /\
     roots SUBSET domain reachable /\
     (!k. k IN domain reachable ==> ?n. n IN roots /\ is_reachable tree n k)
     ==> domain closure = {a | ?n. n IN roots /\ is_reachable tree n a}`,
  MATCH_MP_TAC closure_spt_ind THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[closure_spt_def] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN COND_CASES_TAC THENL
   [STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `a:num` THEN
    EQ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `!x y. RTC (is_adjacent tree) x y ==> x IN domain (reachable:1 spt)
            ==> y IN domain reachable`
     (fun th -> ASM_MESON_TAC[th; is_reachable_def; SUBSET]) THEN
    MATCH_MP_TAC rtc_is_adjacent THEN
    UNDISCH_TAC
     `subspt (spt_fold sptree_union LN (sptree_inter (tree:(1 spt)spt) (reachable:1 spt)))
             reachable` THEN
    REWRITE_TAC[subspt_domain; SUBSET; domain_spt_fold_union; domain_def;
                IN_UNION; NOT_IN_EMPTY; IN_ELIM_THM; is_adjacent_def;
                lookup_inter_alt] THEN
    REWRITE_TAC[domain_lookup] THEN MESON_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
    [`sptree_inter (tree:(1 spt)spt) (reachable:1 spt)`;
     `spt_fold sptree_union LN (sptree_inter (tree:(1 spt)spt) (reachable:1 spt))`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[domain_union] THEN CONJ_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `k:num` THEN REWRITE_TAC[IN_UNION] THEN
  STRIP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC
   `k IN domain (spt_fold sptree_union LN (sptree_inter (tree:(1 spt)spt) (reachable:1 spt)))` THEN
  REWRITE_TAC[domain_spt_fold_union; domain_def; IN_UNION; NOT_IN_EMPTY;
              IN_ELIM_THM; lookup_inter_alt] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `k' IN domain (reachable:1 spt)` ASSUME_TAC THENL
   [ASM_MESON_TAC[option_DISTINCT]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k':num` o check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `n:num` THEN STRIP_TAC THEN ASM_REWRITE_TAC[is_reachable_def] THEN
  MATCH_MP_TAC RTC_TRANS_L THEN EXISTS_TAC `k':num` THEN
  ASM_REWRITE_TAC[GSYM is_reachable_def; is_adjacent_def] THEN
  EXISTS_TAC `aSet:1 spt` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[domain_lookup; EXISTS_ONE_THM]) THEN
  ASM_MESON_TAC[option_DISTINCT]);;

let closure_spt_thm = prove
 (`!tree start.
     domain (closure_spt start tree) =
     {a | ?n. n IN domain start /\ is_reachable tree n a}`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC closure_spt_lemma THEN
  EXISTS_TAC `start:1 spt` THEN REWRITE_TAC[SUBSET_REFL] THEN
  MESON_TAC[is_reachable_def; RTC_REFL]);;

(* ------------------------------------------------------------------------- *)
(* The HOL4 [simp] theorems of sptree, for SIMP/FS/GVS/RW; isEmpty_def      *)
(* because HOL4's isEmpty is an abbreviation of t = LN.                      *)
(* ------------------------------------------------------------------------- *)

let _ = cake_add_simps
  [isEmpty_def; lookup_rwts; sptree_size_def; insert_notEmpty; lookup_insert1;
   isEmpty_union; wf_inter; domain_def; FINITE_domain; domain_union;
   domain_inter; domain_insert; domain_difference; domain_delete; mapi0_def;
   LENGTH_toAList; wf_mk_wf; wf_mk_id; lookup_mk_wf; domain_mk_wf; mk_wf_eq;
   inter_eq; union_mk_wf; inter_mk_wf; insert_mk_wf; delete_mk_wf; union_LN;
   inter_LN; fromAList_def; sptree_map_def; domain_map; map_LN; wf_map; subspt_refl;
   subspt_LN; subspt_union; domain_mapi; map_map_K; wf_LN; wf_fromList;
   wf_list_to_num_set; size_map; size_mapi; size_fromList];;
