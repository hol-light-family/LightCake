(* ========================================================================= *)
(* alist_tree: port of HOL4 src/finite_maps/alist_treeScript.sml (the HOL4  *)
(* library theory used by CakeML v3479's translator).  Definitions and      *)
(* theorems that support automation (the Lib file) for fast insertion and   *)
(* lookup into association lists (alists).                                  *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - The statements keep HOL4's quantifiers and free variables: HOL4's       *)
(*   alist_treeLib instantiates the free l and r of is_insert_l, is_insert_r,*)
(*   is_insert_centre, is_lookup_l and is_lookup_r by name.                  *)
(* - HOL4's ++ is left associative: xs ++ al ++ ys is                        *)
(*   APPEND (APPEND xs al) ys.                                               *)
(* - HOL4's HD_APPEND, LAST_APPEND and DISJ_EQ_IMP are alist_tree_HD_APPEND,*)
(*   alist_tree_LAST_APPEND and alist_tree_DISJ_EQ_IMP (HOL Light and the   *)
(*   library bind those names, the first two to the same statements).        *)
(* - is_insert_centre is HOL4's derived form (is_insert_centre_rule with fl  *)
(*   and fr set to T and simplified under the antecedents), proved directly. *)
(* ========================================================================= *)

needs "hol4/list.ml";;
needs "hol4/alist.ml";;
needs "hol4/sorting.ml";;

type_invention_error := true;;

(* key property: a partial function f can be represented by an assoc list  *)
(* al which is known to be sorted according to R                            *)
let sorted_alist_repr_def = cake_def
  `sorted_alist_repr (R:A->A->bool) (al:(A#B)list) f <=>
     SORTED R (MAP FST al) /\ irreflexive R /\ transitive R /\ f = ALOOKUP al`;;

(* inserts on sorted alists *)

let count_append_def = cake_def
  `count_append (n:num) (xs:A list) ys = APPEND xs ys`;;

let is_insert_def = cake_def
  `is_insert frame_l frame_r (R:A->A->bool) k (x:B) al al' <=>
     irreflexive R /\ transitive R ==>
       SORTED R (MAP FST al) ==>
         ALOOKUP al' = ALOOKUP (CONS (k,x) al) /\
         (frame_l ==> ~(al = []) /\ FST (HD al') = FST (HD al)) /\
         (frame_r ==> ~(al = []) /\ FST (LAST al') = FST (LAST al)) /\
         SORTED R (MAP FST al')`;;

(* HOL4: HD_APPEND (HOL Light's HD_APPEND, with HOL4's free variables) *)
let alist_tree_HD_APPEND = prove
 (`HD (APPEND xs ys) = if xs = [] then HD ys else HD (xs:A list)`,
  REWRITE_TAC[HD_APPEND]);;

(* HOL4: LAST_APPEND (HOL Light's LAST_APPEND) *)
let alist_tree_LAST_APPEND = prove
 (`LAST (APPEND xs ys) = if ys = [] then LAST xs else LAST (ys:A list)`,
  REWRITE_TAC[LAST_APPEND]);;

let HD_MAP = prove
 (`~(xs = []) ==> HD (MAP (f:A->B) xs) = f (HD xs)`,
  CASES_ON `xs:A list` THEN REWRITE_TAC[MAP; HD; NOT_CONS_NIL]);;

let HD_MEM = prove
 (`~(xs = []) ==> MEM (HD xs) (xs:A list)`,
  CASES_ON `xs:A list` THEN REWRITE_TAC[MEM; HD; NOT_CONS_NIL]);;

let is_insert_l = prove
 (`!n. is_insert fl T (R:A->A->bool) k (x:B) l l' ==>
       is_insert fl T R k x (count_append n l r) (count_append ARB l' r)`,
  GEN_TAC THEN REWRITE_TAC[is_insert_def; count_append_def; MAP_APPEND; SORTED_APPEND_GEN] THEN
  DISCH_THEN (LABEL_TAC "H") THEN DISCH_TAC THEN
  DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  REMOVE_THEN "H" MP_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(l':(A#B)list = [])` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `ALOOKUP (l':(A#B)list) = ALOOKUP (CONS (k,x) l)` THEN
    ASM_REWRITE_TAC[FUN_EQ_THM; ALOOKUP_def] THEN DISCH_THEN (MP_TAC o SPEC `k:A`) THEN
    SIMP[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[APPEND_EQ_NIL; HD_APPEND; LAST_APPEND; FUN_EQ_THM; ALOOKUP_APPEND;
                  ALOOKUP_def] THEN
  REPEAT CONJ_TAC THENL
   [GEN_TAC THEN COND_CASES_TAC THEN SIMP[];
    ASM_MESON_TAC[];
    COND_CASES_TAC THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `MAP FST (l:(A#B)list) = [] \/ MAP FST (r:(A#B)list) = [] \/
                 R (LAST (MAP FST l)) (HD (MAP FST r))` THEN
    ASM_SIMP_TAC[LAST_MAP; MAP_EQ_NIL]]);;

let insert_fl_R = prove
 (`is_insert fl fr (R:A->A->bool) k (x:B) al al' ==> fl ==> SORTED R (MAP FST al)
   ==> irreflexive R /\ transitive R
   ==> (k = FST (HD al)) \/ R (HD (MAP FST al)) k`,
  REWRITE_TAC[is_insert_def] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM (MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `MEM (k:A) (MAP FST (al':(A#B)list))` MP_TAC THENL
   [REWRITE_TAC[MEM_MAP] THEN EXISTS_TAC `(k:A,x:B)` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC ALOOKUP_MEM THEN ASM_REWRITE_TAC[ALOOKUP_def]; ALL_TAC] THEN
  ASM_SIMP_TAC[HD_MAP] THEN
  UNDISCH_TAC `FST (HD (al':(A#B)list)) = FST (HD (al:(A#B)list))` THEN
  UNDISCH_TAC `SORTED (R:A->A->bool) (MAP FST (al':(A#B)list))` THEN
  CASES_ON `al':(A#B)list` THEN REWRITE_TAC[MAP; MEM; HD] THEN
  ASM_SIMP_TAC[SORTED_EQ] THEN MESON_TAC[]);;

let insert_fl_R_append = prove
 (`is_insert T fr (R:A->A->bool) k (x:B) r r'
   ==> SORTED R (MAP FST (APPEND l r))
   ==> irreflexive R /\ transitive R
   ==> ~MEM k (MAP FST (l:(A#B)list))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `SORTED R (MAP FST (r:(A#B)list)) /\
                (!a b. MEM a (MAP FST (l:(A#B)list)) ==> MEM b (MAP FST r) ==> R a b)`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `SORTED (R:A->A->bool) (MAP FST (APPEND l (r:(A#B)list)))` THEN
    ASM_SIMP_TAC[MAP_APPEND; SORTED_APPEND]; ALL_TAC] THEN
  SUBGOAL_THEN `~(r:(A#B)list = [])` ASSUME_TAC THENL
   [UNDISCH_TAC `is_insert T fr (R:A->A->bool) k (x:B) r r'` THEN
    ASM_REWRITE_TAC[is_insert_def] THEN MESON_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM (MP_TAC o MATCH_MP insert_fl_R) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `FST (HD r) = HD (MAP FST (r:(A#B)list))` SUBST1_TAC THENL
   [ASM_SIMP_TAC[HD_MAP]; ALL_TAC] THEN
  SUBGOAL_THEN `MEM (HD (MAP FST r)) (MAP FST (r:(A#B)list))` ASSUME_TAC THENL
   [ASM_MESON_TAC[HD_MEM; MAP_EQ_NIL]; ALL_TAC] THEN
  RULE_ASSUM_TAC (REWRITE_RULE[irreflexive_DEF; transitive_DEF]) THEN ASM_MESON_TAC[]);;

let is_insert_r = prove
 (`!n. is_insert T fr (R:A->A->bool) k (x:B) r r' ==>
       is_insert T fr R k x (count_append n l r) (count_append ARB l r')`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM (MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] insert_fl_R_append)) THEN
  UNDISCH_TAC `is_insert T fr (R:A->A->bool) k (x:B) r r'` THEN
  REWRITE_TAC[is_insert_def; count_append_def; MAP_APPEND; SORTED_APPEND_GEN] THEN
  DISCH_THEN (LABEL_TAC "H") THEN DISCH_THEN (LABEL_TAC "M") THEN DISCH_TAC THEN
  DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  REMOVE_THEN "M" MP_TAC THEN
  ASM_REWRITE_TAC[MAP_APPEND; SORTED_APPEND_GEN] THEN DISCH_TAC THEN
  REMOVE_THEN "H" MP_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(r':(A#B)list = [])` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `ALOOKUP (r':(A#B)list) = ALOOKUP (CONS (k,x) r)` THEN
    ASM_REWRITE_TAC[FUN_EQ_THM; ALOOKUP_def] THEN DISCH_THEN (MP_TAC o SPEC `k:A`) THEN
    SIMP[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[APPEND_EQ_NIL; HD_APPEND; LAST_APPEND; FUN_EQ_THM; ALOOKUP_APPEND;
                  ALOOKUP_def] THEN
  REPEAT CONJ_TAC THENL
   [GEN_TAC THEN COND_CASES_TAC THEN SIMP[] THEN
    FIRST_X_ASSUM (SUBST_ALL_TAC o SYM) THEN
    RULE_ASSUM_TAC (REWRITE_RULE[GSYM ALOOKUP_NONE]) THEN ASM_REWRITE_TAC[] THEN SIMP[];
    COND_CASES_TAC THEN ASM_REWRITE_TAC[];
    ASM_MESON_TAC[];
    UNDISCH_TAC `MAP FST (l:(A#B)list) = [] \/ MAP FST (r:(A#B)list) = [] \/
                 R (LAST (MAP FST l)) (HD (MAP FST r))` THEN
    ASM_SIMP_TAC[HD_MAP; MAP_EQ_NIL]]);;

let is_insert_to_empty = prove
 (`!(R:A->A->bool) k (x:B). is_insert F F R k x [] [(k, x)]`,
  REWRITE_TAC[is_insert_def; MAP; SORTED_DEF]);;

let is_insert_overwrite = prove
 (`!(R:A->A->bool) k (x:B) v. (FST v = k) ==> is_insert T T R k x [v] [(k, x)]`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[is_insert_def; MAP; SORTED_DEF; HD; LAST; NOT_CONS_NIL; FUN_EQ_THM;
              ALOOKUP_def] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[]);;

let sorted_fst_insert_centre = prove
 (`!k. SORTED R (APPEND (MAP FST l) (MAP FST r)) ==>
       (~(l = []) ==> R (FST (LAST l)) k) ==>
       (~(r = []) ==> R k (FST (HD r))) ==>
       SORTED R (APPEND (MAP FST (l:(A#B)list)) (CONS k (MAP FST (r:(A#B)list))))`,
  GEN_TAC THEN REWRITE_TAC[SORTED_APPEND_GEN; MAP_EQ_NIL; NOT_CONS_NIL; HD] THEN
  ASM_CASES_TAC `l:(A#B)list = []` THEN ASM_SIMP_TAC[LAST_MAP] THEN
  ASM_CASES_TAC `r:(A#B)list = []` THEN ASM_SIMP_TAC[HD_MAP; LSORTAUX_SORTED_CONS; MAP_EQ_NIL] THEN
  REWRITE_TAC[MAP; SORTED_DEF]);;

let is_insert_centre_rule = prove
 (`(fl ==> ~(l = [])) ==> (~(l = []) ==> R (FST (LAST l)) k) ==>
   (fr ==> ~(r = [])) ==> (~(r = []) ==> R k (FST (HD r))) ==>
   is_insert fl fr (R:A->A->bool) k (x:B) (count_append n l r)
     (count_append ARB l (count_append ARB [(k, x)] r))`,
  REPEAT DISCH_TAC THEN REWRITE_TAC[is_insert_def; count_append_def] THEN
  STRIP_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `SORTED (R:A->A->bool)
                  (APPEND (MAP FST (l:(A#B)list)) (CONS k (MAP FST (r:(A#B)list))))`
    ASSUME_TAC THENL
   [IRULE sorted_fst_insert_centre THEN ASM_REWRITE_TAC[GSYM MAP_APPEND];
    ALL_TAC] THEN
  SUBGOAL_THEN `~MEM (k:A) (MAP FST (l:(A#B)list))` ASSUME_TAC THENL
   [UNDISCH_TAC `SORTED (R:A->A->bool)
                  (APPEND (MAP FST (l:(A#B)list)) (CONS k (MAP FST (r:(A#B)list))))` THEN
    ASM_SIMP_TAC[SORTED_APPEND; MEM] THEN
    RULE_ASSUM_TAC (REWRITE_RULE[irreflexive_DEF]) THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[MAP_APPEND; MAP; APPEND] THEN
  ASM_REWRITE_TAC[APPEND_EQ_NIL; HD_APPEND; LAST_APPEND; NOT_CONS_NIL; FUN_EQ_THM;
                  ALOOKUP_APPEND; ALOOKUP_def; LAST; HD] THEN
  REPEAT CONJ_TAC THENL
   [GEN_TAC THEN COND_CASES_TAC THEN SIMP[] THEN
    FIRST_X_ASSUM (SUBST_ALL_TAC o SYM) THEN
    RULE_ASSUM_TAC (REWRITE_RULE[GSYM ALOOKUP_NONE]) THEN ASM_REWRITE_TAC[] THEN SIMP[];
    DISCH_TAC THEN ASM_MESON_TAC[];
    DISCH_TAC THEN ASM_MESON_TAC[]]);;

(* HOL4: is_insert_centre_rule with fl and fr generalised, then T and T,  *)
(* simplified (bool_ss, which rewrites under the antecedents)              *)
let is_insert_centre = prove
 (`!(R:A->A->bool) n k (x:B).
     ~(l = []) ==> R (FST (LAST l)) k ==> ~(r = []) ==> R k (FST (HD r)) ==>
     is_insert T T R k x (count_append n l r)
       (count_append ARB l (count_append ARB [(k, x)] r))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC (REWRITE_RULE[IMP_IMP] is_insert_centre_rule) THEN
  ASM_REWRITE_TAC[]);;

let is_insert_far_left = prove
 (`!(R:A->A->bool) k (x:B) xs. ~(xs = []) ==> R k (FST (HD xs)) ==>
     is_insert F T R k x xs (count_append ARB [(k, x)] xs)`,
  REPEAT GEN_TAC THEN CASES_ON `xs:(A#B)list` THEN
  REWRITE_TAC[is_insert_def; count_append_def; NOT_CONS_NIL; APPEND; MAP; HD; LAST;
              SORTED_DEF] THEN
  SIMP[]);;

let is_insert_far_right = prove
 (`!(R:A->A->bool) k (x:B) xs. ~(xs = []) ==> R (FST (LAST xs)) k ==>
     is_insert T F R k x xs (count_append ARB xs [(k, x)])`,
  REPEAT STRIP_TAC THEN
  MP_TAC (INST [`T`,`fl:bool`; `F`,`fr:bool`; `[]:(A#B)list`,`r:(A#B)list`;
                `xs:(A#B)list`,`l:(A#B)list`] is_insert_centre_rule) THEN
  ASM_REWRITE_TAC[is_insert_def; count_append_def; APPEND_NIL]);;

(* bookkeeping and balancing count_append trees *)

let count_append_HD_LAST = prove
 (`(HD (count_append i (count_append j xs ys) zs) =
    HD (count_append 0 xs (count_append 0 ys (zs:A list)))) /\
   (HD (count_append i (CONS x xs) ys) = x) /\
   (HD (count_append i [] ys) = HD ys) /\
   (LAST (count_append i xs (count_append j ys zs)) =
    LAST (count_append 0 (count_append 0 xs ys) zs)) /\
   (LAST (count_append i xs (CONS y ys)) = LAST (CONS y ys)) /\
   (LAST (count_append i xs []) = LAST xs) /\
   (HD (CONS x xs) = x) /\
   (LAST (CONS x (CONS y zs)) = LAST (CONS y zs)) /\
   (LAST [x] = x) /\
   ((count_append i (count_append j xs ys) zs = []) <=>
    (count_append 0 xs (count_append 0 ys zs) = [])) /\
   ((count_append i [] ys = []) <=> (ys = [])) /\
   ((count_append i (CONS x xs) ys = []) <=> F) /\
   ((CONS x xs = []) <=> F)`,
  REWRITE_TAC[count_append_def; APPEND; APPEND_ASSOC; APPEND_NIL; HD; LAST;
              LAST_APPEND; NOT_CONS_NIL]);;

let balance_r = prove
 (`count_append i (count_append j xs ys) zs =
   count_append ARB xs (count_append ARB ys (zs:A list))`,
  REWRITE_TAC[count_append_def; APPEND_ASSOC]);;

let balance_l = prove
 (`count_append i xs (count_append j ys zs) =
   count_append ARB (count_append ARB xs ys) (zs:A list)`,
  REWRITE_TAC[count_append_def; APPEND_ASSOC]);;

let set_count = prove
 (`!j. count_append i xs ys = count_append j xs (ys:A list)`,
  REWRITE_TAC[count_append_def]);;

(* reprs of various partial function constructions *)

let option_choice_f_def = cake_def
  `option_choice_f (f:A->B option) g = (\x. OPTION_CHOICE (f x) (g x))`;;

let alookup_append_option_choice_f = prove
 (`ALOOKUP (APPEND xs ys) = option_choice_f (ALOOKUP xs) (ALOOKUP (ys:(A#B)list))`,
  REWRITE_TAC[FUN_EQ_THM; option_choice_f_def; ALOOKUP_APPEND] THEN GEN_TAC THEN
  CASES_ON `ALOOKUP (xs:(A#B)list) x` THEN SIMP[OPTION_CHOICE_DEF]);;

let alookup_empty_option_choice_f = prove
 (`(option_choice_f (ALOOKUP []) f = f) /\
   (option_choice_f f (ALOOKUP []) = (f:A->B option))`,
  REWRITE_TAC[FUN_EQ_THM; option_choice_f_def; ALOOKUP_def; OPTION_CHOICE_DEF] THEN
  GEN_TAC THEN CASES_ON `(f:A->B option) x` THEN REWRITE_TAC[OPTION_CHOICE_DEF]);;

let option_choice_f_assoc = prove
 (`option_choice_f (option_choice_f f g) h =
   option_choice_f f (option_choice_f g (h:A->B option))`,
  REWRITE_TAC[FUN_EQ_THM; option_choice_f_def] THEN GEN_TAC THEN
  CASES_ON `(f:A->B option) x` THEN REWRITE_TAC[OPTION_CHOICE_DEF]);;

let empty_is_ALOOKUP = prove
 (`(\x:A. NONE:B option) = ALOOKUP []`,
  REWRITE_TAC[FUN_EQ_THM; ALOOKUP_def]);;

let repr_insert = prove
 (`sorted_alist_repr R al f /\ is_insert fl fr R k x al al' ==>
   sorted_alist_repr R al' (option_choice_f (ALOOKUP [(k, x)]) (f:A->B option))`,
  REWRITE_TAC[sorted_alist_repr_def; is_insert_def] THEN STRIP_TAC THEN
  FIRST_X_ASSUM (MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC[GSYM alookup_append_option_choice_f; APPEND]);;

let alookup_to_option_choice = prove
 (`(ALOOKUP (CONS x (CONS y zs)) =
    option_choice_f (ALOOKUP [x]) (ALOOKUP (CONS y (zs:(A#B)list)))) /\
   (option_choice_f (ALOOKUP []) g = (g:A->B option))`,
  REWRITE_TAC[GSYM alookup_append_option_choice_f; APPEND] THEN
  REWRITE_TAC[FUN_EQ_THM; option_choice_f_def; ALOOKUP_def; OPTION_CHOICE_DEF]);;

let alist_repr_choice_trans_left = prove
 (`sorted_alist_repr R al f /\
   sorted_alist_repr R al' (option_choice_f (ALOOKUP al) g) ==>
   sorted_alist_repr R al' (option_choice_f f (g:A->B option))`,
  REWRITE_TAC[sorted_alist_repr_def] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let alist_repr_refl = prove
 (`!al. irreflexive R /\ transitive R ==> SORTED R (MAP FST al) ==>
        sorted_alist_repr R al (ALOOKUP (al:(A#B)list))`,
  SIMP[sorted_alist_repr_def]);;

(* lookups on sorted alists *)

let is_lookup_def = cake_def
  `is_lookup fl fr (R:A->A->bool) (al:(A#B)list) x r <=>
     !xs ys. (fl \/ (xs = [])) ==>
       (fr \/ (ys = [])) ==> irreflexive R /\ transitive R ==>
       SORTED R (MAP FST (APPEND (APPEND xs al) ys)) ==>
       (ALOOKUP (APPEND (APPEND xs al) ys) x = r)`;;

let lookup_repr = prove
 (`sorted_alist_repr R al f /\ is_lookup fl fr R al (x:A) r ==> (f x = (r:B option))`,
  REWRITE_TAC[is_lookup_def; sorted_alist_repr_def] THEN STRIP_TAC THEN
  FIRST_X_ASSUM (MP_TAC o SPECL [`[]:(A#B)list`; `[]:(A#B)list`]) THEN
  ASM_REWRITE_TAC[APPEND; APPEND_NIL]);;

let is_lookup_l = prove
 (`!n. is_lookup fl T R l (x:A) res
       ==> is_lookup fl T R (count_append n l r) x (res:B option)`,
  GEN_TAC THEN REWRITE_TAC[is_lookup_def; count_append_def] THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN
  FIRST_X_ASSUM (MP_TAC o SPECL [`xs:(A#B)list`; `APPEND (r:(A#B)list) ys`]) THEN
  REWRITE_TAC[GSYM APPEND_ASSOC] THEN MESON_TAC[]);;

let is_lookup_r = prove
 (`!n. is_lookup T fr R r (x:A) res
       ==> is_lookup T fr R (count_append n l r) x (res:B option)`,
  GEN_TAC THEN REWRITE_TAC[is_lookup_def; count_append_def] THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN
  FIRST_X_ASSUM (MP_TAC o SPECL [`APPEND xs (l:(A#B)list)`; `ys:(A#B)list`]) THEN
  REWRITE_TAC[GSYM APPEND_ASSOC] THEN MESON_TAC[]);;

let is_lookup_far_left = prove
 (`!(R:A->A->bool) k k' (v:B). R k k' ==> is_lookup F T R [(k', v)] k NONE`,
  REWRITE_TAC[is_lookup_def; APPEND; MAP; irreflexive_DEF] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN RULE_ASSUM_TAC (REWRITE_RULE[APPEND; MAP]) THEN
  REWRITE_TAC[APPEND; MAP; ALOOKUP_NONE; MEM] THEN
  UNDISCH_TAC `SORTED (R:A->A->bool) (CONS k' (MAP FST (ys:(A#B)list)))` THEN
  ASM_SIMP_TAC[SORTED_EQ] THEN
  RULE_ASSUM_TAC (REWRITE_RULE[transitive_DEF]) THEN ASM_MESON_TAC[]);;

let is_lookup_far_right = prove
 (`!(R:A->A->bool) k k' (v:B). R k' k ==> is_lookup T F R [(k', v)] k NONE`,
  REWRITE_TAC[is_lookup_def; irreflexive_DEF] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[APPEND_NIL] THEN
  REWRITE_TAC[ALOOKUP_NONE; MAP_APPEND; MAP; MEM_APPEND; MEM] THEN
  QPAT_X_ASSUM "SORTED _ _" MP_TAC THEN
  ASM_SIMP_TAC[APPEND_NIL; MAP_APPEND; MAP; SORTED_APPEND; MEM] THEN
  RULE_ASSUM_TAC (REWRITE_RULE[transitive_DEF]) THEN ASM_MESON_TAC[]);;

let is_lookup_hit = prove
 (`!(R:A->A->bool) k k' (v:B). (k' = k) ==> is_lookup T T R [(k', v)] k (SOME v)`,
  REWRITE_TAC[is_lookup_def; irreflexive_DEF] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `ALOOKUP (xs:(A#B)list) k = NONE` ASSUME_TAC THENL
   [REWRITE_TAC[ALOOKUP_NONE] THEN
    QPAT_X_ASSUM "SORTED _ _" MP_TAC THEN
    ASM_SIMP_TAC[GSYM APPEND_ASSOC; MAP_APPEND; MAP; APPEND; SORTED_APPEND; MEM] THEN
    ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[ALOOKUP_APPEND; ALOOKUP_def] THEN SIMP[]);;

(* HOL4: DISJ_EQ_IMP (a library theorem of that name exists) *)
let alist_tree_DISJ_EQ_IMP = prove
 (`(P \/ Q) <=> (~P ==> Q)`,
  MESON_TAC[]);;

let is_lookup_centre = prove
 (`!(R:A->A->bool) n l r k.
     ~(l = []) ==> R (FST (LAST l)) k ==> ~(r = []) ==> R k (FST (HD r)) ==>
     is_lookup T T R (count_append n l r) k (NONE:B option)`,
  REWRITE_TAC[is_lookup_def; count_append_def] THEN REPEAT STRIP_TAC THEN
  MP_TAC (ISPECL [`k:A`] (INST [`APPEND xs l:(A#B)list`,`l:(A#B)list`;
                                `APPEND r ys:(A#B)list`,`r:(A#B)list`]
                               sorted_fst_insert_centre)) THEN
  ASM_REWRITE_TAC[GSYM MAP_APPEND; APPEND_EQ_NIL; LAST_APPEND; HD_APPEND] THEN
  RULE_ASSUM_TAC (REWRITE_RULE[GSYM APPEND_ASSOC]) THEN
  ASM_REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  ASM_SIMP_TAC[SORTED_APPEND; SORTED_EQ; MEM; MAP_APPEND; MEM_APPEND] THEN STRIP_TAC THEN
  REWRITE_TAC[ALOOKUP_NONE; MAP_APPEND; MEM_APPEND] THEN
  RULE_ASSUM_TAC (REWRITE_RULE[irreflexive_DEF]) THEN ASM_MESON_TAC[]);;

let is_lookup_empty = prove
 (`!(R:A->A->bool) k (al:(A#B)list). (al = []) ==> is_lookup F F R al k NONE`,
  SIMP[is_lookup_def; APPEND; ALOOKUP_def]);;
