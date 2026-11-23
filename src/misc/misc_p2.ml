(* ========================================================================= *)
(* misc_p2: port of HOL4 misc/miscScript.sml (CakeML v3479), part 2 of 3:   *)
(* the blocks of lines 1471-3035 of the script.                             *)
(* Miscellaneous definitions and minor lemmas used throughout the           *)
(* development.                                                              *)
(* HOL4 between is misc_between (a short or common word; between is also a   *)
(* constant of HOL Light's Multivariate), and between_def is                 *)
(* misc_between_def.                                                         *)
(* ========================================================================= *)

needs "hol4/vocab.ml";;
needs "hol4/list.ml";;
needs "hol4/rich_list.ml";;
needs "hol4/basic.ml";;
needs "hol4/finite_map.ml";;
needs "hol4/alist.ml";;
needs "hol4/string4.ml";;
needs "hol4/words4.ml";;
needs "hol4/numposrep.ml";;
needs "hol4/ASCIInumbers.ml";;
needs "hol4/sptree.ml";;
needs "hol4/set_sep.ml";;
needs "hol4/sorting.ml";;
needs "misc/misc_p1.ml";;

prioritize_num();;
type_invention_error := true;;

(* used twice, and only in source_to_flatProof *)
let FOLDL_invariant = prove
 (`!P (f:B->A->B) ls a.
     P a /\ (!x y. MEM y ls /\ P x ==> P (f x y)) ==> P (FOLDL f a ls)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[FOLDL; MEM] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]);;

(* never used *)
let FOLDL_invariant_rest = prove
 (`!P (f:B->A->B) ls a.
     P ls a /\
     (!x n. n < LENGTH ls /\ P (DROP n ls) x
            ==> P (DROP (SUC n) ls) (f x (EL n ls)))
     ==> P [] (FOLDL f a ls)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[FOLDL] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`a:B`; `0`]) THEN
    ASM_REWRITE_TAC[LENGTH; LT_0; RICHAUX_DROP_CLAUSES; EL; HD];
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:B`; `SUC n`]) THEN
    ASM_REWRITE_TAC[LENGTH; LT_SUC; RICHAUX_DROP_CLAUSES; EL; TL]]);;

let misc_between_def = cake_def
  `misc_between x y z <=> x:num <= z /\ z < y`;;

let IN_between = prove
 (`x IN misc_between y z <=> y <= x /\ x < z`,
  REWRITE_TAC[IN; misc_between_def]);;

(* never used *)
let SUC_LEAST = prove
 (`!x. (P:num->bool) x ==> SUC ((minimal) P) = minimal x. 0 < x /\ P (PRE x)`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `(P:num->bool) ((minimal) P) /\ !m. m < (minimal) P ==> ~P m`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[MINIMAL]; ALL_TAC] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MINIMAL_UNIQUE THEN
  ASM_REWRITE_TAC[PRE; LT_0] THEN
  X_GEN_TAC `m:num` THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `PRE m < (minimal) (P:num->bool)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ASM_MESON_TAC[]]);;

(* never used *)
let fmap_linv_def = cake_def
  `fmap_linv (f1:(A,B)fmap) (f2:(B,A)fmap) <=>
     FDOM f2 = FRANGE f1 /\
     (!x. x IN FDOM f1 ==> FLOOKUP f2 (FAPPLY f1 x) = SOME x)`;;

(* never used *)
let fmap_linv_unique = prove
 (`!(f:(A,B)fmap) f1 f2. fmap_linv f f1 /\ fmap_linv f f2 ==> f1 = f2`,
  REWRITE_TAC[fmap_linv_def] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[fmap_eq_flookup] THEN X_GEN_TAC `k:B` THEN
  ASM_CASES_TAC `(k:B) IN FRANGE (f:(A,B)fmap)` THENL
   [FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[IN_FRANGE]) THEN STRIP_TAC THEN
    ASM_MESON_TAC[];
    ASM_MESON_TAC[flookup_thm]]);;

(* never used *)
let INJ_has_fmap_linv = prove
 (`INJ (FAPPLY (f:(A,B)fmap)) (FDOM f) (FRANGE f) ==> ?g. fmap_linv f g`,
  STRIP_TAC THEN
  EXISTS_TAC `FUN_FMAP (\x. @y. FLOOKUP (f:(A,B)fmap) y = SOME x) (FRANGE f)` THEN
  SIMP_TAC[fmap_linv_def; FLOOKUP_FUN_FMAP; FDOM_FMAP; FINITE_FRANGE] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `FAPPLY (f:(A,B)fmap) x IN FRANGE f` (fun th -> REWRITE_TAC[th])
  THENL [REWRITE_TAC[IN_FRANGE] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[option_INJ] THEN
  SUBGOAL_THEN `FLOOKUP (f:(A,B)fmap) (@y. FLOOKUP f y = SOME (FAPPLY f x)) =
                SOME (FAPPLY f x)` MP_TAC THENL
   [CONV_TAC SELECT_CONV THEN EXISTS_TAC `x:A` THEN
    ASM_REWRITE_TAC[flookup_thm];
    ALL_TAC] THEN
  SPEC_TAC(`@y. FLOOKUP (f:(A,B)fmap) y = SOME (FAPPLY f x)`, `y:A`) THEN
  X_GEN_TAC `y:A` THEN REWRITE_TAC[flookup_thm] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o CONJUNCT2 o REWRITE_RULE[INJ]) THEN
  ASM_REWRITE_TAC[]);;

(* never used *)
let has_fmap_linv_inj = prove
 (`(?g. fmap_linv (f:(A,B)fmap) g) <=> INJ (FAPPLY f) (FDOM f) (FRANGE f)`,
  EQ_TAC THENL [ALL_TAC; MESON_TAC[INJ_has_fmap_linv]] THEN
  REWRITE_TAC[fmap_linv_def; INJ; IN_FRANGE] THEN STRIP_TAC THEN
  CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FLOOKUP (g:(B,A)fmap) (FAPPLY (f:(A,B)fmap) x) = SOME x /\
                FLOOKUP g (FAPPLY f y) = SOME y` MP_TAC THENL
   [ASM_MESON_TAC[]; ASM_REWRITE_TAC[] THEN MESON_TAC[option_INJ]]);;

(* never used *)
let fmap_linv_FAPPLY = prove
 (`fmap_linv (f:(A,B)fmap) g /\ x IN FDOM f ==> FAPPLY g (FAPPLY f x) = x`,
  REWRITE_TAC[fmap_linv_def; flookup_thm] THEN MESON_TAC[]);;

(* TODO - candidate for move to HOL *)
let plus_compose = prove
 (`!n:num m. (+) n o (+) m = (+) (n + m)`,
  REWRITE_TAC[FUN_EQ_THM; o_THM; ADD_ASSOC]);;
(* TODO: move elsewhere? export as rewrite? *)
(* never used *)
let IN_option_rwt = prove
 (CASE_TERM
  `(x:A) IN (match (opt:B option) with NONE -> {} | SOME y -> (Q:B->A->bool) y) <=>
   ?y. opt = SOME y /\ x IN Q y`,
  CASES_ON `opt:B option` THEN SIMP[NOT_IN_EMPTY]);;

(* never used *)
let IN_option_rwt2 = prove
 (`(x:A) IN option_CASE (opt:B option) {} (s:B->A->bool) <=>
   ?y. opt = SOME y /\ x IN s y`,
  CASES_ON `opt:B option` THEN SIMP[NOT_IN_EMPTY]);;

(* Re-expressing folds *)

(* only used in flat_elimProof *)
let FOLDR_CONS_triple = prove
 (`!(f:A->B->C->D) ls a.
     ITLIST (\(x,y,z) w. CONS (f x y z) w) ls a =
     APPEND (MAP (\(x,y,z). f x y z) ls) a`,
  GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[FORALL_PAIR_THM; ITLIST; MAP; APPEND] THEN SIMP_TAC[]);;

(* never used *)
let FOLDR_CONS_5tup = prove
 (`!(f:A->B->C->D->E->Z) ls a.
     ITLIST (\(c,d,x,y,z) w. CONS (f c d x y z) w) ls a =
     APPEND (MAP (\(c,d,x,y,z). f c d x y z) ls) a`,
  GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[FORALL_PAIR_THM; ITLIST; MAP; APPEND] THEN SIMP_TAC[]);;

(* never used *)
let FOLDR_transitive_property = prove
 (`!P (ls:A list) (f:A->B->B) a.
     P [] a /\
     (!n a. n < LENGTH ls /\ P (DROP (SUC n) ls) a
            ==> P (DROP n ls) (f (EL n ls) a))
     ==> P ls (ITLIST f ls a)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[ITLIST] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(P:A list->B->bool) t (ITLIST f t a)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `n:num` THEN X_GEN_TAC `b:B` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`SUC n`; `b:B`]) THEN
    ASM_REWRITE_TAC[LENGTH; LT_SUC; RICHAUX_DROP_CLAUSES; EL; TL];
    FIRST_X_ASSUM(MP_TAC o SPECL [`0`; `ITLIST (f:A->B->B) t a`]) THEN
    ASM_REWRITE_TAC[LENGTH; LT_0; RICHAUX_DROP_CLAUSES; EL; HD]]);;

(* Re-expressing curried lambdas *)

let FST_triple = prove
 (`(\(n:A,ns:B,b:C). n) = FST`,
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; FST]);;

(* never used *)
let FST_5tup = prove
 (`(\(n:A,ns:B,b:C,x:D,y:E). n) = FST`,
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; FST]);;

(* never used *)
let SND_triple = prove
 (`(\(n:A,ns:B,b:C). (f:B->C->D) ns b) = UNCURRY f o SND`,
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; o_THM; SND; UNCURRY_DEF]);;

let FST_pair = prove
 (`(\(n:A,v:B). n) = FST`,
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; FST]);;

(* never used *)
let SND_pair = prove
 (`(\(n:A,v:B). v) = SND`,
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; SND]);;

(* never used *)
let SND_FST_pair = prove
 (`(\((n:A,m:B),c:C). m) = SND o FST`,
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; o_THM; FST; SND]);;

(* never used *)
let MAP_ZIP_SND_triple = prove
 (`LENGTH (l1:A list) = LENGTH (l2:(B#C)list)
   ==> MAP (\(x,y,z). (f:B->C->D) y z) (ZIP l1 l2) = MAP (UNCURRY f) l2`,
  SPEC_TAC(`l2:(B#C)list`,`l2:(B#C)list`) THEN
  SPEC_TAC(`l1:A list`,`l1:A list`) THEN
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ; ZIP_def; MAP] THEN
  DISCH_TAC THEN ASM_SIMP_TAC[CONS_11] THEN
  STRUCT_CASES_TAC(ISPEC `h':B#C` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[UNCURRY_DEF]);;

(* Specialisations to identity function *)

(* HOL4: I PERMUTES s, an overload of BIJ I s s *)
let I_PERMUTES = prove
 (`BIJ (I:A->A) s s`,
  REWRITE_TAC[BIJ; INJ; SURJ; I_THM] THEN MESON_TAC[]);;
let _ = cake_add_simps [I_PERMUTES];;

(* never used *)
let INJ_I = prove
 (`!s t. INJ (I:A->A) s t <=> s SUBSET t`,
  REWRITE_TAC[INJ; SUBSET; I_THM] THEN MESON_TAC[]);;

let MAP_EQ_ID = prove
 (`!(f:A->A) ls. MAP f ls = ls <=> !x. MEM x ls ==> f x = x`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; MEM; CONS_11] THEN
  MESON_TAC[]);;

(* Specialisations to FEMPTY *)

let FUN_FMAP_FAPPLY_FEMPTY_FAPPLY = prove
 (`FINITE (s:A->bool)
   ==> FAPPLY (FUN_FMAP (FAPPLY (FEMPTY:(A,B)fmap)) s) x = FAPPLY FEMPTY x`,
  STRIP_TAC THEN ASM_CASES_TAC `(x:A) IN s` THENL
   [ASM_SIMP_TAC[FUN_FMAP_DEF];
    MATCH_MP_TAC NOT_FDOM_FAPPLY_FEMPTY THEN ASM_SIMP_TAC[FDOM_FMAP]]);;
let _ = cake_add_simps [FUN_FMAP_FAPPLY_FEMPTY_FAPPLY];;

(* FUPDATE_LIST stuff *)

let NOT_MEM_FLOOKUP_ZIP = prove
 (`!ys (xs:(A,B)fmap) zs.
     ~MEM n ys ==> FLOOKUP (xs |++ ZIP ys zs) n = FLOOKUP xs n`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ZIP_DEF; FUPDATE_LIST_THM; MEM; DE_MORGAN_THM] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[FLOOKUP_UPDATE] THEN
  COND_CASES_TAC THEN ASM_MESON_TAC[]);;

(* Misc. *)

let LESS_1 = prove
 (`x < 1 <=> x = 0`,
  ARITH_TAC);;
let _ = cake_add_simps [LESS_1];;

(* --------- SO additions --------- *)

let map_fst = prove
 (`!l (f:B->C). MAP FST (MAP (\(x:A,y). (x, f y)) l) = MAP FST l`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MAP_MAP_o] THEN AP_THM_TAC THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; o_THM; FST]);;

(* use INJ_MAP_EQ_IFF and INJ_DEF *)
let map_some_eq = prove
 (`!l1 l2:A list. MAP SOME l1 = MAP SOME l2 <=> l1 = l2`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[MAP; NOT_CONS_NIL; NOT_NIL_CONS; CONS_11; option_INJ]);;

(* never used *)
let map_some_eq_append = prove
 (`!l1 l2 l3:A list.
     APPEND (MAP SOME l1) (MAP SOME l2) = MAP SOME l3 <=> APPEND l1 l2 = l3`,
  REWRITE_TAC[GSYM MAP_APPEND; map_some_eq]);;

let _ = cake_add_simps [map_some_eq; map_some_eq_append];;

(* list misc *)

let LASTN_LEMMA = prove
 (`LASTN (LENGTH xs + 1 + 1) (CONS (x:A) (CONS y xs)) = CONS x (CONS y xs) /\
   LASTN (LENGTH xs + 1) (CONS x xs) = CONS x xs`,
  MP_TAC(ISPEC `CONS (x:A) (CONS y xs)` LASTN_LENGTH_ID) THEN
  MP_TAC(ISPEC `CONS (x:A) xs` LASTN_LENGTH_ID) THEN
  REWRITE_TAC[LENGTH; ADD1; ADD_ASSOC] THEN SIMP_TAC[]);;

(* HOL4: LASTN_CONS specialised to n + 1 *)
let LASTN_TL = prove
 (`n < LENGTH (xs:A list) ==> LASTN (n + 1) (CONS x xs) = LASTN (n + 1) xs`,
  DISCH_TAC THEN MP_TAC(ISPECL [`n + 1`; `xs:A list`] LASTN_CONS) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]]);;

let LASTN_LENGTH_LESS_EQ = prove
 (`!xs:A list n. LENGTH xs <= n ==> LASTN n xs = xs`,
  SIMP_TAC[LASTN_DEF; TAKE_LENGTH_TOO_LONG; LENGTH_REVERSE; REVERSE_REVERSE]);;

let LASTN_ALT = prove
 (`LASTN n ([]:A list) = [] /\
   LASTN n (CONS (x:A) xs) =
     if LENGTH (CONS x xs) <= n then CONS x xs else LASTN n xs`,
  CONJ_TAC THENL [REWRITE_TAC[LASTN_DEF; REVERSE; RICHAUX_TAKE_CLAUSES]; ALL_TAC] THEN
  COND_CASES_TAC THENL [ASM_SIMP_TAC[LASTN_LENGTH_LESS_EQ]; ALL_TAC] THEN
  MP_TAC(ISPECL [`n:num`; `xs:A list`] LASTN_CONS) THEN ANTS_TAC THENL
   [POP_ASSUM MP_TAC THEN REWRITE_TAC[LENGTH] THEN ARITH_TAC; SIMP_TAC[]]);;

let LENGTH_LASTN_LESS = prove
 (`!xs:A list n. LENGTH (LASTN n xs) <= LENGTH xs`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LASTN_ALT; LENGTH; LE_REFL] THEN
  GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[LENGTH; LE_REFL] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ARITH_TAC);;

let MAP_EQ_MAP_IMP = prove
 (`!xs ys (f:A->B).
     (!x y. MEM x xs /\ MEM y ys /\ f x = f y ==> x = y)
     ==> MAP f xs = MAP f ys ==> xs = ys`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP; NOT_CONS_NIL; NOT_NIL_CONS; CONS_11; MEM] THEN
  REPEAT STRIP_TAC THEN ASM_MESON_TAC[]);;

let INJ_MAP_EQ_2 = prove
 (`!(f:A->B) l1 l2.
     (!x y. x IN set_of_list l1 /\ y IN set_of_list l2 /\ f x = f y ==> x = y) /\
     MAP f l1 = MAP f l2
     ==> l1 = l2`,
  REWRITE_TAC[IN_SET_OF_LIST] THEN MESON_TAC[MAP_EQ_MAP_IMP]);;

let LENGTH_EQ_FILTER_FILTER = prove
 (`!xs:A list.
     ALL (\x. (P x \/ Q x) /\ ~(P x /\ Q x)) xs
     ==> LENGTH xs = LENGTH (FILTER P xs) + LENGTH (FILTER Q xs)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; FILTER; LENGTH; ADD_CLAUSES] THEN
  DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[LENGTH; ADD_CLAUSES] THEN
  ASM_MESON_TAC[]);;

let LIST_REL_MAP_FILTER_NEQ = prove
 (`!P (f1:A#B->E) (f2:C#D->G) z1 z2 l1 l2.
     ALL2 P (MAP f1 l1) (MAP f2 l2) /\
     (!y1 y2. MEM (y1,y2) (ZIP l1 l2)
              ==> (~(SND y1 = z1) <=> ~(SND y2 = z2)) /\ P (f1 y1) (f2 y2))
     ==> ALL2 P (MAP f1 (FILTER (\(x,y). ~(y = z1)) l1))
                (MAP f2 (FILTER (\(x,y). ~(y = z2)) l2))`,
  REPEAT GEN_TAC THEN
  SPEC_TAC(`l2:(C#D)list`,`l2:(C#D)list`) THEN
  SPEC_TAC(`l1:(A#B)list`,`l1:(A#B)list`) THEN
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP; ALL2; FILTER; ZIP_def; MEM] THEN
  STRUCT_CASES_TAC(ISPEC `h:A#B` PAIR_SURJECTIVE) THEN
  STRUCT_CASES_TAC(ISPEC `h':C#D` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPECL [`(x:A,y:B)`; `(x':C,y':D)`]) THEN
  REWRITE_TAC[SND] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `ALL2 (P:E->G->bool) (MAP (f1:A#B->E) (FILTER (\(x,y). ~(y = z1)) t))
                        (MAP (f2:C#D->G) (FILTER (\(x,y). ~(y = z2)) t'))`
   ASSUME_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `y:B = z1` THENL
   [SUBGOAL_THEN `y':D = z2` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[];
    SUBGOAL_THEN `~(y':D = z2)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[MAP; ALL2]]);;
(* move into HOL? *)

(* HOL4: word_list (misc_word_list in names.tsv); HOL4 set_sep$one is *)
(* set_sep_one, p * q is p STAR q, a + bytes_in_word is word_add *)
let misc_word_list_def = cake_def
  `(misc_word_list (a:N word) ([]:B list) = set_sep_emp) /\
   (misc_word_list a (CONS x xs) =
      set_sep_one (a,x) STAR misc_word_list (word_add a bytes_in_word) xs)`;;

let word_list_exists_def = cake_def
  `word_list_exists (a:N word) n =
     SEP_EXISTS (xs:B list). misc_word_list a xs STAR set_sep_cond (LENGTH xs = n)`;;

(* lookup_vars vs env = OPT_MMAP (\i. oEL i env) vs *)
let lookup_vars_def = cake_def
  `(lookup_vars [] (env:A list) = SOME []) /\
   (lookup_vars (CONS v vs) env =
      if v < LENGTH env then
        match lookup_vars vs env with
          SOME xs -> SOME (CONS (EL v env) xs)
        | NONE -> NONE
      else NONE)`;;
let EVERY_lookup_vars = prove
 (`!vs (env:A list) env'.
     ALL P env /\ lookup_vars vs env = SOME env' ==> ALL P env'`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[lookup_vars_def; option_INJ] THENL
   [MESON_TAC[ALL]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
  CASES_ON `lookup_vars (t:num list) (env:A list)` THEN
  SIMP[option_INJ; option_DISTINCT] THEN STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[ALL] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[EVERY_EL]; ASM_MESON_TAC[]]);;

let EVERY_LAST = prove
 (`!P (l:A list). ~(l = []) /\ ALL P l ==> P (LAST l)`,
  REWRITE_TAC[EVERY_MEM] THEN MESON_TAC[MEM_LAST_NOT_NIL]);;
(* TODO - candidate for move to HOL *)
let num_to_hex_string_length_1 = prove
 (`!x. x < 16 ==> LENGTH (num_to_hex_string x) = 1`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[num_to_hex_string_def; n2s_def; LENGTH_REVERSE; LENGTH_MAP] THEN
  ONCE_REWRITE_TAC[n2l_def] THEN ASM_REWRITE_TAC[LENGTH; ONE]);;

(* TODO - candidate for move to HOL *)
let num_to_hex_string_length_2 = prove
 (`!x. 16 <= x /\ x < 256 ==> LENGTH (num_to_hex_string x) = 2`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[num_to_hex_string_def; n2s_def; LENGTH_REVERSE; LENGTH_MAP] THEN
  ONCE_REWRITE_TAC[n2l_def] THEN
  SUBGOAL_THEN `~(x < 16) /\ x DIV 16 < 16` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[ARITH_RULE `~(16 < 2)`] THEN
  ONCE_REWRITE_TAC[n2l_def] THEN ASM_REWRITE_TAC[LENGTH] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let num_from_hex_string_length_2 = prove
 (`num_from_hex_string [d1; d2] < 256`,
  REWRITE_TAC[num_from_hex_string_def; s2n_def; REVERSE; APPEND; MAP; l2n_def] THEN
  MP_TAC(SPECL [`UNHEX d1`; `16`] MOD_LT_EQ) THEN
  MP_TAC(SPECL [`UNHEX d2`; `16`] MOD_LT_EQ) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

(* HOL4 #"0" is CHR 48 *)
let num_from_hex_string_leading_0 = prove
 (`!ls. ~(ls = []) ==> num_from_hex_string (CONS (CHR 48) ls) = num_from_hex_string ls`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[num_from_hex_string_def; s2n_def; REVERSE; MAP_APPEND; MAP;
              l2n_APPEND; l2n_def; UNHEX_def] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES]);;

let num_from_hex_string_length_2_less_16 = prove
 (`!h1 h2. isHexDigit h1 ==> num_from_hex_string [h1; h2] < 16 ==> h1 = CHR 48`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[num_from_hex_string_def; s2n_def; REVERSE; APPEND; MAP; l2n_def] THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  SUBGOAL_THEN `UNHEX h1 MOD 16 = 0` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `UNHEX h1 < 16` (fun th -> SIMP_TAC[th; MOD_LT]) THENL
   [UNDISCH_TAC `isHexDigit h1` THEN REWRITE_TAC[isHexDigit_def; UNHEX] THEN
    REPEAT COND_CASES_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `isHexDigit h1` THEN REWRITE_TAC[isHexDigit_def; UNHEX] THEN
  REPEAT COND_CASES_TAC THEN TRY ASM_ARITH_TAC THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ORD h1 = 48` (fun th -> MESON_TAC[th; CHR_ORD]) THEN
  ASM_ARITH_TAC);;

let num_from_hex_string_num_to_hex_string = prove
 (`num_from_hex_string (num_to_hex_string n) = n`,
  MP_TAC(AP_THM num_hex_string `n:num`) THEN REWRITE_TAC[o_THM; I_THM]);;
let _ = cake_add_simps [num_from_hex_string_num_to_hex_string];;

let MAPi_ID = prove
 (`MAPi (\(x:num) (y:A). y) = I`,
  REWRITE_TAC[FUN_EQ_THM; I_THM] THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[MAPi_DEF; o_DEF]);;
let _ = cake_add_simps [MAPi_ID];;

(* TODO - candidate for move to HOL - though                                *)
(*   enumerate i0 l = MAPi (\x i. (i + i0, x)) l                             *)
let enumerate_def = cake_def
  `(enumerate n ([]:A list) = []) /\
   (enumerate n (CONS x xs) = CONS (n,x) (enumerate (n + 1) xs))`;;
(* TODO - candidate for move to HOL *)
let LENGTH_enumerate = prove
 (`!xs:A list k. LENGTH (enumerate k xs) = LENGTH xs`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[enumerate_def; LENGTH]);;

let EL_enumerate = prove
 (`!xs:A list n k. n < LENGTH xs ==> EL n (enumerate k xs) = (n + k, EL n xs)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; CONJUNCT1 LT] THEN
  INDUCT_TAC THEN REWRITE_TAC[enumerate_def; EL; HD; TL; LT_SUC; ADD_CLAUSES] THEN
  ASM_SIMP_TAC[PAIR_EQ] THEN ARITH_TAC);;

let MAP_enumerate_MAPi = prove
 (`!(f:num#A->B) xs. MAP f (enumerate 0 xs) = MAPi (\n e. f (n,e)) xs`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[LIST_EQ_REWRITE; LENGTH_MAP; LENGTH_MAPi; LENGTH_enumerate] THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[EL_MAP; EL_MAPi; LENGTH_enumerate; EL_enumerate; ADD_CLAUSES]);;

let MAPi_enumerate_MAP = prove
 (`!(f:num->A->B) xs. MAPi f xs = MAP (\(i,e). f i e) (enumerate 0 xs)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[LIST_EQ_REWRITE; LENGTH_MAP; LENGTH_MAPi; LENGTH_enumerate] THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[EL_MAP; EL_MAPi; LENGTH_enumerate; EL_enumerate; ADD_CLAUSES]);;

let MEM_enumerate = prove
 (`!xs:A list i e.
     i < LENGTH xs ==> (MEM (i,e) (enumerate 0 xs) <=> EL i xs = e)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MEM_EXISTS_EL; LENGTH_enumerate] THEN
  SUBGOAL_THEN
   `!j. j < LENGTH (xs:A list) ==> EL j (enumerate 0 xs) = (j, EL j xs)`
   ASSUME_TAC THENL [SIMP_TAC[EL_enumerate; ADD_CLAUSES]; ALL_TAC] THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `(i:num,e:A) = EL j (enumerate 0 xs)` THEN
    ASM_SIMP_TAC[PAIR_EQ] THEN MESON_TAC[];
    DISCH_TAC THEN EXISTS_TAC `i:num` THEN ASM_SIMP_TAC[PAIR_EQ]]);;

let MEM_enumerate_IMP = prove
 (`!ls k. MEM (i,e) (enumerate k ls) ==> MEM (e:A) ls`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[enumerate_def; MEM; PAIR_EQ] THEN
  ASM_MESON_TAC[]);;

let MAP_FST_enumerate = prove
 (`MAP FST (enumerate k (ls:A list)) = list_of_seq ((+) k) (LENGTH ls)`,
  REWRITE_TAC[LIST_EQ_REWRITE; LENGTH_MAP; LENGTH_enumerate; LENGTH_LIST_OF_SEQ] THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[EL_MAP; LENGTH_enumerate; EL_enumerate; EL_LIST_OF_SEQ] THEN
  ARITH_TAC);;

let ALL_DISTINCT_MAP_FST_enumerate = prove
 (`ALL_DISTINCT (MAP FST (enumerate k (ls:A list)))`,
  REWRITE_TAC[MAP_FST_enumerate; ALL_DISTINCT_GENLIST] THEN ARITH_TAC);;

let ALOOKUP_enumerate = prove
 (`!ls:A list k x.
     ALOOKUP (enumerate k ls) x =
     if k <= x /\ x < LENGTH ls + k then SOME (EL (x - k) ls) else NONE`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[enumerate_def; ALOOKUP_THM; LENGTH] THEN
  REPEAT GEN_TAC THENL
   [COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ASM_REWRITE_TAC[]] THEN
  ASM_CASES_TAC `k:num = x` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[LE_REFL; SUB_REFL; EL; HD] THEN
    REWRITE_TAC[ARITH_RULE `x < SUC n + x`];
    ALL_TAC] THEN
  ASM_CASES_TAC `k < x:num` THENL
   [SUBGOAL_THEN `x - k = SUC (x - (k + 1))` SUBST1_TAC THENL
     [ASM_ARITH_TAC; REWRITE_TAC[EL; TL]] THEN
    AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    SUBGOAL_THEN `~(k + 1 <= x) /\ ~(k <= x)` (fun th -> REWRITE_TAC[th]) THEN
    ASM_ARITH_TAC]);;

let SUM_MAP_LENGTH_REPLICATE = prove
 (`!n ls:A list. SUM (MAP LENGTH (REPLICATE n ls)) = n * LENGTH ls`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[REPLICATE; MAP; SUM; MULT_CLAUSES] THEN
  ARITH_TAC);;

let SUM_MAP_COUNT_LIST = prove
 (`!n k. SUM (MAP ((+) k) (COUNT_LIST n)) = (n * ((2 * k + n) - 1)) DIV 2`,
  SUBGOAL_THEN
   `!n k. 2 * SUM (MAP ((+) k) (COUNT_LIST n)) = n * ((2 * k + n) - 1)`
   ASSUME_TAC THENL
   [INDUCT_TAC THEN REWRITE_TAC[COUNT_LIST_DEF; MAP; SUM; MULT_CLAUSES] THEN
    X_GEN_TAC `k:num` THEN REWRITE_TAC[MAP_MAP_o] THEN
    SUBGOAL_THEN `(+) k o SUC = (+) (k + 1)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k + 1`) THEN
    REWRITE_TAC[ARITH_RULE `(2 * (k + 1) + n) - 1 = 2 * k + n + 1`;
                ARITH_RULE `(2 * k + SUC n) - 1 = 2 * k + n`] THEN
    ARITH_TAC;
    REPEAT GEN_TAC THEN FIRST_X_ASSUM(fun th -> REWRITE_TAC[GSYM th]) THEN
    SIMP_TAC[DIV_MULT; ARITH_RULE `~(2 = 0)`]]);;

(* HOL4: SUM_REPLICATE is rich_list.ml's SUM_REPLICATE (the same statement) *)

let SUM_MAP_BOUND = prove
 (`(!x. (f:A->num) x <= c) ==> SUM (MAP f ls) <= LENGTH ls * c`,
  DISCH_TAC THEN SPEC_TAC(`ls:A list`,`ls:A list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; SUM; LENGTH; MULT_CLAUSES; LE_0] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `h:A`) THEN ASM_ARITH_TAC);;

let SUM_MOD = prove
 (`k > 0 ==> SUM ls MOD k = SUM (MAP (\n. n MOD k) ls) MOD k`,
  DISCH_TAC THEN SPEC_TAC(`ls:num list`,`ls:num list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[SUM; MAP] THEN
  ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN ASM_REWRITE_TAC[MOD_MOD_REFL]);;

let MOD_SUB_LEMMA = prove
 (`n MOD k = 0 /\ m MOD k = 0 /\ 0 < k ==> (n - m) MOD k = 0`,
  REWRITE_TAC[MOD_EQ_0] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `a:num` SUBST1_TAC)
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `b:num` SUBST1_TAC) ASSUME_TAC)) THEN
  EXISTS_TAC `a - b:num` THEN REWRITE_TAC[RIGHT_SUB_DISTRIB]);;

let FLAT_REPLICATE_NIL = prove
 (`!n. FLAT (REPLICATE n ([]:A list)) = []`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[REPLICATE; FLAT; APPEND]);;

let MEM_REPLICATE_EQ = prove
 (`!n (x:A) y. MEM x (REPLICATE n y) <=> x = y /\ ~(n = 0)`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[REPLICATE; MEM; NOT_SUC] THEN MESON_TAC[]);;

(* n.b. used in hol-reflection *)

(* HOL4: FDOM_FLOOKUP (finite_map.ml binds that name to another form) *)
let misc_FDOM_FLOOKUP = prove
 (`x IN FDOM (f:(A,B)fmap) <=> ?v. FLOOKUP f x = SOME v`,
  REWRITE_TAC[FLOOKUP_DEF] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[option_INJ; option_DISTINCT] THEN MESON_TAC[]);;

let FLAT_MAP_SING = prove
 (`!ls. FLAT (MAP (\x. [(f:A->B) x]) ls) = MAP f ls`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; FLAT; APPEND]);;

let FLAT_MAP_NIL = prove
 (`FLAT (MAP (\x:A. []:B list) ls) = []`,
  SPEC_TAC(`ls:A list`,`ls:A list`) THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; FLAT; APPEND]);;
let UPDATE_LIST_NOT_MEM = prove
 (`!ls (f:A->B) x. ~MEM x (MAP FST ls) ==> (f =++ ls) x = f x`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[UPDATE_LIST_THM; MAP; MEM; DE_MORGAN_THM] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[APPLY_UPDATE_THM] THEN
  COND_CASES_TAC THEN ASM_MESON_TAC[]);;

let MAP_ZIP_UPDATE_LIST_ALL_DISTINCT_same = prove
 (`!ks vs (f:A->B).
     LENGTH ks = LENGTH vs /\ ALL_DISTINCT ks ==> MAP (f =++ ZIP ks vs) ks = vs`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ; MAP; ALL_DISTINCT; ZIP_def] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[UPDATE_LIST_THM; FST; SND; CONS_11] THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[UPDATE_LIST_NOT_MEM; MAP_ZIP; APPLY_UPDATE_THM];
    ASM_SIMP_TAC[]]);;

let flookup_update_list_none = prove
 (`!x (m:(A,B)fmap) l.
     FLOOKUP (m |++ l) x = NONE <=> FLOOKUP m x = NONE /\ ALOOKUP l x = NONE`,
  REPEAT GEN_TAC THEN REWRITE_TAC[flookup_fupdate_list] THEN
  SUBGOAL_THEN `ALOOKUP (REVERSE l) (x:A) = NONE <=> ALOOKUP (l:(A#B)list) x = NONE`
    MP_TAC THENL
   [REWRITE_TAC[ALOOKUP_NONE; GSYM MAP_REVERSE; MEM_REVERSE]; ALL_TAC] THEN
  CASES_ON `ALOOKUP (REVERSE l) (x:A):B option` THEN
  REWRITE_TAC[option_CASE; option_DISTINCT] THEN MESON_TAC[]);;

let flookup_update_list_some = prove
 (`!x (m:(A,B)fmap) l y.
     FLOOKUP (m |++ l) x = SOME y <=>
     ALOOKUP (REVERSE l) x = SOME y \/
     (ALOOKUP l x = NONE /\ FLOOKUP m x = SOME y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[flookup_fupdate_list] THEN
  SUBGOAL_THEN `ALOOKUP (REVERSE l) (x:A) = NONE <=> ALOOKUP (l:(A#B)list) x = NONE`
    MP_TAC THENL
   [REWRITE_TAC[ALOOKUP_NONE; GSYM MAP_REVERSE; MEM_REVERSE]; ALL_TAC] THEN
  CASES_ON `ALOOKUP (REVERSE l) (x:A):B option` THEN
  REWRITE_TAC[option_CASE; option_DISTINCT; option_INJ] THEN MESON_TAC[]);;

let MULT_LE_EXP = prove
 (`!a:num b. ~(a = 1) ==> a * b <= a EXP b`,
  GEN_TAC THEN ASM_CASES_TAC `a = 0` THEN ASM_REWRITE_TAC[MULT_CLAUSES; LE_0] THEN
  ASM_CASES_TAC `a = 1` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `2 <= a` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  INDUCT_TAC THEN REWRITE_TAC[MULT_CLAUSES; EXP; LE_0] THEN
  ASM_CASES_TAC `b = 0` THEN
  ASM_REWRITE_TAC[EXP; MULT_CLAUSES; ADD_CLAUSES; LE_REFL] THEN
  SUBGOAL_THEN `a <= a EXP b` ASSUME_TAC THENL
   [MP_TAC(SPECL [`a:num`; `1`; `b:num`] LE_EXP) THEN
    ASM_REWRITE_TAC[EXP_1] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `2 * a EXP b <= a * a EXP b` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LE_MULT_RCANCEL]; ALL_TAC] THEN
  ASM_ARITH_TAC);;

(* HOL4 domain_rrestrict_subset and range_rrestrict_subset are not ported: *)
(* they are about set_relation (domain, range, rrestrict on sets of pairs), *)
(* which the port does not have                                            *)

let PERM_MAP_BIJ = prove
 (`!(f:A->B) l1 l2.
     BIJ f UNIV UNIV ==> (PERM l1 l2 <=> PERM (MAP f l1) (MAP f l2))`,
  REWRITE_TAC[BIJ_IFF_INV; IN_UNIV] THEN REPEAT STRIP_TAC THEN
  EQ_TAC THENL [REWRITE_TAC[PERM_MAP]; ALL_TAC] THEN
  SUBGOAL_THEN `!l:A list. MAP (g:B->A) (MAP f l) = l` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[MAP_MAP_o; o_DEF; MAP_ID]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (ISPEC `g:B->A` PERM_MAP)) THEN
  ASM_REWRITE_TAC[]);;

let lookup_fromList2 = prove
 (`!l n. lookup n (fromList2 l) =
         if EVEN n then lookup (n DIV 2) (fromList (l:A list)) else NONE`,
  SUBGOAL_THEN
   `!l k (tr:A spt) n.
      (!m. ~(n = k + 2 * m))
      ==> lookup n (SND (FOLDL (\(i,t) a. (i + 2,insert i a t)) (k,tr) l)) =
          lookup n tr`
   (LABEL_TAC "g2b") THENL
   [LIST_INDUCT_TAC THEN REWRITE_TAC[FOLDL; SND] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(fun th -> W(fun (_,w) ->
      MP_TAC(ISPECL [`k + 2`; `insert k (h:A) tr`; `n:num`] th))) THEN
    ANTS_TAC THENL
     [X_GEN_TAC `m:num` THEN FIRST_X_ASSUM(MP_TAC o SPEC `SUC m`) THEN
      ARITH_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[lookup_insert] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN SIMP_TAC[MULT_CLAUSES; ADD_CLAUSES];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!l k (tr:A spt) m.
      lookup (k + 2 * m)
        (SND (FOLDL (\(i,t) a. (i + 2,insert i a t)) (k,tr) l)) =
      if m < LENGTH l then SOME (EL m l) else lookup (k + 2 * m) tr`
   (LABEL_TAC "g2a") THENL
   [LIST_INDUCT_TAC THEN REWRITE_TAC[FOLDL; SND; LENGTH; CONJUNCT1 LT] THEN
    MAP_EVERY X_GEN_TAC [`k:num`; `tr:A spt`] THEN INDUCT_TAC THENL
     [REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; LT_0; EL; HD] THEN
      USE_THEN "g2b" (MP_TAC o
        ISPECL [`t:A list`; `k + 2`; `insert k (h:A) tr`; `k:num`])
      THEN ANTS_TAC THENL [ARITH_TAC; SIMP_TAC[lookup_insert]];
      FIRST_X_ASSUM(MP_TAC o SPECL [`k + 2`; `insert k (h:A) tr`; `m:num`]) THEN
      REWRITE_TAC[ARITH_RULE `(k + 2) + 2 * m = k + 2 * SUC m`] THEN
      DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[LT_SUC; EL; TL; lookup_insert] THEN
      COND_CASES_TAC THEN REWRITE_TAC[] THEN
      COND_CASES_TAC THEN REWRITE_TAC[] THEN
      POP_ASSUM MP_TAC THEN ARITH_TAC];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[fromList2_def; lookup_fromList] THEN
  COND_CASES_TAC THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `m:num` SUBST1_TAC o REWRITE_RULE[EVEN_EXISTS]) THEN
    REWRITE_TAC[ARITH_RULE `(2 * m) DIV 2 = m`] THEN
    USE_THEN "g2a" (MP_TAC o SPECL [`l:A list`; `0`; `LN:A spt`; `m:num`]) THEN
    REWRITE_TAC[ADD_CLAUSES; lookup_rwts];
    USE_THEN "g2b" (MP_TAC o SPECL [`l:A list`; `0`; `LN:A spt`; `n:num`]) THEN
    REWRITE_TAC[lookup_rwts; ADD_CLAUSES] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_MESON_TAC[EVEN_EXISTS]]);;

let domain_fromList2 = prove
 (`!q:A list. domain (fromList2 q) = set_of_list (list_of_seq (\x. 2 * x) (LENGTH q))`,
  REWRITE_TAC[EXTENSION; domain_lookup; lookup_fromList2; IN_SET_OF_LIST;
              MEM_GENLIST] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[option_DISTINCT; lookup_fromList] THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `m:num` SUBST1_TAC o REWRITE_RULE[EVEN_EXISTS]) THEN
    REWRITE_TAC[ARITH_RULE `(2 * m) DIV 2 = m`; ARITH_RULE `2 * m = 2 * n <=> m = n`] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
    ASM_MESON_TAC[];
    ASM_MESON_TAC[EVEN_EXISTS]]);;

let UNCURRY_eq_pair = prove
 (`UNCURRY (f:A->B->C) v = z <=> ?a b. v = (a,b) /\ f a b = z`,
  STRUCT_CASES_TAC(ISPEC `v:A#B` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[UNCURRY_DEF; PAIR_EQ] THEN MESON_TAC[]);;

let OLEAST_SOME_IMP = prove
 (`(OLEAST) P = SOME i ==> P i /\ (!n. n < i ==> ~P n)`,
  REWRITE_TAC[OLEAST_EQ_SOME]);;

let EXP2_EVEN = prove
 (`!n. EVEN (2 EXP n) <=> ~(n = 0)`,
  REWRITE_TAC[EVEN_EXP] THEN CONV_TAC NUM_REDUCE_CONV);;

let FST_UNZIP_MAPi = prove
 (`!l (f:num->A->B#C). FST (UNZIP (MAPi f l)) = MAPi ((o) ((o) FST) f) l`,
  REWRITE_TAC[UNZIP_DEF; FST] THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[MAPi_DEF; MAP; o_THM; o_ASSOC]);;

let SND_UNZIP_MAPi = prove
 (`!l (f:num->A->B#C). SND (UNZIP (MAPi f l)) = MAPi ((o) ((o) SND) f) l`,
  REWRITE_TAC[UNZIP_DEF; SND] THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[MAPi_DEF; MAP; o_THM; o_ASSOC]);;

let ALL_DISTINCT_FLAT = prove
 (`!l:(A list)list.
     ALL_DISTINCT (FLAT l) <=>
     (!l0. MEM l0 l ==> ALL_DISTINCT l0) /\
     (!i j. i < j /\ j < LENGTH l ==> !e. MEM e (EL i l) ==> ~MEM e (EL j l))`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[FLAT; ALL_DISTINCT; MEM; LENGTH; CONJUNCT1 LT]; ALL_TAC] THEN
  ASM_REWRITE_TAC[FLAT; ALL_DISTINCT_APPEND; MEM; MEM_FLAT] THEN
  SUBGOAL_THEN
   `!(P:num->num->bool).
      (!i j. i < j /\ j < LENGTH (CONS (h:A list) t) ==> P i j) <=>
      (!j. j < LENGTH t ==> P 0 (SUC j)) /\
      (!i j. i < j /\ j < LENGTH t ==> P (SUC i) (SUC j))`
   (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[LENGTH] THEN EQ_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      STRIP_TAC THEN INDUCT_TAC THEN INDUCT_TAC THEN
      REWRITE_TAC[LT_REFL; CONJUNCT1 LT; LT_SUC; LT_0] THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[EL; HD; TL; MEM_EXISTS_EL] THEN MESON_TAC[]);;

let ALL_DISTINCT_FLAT_EVERY = prove
 (`!ls:(A list)list. ALL_DISTINCT (FLAT ls) ==> ALL ALL_DISTINCT ls`,
  REWRITE_TAC[ALL_DISTINCT_FLAT; EVERY_MEM] THEN MESON_TAC[]);;

let ALL_DISTINCT_APPEND_APPEND_IMP = prove
 (`ALL_DISTINCT (APPEND (APPEND xs ys) (zs:A list))
   ==> ALL_DISTINCT (APPEND xs ys) /\ ALL_DISTINCT (APPEND xs zs) /\
       ALL_DISTINCT (APPEND ys zs)`,
  REWRITE_TAC[ALL_DISTINCT_APPEND; MEM_APPEND] THEN MESON_TAC[]);;

(* HOL4 states GSPEC f o g = (set comprehension), where HOL4's constant     *)
(* GSPEC f (f : B -> A # bool) is the set of the a with f b = (a,T) for some *)
(* b; HOL Light's GSPEC is another representation, so GSPEC f is written out *)
let GSPEC_o = prove
 (`{a:A | ?b:B. f b = (a,T)} o (g:C->A) = {x | ?y. (g x,T) = f y}`,
  REWRITE_TAC[FUN_EQ_THM; o_THM; GSPEC; SETSPEC] THEN MESON_TAC[]);;

(* TODO - candidate for move to HOL *)
let o_PAIR_MAP = prove
 (`FST o ((f:A->C) ## (g:B->D)) = f o FST /\ SND o (f ## g) = g o SND`,
  REWRITE_TAC[FUN_EQ_THM; o_THM; FORALL_PAIR_THM; PAIR_MAP_THM; FST; SND]);;

let any_el_ALT = prove
 (`!l n (d:A). any_el n l d = if n < LENGTH l then EL n l else d`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[any_el_def; LENGTH; CONJUNCT1 LT] THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[NOT_SUC; SUC_SUB1; LT_0; LT_SUC; EL; HD; TL]);;

let MOD_MINUS = prove
 (`0 < p /\ 0 < k ==> (p * k - n MOD (p * k)) MOD k = (k - n MOD k) MOD k`,
  STRIP_TAC THEN
  SUBGOAL_THEN `!m. m < p * k ==> (p * k - m) MOD k = (k - m MOD k) MOD k`
    MP_TAC THENL
   [X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`m:num`; `k:num`] DIVISION) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SPEC_TAC(`m DIV k`,`q:num`) THEN SPEC_TAC(`m MOD k`,`r:num`) THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `q * k < p * k` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[LT_MULT_RCANCEL] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(q + 1) * k <= p * k` MP_TAC THENL
     [ASM_REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[RIGHT_ADD_DISTRIB; MULT_CLAUSES] THEN DISCH_TAC THEN
    MATCH_MP_TAC MOD_EQ THEN EXISTS_TAC `p - (q + 1)` THEN
    REWRITE_TAC[RIGHT_SUB_DISTRIB; RIGHT_ADD_DISTRIB; MULT_CLAUSES] THEN
    ASM_ARITH_TAC;
    DISCH_THEN(MP_TAC o SPEC `n MOD (p * k)`) THEN
    REWRITE_TAC[MOD_LT_EQ; MULT_EQ_0] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    SUBGOAL_THEN `n MOD (p * k) MOD k = n MOD k` SUBST1_TAC THENL
     [ONCE_REWRITE_TAC[MULT_SYM] THEN REWRITE_TAC[MOD_MOD]; REFL_TAC]]);;
let option_fold_def = cake_def
  `(option_fold (f:A->B->B) x NONE = x) /\
   (option_fold f x (SOME y) = f y x)`;;
let SPLITP_CONS_IMP = prove
 (`!ls l' r. SPLITP (P:A->bool) ls = (l',r) /\ ~(r = []) ==> EX P ls`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `r:A list` list_CASES) THEN
  REWRITE_TAC[NOT_CONS_NIL] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SPLITP_IMP) THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP SPLITP_JOIN) THEN
  REWRITE_TAC[NULL; HD; EXISTS_APPEND; EX] THEN MESON_TAC[]);;

let LAST_CONS_alt = prove
 (`(P:A->bool) x ==> ((~(ls = []) ==> P (LAST ls)) <=> P (LAST (CONS x ls)))`,
  DISCH_TAC THEN STRUCT_CASES_TAC(ISPEC `ls:A list` list_CASES) THEN
  ASM_REWRITE_TAC[LAST; NOT_CONS_NIL]);;

let EL_CONS_IF = prove
 (`EL n (CONS (x:A) xs) = if n = 0 then x else EL (PRE n) xs`,
  STRUCT_CASES_TAC(SPEC `n:num` num_CASES) THEN
  REWRITE_TAC[EL; HD; TL; NOT_SUC; PRE]);;

let EVERY_TOKENS = prove
 (`!P ls. ALL (ALL ((~) o P)) (TOKENS P ls)`,
  MATCH_MP_TAC TOKENS_ind THEN REWRITE_TAC[TOKENS_def; ALL] THEN
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `SPLITP P (CONS (h:char) t)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `l:char list` (X_CHOOSE_THEN `r:char list`
    ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN SIMP[] THEN STRIP_TAC THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[ALL] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SPLITP_IMP) THEN SIMP_TAC[]);;

let TOKENS_START = prove
 (`!l (a:char). TOKENS (\x. x = a) (CONS a l) = TOKENS (\x. x = a) l`,
  REPEAT GEN_TAC THEN REWRITE_TAC[TOKENS_def; SPLITP_DEF] THEN
  SIMP[NULL; TL]);;

let TOKENS_END = prove
 (`!l (a:char). TOKENS (\x. x = a) (APPEND l [a]) = TOKENS (\x. x = a) l`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`\x:char. x = a`; `l:char list`; `a:char`; `[]:char list`]
    TOKENS_APPEND) THEN
  REWRITE_TAC[TOKENS_def; APPEND_NIL]);;

let TOKENS_LENGTH_END = prove
 (`!l (a:char). LENGTH (TOKENS (\x. x = a) (APPEND l [a])) =
                LENGTH (TOKENS (\x. x = a) l)`,
  REWRITE_TAC[TOKENS_END]);;

let TOKENS_LENGTH_START = prove
 (`!l (a:char). LENGTH (TOKENS (\x. x = a) (CONS a l)) =
                LENGTH (TOKENS (\x. x = a) l)`,
  REWRITE_TAC[TOKENS_START]);;

let DROP_EMPTY = prove
 (`!ls:A list n. DROP n ls = [] ==> n >= LENGTH ls`,
  REWRITE_TAC[DROP_EQ_NIL; GE]);;

let FRONT_APPEND' = prove
 (`!l (h:A list) a b t.
     l = APPEND (APPEND h [a; b]) t
     ==> BUTLAST l = APPEND h (BUTLAST (APPEND [a; b] t))`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[GSYM APPEND_ASSOC; APPEND; FRONT_APPEND]);;

let EVERY_NOT_IMP = prove
 (`!ls (a:A). ALL ((~) o (\x. x = a)) ls ==> LIST_ELEM_COUNT a ls = 0`,
  REWRITE_TAC[LIST_ELEM_COUNT_DEF] THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[ALL; FILTER; LENGTH; o_THM] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let LIST_ELEM_COUNT_CONS = prove
 (`!h t (a:A). LIST_ELEM_COUNT a (CONS h t) =
               LIST_ELEM_COUNT a [h] + LIST_ELEM_COUNT a t`,
  REWRITE_TAC[LIST_ELEM_COUNT_DEF; FILTER; LENGTH] THEN REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[LENGTH] THEN ARITH_TAC);;

let FRONT_COUNT_IMP = prove
 (`!l1 l2 (a:A).
     ~(l1 = []) /\ BUTLAST l1 = l2
     ==> LIST_ELEM_COUNT a l2 = LIST_ELEM_COUNT a l1 \/
         LIST_ELEM_COUNT a l2 + 1 = LIST_ELEM_COUNT a l1`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
  SUBGOAL_THEN
   `LIST_ELEM_COUNT (a:A) l1 =
    LIST_ELEM_COUNT a (BUTLAST l1) + LIST_ELEM_COUNT a [LAST l1]`
   SUBST1_TAC THENL
   [GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
      [GSYM(MATCH_MP APPEND_BUTLAST_LAST (ASSUME `~(l1:A list = [])`))] THEN
    REWRITE_TAC[LIST_ELEM_COUNT_THM];
    REWRITE_TAC[LIST_ELEM_COUNT_DEF; FILTER; LENGTH] THEN
    COND_CASES_TAC THEN REWRITE_TAC[LENGTH] THEN ARITH_TAC]);;

let OPT_MMAP_MAP_o = prove
 (`!ls. OPT_MMAP (f:B->C option) (MAP (g:A->B) ls) = OPT_MMAP (f o g) ls`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[OPT_MMAP_DEF; MAP; o_THM]);;

let OPT_MMAP_SOME = prove
 (`OPT_MMAP SOME (ls:A list) = SOME ls`,
  SPEC_TAC(`ls:A list`,`ls:A list`) THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[OPT_MMAP_DEF; OPTION_BIND_DEF]);;
let _ = cake_add_simps [OPT_MMAP_SOME];;

(* HOL4 [defncong] (a congruence rule for termination proofs) *)
let OPT_MMAP_CONG = prove
 (`!l1 l2 (f:A->B option) f'.
     l1 = l2 /\ (!x. MEM x l2 ==> f x = f' x) ==> OPT_MMAP f l1 = OPT_MMAP f' l2`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC MP_TAC) THEN
  SPEC_TAC(`l2:A list`,`l2:A list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[OPT_MMAP_DEF; MEM] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(f:A->B option) h = f' h /\ OPT_MMAP f t = OPT_MMAP f' t`
    (fun th -> REWRITE_TAC[th]) THEN
  ASM_MESON_TAC[]);;

let IMP_OPT_MMAP_EQ = prove
 (`!l1 l2. MAP (f1:A->C option) l1 = MAP (f2:B->C option) l2
           ==> OPT_MMAP f1 l1 = OPT_MMAP f2 l2`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP; OPT_MMAP_DEF; NOT_CONS_NIL; NOT_NIL_CONS; CONS_11] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `OPT_MMAP (f1:A->C option) t = OPT_MMAP (f2:B->C option) t'`
    SUBST1_TAC THENL [ASM_MESON_TAC[]; ASM_REWRITE_TAC[]]);;

let DISJOINT_set_simp = prove
 (`DISJOINT (set_of_list []) (s:A->bool) /\
   (DISJOINT (set_of_list (CONS x xs)) s <=>
    ~(x IN s) /\ DISJOINT (set_of_list xs) s)`,
  REWRITE_TAC[set_of_list; DISJOINT_EMPTY; DISJOINT_INSERT] THEN
  CONV_TAC TAUT);;

let DISJOINT_INTER = prove
 (`DISJOINT b c ==> DISJOINT ((a:A->bool) INTER b) (a INTER c)`,
  SET_TAC[]);;

let ALOOKUP_EXISTS_IFF = prove
 (`(?v. ALOOKUP alist (k:A) = SOME v) <=> (?v:B. MEM (k,v) alist)`,
  MP_TAC(ISPECL [`alist:(A#B)list`; `k:A`] ALOOKUP_NONE) THEN
  CASES_ON `ALOOKUP (alist:(A#B)list) (k:A)` THEN
  REWRITE_TAC[option_DISTINCT; option_INJ; MEM_MAP; EXISTS_PAIR_THM; FST] THEN
  MESON_TAC[]);;

let LUPDATE_commutes = prove
 (`!m n (e1:A) e2 l.
     ~(m = n) ==> LUPDATE e1 m (LUPDATE e2 n l) = LUPDATE e2 n (LUPDATE e1 m l)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIST_EQ_REWRITE; LENGTH_LUPDATE] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REWRITE_TAC[EL_LUPDATE; LENGTH_LUPDATE] THEN
  REPEAT COND_CASES_TAC THEN ASM_MESON_TAC[]);;

let LUPDATE_APPEND = prove
 (`!xs n ys (x:A).
     LUPDATE x n (APPEND xs ys) =
     if n < LENGTH xs then APPEND (LUPDATE x n xs) ys
     else APPEND xs (LUPDATE x (n - LENGTH xs) ys)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND; LENGTH; CONJUNCT1 LT; SUB_0] THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[LUPDATE_def; LT_0; LT_SUC; SUB_SUC] THEN
  REPEAT GEN_TAC THEN TRY COND_CASES_TAC THEN REWRITE_TAC[APPEND]);;

let FILTER_EL_EQ = prove
 (`!l1 l2:A list.
     LENGTH l1 = LENGTH l2 /\
     (!n. n < LENGTH l1 /\ (P (EL n l1) \/ P (EL n l2)) ==> EL n l1 = EL n l2)
     ==> FILTER P l1 = FILTER P l2`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ; FILTER] THEN STRIP_TAC THEN
  SUBGOAL_THEN `FILTER P t = FILTER (P:A->bool) t'` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `SUC n`) THEN ASM_REWRITE_TAC[EL; TL; LT_SUC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN REWRITE_TAC[EL; HD; LT_0] THEN
  ASM_CASES_TAC `(P:A->bool) h` THEN ASM_CASES_TAC `(P:A->bool) h'` THEN
  ASM_REWRITE_TAC[CONS_11] THEN ASM_MESON_TAC[]);;

let FST_EL_AFUPDKEY = prove
 (`!n. n < LENGTH ls ==> FST (EL n (AFUPDKEY (k:A) (f:B->B) ls)) = FST (EL n ls)`,
  SPEC_TAC(`ls:(A#B)list`,`ls:(A#B)list`) THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; CONJUNCT1 LT] THEN
  STRUCT_CASES_TAC(ISPEC `h:A#B` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[AFUPDKEY_def] THEN INDUCT_TAC THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[EL; HD; TL; LT_SUC; FST]);;

let EL_AFUPDKEY_unchanged = prove
 (`!n. n < LENGTH ls /\ ~(FST (EL n ls) = k)
       ==> EL n (AFUPDKEY (k:A) (f:B->B) ls) = EL n ls`,
  SPEC_TAC(`ls:(A#B)list`,`ls:(A#B)list`) THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; CONJUNCT1 LT] THEN
  STRUCT_CASES_TAC(ISPEC `h:A#B` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[AFUPDKEY_def] THEN INDUCT_TAC THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[EL; HD; TL; LT_SUC; FST] THEN
  ASM_MESON_TAC[]);;

let findi_APPEND = prove
 (`!l1 l2 (x:A).
     findi x (APPEND l1 l2) =
     let n0 = findi x l1 in
     if n0 = LENGTH l1 then n0 + findi x l2 else n0`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND; findi_def; LENGTH; LET_DEF; LET_END_DEF; ADD_CLAUSES] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[NOT_SUC] THEN
  REWRITE_TAC[ARITH_RULE `1 + n = SUC m <=> n = m`] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let NOT_MEM_findi_IFF = prove
 (`~MEM (e:A) l <=> findi e l = LENGTH l`,
  SPEC_TAC(`l:A list`,`l:A list`) THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MEM; findi_def; LENGTH] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[NOT_SUC] THEN ARITH_TAC);;

(* HOL4: the left-to-right half of NOT_MEM_findi_IFF *)
let NOT_MEM_findi = prove
 (`~MEM (e:A) l ==> findi e l = LENGTH l`,
  REWRITE_TAC[NOT_MEM_findi_IFF]);;

let ORD_eq_0 = prove
 (`(ORD c = 0 <=> c = CHR 0) /\ (0 = ORD c <=> c = CHR 0)`,
  MESON_TAC[CHR_ORD; ORD_CHR_RWT; ARITH_RULE `0 < 256`]);;


let HD_LUPDATE = prove
 (`0 < LENGTH l ==> HD (LUPDATE (x:A) p l) = if p = 0 then x else HD l`,
  STRUCT_CASES_TAC(ISPEC `l:A list` list_CASES) THEN
  REWRITE_TAC[LENGTH; LT_REFL; LUPDATE_DEF] THEN
  COND_CASES_TAC THEN REWRITE_TAC[HD]);;

(* HOL4: DROP_LUPDATE *)
let misc_DROP_LUPDATE = prove
 (`!n (x:A) m l. n <= m ==> DROP n (LUPDATE x m l) = LUPDATE x (m - n) (DROP n l)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[LIST_EQ_REWRITE; LENGTH_DROP; LENGTH_LUPDATE] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `i + n < LENGTH (l:A list)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[EL_DROP; LENGTH_LUPDATE; EL_LUPDATE; LENGTH_DROP] THEN
  ASM_CASES_TAC `i = m - n` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `m - n + n = m` (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC;
    SUBGOAL_THEN `~(i + n = m)` (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC]);;

(* HOL4: w2n_lt at word8 (dimword(:8) = 256); HOL4 word8 is byte = (8)word *)
let w2n_lt_256 = prove
 (`!w:byte. val w < 256`,
  GEN_TAC THEN MP_TAC(ISPEC `w:byte` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV);;

let CHR_w2n_n2w_ORD = prove
 (`CHR o val o (word:num->byte) o ORD = I`,
  REWRITE_TAC[FUN_EQ_THM; o_THM; I_THM; VAL_WORD; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[MOD_LT; ORD_BOUND; CHR_ORD]);;

let n2w_ORD_CHR_w2n = prove
 (`(word:num->byte) o ORD o CHR o val = I`,
  REWRITE_TAC[FUN_EQ_THM; o_THM; I_THM] THEN
  SIMP_TAC[w2n_lt_256; ORD_CHR_RWT; WORD_VAL]);;

let CHR_w2n_n2w_ORD_simp = prove
 (`!c. CHR (val ((word:num->byte) (ORD c))) = c`,
  MESON_TAC[CHR_w2n_n2w_ORD; o_THM; I_THM]);;
let _ = cake_add_simps [CHR_w2n_n2w_ORD_simp];;

let n2w_ORD_CHR_w2n_simp = prove
 (`!w. word (ORD (CHR (val w))) = (w:byte)`,
  MESON_TAC[n2w_ORD_CHR_w2n; o_THM; I_THM]);;
let _ = cake_add_simps [n2w_ORD_CHR_w2n_simp];;

let MAP_CHR_w2n_11 = prove
 (`!ws1 ws2:byte list.
     MAP (CHR o val) ws1 = MAP (CHR o val) ws2 <=> ws1 = ws2`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[MAP; NOT_CONS_NIL; NOT_NIL_CONS; CONS_11; o_THM] THEN
  SIMP_TAC[CHR_11; w2n_lt_256; VAL_EQ]);;

let MAP_K_REPLICATE = prove
 (`MAP (K (x:B)) (ls:A list) = REPLICATE (LENGTH ls) x`,
  SPEC_TAC(`ls:A list`,`ls:A list`) THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; LENGTH; REPLICATE; K_THM]);;
(* HOL4 a << n is word_shl a n, a >>> n is word_ushr a n, 0w is word 0 *)
let shift_left_def = cake_def_wf
  `MEASURE (\p:(N word)#num. SND p)`
  (REWRITE_TAC[measure_THM] THEN ARITH_TAC)
  `shift_left (a:N word) n =
     if n = 0 then a
     else if a = word 0 \/ n > dimindex(:N) then word 0
     else if n > 32 then shift_left (word_shl a 32) (n - 32)
     else if n > 16 then shift_left (word_shl a 16) (n - 16)
     else if n > 8 then shift_left (word_shl a 8) (n - 8)
     else shift_left (word_shl a 1) (n - 1)`;;

let shift_left_rwt = prove
 (`!(a:N word) n. word_shl a n = shift_left a n`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  X_GEN_TAC `a:N word` THEN ONCE_REWRITE_TAC[shift_left_def] THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[WORD_SHL_ZERO] THEN
  ASM_CASES_TAC `a:N word = word 0` THEN ASM_REWRITE_TAC[WORD_SHL_0] THEN
  ASM_CASES_TAC `n > dimindex(:N)` THEN ASM_REWRITE_TAC[] THENL
   [MATCH_MP_TAC WORD_SHL_TRIVIAL THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REPEAT COND_CASES_TAC THEN
  FIRST_X_ASSUM(fun th -> W(fun (_,w) -> MP_TAC(SPEC (rand(rand w)) th))) THEN
  (ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th; WORD_SHL_COMPOSE]) THEN
  AP_TERM_TAC THEN ASM_ARITH_TAC);;

let shift_right_def = cake_def_wf
  `MEASURE (\p:(N word)#num. SND p)`
  (REWRITE_TAC[measure_THM] THEN ARITH_TAC)
  `shift_right (a:N word) n =
     if n = 0 then a
     else if a = word 0 \/ n > dimindex(:N) then word 0
     else if n > 32 then shift_right (word_ushr a 32) (n - 32)
     else if n > 16 then shift_right (word_ushr a 16) (n - 16)
     else if n > 8 then shift_right (word_ushr a 8) (n - 8)
     else shift_right (word_ushr a 1) (n - 1)`;;

let shift_right_rwt = prove
 (`!(a:N word) n. word_ushr a n = shift_right a n`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  X_GEN_TAC `a:N word` THEN ONCE_REWRITE_TAC[shift_right_def] THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[WORD_USHR_ZERO] THEN
  ASM_CASES_TAC `a:N word = word 0` THEN ASM_REWRITE_TAC[WORD_USHR_0] THEN
  ASM_CASES_TAC `n > dimindex(:N)` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[WORD_USHR_EQ_0] THEN MATCH_MP_TAC LTE_TRANS THEN
    EXISTS_TAC `2 EXP dimindex(:N)` THEN
    REWRITE_TAC[VAL_BOUND; LE_EXP; ARITH_EQ] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT COND_CASES_TAC THEN
  FIRST_X_ASSUM(fun th -> W(fun (_,w) -> MP_TAC(SPEC (rand(rand w)) th))) THEN
  (ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th; WORD_USHR_COMPOSE]) THEN
  AP_TERM_TAC THEN ASM_ARITH_TAC);;

(* HOL4 a >> n is word_ishr a n and -1w is word_neg (word 1) *)
let arith_shift_right_def = cake_def_wf
  `MEASURE (\p:(N word)#num. SND p)`
  (REWRITE_TAC[measure_THM] THEN ARITH_TAC)
  `arith_shift_right (a:N word) n =
     if n = 0 then a
     else if a = word 0 \/ n > dimindex(:N) /\ ~word_msb a then word 0
     else if a = word_neg (word 1) \/ n > dimindex(:N) /\ word_msb a
     then word_neg (word 1)
     else if n > 32 then arith_shift_right (word_ishr a 32) (n - 32)
     else if n > 16 then arith_shift_right (word_ishr a 16) (n - 16)
     else if n > 8 then arith_shift_right (word_ishr a 8) (n - 8)
     else arith_shift_right (word_ishr a 1) (n - 1)`;;

let arith_shift_right_rwt = prove
 (`!(a:N word) n. word_ishr a n = arith_shift_right a n`,
  SUBGOAL_THEN
   `!(a:N word) n. dimindex(:N) <= n
      ==> word_ishr a n = if word_msb a then word_neg (word 1) else word 0`
   ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(i + n < dimindex(:N))` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[BIT_WORD_ISHR; word_msb_def] THEN
    COND_CASES_TAC THEN
    ASM_REWRITE_TAC[WORD_NEG_1; BIT_WORD_NOT; BIT_WORD_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `!n. word_ishr (word_neg (word 1):N word) n = word_neg (word 1)`
    ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MP_TAC(ISPEC `(:N)` DIMINDEX_GE_1) THEN
    ASM_REWRITE_TAC[BIT_WORD_ISHR; WORD_NEG_1; BIT_WORD_NOT; BIT_WORD_0] THEN
    DISCH_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  X_GEN_TAC `a:N word` THEN ONCE_REWRITE_TAC[arith_shift_right_def] THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[WORD_ISHR_ZERO] THEN
  ASM_CASES_TAC `a:N word = word 0` THEN ASM_REWRITE_TAC[WORD_ISHR_0] THEN
  ASM_CASES_TAC `n > dimindex(:N) /\ ~word_msb (a:N word)` THENL
   [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC) THEN
    ASM_SIMP_TAC[ARITH_RULE `n > d ==> d <= n`];
    ASM_REWRITE_TAC[]] THEN
  ASM_CASES_TAC `a:N word = word_neg (word 1)` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `n > dimindex(:N) /\ word_msb (a:N word)` THENL
   [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC) THEN
    ASM_SIMP_TAC[ARITH_RULE `n > d ==> d <= n`];
    ASM_REWRITE_TAC[]] THEN
  REPEAT COND_CASES_TAC THEN
  FIRST_X_ASSUM(fun th -> W(fun (_,w) -> MP_TAC(SPEC (rand(rand w)) th))) THEN
  (ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th; WORD_ISHR_COMPOSE]) THEN
  AP_TERM_TAC THEN ASM_ARITH_TAC);;


(* HOL4 word64 is int64 = (64)word *)
let any_word64_ror_def = cake_def_wf
  `MEASURE (\p:int64#num. SND p)`
  (REWRITE_TAC[measure_THM] THEN ARITH_TAC)
  `any_word64_ror (w:int64) (n:num) =
     if 64 <= n then any_word64_ror w (n - 64) else
     if 32 <= n then any_word64_ror (word_ror w 32) (n - 32) else
     if 16 <= n then any_word64_ror (word_ror w 16) (n - 16) else
     if 8 <= n then any_word64_ror (word_ror w 8) (n - 8) else
     if 4 <= n then any_word64_ror (word_ror w 4) (n - 4) else
     if 2 <= n then any_word64_ror (word_ror w 2) (n - 2) else
     if 1 <= n then word_ror w 1 else w`;;

let word_ror_eq_any_word64_ror = prove
 (`!(a:int64) n. word_ror a n = any_word64_ror a n`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  X_GEN_TAC `a:int64` THEN ONCE_REWRITE_TAC[any_word64_ror_def] THEN
  ASM_CASES_TAC `64 <= n` THEN ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `n - 64`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
    SUBGOAL_THEN `word_ror (a:int64) n = word_ror (word_ror a (n - 64)) 64`
      SUBST1_TAC THENL
     [REWRITE_TAC[WORD_ROR_COMPOSE] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
      MATCH_MP_TAC WORD_ROR_EQ_SELF THEN
      REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUMBER_RULE];
    ALL_TAC] THEN
  REPEAT COND_CASES_TAC THEN
  TRY(FIRST_X_ASSUM(fun th -> W(fun (_,w) -> MP_TAC(SPEC (rand(rand w)) th))) THEN
      (ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[GSYM th; WORD_ROR_COMPOSE]) THEN
      AP_TERM_TAC THEN ASM_ARITH_TAC) THEN
  TRY(AP_TERM_TAC THEN ASM_ARITH_TAC) THEN
  SUBGOAL_THEN `n = 0` SUBST1_TAC THENL
   [ASM_ARITH_TAC; REWRITE_TAC[WORD_ROR_ZERO]]);;

let TL_DROP_SUC = prove
 (`!x ls:A list. x < LENGTH ls ==> TL (DROP x ls) = DROP (SUC x) ls`,
  INDUCT_TAC THEN GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `ls:A list` list_CASES) THEN
  REWRITE_TAC[LENGTH; CONJUNCT1 LT; LT_SUC; RICHAUX_DROP_CLAUSES; TL] THEN
  ASM_SIMP_TAC[]);;

let DROP_IMP_LESS_LENGTH = prove
 (`!xs n (y:A) ys. DROP n xs = CONS y ys ==> n < LENGTH xs`,
  MESON_TAC[DROP_LENGTH_TOO_LONG; NOT_LT; NOT_NIL_CONS]);;

let DROP_EQ_CONS_IMP_DROP_SUC = prove
 (`!xs n (y:A) ys. DROP n xs = CONS y ys ==> DROP (SUC n) xs = ys`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[DROP_SUC] THEN
  ASM_REWRITE_TAC[DROP_DEF] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[DROP_0]);;

let DROP_IMP_EL = prove
 (`!xs n (h:A) t. DROP n xs = CONS h t ==> EL n xs = h`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DROP_IMP_LESS_LENGTH) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP DROP_EL_CONS) THEN
  ASM_REWRITE_TAC[CONS_11] THEN MESON_TAC[]);;

let LENGTH_FIELDS = prove
 (`!ls. LENGTH (FIELDS P ls) = LENGTH (FILTER P ls) + 1`,
  SPEC_TAC(`P:char->bool`,`P:char->bool`) THEN
  MATCH_MP_TAC FIELDS_ind THEN CONJ_TAC THENL
   [REWRITE_TAC[FIELDS_def; FILTER; LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `SPLITP P (CONS (h:char) t)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `l:char list` (X_CHOOSE_THEN `r:char list`
    ASSUME_TAC)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPECL [`l:char list`; `r:char list`])
                             (MP_TAC o SPECL [`l:char list`; `r:char list`])) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SPLITP_JOIN) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SPLITP_IMP) THEN
  SUBGOAL_THEN `FILTER P (CONS (h:char) t) = FILTER P r` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[FILTER_APPEND] THEN
    SUBGOAL_THEN `FILTER (P:char->bool) l = []`
      (fun th -> REWRITE_TAC[th; APPEND]) THEN
    REWRITE_TAC[FILTER_EQ_NIL] THEN
    UNDISCH_TAC `ALL ((~) o (P:char->bool)) l` THEN REWRITE_TAC[o_DEF];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[FIELDS_def] THEN SIMP[] THEN
  CASES_ON `r:char list` THEN CASES_ON `l:char list` THEN
  REWRITE_TAC[NULL; TL; LENGTH; FILTER] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NULL; HD; APPEND; APPEND_NIL; NOT_CONS_NIL]) THEN
  TRY(FIRST_ASSUM CONTR_TAC) THEN ASM_REWRITE_TAC[LENGTH] THEN ARITH_TAC);;

let FIELDS_NEQ_NIL = prove
 (`~(FIELDS P ls = [])`,
  DISCH_THEN(MP_TAC o AP_TERM `LENGTH:(char list)list->num`) THEN
  REWRITE_TAC[LENGTH_FIELDS; LENGTH] THEN ARITH_TAC);;
let _ = cake_add_simps [FIELDS_NEQ_NIL];;

(* HOL4: CONCAT, an overload of FLAT on strings *)
let CONCAT_FIELDS = prove
 (`!ls. FLAT (FIELDS P ls) = FILTER ((~) o P) ls`,
  SPEC_TAC(`P:char->bool`,`P:char->bool`) THEN
  MATCH_MP_TAC FIELDS_ind THEN CONJ_TAC THENL
   [REWRITE_TAC[FIELDS_def; FILTER; FLAT; APPEND]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `SPLITP P (CONS (h:char) t)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `l:char list` (X_CHOOSE_THEN `r:char list`
    ASSUME_TAC)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPECL [`l:char list`; `r:char list`])
                             (MP_TAC o SPECL [`l:char list`; `r:char list`])) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SPLITP_JOIN) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SPLITP_IMP) THEN
  SUBGOAL_THEN
   `FILTER ((~) o P) (CONS (h:char) t) = APPEND l (FILTER ((~) o P) r)`
   SUBST1_TAC THENL
   [ASM_REWRITE_TAC[FILTER_APPEND] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    ASM_REWRITE_TAC[FILTER_EQ_ID];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[FIELDS_def] THEN SIMP[] THEN
  CASES_ON `r:char list` THEN CASES_ON `l:char list` THEN
  REWRITE_TAC[NULL; TL; FLAT; FILTER; APPEND; APPEND_NIL; o_THM] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NULL; HD; APPEND; APPEND_NIL; NOT_CONS_NIL]) THEN
  TRY(FIRST_ASSUM CONTR_TAC) THEN ASM_SIMP_TAC[]);;

let FIELDS_next = prove
 (`!ls l1 l2.
     FIELDS P ls = CONS l1 l2
     ==> LENGTH l1 < LENGTH ls
     ==> FIELDS P (DROP (SUC (LENGTH l1)) ls) = l2 /\
         (?c. APPEND l1 [c] <<= ls /\ P c)`,
  SUBGOAL_THEN
   `!l:char list (c:char) r.
      DROP (SUC (LENGTH l)) (APPEND l (CONS c r)) = r /\
      APPEND l [c] <<= APPEND l (CONS c r)`
   ASSUME_TAC THENL
   [LIST_INDUCT_TAC THEN
    ASM_REWRITE_TAC[LENGTH; APPEND; RICHAUX_DROP_CLAUSES; isPREFIX_THM];
    ALL_TAC] THEN
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[FIELDS_def; CONS_11; LENGTH; CONJUNCT1 LT]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `SPLITP P (CONS (h:char) t)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `l:char list` (X_CHOOSE_THEN `r:char list`
    ASSUME_TAC)) THEN
  REWRITE_TAC[FIELDS_def] THEN ASM_REWRITE_TAC[pair_CASE] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SPLITP_JOIN) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SPLITP_IMP) THEN
  FIRST_ASSUM SUBST1_TAC THEN
  CASES_ON `r:char list` THEN CASES_ON `l:char list` THEN
  REWRITE_TAC[NULL; TL; CONS_11] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NULL; HD; APPEND; NOT_CONS_NIL]) THEN
  TRY(FIRST_ASSUM CONTR_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  ASM_REWRITE_TAC[APPEND_NIL; LT_REFL] THEN ASM_MESON_TAC[]);;

let FIELDS_full = prove
 (`!P ls l1 l2.
     FIELDS P ls = CONS l1 l2 /\ LENGTH ls <= LENGTH l1 ==> l1 = ls /\ l2 = []`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[FIELDS_def; CONS_11] THEN MESON_TAC[]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `SPLITP P (CONS (h:char) t)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `l:char list` (X_CHOOSE_THEN `r:char list`
    ASSUME_TAC)) THEN
  REWRITE_TAC[FIELDS_def] THEN ASM_REWRITE_TAC[pair_CASE] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SPLITP_JOIN) THEN
  FIRST_ASSUM SUBST1_TAC THEN
  CASES_ON `r:char list` THEN CASES_ON `l:char list` THEN
  REWRITE_TAC[NULL; TL; CONS_11] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[APPEND; NOT_CONS_NIL]) THEN
  TRY(FIRST_ASSUM CONTR_TAC) THEN
  REWRITE_TAC[APPEND_NIL; LENGTH_APPEND; LENGTH] THEN
  STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[LENGTH] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[LENGTH] THEN ARITH_TAC);;

let FLAT_MAP_TOKENS_FIELDS = prove
 (`!P' ls P.
     (!x. P' x ==> P x)
     ==> FLAT (MAP (TOKENS P) (FIELDS P' ls)) = TOKENS P ls`,
  MATCH_MP_TAC FIELDS_ind THEN CONJ_TAC THENL
   [REWRITE_TAC[FIELDS_def; MAP; FLAT; TOKENS_def; APPEND]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`P':char->bool`; `h:char`; `t:char list`] THEN
  MP_TAC(ISPEC `SPLITP P' (CONS (h:char) t)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `l:char list` (X_CHOOSE_THEN `r:char list`
    ASSUME_TAC)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPECL [`l:char list`; `r:char list`])
                             (MP_TAC o SPECL [`l:char list`; `r:char list`])) THEN
  REWRITE_TAC[FIELDS_def] THEN ASM_REWRITE_TAC[pair_CASE] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SPLITP_JOIN) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SPLITP_IMP) THEN
  FIRST_ASSUM SUBST1_TAC THEN
  CASES_ON `r:char list` THEN CASES_ON `l:char list` THEN
  REWRITE_TAC[NULL; TL] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NULL; HD; APPEND; NOT_CONS_NIL]) THEN
  TRY(FIRST_ASSUM CONTR_TAC) THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[MAP; FLAT; APPEND_NIL] THEN
  ASM_SIMP_TAC[TOKENS_APPEND] THEN
  REWRITE_TAC[TOKENS_def; APPEND]);;

let the_nil_eq_cons = prove
 (`misc_the [] x = CONS (y:A) z <=> x = SOME (CONS y z)`,
  CASES_ON `x:(A list)option` THEN
  REWRITE_TAC[misc_the_def; option_INJ; option_DISTINCT; NOT_NIL_CONS]);;

(* HOL4 #"\n" is CHR 10; the HOL4 comment: discard trailing newline *)
let splitlines_def = cake_def
  `splitlines ls =
     let lines = FIELDS ((=) (CHR 10)) ls in
     if NULL (LAST lines) then BUTLAST lines else lines`;;

let splitlines_next = prove
 (`splitlines ls = CONS ln lns
   ==> splitlines (DROP (SUC (LENGTH ln)) ls) = lns /\ ln <<= ls /\
       (LENGTH ln < LENGTH ls ==> APPEND ln [CHR 10] <<= ls)`,
  REWRITE_TAC[splitlines_def; LET_DEF; LET_END_DEF] THEN
  MP_TAC(ISPEC `FIELDS ((=) (CHR 10)) ls` list_CASES) THEN
  REWRITE_TAC[FIELDS_NEQ_NIL] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:char list` (X_CHOOSE_THEN `t:(char list)list`
    ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `LENGTH (h:char list) < LENGTH (ls:char list)` THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP FIELDS_next) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `c:char`
      (CONJUNCTS_THEN2 ASSUME_TAC (SUBST_ALL_TAC o SYM)))) THEN
    SUBGOAL_THEN `~(t:(char list)list = [])` ASSUME_TAC THENL
     [ASM_MESON_TAC[FIELDS_NEQ_NIL]; ALL_TAC] THEN
    ASM_REWRITE_TAC[LAST; BUTLAST] THEN
    COND_CASES_TAC THEN REWRITE_TAC[CONS_11] THEN
    DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[IS_PREFIX_APPEND1];
    MP_TAC(ISPECL [`(=) (CHR 10)`; `ls:char list`; `h:char list`;
                   `t:(char list)list`] FIELDS_full) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN SUBST_ALL_TAC) THEN
    REWRITE_TAC[LAST; BUTLAST] THEN
    COND_CASES_TAC THEN REWRITE_TAC[NOT_NIL_CONS; CONS_11] THEN
    DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    SIMP_TAC[DROP_LENGTH_TOO_LONG; ARITH_RULE `n <= SUC n`] THEN
    REWRITE_TAC[FIELDS_def; LAST; BUTLAST; NULL; IS_PREFIX_REFL; LT_REFL]]);;

(* HOL4: the EVAL theorem for splitlines of the empty string *)
let splitlines_nil = prove
 (`splitlines [] = []`,
  REWRITE_TAC[splitlines_def; LET_DEF; LET_END_DEF; FIELDS_def; LAST;
              BUTLAST; NULL]);;
let _ = cake_add_simps [splitlines_nil];;

let splitlines_eq_nil = prove
 (`splitlines ls = [] <=> ls = []`,
  EQ_TAC THENL [ALL_TAC; DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[splitlines_nil]] THEN
  REWRITE_TAC[splitlines_def; LET_DEF; LET_END_DEF] THEN
  MP_TAC(ISPEC `FIELDS ((=) (CHR 10)) ls` list_CASES) THEN
  REWRITE_TAC[FIELDS_NEQ_NIL] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:char list` (X_CHOOSE_THEN `t:(char list)list`
    ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[LAST; BUTLAST] THEN
  ASM_CASES_TAC `t:(char list)list = []` THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN REWRITE_TAC[NOT_CONS_NIL] THEN
  SUBGOAL_THEN `FIELDS ((=) (CHR 10)) ls = [[]]` MP_TAC THENL
   [ASM_REWRITE_TAC[CONS_11] THEN ASM_MESON_TAC[NULL_EQ]; ALL_TAC] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN DISCH_TAC THEN
  MP_TAC(INST [`(=) (CHR 10)`,`P:char->bool`] (SPEC `ls:char list` LENGTH_FIELDS)) THEN
  MP_TAC(INST [`(=) (CHR 10)`,`P:char->bool`] (SPEC `ls:char list` CONCAT_FIELDS)) THEN
  ASM_REWRITE_TAC[FLAT; APPEND; LENGTH; ARITH_RULE `SUC 0 = n + 1 <=> n = 0`;
                  LENGTH_EQ_NIL] THEN
  REWRITE_TAC[IMP_IMP] THEN DISCH_THEN(MP_TAC o MATCH_MP (MESON[]
   `[] = FILTER (P:char->bool) l /\ FILTER (Q:char->bool) l = []
    ==> FILTER P l = [] /\ FILTER Q l = []`)) THEN
  REWRITE_TAC[FILTER_EQ_NIL] THEN
  STRUCT_CASES_TAC(ISPEC `ls:char list` list_CASES) THEN
  REWRITE_TAC[ALL; o_THM; NOT_CONS_NIL] THEN CONV_TAC TAUT);;
let _ = cake_add_simps [splitlines_eq_nil];;

let splitlines_CONS_FST_SPLITP = prove
 (`splitlines ls = CONS ln lns ==> FST (SPLITP ((=) (CHR 10)) ls) = ln`,
  SUBGOAL_THEN
   `!x (y:(char list)list).
      (if NULL (LAST (CONS x y)) then BUTLAST (CONS x y) else CONS x y) =
      CONS ln lns ==> x = ln`
   ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `y:(char list)list` list_CASES) THEN
    REWRITE_TAC[LAST; BUTLAST; NOT_CONS_NIL] THEN
    REPEAT COND_CASES_TAC THEN REWRITE_TAC[NOT_NIL_CONS; CONS_11] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[splitlines_def; LET_DEF; LET_END_DEF] THEN
  STRUCT_CASES_TAC(ISPEC `ls:char list` list_CASES) THEN
  REWRITE_TAC[FIELDS_def; LAST; BUTLAST; NULL; NOT_NIL_CONS] THEN
  MP_TAC(ISPEC `SPLITP ((=) (CHR 10)) (CONS h t)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `l:char list` (X_CHOOSE_THEN `r:char list`
    SUBST1_TAC)) THEN
  REWRITE_TAC[pair_CASE; FST] THEN
  ASM_CASES_TAC `NULL (l:char list)` THEN ASM_REWRITE_TAC[] THEN
  TRY(ASM_CASES_TAC `NULL (r:char list)` THEN ASM_REWRITE_TAC[]) THEN
  DISCH_THEN(fun th -> FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN
  ASM_MESON_TAC[NULL_EQ]);;

let n2l_DIV_MOD = prove
 (`!b n k. 1 < b /\ 0 < k /\ b EXP k <= n
     ==> APPEND (APPEND (n2l b (n MOD (b EXP k)))
                        (REPLICATE (k - LENGTH (n2l b (n MOD (b EXP k)))) 0))
                (n2l b (n DIV (b EXP k))) = n2l b n`,
  GEN_TAC THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  INDUCT_TAC THEN REWRITE_TAC[LT_REFL] THEN
  POP_ASSUM(LABEL_TAC "ih") THEN
  X_GEN_TAC `n:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(b = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!m. b <= m ==> n2l b m = CONS (m MOD b) (n2l b (m DIV b))`
    ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN GEN_REWRITE_TAC LAND_CONV [n2l_def] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!m. m < b ==> n2l b m = [m]` ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN GEN_REWRITE_TAC LAND_CONV [n2l_def] THEN
    ASM_SIMP_TAC[MOD_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `b <= n` ASSUME_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `b EXP SUC k` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `b EXP 1` THEN
    CONJ_TAC THENL [REWRITE_TAC[EXP_1; LE_REFL]; ALL_TAC] THEN
    ASM_REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [MATCH_MP th (ASSUME `b <= n`)]) THEN
  REWRITE_TAC[EXP; GSYM DIV_DIV; MOD_MULT_MOD] THEN
  ASM_CASES_TAC `k = 0` THENL
   [ASM_REWRITE_TAC[EXP; MOD_1; DIV_1; MULT_CLAUSES; ADD_CLAUSES] THEN
    SUBGOAL_THEN `n MOD b < b` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[MOD_LT_EQ]; ALL_TAC] THEN
    ASM_SIMP_TAC[LENGTH; SUB_REFL; REPLICATE; APPEND; APPEND_NIL];
    ALL_TAC] THEN
  REMOVE_THEN "ih" (MP_TAC o SPEC `n DIV b`) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[LE_RDIV_EQ] THEN UNDISCH_TAC `b EXP SUC k <= n` THEN
    REWRITE_TAC[EXP] THEN ASM_ARITH_TAC;
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  SPEC_TAC(`n2l b (n DIV b DIV b EXP k)`,`d:num list`) THEN
  SPEC_TAC(`n DIV b MOD b EXP k`,`r:num`) THEN
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `n MOD b < b` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[MOD_LT_EQ]; ALL_TAC] THEN
  ASM_CASES_TAC `r = 0` THENL
   [ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
    SUBGOAL_THEN `n2l b (n MOD b) = [n MOD b] /\ n2l b 0 = [0]`
      (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `k = SUC (k - 1)` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[LENGTH; SUB_SUC; SUB_0; REPLICATE; APPEND];
    ALL_TAC] THEN
  SUBGOAL_THEN `n2l b (b * r + n MOD b) = CONS (n MOD b) (n2l b r)` SUBST1_TAC THENL
   [MP_TAC(SPEC `b * r + n MOD b` (ASSUME
      `!m. b <= m ==> n2l b m = CONS (m MOD b) (n2l b (m DIV b))`)) THEN
    ANTS_TAC THENL
     [SUBGOAL_THEN `b * 1 <= b * r` MP_TAC THENL
       [REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC; ARITH_TAC];
      DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[MOD_MULT_ADD; MOD_MOD_REFL; CONS_11] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `n MOD b` THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    REWRITE_TAC[LENGTH; SUB_SUC; APPEND]]);;


let irreflexive_inv_image = prove
 (`!(R:B->B->bool) (f:A->B). irreflexive R ==> irreflexive (inv_image R f)`,
  REWRITE_TAC[irreflexive_DEF; inv_image_THM] THEN MESON_TAC[]);;

let trichotomous_inv_image = prove
 (`!(R:B->B->bool) (f:A->B).
     trichotomous R /\ INJ f UNIV UNIV ==> trichotomous (inv_image R f)`,
  REWRITE_TAC[trichotomous_DEF; inv_image_THM; INJ; IN_UNIV] THEN MESON_TAC[]);;

let MEM_REPLICATE_IMP = prove
 (`MEM (x:A) (REPLICATE n y) ==> x = y`,
  SPEC_TAC(`n:num`,`n:num`) THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[REPLICATE; MEM] THEN ASM_MESON_TAC[]);;

let plus_0_I = prove
 (`(+) 0 = I`,
  REWRITE_TAC[FUN_EQ_THM; I_THM; ADD_CLAUSES]);;
let _ = cake_add_simps [plus_0_I];;
