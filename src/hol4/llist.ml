(* ========================================================================= *)
(* llist: port of HOL4 src/coalgebras/llistScript.sml (the HOL4 library     *)
(* used by CakeML v3479): possibly infinite sequences (lazy lists).          *)
(*                                                                           *)
(* As in HOL4, A llist is the type of the functions f:num->A option that are *)
(* prefix closed (lrep_ok f: f n = NONE implies f (SUC n) = NONE), with      *)
(* llist_abs/llist_rep; LNIL, LCONS, LHD, LTL (option valued), LNTH, LUNFOLD *)
(* and the rest are defined from the representation, and the coinduction    *)
(* principles (LLIST_BISIMULATION, LLIST_EQ, ...) are theorems.             *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - HOL4 fromList/toList of this theory are llist_fromList/llist_toList     *)
(*   (sptree has fromList and toList); HOL4 exists is llist_exists (exists   *)
(*   is a binder keyword of the HOL Light parser).  Theorem names are HOL4's *)
(*   (LNTH_fromList, from_toList, exists_thm, ...).                          *)
(* - HOL4 case x of NONE => a | SOME (v1,v2) => b is written with match and  *)
(*   compiled by the kit to option_CASE/pair_CASE (CASE_TERM).              *)
(* - FUNPOW f n x is ITER n f x.  The [||] and ::: notations are not       *)
(*   defined: LNIL, LCONS h t.                                               *)
(* - Definitions: lrep_ok by its characterization lrep_ok_alt (coinductive   *)
(*   in HOL4); LNTH as llist_rep (LNTH_rep), HOL4 recursive equations are    *)
(*   the theorem LNTH; always by its coinduction invariant (always_def; HOL4 *)
(*   Hol_coreln).  The definition theorems of toList and fromList are        *)
(*   llist_toList and llist_fromList_def.                                    *)
(* - LLIST_CASE_TAC tm splits an llist term (the kit's CASES_ON does not     *)
(*   handle llist).                                                          *)
(* - Not ported (unused by the closure): LTL_HD, llist_CASE, LFILTER,        *)
(*   LFLATTEN, LZIP, LGENLIST, LREPEAT, llist_rel, fromSeq, LSUFFIX,         *)
(*   until, LTAKE_WHILE, LDROP_WHILE, lbind, linear_order_to_llist.          *)
(* - Lemmas named LLISTAUX_... are helpers of this file (not HOL4 names).    *)
(* - HOL4 eventually and every are llist_eventually and llist_every (short   *)
(*   or common words; eventually is also a constant of HOL Light's           *)
(*   Multivariate), with the theorems renamed alike (eventually_cases is     *)
(*   llist_eventually_cases, ...).                                           *)
(* ========================================================================= *)

needs "hol4/vocab.ml";;

(* ------------------------------------------------------------------------- *)
(* The representing type is num -> A option.                                 *)
(* ------------------------------------------------------------------------- *)

let lrep_ok_alt = new_definition
  `lrep_ok (f:num->A option) <=> !n. IS_SOME (f (SUC n)) ==> IS_SOME (f n)`;;

let LLISTAUX_IS_SOME_NONE = prove
 (`!x:A option. IS_SOME x <=> ~(x = NONE)`,
  MATCH_MP_TAC option_INDUCT THEN REWRITE_TAC[IS_SOME_DEF; option_DISTINCT]);;

let LLISTAUX_lrep_ok_NONE = prove
 (`!f:num->A option. lrep_ok f <=> !n. f n = NONE ==> f (SUC n) = NONE`,
  REWRITE_TAC[lrep_ok_alt; LLISTAUX_IS_SOME_NONE] THEN MESON_TAC[]);;

let LLISTAUX_lrep_ok_mono = prove
 (`!f:num->A option m n. lrep_ok f /\ f m = NONE /\ m <= n ==> f n = NONE`,
  REWRITE_TAC[LLISTAUX_lrep_ok_NONE] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!d. (f:num->A option) (m + d) = NONE` MP_TAC THENL
   [INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    DISCH_THEN(MP_TAC o SPEC `n - m:num`) THEN
    ASM_SIMP_TAC[ARITH_RULE `m <= n ==> m + (n - m) = n:num`]]);;

let lrep_ok_rules = prove
 (`lrep_ok (\n:num. NONE:A option) /\
   (!(h:A) t. lrep_ok t ==> lrep_ok (\n. if n = 0 then SOME h else t (n - 1)))`,
  REWRITE_TAC[lrep_ok_alt; IS_SOME_DEF] THEN REPEAT STRIP_TAC THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[NOT_SUC; SUC_SUB1] THEN
  STRUCT_CASES_TAC(SPEC `n:num` num_CASES) THEN
  ASM_REWRITE_TAC[NOT_SUC; SUC_SUB1; IS_SOME_DEF]);;

let llist_absrep = new_type_definition "llist" ("llist_abs","llist_rep")
 (prove(`?f:num->A option. lrep_ok f`,
        EXISTS_TAC `\n:num. NONE:A option` THEN
        REWRITE_TAC[lrep_ok_rules]));;

let lrep_ok_llist_rep = prove
 (`!l:A llist. lrep_ok (llist_rep l)`,
  MESON_TAC[llist_absrep]);;

let LLISTAUX_repabs = prove
 (`!r:num->A option. lrep_ok r ==> llist_rep (llist_abs r) = r`,
  MESON_TAC[llist_absrep]);;

let llist_abs_11 = prove
 (`!r1 r2:num->A option.
     lrep_ok r1 /\ lrep_ok r2 ==> (llist_abs r1 = llist_abs r2 <=> r1 = r2)`,
  MESON_TAC[llist_absrep]);;

let llist_rep_11 = prove
 (`!t1 t2:A llist. llist_rep t1 = llist_rep t2 <=> t1 = t2`,
  MESON_TAC[llist_absrep]);;

let LLISTAUX_rep_mono = prove
 (`!l:A llist m n. llist_rep l m = NONE /\ m <= n ==> llist_rep l n = NONE`,
  MESON_TAC[LLISTAUX_lrep_ok_mono; lrep_ok_llist_rep]);;

let LNIL = new_definition
  `LNIL = llist_abs (\n:num. NONE:A option)`;;

let LCONS = new_definition
  `LCONS (h:A) t = llist_abs (\n. if n = 0 then SOME h else llist_rep t (n - 1))`;;

let llist_rep_LCONS = prove
 (`!(h:A) t. llist_rep (LCONS h t) =
            \n. if n = 0 then SOME h else llist_rep t (n - 1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LCONS] THEN
  MATCH_MP_TAC LLISTAUX_repabs THEN
  MATCH_MP_TAC(CONJUNCT2 lrep_ok_rules) THEN
  REWRITE_TAC[ETA_AX; lrep_ok_llist_rep]);;

let llist_rep_LNIL = prove
 (`llist_rep (LNIL:A llist) = \n. NONE`,
  REWRITE_TAC[LNIL] THEN MATCH_MP_TAC LLISTAUX_repabs THEN
  REWRITE_TAC[lrep_ok_rules]);;

(* ------------------------------------------------------------------------- *)
(* Head, tail, cases, indexing (LNTH is llist_rep with arguments swapped).   *)
(* ------------------------------------------------------------------------- *)

let LHD = new_definition
  `LHD (ll:A llist) = llist_rep ll 0`;;

let LTL = new_definition
  `LTL (ll:A llist) =
     option_CASE (LHD ll) NONE (\x:A. SOME (llist_abs (\n. llist_rep ll (n + 1))))`;;

let LLISTAUX_lrep_ok_shift = prove
 (`!l:A llist. lrep_ok (\n. llist_rep l (n + 1))`,
  REWRITE_TAC[LLISTAUX_lrep_ok_NONE] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC LLISTAUX_rep_mono THEN EXISTS_TAC `n + 1` THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let LLISTAUX_rep_shift = prove
 (`!l:A llist. llist_rep (llist_abs (\n. llist_rep l (n + 1))) =
               \n. llist_rep l (n + 1)`,
  SIMP_TAC[LLISTAUX_repabs; LLISTAUX_lrep_ok_shift]);;

let llist_CASES = prove
 (`!l:A llist. l = LNIL \/ ?h t. l = LCONS h t`,
  GEN_TAC THEN ONCE_REWRITE_TAC[GSYM llist_rep_11] THEN
  REWRITE_TAC[llist_rep_LNIL; llist_rep_LCONS] THEN
  ASM_CASES_TAC `llist_rep (l:A llist) 0 = NONE` THENL
   [DISJ1_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `n:num` THEN
    MATCH_MP_TAC LLISTAUX_rep_mono THEN EXISTS_TAC `0` THEN
    ASM_REWRITE_TAC[LE_0];
    DISJ2_TAC THEN
    MP_TAC(ISPEC `llist_rep (l:A llist) 0` (cases "option")) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `h:A`) THEN
    MAP_EVERY EXISTS_TAC [`h:A`; `llist_abs (\n. llist_rep (l:A llist) (n + 1))`] THEN
    REWRITE_TAC[LLISTAUX_rep_shift; FUN_EQ_THM] THEN X_GEN_TAC `n:num` THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN ASM_ARITH_TAC]);;

let LLIST_CASE_TAC tm = STRUCT_CASES_TAC (ISPEC tm llist_CASES);;

let LCONS_NOT_NIL = prove
 (`!(h:A) t. ~(LCONS h t = LNIL) /\ ~(LNIL = LCONS h t)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM llist_rep_11] THEN
  REWRITE_TAC[llist_rep_LNIL; llist_rep_LCONS; FUN_EQ_THM] THEN
  CONJ_TAC THEN DISCH_THEN(MP_TAC o SPEC `0`) THEN REWRITE_TAC[option_DISTINCT]);;

let LCONS_11 = prove
 (`!(h1:A) t1 h2 t2. LCONS h1 t1 = LCONS h2 t2 <=> h1 = h2 /\ t1 = t2`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [ONCE_REWRITE_TAC[GSYM llist_rep_11] THEN
    REWRITE_TAC[llist_rep_LCONS; FUN_EQ_THM] THEN DISCH_TAC THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN REWRITE_TAC[option_INJ];
      X_GEN_TAC `n:num` THEN FIRST_X_ASSUM(MP_TAC o SPEC `SUC n`) THEN
      REWRITE_TAC[NOT_SUC; SUC_SUB1]];
    MESON_TAC[]]);;

let LLIST_DISTINCT = prove
 (`!(a1:A) a2. ~(LNIL = LCONS a1 a2)`,
  REWRITE_TAC[LCONS_NOT_NIL]);;

let LHD_THM = prove
 (`LHD (LNIL:A llist) = NONE /\ (!(h:A) t. LHD (LCONS h t) = SOME h)`,
  REWRITE_TAC[LHD; llist_rep_LNIL; llist_rep_LCONS]);;

let LTL_THM = prove
 (`LTL (LNIL:A llist) = NONE /\ (!(h:A) t. LTL (LCONS h t) = SOME t)`,
  REWRITE_TAC[LTL; LHD_THM; option_CASE] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[option_INJ; llist_rep_LCONS; ADD_EQ_0; ARITH_EQ; ADD_SUB] THEN
  REWRITE_TAC[ETA_AX; llist_absrep]);;

let LHD_LCONS = prove
 (`LHD (LCONS (h:A) t) = SOME h`,
  REWRITE_TAC[LHD_THM]);;

let LTL_LCONS = prove
 (`LTL (LCONS (h:A) t) = SOME t`,
  REWRITE_TAC[LTL_THM]);;

let LHDTL_CONS_THM = prove
 (`!(h:A) t. LHD (LCONS h t) = SOME h /\ LTL (LCONS h t) = SOME t`,
  REWRITE_TAC[LHD_THM; LTL_THM]);;

let LHD_EQ_NONE = prove
 (`!ll:A llist. (LHD ll = NONE <=> ll = LNIL) /\ (NONE = LHD ll <=> ll = LNIL)`,
  GEN_TAC THEN LLIST_CASE_TAC `ll:A llist` THEN
  REWRITE_TAC[LHD_THM; LCONS_NOT_NIL; option_DISTINCT]);;

let LTL_EQ_NONE = prove
 (`!ll:A llist. (LTL ll = NONE <=> ll = LNIL) /\ (NONE = LTL ll <=> ll = LNIL)`,
  GEN_TAC THEN LLIST_CASE_TAC `ll:A llist` THEN
  REWRITE_TAC[LTL_THM; LCONS_NOT_NIL; option_DISTINCT]);;

let LHDTL_EQ_SOME = prove
 (`!(h:A) t ll. ll = LCONS h t <=> LHD ll = SOME h /\ LTL ll = SOME t`,
  REPEAT GEN_TAC THEN LLIST_CASE_TAC `ll:A llist` THEN
  REWRITE_TAC[LHD_THM; LTL_THM; LCONS_NOT_NIL; option_DISTINCT; option_INJ;
              LCONS_11] THEN
  MESON_TAC[]);;

(* LNTH is llist_rep with the arguments swapped *)

let LLISTAUX_LNTH_DEF = new_definition
  `LNTH i (ll:A llist) = llist_rep ll i`;;

let LNTH_rep = prove
 (`!i (ll:A llist). LNTH i ll = llist_rep ll i`,
  REWRITE_TAC[LLISTAUX_LNTH_DEF]);;

let LNTH = prove
 (`(!ll:A llist. LNTH 0 ll = LHD ll) /\
   (!n ll:A llist. LNTH (SUC n) ll = OPTION_JOIN (OPTION_MAP (LNTH n) (LTL ll)))`,
  REWRITE_TAC[LNTH_rep; LHD] THEN REPEAT GEN_TAC THEN
  LLIST_CASE_TAC `ll:A llist` THEN
  REWRITE_TAC[LTL_THM; OPTION_MAP_DEF; OPTION_JOIN_DEF; llist_rep_LNIL;
              llist_rep_LCONS; NOT_SUC; SUC_SUB1; LNTH_rep]);;

let LNTH_THM = prove
 (`(!n. LNTH n (LNIL:A llist) = NONE) /\
   (!(h:A) t. LNTH 0 (LCONS h t) = SOME h) /\
   (!n (h:A) t. LNTH (SUC n) (LCONS h t) = LNTH n t)`,
  REWRITE_TAC[LNTH_rep; llist_rep_LNIL; llist_rep_LCONS; NOT_SUC; SUC_SUB1]);;

let LNTH_EQ = prove
 (`!ll1 ll2:A llist. ll1 = ll2 <=> !n. LNTH n ll1 = LNTH n ll2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LNTH_rep; GSYM llist_rep_11; FUN_EQ_THM]);;

let LNTH_NONE_MONO = prove
 (`!m n (l:A llist). LNTH m l = NONE /\ m <= n ==> LNTH n l = NONE`,
  REWRITE_TAC[LNTH_rep; LLISTAUX_rep_mono]);;

(* ------------------------------------------------------------------------- *)
(* LUNFOLD and bisimulation.                                                 *)
(* ------------------------------------------------------------------------- *)

let LLISTAUX_OPTION_MAP_EQ_NONE = prove
 (`!(f:A->B) x. OPTION_MAP f x = NONE <=> x = NONE`,
  GEN_TAC THEN MATCH_MP_TAC option_INDUCT THEN
  REWRITE_TAC[OPTION_MAP_DEF; option_DISTINCT]);;

let LLISTAUX_ITER_BIND_NONE = prove
 (`!(g:A->A option) n. ITER n (\m. OPTION_BIND m g) NONE = NONE`,
  GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC[ITER; OPTION_BIND_DEF]);;

let LLISTAUX_lrep_ok_ITER_BIND = prove
 (`!(g:A#B->(A#B)option) x.
     lrep_ok (\n. OPTION_MAP SND (ITER n (\m. OPTION_BIND m g) x))`,
  REWRITE_TAC[LLISTAUX_lrep_ok_NONE; LLISTAUX_OPTION_MAP_EQ_NONE] THEN
  SIMP_TAC[ITER; OPTION_BIND_DEF]);;

let LLISTAUX_UNCURRY_K = prove
 (`!(f:A->C) (p:A#B). UNCURRY (combin_K o f) p = f (FST p)`,
  GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM; UNCURRY_DEF; o_THM; K_THM]);;

let LUNFOLD_def = new_definition
  `LUNFOLD (f:A->(A#B)option) z =
     llist_abs (\n. OPTION_MAP SND
                      (ITER n (\m. OPTION_BIND m (UNCURRY (combin_K o f))) (f z)))`;;

let LLISTAUX_LNTH_LUNFOLD = prove
 (`!(f:A->(A#B)option) z n.
     LNTH n (LUNFOLD f z) =
     OPTION_MAP SND (ITER n (\m. OPTION_BIND m (UNCURRY (combin_K o f))) (f z))`,
  SIMP_TAC[LNTH_rep; LUNFOLD_def; LLISTAUX_repabs; LLISTAUX_lrep_ok_ITER_BIND]);;

let LUNFOLD = prove
 (CASE_TERM
  `!(f:A->(A#B)option) x.
     LUNFOLD f x =
     match f x with NONE -> LNIL | SOME (v1,v2) -> LCONS v2 (LUNFOLD f v1)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `(f:A->(A#B)option) x` (cases "option")) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[option_CASE] THENL
   [REWRITE_TAC[LNTH_EQ; LLISTAUX_LNTH_LUNFOLD; LNTH_THM] THEN
    ASM_REWRITE_TAC[LLISTAUX_ITER_BIND_NONE; OPTION_MAP_DEF];
    ALL_TAC] THEN
  SUBST1_TAC(ISPEC `a:A#B` (GSYM PAIR)) THEN REWRITE_TAC[pair_CASE] THEN
  REWRITE_TAC[LNTH_EQ; LLISTAUX_LNTH_LUNFOLD] THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[ITER_ALT; LNTH_THM; LLISTAUX_LNTH_LUNFOLD] THEN
  REWRITE_TAC[OPTION_MAP_DEF; OPTION_BIND_DEF; LLISTAUX_UNCURRY_K] THEN
  REWRITE_TAC[PAIR]);;

let LLISTAUX_BISIM = prove
 (`!R x y:A llist.
     (!a b. R a b ==>
            (a = LNIL /\ b = LNIL) \/
            (?h t1 t2. a = LCONS h t1 /\ b = LCONS h t2 /\ R t1 t2)) /\
     R x y ==> x = y`,
  GEN_TAC THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "bis") MP_TAC) THEN
  SPEC_TAC(`y:A llist`,`y:A llist`) THEN SPEC_TAC(`x:A llist`,`x:A llist`) THEN
  SUBGOAL_THEN `!n x y:A llist. R x y ==> LNTH n x = LNTH n y` ASSUME_TAC THENL
   [INDUCT_TAC THEN REPEAT GEN_TAC THEN
    DISCH_THEN(fun th -> USE_THEN "bis" (MP_TAC o C MATCH_MP th)) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[LNTH_THM] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[LNTH_EQ] THEN ASM_MESON_TAC[]]);;

let LLIST_BISIMULATION0 = prove
 (`!ll1 ll2:A llist.
     ll1 = ll2 <=>
     ?R. R ll1 ll2 /\
         !ll3 ll4. R ll3 ll4 ==>
                   (ll3 = LNIL /\ ll4 = LNIL) \/
                   ?h t1 t2. ll3 = LCONS h t1 /\ ll4 = LCONS h t2 /\ R t1 t2`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN SUBST1_TAC THEN EXISTS_TAC `(=):A llist->A llist->bool` THEN
    REWRITE_TAC[] THEN REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
    MESON_TAC[llist_CASES];
    DISCH_THEN(X_CHOOSE_THEN `R:A llist->A llist->bool` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC LLISTAUX_BISIM THEN EXISTS_TAC `R:A llist->A llist->bool` THEN
    ASM_REWRITE_TAC[]]);;

let LLIST_BISIMULATION = prove
 (`!ll1 ll2:A llist.
     ll1 = ll2 <=>
     ?R. R ll1 ll2 /\
         !ll3 ll4. R ll3 ll4 ==>
                   (ll3 = LNIL /\ ll4 = LNIL) \/
                   (LHD ll3 = LHD ll4 /\ R (THE (LTL ll3)) (THE (LTL ll4)))`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN SUBST1_TAC THEN EXISTS_TAC `(=):A llist->A llist->bool` THEN
    REWRITE_TAC[] THEN MESON_TAC[llist_CASES];
    DISCH_THEN(X_CHOOSE_THEN `R:A llist->A llist->bool` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC LLISTAUX_BISIM THEN EXISTS_TAC `R:A llist->A llist->bool` THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`x:A llist`; `y:A llist`] THEN
    DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th)) THEN
    LLIST_CASE_TAC `x:A llist` THEN LLIST_CASE_TAC `y:A llist` THEN
    REWRITE_TAC[LHD_THM; LTL_THM; THE_DEF; LCONS_NOT_NIL; option_DISTINCT;
                option_INJ; LCONS_11] THEN
    MESON_TAC[]]);;

let LLIST_STRONG_BISIMULATION = prove
 (`!ll1 ll2:A llist.
     ll1 = ll2 <=>
     ?R. R ll1 ll2 /\
         !ll3 ll4. R ll3 ll4 ==>
                   ll3 = ll4 \/
                   ?h t1 t2. ll3 = LCONS h t1 /\ ll4 = LCONS h t2 /\ R t1 t2`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN SUBST1_TAC THEN EXISTS_TAC `(=):A llist->A llist->bool` THEN
    REWRITE_TAC[] THEN MESON_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `R:A llist->A llist->bool` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC LLISTAUX_BISIM THEN
    EXISTS_TAC `\x y:A llist. R x y \/ x = y` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `!a:A llist. (a = LNIL /\ a = LNIL) \/
                  (?h t1 t2. a = LCONS h t1 /\ a = LCONS h t2 /\
                             (R t1 t2 \/ t1 = t2))`
     ASSUME_TAC THENL
     [GEN_TAC THEN LLIST_CASE_TAC `a:A llist` THEN
      REWRITE_TAC[LCONS_NOT_NIL; LCONS_11] THEN MESON_TAC[];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`a:A llist`; `b:A llist`] THEN STRIP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`a:A llist`; `b:A llist`]) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
       [ASM_MESON_TAC[]; ASM_MESON_TAC[]];
      ASM_MESON_TAC[]]]);;

let LLIST_BISIMULATION_I = prove
 (`!ll2 ll1:A llist.
     (?R. R ll1 ll2 /\
          !ll3 ll4. R ll3 ll4 ==>
                    (ll3 = LNIL /\ ll4 = LNIL) \/
                    (LHD ll3 = LHD ll4 /\ R (THE (LTL ll3)) (THE (LTL ll4))))
     ==> ll1 = ll2`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN ONCE_REWRITE_TAC[LLIST_BISIMULATION] THEN
  ASM_REWRITE_TAC[]);;

let LLISTAUX_OPT_PAIR_CASES = prove
 (`!x:(A#B)option. x = NONE \/ ?a b. x = SOME (a,b)`,
  MESON_TAC[cases "option"; PAIR_SURJECTIVE]);;

let LLISTAUX_OPT_PAIR_CASES_TAC tm =
  STRUCT_CASES_TAC (ISPEC tm LLISTAUX_OPT_PAIR_CASES);;

let LUNFOLD_UNIQUE = prove
 (CASE_TERM
  `!(f:A->(A#B)option) g.
     (!x. g x = match f x with NONE -> LNIL | SOME (v1,v2) -> LCONS v2 (g v1))
     ==> !y. g y = LUNFOLD f y`,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "g") THEN
  REWRITE_TAC[LNTH_EQ] THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  INDUCT_TAC THEN X_GEN_TAC `y:A` THEN
  REMOVE_THEN "g" (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [LUNFOLD] THEN
  LLISTAUX_OPT_PAIR_CASES_TAC `(f:A->(A#B)option) y` THEN
  ASM_REWRITE_TAC[option_CASE; pair_CASE; LNTH_THM]);;

let LNTH_LUNFOLD = prove
 (CASE_TERM
  `(LNTH 0 (LUNFOLD (f:A->(A#B)option) x) = OPTION_MAP SND (f x)) /\
   (LNTH (SUC n) (LUNFOLD f x) =
      match f x with NONE -> NONE | SOME (tx,hx) -> LNTH n (LUNFOLD f tx))`,
  CONJ_TAC THEN GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [LUNFOLD] THEN
  LLISTAUX_OPT_PAIR_CASES_TAC `(f:A->(A#B)option) x` THEN
  REWRITE_TAC[option_CASE; pair_CASE; LNTH_THM; OPTION_MAP_DEF]);;

let LHD_LUNFOLD = prove
 (`LHD (LUNFOLD (f:A->(A#B)option) x) = OPTION_MAP SND (f x)`,
  REWRITE_TAC[GSYM(CONJUNCT1 LNTH); LNTH_LUNFOLD]);;

let LTL_LUNFOLD = prove
 (`LTL (LUNFOLD (f:A->(A#B)option) x) = OPTION_MAP (LUNFOLD f o FST) (f x)`,
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [LUNFOLD] THEN
  LLISTAUX_OPT_PAIR_CASES_TAC `(f:A->(A#B)option) x` THEN
  REWRITE_TAC[option_CASE; pair_CASE; LTL_THM; OPTION_MAP_DEF; o_THM]);;

let LUNFOLD_THM = prove
 (`!(f:A->(A#B)option) x v1 v2.
     (f x = NONE ==> LUNFOLD f x = LNIL) /\
     (f x = SOME (v1,v2) ==> LUNFOLD f x = LCONS v2 (LUNFOLD f v1))`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [LUNFOLD] THEN
  ASM_REWRITE_TAC[option_CASE; pair_CASE]);;

let llist_Axiom_1 = prove
 (CASE_TERM
  `!f:A->(A#B)option.
     ?g:A->B llist.
       !x. g x = match f x with NONE -> LNIL | SOME (a,b) -> LCONS b (g a)`,
  GEN_TAC THEN EXISTS_TAC `LUNFOLD (f:A->(A#B)option)` THEN
  MATCH_ACCEPT_TAC LUNFOLD);;

let llist_Axiom_1ue = prove
 (CASE_TERM
  `!f:A->(A#B)option.
     ?!g:A->B llist.
       !x. g x = match f x with NONE -> LNIL | SOME (a,b) -> LCONS b (g a)`,
  GEN_TAC THEN REWRITE_TAC[EXISTS_UNIQUE_THM] THEN CONJ_TAC THENL
   [EXISTS_TAC `LUNFOLD (f:A->(A#B)option)` THEN MATCH_ACCEPT_TAC LUNFOLD;
    REPEAT STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
    ASM_MESON_TAC[LUNFOLD_UNIQUE]]);;

let LLISTAUX_ue_lemma = prove
 (CASE_TERM
  `!(f:A->(A#B)option) (g:A->B llist).
     ((!x. LHD (g x) = OPTION_MAP SND (f x)) /\
      (!x. LTL (g x) = OPTION_MAP (g o FST) (f x))) <=>
     (!x. g x = match f x with NONE -> LNIL | SOME (a,b) -> LCONS b (g a))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM FORALL_AND_THM] THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:A` THEN
  LLISTAUX_OPT_PAIR_CASES_TAC `(f:A->(A#B)option) x` THEN
  REWRITE_TAC[option_CASE; pair_CASE; OPTION_MAP_DEF; o_THM] THEN
  REWRITE_TAC[LHD_EQ_NONE; LTL_EQ_NONE; GSYM LHDTL_EQ_SOME]);;

let llist_ue_Axiom = prove
 (`!f:A->(A#B)option.
     ?!g:A->B llist.
       (!x. LHD (g x) = OPTION_MAP SND (f x)) /\
       (!x. LTL (g x) = OPTION_MAP (g o FST) (f x))`,
  REWRITE_TAC[LLISTAUX_ue_lemma; llist_Axiom_1ue]);;

let llist_Axiom = prove
 (`!f:A->(A#B)option.
     ?g:A->B llist.
       (!x. LHD (g x) = OPTION_MAP SND (f x)) /\
       (!x. LTL (g x) = OPTION_MAP (g o FST) (f x))`,
  MESON_TAC[llist_ue_Axiom; EXISTS_UNIQUE_THM]);;

let LUNFOLD_BISIMULATION = prove
 (`!(f1:A->(A#C)option) (f2:B->(B#C)option) x1 x2.
     LUNFOLD f1 x1 = LUNFOLD f2 x2 <=>
     ?R. R x1 x2 /\
         !y1 y2. R y1 y2 ==>
                 (f1 y1 = NONE /\ f2 y2 = NONE) \/
                 ?h t1 t2. f1 y1 = SOME (t1,h) /\ f2 y2 = SOME (t2,h) /\
                           R t1 t2`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN
    EXISTS_TAC `\y1 y2. LUNFOLD (f1:A->(A#C)option) y1 = LUNFOLD
                        (f2:B->(B#C)option) y2` THEN
    ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`y1:A`; `y2:B`] THEN
    DISCH_THEN(MP_TAC o ONCE_REWRITE_RULE[LUNFOLD]) THEN
    LLISTAUX_OPT_PAIR_CASES_TAC `(f1:A->(A#C)option) y1` THEN
    LLISTAUX_OPT_PAIR_CASES_TAC `(f2:B->(B#C)option) y2` THEN
    REWRITE_TAC[option_CASE; pair_CASE; LCONS_NOT_NIL; LCONS_11;
                option_DISTINCT; option_INJ; PAIR_EQ] THEN
    MESON_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `R:A->B->bool` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC LLISTAUX_BISIM THEN
    EXISTS_TAC `\l1 l2. ?y1 y2. R y1 y2 /\
                         l1 = LUNFOLD (f1:A->(A#C)option) y1 /\
                         l2 = LUNFOLD (f2:B->(B#C)option) y2` THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    MAP_EVERY X_GEN_TAC [`l1:C llist`; `l2:C llist`] THEN
    DISCH_THEN(X_CHOOSE_THEN `y1:A` (X_CHOOSE_THEN `y2:B`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN SUBST1_TAC)))) THEN
    SUBST1_TAC(ISPECL [`f1:A->(A#C)option`; `y1:A`] LUNFOLD) THEN
    SUBST1_TAC(ISPECL [`f2:B->(B#C)option`; `y2:B`] LUNFOLD) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`y1:A`; `y2:B`]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[option_CASE; pair_CASE; LCONS_NOT_NIL; LCONS_11] THEN
    ASM_MESON_TAC[]]);;

let LLIST_EQ = prove
 (`!f g:A->B llist.
     (!x. (f x = LNIL /\ g x = LNIL) \/
          (?h y. f x = LCONS h (f y) /\ g x = LCONS h (g y)))
     ==> !x. f x = g x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LLISTAUX_BISIM THEN
  EXISTS_TAC `\l1 l2. ?x:A. l1 = (f:A->B llist) x /\ l2 = (g:A->B llist) x` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  MAP_EVERY X_GEN_TAC [`l1:B llist`; `l2:B llist`] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:A` (CONJUNCTS_THEN SUBST1_TAC)) THEN
  ASM_MESON_TAC[]);;

let LUNFOLD_EQ = prove
 (`!(R:A->B llist->bool) f s ll.
     R s ll /\
     (!s ll. R s ll ==>
             (f s = NONE /\ ll = LNIL) \/
             ?s' x ll'. f s = SOME (s',x) /\ LHD ll = SOME x /\
                        LTL ll = SOME ll' /\ R s' ll')
     ==> LUNFOLD f s = ll`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LLISTAUX_BISIM THEN
  EXISTS_TAC `\l1 l2. ?s:A. l1 = LUNFOLD (f:A->(A#B)option) s /\
                            (R:A->B llist->bool) s l2` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  MAP_EVERY X_GEN_TAC [`l1:B llist`; `l2:B llist`] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:A` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`z:A`; `l2:B llist`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBST1_TAC(ISPECL [`f:A->(A#B)option`; `z:A`] LUNFOLD) THEN
    ASM_REWRITE_TAC[option_CASE];
    SUBGOAL_THEN `l2 = LCONS (x:B) ll'` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[LHDTL_EQ_SOME]; ALL_TAC] THEN
    SUBST1_TAC(ISPECL [`f:A->(A#B)option`; `z:A`] LUNFOLD) THEN
    ASM_REWRITE_TAC[option_CASE; pair_CASE; LCONS_11; LCONS_NOT_NIL] THEN
    ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* LTAKE: the prefix of a given length, if the list is at least that long.  *)
(* ------------------------------------------------------------------------- *)

let LLISTAUX_OPTION_MAP_EQ_SOME = prove
 (`!(f:A->B) x y. OPTION_MAP f x = SOME y <=> ?z. x = SOME z /\ y = f z`,
  GEN_TAC THEN MATCH_MP_TAC option_INDUCT THEN
  REWRITE_TAC[OPTION_MAP_DEF; option_DISTINCT; option_INJ] THEN MESON_TAC[]);;

let LLISTAUX_option_CASE_NONE_SOME = prove
 (`!(x:A option) (f:A->B). option_CASE x NONE (\y. SOME (f y)) = OPTION_MAP f x`,
  MATCH_MP_TAC option_INDUCT THEN REWRITE_TAC[option_CASE; OPTION_MAP_DEF]);;

let LTAKE =
  let th = new_recursive_definition num_RECURSION (CASE_TERM
  `(LTAKE 0 (ll:A llist) = SOME []) /\
   (LTAKE (SUC n) ll =
      match LHD ll with
        NONE -> NONE
      | SOME hd -> (match LTAKE n (THE (LTL ll)) with
                      NONE -> NONE
                    | SOME tl -> SOME (CONS hd tl)))`) in
  CONJ (GEN_ALL (CONJUNCT1 th)) (GEN_ALL (CONJUNCT2 th));;

let LTAKE_THM = prove
 (`(!l:A llist. LTAKE 0 l = SOME []) /\
   (!n. LTAKE (SUC n) (LNIL:A llist) = NONE) /\
   (!n (h:A) t. LTAKE (SUC n) (LCONS h t) = OPTION_MAP (CONS h) (LTAKE n t))`,
  REWRITE_TAC[LTAKE; LHD_THM; LTL_THM; THE_DEF; option_CASE;
              LLISTAUX_option_CASE_NONE_SOME; ETA_AX]);;

let LTAKE_LUNFOLD = prove
 (CASE_TERM
  `(LTAKE 0 (LUNFOLD (f:A->(A#B)option) x) = SOME []) /\
   (LTAKE (SUC n) (LUNFOLD f x) =
      match f x with
        NONE -> NONE
      | SOME (tx,hx) -> OPTION_MAP (CONS hx) (LTAKE n (LUNFOLD f tx)))`,
  REWRITE_TAC[LTAKE_THM] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [LUNFOLD] THEN
  LLISTAUX_OPT_PAIR_CASES_TAC `(f:A->(A#B)option) x` THEN
  REWRITE_TAC[option_CASE; pair_CASE; LTAKE_THM]);;

let LLISTAUX_LTAKE_SUC_NONE = prove
 (`!n (ll:A llist). LTAKE (SUC n) ll = NONE <=> LNTH n ll = NONE`,
  INDUCT_TAC THEN GEN_TAC THEN LLIST_CASE_TAC `ll:A llist` THEN
  ASM_REWRITE_TAC[LTAKE_THM; LNTH_THM; LLISTAUX_OPTION_MAP_EQ_NONE;
                  option_DISTINCT]);;

let LTAKE_EQ_NONE_LNTH = prove
 (`!n (ll:A llist). LTAKE n ll = NONE ==> LNTH n ll = NONE`,
  INDUCT_TAC THEN REWRITE_TAC[LTAKE_THM; option_DISTINCT] THEN
  REWRITE_TAC[LLISTAUX_LTAKE_SUC_NONE] THEN
  MESON_TAC[LNTH_NONE_MONO; ARITH_RULE `n <= SUC n`]);;

let LLISTAUX_LTAKE_NONE = prove
 (`!n (ll:A llist). LTAKE n ll = NONE <=> ?m. m < n /\ LNTH m ll = NONE`,
  INDUCT_TAC THEN REWRITE_TAC[LTAKE_THM; option_DISTINCT; LT] THEN
  REWRITE_TAC[LLISTAUX_LTAKE_SUC_NONE] THEN
  MESON_TAC[LNTH_NONE_MONO; ARITH_RULE `m < SUC n ==> m <= n`; LT]);;

let LTAKE_NIL_EQ_SOME = prove
 (`!l m. LTAKE m (LNIL:A llist) = SOME l <=> m = 0 /\ l = []`,
  GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[LTAKE_THM; option_DISTINCT; option_INJ; NOT_SUC] THEN
  MESON_TAC[]);;

let LTAKE_NIL_EQ_NONE = prove
 (`!m. LTAKE m (LNIL:A llist) = NONE <=> 0 < m`,
  INDUCT_TAC THEN REWRITE_TAC[LTAKE_THM; option_DISTINCT; LT_REFL; LT_0]);;

let LTAKE_LNTH_EL = prove
 (`!n (ll:A llist) m l. LTAKE n ll = SOME l /\ m < n ==> LNTH m ll = SOME (EL m l)`,
  INDUCT_TAC THENL [REWRITE_TAC[LT]; POP_ASSUM(LABEL_TAC "ih")] THEN
  GEN_TAC THEN LLIST_CASE_TAC `ll:A llist` THEN
  REWRITE_TAC[LTAKE_THM; option_DISTINCT; LLISTAUX_OPTION_MAP_EQ_SOME] THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `l:A list`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `z:A list` STRIP_ASSUME_TAC)
    MP_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  STRUCT_CASES_TAC(SPEC `m:num` num_CASES) THEN
  REWRITE_TAC[LNTH_THM; EL; HD; TL; LT_SUC] THEN
  DISCH_TAC THEN REMOVE_THEN "ih" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let LTAKE_LENGTH = prove
 (`!n (ll:A llist) l. LTAKE n ll = SOME l ==> n = LENGTH l`,
  INDUCT_TAC THENL
   [REWRITE_TAC[LTAKE_THM; option_INJ] THEN MESON_TAC[LENGTH];
    POP_ASSUM(LABEL_TAC "ih")] THEN
  GEN_TAC THEN LLIST_CASE_TAC `ll:A llist` THEN
  REWRITE_TAC[LTAKE_THM; option_DISTINCT; LLISTAUX_OPTION_MAP_EQ_SOME] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[LENGTH; SUC_INJ] THEN
  REMOVE_THEN "ih" MATCH_MP_TAC THEN EXISTS_TAC `t:A llist` THEN
  ASM_REWRITE_TAC[]);;

let LLISTAUX_LTAKE_SOME_EQ = prove
 (`!n (ll:A llist) l.
     LTAKE n ll = SOME l <=>
     LENGTH l = n /\ !m. m < n ==> LNTH m ll = SOME (EL m l)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [MESON_TAC[LTAKE_LENGTH; LTAKE_LNTH_EL]; STRIP_TAC] THEN
  MP_TAC(ISPEC `LTAKE n (ll:A llist)` (cases "option")) THEN STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[LLISTAUX_LTAKE_NONE]) THEN
    ASM_MESON_TAC[option_DISTINCT];
    ASM_REWRITE_TAC[option_INJ] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP LTAKE_LENGTH) THEN DISCH_TAC THEN
    REWRITE_TAC[LIST_EQ] THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[LTAKE_LNTH_EL; option_INJ]]);;

let LTAKE_SNOC_LNTH = prove
 (CASE_TERM
  `!n (ll:A llist).
     LTAKE (SUC n) ll =
       match LTAKE n ll with
         NONE -> NONE
       | SOME l -> (match LNTH n ll with
                      NONE -> NONE
                    | SOME e -> SOME (APPEND l [e]))`,
  INDUCT_TAC THEN GEN_TAC THEN LLIST_CASE_TAC `ll:A llist` THEN
  REWRITE_TAC[LTAKE_THM; LNTH_THM; option_CASE; OPTION_MAP_DEF; APPEND] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `LTAKE n (t:A llist)` (cases "option")) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[option_CASE; OPTION_MAP_DEF] THEN
  MP_TAC(ISPEC `LNTH n (t:A llist)` (cases "option")) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[option_CASE; OPTION_MAP_DEF; APPEND]);;

let LTAKE_EQ = prove
 (`!ll1 ll2:A llist. ll1 = ll2 <=> !n. LTAKE n ll1 = LTAKE n ll2`,
  REPEAT GEN_TAC THEN EQ_TAC THENL [MESON_TAC[]; DISCH_TAC] THEN
  REWRITE_TAC[LNTH_EQ] THEN X_GEN_TAC `n:num` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `SUC n`) THEN
  MP_TAC(ISPEC `LTAKE (SUC n) (ll1:A llist)` (cases "option")) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [ASM_MESON_TAC[LLISTAUX_LTAKE_SUC_NONE];
    ASM_MESON_TAC[LTAKE_LNTH_EL; ARITH_RULE `n < SUC n`]]);;

let LTAKE_CONS_EQ_NONE = prove
 (`!m (h:A) t. LTAKE m (LCONS h t) = NONE <=> ?n. m = SUC n /\ LTAKE n t = NONE`,
  INDUCT_TAC THEN
  REWRITE_TAC[LTAKE_THM; option_DISTINCT; NOT_SUC; SUC_INJ;
              LLISTAUX_OPTION_MAP_EQ_NONE] THEN
  MESON_TAC[]);;

let LTAKE_CONS_EQ_SOME = prove
 (`!m (h:A) t l.
     LTAKE m (LCONS h t) = SOME l <=>
     (m = 0 /\ l = []) \/
     ?n l'. m = SUC n /\ LTAKE n t = SOME l' /\ l = CONS h l'`,
  INDUCT_TAC THEN
  REWRITE_TAC[LTAKE_THM; option_INJ; NOT_SUC; SUC_INJ;
              LLISTAUX_OPTION_MAP_EQ_SOME] THEN
  MESON_TAC[]);;

let LTAKE_EQ_SOME_CONS = prove
 (`!n (l:A llist) x. LTAKE n l = SOME x ==> !h. ?y. LTAKE n (LCONS h l) = SOME y`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(MESON[cases "option"]
    `~((x:(A list)option) = NONE) ==> ?y. x = SOME y`) THEN
  REWRITE_TAC[LTAKE_CONS_EQ_NONE; LLISTAUX_LTAKE_NONE; NOT_EXISTS_THM] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `LTAKE n (l:A llist) = NONE`
    (fun th -> ASM_MESON_TAC[th; option_DISTINCT]) THEN
  REWRITE_TAC[LLISTAUX_LTAKE_NONE] THEN EXISTS_TAC `m:num` THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* TAKE facts (list theory; local) *)

let LLISTAUX_LENGTH_TAKE = prove
 (`!n (l:A list). n <= LENGTH l ==> LENGTH (TAKE n l) = n`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[TAKE_DEF; LENGTH] THENL [ARITH_TAC; ALL_TAC] THEN
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[LENGTH] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n - 1`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN ASM_ARITH_TAC);;

let LLISTAUX_EL_TAKE = prove
 (`!n m (l:A list). m < n ==> EL m (TAKE n l) = EL m l`,
  REPEAT GEN_TAC THEN SPEC_TAC(`n:num`,`n:num`) THEN
  SPEC_TAC(`m:num`,`m:num`) THEN SPEC_TAC(`l:A list`,`l:A list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[TAKE_DEF] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THENL [ASM_REWRITE_TAC[LT]; ALL_TAC] THEN
  STRUCT_CASES_TAC(SPEC `m:num` num_CASES) THEN REWRITE_TAC[EL; HD; TL] THEN
  DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let LTAKE_TAKE_LESS = prove
 (`LTAKE n (ll:A llist) = SOME l /\ m <= n ==> LTAKE m ll = SOME (TAKE m l)`,
  REWRITE_TAC[LLISTAUX_LTAKE_SOME_EQ] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[LLISTAUX_LENGTH_TAKE; LE_REFL] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[LLISTAUX_EL_TAKE] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* LMAP (specified by its equations, as in HOL4).                            *)
(* ------------------------------------------------------------------------- *)

let lrep_ok_MAP = prove
 (`!(f:A->B) g. lrep_ok (\n. OPTION_MAP f (g n)) <=> lrep_ok g`,
  REWRITE_TAC[LLISTAUX_lrep_ok_NONE; LLISTAUX_OPTION_MAP_EQ_NONE]);;

let LMAP = new_specification ["LMAP"]
 (prove
   (`?LMAP. (!f:A->B. LMAP f LNIL = LNIL) /\
            (!(f:A->B) h t. LMAP f (LCONS h t) = LCONS (f h) (LMAP f t))`,
    EXISTS_TAC `\(f:A->B) (ll:A llist). llist_abs (\n. OPTION_MAP f (llist_rep ll n))` THEN
    REWRITE_TAC[] THEN CONJ_TAC THEN REPEAT GEN_TAC THENL
     [REWRITE_TAC[llist_rep_LNIL; OPTION_MAP_DEF; LNIL];
      REWRITE_TAC[llist_rep_LCONS] THEN REWRITE_TAC[LCONS] THEN
      AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `n:num` THEN
      SIMP_TAC[LLISTAUX_repabs; lrep_ok_MAP; lrep_ok_llist_rep; ETA_AX] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[OPTION_MAP_DEF]]));;

let LNTH_LMAP = prove
 (`!n (f:A->B) l. LNTH n (LMAP f l) = OPTION_MAP f (LNTH n l)`,
  INDUCT_TAC THEN REPEAT GEN_TAC THEN LLIST_CASE_TAC `l:A llist` THEN
  ASM_REWRITE_TAC[LMAP; LNTH_THM; OPTION_MAP_DEF]);;

let LMAP_EQ_NIL = prove
 (`(LMAP (f:A->B) l = LNIL <=> l = LNIL) /\ (LNIL = LMAP f l <=> l = LNIL)`,
  LLIST_CASE_TAC `l:A llist` THEN REWRITE_TAC[LMAP; LCONS_NOT_NIL]);;

let LMAP_EQ_CONS = prove
 (`LMAP (f:A->B) l = LCONS h t <=> ?h0 t0. l = LCONS h0 t0 /\ h = f h0 /\ t = LMAP f t0`,
  LLIST_CASE_TAC `l:A llist` THEN REWRITE_TAC[LMAP; LCONS_NOT_NIL; LCONS_11] THEN
  MESON_TAC[]);;

let LMAP_MAP = prove
 (`!(f:A->B) (g:C->A) (ll:C llist). LMAP f (LMAP g ll) = LMAP (f o g) ll`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LNTH_EQ; LNTH_LMAP] THEN GEN_TAC THEN
  MP_TAC(ISPEC `LNTH n (ll:C llist)` (cases "option")) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[OPTION_MAP_DEF; o_THM]);;

(* ------------------------------------------------------------------------- *)
(* LAPPEND (specified by its equations; the witness is an LUNFOLD).          *)
(* ------------------------------------------------------------------------- *)

let LAPPEND = new_specification ["LAPPEND"]
 (prove
   (`?LAPPEND. (!x:A llist. LAPPEND LNIL x = x) /\
               (!(h:A) t x. LAPPEND (LCONS h t) x = LCONS h (LAPPEND t x))`,
    EXISTS_TAC
     `\l1 l2:A llist.
        LUNFOLD (\p:A llist#A llist.
                   if FST p = LNIL then
                     (if SND p = LNIL then NONE
                      else SOME ((FST p, THE (LTL (SND p))), THE (LHD (SND p))))
                   else SOME ((THE (LTL (FST p)), SND p), THE (LHD (FST p))))
                (l1,l2)` THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC LUNFOLD_EQ THEN
      EXISTS_TAC `\s:A llist#A llist ll:A llist. s = (LNIL,ll)` THEN
      REWRITE_TAC[] THEN REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
      LLIST_CASE_TAC `ll:A llist` THEN
      REWRITE_TAC[LCONS_NOT_NIL; LHD_THM; LTL_THM; THE_DEF; option_INJ;
                  PAIR_EQ] THEN
      MESON_TAC[];
      REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [LUNFOLD] THEN
      REWRITE_TAC[FST; SND; LCONS_NOT_NIL; LHD_THM; LTL_THM; THE_DEF;
                  option_CASE; pair_CASE]]));;

let LAPPEND_EQ_LNIL = prove
 (`LAPPEND l1 l2 = (LNIL:A llist) <=> l1 = LNIL /\ l2 = LNIL`,
  LLIST_CASE_TAC `l1:A llist` THEN REWRITE_TAC[LAPPEND; LCONS_NOT_NIL]);;

let LAPPEND_ASSOC = prove
 (`!ll1 ll2 ll3:A llist.
     LAPPEND (LAPPEND ll1 ll2) ll3 = LAPPEND ll1 (LAPPEND ll2 ll3)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[LLIST_STRONG_BISIMULATION] THEN
  EXISTS_TAC `\l1 l2:A llist. ?u. l1 = LAPPEND (LAPPEND u ll2) ll3 /\
                                 l2 = LAPPEND u (LAPPEND ll2 ll3)` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `u:A llist` (CONJUNCTS_THEN SUBST1_TAC)) THEN
  LLIST_CASE_TAC `u:A llist` THEN REWRITE_TAC[LAPPEND; LCONS_11] THEN
  MESON_TAC[]);;

let LHD_LAPPEND = prove
 (`LHD (LAPPEND l1 l2) = if l1 = LNIL then LHD l2 else LHD (l1:A llist)`,
  LLIST_CASE_TAC `l1:A llist` THEN REWRITE_TAC[LAPPEND; LCONS_NOT_NIL; LHD_THM]);;

let LTL_LAPPEND = prove
 (`LTL (LAPPEND l1 l2) =
   if l1 = LNIL then LTL l2 else SOME (LAPPEND (THE (LTL l1)) (l2:A llist))`,
  LLIST_CASE_TAC `l1:A llist` THEN
  REWRITE_TAC[LAPPEND; LCONS_NOT_NIL; LTL_THM; THE_DEF]);;

let LTAKE_LAPPEND1 = prove
 (`!n (l1:A llist) l2. IS_SOME (LTAKE n l1) ==> LTAKE n (LAPPEND l1 l2) = LTAKE n l1`,
  INDUCT_TAC THEN REWRITE_TAC[LTAKE_THM] THEN GEN_TAC THEN
  LLIST_CASE_TAC `l1:A llist` THEN
  REWRITE_TAC[LTAKE_THM; LAPPEND; IS_SOME_DEF] THEN
  REWRITE_TAC[LLISTAUX_IS_SOME_NONE; LLISTAUX_OPTION_MAP_EQ_NONE] THEN
  ASM_SIMP_TAC[GSYM LLISTAUX_IS_SOME_NONE]);;

let LTAKE_LMAP = prove
 (`!n (f:A->B) ll. LTAKE n (LMAP f ll) = OPTION_MAP (MAP f) (LTAKE n ll)`,
  INDUCT_TAC THEN REPEAT GEN_TAC THEN LLIST_CASE_TAC `ll:A llist` THEN
  ASM_REWRITE_TAC[LTAKE_THM; LMAP; OPTION_MAP_DEF; MAP] THEN
  MP_TAC(ISPEC `LTAKE n (t:A llist)` (cases "option")) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[OPTION_MAP_DEF; MAP]);;

(* ------------------------------------------------------------------------- *)
(* Finiteness and length.                                                    *)
(* ------------------------------------------------------------------------- *)

let LFINITE_rules,LFINITE_ind,LFINITE_cases = new_inductive_definition
  `LFINITE (LNIL:A llist) /\ (!(h:A) t. LFINITE t ==> LFINITE (LCONS h t))`;;

let LFINITE_strongind = derive_strong_induction(LFINITE_rules,LFINITE_ind);;

let LFINITE_INDUCTION = LFINITE_ind;;

let LFINITE_STRONG_INDUCTION = LFINITE_strongind;;

let LFINITE_THM = prove
 (`(LFINITE (LNIL:A llist) <=> T) /\ (!(h:A) t. LFINITE (LCONS h t) <=> LFINITE t)`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [LFINITE_cases] THEN
  REWRITE_TAC[LCONS_NOT_NIL; LCONS_11] THEN MESON_TAC[]);;

let LFINITE_LNTH_NONE = prove
 (`LFINITE (ll:A llist) <=> ?n. LNTH n ll = NONE`,
  EQ_TAC THENL
   [SPEC_TAC(`ll:A llist`,`ll:A llist`) THEN MATCH_MP_TAC LFINITE_ind THEN
    REWRITE_TAC[LNTH_THM] THEN MESON_TAC[LNTH_THM];
    ALL_TAC] THEN
  SPEC_TAC(`ll:A llist`,`ll:A llist`) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  INDUCT_TAC THEN GEN_TAC THEN LLIST_CASE_TAC `ll:A llist` THEN
  REWRITE_TAC[LNTH_THM; option_DISTINCT; LFINITE_THM] THEN
  ASM_REWRITE_TAC[]);;

let LFINITE = prove
 (`LFINITE (ll:A llist) <=> ?n. LTAKE n ll = NONE`,
  REWRITE_TAC[LFINITE_LNTH_NONE; LLISTAUX_LTAKE_NONE] THEN
  MESON_TAC[ARITH_RULE `n < SUC n`]);;

let infinite_lnth_some = prove
 (`!ll:A llist. ~LFINITE ll <=> !n. ?x. LNTH n ll = SOME x`,
  REWRITE_TAC[LFINITE_LNTH_NONE; NOT_EXISTS_THM] THEN
  MESON_TAC[cases "option"; option_DISTINCT]);;

let llength_rel_rules,llength_rel_ind,llength_rel_cases = new_inductive_definition
  `llength_rel (LNIL:A llist) 0 /\
   (!(h:A) n t. llength_rel t n ==> llength_rel (LCONS h t) (SUC n))`;;

let llength_lfinite = prove
 (`!t:A llist n. llength_rel t n ==> LFINITE t`,
  MATCH_MP_TAC llength_rel_ind THEN SIMP_TAC[LFINITE_THM]);;

let lfinite_llength = prove
 (`!t:A llist. LFINITE t ==> ?n. llength_rel t n`,
  MATCH_MP_TAC LFINITE_ind THEN MESON_TAC[llength_rel_rules]);;

let llength_unique = prove
 (`!t:A llist m n. llength_rel t n /\ llength_rel t m ==> m = n`,
  SUBGOAL_THEN `!t:A llist n. llength_rel t n ==> !m. llength_rel t m ==> m = n`
    (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC llength_rel_ind THEN CONJ_TAC THEN REPEAT GEN_TAC THENL
   [ONCE_REWRITE_TAC[llength_rel_cases] THEN REWRITE_TAC[LCONS_NOT_NIL];
    DISCH_TAC THEN GEN_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [llength_rel_cases] THEN
    REWRITE_TAC[LCONS_NOT_NIL; LCONS_11] THEN STRIP_TAC THEN
    ASM_MESON_TAC[]]);;

let llength_rel_nil = prove
 (`llength_rel (LNIL:A llist) n <=> n = 0`,
  ONCE_REWRITE_TAC[llength_rel_cases] THEN REWRITE_TAC[LCONS_NOT_NIL]);;

let LLENGTH = new_definition
  `LLENGTH (ll:A llist) =
     if LFINITE ll then SOME (@n. llength_rel ll n) else NONE`;;

let LLISTAUX_llength_select = prove
 (`!t:A llist n. llength_rel t n ==> (@n. llength_rel t n) = n`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  ASM_MESON_TAC[llength_unique]);;

let LLENGTH_THM = prove
 (`(LLENGTH (LNIL:A llist) = SOME 0) /\
   (!(h:A) t. LLENGTH (LCONS h t) = OPTION_MAP SUC (LLENGTH t))`,
  REWRITE_TAC[LLENGTH; LFINITE_THM] THEN CONJ_TAC THENL
   [AP_TERM_TAC THEN MATCH_MP_TAC LLISTAUX_llength_select THEN
    REWRITE_TAC[llength_rel_rules];
    REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[OPTION_MAP_DEF] THEN
    FIRST_ASSUM(X_CHOOSE_TAC `k:num` o MATCH_MP lfinite_llength) THEN
    SUBGOAL_THEN `(@n. llength_rel (t:A llist) n) = k /\
                  (@n. llength_rel (LCONS (h:A) t) n) = SUC k`
      (fun th -> REWRITE_TAC[th]) THEN
    CONJ_TAC THEN MATCH_MP_TAC LLISTAUX_llength_select THEN
    ASM_SIMP_TAC[llength_rel_rules]]);;

let LLENGTH_0 = prove
 (`LLENGTH (x:A llist) = SOME 0 <=> x = LNIL`,
  LLIST_CASE_TAC `x:A llist` THEN
  REWRITE_TAC[LLENGTH_THM; LCONS_NOT_NIL; LLISTAUX_OPTION_MAP_EQ_SOME] THEN
  REWRITE_TAC[NOT_SUC]);;

let LFINITE_HAS_LENGTH = prove
 (`!ll:A llist. LFINITE ll ==> ?n. LLENGTH ll = SOME n`,
  SIMP_TAC[LLENGTH; option_INJ] THEN MESON_TAC[]);;

let NOT_LFINITE_NO_LENGTH = prove
 (`!ll:A llist. ~LFINITE ll ==> LLENGTH ll = NONE`,
  SIMP_TAC[LLENGTH]);;

let LFINITE_LLENGTH = prove
 (`LFINITE (ll:A llist) <=> ?n. LLENGTH ll = SOME n`,
  MESON_TAC[LFINITE_HAS_LENGTH; NOT_LFINITE_NO_LENGTH; option_DISTINCT]);;

(* the length in terms of LNTH (local) *)

let LLISTAUX_LLENGTH_SOME_LNTH = prove
 (`!(ll:A llist) k. LLENGTH ll = SOME k <=> !n. LNTH n ll = NONE <=> k <= n`,
  SUBGOAL_THEN
   `!ll:A llist. LFINITE ll ==>
                 !k. LLENGTH ll = SOME k ==> !n. LNTH n ll = NONE <=> k <= n`
   ASSUME_TAC THENL
   [MATCH_MP_TAC LFINITE_ind THEN
    REWRITE_TAC[LLENGTH_THM; option_INJ; LLISTAUX_OPTION_MAP_EQ_SOME] THEN
    CONJ_TAC THENL [REWRITE_TAC[LNTH_THM] THEN MESON_TAC[LE_0]; ALL_TAC] THEN
    REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
    DISCH_THEN(X_CHOOSE_THEN `z:num` (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:num`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN GEN_TAC THEN STRUCT_CASES_TAC(SPEC `n:num` num_CASES) THEN
    ASM_REWRITE_TAC[LNTH_THM; option_DISTINCT; LE; NOT_SUC; LE_SUC];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [ASM_MESON_TAC[LFINITE_LLENGTH]; DISCH_TAC] THEN
  SUBGOAL_THEN `LFINITE (ll:A llist)` ASSUME_TAC THENL
   [REWRITE_TAC[LFINITE_LNTH_NONE] THEN ASM_MESON_TAC[LE_REFL]; ALL_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_TAC `m:num` o MATCH_MP LFINITE_HAS_LENGTH) THEN
  ASM_REWRITE_TAC[option_INJ] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `ll:A llist`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `m:num`) THEN REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_MESON_TAC[LE_ANTISYM; LE_REFL]);;

let LLISTAUX_LLENGTH_NONE_LNTH = prove
 (`!ll:A llist. LLENGTH ll = NONE <=> !n. ?x. LNTH n ll = SOME x`,
  GEN_TAC THEN REWRITE_TAC[GSYM infinite_lnth_some] THEN
  MESON_TAC[LFINITE_LLENGTH; NOT_LFINITE_NO_LENGTH; option_DISTINCT]);;

let LNTH_LLENGTH_NONE = prove
 (`!x n (l:A llist). LLENGTH l = SOME x /\ x <= n ==> LNTH n l = NONE`,
  MESON_TAC[LLISTAUX_LLENGTH_SOME_LNTH]);;

(* ------------------------------------------------------------------------- *)
(* LAPPEND, LMAP and finiteness.                                             *)
(* ------------------------------------------------------------------------- *)

let NOT_LFINITE_APPEND = prove
 (`!ll1 ll2:A llist. ~LFINITE ll1 ==> LAPPEND ll1 ll2 = ll1`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LLISTAUX_BISIM THEN
  EXISTS_TAC `\a b:A llist. ~LFINITE b /\ ?l3. a = LAPPEND b l3` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  MAP_EVERY X_GEN_TAC [`a:A llist`; `b:A llist`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (X_CHOOSE_THEN `l3:A llist` SUBST1_TAC)) THEN
  LLIST_CASE_TAC `b:A llist` THEN
  REWRITE_TAC[LFINITE_THM; LAPPEND; LCONS_11; LCONS_NOT_NIL] THEN
  MESON_TAC[]);;

let LNTH_LAPPEND = prove
 (CASE_TERM
  `LNTH n (LAPPEND (l1:A llist) l2) =
   match LLENGTH l1 with
     NONE -> LNTH n l1
   | SOME m -> if n < m then LNTH n l1 else LNTH (n - m) l2`,
  ASM_CASES_TAC `LFINITE (l1:A llist)` THENL
   [ALL_TAC; ASM_SIMP_TAC[NOT_LFINITE_NO_LENGTH; NOT_LFINITE_APPEND; option_CASE]] THEN
  SPEC_TAC(`n:num`,`n:num`) THEN POP_ASSUM MP_TAC THEN
  SPEC_TAC(`l1:A llist`,`l1:A llist`) THEN MATCH_MP_TAC LFINITE_strongind THEN
  REWRITE_TAC[LAPPEND; LLENGTH_THM; option_CASE; LT; SUB_0] THEN
  MAP_EVERY X_GEN_TAC [`h:A`; `t:A llist`] THEN STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_TAC `m:num` o MATCH_MP LFINITE_HAS_LENGTH) THEN
  FIRST_X_ASSUM(MP_TAC o check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[OPTION_MAP_DEF; option_CASE] THEN DISCH_TAC THEN
  GEN_TAC THEN STRUCT_CASES_TAC(SPEC `n:num` num_CASES) THEN
  ASM_REWRITE_TAC[LNTH_THM; LT_0; LT_SUC; SUB_SUC]);;

let LFINITE_MAP = prove
 (`!(f:A->B) ll. LFINITE (LMAP f ll) <=> LFINITE ll`,
  REWRITE_TAC[LFINITE_LNTH_NONE; LNTH_LMAP; LLISTAUX_OPTION_MAP_EQ_NONE]);;

let LFINITE_APPEND = prove
 (`!ll1 ll2:A llist. LFINITE (LAPPEND ll1 ll2) <=> LFINITE ll1 /\ LFINITE ll2`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `LFINITE (ll1:A llist)` THEN
  ASM_SIMP_TAC[NOT_LFINITE_APPEND] THEN
  POP_ASSUM MP_TAC THEN SPEC_TAC(`ll1:A llist`,`ll1:A llist`) THEN
  MATCH_MP_TAC LFINITE_ind THEN SIMP_TAC[LAPPEND; LFINITE_THM]);;

let LFINITE_LAPPEND_IMP_NIL = prove
 (`!ll:A llist. LFINITE ll ==> !l2. LAPPEND ll l2 = ll ==> l2 = LNIL`,
  MATCH_MP_TAC LFINITE_ind THEN REWRITE_TAC[LAPPEND; LCONS_11] THEN
  MESON_TAC[]);;

let LLENGTH_MAP = prove
 (`!ll (f:A->B). LLENGTH (LMAP f ll) = LLENGTH ll`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `LFINITE (ll:A llist)` THENL
   [FIRST_ASSUM(X_CHOOSE_TAC `k:num` o MATCH_MP LFINITE_HAS_LENGTH) THEN
    ASM_REWRITE_TAC[LLISTAUX_LLENGTH_SOME_LNTH; LNTH_LMAP;
                    LLISTAUX_OPTION_MAP_EQ_NONE] THEN
    ASM_MESON_TAC[LLISTAUX_LLENGTH_SOME_LNTH];
    ASM_MESON_TAC[NOT_LFINITE_NO_LENGTH; LFINITE_MAP]]);;

let LLENGTH_APPEND = prove
 (`!ll1 ll2:A llist.
     LLENGTH (LAPPEND ll1 ll2) =
     if LFINITE ll1 /\ LFINITE ll2
     then SOME (THE (LLENGTH ll1) + THE (LLENGTH ll2)) else NONE`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[NOT_LFINITE_NO_LENGTH; LFINITE_APPEND]] THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  SPEC_TAC(`ll1:A llist`,`ll1:A llist`) THEN MATCH_MP_TAC LFINITE_strongind THEN
  REWRITE_TAC[LAPPEND; LLENGTH_THM; THE_DEF; ADD_CLAUSES] THEN CONJ_TAC THENL
   [FIRST_ASSUM(X_CHOOSE_TAC `k:num` o MATCH_MP LFINITE_HAS_LENGTH) THEN
    ASM_REWRITE_TAC[THE_DEF];
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(X_CHOOSE_TAC `m:num` o MATCH_MP LFINITE_HAS_LENGTH) THEN
    ASM_REWRITE_TAC[OPTION_MAP_DEF; THE_DEF; ADD_CLAUSES]]);;

let LMAP_APPEND = prove
 (`!(f:A->B) ll1 ll2. LMAP f (LAPPEND ll1 ll2) = LAPPEND (LMAP f ll1) (LMAP f ll2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LNTH_EQ; LNTH_LMAP; LNTH_LAPPEND; LLENGTH_MAP] THEN
  GEN_TAC THEN MP_TAC(ISPEC `LLENGTH (ll1:A llist)` (cases "option")) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[option_CASE] THEN
  COND_CASES_TAC THEN REWRITE_TAC[LNTH_LMAP]);;

let LAPPEND_NIL_2ND = prove
 (`!ll:A llist. LAPPEND ll LNIL = ll`,
  GEN_TAC THEN REWRITE_TAC[LNTH_EQ; LNTH_LAPPEND; LNTH_THM] THEN GEN_TAC THEN
  MP_TAC(ISPEC `LLENGTH (ll:A llist)` (cases "option")) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[option_CASE] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  ASM_MESON_TAC[LNTH_LLENGTH_NONE; NOT_LT]);;

(* ------------------------------------------------------------------------- *)
(* Mapping in and out of ordinary lists: HOL4 toList and fromList are        *)
(* llist_toList and llist_fromList here.                                     *)
(* ------------------------------------------------------------------------- *)

let llist_toList = new_definition
  `llist_toList (ll:A llist) =
     if LFINITE ll then LTAKE (THE (LLENGTH ll)) ll else NONE`;;

let llist_fromList_def = new_recursive_definition list_RECURSION
  `(llist_fromList [] = (LNIL:A llist)) /\
   (llist_fromList (CONS (h:A) t) = LCONS h (llist_fromList t))`;;

let toList_THM = prove
 (`(llist_toList (LNIL:A llist) = SOME []) /\
   (!(h:A) t. llist_toList (LCONS h t) = OPTION_MAP (CONS h) (llist_toList t))`,
  REWRITE_TAC[llist_toList; LFINITE_THM; LLENGTH_THM; THE_DEF; LTAKE_THM] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[OPTION_MAP_DEF] THEN
  FIRST_ASSUM(X_CHOOSE_TAC `m:num` o MATCH_MP LFINITE_HAS_LENGTH) THEN
  ASM_REWRITE_TAC[OPTION_MAP_DEF; THE_DEF; LTAKE_THM]);;

let fromList_EQ_LNIL = prove
 (`llist_fromList l = (LNIL:A llist) <=> l = []`,
  STRUCT_CASES_TAC(ISPEC `l:A list` list_CASES) THEN
  REWRITE_TAC[llist_fromList_def; LCONS_NOT_NIL; NOT_CONS_NIL]);;

let LHD_fromList = prove
 (`LHD (llist_fromList l) = if NULL l then NONE else SOME (HD (l:A list))`,
  STRUCT_CASES_TAC(ISPEC `l:A list` list_CASES) THEN
  REWRITE_TAC[llist_fromList_def; LHD_THM; NULL; HD]);;

let LTL_fromList = prove
 (`LTL (llist_fromList l) =
   if NULL l then NONE else SOME (llist_fromList (TL (l:A list)))`,
  STRUCT_CASES_TAC(ISPEC `l:A list` list_CASES) THEN
  REWRITE_TAC[llist_fromList_def; LTL_THM; NULL; TL]);;

let LFINITE_fromList = prove
 (`!l:A list. LFINITE (llist_fromList l)`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[llist_fromList_def; LFINITE_THM]);;

let LLENGTH_fromList = prove
 (`!l:A list. LLENGTH (llist_fromList l) = SOME (LENGTH l)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[llist_fromList_def; LLENGTH_THM; LENGTH; OPTION_MAP_DEF]);;

let LTAKE_fromList = prove
 (`!l:A list. LTAKE (LENGTH l) (llist_fromList l) = SOME l`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[llist_fromList_def; LTAKE_THM; LENGTH; OPTION_MAP_DEF]);;

let from_toList = prove
 (`!l:A list. llist_toList (llist_fromList l) = SOME l`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[llist_fromList_def; toList_THM; OPTION_MAP_DEF]);;

let LFINITE_IMP_fromList = prove
 (`!ll:A llist. LFINITE ll ==> ?l. ll = llist_fromList l`,
  MATCH_MP_TAC LFINITE_ind THEN CONJ_TAC THENL
   [EXISTS_TAC `[]:A list` THEN REWRITE_TAC[llist_fromList_def];
    REPEAT STRIP_TAC THEN EXISTS_TAC `CONS (h:A) l` THEN
    ASM_REWRITE_TAC[llist_fromList_def]]);;

let LFINITE_toList = prove
 (`!ll:A llist. LFINITE ll ==> ?l. llist_toList ll = SOME l`,
  MESON_TAC[LFINITE_IMP_fromList; from_toList]);;

let LFINITE_toList_SOME = prove
 (`LFINITE (ll:A llist) <=> IS_SOME (llist_toList ll)`,
  EQ_TAC THENL
   [MESON_TAC[LFINITE_toList; IS_SOME_DEF];
    REWRITE_TAC[llist_toList] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[IS_SOME_DEF]]);;

let to_fromList = prove
 (`!ll:A llist. LFINITE ll ==> llist_fromList (THE (llist_toList ll)) = ll`,
  MESON_TAC[LFINITE_IMP_fromList; from_toList; THE_DEF]);;

let LNTH_fromList = prove
 (`LNTH n (llist_fromList (l:A list)) =
   if n < LENGTH l then SOME (EL n l) else NONE`,
  SPEC_TAC(`n:num`,`n:num`) THEN SPEC_TAC(`l:A list`,`l:A list`) THEN
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[llist_fromList_def; LNTH_THM; LENGTH; LT]; ALL_TAC] THEN
  REWRITE_TAC[llist_fromList_def; LENGTH] THEN
  GEN_TAC THEN STRUCT_CASES_TAC(SPEC `n:num` num_CASES) THEN
  ASM_REWRITE_TAC[LNTH_THM; EL; HD; TL; LT_SUC; LT_0]);;

let lnth_fromList_some = prove
 (`!n (l:A list). n < LENGTH l <=> LNTH n (llist_fromList l) = SOME (EL n l)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LNTH_fromList] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT]);;

let LAPPEND_fromList = prove
 (`!l1 l2:A list.
     LAPPEND (llist_fromList l1) (llist_fromList l2) = llist_fromList (APPEND l1 l2)`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[llist_fromList_def; LAPPEND; APPEND]);;

let LMAP_fromList = prove
 (`LMAP (f:A->B) (llist_fromList l) = llist_fromList (MAP f l)`,
  SPEC_TAC(`l:A list`,`l:A list`) THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[llist_fromList_def; LMAP; MAP]);;

let fromList_11 = prove
 (`!xs ys:A list. llist_fromList xs = llist_fromList ys <=> xs = ys`,
  MESON_TAC[from_toList; option_INJ]);;

let fromList_EQ_CONS = prove
 (`llist_fromList l = LCONS (h:A) t <=> ?t0. l = CONS h t0 /\ t = llist_fromList t0`,
  STRUCT_CASES_TAC(ISPEC `l:A list` list_CASES) THEN
  REWRITE_TAC[llist_fromList_def; LCONS_NOT_NIL; LCONS_11; CONS_11;
              NOT_CONS_NIL] THEN
  MESON_TAC[]);;

let MAP_toList = prove
 (`!ll (f:A->B). LFINITE ll ==>
                 MAP f (THE (llist_toList ll)) = THE (llist_toList (LMAP f ll))`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `l:A list` SUBST1_TAC o MATCH_MP LFINITE_IMP_fromList) THEN
  REWRITE_TAC[LMAP_fromList; from_toList; THE_DEF]);;

(* ------------------------------------------------------------------------- *)
(* LDROP: drop a prefix of a given length, if there are that many elements.  *)
(* ------------------------------------------------------------------------- *)

let LDROP =
  let th = new_recursive_definition num_RECURSION
   `(LDROP 0 (ll:A llist) = SOME ll) /\
    (LDROP (SUC n) ll = OPTION_JOIN (OPTION_MAP (LDROP n) (LTL ll)))` in
  CONJ (GEN_ALL (CONJUNCT1 th)) (GEN_ALL (CONJUNCT2 th));;

let LDROP_THM = prove
 (`(!ll:A llist. LDROP 0 ll = SOME ll) /\
   (!n. LDROP (SUC n) (LNIL:A llist) = NONE) /\
   (!n (h:A) t. LDROP (SUC n) (LCONS h t) = LDROP n t)`,
  REWRITE_TAC[LDROP; LTL_THM; OPTION_MAP_DEF; OPTION_JOIN_DEF]);;

let LDROP_FUNPOW = prove
 (`!n (ll:A llist). LDROP n ll = ITER n (\m. OPTION_BIND m LTL) (SOME ll)`,
  INDUCT_TAC THENL [REWRITE_TAC[LDROP_THM; ITER]; ALL_TAC] THEN GEN_TAC THEN
  REWRITE_TAC[ITER_ALT; OPTION_BIND_DEF] THEN LLIST_CASE_TAC `ll:A llist` THEN
  ASM_REWRITE_TAC[LDROP_THM; LTL_THM; LLISTAUX_ITER_BIND_NONE]);;

let LDROP1_THM = prove
 (`LDROP 1 = (LTL:A llist->(A llist)option)`,
  REWRITE_TAC[FUN_EQ_THM; num_CONV `1`] THEN GEN_TAC THEN
  LLIST_CASE_TAC `x:A llist` THEN REWRITE_TAC[LDROP_THM; LTL_THM]);;

let LNTH_HD_LDROP = prove
 (`!n (ll:A llist). LNTH n ll = OPTION_BIND (LDROP n ll) LHD`,
  INDUCT_TAC THEN GEN_TAC THEN LLIST_CASE_TAC `ll:A llist` THEN
  ASM_REWRITE_TAC[LNTH_THM; LDROP_THM; OPTION_BIND_DEF; LHD_THM]);;

let LLISTAUX_LDROP_NONE = prove
 (`!n (ll:A llist). LDROP n ll = NONE <=> LTAKE n ll = NONE`,
  INDUCT_TAC THEN GEN_TAC THEN LLIST_CASE_TAC `ll:A llist` THEN
  ASM_REWRITE_TAC[LDROP_THM; LTAKE_THM; LLISTAUX_OPTION_MAP_EQ_NONE;
                  option_DISTINCT]);;

let LNTH_ADD = prove
 (`!a b (ll:A llist). LNTH (a + b) ll = OPTION_BIND (LDROP a ll) (LNTH b)`,
  INDUCT_TAC THEN REWRITE_TAC[ADD_CLAUSES; LDROP_THM; OPTION_BIND_DEF] THEN
  REPEAT GEN_TAC THEN LLIST_CASE_TAC `ll:A llist` THEN
  ASM_REWRITE_TAC[LNTH_THM; LDROP_THM; OPTION_BIND_DEF]);;

let LLISTAUX_LDROP_LNTH = prove
 (`!n (ll:A llist) l. LDROP n ll = SOME l ==> !m. LNTH m l = LNTH (n + m) ll`,
  SIMP_TAC[LNTH_ADD; OPTION_BIND_DEF]);;

let lnth_some_down_closed = prove
 (`!(ll:A llist) x n1 n2. LNTH n1 ll = SOME x /\ n2 <= n1 ==> ?y. LNTH n2 ll = SOME y`,
  MESON_TAC[LNTH_NONE_MONO; cases "option"; option_DISTINCT]);;

let LNTH_IS_SOME_MONO = prove
 (`!m n (l:A llist). IS_SOME (LNTH n l) /\ m <= n ==> IS_SOME (LNTH m l)`,
  REWRITE_TAC[LLISTAUX_IS_SOME_NONE] THEN MESON_TAC[LNTH_NONE_MONO]);;

let LNTH_IS_SOME = prove
 (`!n (ll:A llist). IS_SOME (LNTH n ll) <=> (LFINITE ll ==> n < THE (LLENGTH ll))`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `LFINITE (ll:A llist)` THENL
   [FIRST_ASSUM(X_CHOOSE_TAC `k:num` o MATCH_MP LFINITE_HAS_LENGTH) THEN
    FIRST_ASSUM(MP_TAC o REWRITE_RULE[LLISTAUX_LLENGTH_SOME_LNTH]) THEN
    ASM_REWRITE_TAC[THE_DEF; LLISTAUX_IS_SOME_NONE] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN ARITH_TAC;
    ASM_REWRITE_TAC[LLISTAUX_IS_SOME_NONE] THEN
    ASM_MESON_TAC[LFINITE_LNTH_NONE]]);;

let LFINITE_LNTH_IS_SOME = prove
 (`!n (ll:A llist). LFINITE ll ==> (IS_SOME (LNTH n ll) <=> n < THE (LLENGTH ll))`,
  SIMP_TAC[LNTH_IS_SOME]);;

let LDROP_LCONS_LNTH = prove
 (`!n (xs:A llist) a t. LDROP n xs = SOME (LCONS a t) ==> LNTH n xs = SOME a`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[LNTH_HD_LDROP; OPTION_BIND_DEF; LHD_THM]);;

let LNTH_LDROP = prove
 (`!n (l:A llist) x. LNTH n l = SOME x ==> LHD (THE (LDROP n l)) = SOME x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LNTH_HD_LDROP] THEN
  MP_TAC(ISPEC `LDROP n (l:A llist)` (cases "option")) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[OPTION_BIND_DEF; option_DISTINCT; THE_DEF]);;

let NOT_LFINITE_TAKE = prove
 (`!ll:A llist. ~LFINITE ll ==> !n. ?y. LTAKE n ll = SOME y`,
  REWRITE_TAC[LFINITE] THEN MESON_TAC[cases "option"]);;

let LFINITE_TAKE = prove
 (`!n (ll:A llist). LFINITE ll /\ n <= THE (LLENGTH ll) ==> ?y. LTAKE n ll = SOME y`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `k:num` o MATCH_MP LFINITE_HAS_LENGTH) THEN
  MATCH_MP_TAC(MESON[cases "option"]
    `~((x:(A list)option) = NONE) ==> ?y. x = SOME y`) THEN
  REWRITE_TAC[LLISTAUX_LTAKE_NONE; NOT_EXISTS_THM] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[THE_DEF] o
    check (fun th -> is_binary "<=" (concl th))) THEN
  ASM_REWRITE_TAC[THE_DEF] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[LLISTAUX_LLENGTH_SOME_LNTH]) THEN
  MESON_TAC[LTE_TRANS; NOT_LE]);;

let NOT_LFINITE_DROP = prove
 (`!ll:A llist. ~LFINITE ll ==> !n. ?y. LDROP n ll = SOME y`,
  REWRITE_TAC[LFINITE] THEN
  MESON_TAC[cases "option"; LLISTAUX_LDROP_NONE]);;

let LFINITE_DROP = prove
 (`!n (ll:A llist). LFINITE ll /\ n <= THE (LLENGTH ll) ==> ?y. LDROP n ll = SOME y`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP LFINITE_TAKE) THEN
  MESON_TAC[cases "option"; LLISTAUX_LDROP_NONE; option_DISTINCT]);;

let LTAKE_IMP_LDROP = prove
 (`!n (ll:A llist) l1.
     LTAKE n ll = SOME l1 ==>
     ?l2. LDROP n ll = SOME l2 /\ LAPPEND (llist_fromList l1) l2 = ll`,
  INDUCT_TAC THEN GEN_TAC THEN LLIST_CASE_TAC `ll:A llist` THEN
  REWRITE_TAC[LTAKE_THM; LDROP_THM; option_INJ; option_DISTINCT;
              LLISTAUX_OPTION_MAP_EQ_SOME] THEN
  REPEAT STRIP_TAC THENL
   [EXISTS_TAC `LNIL:A llist` THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[llist_fromList_def; LAPPEND];
    EXISTS_TAC `LCONS (h:A) t` THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[llist_fromList_def; LAPPEND];
    ASM_REWRITE_TAC[llist_fromList_def; LAPPEND; LCONS_11] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`t:A llist`; `z:A list`]) THEN
    ASM_REWRITE_TAC[]]);;

let LTAKE_DROP = prove
 (`(!n (ll:A llist).
      ~LFINITE ll ==>
      LAPPEND (llist_fromList (THE (LTAKE n ll))) (THE (LDROP n ll)) = ll) /\
   (!n (ll:A llist).
      LFINITE ll /\ n <= THE (LLENGTH ll) ==>
      LAPPEND (llist_fromList (THE (LTAKE n ll))) (THE (LDROP n ll)) = ll)`,
  SUBGOAL_THEN
   `!n (ll:A llist) y.
      LTAKE n ll = SOME y ==>
      LAPPEND (llist_fromList (THE (LTAKE n ll))) (THE (LDROP n ll)) = ll`
   ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP LTAKE_IMP_LDROP) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[THE_DEF];
    ASM_MESON_TAC[NOT_LFINITE_TAKE; LFINITE_TAKE]]);;

let LDROP_ADD = prove
 (CASE_TERM
  `!k1 k2 (x:A llist).
     LDROP (k1 + k2) x = match LDROP k1 x with NONE -> NONE | SOME ll -> LDROP k2 ll`,
  INDUCT_TAC THEN REWRITE_TAC[ADD_CLAUSES; LDROP_THM; option_CASE] THEN
  REPEAT GEN_TAC THEN LLIST_CASE_TAC `x:A llist` THEN
  ASM_REWRITE_TAC[LDROP_THM; option_CASE]);;

let LDROP_SOME_LLENGTH = prove
 (`LDROP n (ll:A llist) = SOME l /\ LLENGTH ll = SOME m ==>
   n <= m /\ LLENGTH l = SOME (m - n)`,
  SPEC_TAC(`m:num`,`m:num`) THEN SPEC_TAC(`ll:A llist`,`ll:A llist`) THEN
  SPEC_TAC(`n:num`,`n:num`) THEN
  INDUCT_TAC THEN REWRITE_TAC[LDROP_THM; option_INJ; LE_0; SUB_0] THENL
   [MESON_TAC[]; ALL_TAC] THEN
  GEN_TAC THEN LLIST_CASE_TAC `ll:A llist` THEN
  REWRITE_TAC[LDROP_THM; option_DISTINCT; LLENGTH_THM;
              LLISTAUX_OPTION_MAP_EQ_SOME] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`t:A llist`; `z:num`]) THEN
  ASM_REWRITE_TAC[LE_SUC; SUB_SUC] THEN MESON_TAC[]);;

let LDROP_EQ_LNIL = prove
 (`LDROP n (ll:A llist) = SOME LNIL <=> LLENGTH ll = SOME n`,
  SPEC_TAC(`ll:A llist`,`ll:A llist`) THEN SPEC_TAC(`n:num`,`n:num`) THEN
  INDUCT_TAC THEN REWRITE_TAC[LDROP_THM; option_INJ; LLENGTH_0] THEN
  GEN_TAC THEN LLIST_CASE_TAC `ll:A llist` THEN
  ASM_REWRITE_TAC[LDROP_THM; option_DISTINCT; LLENGTH_THM; option_INJ;
                  LLISTAUX_OPTION_MAP_EQ_SOME; NOT_SUC; SUC_INJ] THEN
  MESON_TAC[]);;

let NOT_LFINITE_DROP_LFINITE = prove
 (`!n (l:A llist) t. ~LFINITE l /\ LDROP n l = SOME t ==> ~LFINITE t`,
  INDUCT_TAC THEN REWRITE_TAC[LDROP_THM; option_INJ] THENL
   [MESON_TAC[]; ALL_TAC] THEN
  GEN_TAC THEN LLIST_CASE_TAC `l:A llist` THEN
  REWRITE_TAC[LDROP_THM; option_DISTINCT; LFINITE_THM] THEN
  ASM_MESON_TAC[]);;

let LDROP_APPEND1 = prove
 (`LDROP n l1 = SOME (l:A llist) ==> LDROP n (LAPPEND l1 l2) = SOME (LAPPEND l l2)`,
  SPEC_TAC(`l1:A llist`,`l1:A llist`) THEN SPEC_TAC(`n:num`,`n:num`) THEN
  INDUCT_TAC THEN REWRITE_TAC[LDROP_THM; option_INJ] THENL
   [MESON_TAC[]; ALL_TAC] THEN
  GEN_TAC THEN LLIST_CASE_TAC `l1:A llist` THEN
  ASM_REWRITE_TAC[LDROP_THM; option_DISTINCT; LAPPEND]);;

let LDROP_fromList = prove
 (`!ls:A list n.
     LDROP n (llist_fromList ls) =
     if n <= LENGTH ls then SOME (llist_fromList (DROP n ls)) else NONE`,
  LIST_INDUCT_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC(SPEC `n:num` num_CASES) THEN
  ASM_REWRITE_TAC[llist_fromList_def; LDROP_THM; LENGTH; LE_0; LE; NOT_SUC;
                  DROP_DEF; LE_SUC; SUC_SUB1]);;

let LDROP_SUC = prove
 (`LDROP (SUC n) (ls:A llist) = OPTION_BIND (LDROP n ls) LTL`,
  REWRITE_TAC[LDROP_FUNPOW; ITER]);;

let LDROP_1 = prove
 (`LDROP (1:num) (LCONS (h:A) t) = SOME t`,
  REWRITE_TAC[num_CONV `1`; LDROP_THM]);;

let LDROP_NONE_LFINITE = prove
 (`LDROP k (l:A llist) = NONE ==> LFINITE l`,
  MESON_TAC[NOT_LFINITE_DROP; option_DISTINCT]);;

let LDROP_LDROP = prove
 (`!(ll:A llist) k1 k2.
     ~LFINITE ll ==>
     THE (LDROP k2 (THE (LDROP k1 ll))) = THE (LDROP k1 (THE (LDROP k2 ll)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k1:num`; `k2:num`; `ll:A llist`] LDROP_ADD) THEN
  MP_TAC(ISPECL [`k2:num`; `k1:num`; `ll:A llist`] LDROP_ADD) THEN
  FIRST_ASSUM(MP_TAC o SPEC `k1:num` o MATCH_MP NOT_LFINITE_DROP) THEN
  FIRST_ASSUM(MP_TAC o SPEC `k2:num` o MATCH_MP NOT_LFINITE_DROP) THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SYM) THEN
  FIRST_X_ASSUM(MP_TAC o SYM) THEN
  ASM_REWRITE_TAC[option_CASE; THE_DEF] THEN
  REWRITE_TAC[ADD_SYM] THEN MESON_TAC[]);;

let LTAKE_LLENGTH_NONE = prove
 (`LLENGTH (ll:A llist) = SOME n /\ n < m ==> LTAKE m ll = NONE`,
  REWRITE_TAC[LLISTAUX_LLENGTH_SOME_LNTH; LLISTAUX_LTAKE_NONE] THEN
  MESON_TAC[LE_REFL]);;

let LTAKE_LLENGTH_SOME = prove
 (`LLENGTH (ll:A llist) = SOME n ==> ?l. LTAKE n ll = SOME l /\ llist_toList ll = SOME l`,
  DISCH_TAC THEN SUBGOAL_THEN `LFINITE (ll:A llist)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LFINITE_LLENGTH]; ALL_TAC] THEN
  ASM_REWRITE_TAC[llist_toList; THE_DEF] THEN
  MATCH_MP_TAC LFINITE_TAKE THEN ASM_REWRITE_TAC[THE_DEF; LE_REFL]);;

let LTAKE_LAPPEND2 = prove
 (`!n (l1:A llist) l2.
     LTAKE n l1 = NONE ==>
     LTAKE n (LAPPEND l1 l2) =
     OPTION_MAP (APPEND (THE (llist_toList l1))) (LTAKE (n - THE (LLENGTH l1)) l2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `LFINITE (l1:A llist)` MP_TAC THENL
   [ASM_MESON_TAC[LFINITE]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:A list` SUBST_ALL_TAC o
    MATCH_MP LFINITE_IMP_fromList) THEN
  POP_ASSUM MP_TAC THEN
  REWRITE_TAC[from_toList; LLENGTH_fromList; THE_DEF] THEN
  SPEC_TAC(`n:num`,`n:num`) THEN SPEC_TAC(`l:A list`,`l:A list`) THEN
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[llist_fromList_def; LAPPEND; LENGTH; SUB_0; APPEND] THENL
   [REWRITE_TAC[LTAKE_NIL_EQ_NONE] THEN GEN_TAC THEN DISCH_TAC THEN
    MP_TAC(ISPEC `LTAKE n (l2:A llist)` (cases "option")) THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[OPTION_MAP_DEF; APPEND; ETA_AX] THEN
    REWRITE_TAC[GSYM(CONJUNCT1 APPEND); ETA_AX];
    ALL_TAC] THEN
  GEN_TAC THEN STRUCT_CASES_TAC(SPEC `n:num` num_CASES) THEN
  REWRITE_TAC[LTAKE_THM; option_DISTINCT; LLISTAUX_OPTION_MAP_EQ_NONE] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `n':num`) THEN
  ASM_REWRITE_TAC[SUB_SUC] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPEC `LTAKE (n' - LENGTH (t:A list)) (l2:A llist)` (cases "option")) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[OPTION_MAP_DEF; APPEND]);;

let toList_LAPPEND_APPEND = prove
 (`llist_toList (LAPPEND l1 l2) = SOME x ==>
   x = APPEND (THE (llist_toList l1)) (THE (llist_toList (l2:A llist)))`,
  DISCH_TAC THEN
  SUBGOAL_THEN `LFINITE (LAPPEND l1 (l2:A llist))` MP_TAC THENL
   [ASM_REWRITE_TAC[LFINITE_toList_SOME; IS_SOME_DEF]; ALL_TAC] THEN
  REWRITE_TAC[LFINITE_APPEND] THEN STRIP_TAC THEN
  MAP_EVERY (fun v -> FIRST_X_ASSUM(X_CHOOSE_THEN v SUBST_ALL_TAC o
                        MATCH_MP LFINITE_IMP_fromList))
   [`k2:A list`; `k1:A list`] THEN
  POP_ASSUM MP_TAC THEN
  REWRITE_TAC[LAPPEND_fromList; from_toList; THE_DEF; option_INJ] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* exists (HOL4 exists, here llist_exists: inductive) and every.             *)
(* ------------------------------------------------------------------------- *)

let exists_rules,exists_ind,exists_cases = new_inductive_definition
  `(!(h:A) t. P h ==> llist_exists P (LCONS h t)) /\
   (!(h:A) t. llist_exists P t ==> llist_exists P (LCONS h t))`;;

let exists_strongind = derive_strong_induction(exists_rules,exists_ind);;

let exists_thm = prove
 (`(llist_exists P (LNIL:A llist) <=> F) /\
   (llist_exists P (LCONS (h:A) t) <=> P h \/ llist_exists P t)`,
  CONJ_TAC THEN GEN_REWRITE_TAC LAND_CONV [exists_cases] THEN
  REWRITE_TAC[LCONS_NOT_NIL; LCONS_11] THEN MESON_TAC[]);;

let exists_LNTH = prove
 (`!l:A llist. llist_exists P l <=> ?n e. SOME e = LNTH n l /\ P e`,
  GEN_TAC THEN EQ_TAC THENL
   [SPEC_TAC(`l:A llist`,`l:A llist`) THEN MATCH_MP_TAC exists_ind THEN
    CONJ_TAC THEN REPEAT GEN_TAC THENL
     [DISCH_TAC THEN MAP_EVERY EXISTS_TAC [`0`; `h:A`] THEN
      ASM_REWRITE_TAC[LNTH_THM];
      DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_TAC `e:A`)) THEN
      MAP_EVERY EXISTS_TAC [`SUC n`; `e:A`] THEN ASM_REWRITE_TAC[LNTH_THM]];
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN SPEC_TAC(`l:A llist`,`l:A llist`) THEN
    ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN INDUCT_TAC THEN
    GEN_TAC THEN LLIST_CASE_TAC `l:A llist` THEN
    REWRITE_TAC[LNTH_THM; option_DISTINCT; option_INJ; exists_thm] THEN
    ASM_MESON_TAC[]]);;

let MONO_exists = prove
 (`(!x:A. P x ==> Q x) ==> (llist_exists P l ==> llist_exists Q l)`,
  REWRITE_TAC[exists_LNTH] THEN MESON_TAC[]);;

let exists_strong_ind = prove
 (`!P Q. (!(h:A) t. P h ==> Q (LCONS h t)) /\
         (!h t. Q t /\ llist_exists P t ==> Q (LCONS h t))
         ==> !a0. llist_exists P a0 ==> Q a0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC exists_strongind THEN
  ASM_MESON_TAC[]);;

let LLISTAUX_LNTH_LDROP_SOME = prove
 (`!n (ll:A llist) e. LNTH n ll = SOME e <=> ?t. LDROP n ll = SOME (LCONS e t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LNTH_HD_LDROP] THEN
  MP_TAC(ISPEC `LDROP n (ll:A llist)` (cases "option")) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[OPTION_BIND_DEF; option_DISTINCT; option_INJ] THEN
  LLIST_CASE_TAC `a:A llist` THEN
  REWRITE_TAC[LHD_THM; option_DISTINCT; option_INJ; LCONS_NOT_NIL; LCONS_11] THEN
  MESON_TAC[]);;

let exists_LDROP = prove
 (`llist_exists P (ll:A llist) <=> ?n a t. LDROP n ll = SOME (LCONS a t) /\ P a`,
  REWRITE_TAC[exists_LNTH] THEN MESON_TAC[LLISTAUX_LNTH_LDROP_SOME]);;

let exists_thm_strong = prove
 (`llist_exists P (ll:A llist) <=>
   ?n a t l. LDROP n ll = SOME (LCONS a t) /\ P a /\
             LTAKE n ll = SOME l /\ ALL ((~) o P) l`,
  EQ_TAC THENL [ALL_TAC; REWRITE_TAC[exists_LDROP] THEN MESON_TAC[]] THEN
  REWRITE_TAC[exists_LNTH] THEN
  GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `a:A` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`n:num`; `ll:A llist`; `a:A`] LLISTAUX_LNTH_LDROP_SOME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `t:A llist`) THEN
  SUBGOAL_THEN `?l:A list. LTAKE n ll = SOME l` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(MESON[cases "option"]
      `~((x:(A list)option) = NONE) ==> ?y. x = SOME y`) THEN
    REWRITE_TAC[LLISTAUX_LTAKE_NONE] THEN
    ASM_MESON_TAC[LNTH_NONE_MONO; LT_IMP_LE; option_DISTINCT];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`n:num`; `a:A`; `t:A llist`; `l:A list`] THEN
  ASM_REWRITE_TAC[GSYM ALL_EL; o_THM] THEN
  FIRST_ASSUM(ASSUME_TAC o SYM o MATCH_MP LTAKE_LENGTH) THEN
  X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`n:num`; `ll:A llist`; `m:num`; `l:A list`] LTAKE_LNTH_EL) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MESON_TAC[]);;

let llist_every_def = new_definition
  `llist_every P (ll:A llist) <=> ~llist_exists ((~) o P) ll`;;

let every_LNTH = prove
 (`!P (ll:A llist). llist_every P ll <=> !n e. LNTH n ll = SOME e ==> P e`,
  REWRITE_TAC[llist_every_def; exists_LNTH; o_THM] THEN MESON_TAC[]);;

let every_thm = prove
 (`(llist_every P (LNIL:A llist) <=> T) /\
   (llist_every P (LCONS (h:A) t) <=> P h /\ llist_every P t)`,
  REWRITE_TAC[llist_every_def; exists_thm; o_THM; DE_MORGAN_THM]);;

let LL_ALL_THM = every_thm;;

let llist_every_coind = prove
 (`!P (Q:A llist->bool).
     (!h t. Q (LCONS h t) ==> P h /\ Q t) ==> !ll. Q ll ==> llist_every P ll`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[every_LNTH] THEN
  SUBGOAL_THEN `!n (ll:A llist) e. Q ll /\ LNTH n ll = SOME e ==> P e`
    (fun th -> MESON_TAC[th]) THEN
  INDUCT_TAC THEN GEN_TAC THEN LLIST_CASE_TAC `ll:A llist` THEN
  REWRITE_TAC[LNTH_THM; option_DISTINCT; option_INJ] THEN ASM_MESON_TAC[]);;

let MONO_every = prove
 (`(!x:A. P x ==> Q x) ==> (llist_every P l ==> llist_every Q l)`,
  REWRITE_TAC[every_LNTH] THEN MESON_TAC[]);;

let every_strong_coind = prove
 (`!P (Q:A llist->bool).
     (!h t. Q (LCONS h t) ==> P h) /\ (!h t. Q (LCONS h t) ==> Q t \/ llist_every P t)
     ==> !ll. Q ll ==> llist_every P ll`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`P:A->bool`; `\ll:A llist. Q ll \/ llist_every P ll`] llist_every_coind) THEN
  REWRITE_TAC[every_thm] THEN ANTS_TAC THENL [ASM_MESON_TAC[]; MESON_TAC[]]);;

let every_LDROP = prove
 (`!f i (ll1:A llist) ll2. llist_every f ll1 /\ LDROP i ll1 = SOME ll2 ==> llist_every f ll2`,
  REWRITE_TAC[every_LNTH] THEN MESON_TAC[LLISTAUX_LDROP_LNTH]);;

let every_LAPPEND1 = prove
 (`!P (ll1:A llist) ll2. llist_every P (LAPPEND ll1 ll2) ==> llist_every P ll1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[every_LNTH; LNTH_LAPPEND] THEN
  MP_TAC(ISPEC `LLENGTH (ll1:A llist)` (cases "option")) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[option_CASE] THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `e:A`] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `e:A`]) THEN
  ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[LNTH_LLENGTH_NONE; NOT_LT; option_DISTINCT]);;

let every_fromList_EVERY = prove
 (`!l:A list P. llist_every P (llist_fromList l) <=> ALL P l`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[llist_fromList_def; every_thm; ALL]);;

let every_LAPPEND2_LFINITE = prove
 (`!(l:A llist) P ll. LFINITE l /\ llist_every P (LAPPEND l ll) ==> llist_every P ll`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC LFINITE_ind THEN SIMP_TAC[LAPPEND; every_thm]);;

let every_APPEND_EQN = prove
 (`llist_every P (LAPPEND l1 l2) <=> llist_every P (l1:A llist) /\ (LFINITE l1 ==> llist_every P l2)`,
  ASM_CASES_TAC `LFINITE (l1:A llist)` THEN
  ASM_SIMP_TAC[NOT_LFINITE_APPEND] THEN
  POP_ASSUM MP_TAC THEN SPEC_TAC(`l1:A llist`,`l1:A llist`) THEN
  MATCH_MP_TAC LFINITE_ind THEN SIMP_TAC[LAPPEND; every_thm; CONJ_ACI]);;

let exists_APPEND = prove
 (`!l1 l2:A llist.
     llist_exists P (LAPPEND l1 l2) <=>
     llist_exists P l1 \/ LFINITE l1 /\ llist_exists P l2`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `LFINITE (l1:A llist)` THEN
  ASM_SIMP_TAC[NOT_LFINITE_APPEND] THEN
  POP_ASSUM MP_TAC THEN SPEC_TAC(`l1:A llist`,`l1:A llist`) THEN
  MATCH_MP_TAC LFINITE_ind THEN SIMP_TAC[LAPPEND; exists_thm; DISJ_ACI]);;

let every_LMAP = prove
 (`llist_every P (LMAP (f:A->B) l) <=> llist_every (P o f) l`,
  REWRITE_TAC[every_LNTH; LNTH_LMAP; LLISTAUX_OPTION_MAP_EQ_SOME; o_THM] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* LPREFIX (HOL4 definition by cases on llist_toList); LPREFIX_NTH is the     *)
(* pointwise characterization the rest of the theory uses.                   *)
(* ------------------------------------------------------------------------- *)

let LPREFIX_def = new_definition (CASE_TERM
  `LPREFIX (l1:A llist) l2 <=>
     match llist_toList l1 with
       NONE -> l1 = l2
     | SOME xs -> (match llist_toList l2 with
                     NONE -> LTAKE (LENGTH xs) l2 = SOME xs
                   | SOME ys -> isPREFIX xs ys)`);;

(* list facts (list theory; local) *)

let LLISTAUX_FORALL_LT_SUC = prove
 (`!P n. (!i. i < SUC n ==> P i) <=> P 0 /\ (!j. j < n ==> P (SUC j))`,
  REPEAT GEN_TAC THEN EQ_TAC THENL [MESON_TAC[LT_0; LT_SUC]; STRIP_TAC] THEN
  INDUCT_TAC THEN ASM_SIMP_TAC[LT_SUC]);;

let LLISTAUX_isPREFIX_EL = prove
 (`!xs ys:A list.
     isPREFIX xs ys <=>
     LENGTH xs <= LENGTH ys /\ !i. i < LENGTH xs ==> EL i xs = EL i ys`,
  LIST_INDUCT_TAC THENL [REWRITE_TAC[isPREFIX; LENGTH; LE_0; LT]; ALL_TAC] THEN
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `ys:A list` list_CASES) THEN
  ASM_REWRITE_TAC[isPREFIX; list_CASE; LENGTH; LE_SUC;
                  ARITH_RULE `!n. ~(SUC n <= 0)`;
                  LLISTAUX_FORALL_LT_SUC; EL; HD; TL] THEN
  MESON_TAC[]);;

let LLISTAUX_fromList_NTH = prove
 (`!xs (l2:A llist).
     (!i v. LNTH i (llist_fromList xs) = SOME v ==> LNTH i l2 = SOME v) <=>
     (!i. i < LENGTH xs ==> LNTH i l2 = SOME (EL i xs))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LNTH_fromList] THEN EQ_TAC THEN
  REPEAT STRIP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    POP_ASSUM MP_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC[option_INJ; option_DISTINCT] THEN ASM_MESON_TAC[]]);;

let LPREFIX_NTH = prove
 (`LPREFIX (l1:A llist) l2 <=> !i v. LNTH i l1 = SOME v ==> LNTH i l2 = SOME v`,
  ASM_CASES_TAC `LFINITE (l1:A llist)` THENL
   [ALL_TAC;
    ASM_REWRITE_TAC[LPREFIX_def; llist_toList; option_CASE; LNTH_EQ] THEN
    FIRST_ASSUM(MP_TAC o REWRITE_RULE[infinite_lnth_some]) THEN
    MESON_TAC[]] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `xs:A list` SUBST1_TAC o
    MATCH_MP LFINITE_IMP_fromList) THEN
  REWRITE_TAC[LPREFIX_def; from_toList; option_CASE; LLISTAUX_fromList_NTH] THEN
  ASM_CASES_TAC `LFINITE (l2:A llist)` THENL
   [ALL_TAC;
    ASM_REWRITE_TAC[llist_toList; option_CASE; LLISTAUX_LTAKE_SOME_EQ]] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `ys:A list` SUBST1_TAC o
    MATCH_MP LFINITE_IMP_fromList) THEN
  REWRITE_TAC[from_toList; option_CASE; LLISTAUX_isPREFIX_EL; LNTH_fromList] THEN
  EQ_TAC THEN STRIP_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `i < LENGTH (ys:A list)` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ASM_CASES_TAC `xs:A list = []` THEN ASM_REWRITE_TAC[LENGTH; LE_0] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `LENGTH (xs:A list) - 1`) THEN
    SUBGOAL_THEN `LENGTH (xs:A list) - 1 < LENGTH xs` ASSUME_TAC THENL
     [ASM_MESON_TAC[LENGTH_EQ_NIL; ARITH_RULE `~(n = 0) ==> n - 1 < n`];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN
    REWRITE_TAC[option_DISTINCT] THEN ASM_ARITH_TAC;
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
    COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
    MESON_TAC[]]);;

let LPREFIX_REFL = prove
 (`LPREFIX (ll:A llist) ll`,
  REWRITE_TAC[LPREFIX_NTH]);;

let LPREFIX_ANTISYM = prove
 (`LPREFIX (l1:A llist) l2 /\ LPREFIX l2 l1 ==> l1 = l2`,
  REWRITE_TAC[LPREFIX_NTH; LNTH_EQ] THEN STRIP_TAC THEN X_GEN_TAC `n:num` THEN
  MP_TAC(ISPEC `LNTH n (l1:A llist)` (cases "option")) THEN
  MP_TAC(ISPEC `LNTH n (l2:A llist)` (cases "option")) THEN
  ASM_MESON_TAC[option_DISTINCT]);;

let LPREFIX_TRANS = prove
 (`LPREFIX (l1:A llist) l2 /\ LPREFIX l2 l3 ==> LPREFIX l1 l3`,
  REWRITE_TAC[LPREFIX_NTH] THEN MESON_TAC[]);;

let LPREFIX_LNIL = prove
 (`LPREFIX (LNIL:A llist) ll /\ (LPREFIX ll (LNIL:A llist) <=> ll = LNIL)`,
  REWRITE_TAC[LPREFIX_NTH; LNTH_THM; option_DISTINCT] THEN
  LLIST_CASE_TAC `ll:A llist` THEN
  REWRITE_TAC[LNTH_THM; LCONS_NOT_NIL; option_DISTINCT] THEN
  DISCH_THEN(MP_TAC o SPECL [`0`; `h:A`]) THEN REWRITE_TAC[LNTH_THM]);;

let LLISTAUX_FORALL_NUM_SPLIT = prove
 (`!P. (!n. P n) <=> P 0 /\ (!n. P (SUC n))`,
  MESON_TAC[num_CASES]);;

let LPREFIX_LCONS = prove
 (`(!(ll:A llist) h t.
      LPREFIX ll (LCONS h t) <=> ll = LNIL \/ ?l. ll = LCONS h l /\ LPREFIX l t) /\
   (!(h:A) t ll. LPREFIX (LCONS h t) ll <=> ?l. ll = LCONS h l /\ LPREFIX t l)`,
  CONJ_TAC THEN REPEAT GEN_TAC THEN LLIST_CASE_TAC `ll:A llist` THEN
  REWRITE_TAC[LPREFIX_LNIL; LCONS_NOT_NIL; LCONS_11] THEN
  REWRITE_TAC[LPREFIX_NTH] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [LLISTAUX_FORALL_NUM_SPLIT] THEN
  REWRITE_TAC[LNTH_THM; option_INJ; option_DISTINCT; UNWIND_THM1] THEN
  MESON_TAC[]);;

let LPREFIX_fromList = prove
 (CASE_TERM
  `!l (ll:A llist).
     LPREFIX (llist_fromList l) ll <=>
     match llist_toList ll with
       NONE -> LTAKE (LENGTH l) ll = SOME l
     | SOME ys -> isPREFIX l ys`,
  REWRITE_TAC[LPREFIX_def; from_toList; option_CASE]);;

let prefixes_lprefix_total = prove
 (`!ll:A llist. !l1 l2. LPREFIX l1 ll /\ LPREFIX l2 ll ==> LPREFIX l1 l2 \/ LPREFIX l2 l1`,
  REWRITE_TAC[LPREFIX_NTH] THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `!i v. LNTH i (l1:A llist) = SOME v ==> LNTH i l2 = SOME v` THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[NOT_FORALL_THM; NOT_IMP]) THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` (X_CHOOSE_THEN `v:A` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `LNTH i (l2:A llist) = NONE` ASSUME_TAC THENL
   [MP_TAC(ISPEC `LNTH i (l2:A llist)` (cases "option")) THEN
    ASM_MESON_TAC[option_INJ];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`j:num`; `u:A`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `j < i` ASSUME_TAC THENL
   [ASM_MESON_TAC[LNTH_NONE_MONO; NOT_LT; option_DISTINCT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`l1:A llist`; `v:A`; `i:num`; `j:num`] lnth_some_down_closed) THEN
  ASM_SIMP_TAC[LT_IMP_LE] THEN ASM_MESON_TAC[option_INJ]);;

let LPREFIX_APPEND = prove
 (`LPREFIX (l1:A llist) l2 <=> ?ll. l2 = LAPPEND l1 ll`,
  EQ_TAC THENL
   [ALL_TAC;
    DISCH_THEN(X_CHOOSE_THEN `ll:A llist` SUBST1_TAC) THEN
    REWRITE_TAC[LPREFIX_NTH; LNTH_LAPPEND] THEN REPEAT GEN_TAC THEN
    MP_TAC(ISPEC `LLENGTH (l1:A llist)` (cases "option")) THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[option_CASE] THEN
    ASM_MESON_TAC[LNTH_LLENGTH_NONE; NOT_LT; option_DISTINCT]] THEN
  REWRITE_TAC[LPREFIX_NTH] THEN DISCH_TAC THEN
  ASM_CASES_TAC `LFINITE (l1:A llist)` THENL
   [ALL_TAC;
    EXISTS_TAC `LNIL:A llist` THEN ASM_SIMP_TAC[NOT_LFINITE_APPEND] THEN
    REWRITE_TAC[LNTH_EQ] THEN
    FIRST_ASSUM(MP_TAC o REWRITE_RULE[infinite_lnth_some]) THEN
    ASM_MESON_TAC[]] THEN
  FIRST_ASSUM(X_CHOOSE_TAC `m:num` o MATCH_MP LFINITE_HAS_LENGTH) THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[LLISTAUX_LLENGTH_SOME_LNTH]) THEN
  SUBGOAL_THEN `?ll:A llist. LDROP m l2 = SOME ll` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(MESON[cases "option"]
      `~((x:(A llist)option) = NONE) ==> ?y. x = SOME y`) THEN
    REWRITE_TAC[LLISTAUX_LDROP_NONE; LLISTAUX_LTAKE_NONE; NOT_EXISTS_THM] THEN
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    MP_TAC(ISPEC `LNTH k (l1:A llist)` (cases "option")) THEN
    ASM_MESON_TAC[NOT_LT; option_DISTINCT];
    ALL_TAC] THEN
  EXISTS_TAC `ll:A llist` THEN REWRITE_TAC[LNTH_EQ; LNTH_LAPPEND] THEN
  ASM_REWRITE_TAC[option_CASE] THEN X_GEN_TAC `n:num` THEN
  COND_CASES_TAC THENL
   [MP_TAC(ISPEC `LNTH n (l1:A llist)` (cases "option")) THEN
    ASM_MESON_TAC[NOT_LT; option_DISTINCT];
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LLISTAUX_LDROP_LNTH th]) THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC]);;

let LAPPEND11_FINITE1 = prove
 (`!l1 l2 l3:A llist. LFINITE l1 ==> (LAPPEND l1 l2 = LAPPEND l1 l3 <=> l2 = l3)`,
  SUBGOAL_THEN
   `!l1:A llist. LFINITE l1 ==>
                 !l2 l3. LAPPEND l1 l2 = LAPPEND l1 l3 <=> l2 = l3`
   (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC LFINITE_ind THEN SIMP_TAC[LAPPEND; LCONS_11]);;

let LPREFIX_LAPPEND_fromList = prove
 (`LPREFIX (LAPPEND (llist_fromList l) l1) (LAPPEND (llist_fromList l) l2) <=>
   LPREFIX (l1:A llist) l2`,
  REWRITE_TAC[LPREFIX_APPEND; LAPPEND_ASSOC] THEN
  SIMP_TAC[LAPPEND11_FINITE1; LFINITE_fromList]);;

let LTAKE_LPREFIX = prove
 (`!x (ll:A llist).
     ~LFINITE ll ==> ?l. LTAKE x ll = SOME l /\ LPREFIX (llist_fromList l) ll`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `l:A list` o SPEC `x:num` o MATCH_MP NOT_LFINITE_TAKE) THEN
  EXISTS_TAC `l:A list` THEN ASM_REWRITE_TAC[LPREFIX_NTH; LLISTAUX_fromList_NTH] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP LTAKE_LENGTH) THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LTAKE_LNTH_EL THEN
  EXISTS_TAC `x:num` THEN ASM_MESON_TAC[]);;

let LPREFIX_LUNFOLD = prove
 (CASE_TERM
  `LPREFIX ll (LUNFOLD (f:A->(A#B)option) n) <=>
   match f n with
     NONE -> ll = LNIL
   | SOME (n,x) -> !h t. ll = LCONS h t ==> h = x /\ LPREFIX t (LUNFOLD f n)`,
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [LUNFOLD] THEN
  LLISTAUX_OPT_PAIR_CASES_TAC `(f:A->(A#B)option) n` THEN
  REWRITE_TAC[option_CASE; pair_CASE; LPREFIX_LNIL; LPREFIX_LCONS] THEN
  LLIST_CASE_TAC `ll:B llist` THEN
  REWRITE_TAC[LCONS_NOT_NIL; LCONS_11] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The set of the elements of a lazy list (HOL4 LSET_def; the Candle prover  *)
(* uses it).                                                                 *)
(* ------------------------------------------------------------------------- *)

let LSET_def = new_definition
  `LSET (l:A llist) x <=> ?n. LNTH n l = SOME x`;;

(* ------------------------------------------------------------------------- *)
(* Temporal logic style operators: eventually (inductive), always            *)
(* (coinductive).                                                            *)
(* ------------------------------------------------------------------------- *)

let llist_eventually_rules,llist_eventually_ind,llist_eventually_cases = new_inductive_definition
  `(!ll:A llist. P ll ==> llist_eventually P ll) /\
   (!(h:A) t. llist_eventually P t ==> llist_eventually P (LCONS h t))`;;

let eventually_thm = prove
 (`(llist_eventually P (LNIL:A llist) <=> P LNIL) /\
   (llist_eventually P (LCONS (h:A) t) <=> P (LCONS h t) \/ llist_eventually P t)`,
  CONJ_TAC THEN GEN_REWRITE_TAC LAND_CONV [llist_eventually_cases] THEN
  REWRITE_TAC[LCONS_NOT_NIL; LCONS_11] THEN MESON_TAC[]);;

(* always is coinductive (HOL4 Hol_coreln): the greatest fixpoint, given by *)
(* an invariant.                                                             *)

let always_def = new_definition
  `always P (ll:A llist) <=>
     ?Q. Q ll /\ !l. Q l ==> ?h t. l = LCONS h t /\ P (LCONS h t) /\ Q t`;;

let always_coind = prove
 (`!P always'.
     (!a0:A llist. always' a0 ==>
                   ?h t. a0 = LCONS h t /\ P (LCONS h t) /\ always' t)
     ==> !a0. always' a0 ==> always P a0`,
  REWRITE_TAC[always_def] THEN MESON_TAC[]);;

let always_cases = prove
 (`!P (a0:A llist).
     always P a0 <=> ?h t. a0 = LCONS h t /\ P (LCONS h t) /\ always P t`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[always_def] THEN MESON_TAC[]; STRIP_TAC] THEN
  REWRITE_TAC[always_def] THEN
  EXISTS_TAC `\l:A llist. l = a0 \/ always P l` THEN REWRITE_TAC[] THEN
  X_GEN_TAC `l:A llist` THEN STRIP_TAC THENL
   [ASM_MESON_TAC[];
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[always_def]) THEN
    DISCH_THEN(X_CHOOSE_THEN `Q:A llist->bool` STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP th (ASSUME `(Q:A llist->bool) l`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `h1:A` (X_CHOOSE_THEN `t1:A llist`
      STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`h1:A`; `t1:A llist`] THEN ASM_REWRITE_TAC[] THEN
    DISJ2_TAC THEN REWRITE_TAC[always_def] THEN
    EXISTS_TAC `Q:A llist->bool` THEN ASM_REWRITE_TAC[]]);;

let always_rules = prove
 (`!P (h:A) t. P (LCONS h t) /\ always P t ==> always P (LCONS h t)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[always_cases] THEN ASM_MESON_TAC[]);;

let always_thm = prove
 (`(always P (LNIL:A llist) <=> F) /\
   (!(h:A) t. always P (LCONS h t) <=> P (LCONS h t) /\ always P t)`,
  CONJ_TAC THEN REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [always_cases] THEN
  REWRITE_TAC[LCONS_NOT_NIL; LCONS_11] THEN MESON_TAC[]);;

let always_conj_l = prove
 (`!ll:A llist. always (\x. P x /\ Q x) ll ==> always P ll`,
  MATCH_MP_TAC always_coind THEN X_GEN_TAC `ll:A llist` THEN
  GEN_REWRITE_TAC LAND_CONV [always_cases] THEN MESON_TAC[]);;

let always_eventually_ind = prove
 (`(!ll:A llist. (P ll \/ (~P ll /\ Q (THE (LTL ll)))) ==> Q ll) ==>
   !ll. ~(ll = LNIL) ==> always (llist_eventually P) ll ==> Q ll`,
  DISCH_TAC THEN
  SUBGOAL_THEN `!ll:A llist. llist_eventually P ll ==> Q ll` ASSUME_TAC THENL
   [MATCH_MP_TAC llist_eventually_ind THEN ASM_SIMP_TAC[] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[LTL_THM; THE_DEF] THEN ASM_MESON_TAC[];
    GEN_TAC THEN DISCH_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [always_cases] THEN ASM_MESON_TAC[]]);;

let always_DROP = prove
 (`!ll:A llist. always P ll ==> always P (THE (LDROP k ll))`,
  SPEC_TAC(`k:num`,`k:num`) THEN INDUCT_TAC THEN
  REWRITE_TAC[LDROP_THM; THE_DEF] THEN GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [always_cases] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[LDROP_THM]);;

(* ------------------------------------------------------------------------- *)
(* The HOL4 [simp] and export_rewrites theorems of this file.                *)
(* ------------------------------------------------------------------------- *)

let _ = cake_add_simps
  [LCONS_NOT_NIL; LCONS_11; LHD_THM; LTL_THM; LHD_EQ_NONE; LTL_EQ_NONE;
   LNTH_THM; LNTH_LUNFOLD; LHD_LUNFOLD; LTL_LUNFOLD; LTAKE_THM;
   LTAKE_NIL_EQ_SOME; LTAKE_NIL_EQ_NONE; LMAP; LAPPEND; LAPPEND_EQ_LNIL;
   LFINITE_THM; LLENGTH_THM; LLENGTH_0; LFINITE_MAP; LFINITE_APPEND;
   llist_fromList_def; fromList_EQ_LNIL; LFINITE_fromList; LLENGTH_fromList;
   LDROP_THM; LDROP_1; exists_thm; every_thm; LPREFIX_LNIL; LPREFIX_REFL;
   LNTH_LMAP; LMAP_EQ_NIL; fromList_11; eventually_thm; always_thm];;
