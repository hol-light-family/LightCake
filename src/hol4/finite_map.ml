(* ========================================================================= *)
(* finite_map: port of HOL4 src/finite_maps/finite_mapScript.sml.           *)
(* A theory of finite maps (Graham Collins and Donald Syme, 1995; updated   *)
(* for HOL4 in 2002 by Michael Norrish).                                     *)
(*                                                                           *)
(* Notation: the type a |-> b is (A,B)fmap; f ' x is FAPPLY f x;             *)
(* f |+ (k,v) is FUPDATE f (k,v) (infix |+); f |++ l is FUPDATE_LIST f l     *)
(* (infix |++); fm \\ k is fdomsub fm k (infix \\); f o_f fm, f f_o_f g and  *)
(* f SUBMAP g are infixes; FUNION f g is prefix (HOL4 also has an infix).    *)
(* ========================================================================= *)

needs "hol4/vocab.ml";;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Definition of a finite map.  HOL4 represents (A,B)fmap by the functions  *)
(* A -> B + one with finite support; the port uses A -> B option.           *)
(* ------------------------------------------------------------------------- *)

let fmap_ISO_DEF =
  new_type_definition "fmap" ("fmap_ABS","fmap_REP")
   (prove(`?f:A->B option. FINITE {x | ~(f x = NONE)}`,
          EXISTS_TAC `\x:A. NONE:B option` THEN
          REWRITE_TAC[EMPTY_GSPEC; FINITE_EMPTY]));;

let fmap_REP_ABS = prove
 (`!r:A->B option. FINITE {x | ~(r x = NONE)} ==> fmap_REP (fmap_ABS r) = r`,
  MESON_TAC[fmap_ISO_DEF]);;

let fmap_REP_ABS_SUBSET = prove
 (`!(r:A->B option) s.
     FINITE s /\ (!a. ~(r a = NONE) ==> a IN s) ==> fmap_REP (fmap_ABS r) = r`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC fmap_REP_ABS THEN
  MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `s:A->bool` THEN
  ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM]);;

let fmap_REP_FINITE = prove
 (`!f:(A,B)fmap. FINITE {x | ~(fmap_REP f x = NONE)}`,
  REWRITE_TAC[CONJUNCT2 fmap_ISO_DEF; ETA_AX; CONJUNCT1 fmap_ISO_DEF]);;

let fmap_REP_11 = prove
 (`!f g:(A,B)fmap. fmap_REP f = fmap_REP g <=> f = g`,
  REPEAT GEN_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN
  DISCH_THEN(MP_TAC o AP_TERM `fmap_ABS:(A->B option)->(A,B)fmap`) THEN
  REWRITE_TAC[CONJUNCT1 fmap_ISO_DEF]);;

(* ------------------------------------------------------------------------- *)
(* Update, empty map, application and domain.                                *)
(* ------------------------------------------------------------------------- *)

let FUPDATE_DEF = new_definition
  `FUPDATE (f:(A,B)fmap) (x:A,y:B) =
     fmap_ABS (\a. if a = x then SOME y else fmap_REP f a)`;;

parse_as_infix("|+",(23,"left"));;
override_interface("|+",`FUPDATE:(A,B)fmap->A#B->(A,B)fmap`);;

let FEMPTY_DEF = new_definition
  `(FEMPTY:(A,B)fmap) = fmap_ABS (\a. NONE)`;;

(* HOL4 writes FAPPLY f x as f ' x *)

let FAPPLY_DEF = new_definition
  `FAPPLY (f:(A,B)fmap) (x:A) = THE (fmap_REP f x)`;;

let FDOM_DEF = new_definition
  `FDOM (f:(A,B)fmap) = {x | ~(fmap_REP f x = NONE)}`;;

let fmap_REP_FUPDATE = prove
 (`!(f:(A,B)fmap) x y.
     fmap_REP (f |+ (x,y)) = \a. if a = x then SOME y else fmap_REP f a`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FUPDATE_DEF] THEN
  MATCH_MP_TAC fmap_REP_ABS_SUBSET THEN
  EXISTS_TAC `(x:A) INSERT {a | ~(fmap_REP (f:(A,B)fmap) a = NONE)}` THEN
  REWRITE_TAC[FINITE_INSERT; fmap_REP_FINITE; IN_INSERT; IN_ELIM_THM] THEN
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

let fmap_REP_FEMPTY = prove
 (`fmap_REP (FEMPTY:(A,B)fmap) = \a. NONE`,
  REWRITE_TAC[FEMPTY_DEF] THEN MATCH_MP_TAC fmap_REP_ABS THEN
  REWRITE_TAC[EMPTY_GSPEC; FINITE_EMPTY]);;

(* HOL4 defines FLOOKUP after the union of maps; the port needs it first. *)

let FLOOKUP_DEF = new_definition
  `FLOOKUP (f:(A,B)fmap) x = if x IN FDOM f then SOME (FAPPLY f x) else NONE`;;

let FLOOKUP_REP = prove
 (`!f:(A,B)fmap. FLOOKUP f = fmap_REP f`,
  GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:A` THEN
  REWRITE_TAC[FLOOKUP_DEF; FDOM_DEF; FAPPLY_DEF; IN_ELIM_THM] THEN
  STRUCT_CASES_TAC(ISPEC `fmap_REP (f:(A,B)fmap) x` (cases "option")) THEN
  REWRITE_TAC[THE_DEF; option_DISTINCT]);;

(* ------------------------------------------------------------------------- *)
(* Everything in terms of FLOOKUP (the port's main proof tool).              *)
(* ------------------------------------------------------------------------- *)

let FDOM_FLOOKUP = prove
 (`!(f:(A,B)fmap) x. x IN FDOM f <=> ~(FLOOKUP f x = NONE)`,
  REWRITE_TAC[FDOM_DEF; FLOOKUP_REP; IN_ELIM_THM]);;

let FAPPLY_FLOOKUP = prove
 (`!(f:(A,B)fmap) x. FAPPLY f x = THE (FLOOKUP f x)`,
  REWRITE_TAC[FAPPLY_DEF; FLOOKUP_REP]);;

let FLOOKUP_EXT = prove
 (`!f1 f2:(A,B)fmap. (f1 = f2) <=> (FLOOKUP f1 = FLOOKUP f2)`,
  REWRITE_TAC[FLOOKUP_REP; fmap_REP_11]);;

let fmap_eq_flookup = prove
 (`!f1 f2:(A,B)fmap. (f1 = f2) <=> !x. FLOOKUP f1 x = FLOOKUP f2 x`,
  REWRITE_TAC[FLOOKUP_EXT; FUN_EQ_THM]);;

let FLOOKUP_EMPTY = prove
 (`!k:A. FLOOKUP (FEMPTY:(A,B)fmap) k = NONE`,
  REWRITE_TAC[FLOOKUP_REP; fmap_REP_FEMPTY]);;

let FLOOKUP_UPDATE = prove
 (`!(fm:(A,B)fmap) k1 v k2.
     FLOOKUP (fm |+ (k1,v)) k2 = if k1 = k2 then SOME v else FLOOKUP fm k2`,
  REWRITE_TAC[FLOOKUP_REP; fmap_REP_FUPDATE] THEN
  MESON_TAC[]);;

let flookup_thm = prove
 (`!(f:(A,B)fmap) x v.
     ((FLOOKUP f x = NONE) <=> ~(x IN FDOM f)) /\
     ((FLOOKUP f x = SOME v) <=> x IN FDOM f /\ (FAPPLY f x = v))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FLOOKUP_DEF] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT; option_INJ]);;

(* ------------------------------------------------------------------------- *)
(* Now some theorems.                                                        *)
(* ------------------------------------------------------------------------- *)

let FAPPLY_FUPDATE = prove
 (`!(f:(A,B)fmap) x y. FAPPLY (f |+ (x,y)) x = y`,
  REWRITE_TAC[FAPPLY_FLOOKUP; FLOOKUP_UPDATE; THE_DEF]);;

let NOT_EQ_FAPPLY = prove
 (`!(f:(A,B)fmap) a x y. ~(a = x) ==> (FAPPLY (f |+ (x,y)) a = FAPPLY f a)`,
  SIMP_TAC[FAPPLY_FLOOKUP; FLOOKUP_UPDATE] THEN MESON_TAC[]);;

let FUPDATE_COMMUTES = prove
 (`!(f:(A,B)fmap) a b c d.
     ~(a = c) ==> (f |+ (a,b) |+ (c,d) = f |+ (c,d) |+ (a,b))`,
  REWRITE_TAC[fmap_eq_flookup; FLOOKUP_UPDATE] THEN MESON_TAC[]);;

let FUPDATE_EQ = prove
 (`!(f:(A,B)fmap) a b c. f |+ (a,b) |+ (a,c) = f |+ (a,c)`,
  REWRITE_TAC[fmap_eq_flookup; FLOOKUP_UPDATE] THEN MESON_TAC[]);;

let FDOM_FEMPTY = prove
 (`FDOM (FEMPTY:(A,B)fmap) = {}`,
  REWRITE_TAC[EXTENSION; FDOM_FLOOKUP; FLOOKUP_EMPTY; NOT_IN_EMPTY]);;

let FDOM_FUPDATE = prove
 (`!(f:(A,B)fmap) a b. FDOM (f |+ (a,b)) = a INSERT FDOM f`,
  REWRITE_TAC[EXTENSION; FDOM_FLOOKUP; FLOOKUP_UPDATE; IN_INSERT] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[option_DISTINCT]);;

let FAPPLY_FUPDATE_THM = prove
 (`!(f:(A,B)fmap) a b x.
     FAPPLY (f |+ (a,b)) x = if x = a then b else FAPPLY f x`,
  REWRITE_TAC[FAPPLY_FLOOKUP; FLOOKUP_UPDATE] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[THE_DEF] THEN
  ASM_MESON_TAC[]);;

let NOT_EQ_FEMPTY_FUPDATE = prove
 (`!(f:(A,B)fmap) a b. ~(FEMPTY = f |+ (a,b))`,
  REWRITE_TAC[fmap_eq_flookup; FLOOKUP_UPDATE; FLOOKUP_EMPTY] THEN
  MESON_TAC[option_DISTINCT]);;

let FDOM_EQ_FDOM_FUPDATE = prove
 (`!(f:(A,B)fmap) x. x IN FDOM f ==> !y. FDOM (f |+ (x,y)) = FDOM f`,
  SIMP_TAC[FDOM_FUPDATE; SET_RULE `(x:A) IN s ==> x INSERT s = s`]);;

let FDOM_FINITE = prove
 (`!fm:(A,B)fmap. FINITE (FDOM fm)`,
  REWRITE_TAC[FDOM_DEF; fmap_REP_FINITE]);;

let FDOM_EQ_EMPTY = prove
 (`!f:(A,B)fmap. (FDOM f = {}) <=> (f = FEMPTY)`,
  REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; FDOM_FLOOKUP; fmap_eq_flookup;
              FLOOKUP_EMPTY]);;

let FDOM_EQ_EMPTY_SYM = prove
 (`!f:(A,B)fmap. ({} = FDOM f) <=> (f = FEMPTY)`,
  MESON_TAC[FDOM_EQ_EMPTY]);;

let FDOM_F_FEMPTY1 = prove
 (`!f:(A,B)fmap. (!a. ~(a IN FDOM f)) <=> (f = FEMPTY)`,
  REWRITE_TAC[GSYM FDOM_EQ_EMPTY; EXTENSION; NOT_IN_EMPTY]);;

(* deleting a key, before the theory has DRESTRICT and the \\ operator *)

let fmap_DELETE_EXISTS = prove
 (`!(f:(A,B)fmap) x.
     ?g. !a. FLOOKUP g a = if a = x then NONE else FLOOKUP f a`,
  REPEAT GEN_TAC THEN
  EXISTS_TAC `fmap_ABS (\a. if a = x then NONE else fmap_REP (f:(A,B)fmap) a)` THEN
  REWRITE_TAC[FLOOKUP_REP] THEN
  SUBGOAL_THEN
   `fmap_REP (fmap_ABS (\a. if a = x then NONE else fmap_REP (f:(A,B)fmap) a)) =
    (\a. if a = x then NONE else fmap_REP f a)` SUBST1_TAC THENL
   [MATCH_MP_TAC fmap_REP_ABS_SUBSET THEN
    EXISTS_TAC `FDOM (f:(A,B)fmap)` THEN
    REWRITE_TAC[FDOM_FINITE; FDOM_DEF; IN_ELIM_THM] THEN
    GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[];
    REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Induction.                                                                *)
(* ------------------------------------------------------------------------- *)

let fmap_INDUCT = prove
 (`!P. P FEMPTY /\
       (!f. P f ==> !x y. ~(x IN FDOM f) ==> P (f |+ (x,y)))
       ==> !f:(A,B)fmap. P f`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!s. FINITE s ==> !f:(A,B)fmap. FDOM f = s ==> P f`
   (fun th -> MESON_TAC[th; FDOM_FINITE]) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [ASM_MESON_TAC[FDOM_EQ_EMPTY]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `s:A->bool`] THEN STRIP_TAC THEN
  X_GEN_TAC `f:(A,B)fmap` THEN DISCH_TAC THEN
  X_CHOOSE_TAC `g:(A,B)fmap` (ISPECL [`f:(A,B)fmap`; `x:A`] fmap_DELETE_EXISTS) THEN
  SUBGOAL_THEN `FDOM (g:(A,B)fmap) = s` ASSUME_TAC THENL
   [UNDISCH_TAC `FDOM (f:(A,B)fmap) = x INSERT s` THEN
    ASM_REWRITE_TAC[EXTENSION; FDOM_FLOOKUP; IN_INSERT] THEN
    DISCH_TAC THEN X_GEN_TAC `a:A` THEN
    ASM_CASES_TAC `a:A = x` THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `f:(A,B)fmap = g |+ (x, FAPPLY f x)` SUBST1_TAC THENL
   [REWRITE_TAC[fmap_eq_flookup; FLOOKUP_UPDATE] THEN X_GEN_TAC `a:A` THEN
    ASM_CASES_TAC `x:A = a` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[flookup_thm; IN_INSERT];
    ASM_MESON_TAC[]]);;

let fmap_SIMPLE_INDUCT = prove
 (`!P:(A,B)fmap->bool.
     P FEMPTY /\ (!f. P f ==> !x y. P (f |+ (x,y))) ==> !f. P f`,
  GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC fmap_INDUCT THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Cardinality: the cardinality of the domain of the map.                   *)
(* ------------------------------------------------------------------------- *)

let FCARD_DEF = new_definition
  `FCARD (fm:(A,B)fmap) = CARD (FDOM fm)`;;

let FCARD_FEMPTY = prove
 (`FCARD (FEMPTY:(A,B)fmap) = 0`,
  REWRITE_TAC[FCARD_DEF; FDOM_FEMPTY; CARD_CLAUSES]);;

let FCARD_FUPDATE = prove
 (`!(fm:(A,B)fmap) a b.
     FCARD (fm |+ (a,b)) = if a IN FDOM fm then FCARD fm else 1 + FCARD fm`,
  SIMP_TAC[FCARD_DEF; FDOM_FUPDATE; CARD_CLAUSES; FDOM_FINITE] THEN ARITH_TAC);;

let FCARD_0_FEMPTY = prove
 (`!f:(A,B)fmap. (FCARD f = 0) <=> (f = FEMPTY)`,
  SIMP_TAC[FCARD_DEF; CARD_EQ_0; FDOM_FINITE; FDOM_EQ_EMPTY]);;

(* splitting a finite map on a key *)

let FM_PULL_APART = prove
 (`!(fm:(A,B)fmap) k.
     k IN FDOM fm ==> ?fm0 v. (fm = fm0 |+ (k,v)) /\ ~(k IN FDOM fm0)`,
  REPEAT STRIP_TAC THEN
  X_CHOOSE_TAC `g:(A,B)fmap` (ISPECL [`fm:(A,B)fmap`; `k:A`] fmap_DELETE_EXISTS) THEN
  MAP_EVERY EXISTS_TAC [`g:(A,B)fmap`; `FAPPLY (fm:(A,B)fmap) k`] THEN
  ASM_REWRITE_TAC[fmap_eq_flookup; FLOOKUP_UPDATE; FDOM_FLOOKUP] THEN
  X_GEN_TAC `a:A` THEN ASM_CASES_TAC `k:A = a` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[flookup_thm]);;

let FCARD_SUC = prove
 (`!(f:(A,B)fmap) n.
     (FCARD f = SUC n) <=>
     (?f' x y. ~(x IN FDOM f') /\ (FCARD f' = n) /\ (f = f' |+ (x,y)))`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `?x:A. x IN FDOM (f:(A,B)fmap)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[MEMBER_NOT_EMPTY; FCARD_0_FEMPTY; FDOM_EQ_EMPTY; NOT_SUC];
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP FM_PULL_APART) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`g:(A,B)fmap`; `v:B`] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`g:(A,B)fmap`; `x:A`; `v:B`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `FCARD (f:(A,B)fmap) = SUC n` THEN
    ASM_REWRITE_TAC[FCARD_FUPDATE] THEN ARITH_TAC;
    STRIP_TAC THEN ASM_REWRITE_TAC[FCARD_FUPDATE] THEN ARITH_TAC]);;

let NOT_FDOM_FAPPLY_FEMPTY = prove
 (`!(f:(A,B)fmap) x. ~(x IN FDOM f) ==> (FAPPLY f x = FAPPLY FEMPTY x)`,
  SIMP_TAC[FDOM_FLOOKUP; FAPPLY_FLOOKUP; FLOOKUP_EMPTY]);;

(* ------------------------------------------------------------------------- *)
(* Equality of finite maps.                                                  *)
(* ------------------------------------------------------------------------- *)

let fmap_EQ = prove
 (`!(f:(A,B)fmap) g. (FDOM f = FDOM g) /\ (FAPPLY f = FAPPLY g) <=> (f = g)`,
  REPEAT GEN_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[fmap_eq_flookup; FLOOKUP_DEF]);;

let fmap_EQ_THM = prove
 (`!(f:(A,B)fmap) g.
     (FDOM f = FDOM g) /\ (!x. x IN FDOM f ==> (FAPPLY f x = FAPPLY g x)) <=>
     (f = g)`,
  REPEAT GEN_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[fmap_eq_flookup; FLOOKUP_DEF] THEN X_GEN_TAC `x:A` THEN
  ASM_CASES_TAC `x IN FDOM (g:(A,B)fmap)` THEN ASM_MESON_TAC[]);;

(* it is more useful still if the main equality is the other way round *)

let fmap_EXT = prove
 (`!(f:(A,B)fmap) g.
     (f = g) <=>
     (FDOM f = FDOM g) /\ (!x. x IN FDOM f ==> (FAPPLY f x = FAPPLY g x))`,
  REWRITE_TAC[fmap_EQ_THM]);;

(* ------------------------------------------------------------------------- *)
(* Submaps.                                                                  *)
(* ------------------------------------------------------------------------- *)

let SUBMAP_DEF = new_definition
  `SUBMAP (f:(A,B)fmap) g <=>
     !x. x IN FDOM f ==> x IN FDOM g /\ (FAPPLY f x = FAPPLY g x)`;;

parse_as_infix("SUBMAP",(12,"right"));;

let SUBMAP_FEMPTY = prove
 (`!f:(A,B)fmap. FEMPTY SUBMAP f`,
  REWRITE_TAC[SUBMAP_DEF; FDOM_FEMPTY; NOT_IN_EMPTY]);;

let SUBMAP_REFL = prove
 (`!f:(A,B)fmap. f SUBMAP f`,
  REWRITE_TAC[SUBMAP_DEF]);;

let SUBMAP_ANTISYM = prove
 (`!(f:(A,B)fmap) g. (f SUBMAP g /\ g SUBMAP f) <=> (f = g)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[SUBMAP_DEF; GSYM fmap_EQ_THM; EXTENSION] THEN MESON_TAC[];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[SUBMAP_REFL]]);;

let SUBMAP_TRANS = prove
 (`!f g (h:(A,B)fmap). f SUBMAP g /\ g SUBMAP h ==> f SUBMAP h`,
  REWRITE_TAC[SUBMAP_DEF] THEN MESON_TAC[]);;

let SUBMAP_FUPDATE_EXTENDED = prove
 (`!(f:(A,B)fmap) k v. ~(k IN FDOM f) ==> f SUBMAP f |+ (k,v)`,
  REWRITE_TAC[SUBMAP_DEF; FDOM_FUPDATE; IN_INSERT; FAPPLY_FUPDATE_THM] THEN
  MESON_TAC[]);;

let EQ_FDOM_SUBMAP = prove
 (`!(f:(A,B)fmap) g. (f = g) <=> f SUBMAP g /\ (FDOM f = FDOM g)`,
  REWRITE_TAC[fmap_EXT; SUBMAP_DEF] THEN MESON_TAC[]);;

let SUBMAP_FUPDATE_EQN = prove
 (`!(f:(A,B)fmap) x y.
     f SUBMAP f |+ (x,y) <=>
     ~(x IN FDOM f) \/ (FAPPLY f x = y) /\ x IN FDOM f`,
  REWRITE_TAC[SUBMAP_DEF; FDOM_FUPDATE; IN_INSERT; FAPPLY_FUPDATE_THM] THEN
  MESON_TAC[]);;

let SUBMAP_FDOM_SUBSET = prove
 (`!f1 f2:(A,B)fmap. f1 SUBMAP f2 ==> FDOM f1 SUBSET FDOM f2`,
  REWRITE_TAC[SUBMAP_DEF; SUBSET] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Maps given by their lookup function (used to introduce the constants      *)
(* that HOL4 introduces by new_specification).                               *)
(* ------------------------------------------------------------------------- *)

let FLOOKUP_fmap_ABS = prove
 (`!(r:A->B option) s.
     FINITE s /\ (!a. ~(r a = NONE) ==> a IN s) ==> FLOOKUP (fmap_ABS r) = r`,
  REWRITE_TAC[FLOOKUP_REP; fmap_REP_ABS_SUBSET]);;

let FLOOKUP_EQ_FDOM_FAPPLY = prove
 (`!(g:(A,B)fmap) r.
     FLOOKUP g = r ==>
     FDOM g = {x | ~(r x = NONE)} /\ (!x. FAPPLY g x = THE (r x))`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; FDOM_FLOOKUP; FAPPLY_FLOOKUP]);;

let FMAPAUX_IN_COMPL = prove
 (`!(x:A) s. x IN COMPL s <=> ~(x IN s)`,
  REWRITE_TAC[COMPL_DEF; IN_DIFF; IN_UNIV]);;

(* ------------------------------------------------------------------------- *)
(* Restriction.                                                              *)
(* ------------------------------------------------------------------------- *)

let DRESTRICT_DEF = new_specification ["DRESTRICT"]
 (prove
   (`?DRESTRICT. !(f:(A,B)fmap) r.
       (FDOM (DRESTRICT f r) = FDOM f INTER r) /\
       (!x. FAPPLY (DRESTRICT f r) x =
            if x IN FDOM f INTER r then FAPPLY f x else FAPPLY FEMPTY x)`,
    EXISTS_TAC `\(f:(A,B)fmap) (r:A->bool).
                  fmap_ABS (\x. if x IN r then FLOOKUP f x else NONE)` THEN
    MAP_EVERY X_GEN_TAC [`f:(A,B)fmap`; `r:A->bool`] THEN
    SUBGOAL_THEN
     `FLOOKUP (fmap_ABS (\x. if x IN r then FLOOKUP (f:(A,B)fmap) x else NONE)) =
      (\x. if x IN r then FLOOKUP f x else NONE)` ASSUME_TAC THENL
     [MATCH_MP_TAC FLOOKUP_fmap_ABS THEN EXISTS_TAC `FDOM (f:(A,B)fmap)` THEN
      REWRITE_TAC[FDOM_FINITE; FDOM_FLOOKUP] THEN MESON_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[EXTENSION; FDOM_FLOOKUP; FAPPLY_FLOOKUP; IN_INTER;
                    FLOOKUP_EMPTY] THEN
    CONJ_TAC THEN X_GEN_TAC `x:A` THEN ASM_CASES_TAC `(x:A) IN r` THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `FLOOKUP (f:(A,B)fmap) x = NONE` THEN ASM_REWRITE_TAC[]));;

let FLOOKUP_DRESTRICT = prove
 (`!(fm:(A,B)fmap) s k.
     FLOOKUP (DRESTRICT fm s) k = if k IN s then FLOOKUP fm k else NONE`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FLOOKUP_DEF; DRESTRICT_DEF; IN_INTER] THEN
  MESON_TAC[]);;

let DRESTRICT_FEMPTY = prove
 (`!r. DRESTRICT (FEMPTY:(A,B)fmap) r = FEMPTY`,
  REWRITE_TAC[fmap_eq_flookup; FLOOKUP_DRESTRICT; FLOOKUP_EMPTY; COND_ID]);;

let DRESTRICT_FUPDATE = prove
 (`!(f:(A,B)fmap) r x y.
     DRESTRICT (f |+ (x,y)) r =
     if x IN r then DRESTRICT f r |+ (x,y) else DRESTRICT f r`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[fmap_eq_flookup; FLOOKUP_DRESTRICT; FLOOKUP_UPDATE] THEN
  ASM_MESON_TAC[]);;

let DRESTRICT_EQ_FEMPTY = prove
 (`!(m:(A,B)fmap) s. DISJOINT s (FDOM m) <=> DRESTRICT m s = FEMPTY`,
  REWRITE_TAC[fmap_eq_flookup; FLOOKUP_DRESTRICT; FLOOKUP_EMPTY; DISJOINT;
              EXTENSION; IN_INTER; NOT_IN_EMPTY; FDOM_FLOOKUP] THEN
  MESON_TAC[]);;

let STRONG_DRESTRICT_FUPDATE = prove
 (`!(f:(A,B)fmap) r x y.
     x IN r ==> (DRESTRICT (f |+ (x,y)) r = DRESTRICT f (r DELETE x) |+ (x,y))`,
  REWRITE_TAC[fmap_eq_flookup; FLOOKUP_DRESTRICT; FLOOKUP_UPDATE; IN_DELETE] THEN
  MESON_TAC[]);;

let FDOM_DRESTRICT = prove
 (`!(f:(A,B)fmap) r (x:A). FDOM (DRESTRICT f r) = FDOM f INTER r`,
  REWRITE_TAC[DRESTRICT_DEF]);;

let NOT_FDOM_DRESTRICT = prove
 (`!(f:(A,B)fmap) x. ~(x IN FDOM f) ==> (DRESTRICT f (COMPL {x}) = f)`,
  REWRITE_TAC[fmap_eq_flookup; FLOOKUP_DRESTRICT; FMAPAUX_IN_COMPL; IN_SING;
              FDOM_FLOOKUP] THEN
  MESON_TAC[]);;

let DRESTRICT_SUBMAP = prove
 (`!(f:(A,B)fmap) r. (DRESTRICT f r) SUBMAP f`,
  REWRITE_TAC[SUBMAP_DEF; DRESTRICT_DEF; IN_INTER] THEN MESON_TAC[]);;

let DRESTRICT_DRESTRICT = prove
 (`!(f:(A,B)fmap) P Q. DRESTRICT (DRESTRICT f P) Q = DRESTRICT f (P INTER Q)`,
  REWRITE_TAC[fmap_eq_flookup; FLOOKUP_DRESTRICT; IN_INTER] THEN MESON_TAC[]);;

let DRESTRICT_IS_FEMPTY = prove
 (`!f:(A,B)fmap. DRESTRICT f {} = FEMPTY`,
  REWRITE_TAC[fmap_eq_flookup; FLOOKUP_DRESTRICT; FLOOKUP_EMPTY; NOT_IN_EMPTY]);;

let FUPDATE_DRESTRICT = prove
 (`!(f:(A,B)fmap) x y. f |+ (x,y) = DRESTRICT f (COMPL {x}) |+ (x,y)`,
  REWRITE_TAC[fmap_eq_flookup; FLOOKUP_DRESTRICT; FLOOKUP_UPDATE;
              FMAPAUX_IN_COMPL; IN_SING] THEN
  MESON_TAC[]);;

let STRONG_DRESTRICT_FUPDATE_THM = prove
 (`!(f:(A,B)fmap) r x y.
     DRESTRICT (f |+ (x,y)) r =
     if x IN r then DRESTRICT f (COMPL {x} INTER r) |+ (x,y)
     else DRESTRICT f (COMPL {x} INTER r)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[fmap_eq_flookup; FLOOKUP_DRESTRICT; FLOOKUP_UPDATE;
              FMAPAUX_IN_COMPL; IN_SING; IN_INTER] THEN
  ASM_MESON_TAC[]);;

let DRESTRICT_UNIV = prove
 (`!f:(A,B)fmap. DRESTRICT f UNIV = f`,
  REWRITE_TAC[fmap_eq_flookup; FLOOKUP_DRESTRICT; IN_UNIV]);;

let SUBMAP_DRESTRICT = prove
 (`!(f:(A,B)fmap) P. DRESTRICT f P SUBMAP f`,
  REWRITE_TAC[DRESTRICT_SUBMAP]);;

let SUBMAP_DRESTRICT_MONOTONE = prove
 (`!(f1:(A,B)fmap) f2 s1 s2.
     f1 SUBMAP f2 /\ s1 SUBSET s2 ==> DRESTRICT f1 s1 SUBMAP DRESTRICT f2 s2`,
  REWRITE_TAC[SUBMAP_DEF; DRESTRICT_DEF; SUBSET; IN_INTER] THEN MESON_TAC[]);;

let DRESTRICT_EQ_DRESTRICT = prove
 (`!(f1:(A,B)fmap) f2 s1 s2.
     (DRESTRICT f1 s1 = DRESTRICT f2 s2) <=>
     (DRESTRICT f1 s1 SUBMAP f2 /\ DRESTRICT f2 s2 SUBMAP f1 /\
      (s1 INTER FDOM f1 = s2 INTER FDOM f2))`,
  REWRITE_TAC[GSYM fmap_EQ_THM; DRESTRICT_DEF; SUBMAP_DEF; EXTENSION;
              IN_INTER] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Union of finite maps.                                                     *)
(* ------------------------------------------------------------------------- *)

let FUNION_DEF = new_specification ["FUNION"]
 (prove
   (`?FUNION. !(f:(A,B)fmap) g.
       (FDOM (FUNION f g) = FDOM f UNION FDOM g) /\
       (!x. FAPPLY (FUNION f g) x =
            if x IN FDOM f then FAPPLY f x else FAPPLY g x)`,
    EXISTS_TAC `\(f:(A,B)fmap) (g:(A,B)fmap).
                  fmap_ABS (\x. if x IN FDOM f then FLOOKUP f x else FLOOKUP g x)` THEN
    MAP_EVERY X_GEN_TAC [`f:(A,B)fmap`; `g:(A,B)fmap`] THEN
    SUBGOAL_THEN
     `FLOOKUP (fmap_ABS (\x. if x IN FDOM f then FLOOKUP (f:(A,B)fmap) x
                             else FLOOKUP g x)) =
      (\x. if x IN FDOM f then FLOOKUP f x else FLOOKUP g x)` ASSUME_TAC THENL
     [MATCH_MP_TAC FLOOKUP_fmap_ABS THEN
      EXISTS_TAC `FDOM (f:(A,B)fmap) UNION FDOM (g:(A,B)fmap)` THEN
      REWRITE_TAC[FINITE_UNION; FDOM_FINITE; IN_UNION] THEN
      REWRITE_TAC[FDOM_FLOOKUP] THEN MESON_TAC[];
      ALL_TAC] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP FLOOKUP_EQ_FDOM_FAPPLY) THEN
    ASM_REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_UNION] THEN
    REWRITE_TAC[FDOM_FLOOKUP; FAPPLY_FLOOKUP] THEN
    CONJ_TAC THEN X_GEN_TAC `x:A` THEN
    ASM_CASES_TAC `FLOOKUP (f:(A,B)fmap) x = NONE` THEN ASM_REWRITE_TAC[]));;

let FDOM_FUNION = prove
 (`!(f:(A,B)fmap) g. FDOM (FUNION f g) = FDOM f UNION FDOM g`,
  REWRITE_TAC[FUNION_DEF]);;

let FLOOKUP_FUNION = prove
 (`!(f1:(A,B)fmap) f2 k.
     FLOOKUP (FUNION f1 f2) k =
     option_CASE (FLOOKUP f1 k) (FLOOKUP f2 k) (\v. SOME v)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[FLOOKUP_DEF; FUNION_DEF; IN_UNION] THEN
  ASM_CASES_TAC `(k:A) IN FDOM (f1:(A,B)fmap)` THEN ASM_REWRITE_TAC[option_CASE]);;

let FUNION_FEMPTY_1 = prove
 (`!g:(A,B)fmap. FUNION FEMPTY g = g`,
  REWRITE_TAC[fmap_eq_flookup; FLOOKUP_FUNION; FLOOKUP_EMPTY; option_CASE]);;

let FUNION_FEMPTY_2 = prove
 (`!f:(A,B)fmap. FUNION f FEMPTY = f`,
  REWRITE_TAC[fmap_eq_flookup; FLOOKUP_FUNION; FLOOKUP_EMPTY] THEN
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `FLOOKUP (f:(A,B)fmap) x` (cases "option")) THEN
  REWRITE_TAC[option_CASE]);;

let FUNION_FUPDATE_1 = prove
 (`!(f:(A,B)fmap) g x y. FUNION (f |+ (x,y)) g = FUNION f g |+ (x,y)`,
  REWRITE_TAC[fmap_eq_flookup; FLOOKUP_FUNION; FLOOKUP_UPDATE] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[option_CASE]);;

let FUNION_FUPDATE_2 = prove
 (`!(f:(A,B)fmap) g x y.
     FUNION f (g |+ (x,y)) =
     if x IN FDOM f then FUNION f g else FUNION f g |+ (x,y)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[fmap_eq_flookup; FLOOKUP_FUNION; FLOOKUP_UPDATE] THEN
  X_GEN_TAC `a:A` THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[FDOM_FLOOKUP] THEN
  ASM_CASES_TAC `x:A = a` THEN ASM_REWRITE_TAC[] THEN
  STRUCT_CASES_TAC(ISPEC `FLOOKUP (f:(A,B)fmap) a` (cases "option")) THEN
  REWRITE_TAC[option_CASE; option_DISTINCT]);;

let FUNION_IDEMPOT = prove
 (`!fm:(A,B)fmap. FUNION fm fm = fm`,
  REWRITE_TAC[fmap_eq_flookup; FLOOKUP_FUNION] THEN REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `FLOOKUP (fm:(A,B)fmap) x` (cases "option")) THEN
  REWRITE_TAC[option_CASE]);;

(* ------------------------------------------------------------------------- *)
(* Merging of finite maps (Thomas Tuerk, 2009).                              *)
(* ------------------------------------------------------------------------- *)

let FMERGE_DEF = new_specification ["FMERGE"]
 (prove
   (`?FMERGE. !(m:B->B->B) (f:(A,B)fmap) g.
       (FDOM (FMERGE m f g) = FDOM f UNION FDOM g) /\
       (!x. FAPPLY (FMERGE m f g) x =
            if ~(x IN FDOM f) then FAPPLY g x
            else if ~(x IN FDOM g) then FAPPLY f x
            else m (FAPPLY f x) (FAPPLY g x))`,
    EXISTS_TAC `\(m:B->B->B) (f:(A,B)fmap) (g:(A,B)fmap).
                  fmap_ABS (\x. if ~(x IN FDOM f) then FLOOKUP g x
                                else if ~(x IN FDOM g) then FLOOKUP f x
                                else SOME (m (FAPPLY f x) (FAPPLY g x)))` THEN
    MAP_EVERY X_GEN_TAC [`m:B->B->B`; `f:(A,B)fmap`; `g:(A,B)fmap`] THEN
    SUBGOAL_THEN
     `FLOOKUP (fmap_ABS (\x. if ~(x IN FDOM f) then FLOOKUP g x
                             else if ~(x IN FDOM g) then FLOOKUP (f:(A,B)fmap) x
                             else SOME ((m:B->B->B) (FAPPLY f x) (FAPPLY g x)))) =
      (\x. if ~(x IN FDOM f) then FLOOKUP g x
           else if ~(x IN FDOM g) then FLOOKUP f x
           else SOME (m (FAPPLY f x) (FAPPLY g x)))` ASSUME_TAC THENL
     [MATCH_MP_TAC FLOOKUP_fmap_ABS THEN
      EXISTS_TAC `FDOM (f:(A,B)fmap) UNION FDOM (g:(A,B)fmap)` THEN
      REWRITE_TAC[FINITE_UNION; FDOM_FINITE; IN_UNION] THEN
      REWRITE_TAC[FDOM_FLOOKUP] THEN MESON_TAC[option_DISTINCT];
      ALL_TAC] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP FLOOKUP_EQ_FDOM_FAPPLY) THEN
    ASM_REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_UNION] THEN
    REWRITE_TAC[FDOM_FLOOKUP; FAPPLY_FLOOKUP] THEN
    CONJ_TAC THEN X_GEN_TAC `x:A` THEN
    ASM_CASES_TAC `FLOOKUP (f:(A,B)fmap) x = NONE` THEN
    ASM_CASES_TAC `FLOOKUP (g:(A,B)fmap) x = NONE` THEN
    ASM_REWRITE_TAC[option_DISTINCT; THE_DEF]));;

let FDOM_FMERGE = prove
 (`!(m:B->B->B) (f:(A,B)fmap) g. FDOM (FMERGE m f g) = FDOM f UNION FDOM g`,
  REWRITE_TAC[FMERGE_DEF]);;

let FLOOKUP_FMERGE = prove
 (`!(f:B->B->B) (m1:(A,B)fmap) m2 k.
     FLOOKUP (FMERGE f m1 m2) k =
     option_CASE (FLOOKUP m1 k) (FLOOKUP m2 k)
       (\v1. option_CASE (FLOOKUP m2 k) (SOME v1) (\v2. SOME (f v1 v2)))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[FLOOKUP_DEF; FMERGE_DEF; IN_UNION] THEN
  ASM_CASES_TAC `(k:A) IN FDOM (m1:(A,B)fmap)` THEN
  ASM_CASES_TAC `(k:A) IN FDOM (m2:(A,B)fmap)` THEN
  ASM_REWRITE_TAC[option_CASE]);;

(* ------------------------------------------------------------------------- *)
(* FLOOKUP (the rest of HOL4's block "assoc for finite maps").               *)
(* ------------------------------------------------------------------------- *)

let FLOOKUP_UPDATE_SAME = prove
 (`!(fm:(A,B)fmap) a b. FLOOKUP (fm |+ (a,b)) a = SOME b`,
  REWRITE_TAC[FLOOKUP_UPDATE]);;

let FLOOKUP_UPDATE_DIFF = prove
 (`!(fm:(A,B)fmap) a b x.
     ~(a = x) ==> (FLOOKUP (fm |+ (a,b)) x = FLOOKUP fm x)`,
  SIMP_TAC[FLOOKUP_UPDATE]);;

let FLOOKUP_SUBMAP = prove
 (`!(f:(A,B)fmap) g k v.
     f SUBMAP g /\ (FLOOKUP f k = SOME v) ==> (FLOOKUP g k = SOME v)`,
  REWRITE_TAC[SUBMAP_DEF; flookup_thm] THEN MESON_TAC[]);;

let SUBMAP_FLOOKUP_EQN = prove
 (`!(f:(A,B)fmap) g.
     f SUBMAP g <=> !x y. (FLOOKUP f x = SOME y) ==> (FLOOKUP g x = SOME y)`,
  REWRITE_TAC[SUBMAP_DEF; flookup_thm] THEN MESON_TAC[]);;

let SUBMAP_FUPDATE_FLOOKUP = prove
 (`!(f:(A,B)fmap) x y.
     f SUBMAP (f |+ (x,y)) <=> (FLOOKUP f x = NONE) \/ (FLOOKUP f x = SOME y)`,
  REWRITE_TAC[SUBMAP_FUPDATE_EQN; flookup_thm] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Universal quantifier on finite maps.                                      *)
(* ------------------------------------------------------------------------- *)

let FEVERY_DEF = new_definition
  `FEVERY (P:A#B->bool) (f:(A,B)fmap) <=>
     !x. x IN FDOM f ==> P (x, FAPPLY f x)`;;

let FEVERY_FEMPTY = prove
 (`!P:A#B->bool. FEVERY P FEMPTY`,
  REWRITE_TAC[FEVERY_DEF; FDOM_FEMPTY; NOT_IN_EMPTY]);;

let FEVERY_FUPDATE = prove
 (`!(P:A#B->bool) (f:(A,B)fmap) x y.
     FEVERY P (f |+ (x,y)) <=> P (x,y) /\ FEVERY P (DRESTRICT f (COMPL {x}))`,
  REWRITE_TAC[FEVERY_DEF; FDOM_FUPDATE; FAPPLY_FUPDATE_THM; DRESTRICT_DEF;
              IN_INSERT; IN_INTER; FMAPAUX_IN_COMPL; IN_SING] THEN
  MESON_TAC[]);;

let FEVERY_FLOOKUP = prove
 (`!(P:A#B->bool) (f:(A,B)fmap) k v.
     FEVERY P f /\ (FLOOKUP f k = SOME v) ==> P (k,v)`,
  REWRITE_TAC[FEVERY_DEF; flookup_thm] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Composition of finite maps.                                               *)
(* ------------------------------------------------------------------------- *)

let f_o_f_DEF = new_specification ["f_o_f"]
 (prove
   (`?fof. !(f:(B,C)fmap) (g:(A,B)fmap).
       (FDOM (fof f g) = FDOM g INTER {x | FAPPLY g x IN FDOM f}) /\
       (!x. x IN FDOM (fof f g) ==> (FAPPLY (fof f g) x = FAPPLY f (FAPPLY g x)))`,
    EXISTS_TAC `\(f:(B,C)fmap) (g:(A,B)fmap).
                  fmap_ABS (\x. if x IN FDOM g then FLOOKUP f (FAPPLY g x)
                                else NONE)` THEN
    MAP_EVERY X_GEN_TAC [`f:(B,C)fmap`; `g:(A,B)fmap`] THEN
    SUBGOAL_THEN
     `FLOOKUP (fmap_ABS (\x. if x IN FDOM (g:(A,B)fmap)
                             then FLOOKUP (f:(B,C)fmap) (FAPPLY g x) else NONE)) =
      (\x. if x IN FDOM g then FLOOKUP f (FAPPLY g x) else NONE)` ASSUME_TAC THENL
     [MATCH_MP_TAC FLOOKUP_fmap_ABS THEN EXISTS_TAC `FDOM (g:(A,B)fmap)` THEN
      REWRITE_TAC[FDOM_FINITE] THEN MESON_TAC[];
      ALL_TAC] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP FLOOKUP_EQ_FDOM_FAPPLY) THEN
    ASM_REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER] THEN
    CONJ_TAC THEN X_GEN_TAC `x:A` THEN ASM_CASES_TAC `x IN FDOM (g:(A,B)fmap)` THEN
    ASM_REWRITE_TAC[FDOM_FLOOKUP; FAPPLY_FLOOKUP]));;

parse_as_infix("f_o_f",(26,"right"));;

let f_o_f_FEMPTY_1 = prove
 (`!f:(A,B)fmap. (FEMPTY:(B,C)fmap) f_o_f f = FEMPTY`,
  REWRITE_TAC[GSYM fmap_EQ_THM; f_o_f_DEF; FDOM_FEMPTY; EXTENSION; IN_INTER;
              IN_ELIM_THM; NOT_IN_EMPTY]);;

let f_o_f_FEMPTY_2 = prove
 (`!f:(B,C)fmap. f f_o_f (FEMPTY:(A,B)fmap) = FEMPTY`,
  REWRITE_TAC[GSYM fmap_EQ_THM; f_o_f_DEF; FDOM_FEMPTY; INTER_EMPTY;
              NOT_IN_EMPTY]);;

(* ------------------------------------------------------------------------- *)
(* Mapping a function over the values: f o_f fm (HOL4 infix, kept).         *)
(* ------------------------------------------------------------------------- *)

let o_f_DEF = new_specification ["o_f"]
 (prove
   (`?of. !(f:B->C) (g:(A,B)fmap).
       (FDOM (of f g) = FDOM g) /\
       (!x. x IN FDOM (of f g) ==> (FAPPLY (of f g) x = f (FAPPLY g x)))`,
    EXISTS_TAC `\(f:B->C) (g:(A,B)fmap).
                  fmap_ABS (\x. if x IN FDOM g then SOME (f (FAPPLY g x))
                                else NONE)` THEN
    MAP_EVERY X_GEN_TAC [`f:B->C`; `g:(A,B)fmap`] THEN
    SUBGOAL_THEN
     `FLOOKUP (fmap_ABS (\x. if x IN FDOM (g:(A,B)fmap)
                             then SOME ((f:B->C) (FAPPLY g x)) else NONE)) =
      (\x. if x IN FDOM g then SOME (f (FAPPLY g x)) else NONE)` ASSUME_TAC THENL
     [MATCH_MP_TAC FLOOKUP_fmap_ABS THEN EXISTS_TAC `FDOM (g:(A,B)fmap)` THEN
      REWRITE_TAC[FDOM_FINITE] THEN MESON_TAC[];
      ALL_TAC] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP FLOOKUP_EQ_FDOM_FAPPLY) THEN
    ASM_REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
    CONJ_TAC THEN X_GEN_TAC `x:A` THEN ASM_CASES_TAC `x IN FDOM (g:(A,B)fmap)` THEN
    ASM_REWRITE_TAC[option_DISTINCT; THE_DEF]));;

parse_as_infix("o_f",(26,"right"));;

let o_f_FDOM = prove
 (`!(f:B->C) (g:(A,B)fmap). FDOM g = FDOM (f o_f g)`,
  REWRITE_TAC[o_f_DEF]);;

let FDOM_o_f = prove
 (`!(f:B->C) (g:(A,B)fmap). FDOM (f o_f g) = FDOM g`,
  REWRITE_TAC[o_f_DEF]);;

let o_f_FAPPLY = prove
 (`!(f:B->C) (g:(A,B)fmap) x.
     x IN FDOM g ==> (FAPPLY (f o_f g) x = f (FAPPLY g x))`,
  SIMP_TAC[o_f_DEF]);;

let FLOOKUP_o_f = prove
 (`!(f:B->C) (fm:(A,B)fmap) k.
     FLOOKUP (f o_f fm) k = option_CASE (FLOOKUP fm k) NONE (\v. SOME (f v))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FLOOKUP_DEF; FDOM_o_f] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[option_CASE; o_f_FAPPLY]);;

let o_f_FEMPTY = prove
 (`!f:B->C. f o_f (FEMPTY:(A,B)fmap) = FEMPTY`,
  REWRITE_TAC[fmap_eq_flookup; FLOOKUP_o_f; FLOOKUP_EMPTY; option_CASE]);;

let o_f_id = prove
 (`!m:(A,B)fmap. (\x. x) o_f m = m`,
  REWRITE_TAC[fmap_eq_flookup; FLOOKUP_o_f] THEN REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `FLOOKUP (m:(A,B)fmap) x` (cases "option")) THEN
  REWRITE_TAC[option_CASE]);;

let FEVERY_o_f = prove
 (`!(m:(A,B)fmap) (P:A#C->bool) (f:B->C).
     FEVERY P (f o_f m) <=> FEVERY (\x. P (FST x, f (SND x))) m`,
  SIMP_TAC[FEVERY_DEF; o_f_DEF]);;

let o_f_o_f = prove
 (`!(f:C->D) (g:B->C) (h:(A,B)fmap). f o_f (g o_f h) = (f o g) o_f h`,
  REWRITE_TAC[fmap_eq_flookup; FLOOKUP_o_f] THEN REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `FLOOKUP (h:(A,B)fmap) x` (cases "option")) THEN
  REWRITE_TAC[option_CASE; o_THM]);;

(* ------------------------------------------------------------------------- *)
(* Range of a finite map.                                                    *)
(* ------------------------------------------------------------------------- *)

let FRANGE_DEF = new_definition
  `FRANGE (f:(A,B)fmap) = {y | ?x. x IN FDOM f /\ (FAPPLY f x = y)}`;;

let FRANGE_FEMPTY = prove
 (`FRANGE (FEMPTY:(A,B)fmap) = {}`,
  REWRITE_TAC[FRANGE_DEF; FDOM_FEMPTY; NOT_IN_EMPTY; EMPTY_GSPEC]);;

let FRANGE_FUPDATE = prove
 (`!(f:(A,B)fmap) x y.
     FRANGE (f |+ (x,y)) = y INSERT FRANGE (DRESTRICT f (COMPL {x}))`,
  REWRITE_TAC[FRANGE_DEF; FDOM_FUPDATE; DRESTRICT_DEF; EXTENSION; IN_ELIM_THM;
              IN_INSERT; IN_INTER; FMAPAUX_IN_COMPL; IN_SING;
              FAPPLY_FUPDATE_THM] THEN
  MESON_TAC[]);;

let SUBMAP_FRANGE = prove
 (`!(f:(A,B)fmap) g. f SUBMAP g ==> FRANGE f SUBSET FRANGE g`,
  REWRITE_TAC[SUBMAP_DEF; FRANGE_DEF; SUBSET; IN_ELIM_THM] THEN MESON_TAC[]);;

let FINITE_FRANGE = prove
 (`!fm:(A,B)fmap. FINITE (FRANGE fm)`,
  GEN_TAC THEN
  SUBGOAL_THEN `FRANGE (fm:(A,B)fmap) = IMAGE (FAPPLY fm) (FDOM fm)` SUBST1_TAC THENL
   [REWRITE_TAC[FRANGE_DEF; EXTENSION; IN_ELIM_THM; IN_IMAGE] THEN MESON_TAC[];
    SIMP_TAC[FINITE_IMAGE; FDOM_FINITE]]);;

let o_f_FRANGE = prove
 (`!(f:B->C) (g:(A,B)fmap) x. x IN FRANGE g ==> f x IN FRANGE (f o_f g)`,
  REWRITE_TAC[FRANGE_DEF; IN_ELIM_THM; FDOM_o_f] THEN MESON_TAC[o_f_FAPPLY]);;

let FRANGE_FLOOKUP = prove
 (`!(f:(A,B)fmap) v. v IN FRANGE f <=> ?k. FLOOKUP f k = SOME v`,
  REWRITE_TAC[FRANGE_DEF; IN_ELIM_THM; flookup_thm]);;

let FRANGE_FUNION = prove
 (`!(fm1:(A,B)fmap) fm2.
     DISJOINT (FDOM fm1) (FDOM fm2) ==>
     (FRANGE (FUNION fm1 fm2) = FRANGE fm1 UNION FRANGE fm2)`,
  REWRITE_TAC[FRANGE_DEF; FUNION_DEF; EXTENSION; IN_ELIM_THM; IN_UNION;
              DISJOINT; IN_INTER; NOT_IN_EMPTY] THEN
  MESON_TAC[]);;

let o_f_cong = prove
 (`!(f:B->C) (fm:(A,B)fmap) f' fm'.
     (fm = fm') /\ (!v. v IN FRANGE fm ==> (f v = f' v)) ==>
     (f o_f fm = f' o_f fm')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FRANGE_DEF; IN_ELIM_THM] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  ASM_SIMP_TAC[fmap_EXT; FDOM_o_f; o_f_FAPPLY] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Functions as finite maps.                                                 *)
(* ------------------------------------------------------------------------- *)

let FUN_FMAP_DEF = new_specification ["FUN_FMAP"]
 (prove
   (`?FUN_FMAP. !(f:A->B) P.
       FINITE P ==>
       (FDOM (FUN_FMAP f P) = P) /\
       (!x. x IN P ==> (FAPPLY (FUN_FMAP f P) x = f x))`,
    EXISTS_TAC `\(f:A->B) (P:A->bool).
                  fmap_ABS (\x. if x IN P then SOME (f x) else NONE)` THEN
    MAP_EVERY X_GEN_TAC [`f:A->B`; `P:A->bool`] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `FLOOKUP (fmap_ABS (\x. if x IN P then SOME ((f:A->B) x) else NONE)) =
      (\x. if x IN P then SOME (f x) else NONE)` ASSUME_TAC THENL
     [MATCH_MP_TAC FLOOKUP_fmap_ABS THEN EXISTS_TAC `P:A->bool` THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[];
      ALL_TAC] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP FLOOKUP_EQ_FDOM_FAPPLY) THEN
    ASM_REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
    CONJ_TAC THEN X_GEN_TAC `x:A` THEN ASM_CASES_TAC `(x:A) IN P` THEN
    ASM_REWRITE_TAC[option_DISTINCT; THE_DEF]));;

let FLOOKUP_FUN_FMAP = prove
 (`!(f:A->B) P k.
     FINITE P ==>
     (FLOOKUP (FUN_FMAP f P) k = if k IN P then SOME (f k) else NONE)`,
  SIMP_TAC[FLOOKUP_DEF; FUN_FMAP_DEF]);;

let FUN_FMAP_EMPTY = prove
 (`!f:A->B. FUN_FMAP f {} = FEMPTY`,
  SIMP_TAC[fmap_eq_flookup; FLOOKUP_FUN_FMAP; FINITE_EMPTY; NOT_IN_EMPTY;
           FLOOKUP_EMPTY]);;

let FRANGE_FMAP = prove
 (`!(f:A->B) P. FINITE P ==> (FRANGE (FUN_FMAP f P) = IMAGE f P)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:A->B`; `P:A->bool`] FUN_FMAP_DEF) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[FRANGE_DEF; EXTENSION; IN_ELIM_THM; IN_IMAGE] THEN
  ASM_MESON_TAC[]);;

let FDOM_FMAP = prove
 (`!(f:A->B) s. FINITE s ==> (FDOM (FUN_FMAP f s) = s)`,
  SIMP_TAC[FUN_FMAP_DEF]);;

let FUN_FMAP_INSERT = prove
 (`!(f:A->B) e s.
     FINITE s /\ ~(e IN s) ==>
     FUN_FMAP f (e INSERT s) = FUN_FMAP f s |+ (e,f e)`,
  SIMP_TAC[fmap_eq_flookup; FLOOKUP_FUN_FMAP; FINITE_INSERT; FLOOKUP_UPDATE;
           IN_INSERT] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Domain subtraction (at a single point): fdomsub fm k, written fm \\ k.    *)
(* ------------------------------------------------------------------------- *)

let fmap_domsub = new_definition
  `fdomsub (fm:(A,B)fmap) (k:A) = DRESTRICT fm (COMPL {k})`;;

parse_as_infix("\\\\",(23,"left"));;
override_interface("\\\\",`fdomsub:(A,B)fmap->A->(A,B)fmap`);;

let DOMSUB_FLOOKUP_THM = prove
 (`!(fm:(A,B)fmap) k1 k2.
     FLOOKUP (fm \\ k1) k2 = if k1 = k2 then NONE else FLOOKUP fm k2`,
  REWRITE_TAC[fmap_domsub; FLOOKUP_DRESTRICT; FMAPAUX_IN_COMPL; IN_SING] THEN
  MESON_TAC[]);;

let DOMSUB_FEMPTY = prove
 (`!k:A. (FEMPTY:(A,B)fmap) \\ k = FEMPTY`,
  REWRITE_TAC[fmap_eq_flookup; DOMSUB_FLOOKUP_THM; FLOOKUP_EMPTY; COND_ID]);;

let DOMSUB_FUPDATE = prove
 (`!(fm:(A,B)fmap) k v. fm |+ (k,v) \\ k = fm \\ k`,
  REWRITE_TAC[fmap_eq_flookup; DOMSUB_FLOOKUP_THM; FLOOKUP_UPDATE] THEN
  MESON_TAC[]);;

let DOMSUB_FUPDATE_NEQ = prove
 (`!(fm:(A,B)fmap) k1 k2 v.
     ~(k1 = k2) ==> (fm |+ (k1,v) \\ k2 = fm \\ k2 |+ (k1,v))`,
  REWRITE_TAC[fmap_eq_flookup; DOMSUB_FLOOKUP_THM; FLOOKUP_UPDATE] THEN
  MESON_TAC[]);;

let DOMSUB_FUPDATE_THM = prove
 (`!(fm:(A,B)fmap) k1 k2 v.
     fm |+ (k1,v) \\ k2 =
     if k1 = k2 then fm \\ k2 else (fm \\ k2) |+ (k1,v)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[fmap_eq_flookup; DOMSUB_FLOOKUP_THM; FLOOKUP_UPDATE] THEN
  ASM_MESON_TAC[]);;

let FDOM_DOMSUB = prove
 (`!(fm:(A,B)fmap) k. FDOM (fm \\ k) = FDOM fm DELETE k`,
  REWRITE_TAC[EXTENSION; IN_DELETE; FDOM_FLOOKUP; DOMSUB_FLOOKUP_THM] THEN
  MESON_TAC[]);;

let DOMSUB_FAPPLY = prove
 (`!(fm:(A,B)fmap) k. FAPPLY (fm \\ k) k = FAPPLY FEMPTY k`,
  REWRITE_TAC[FAPPLY_FLOOKUP; DOMSUB_FLOOKUP_THM; FLOOKUP_EMPTY]);;

let DOMSUB_FAPPLY_NEQ = prove
 (`!(fm:(A,B)fmap) k1 k2. ~(k1 = k2) ==> (FAPPLY (fm \\ k1) k2 = FAPPLY fm k2)`,
  SIMP_TAC[FAPPLY_FLOOKUP; DOMSUB_FLOOKUP_THM]);;

let DOMSUB_FAPPLY_THM = prove
 (`!(fm:(A,B)fmap) k1 k2.
     FAPPLY (fm \\ k1) k2 = if k1 = k2 then FAPPLY FEMPTY k2 else FAPPLY fm k2`,
  REWRITE_TAC[FAPPLY_FLOOKUP; DOMSUB_FLOOKUP_THM; FLOOKUP_EMPTY] THEN
  MESON_TAC[]);;

let DOMSUB_FLOOKUP = prove
 (`!(fm:(A,B)fmap) k. FLOOKUP (fm \\ k) k = NONE`,
  REWRITE_TAC[DOMSUB_FLOOKUP_THM]);;

let DOMSUB_FLOOKUP_NEQ = prove
 (`!(fm:(A,B)fmap) k1 k2. ~(k1 = k2) ==> (FLOOKUP (fm \\ k1) k2 = FLOOKUP fm k2)`,
  SIMP_TAC[DOMSUB_FLOOKUP_THM]);;

let FRANGE_FUPDATE_DOMSUB = prove
 (`!(fm:(A,B)fmap) k v. FRANGE (fm |+ (k,v)) = v INSERT FRANGE (fm \\ k)`,
  REWRITE_TAC[FRANGE_FUPDATE; fmap_domsub]);;

let o_f_DOMSUB = prove
 (`!(g:B->C) (fm:(A,B)fmap) k. (g o_f fm) \\ k = g o_f (fm \\ k)`,
  REWRITE_TAC[fmap_eq_flookup; DOMSUB_FLOOKUP_THM; FLOOKUP_o_f] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[option_CASE]);;

let DOMSUB_IDEM = prove
 (`!(fm:(A,B)fmap) k. (fm \\ k) \\ k = fm \\ k`,
  REWRITE_TAC[fmap_eq_flookup; DOMSUB_FLOOKUP_THM] THEN MESON_TAC[]);;

let DOMSUB_COMMUTES = prove
 (`!(fm:(A,B)fmap) k1 k2. fm \\ k1 \\ k2 = fm \\ k2 \\ k1`,
  REWRITE_TAC[fmap_eq_flookup; DOMSUB_FLOOKUP_THM] THEN MESON_TAC[]);;

let o_f_FUPDATE = prove
 (`!(f:B->C) (fm:(A,B)fmap) k v. f o_f (fm |+ (k,v)) = (f o_f fm) |+ (k,f v)`,
  REWRITE_TAC[fmap_eq_flookup; FLOOKUP_o_f; FLOOKUP_UPDATE] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[option_CASE]);;

let DOMSUB_NOT_IN_DOM = prove
 (`!(fm:(A,B)fmap) k. ~(k IN FDOM fm) ==> (fm \\ k = fm)`,
  REWRITE_TAC[fmap_eq_flookup; DOMSUB_FLOOKUP_THM; FDOM_FLOOKUP] THEN
  MESON_TAC[]);;

let fmap_CASES = prove
 (`!f:(A,B)fmap. (f = FEMPTY) \/ ?g x y. f = g |+ (x,y)`,
  MATCH_MP_TAC fmap_SIMPLE_INDUCT THEN MESON_TAC[]);;

let SUBMAP_DOMSUB = prove
 (`!(f:(A,B)fmap) k. (f \\ k) SUBMAP f`,
  REWRITE_TAC[fmap_domsub; SUBMAP_DRESTRICT]);;

let FMERGE_DOMSUB = prove
 (`!(m:B->B->B) (m1:(A,B)fmap) m2 k.
     (FMERGE m m1 m2) \\ k = FMERGE m (m1 \\ k) (m2 \\ k)`,
  REWRITE_TAC[fmap_eq_flookup; FLOOKUP_FMERGE; DOMSUB_FLOOKUP_THM] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[option_CASE]);;

let SUBMAP_FUPDATE = prove
 (`!(f:(A,B)fmap) g x y.
     (f |+ (x,y)) SUBMAP g <=>
     x IN FDOM g /\ (FAPPLY g x = y) /\ (f \\ x) SUBMAP (g \\ x)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[SUBMAP_FLOOKUP_EQN; FLOOKUP_UPDATE; DOMSUB_FLOOKUP_THM] THEN
  REWRITE_TAC[CONJ_ASSOC] THEN
  SUBGOAL_THEN `x IN FDOM (g:(A,B)fmap) /\ FAPPLY g x = y <=> FLOOKUP g x = SOME y`
   SUBST1_TAC THENL [REWRITE_TAC[flookup_thm]; ALL_TAC] THEN
  EQ_TAC THENL
   [DISCH_TAC THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`x:A`; `y:B`]) THEN REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`a:A`; `b:B`] THEN
      ASM_CASES_TAC `x:A = a` THEN ASM_REWRITE_TAC[option_DISTINCT] THEN
      ASM_MESON_TAC[]];
    STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`a:A`; `b:B`] THEN
    ASM_CASES_TAC `x:A = a` THEN ASM_REWRITE_TAC[option_INJ] THEN
    ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Iterated updates: FUPDATE_LIST f l, written f |++ l.                      *)
(* ------------------------------------------------------------------------- *)

let FUPDATE_LIST = new_definition
  `FUPDATE_LIST = FOLDL (FUPDATE:(A,B)fmap->A#B->(A,B)fmap)`;;

parse_as_infix("|++",(19,"left"));;
override_interface("|++",`FUPDATE_LIST:(A,B)fmap->(A#B)list->(A,B)fmap`);;

let FUPDATE_LIST_THM = prove
 (`!f:(A,B)fmap.
     (f |++ [] = f) /\ (!h t. f |++ (CONS h t) = (FUPDATE f h) |++ t)`,
  REWRITE_TAC[FUPDATE_LIST; FOLDL]);;

let FUPDATE_LIST_APPLY_NOT_MEM = prove
 (`!kvl (f:(A,B)fmap) k.
     ~MEM k (MAP FST kvl) ==> (FAPPLY (f |++ kvl) k = FAPPLY f k)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[FUPDATE_LIST_THM; MAP; MEM] THEN
  SPEC_TAC(`h:A#B`,`h:A#B`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  ASM_SIMP_TAC[DE_MORGAN_THM; FAPPLY_FUPDATE_THM]);;

let FMAPAUX_FOLDL_APPEND = prove
 (`!(f:B->A->B) l1 l2 e. FOLDL f e (APPEND l1 l2) = FOLDL f (FOLDL f e l1) l2`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND; FOLDL]);;

let FUPDATE_LIST_APPEND = prove
 (`!(fm:(A,B)fmap) kvl1 kvl2.
     fm |++ (APPEND kvl1 kvl2) = fm |++ kvl1 |++ kvl2`,
  REWRITE_TAC[FUPDATE_LIST; FMAPAUX_FOLDL_APPEND]);;

let FUPDATE_FUPDATE_LIST_COMMUTES = prove
 (`!(fm:(A,B)fmap) k v kvl.
     ~MEM k (MAP FST kvl) ==> (fm |+ (k,v) |++ kvl = (fm |++ kvl) |+ (k,v))`,
  REPEAT GEN_TAC THEN SPEC_TAC(`fm:(A,B)fmap`,`fm:(A,B)fmap`) THEN
  SPEC_TAC(`kvl:(A#B)list`,`kvl:(A#B)list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[FUPDATE_LIST_THM; MAP; MEM] THEN
  SPEC_TAC(`h:A#B`,`h:A#B`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  REWRITE_TAC[DE_MORGAN_THM] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP FUPDATE_COMMUTES th]) THEN
  ASM_MESON_TAC[]);;

let FUPDATE_FUPDATE_LIST_MEM = prove
 (`!(fm:(A,B)fmap) k v kvl.
     MEM k (MAP FST kvl) ==> (fm |+ (k,v) |++ kvl = fm |++ kvl)`,
  REPEAT GEN_TAC THEN SPEC_TAC(`fm:(A,B)fmap`,`fm:(A,B)fmap`) THEN
  SPEC_TAC(`kvl:(A#B)list`,`kvl:(A#B)list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[FUPDATE_LIST_THM; MAP; MEM] THEN
  SPEC_TAC(`h:A#B`,`h:A#B`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `b:B`] THEN REWRITE_TAC[] THEN
  ASM_CASES_TAC `k:A = a` THEN ASM_REWRITE_TAC[FUPDATE_EQ] THEN
  ASM_SIMP_TAC[FUPDATE_COMMUTES]);;

let FEVERY_FUPDATE_LIST = prove
 (`!kvl (P:A#B->bool) (fm:(A,B)fmap).
     ALL_DISTINCT (MAP FST kvl) ==>
     (FEVERY P (fm |++ kvl) <=>
      ALL P kvl /\ FEVERY P (DRESTRICT fm (COMPL (set_of_list (MAP FST kvl)))))`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[FUPDATE_LIST_THM; ALL; MAP; set_of_list; COMPL_DEF; DIFF_EMPTY;
                DRESTRICT_UNIV];
    ALL_TAC] THEN
  SPEC_TAC(`h:A#B`,`h:A#B`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `b:B`; `P:A#B->bool`; `fm:(A,B)fmap`] THEN
  REWRITE_TAC[MAP; ALL_DISTINCT; ALL; FUPDATE_LIST_THM; set_of_list] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(fun th -> ASM_SIMP_TAC[th]) THEN
  SUBGOAL_THEN `(a:A) IN COMPL (set_of_list (MAP FST (t:(A#B)list)))`
   (fun th -> REWRITE_TAC[th; DRESTRICT_FUPDATE]) THENL
   [ASM_REWRITE_TAC[FMAPAUX_IN_COMPL; IN_SET_OF_LIST]; ALL_TAC] THEN
  REWRITE_TAC[FEVERY_FUPDATE; DRESTRICT_DRESTRICT] THEN
  SUBGOAL_THEN
   `COMPL (set_of_list (MAP FST (t:(A#B)list))) INTER COMPL {a} =
    COMPL (a INSERT set_of_list (MAP FST t))` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; FMAPAUX_IN_COMPL; IN_INSERT; IN_SING] THEN
    MESON_TAC[];
    CONV_TAC TAUT]);;

let FOLDL_FUPDATE_LIST = prove
 (`!(f1:C->A) (f2:C->B) ls a.
     FOLDL (\fm k. fm |+ (f1 k, f2 k)) a ls = a |++ MAP (\k. (f1 k, f2 k)) ls`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[FOLDL; MAP; FUPDATE_LIST_THM]);;

let FUPDATE_LIST_SNOC = prove
 (`!xs (x:A#B) fm. fm |++ SNOC x xs = (fm |++ xs) |+ x`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[SNOC; FUPDATE_LIST_THM]);;

let FUPD11_SAME_KEY_AND_BASE = prove
 (`!(f:(A,B)fmap) k v1 v2. (f |+ (k,v1) = f |+ (k,v2)) <=> (v1 = v2)`,
  REPEAT GEN_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN
  REWRITE_TAC[fmap_eq_flookup; FLOOKUP_UPDATE] THEN
  DISCH_THEN(MP_TAC o SPEC `k:A`) THEN REWRITE_TAC[option_INJ]);;

let FUPD11_SAME_NEW_KEY = prove
 (`!(f1:(A,B)fmap) f2 k v1 v2.
     ~(k IN FDOM f1) /\ ~(k IN FDOM f2) ==>
     ((f1 |+ (k,v1) = f2 |+ (k,v2)) <=> (f1 = f2) /\ (v1 = v2))`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN
  REWRITE_TAC[fmap_eq_flookup; FLOOKUP_UPDATE] THEN DISCH_TAC THEN
  CONJ_TAC THENL
   [X_GEN_TAC `x:A` THEN FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN
    ASM_CASES_TAC `k:A = x` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
    ASM_MESON_TAC[flookup_thm];
    FIRST_X_ASSUM(MP_TAC o SPEC `k:A`) THEN REWRITE_TAC[option_INJ]]);;

let FDOM_FUPDATE_LIST = prove
 (`!kvl (fm:(A,B)fmap).
     FDOM (fm |++ kvl) = FDOM fm UNION set_of_list (MAP FST kvl)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[FUPDATE_LIST_THM; MAP; set_of_list; UNION_EMPTY] THEN
  SPEC_TAC(`h:A#B`,`h:A#B`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  REWRITE_TAC[FDOM_FUPDATE] THEN SET_TAC[]);;

let FUPDATE_PURGE' = prove
 (`!(f:(A,B)fmap) x y. (f \\ x) |+ (x,y) = f |+ (x,y)`,
  REWRITE_TAC[fmap_eq_flookup; FLOOKUP_UPDATE; DOMSUB_FLOOKUP_THM] THEN
  MESON_TAC[]);;

let FUPDATE_PURGE = prove
 (`!(f:(A,B)fmap) x y. f |+ (x,y) = (f \\ x) |+ (x,y)`,
  REWRITE_TAC[FUPDATE_PURGE']);;

(* ------------------------------------------------------------------------- *)
(* Mapping over the key-value pairs (HOL4 FMAP_MAP2).                        *)
(* ------------------------------------------------------------------------- *)

let FMAP_MAP2_def = new_definition
  `FMAP_MAP2 (f:A#B->C) (m:(A,B)fmap) =
     FUN_FMAP (\x. f (x, FAPPLY m x)) (FDOM m)`;;

let FMAP_MAP2_THM = prove
 (`!(f:A#B->C) (m:(A,B)fmap).
     (FDOM (FMAP_MAP2 f m) = FDOM m) /\
     (!x. x IN FDOM m ==> (FAPPLY (FMAP_MAP2 f m) x = f (x, FAPPLY m x)))`,
  SIMP_TAC[FMAP_MAP2_def; FUN_FMAP_DEF; FDOM_FINITE]);;

let FLOOKUP_FMAP_MAP2 = prove
 (`!(f:A#B->C) (m:(A,B)fmap) k.
     FLOOKUP (FMAP_MAP2 f m) k = OPTION_MAP (\v. f (k,v)) (FLOOKUP m k)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FLOOKUP_DEF; FMAP_MAP2_THM] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[OPTION_MAP_DEF; FMAP_MAP2_THM]);;

let FMAP_MAP2_FEMPTY = prove
 (`!f:A#B->C. FMAP_MAP2 f FEMPTY = FEMPTY`,
  REWRITE_TAC[fmap_eq_flookup; FLOOKUP_FMAP_MAP2; FLOOKUP_EMPTY; OPTION_MAP_DEF]);;

let FMAP_MAP2_FUPDATE = prove
 (`!(f:A#B->C) (m:(A,B)fmap) x v.
     FMAP_MAP2 f (m |+ (x,v)) = (FMAP_MAP2 f m) |+ (x, f (x,v))`,
  REWRITE_TAC[fmap_eq_flookup; FLOOKUP_FMAP_MAP2; FLOOKUP_UPDATE] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[OPTION_MAP_DEF]);;

let DOMSUB_FMAP_MAP2 = prove
 (`!(f:A#B->C) (m:(A,B)fmap) s. (FMAP_MAP2 f m) \\ s = FMAP_MAP2 f (m \\ s)`,
  REWRITE_TAC[fmap_eq_flookup; FLOOKUP_FMAP_MAP2; DOMSUB_FLOOKUP_THM] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[OPTION_MAP_DEF]);;

let FEVERY_STRENGTHEN_THM = prove
 (`!(P:A#B->bool) f x y.
     FEVERY P FEMPTY /\
     ((FEVERY P f /\ P (x,y)) ==> FEVERY P (f |+ (x,y)))`,
  REWRITE_TAC[FEVERY_DEF; FDOM_FEMPTY; NOT_IN_EMPTY; FAPPLY_FUPDATE_THM;
              FDOM_FUPDATE; IN_INSERT] THEN
  MESON_TAC[]);;

let FUPDATE_ELIM = prove
 (`!k v (f:(A,B)fmap). ((k IN FDOM f) /\ (FAPPLY f k = v)) ==> (f |+ (k,v) = f)`,
  REWRITE_TAC[GSYM flookup_thm; fmap_eq_flookup; FLOOKUP_UPDATE] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* More on FUNION and DRESTRICT.                                             *)
(* ------------------------------------------------------------------------- *)

let FUNION_EQ_FEMPTY = prove
 (`!h1 h2:(A,B)fmap. (FUNION h1 h2 = FEMPTY) <=> (h1 = FEMPTY) /\ (h2 = FEMPTY)`,
  REWRITE_TAC[GSYM FDOM_EQ_EMPTY; FDOM_FUNION; EMPTY_UNION]);;

let SUBMAP_FUNION = prove
 (`!f1 f2 f3:(A,B)fmap.
     f1 SUBMAP f2 \/ (DISJOINT (FDOM f1) (FDOM f2) /\ f1 SUBMAP f3) ==>
     f1 SUBMAP FUNION f2 f3`,
  REWRITE_TAC[SUBMAP_DEF; FUNION_DEF; IN_UNION; DISJOINT; EXTENSION;
              NOT_IN_EMPTY; IN_INTER] THEN
  MESON_TAC[]);;

let SUBMAP_FUNION_ID = prove
 (`(!f1 f2:(A,B)fmap. f1 SUBMAP FUNION f1 f2) /\
   (!f1 f2:(A,B)fmap. DISJOINT (FDOM f1) (FDOM f2) ==> f2 SUBMAP (FUNION f1 f2))`,
  MESON_TAC[SUBMAP_REFL; SUBMAP_FUNION; DISJOINT_SYM]);;

let FUNION_COMM = prove
 (`!f g:(A,B)fmap. DISJOINT (FDOM f) (FDOM g) ==> (FUNION f g = FUNION g f)`,
  REWRITE_TAC[GSYM fmap_EQ_THM; FUNION_DEF; IN_UNION; DISJOINT; EXTENSION;
              NOT_IN_EMPTY; IN_INTER] THEN
  MESON_TAC[]);;

let FUNION_ASSOC = prove
 (`!f g h:(A,B)fmap. FUNION f (FUNION g h) = FUNION (FUNION f g) h`,
  REWRITE_TAC[GSYM fmap_EQ_THM; FUNION_DEF; IN_UNION; UNION_ASSOC] THEN
  MESON_TAC[]);;

let DRESTRICT_FUNION = prove
 (`!(h:(A,B)fmap) s1 s2.
     FUNION (DRESTRICT h s1) (DRESTRICT h s2) = DRESTRICT h (s1 UNION s2)`,
  REWRITE_TAC[GSYM fmap_EQ_THM; FUNION_DEF; DRESTRICT_DEF; EXTENSION;
              IN_UNION; IN_INTER] THEN
  MESON_TAC[]);;

let DRESTRICT_IDEMPOT = prove
 (`!(s:(A,B)fmap) vs. DRESTRICT (DRESTRICT s vs) vs = DRESTRICT s vs`,
  REWRITE_TAC[DRESTRICT_DRESTRICT; INTER_IDEMPOT]);;

let SUBMAP_FUNION_ABSORPTION = prove
 (`!f g:(A,B)fmap. f SUBMAP g <=> (FUNION f g = g)`,
  REWRITE_TAC[SUBMAP_DEF; GSYM fmap_EQ_THM; EXTENSION; FUNION_DEF; IN_UNION] THEN
  MESON_TAC[]);;

let o_f_FUNION = prove
 (`!(f:B->C) (f1:(A,B)fmap) f2.
     f o_f (FUNION f1 f2) = FUNION (f o_f f1) (f o_f f2)`,
  REWRITE_TAC[fmap_eq_flookup; FLOOKUP_o_f; FLOOKUP_FUNION] THEN
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `FLOOKUP (f1:(A,B)fmap) x` (cases "option")) THEN
  REWRITE_TAC[option_CASE]);;

(* ------------------------------------------------------------------------- *)
(* Mapping an injective function over the keys of a finite map.              *)
(* ------------------------------------------------------------------------- *)

let MAP_KEYS_def = new_specification ["MAP_KEYS"]
 (prove
   (`?MAP_KEYS. !(f:A->B) (fm:(A,C)fmap).
       (FDOM (MAP_KEYS f fm) = IMAGE f (FDOM fm)) /\
       (INJ f (FDOM fm) UNIV ==>
        !x. x IN FDOM fm ==> (FAPPLY (MAP_KEYS f fm) (f x) = FAPPLY fm x))`,
    EXISTS_TAC `\(f:A->B) (fm:(A,C)fmap).
       fmap_ABS (\y. if y IN IMAGE f (FDOM fm)
                     then SOME (FAPPLY fm (@x. x IN FDOM fm /\ f x = y))
                     else NONE)` THEN
    MAP_EVERY X_GEN_TAC [`f:A->B`; `fm:(A,C)fmap`] THEN
    SUBGOAL_THEN
     `FLOOKUP (fmap_ABS (\y. if y IN IMAGE (f:A->B) (FDOM (fm:(A,C)fmap))
                             then SOME (FAPPLY fm (@x. x IN FDOM fm /\ f x = y))
                             else NONE)) =
      (\y. if y IN IMAGE f (FDOM fm)
           then SOME (FAPPLY fm (@x. x IN FDOM fm /\ f x = y)) else NONE)`
     ASSUME_TAC THENL
     [MATCH_MP_TAC FLOOKUP_fmap_ABS THEN
      EXISTS_TAC `IMAGE (f:A->B) (FDOM (fm:(A,C)fmap))` THEN
      SIMP_TAC[FINITE_IMAGE; FDOM_FINITE] THEN MESON_TAC[];
      ALL_TAC] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP FLOOKUP_EQ_FDOM_FAPPLY) THEN
    ASM_REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN CONJ_TAC THENL
     [X_GEN_TAC `y:B` THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT];
      ALL_TAC] THEN
    REWRITE_TAC[INJ; IN_UNIV] THEN STRIP_TAC THEN X_GEN_TAC `x:A` THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(f:A->B) x IN IMAGE f (FDOM (fm:(A,C)fmap))`
     (fun th -> REWRITE_TAC[th; THE_DEF]) THENL
     [ASM_MESON_TAC[IN_IMAGE]; ALL_TAC] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC SELECT_UNIQUE THEN ASM_MESON_TAC[]));;

let MAP_KEYS_FEMPTY = prove
 (`!f:A->B. MAP_KEYS f (FEMPTY:(A,C)fmap) = FEMPTY`,
  REWRITE_TAC[GSYM FDOM_EQ_EMPTY; MAP_KEYS_def; FDOM_FEMPTY; IMAGE_CLAUSES]);;

let MAP_KEYS_FUPDATE = prove
 (`!(f:A->B) (fm:(A,C)fmap) k v.
     INJ f (k INSERT FDOM fm) UNIV ==>
     (MAP_KEYS f (fm |+ (k,v)) = (MAP_KEYS f fm) |+ (f k,v))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `INJ (f:A->B) (FDOM (fm:(A,C)fmap)) UNIV` ASSUME_TAC THENL
   [UNDISCH_TAC `INJ (f:A->B) (k INSERT FDOM (fm:(A,C)fmap)) UNIV` THEN
    REWRITE_TAC[INJ; IN_INSERT; IN_UNIV] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[fmap_EXT; MAP_KEYS_def; FDOM_FUPDATE; IMAGE_CLAUSES] THEN
  REWRITE_TAC[FORALL_IN_INSERT; FORALL_IN_IMAGE] THEN
  MP_TAC(ISPECL [`f:A->B`; `(fm:(A,C)fmap) |+ (k,v)`] MAP_KEYS_def) THEN
  MP_TAC(ISPECL [`f:A->B`; `fm:(A,C)fmap`] MAP_KEYS_def) THEN
  ASM_REWRITE_TAC[FDOM_FUPDATE] THEN REPEAT STRIP_TAC THENL
   [ASM_SIMP_TAC[IN_INSERT; FAPPLY_FUPDATE_THM]; ALL_TAC] THEN
  UNDISCH_TAC `INJ (f:A->B) (k INSERT FDOM (fm:(A,C)fmap)) UNIV` THEN
  REWRITE_TAC[INJ; IN_INSERT; IN_UNIV] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[IN_INSERT; FAPPLY_FUPDATE_THM] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let FLOOKUP_MAP_KEYS = prove
 (`!(f:A->B) (m:(A,C)fmap) k.
     INJ f (FDOM m) UNIV ==>
     (FLOOKUP (MAP_KEYS f m) k =
      OPTION_BIND (some x. (k = f x) /\ x IN FDOM m) (FLOOKUP m))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[some_DEF] THEN
  REWRITE_TAC[FLOOKUP_DEF; MAP_KEYS_def; IN_IMAGE] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[OPTION_BIND_DEF] THEN
  FIRST_ASSUM(MP_TAC o SELECT_RULE) THEN
  SPEC_TAC(`@x. (k:B) = f x /\ x IN FDOM (m:(A,C)fmap)`,`x0:A`) THEN
  GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[MAP_KEYS_def; FLOOKUP_DEF]);;

let FMAPAUX_INJ_UNIV = prove
 (`!(f:A->B) s. INJ f UNIV UNIV ==> INJ f s UNIV`,
  REWRITE_TAC[INJ; IN_UNIV] THEN MESON_TAC[]);;

let FLOOKUP_MAP_KEYS_MAPPED = prove
 (`!(f:A->B) (m:(A,C)fmap) k.
     INJ f UNIV UNIV ==> (FLOOKUP (MAP_KEYS f m) (f k) = FLOOKUP m k)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o SPEC `FDOM (m:(A,C)fmap)` o MATCH_MP FMAPAUX_INJ_UNIV) THEN
  SUBGOAL_THEN `(f:A->B) k IN IMAGE f (FDOM (m:(A,C)fmap)) <=> k IN FDOM m`
   ASSUME_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[INJ; IN_UNIV]; ALL_TAC] THEN
  ASM_REWRITE_TAC[FLOOKUP_DEF; MAP_KEYS_def] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[MAP_KEYS_def]);;

let FLOOKUP_MAP_KEYS_NOTIN_IMAGE = prove
 (`!(f:A->B) (m:(A,C)fmap) y.
     ~(?x. y = f x) ==> (FLOOKUP (MAP_KEYS f m) y = NONE)`,
  REWRITE_TAC[flookup_thm; MAP_KEYS_def; IN_IMAGE] THEN MESON_TAC[]);;

let DRESTRICT_MAP_KEYS_IMAGE = prove
 (`!(f:A->B) (fm:(A,C)fmap) s.
     INJ f UNIV UNIV ==>
     (DRESTRICT (MAP_KEYS f fm) (IMAGE f s) = MAP_KEYS f (DRESTRICT fm s))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fmap_eq_flookup; FLOOKUP_DRESTRICT] THEN
  X_GEN_TAC `y:B` THEN ASM_CASES_TAC `?x:A. (y:B) = (f:A->B) x` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `x:A` SUBST1_TAC) THEN
    ASM_SIMP_TAC[FLOOKUP_MAP_KEYS_MAPPED; FLOOKUP_DRESTRICT] THEN
    SUBGOAL_THEN `(f:A->B) x IN IMAGE f s <=> x IN s` (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[INJ; IN_UNIV];
    ASM_SIMP_TAC[FLOOKUP_MAP_KEYS_NOTIN_IMAGE; IN_IMAGE] THEN
    ASM_MESON_TAC[]]);;

let DOMSUB_MAP_KEYS = prove
 (`!(f:A->B) (fm:(A,C)fmap) s.
     BIJ f UNIV UNIV ==> ((MAP_KEYS f fm) \\ (f s) = MAP_KEYS f (fm \\ s))`,
  REWRITE_TAC[BIJ] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[fmap_eq_flookup; DOMSUB_FLOOKUP_THM] THEN X_GEN_TAC `y:B` THEN
  SUBGOAL_THEN `?x:A. (y:B) = (f:A->B) x` (X_CHOOSE_THEN `x:A` SUBST1_TAC) THENL
   [ASM_MESON_TAC[SURJ; IN_UNIV]; ALL_TAC] THEN
  ASM_SIMP_TAC[FLOOKUP_MAP_KEYS_MAPPED; DOMSUB_FLOOKUP_THM] THEN
  SUBGOAL_THEN `(f:A->B) s = f x <=> s = x` (fun th -> REWRITE_TAC[th]) THEN
  ASM_MESON_TAC[INJ; IN_UNIV]);;

(* ------------------------------------------------------------------------- *)
(* Relating the values in two finite maps.                                   *)
(* ------------------------------------------------------------------------- *)

let fmap_rel_def = new_definition
  `fmap_rel (R:B->C->bool) (f1:(A,B)fmap) (f2:(A,C)fmap) <=>
     FDOM f2 = FDOM f1 /\ (!x. x IN FDOM f1 ==> R (FAPPLY f1 x) (FAPPLY f2 x))`;;

let fmap_rel_FUPDATE_same = prove
 (`!(R:B->C->bool) (f1:(A,B)fmap) f2 v1 v2 k.
     fmap_rel R f1 f2 /\ R v1 v2 ==> fmap_rel R (f1 |+ (k,v1)) (f2 |+ (k,v2))`,
  REWRITE_TAC[fmap_rel_def; FDOM_FUPDATE; IN_INSERT; FAPPLY_FUPDATE_THM] THEN
  MESON_TAC[]);;

let fmap_rel_FUPDATE_LIST_same = prove
 (`!(R:B->C->bool) (ls1:(A#B)list) (ls2:(A#C)list) f1 f2.
     fmap_rel R f1 f2 /\ (MAP FST ls1 = MAP FST ls2) /\
     ALL2 R (MAP SND ls1) (MAP SND ls2) ==>
     fmap_rel R (f1 |++ ls1) (f2 |++ ls2)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP; NOT_CONS_NIL; ALL2; FUPDATE_LIST_THM; CONS_11] THEN
  SPEC_TAC(`h:A#B`,`h:A#B`) THEN SPEC_TAC(`h':A#C`,`h':A#C`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC fmap_rel_FUPDATE_same THEN ASM_MESON_TAC[]);;

let fmap_rel_FEMPTY = prove
 (`(!(R:A->B->bool) (f2:(C,B)fmap). fmap_rel R FEMPTY f2 <=> f2 = FEMPTY) /\
   (!(R:A->B->bool) (f1:(C,A)fmap). fmap_rel R f1 FEMPTY <=> f1 = FEMPTY)`,
  REWRITE_TAC[fmap_rel_def; FDOM_FEMPTY; NOT_IN_EMPTY] THEN
  REWRITE_TAC[FDOM_EQ_EMPTY; FDOM_EQ_EMPTY_SYM] THEN
  MESON_TAC[FDOM_FEMPTY; NOT_IN_EMPTY]);;

let fmap_rel_refl = prove
 (`!(R:B->B->bool) (x:(A,B)fmap). (!x. R x x) ==> fmap_rel R x x`,
  SIMP_TAC[fmap_rel_def]);;

let fmap_rel_FUNION_rels = prove
 (`!(R:B->C->bool) (f1:(A,B)fmap) f2 f3 f4.
     fmap_rel R f1 f2 /\ fmap_rel R f3 f4 ==>
     fmap_rel R (FUNION f1 f3) (FUNION f2 f4)`,
  REWRITE_TAC[fmap_rel_def; FUNION_DEF; IN_UNION] THEN MESON_TAC[]);;

let fmap_rel_FUPDATE_I = prove
 (`!(R:B->C->bool) (f1:(A,B)fmap) f2 k v1 v2.
     fmap_rel R (f1 \\ k) (f2 \\ k) /\ R v1 v2 ==>
     fmap_rel R (f1 |+ (k,v1)) (f2 |+ (k,v2))`,
  REWRITE_TAC[fmap_rel_def; FDOM_DOMSUB; FDOM_FUPDATE; DOMSUB_FAPPLY_THM;
              FAPPLY_FUPDATE_THM; EXTENSION; IN_DELETE; IN_INSERT] THEN
  MESON_TAC[]);;

let fmap_rel_mono = prove
 (`!(R1:B->C->bool) R2 (f1:(A,B)fmap) f2.
     (!x y. R1 x y ==> R2 x y) ==> fmap_rel R1 f1 f2 ==> fmap_rel R2 f1 f2`,
  REWRITE_TAC[fmap_rel_def] THEN MESON_TAC[]);;

let fmap_rel_OPTREL_FLOOKUP = prove
 (`!(R:B->C->bool) (f1:(A,B)fmap) f2.
     fmap_rel R f1 f2 <=> !k. OPTREL R (FLOOKUP f1 k) (FLOOKUP f2 k)`,
  REWRITE_TAC[fmap_rel_def; OPTREL_DEF; flookup_thm; EXTENSION] THEN
  MESON_TAC[]);;

let fmap_rel_FLOOKUP_imp = prove
 (`!(R:B->C->bool) (f1:(A,B)fmap) f2.
     fmap_rel R f1 f2 ==>
     (!k. FLOOKUP f1 k = NONE ==> FLOOKUP f2 k = NONE) /\
     (!k v1. FLOOKUP f1 k = SOME v1 ==> ?v2. FLOOKUP f2 k = SOME v2 /\ R v1 v2)`,
  REWRITE_TAC[fmap_rel_OPTREL_FLOOKUP; OPTREL_DEF] THEN
  MESON_TAC[option_DISTINCT; option_INJ]);;

let fmap_rel_trans = prove
 (`!(R:B->B->bool).
     (!x y z. R x y /\ R y z ==> R x z) ==>
     !x y (z:(A,B)fmap). fmap_rel R x y /\ fmap_rel R y z ==> fmap_rel R x z`,
  REWRITE_TAC[fmap_rel_def] THEN MESON_TAC[]);;

let fmap_rel_sym = prove
 (`!(R:B->B->bool).
     (!x y. R x y ==> R y x) ==>
     !x (y:(A,B)fmap). fmap_rel R x y ==> fmap_rel R y x`,
  REWRITE_TAC[fmap_rel_def] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Miscellaneous lemmas (HOL4 order).                                        *)
(* ------------------------------------------------------------------------- *)

let FEVERY_SUBMAP = prove
 (`!(P:A#B->bool) fm fm0. FEVERY P fm /\ fm0 SUBMAP fm ==> FEVERY P fm0`,
  REWRITE_TAC[FEVERY_DEF; SUBMAP_DEF] THEN MESON_TAC[]);;

let FEVERY_ALL_FLOOKUP = prove
 (`!(P:A#B->bool) f. FEVERY P f <=> !k v. (FLOOKUP f k = SOME v) ==> P (k,v)`,
  REWRITE_TAC[FEVERY_DEF; flookup_thm] THEN MESON_TAC[]);;

let FUPDATE_LIST_CANCEL = prove
 (`!ls1 (fm:(A,B)fmap) ls2.
     (!k. MEM k (MAP FST ls1) ==> MEM k (MAP FST ls2)) ==>
     (fm |++ ls1 |++ ls2 = fm |++ ls2)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[FUPDATE_LIST_THM; MAP; MEM] THEN
  SPEC_TAC(`h:A#B`,`h:A#B`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(fm:(A,B)fmap) |+ (p1,p2) |++ t |++ ls2 = fm |+ (p1,p2) |++ ls2`
   SUBST1_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC FUPDATE_FUPDATE_LIST_MEM THEN ASM_MESON_TAC[]);;

let FUPDATE_EQ_FUNION = prove
 (`!(fm:(A,B)fmap) kv. fm |+ kv = FUNION (FEMPTY |+ kv) fm`,
  GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  REWRITE_TAC[fmap_eq_flookup; FLOOKUP_FUNION; FLOOKUP_UPDATE; FLOOKUP_EMPTY] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[option_CASE]);;

let FUPDATE_LIST_APPEND_COMMUTES = prove
 (`!l1 l2 (fm:(A,B)fmap).
     DISJOINT (set_of_list (MAP FST l1)) (set_of_list (MAP FST l2)) ==>
     (fm |++ l1 |++ l2 = fm |++ l2 |++ l1)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[FUPDATE_LIST_THM] THEN
  SPEC_TAC(`h:A#B`,`h:A#B`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  REWRITE_TAC[MAP; set_of_list; DISJOINT_INSERT; IN_SET_OF_LIST] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[FUPDATE_FUPDATE_LIST_COMMUTES] THEN
  ASM_SIMP_TAC[GSYM FUPDATE_FUPDATE_LIST_COMMUTES]);;

let IMAGE_FRANGE = prove
 (`!(f:B->C) (fm:(A,B)fmap). IMAGE f (FRANGE fm) = FRANGE (f o_f fm)`,
  REWRITE_TAC[EXTENSION; IN_IMAGE; FRANGE_DEF; IN_ELIM_THM; FDOM_o_f] THEN
  MESON_TAC[o_f_FAPPLY]);;

let SUBMAP_mono_FUPDATE = prove
 (`!(f:(A,B)fmap) g x y. f \\ x SUBMAP g \\ x ==> f |+ (x,y) SUBMAP g |+ (x,y)`,
  REWRITE_TAC[SUBMAP_FUPDATE; FDOM_FUPDATE; IN_INSERT; FAPPLY_FUPDATE_THM;
              DOMSUB_FUPDATE]);;

let SUBMAP_DOMSUB_gen = prove
 (`!(f:(A,B)fmap) g k. f \\ k SUBMAP g <=> f \\ k SUBMAP g \\ k`,
  REWRITE_TAC[SUBMAP_FLOOKUP_EQN; DOMSUB_FLOOKUP_THM] THEN
  MESON_TAC[option_DISTINCT]);;

let DOMSUB_SUBMAP = prove
 (`!(f:(A,B)fmap) g x. f SUBMAP g /\ ~(x IN FDOM f) ==> f SUBMAP g \\ x`,
  REWRITE_TAC[SUBMAP_DEF; FDOM_DOMSUB; IN_DELETE; DOMSUB_FAPPLY_THM] THEN
  MESON_TAC[]);;

let DRESTRICT_DOMSUB = prove
 (`!(f:(A,B)fmap) s k. DRESTRICT f s \\ k = DRESTRICT f (s DELETE k)`,
  REWRITE_TAC[fmap_eq_flookup; DOMSUB_FLOOKUP_THM; FLOOKUP_DRESTRICT;
              IN_DELETE] THEN
  MESON_TAC[]);;

let FUPDATE_LIST_APPLY_NOT_MEM_matchable = prove
 (`!kvl (f:(A,B)fmap) k v.
     ~MEM k (MAP FST kvl) /\ (v = FAPPLY f k) ==> (FAPPLY (f |++ kvl) k = v)`,
  MESON_TAC[FUPDATE_LIST_APPLY_NOT_MEM]);;

let FUPDATE_SAME_APPLY = prove
 (`!(x:A) (kv:A#B) fm1 fm2.
     (x = FST kv) \/ (FAPPLY fm1 x = FAPPLY fm2 x) ==>
     (FAPPLY (fm1 |+ kv) x = FAPPLY (fm2 |+ kv) x)`,
  GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM; FAPPLY_FUPDATE_THM] THEN
  MESON_TAC[]);;

let FUPDATE_SAME_LIST_APPLY = prove
 (`!kvl (fm1:(A,B)fmap) fm2 x.
     MEM x (MAP FST kvl) ==> (FAPPLY (fm1 |++ kvl) x = FAPPLY (fm2 |++ kvl) x)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; MEM; FUPDATE_LIST_THM] THEN
  SPEC_TAC(`h:A#B`,`h:A#B`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `b:B`; `fm1:(A,B)fmap`; `fm2:(A,B)fmap`; `x:A`] THEN
  ASM_CASES_TAC `MEM (x:A) (MAP FST (t:(A#B)list))` THEN ASM_SIMP_TAC[] THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  ASM_SIMP_TAC[FUPDATE_LIST_APPLY_NOT_MEM; FAPPLY_FUPDATE]);;

let FUPDATE_LIST_ALL_DISTINCT_REVERSE = prove
 (`!ls. ALL_DISTINCT (MAP FST ls) ==> !fm:(A,B)fmap. fm |++ (REVERSE ls) = fm |++ ls`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[REVERSE; MAP; ALL_DISTINCT] THEN
  SPEC_TAC(`h:A#B`,`h:A#B`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[FUPDATE_LIST_APPEND; FUPDATE_LIST_THM;
               FUPDATE_FUPDATE_LIST_COMMUTES]);;

let IN_FRANGE = prove
 (`!(f:(A,B)fmap) v. v IN FRANGE f <=> ?k. k IN FDOM f /\ (FAPPLY f k = v)`,
  REWRITE_TAC[FRANGE_DEF; IN_ELIM_THM]);;

let IN_FRANGE_FLOOKUP = prove
 (`!(f:(A,B)fmap) v. v IN FRANGE f <=> ?k. FLOOKUP f k = SOME v`,
  REWRITE_TAC[FRANGE_FLOOKUP]);;

let FRANGE_FUPDATE_LIST_SUBSET = prove
 (`!ls (fm:(A,B)fmap).
     FRANGE (fm |++ ls) SUBSET FRANGE fm UNION (set_of_list (MAP SND ls))`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[FUPDATE_LIST_THM; MAP; set_of_list; UNION_EMPTY; SUBSET_REFL] THEN
  SPEC_TAC(`h:A#B`,`h:A#B`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `b:B`; `fm:(A,B)fmap`] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(fm:(A,B)fmap) |+ (a,b)`) THEN
  REWRITE_TAC[FRANGE_FUPDATE_DOMSUB] THEN
  MP_TAC(ISPECL [`(fm:(A,B)fmap) \\ a`; `fm:(A,B)fmap`] SUBMAP_FRANGE) THEN
  REWRITE_TAC[SUBMAP_DOMSUB] THEN SET_TAC[]);;

let IN_FRANGE_FUPDATE_LIST_suff = prove
 (`!(P:B->bool) (fm:(A,B)fmap) ls.
     (!v. v IN FRANGE fm ==> P v) /\ (!v. MEM v (MAP SND ls) ==> P v) ==>
     !v. v IN FRANGE (fm |++ ls) ==> P v`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`ls:(A#B)list`; `fm:(A,B)fmap`] FRANGE_FUPDATE_LIST_SUBSET) THEN
  REWRITE_TAC[SUBSET; IN_UNION; IN_SET_OF_LIST] THEN MESON_TAC[]);;

let IN_FRANGE_o_f_suff = prove
 (`!(P:C->bool) (f:B->C) (fm:(A,B)fmap).
     (!v. v IN FRANGE fm ==> P (f v)) ==> !v. v IN FRANGE (f o_f fm) ==> P v`,
  REWRITE_TAC[IN_FRANGE; FDOM_o_f] THEN MESON_TAC[o_f_FAPPLY]);;

let fupdate_list_map = prove
 (`!l (f:B->C) (x:A) (y:A).
     x IN FDOM (FEMPTY |++ l) ==>
     (FAPPLY (FEMPTY |++ MAP (\(a,b). (a, f b)) l) x =
      f (FAPPLY (FEMPTY |++ l) x))`,
  SUBGOAL_THEN
   `!l (f:B->C) (fm:(A,B)fmap) (x:A).
      x IN FDOM (fm |++ l) ==>
      (FAPPLY ((f o_f fm) |++ MAP (\(a,b). (a, f b)) l) x =
       f (FAPPLY (fm |++ l) x))`
   (fun th -> MESON_TAC[th; o_f_FEMPTY]) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; FUPDATE_LIST_THM] THEN
  SIMP_TAC[o_f_FAPPLY] THEN
  SPEC_TAC(`h:A#B`,`h:A#B`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  REWRITE_TAC[GSYM o_f_FUPDATE] THEN ASM_MESON_TAC[]);;

let fdom_fupdate_list2 = prove
 (`!kvl (fm:(A,B)fmap).
     FDOM (fm |++ kvl) =
     (FDOM fm DIFF set_of_list (MAP FST kvl)) UNION set_of_list (MAP FST kvl)`,
  REWRITE_TAC[FDOM_FUPDATE_LIST] THEN SET_TAC[]);;

let FINITE_MAP_LOOKUP_RANGE = prove
 (`(!(f:(A,B)fmap) x y. FLOOKUP f x = SOME y ==> y IN FRANGE f) /\
   (!(f:(A,B)fmap) x. x IN FDOM f ==> FAPPLY f x IN FRANGE f)`,
  MESON_TAC[FRANGE_FLOOKUP; flookup_thm]);;

let FUPDATE_EQ_FUPDATE_LIST = prove
 (`!(fm:(A,B)fmap) kv. fm |+ kv = fm |++ [kv]`,
  REWRITE_TAC[FUPDATE_LIST_THM]);;

let fupdate_list_foldr = prove
 (`!(m:(A,B)fmap) l. ITLIST (\(k,v) env. env |+ (k,v)) l m = m |++ REVERSE l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[ITLIST; REVERSE; FUPDATE_LIST_THM; FUPDATE_LIST_APPEND] THEN
  SPEC_TAC(`h:A#B`,`h:A#B`) THEN REWRITE_TAC[FORALL_PAIR_THM]);;

let fupdate_list_foldl = prove
 (`!(m:(A,B)fmap) l. FOLDL (\env (k,v). env |+ (k,v)) m l = m |++ l`,
  REWRITE_TAC[FUPDATE_LIST] THEN GEN_TAC THEN
  SUBGOAL_THEN `(\env (k,v). (env:(A,B)fmap) |+ (k,v)) = FUPDATE`
   (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM]);;

let fmap_to_list = prove
 (`!m:(A,B)fmap. ?l. ALL_DISTINCT (MAP FST l) /\ (m = FEMPTY |++ l)`,
  MATCH_MP_TAC fmap_INDUCT THEN CONJ_TAC THENL
   [EXISTS_TAC `[]:(A#B)list` THEN REWRITE_TAC[MAP; ALL_DISTINCT; FUPDATE_LIST_THM];
    ALL_TAC] THEN
  X_GEN_TAC `m:(A,B)fmap` THEN DISCH_THEN(X_CHOOSE_THEN `l:(A#B)list` STRIP_ASSUME_TAC) THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `y:B`] THEN DISCH_TAC THEN
  EXISTS_TAC `CONS (x:A,y:B) l` THEN
  SUBGOAL_THEN `~MEM (x:A) (MAP FST (l:(A#B)list))` ASSUME_TAC THENL
   [UNDISCH_TAC `~((x:A) IN FDOM (m:(A,B)fmap))` THEN
    ASM_REWRITE_TAC[FDOM_FUPDATE_LIST; FDOM_FEMPTY; UNION_EMPTY; IN_SET_OF_LIST];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MAP; ALL_DISTINCT; FUPDATE_LIST_THM; FUPDATE_FUPDATE_LIST_COMMUTES]);;

let disjoint_drestrict = prove
 (`!s (m:(A,B)fmap). DISJOINT s (FDOM m) ==> (DRESTRICT m (COMPL s) = m)`,
  REWRITE_TAC[fmap_eq_flookup; FLOOKUP_DRESTRICT; FMAPAUX_IN_COMPL; DISJOINT;
              EXTENSION; IN_INTER; NOT_IN_EMPTY; FDOM_FLOOKUP] THEN
  MESON_TAC[]);;

let fevery_funion = prove
 (`!(P:A#B->bool) m1 m2. FEVERY P m1 /\ FEVERY P m2 ==> FEVERY P (FUNION m1 m2)`,
  REWRITE_TAC[FEVERY_DEF; FUNION_DEF; IN_UNION] THEN MESON_TAC[]);;

let DISJOINT_FEVERY_FUNION = prove
 (`!(P:A#B->bool) m1 m2.
     DISJOINT (FDOM m1) (FDOM m2) ==>
     (FEVERY P (FUNION m1 m2) <=> FEVERY P m1 /\ FEVERY P m2)`,
  REWRITE_TAC[FEVERY_DEF; FUNION_DEF; IN_UNION; DISJOINT; EXTENSION; IN_INTER;
              NOT_IN_EMPTY] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* FDIFF: removes a whole bunch of keys at once.                             *)
(* ------------------------------------------------------------------------- *)

let FDIFF_def = new_definition
  `FDIFF (f1:(A,B)fmap) s = DRESTRICT f1 (COMPL s)`;;

let FDOM_FDIFF = prove
 (`!x (refs:(A,B)fmap) f2.
     x IN FDOM (FDIFF refs f2) <=> x IN FDOM refs /\ ~(x IN f2)`,
  REWRITE_TAC[FDIFF_def; FDOM_DRESTRICT; IN_INTER; FMAPAUX_IN_COMPL]);;

let FDOM_F_COMP_G_SUBSET_FDOM_G = prove
 (`!(f:(B,C)fmap) (g:(A,B)fmap). FDOM (f f_o_f g) SUBSET (FDOM g)`,
  REWRITE_TAC[f_o_f_DEF; INTER_SUBSET]);;

let FRANGE_SUBSET_FDOM_COMP_FDOM_EQUALITY = prove
 (`!(f:(B,C)fmap) (g:(A,B)fmap).
     FRANGE g SUBSET FDOM f ==> FDOM (f f_o_f g) = FDOM g`,
  REWRITE_TAC[f_o_f_DEF; FRANGE_DEF; SUBSET; EXTENSION; IN_INTER; IN_ELIM_THM] THEN
  MESON_TAC[]);;

let NUM_NOT_IN_FDOM = prove
 (`!f:(num,A)fmap. ?x. ~(x IN FDOM f)`,
  GEN_TAC THEN REWRITE_TAC[GSYM NOT_FORALL_THM] THEN DISCH_TAC THEN
  MP_TAC num_INFINITE THEN REWRITE_TAC[INFINITE] THEN
  SUBGOAL_THEN `(:num) = FDOM (f:(num,A)fmap)` SUBST1_TAC THENL
   [ASM SET_TAC[]; REWRITE_TAC[FDOM_FINITE]]);;

let LEAST_NOTIN_FDOM = prove
 (`!refs:(num,A)fmap. ~((minimal ptr. ~(ptr IN FDOM refs)) IN FDOM refs)`,
  GEN_TAC THEN MP_TAC(ISPEC `refs:(num,A)fmap` NUM_NOT_IN_FDOM) THEN
  REWRITE_TAC[MINIMAL] THEN MESON_TAC[]);;

let FLOOKUP_FDIFF = prove
 (`!(fm:(A,B)fmap) s k.
     FLOOKUP (FDIFF fm s) k = if k IN s then NONE else FLOOKUP fm k`,
  REWRITE_TAC[FDIFF_def; FLOOKUP_DRESTRICT; FMAPAUX_IN_COMPL] THEN
  MESON_TAC[]);;

let FDIFF_FDIFF = prove
 (`!(fm:(A,B)fmap) s1 s2. FDIFF (FDIFF fm s1) s2 = FDIFF fm (s1 UNION s2)`,
  REWRITE_TAC[fmap_eq_flookup; FLOOKUP_FDIFF; IN_UNION] THEN MESON_TAC[]);;

let FDIFF_FUNION = prove
 (`!(fm1:(A,B)fmap) fm2 s.
     FDIFF (FUNION fm1 fm2) s = FUNION (FDIFF fm1 s) (FDIFF fm2 s)`,
  REWRITE_TAC[fmap_eq_flookup; FLOOKUP_FDIFF; FLOOKUP_FUNION] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[option_CASE]);;

let FDIFF_FDOMSUB = prove
 (`!(f:(A,B)fmap) x p. FDIFF (f \\ x) p = FDIFF f p \\ x`,
  REWRITE_TAC[fmap_eq_flookup; FLOOKUP_FDIFF; DOMSUB_FLOOKUP_THM] THEN
  MESON_TAC[]);;

let FDIFF_FDOMSUB_INSERT = prove
 (`!(f:(A,B)fmap) x p. FDIFF (f \\ x) p = FDIFF f (x INSERT p)`,
  REWRITE_TAC[fmap_eq_flookup; FLOOKUP_FDIFF; DOMSUB_FLOOKUP_THM; IN_INSERT] THEN
  MESON_TAC[]);;

let FDIFF_BOUND = prove
 (`!(f:(A,B)fmap) p. FDIFF f p = FDIFF f (p INTER FDOM f)`,
  REWRITE_TAC[fmap_eq_flookup; FLOOKUP_FDIFF; IN_INTER; FDOM_FLOOKUP] THEN
  MESON_TAC[]);;

let FDIFF_FUPDATE = prove
 (`!(fm:(A,B)fmap) k v s.
     FDIFF (fm |+ (k,v)) s =
     if k IN s then FDIFF fm s else (FDIFF fm s) |+ (k,v)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[fmap_eq_flookup; FLOOKUP_FDIFF; FLOOKUP_UPDATE] THEN
  ASM_MESON_TAC[]);;

let FDIFF_FEMPTY = prove
 (`!s. FDIFF (FEMPTY:(A,B)fmap) s = FEMPTY`,
  REWRITE_TAC[fmap_eq_flookup; FLOOKUP_FDIFF; FLOOKUP_EMPTY; COND_ID]);;

let FDIFF_EMPTY = prove
 (`!f:(A,B)fmap. FDIFF f {} = f`,
  REWRITE_TAC[fmap_eq_flookup; FLOOKUP_FDIFF; NOT_IN_EMPTY]);;

let FDIFF_FMAP_MAP2 = prove
 (`!(f:A#B->C) (m:(A,B)fmap) s. FDIFF (FMAP_MAP2 f m) s = FMAP_MAP2 f (FDIFF m s)`,
  REWRITE_TAC[fmap_eq_flookup; FLOOKUP_FDIFF; FLOOKUP_FMAP_MAP2] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[OPTION_MAP_DEF]);;

(* FMINUS: FDIFF with the domain of a second map as the set of keys *)

let FMINUS_def = new_definition
  `FMINUS (fm1:(A,B)fmap) (fm2:(A,C)fmap) = FDIFF fm1 (FDOM fm2)`;;

let FLOOKUP_FMINUS = prove
 (`!(f1:(A,B)fmap) (f2:(A,C)fmap) k.
     FLOOKUP (FMINUS f1 f2) k = option_CASE (FLOOKUP f2 k) (FLOOKUP f1 k) (\v. NONE)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FMINUS_def; FLOOKUP_FDIFF; FDOM_FLOOKUP] THEN
  STRUCT_CASES_TAC(ISPEC `FLOOKUP (f2:(A,C)fmap) k` (cases "option")) THEN
  REWRITE_TAC[option_CASE; option_DISTINCT]);;

(* FINTER: keeps the entries whose keys are in the domain of a second map *)

let FINTER_def = new_definition
  `FINTER (f1:(A,B)fmap) (f2:(A,C)fmap) = DRESTRICT f1 (FDOM f2)`;;

let FLOOKUP_FINTER = prove
 (`!(f1:(A,B)fmap) (f2:(A,C)fmap) k.
     FLOOKUP (FINTER f1 f2) k = option_CASE (FLOOKUP f2 k) NONE (\v. FLOOKUP f1 k)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FINTER_def; FLOOKUP_DRESTRICT; FDOM_FLOOKUP] THEN
  STRUCT_CASES_TAC(ISPEC `FLOOKUP (f2:(A,C)fmap) k` (cases "option")) THEN
  REWRITE_TAC[option_CASE; option_DISTINCT]);;

(* ------------------------------------------------------------------------- *)
(* The FLOOKUP rewrites (HOL4 FLOOKUP_SIMP) and TO_FLOOKUP.                  *)
(* ------------------------------------------------------------------------- *)

let FLOOKUP_SIMP = end_itlist CONJ (map SPEC_ALL
  [FLOOKUP_EMPTY; FLOOKUP_UPDATE; FDIFF_def; FLOOKUP_FMAP_MAP2;
   FLOOKUP_DRESTRICT; FLOOKUP_FDIFF; FLOOKUP_FUNION; FLOOKUP_FUN_FMAP;
   FLOOKUP_FMERGE; FLOOKUP_FMINUS; FLOOKUP_FINTER]);;

let TO_FLOOKUP = prove
 (`!x (m:(A,B)fmap) y m' (P:A#B->bool).
     (x IN FDOM m <=> ~(FLOOKUP m x = NONE)) /\
     (y IN FRANGE m <=> ?k. FLOOKUP m k = SOME y) /\
     (~(FLOOKUP m x = NONE) ==> FAPPLY m x = THE (FLOOKUP m x)) /\
     (m = m' <=> FLOOKUP m = FLOOKUP m') /\
     (m SUBMAP m' <=> !k v. FLOOKUP m k = SOME v ==> FLOOKUP m' k = SOME v) /\
     (FEVERY P m <=> !k v. FLOOKUP m k = SOME v ==> P (k,v))`,
  REWRITE_TAC[FDOM_FLOOKUP; FRANGE_FLOOKUP; FAPPLY_FLOOKUP; FLOOKUP_EXT;
              SUBMAP_FLOOKUP_EQN; FEVERY_ALL_FLOOKUP]);;

(* ------------------------------------------------------------------------- *)
(* The HOL4 [simp] theorems of this theory, for the project simpset.         *)
(* ------------------------------------------------------------------------- *)

let _ = cake_add_simps
  [FAPPLY_FUPDATE; FUPDATE_EQ; FDOM_FEMPTY; FDOM_FUPDATE; NOT_EQ_FEMPTY_FUPDATE;
   FDOM_FINITE; SUBMAP_FEMPTY; SUBMAP_REFL; SUBMAP_FUPDATE_EQN;
   DRESTRICT_FEMPTY; DRESTRICT_FUPDATE; DRESTRICT_SUBMAP; DRESTRICT_DRESTRICT;
   SUBMAP_DRESTRICT; FDOM_FUNION; FUNION_FEMPTY_1; FUNION_FEMPTY_2;
   FUNION_IDEMPOT; FDOM_FMERGE; FLOOKUP_EMPTY; f_o_f_FEMPTY_1; f_o_f_FEMPTY_2;
   FDOM_o_f; o_f_FAPPLY; o_f_FEMPTY; o_f_id; o_f_o_f; FRANGE_FEMPTY;
   FINITE_FRANGE; o_f_FRANGE; FUN_FMAP_EMPTY; FRANGE_FMAP; FDOM_FMAP;
   DOMSUB_FEMPTY; DOMSUB_FUPDATE; FDOM_DOMSUB; DOMSUB_FAPPLY; DOMSUB_FLOOKUP;
   FRANGE_FUPDATE_DOMSUB; o_f_DOMSUB; DOMSUB_IDEM; o_f_FUPDATE; SUBMAP_DOMSUB;
   FUPDATE_PURGE'; DRESTRICT_IDEMPOT; MAP_KEYS_FEMPTY; fmap_rel_FEMPTY;
   fmap_rel_refl; FDOM_FDIFF; FDIFF_FEMPTY; FDIFF_EMPTY];;

(* ------------------------------------------------------------------------- *)
(* Lemmas used by several later files.                                       *)
(* ------------------------------------------------------------------------- *)

let FMAPAUX_FUPDATE_FLOOKUP_ELIM = prove
 (`!(f:(A,B)fmap) k v. FLOOKUP f k = SOME v ==> f |+ (k,v) = f`,
  REWRITE_TAC[FLOOKUP_DEF] THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[option_DISTINCT; option_INJ] THEN DISCH_TAC THEN
  MATCH_MP_TAC FUPDATE_ELIM THEN ASM_REWRITE_TAC[]);;
