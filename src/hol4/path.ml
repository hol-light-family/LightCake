(* ========================================================================= *)
(* path: port of HOL4 src/coalgebras/pathScript.sml (the HOL4 library used   *)
(* by CakeML v3479), the part the CakeML closure uses: possibly infinite     *)
(* paths, (A,B)path, isomorphic to A # (B # A) llist (a first state and a    *)
(* lazy list of label, state pairs), with first, stopped_at, pcons, okpath.  *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - okpath is HOL4's gfp (okpath_f R), defined here directly by its         *)
(*   coinduction invariant; okpath_co_ind, okpath_cases and okpath_thm are   *)
(*   HOL4's theorems.                                                        *)
(* - Not ported (unused by the closure): finite, last, length, el, pmap,     *)
(*   path_case, pconcat, PL, exists, every, ...                              *)
(* - Lemmas named LLISTAUX_... are helpers (not HOL4 names).                 *)
(* ========================================================================= *)

needs "hol4/vocab.ml";;
needs "hol4/llist.ml";;

let path_absrep_bijections = new_type_definition "path" ("toPath","fromPath")
 (prove(`?x:A#(B#A)llist. (\x. T) x`, REWRITE_TAC[]));;

let path_rep_bijections_thm = prove
 (`(!a:(A,B)path. toPath (fromPath a) = a) /\
   (!r:A#(B#A)llist. fromPath (toPath r) = r)`,
  REWRITE_TAC[REWRITE_RULE[] (BETA_RULE path_absrep_bijections)]);;

let toPath_11 = prove
 (`!r r':A#(B#A)llist. toPath r = toPath r' <=> r = r'`,
  MESON_TAC[path_rep_bijections_thm]);;

let fromPath_11 = prove
 (`!a a':(A,B)path. fromPath a = fromPath a' <=> a = a'`,
  MESON_TAC[path_rep_bijections_thm]);;

let fromPath_onto = prove
 (`!r:A#(B#A)llist. ?a:(A,B)path. r = fromPath a`,
  MESON_TAC[path_rep_bijections_thm]);;

let toPath_onto = prove
 (`!a:(A,B)path. ?r:A#(B#A)llist. a = toPath r`,
  MESON_TAC[path_rep_bijections_thm]);;

let first_def = new_definition
  `first (p:(A,B)path) = FST (fromPath p)`;;

let stopped_at_def = new_definition
  `stopped_at (x:A) = (toPath (x, LNIL:(B#A)llist) :(A,B)path)`;;

let pcons_def = new_definition
  `pcons (x:A) (r:B) (p:(A,B)path) =
     (toPath (x, LCONS (r, first p) (SND (fromPath p))) :(A,B)path)`;;

let stopped_at_11 = prove
 (`!x y:A. (stopped_at x = (stopped_at y:(A,B)path)) <=> x = y`,
  REWRITE_TAC[stopped_at_def; toPath_11; PAIR_EQ]);;

let LLISTAUX_PAIR_FST_SND_EQ = prove
 (`!p q:A#B. p = q <=> FST p = FST q /\ SND p = SND q`,
  REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ]);;

let pcons_11 = prove
 (`!(x:A) (r:B) p y s q.
     pcons x r p = pcons y s q <=> x = y /\ r = s /\ p = q`,
  REWRITE_TAC[pcons_def; toPath_11; PAIR_EQ; LCONS_11; first_def] THEN
  REWRITE_TAC[GSYM fromPath_11] THEN
  REWRITE_TAC[LLISTAUX_PAIR_FST_SND_EQ; CONJ_ASSOC]);;

let stopped_at_not_pcons = prove
 (`!(x:A) y (r:B) p. ~(stopped_at x = pcons y r p) /\ ~(pcons y r p = stopped_at x)`,
  REWRITE_TAC[stopped_at_def; pcons_def; toPath_11; PAIR_EQ; LCONS_NOT_NIL]);;

let path_cases = prove
 (`!p:(A,B)path. (?x. p = stopped_at x) \/ (?x r q. p = pcons x r q)`,
  GEN_TAC THEN
  MP_TAC(ISPEC `p:(A,B)path` toPath_onto) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:A#(B#A)llist` SUBST1_TAC) THEN
  SUBST1_TAC(ISPEC `r:A#(B#A)llist` (GSYM PAIR)) THEN
  SPEC_TAC(`SND (r:A#(B#A)llist)`,`l:(B#A)llist`) THEN
  SPEC_TAC(`FST (r:A#(B#A)llist)`,`a:A`) THEN
  REPEAT GEN_TAC THEN LLIST_CASE_TAC `l:(B#A)llist` THENL
   [DISJ1_TAC THEN EXISTS_TAC `a:A` THEN REWRITE_TAC[stopped_at_def];
    DISJ2_TAC THEN
    MAP_EVERY EXISTS_TAC [`a:A`; `FST (h:B#A)`; `toPath (SND (h:B#A), t):(A,B)path`] THEN
    REWRITE_TAC[pcons_def; first_def; path_rep_bijections_thm; PAIR]]);;

let FORALL_path = prove
 (`!P. (!p:(A,B)path. P p) <=> (!x. P (stopped_at x)) /\ (!x r p. P (pcons x r p))`,
  MESON_TAC[path_cases]);;

let EXISTS_path = prove
 (`!P. (?p:(A,B)path. P p) <=> (?x. P (stopped_at x)) \/ (?x r p. P (pcons x r p))`,
  MESON_TAC[path_cases]);;

let first_thm = prove
 (`(!x:A. first (stopped_at x:(A,B)path) = x) /\
   (!(x:A) (r:B) p. first (pcons x r p) = x)`,
  REWRITE_TAC[first_def; stopped_at_def; pcons_def; path_rep_bijections_thm]);;

(* okpath: HOL4 defines it as the greatest fixpoint gfp (okpath_f R); here it *)
(* is defined directly by its coinduction invariant (the same set).          *)

let okpath_def = new_definition
  `okpath (R:A->B->A->bool) (p:(A,B)path) <=>
     ?P. P p /\
         !q. P q ==> (?x. q = stopped_at x) \/
                     (?x r q'. q = pcons x r q' /\ R x r (first q') /\ P q')`;;

let okpath_co_ind = prove
 (`!P. (!(x:A) (r:B) p. P (pcons x r p) ==> R x r (first p) /\ P p) ==>
       !p. P p ==> okpath R p`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[okpath_def] THEN
  EXISTS_TAC `P:(A,B)path->bool` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `q:(A,B)path` THEN DISCH_TAC THEN
  MP_TAC(ISPEC `q:(A,B)path` path_cases) THEN STRIP_TAC THENL
   [DISJ1_TAC THEN ASM_MESON_TAC[];
    DISJ2_TAC THEN ASM_MESON_TAC[]]);;

let okpath_cases = prove
 (`!R (p:(A,B)path).
     okpath R p <=>
     (?x. p = stopped_at x) \/
     (?x r q. p = pcons x r q /\ R x r (first q) /\ okpath R q)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[okpath_def] THEN
    DISCH_THEN(X_CHOOSE_THEN `P:(A,B)path->bool` STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP th (ASSUME `(P:(A,B)path->bool) p`))) THEN
    STRIP_TAC THENL
     [DISJ1_TAC THEN ASM_MESON_TAC[];
      DISJ2_TAC THEN MAP_EVERY EXISTS_TAC [`x:A`; `r:B`; `q':(A,B)path`] THEN
      ASM_REWRITE_TAC[] THEN EXISTS_TAC `P:(A,B)path->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_TAC THEN REWRITE_TAC[okpath_def] THEN
  EXISTS_TAC `\q:(A,B)path. q = p \/ okpath R q` THEN REWRITE_TAC[] THEN
  X_GEN_TAC `q:(A,B)path` THEN STRIP_TAC THENL
   [POP_ASSUM SUBST1_TAC THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
     [DISJ1_TAC THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[];
      DISJ2_TAC THEN MAP_EVERY EXISTS_TAC [`x:A`; `r:B`; `q:(A,B)path`] THEN
      ASM_REWRITE_TAC[]];
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[okpath_def]) THEN
    DISCH_THEN(X_CHOOSE_THEN `Q:(A,B)path->bool` STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP th (ASSUME `(Q:(A,B)path->bool) q`))) THEN
    STRIP_TAC THENL
     [DISJ1_TAC THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[];
      DISJ2_TAC THEN
      MAP_EVERY EXISTS_TAC [`x:A`; `r:B`; `q':(A,B)path`] THEN
      ASM_REWRITE_TAC[okpath_def] THEN DISJ2_TAC THEN
      EXISTS_TAC `Q:(A,B)path->bool` THEN ASM_REWRITE_TAC[]]]);;

let okpath_thm = prove
 (`!R. (!x:A. okpath R (stopped_at x:(A,B)path)) /\
       (!(x:A) (r:B) p. okpath R (pcons x r p) <=> R x r (first p) /\ okpath R p)`,
  GEN_TAC THEN CONJ_TAC THEN REPEAT GEN_TAC THENL
   [ONCE_REWRITE_TAC[okpath_cases]; GEN_REWRITE_TAC LAND_CONV [okpath_cases]] THEN
  REWRITE_TAC[stopped_at_not_pcons; pcons_11; stopped_at_11] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The HOL4 [simp] theorems of this file (HOL4 also adds                     *)
(* path_rep_bijections_thm, toPath_11 and fromPath_11 to srw_ss).            *)
(* ------------------------------------------------------------------------- *)

let _ = cake_add_simps
  [path_rep_bijections_thm; toPath_11; fromPath_11; stopped_at_11; pcons_11;
   stopped_at_not_pcons; first_thm; okpath_thm];;
