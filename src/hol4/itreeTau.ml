(* ========================================================================= *)
(* itreeTau: port of HOL4 src/coalgebras/itreeTauScript.sml (the HOL4       *)
(* library theory that CakeML v3479's Pancake semantics uses).               *)
(* Potentially infinite interaction trees, after Xia et al., POPL 2020:     *)
(*   (A,E,R) itree = itree_Ret R | Tau ((A,E,R) itree)                       *)
(*                 | Vis E (A -> (A,E,R) itree)                              *)
(* (A: answers, E: events, R: results).                                      *)
(*                                                                           *)
(* As in HOL4, (A,E,R) itree is a new_type_definition over the functions    *)
(* from paths ((A option) list, NONE for a silent step) to (E,R) itree_el   *)
(* that are Silence off the well-formed paths (itree_rep_ok); itree_unfold  *)
(* builds trees corecursively, and itree_bisimulation and                   *)
(* itree_strong_bisimulation prove them equal.  itree_wbisim, and the       *)
(* relations strong_bisim_upfrom_abs and weak_bisim_upfrom_abs, are HOL     *)
(* Light new_coinductive_definitions (rules, coind, cases as in HOL4);      *)
(* strip_tau and after_taus are inductive.                                   *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - Names from notes/naming/names.tsv: HOL4 Ret is itree_Ret (bviSem has a  *)
(*   constructor Ret) and Return is itree_Return; theorems that OCaml would *)
(*   read as constructors take the prefix itree_ (itree_Ret_def,            *)
(*   itree_Tau_11, ...).  HOL4's 'seed is S (itree_next is (A,E,R,S)).     *)
(* - itree is registered by hand as a case type (after itree_CASE_elim):    *)
(*   CASES_ON, TOP_CASE_TAC, match patterns, case_eq "itree" and the         *)
(*   simpset work on it as on a datatype; HOL Light's rectype net has its   *)
(*   distinctness and injectivity (MATCH_CONV, definitions by clauses).     *)
(* - HOL4 definitions that the script rebinds to theorems of the same name  *)
(*   are ITREEAUX_itree_CASE_def, ITREEAUX_itree_unfold_def and             *)
(*   ITREEAUX_spin_def; the theorems itree_CASE, itree_unfold and spin are  *)
(*   HOL4's.  HOL4's TYPE_DEFINITION is unfolded in itree_TY_DEF.           *)
(* - FUNPOW f n x is ITER n f x; HOL4 () is one; rel_to_reln R is UNCURRY R  *)
(*   and reln_to_rel r is CURRY r.  HOL4's fixedPoint and companion         *)
(*   theories are not ported: the few items used here (monotone, gfp,       *)
(*   set_compatible, set_companion and five facts) are local copies         *)
(*   ITREEAUX_....  HOL4's variables abs, abs' are ab, ab' (abs is a HOL     *)
(*   Light constant).                                                        *)
(* - Not ported: untau and untau_spin, untau_IMP_wbisim, wbisim_IMP_untau    *)
(*   (untau maps into HOL4's other itree type, of theory itree, which no     *)
(*   theory of the port uses); datatype_itree (a TypeBase marker).          *)
(* - Lemmas named ITREEAUX_... are helpers of this file (not HOL4 names).    *)
(* ========================================================================= *)

needs "hol4/vocab.ml";;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The representation: a tree is the function from paths (lists of answers, *)
(* NONE for a silent step) to the element at the end of the path.            *)
(* ------------------------------------------------------------------------- *)

let _ = cake_type "itree_el = Event E | itree_Return R | Silence";;

let path_ok_def = cake_def
 `path_ok (path:(A option)list) (f:(A option)list->(E,R)itree_el) <=>
    !xs y ys.
      path = APPEND xs (CONS y ys) ==>
      match f xs with
        itree_Return _ -> F
      | Silence -> y = NONE
      | Event e -> IS_SOME y`;;

let itree_rep_ok_def = cake_def
 `itree_rep_ok (f:(A option)list->(E,R)itree_el) <=>
    !path. ~path_ok path f ==> f path = Silence`;;

let type_inhabited = prove
 (`?f:(A option)list->(E,R)itree_el. itree_rep_ok f`,
  QEXISTS_TAC "\p. Silence" THEN FS[itree_rep_ok_def]);;

let itree_absrep =
  new_type_definition "itree" ("itree_abs","itree_rep") type_inhabited;;

(* HOL4's itree_TY_DEF  ?rep. TYPE_DEFINITION itree_rep_ok rep, with HOL4's *)
(* TYPE_DEFINITION unfolded                                                  *)

let itree_TY_DEF = prove
 (`?rep:(A,E,R)itree->(A option)list->(E,R)itree_el.
     (!x' x''. rep x' = rep x'' ==> x' = x'') /\
     (!x. itree_rep_ok x <=> ?x'. x = rep x')`,
  EXISTS_TAC `itree_rep:(A,E,R)itree->(A option)list->(E,R)itree_el` THEN
  MESON_TAC[itree_absrep]);;

(* HOL4's itree_repabs (an ML binding of CONJUNCT2 itree_absrep) *)

let ITREEAUX_itree_repabs = CONJUNCT2 itree_absrep;;

let itree_rep_ok_itree_rep = prove
 (`!t:(A,E,R)itree. itree_rep_ok (itree_rep t)`,
  MESON_TAC[itree_absrep]);;

let itree_abs_11 = prove
 (`!r1 r2:(A option)list->(E,R)itree_el.
     itree_rep_ok r1 /\ itree_rep_ok r2 ==>
     (itree_abs r1 = itree_abs r2 <=> r1 = r2)`,
  MESON_TAC[itree_absrep]);;

let itree_rep_11 = prove
 (`!t1 t2:(A,E,R)itree. itree_rep t1 = itree_rep t2 <=> t1 = t2`,
  MESON_TAC[itree_absrep]);;

(* ------------------------------------------------------------------------- *)
(* The constructors.                                                         *)
(* ------------------------------------------------------------------------- *)

let itree_Ret_rep_def = cake_def
 `Ret_rep (x:R) =
    \path:(A option)list. if path = [] then itree_Return x
                          else (Silence:(E,R)itree_el)`;;

let itree_Tau_rep_def = cake_def
 `Tau_rep (f:(A option)list->(E,R)itree_el) =
    \path. match path with
             CONS NONE rest -> f rest
           | _ -> Silence`;;

let itree_Vis_rep_def = cake_def
 `Vis_rep (e:E) (g:A->(A option)list->(E,R)itree_el) =
    \path. match path with
             [] -> Event e
           | CONS NONE rest -> Silence
           | CONS (SOME a) rest -> g a rest`;;

let itree_Ret_def = cake_def
 `itree_Ret (x:R) = itree_abs (Ret_rep x):(A,E,R)itree`;;

let itree_Tau_def = cake_def
 `Tau (t:(A,E,R)itree) = itree_abs (Tau_rep (itree_rep t))`;;

let itree_Vis_def = cake_def
 `Vis (e:E) (g:A->(A,E,R)itree) = itree_abs (Vis_rep e (itree_rep o g))`;;

(* path_ok by recursion on the path (helpers for the rep_ok proofs) *)

let ITREEAUX_path_ok_NIL = prove
 (`!f:(A option)list->(E,R)itree_el. path_ok [] f`,
  REWRITE_TAC[path_ok_def] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o SYM) THEN REWRITE_TAC[APPEND_EQ_NIL; NOT_CONS_NIL]);;

let ITREEAUX_path_ok_CONS = prove(CASE_TERM
 `!h t f:(A option)list->(E,R)itree_el.
    path_ok (CONS h t) f <=>
    (match f [] with
       itree_Return _ -> F
     | Silence -> h = NONE
     | Event e -> IS_SOME h) /\
    path_ok t (\p. f (CONS h p))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[path_ok_def] THEN EQ_TAC THENL
   [DISCH_TAC THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL
        [`[]:(A option)list`; `h:A option`; `t:(A option)list`]) THEN
      REWRITE_TAC[APPEND];
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL
        [`CONS (h:A option) xs`; `y:A option`; `ys:(A option)list`]) THEN
      ASM_REWRITE_TAC[APPEND]];
    STRIP_TAC THEN X_GEN_TAC `xs:(A option)list` THEN
    STRUCT_CASES_TAC(ISPEC `xs:(A option)list` list_CASES) THEN
    REWRITE_TAC[APPEND; CONS_11] THEN REPEAT STRIP_TAC THEN
    ASM_MESON_TAC[]]);;

let itree_rep_ok_Ret = prove
 (`!x:R. itree_rep_ok (Ret_rep x:(A option)list->(E,R)itree_el)`,
  REWRITE_TAC[itree_rep_ok_def; itree_Ret_rep_def] THEN REPEAT GEN_TAC THEN
  QCASES_ON "path" THEN SIMP[ITREEAUX_path_ok_NIL]);;

let itree_rep_ok_Tau = prove
 (`!f:(A option)list->(E,R)itree_el.
     itree_rep_ok f ==> itree_rep_ok (Tau_rep f)`,
  REWRITE_TAC[itree_rep_ok_def] THEN REPEAT STRIP_TAC THEN
  QCASES_ON "path" THEN SIMP[itree_Tau_rep_def] THEN
  QCASES_ON "a0" THEN SIMP[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_X_ASSUM MP_TAC THEN
  SIMP[ITREEAUX_path_ok_CONS; itree_Tau_rep_def; ETA_AX]);;

let itree_rep_ok_Vis = prove
 (`!(a:A) g. (!a. itree_rep_ok (g a)) ==>
             itree_rep_ok (Vis_rep (e:E) g:(A option)list->(E,R)itree_el)`,
  REWRITE_TAC[itree_rep_ok_def] THEN REPEAT STRIP_TAC THEN
  QCASES_ON "path" THEN FS[ITREEAUX_path_ok_NIL; itree_Vis_rep_def] THEN
  QCASES_ON "a0" THEN SIMP[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_X_ASSUM MP_TAC THEN
  SIMP[ITREEAUX_path_ok_CONS; itree_Vis_rep_def; ETA_AX; IS_SOME_DEF]);;

(* the representations of the constructors (helpers) *)

let ITREEAUX_itree_rep_Ret = prove
 (`!x:R. itree_rep (itree_Ret x:(A,E,R)itree) = Ret_rep x`,
  MESON_TAC[itree_Ret_def; ITREEAUX_itree_repabs; itree_rep_ok_Ret]);;

let ITREEAUX_itree_rep_Tau = prove
 (`!t:(A,E,R)itree. itree_rep (Tau t) = Tau_rep (itree_rep t)`,
  MESON_TAC[itree_Tau_def; ITREEAUX_itree_repabs; itree_rep_ok_Tau;
            itree_rep_ok_itree_rep]);;

let ITREEAUX_itree_rep_Vis = prove
 (`!(e:E) (g:A->(A,E,R)itree).
     itree_rep (Vis e g) = Vis_rep e (itree_rep o g)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[itree_Vis_def] THEN
  REWRITE_TAC[GSYM ITREEAUX_itree_repabs] THEN
  MATCH_MP_TAC itree_rep_ok_Vis THEN
  REWRITE_TAC[o_THM; itree_rep_ok_itree_rep]);;

(* prove injectivity *)

let itree_Ret_rep_11 = prove
 (`!x y:R. (Ret_rep x:(A option)list->(E,R)itree_el) = Ret_rep y <=> x = y`,
  REWRITE_TAC[itree_Ret_rep_def; FUN_EQ_THM] THEN REPEAT GEN_TAC THEN
  EQ_TAC THEN SIMP[] THEN DISCH_THEN(MP_TAC o SPEC `[]:(A option)list`) THEN
  SIMP[]);;

let itree_Ret_11 = prove
 (`!x y:R. (itree_Ret x:(A,E,R)itree) = itree_Ret y <=> x = y`,
  REWRITE_TAC[GSYM itree_rep_11; ITREEAUX_itree_rep_Ret; itree_Ret_rep_11]);;

let itree_Tau_rep_11 = prove
 (`!x y:(A option)list->(E,R)itree_el. Tau_rep x = Tau_rep y <=> x = y`,
  REWRITE_TAC[itree_Tau_rep_def; FUN_EQ_THM] THEN REPEAT GEN_TAC THEN
  EQ_TAC THEN SIMP[] THEN DISCH_TAC THEN X_GEN_TAC `path:(A option)list` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `CONS (NONE:A option) path`) THEN SIMP[]);;

let itree_Tau_11 = prove
 (`!x y:(A,E,R)itree. Tau x = Tau y <=> x = y`,
  REWRITE_TAC[GSYM itree_rep_11; ITREEAUX_itree_rep_Tau; itree_Tau_rep_11]);;

let itree_Vis_rep_11 = prove
 (`!(x:E) y (g:A->(A option)list->(E,R)itree_el) g'.
     Vis_rep x g = Vis_rep y g' <=> x = y /\ g = g'`,
  REWRITE_TAC[itree_Vis_rep_def] THEN REPEAT GEN_TAC THEN
  EQ_TAC THEN SIMP[] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o C AP_THM `[]:(A option)list`) THEN
  SIMP[] THEN DISCH_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `path:(A option)list`] THEN
  FIRST_X_ASSUM(MP_TAC o C AP_THM `CONS (SOME (a:A)) path`) THEN SIMP[]);;

let itree_Vis_11 = prove
 (`!(x:E) (f:A->(A,E,R)itree) y g. Vis x f = Vis y g <=> x = y /\ f = g`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM itree_rep_11; ITREEAUX_itree_rep_Vis; itree_Vis_rep_11] THEN
  AP_TERM_TAC THEN EQ_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  DISCH_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `a:A` THEN
  FIRST_X_ASSUM(MP_TAC o C AP_THM `a:A`) THEN REWRITE_TAC[o_THM; itree_rep_11]);;

let itree_11 = end_itlist CONJ [itree_Ret_11; itree_Tau_11; itree_Vis_11];;

(* distinctness theorem *)

let itree_distinct_lemma = prove
 (`!x t (e:E) (g:A->(A,E,R)itree).
     ALL_DISTINCT [itree_Ret x; Tau t; Vis e g]`,
  REWRITE_TAC[ALL_DISTINCT; MEM; DE_MORGAN_THM] THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[GSYM itree_rep_11] THEN
  REWRITE_TAC[ITREEAUX_itree_rep_Ret; ITREEAUX_itree_rep_Tau;
              ITREEAUX_itree_rep_Vis] THEN
  REPEAT CONJ_TAC THEN DISCH_THEN(MP_TAC o C AP_THM `[]:(A option)list`) THEN
  SIMP[itree_Ret_rep_def; itree_Tau_rep_def; itree_Vis_rep_def]);;

let itree_distinct = prove
 (`(!(x:R) t:(A,E,R)itree. ~(itree_Ret x = Tau t)) /\
   (!(x:R) (e:E) (g:A->(A,E,R)itree). ~(itree_Ret x = Vis e g)) /\
   (!t (e:E) (g:A->(A,E,R)itree). ~(Tau t = Vis e g))`,
  MP_TAC itree_distinct_lemma THEN
  REWRITE_TAC[ALL_DISTINCT; MEM; DE_MORGAN_THM] THEN MESON_TAC[]);;

(* prove cases theorem *)

let rep_exists = prove
 (`!f:(A option)list->(E,R)itree_el.
     itree_rep_ok f ==>
     (?x. f = Ret_rep x) \/
     (?u. f = Tau_rep u /\ itree_rep_ok u) \/
     (?a g. f = Vis_rep a g /\ !v. itree_rep_ok (g v))`,
  GEN_TAC THEN REWRITE_TAC[itree_rep_ok_def] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!h t. ~path_ok (CONS h t) (f:(A option)list->(E,R)itree_el)
                      ==> f (CONS h t) = Silence` MP_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[ITREEAUX_path_ok_CONS] THEN DISCH_TAC THEN
  QCASES_ON "(f:(A option)list->(E,R)itree_el) []" THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[IS_SOME_DEF]) THENL
   [DISJ2_TAC THEN DISJ2_TAC THEN
    MAP_EVERY EXISTS_TAC
     [`a:E`; `\(x:A) p. (f:(A option)list->(E,R)itree_el) (CONS (SOME x) p)`] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; itree_Vis_rep_def] THEN
      X_GEN_TAC `path:(A option)list` THEN QCASES_ON "path" THEN SIMP[] THEN
      QCASES_ON "a0" THEN SIMP[IS_SOME_DEF];
      SIMP[IS_SOME_DEF]];
    DISJ1_TAC THEN QEXISTS_TAC "a" THEN
    REWRITE_TAC[FUN_EQ_THM; itree_Ret_rep_def] THEN
    X_GEN_TAC `path:(A option)list` THEN QCASES_ON "path" THEN SIMP[];
    DISJ2_TAC THEN DISJ1_TAC THEN
    QEXISTS_TAC "\p. (f:(A option)list->(E,R)itree_el) (CONS NONE p)" THEN
    CONJ_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; itree_Tau_rep_def] THEN
      X_GEN_TAC `path:(A option)list` THEN QCASES_ON "path" THEN SIMP[] THEN
      QCASES_ON "a0" THEN SIMP[IS_SOME_DEF];
      SIMP[]]]);;

let itree_cases = prove
 (`!t:(A,E,R)itree. (?x. t = itree_Ret x) \/ (?u. t = Tau u) \/
                    (?a g. t = Vis a g)`,
  GEN_TAC THEN
  MP_TAC(ISPEC `itree_rep (t:(A,E,R)itree)` rep_exists) THEN
  REWRITE_TAC[itree_rep_ok_itree_rep] THEN STRIP_TAC THENL
   [DISJ1_TAC THEN EXISTS_TAC `x:R` THEN
    ASM_REWRITE_TAC[GSYM itree_rep_11; ITREEAUX_itree_rep_Ret];
    DISJ2_TAC THEN DISJ1_TAC THEN
    EXISTS_TAC `itree_abs (u:(A option)list->(E,R)itree_el)` THEN
    REWRITE_TAC[GSYM itree_rep_11; ITREEAUX_itree_rep_Tau] THEN
    ASM_MESON_TAC[ITREEAUX_itree_repabs];
    DISJ2_TAC THEN DISJ2_TAC THEN
    MAP_EVERY EXISTS_TAC
     [`a:E`; `itree_abs o (g:A->(A option)list->(E,R)itree_el)`] THEN
    REWRITE_TAC[GSYM itree_rep_11; ITREEAUX_itree_rep_Vis] THEN
    ASM_REWRITE_TAC[itree_Vis_rep_11] THEN
    REWRITE_TAC[FUN_EQ_THM; o_THM] THEN
    ASM_MESON_TAC[ITREEAUX_itree_repabs]]);;

(* itree_CASE constant (HOL4's definition is rebound to the theorem         *)
(* itree_CASE below; the definition itself is ITREEAUX_itree_CASE_def)       *)

let ITREEAUX_itree_CASE_def = cake_def
 `itree_CASE (t:(A,E,R)itree) (ret:R->Z) (tau:(A,E,R)itree->Z)
             (vis:E->(A->(A,E,R)itree)->Z) =
    match itree_rep t [] with
      itree_Return r -> ret r
    | Silence -> tau (itree_abs (\path. itree_rep t (CONS NONE path)))
    | Event e -> vis e (\a. itree_abs (\path. itree_rep t (CONS (SOME a) path)))`;;

let itree_CASE = prove
 (`(!(r:R) (ret:R->Z) tau vis.
      itree_CASE (itree_Ret r:(A,E,R)itree) ret tau vis = ret r) /\
   (!(t:(A,E,R)itree) (ret:R->Z) tau vis.
      itree_CASE (Tau t) ret tau vis = tau t) /\
   (!(a:E) (g:A->(A,E,R)itree) (ret:R->Z) tau vis.
      itree_CASE (Vis a g) ret tau vis = vis a g)`,
  REWRITE_TAC[ITREEAUX_itree_CASE_def; ITREEAUX_itree_rep_Ret;
              ITREEAUX_itree_rep_Tau; ITREEAUX_itree_rep_Vis] THEN
  SIMP[itree_Ret_rep_def; itree_Tau_rep_def; itree_Vis_rep_def; o_THM;
       ETA_AX; itree_absrep]);;

let itree_CASE_eq = prove
 (`!t:(A,E,R)itree (ret:R->Z) tau vis v.
     itree_CASE t ret tau vis = v <=>
     (?r. t = itree_Ret r /\ ret r = v) \/
     (?u. t = Tau u /\ tau u = v) \/
     (?a g. t = Vis a g /\ vis a g = v)`,
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `t:(A,E,R)itree` itree_cases) THEN
  REWRITE_TAC[itree_CASE; itree_11; itree_distinct] THEN MESON_TAC[]);;

let itree_CASE_elim = prove
 (`!f t:(A,E,R)itree (ret:R->Z) tau vis.
     f (itree_CASE t ret tau vis) <=>
     (?r. t = itree_Ret r /\ f (ret r)) \/
     (?u. t = Tau u /\ f (tau u)) \/
     (?a g. t = Vis a g /\ f (vis a g))`,
  GEN_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `t:(A,E,R)itree` itree_cases) THEN
  REWRITE_TAC[itree_CASE; itree_11; itree_distinct] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* itree as a case type (HOL4: TypeBase.export below), registered by hand    *)
(* since it is not a HOL Light datatype: with the kit (case constant,       *)
(* nchotomy, case_eq: CASES_ON, TOP_CASE_TAC, match patterns, case_eq       *)
(* "itree", all_case_eqs, the simpset and the case net) and with HOL Light's *)
(* rectype net and distinctness/injectivity stores (MATCH_CONV and the      *)
(* recursion package simplify itree constructor equations with them).       *)
(* ------------------------------------------------------------------------- *)

let itree_case_info =
  let ds = CONJUNCTS itree_distinct and is = CONJUNCTS itree_11 in
  let ci = { ci_tyname = "itree";
             ci_case = mk_const("itree_CASE",[]);
             ci_def = itree_CASE;
             ci_pats = patterns_of_nchotomy itree_cases;
             ci_nchotomy = itree_cases;
             ci_case_eq = itree_CASE_eq;
             ci_match = ref None;
             ci_distinct = ds @ map sym_neg ds;
             ci_inject = is } in
  the_case_infos := ("itree",ci) :: !the_case_infos;
  distinctness_store := ("itree",fun () -> itree_distinct) :: !distinctness_store;
  injectivity_store := ("itree",itree_11) :: !injectivity_store;
  basic_rectype_net :=
    itlist (net_of_thm true)
           (itlist (mk_rewrites false) [itree_distinct; itree_11] [])
           (!basic_rectype_net);
  cake_register_type_simps "itree";
  cake_update_case_net();
  ci;;

(* ------------------------------------------------------------------------- *)
(* itree unfold.  HOL4's type variable 'seed is S.                           *)
(* ------------------------------------------------------------------------- *)

let _ = cake_type "itree_next = Ret' R | Tau' S | Vis' E (A -> S)";;

let itree_unfold_path_def = cake_def
 `(itree_unfold_path (f:S->(A,E,R,S)itree_next) seed [] =
     match f seed with
       Ret' r -> itree_Return r
     | Tau' s -> Silence
     | Vis' e g -> Event e) /\
  (itree_unfold_path f seed (CONS NONE rest) =
     match f seed with
       Ret' r -> Silence
     | Tau' s -> itree_unfold_path f s rest
     | Vis' e g -> Silence) /\
  (itree_unfold_path f seed (CONS (SOME n) rest) =
     match f seed with
       Ret' r -> Silence
     | Tau' s -> Silence
     | Vis' e g -> itree_unfold_path f (g n) rest)`;;

let itree_unfold_path_ind = cake_ind "itree_unfold_path";;

(* HOL4's definition itree_unfold, rebound to the theorem itree_unfold below *)

let ITREEAUX_itree_unfold_def = cake_def
 `itree_unfold (f:S->(A,E,R,S)itree_next) seed =
    itree_abs (itree_unfold_path f seed):(A,E,R)itree`;;

let itree_rep_abs_itree_unfold_path = prove
 (`!(f:S->(A,E,R,S)itree_next) s.
     itree_rep (itree_abs (itree_unfold_path f s)) = itree_unfold_path f s`,
  REWRITE_TAC[GSYM ITREEAUX_itree_repabs; itree_rep_ok_def] THEN
  GEN_TAC THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[ITREEAUX_path_ok_NIL; ITREEAUX_path_ok_CONS] THEN
  X_GEN_TAC `s:S` THEN QCASES_ON "h" THEN
  QCASES_ON "(f:S->(A,E,R,S)itree_next) s" THEN
  SIMP[itree_unfold_path_def; ETA_AX; IS_SOME_DEF]);;

let itree_unfold = prove(CASE_TERM
 `!(f:S->(A,E,R,S)itree_next) seed.
    itree_unfold f seed =
    match f seed with
      Ret' r -> itree_Ret r
    | Tau' s -> Tau (itree_unfold f s)
    | Vis' e g -> Vis e (itree_unfold f o g)`,
  REPEAT GEN_TAC THEN QCASES_ON "(f:S->(A,E,R,S)itree_next) seed" THEN
  SIMP[ITREEAUX_itree_unfold_def; itree_Ret_def; itree_Tau_def; itree_Vis_def;
       itree_rep_abs_itree_unfold_path] THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  X_GEN_TAC `path:(A option)list` THEN NAMED_CASES_ON "path" [""; "h t"] THEN
  TRY(NAMED_CASES_ON "h" [""; "x"]) THEN
  SIMP[itree_unfold_path_def; itree_Ret_rep_def; itree_Tau_rep_def;
       itree_Vis_rep_def; o_THM; ITREEAUX_itree_unfold_def;
       itree_rep_abs_itree_unfold_path]);;

(* proving equivalences *)

let itree_el_thm = prove
 (`(!r:R. itree_rep (itree_Ret r:(A,E,R)itree) [] = itree_Return r) /\
   (!t:(A,E,R)itree. itree_rep (Tau t) [] = Silence) /\
   (!(e:E) (g:A->(A,E,R)itree). itree_rep (Vis e g) [] = Event e) /\
   (!(r:R) ns. itree_rep (itree_Ret r:(A,E,R)itree) (CONS NONE ns) = Silence) /\
   (!(t:(A,E,R)itree) ns. itree_rep (Tau t) (CONS NONE ns) = itree_rep t ns) /\
   (!(e:E) (g:A->(A,E,R)itree) ns.
      itree_rep (Vis e g) (CONS NONE ns) = Silence) /\
   (!(r:R) a ns.
      itree_rep (itree_Ret r:(A,E,R)itree) (CONS (SOME a) ns) = Silence) /\
   (!(t:(A,E,R)itree) a ns. itree_rep (Tau t) (CONS (SOME a) ns) = Silence) /\
   (!(e:E) (g:A->(A,E,R)itree) a ns.
      itree_rep (Vis e g) (CONS (SOME a) ns) = itree_rep (g a) ns)`,
  SIMP[ITREEAUX_itree_rep_Ret; ITREEAUX_itree_rep_Tau; ITREEAUX_itree_rep_Vis;
       itree_Ret_rep_def; itree_Tau_rep_def; itree_Vis_rep_def; o_THM]);;
let _ = cake_add_simps [itree_el_thm];;

let itree_bisimulation = prove
 (`!t1 t2:(A,E,R)itree.
     t1 = t2 <=>
     ?R. R t1 t2 /\
         (!x t. R (itree_Ret x) t ==> t = itree_Ret x) /\
         (!u t. R (Tau u) t ==> ?v. t = Tau v /\ R u v) /\
         (!a f t. R (Vis a f) t ==> ?g. t = Vis a g /\ !s. R (f s) (g s))`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN SUBST1_TAC THEN
    EXISTS_TAC `(=):(A,E,R)itree->(A,E,R)itree->bool` THEN MESON_TAC[];
    STRIP_TAC] THEN
  ONCE_REWRITE_TAC[GSYM itree_rep_11] THEN REWRITE_TAC[FUN_EQ_THM] THEN
  X_GEN_TAC `path:(A option)list` THEN
  UNDISCH_TAC `R (t1:(A,E,R)itree) (t2:(A,E,R)itree):bool` THEN
  MAP_EVERY (fun t -> SPEC_TAC(t,t))
    [`t2:(A,E,R)itree`; `t1:(A,E,R)itree`; `path:(A option)list`] THEN
  LIST_INDUCT_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `t1:(A,E,R)itree` itree_cases) THEN
  GEN_TAC THEN DISCH_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[itree_el_thm] THEN
  TRY(NAMED_CASES_ON "h" [""; "x"]) THEN ASM_REWRITE_TAC[itree_el_thm] THEN
  ASM_MESON_TAC[]);;

let itree_strong_bisimulation = prove
 (`!t1 t2:(A,E,R)itree.
     t1 = t2 <=>
     ?R. R t1 t2 /\
         (!x t. R (itree_Ret x) t ==> t = itree_Ret x) /\
         (!u t. R (Tau u) t ==> ?v. t = Tau v /\ (R u v \/ u = v)) /\
         (!a f t. R (Vis a f) t ==> ?g. t = Vis a g /\
                                        !s. R (f s) (g s) \/ f s = g s)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN SUBST1_TAC THEN
    EXISTS_TAC `(=):(A,E,R)itree->(A,E,R)itree->bool` THEN MESON_TAC[];
    STRIP_TAC THEN ONCE_REWRITE_TAC[itree_bisimulation] THEN
    EXISTS_TAC `\x y:(A,E,R)itree. R x y \/ x = y` THEN
    REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

(* register with TypeBase (HOL4): done above, after itree_CASE_elim *)

let itree_CASE_cong = prove
 (`!M M' (ret:R->Z) tau vis ret' tau' vis'.
     M = M' /\
     (!x. M' = itree_Ret x ==> ret x = ret' x) /\
     (!t. M' = Tau t ==> tau t = tau' t) /\
     (!a g. M' = Vis a g ==> vis a g = vis' a g) ==>
     itree_CASE (M:(A,E,R)itree) ret tau vis = itree_CASE M' ret' tau' vis'`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  QCASES_ON "M'" THEN ASM_SIMP_TAC[itree_CASE]);;

(* ------------------------------------------------------------------------- *)
(* itree combinators                                                         *)
(* ------------------------------------------------------------------------- *)

let itree_bind_def = cake_def
 `itree_bind (t:(A,E,R)itree) (k:R->(A,E,B)itree) =
  itree_unfold
    (\x. match x with
           INL (itree_Ret r) ->
             (match k r with
                itree_Ret s -> Ret' s
              | Tau t -> Tau' (INR t)
              | Vis e g -> Vis' e (INR o g))
         | INL (Vis e g) -> Vis' e (INL o g)
         | INL (Tau t) -> Tau' (INL t)
         | INR (itree_Ret r) -> Ret' r
         | INR (Vis e g) -> Vis' e (INR o g)
         | INR (Tau t) -> Tau' (INR t))
    (INL t)`;;

(* an unfold that copies the INR seeds (helper for itree_unfold_bind_INR) *)

let ITREEAUX_unfold_INR = prove
 (`!(h:(A,E,R)itree+(A,E,B)itree->(A,E,B,(A,E,R)itree+(A,E,B)itree)itree_next)
    u. (!r. h (INR (itree_Ret r)) = Ret' r) /\
       (!t. h (INR (Tau t)) = Tau' (INR t)) /\
       (!e g. h (INR (Vis e g)) = Vis' e (INR o g))
       ==> itree_unfold h (INR u) = u`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[itree_bisimulation] THEN
  QEXISTS_TAC "\\x y. x = itree_unfold h (INR y)" THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  QCASES_ON "t" THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [itree_unfold] THEN
  SIMP[o_THM; FUN_EQ_THM] THEN MESON_TAC[]);;

let itree_unfold_bind_INR = prove(CASE_TERM
 `!(k:R->(A,E,B)itree) u.
    itree_unfold
    (\x. match x with
           INL (itree_Ret r) ->
             itree_CASE (k r) (\s. Ret' s) (\t. Tau' (INR t))
                        (\e g. Vis' e (INR o g))
         | INL (Tau t) -> Tau' (INL t)
         | INL (Vis e g) -> Vis' e (INL o g)
         | INR (itree_Ret r') -> Ret' r'
         | INR (Tau t') -> Tau' (INR t')
         | INR (Vis e' g') -> Vis' e' (INR o g')) (INR u) =
    u`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC ITREEAUX_unfold_INR THEN SIMP[]);;

let itree_bind_thm = prove
 (`(!(r:R) (k:R->(A,E,B)itree). itree_bind (itree_Ret r) k = k r) /\
   (!(t:(A,E,R)itree) (k:R->(A,E,B)itree).
      itree_bind (Tau t) k = Tau (itree_bind t k)) /\
   (!(e:E) (k':A->(A,E,R)itree) (k:R->(A,E,B)itree).
      itree_bind (Vis e k') k = Vis e (\x. itree_bind (k' x) k))`,
  REWRITE_TAC[itree_bind_def] THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [itree_unfold] THEN SIMP[] THENL
   [QCASES_ON "(k:R->(A,E,B)itree) r" THEN
    SIMP[itree_unfold_bind_INR; FUN_EQ_THM; o_THM];
    SIMP[FUN_EQ_THM; o_THM]]);;
let _ = cake_add_simps [itree_bind_thm];;

let itree_bind_right_identity = prove
 (`!t:(A,E,R)itree. itree_bind t itree_Ret = t`,
  GEN_TAC THEN ONCE_REWRITE_TAC[itree_bisimulation] THEN
  QEXISTS_TAC "\\x y. x = itree_bind y itree_Ret" THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  QCASES_ON "t" THEN GVS[] THEN MESON_TAC[]);;
let _ = cake_add_simps [itree_bind_right_identity];;

let itree_bind_assoc = prove
 (`!(t:(A,E,R)itree) (k:R->(A,E,B)itree) (k':B->(A,E,C)itree).
     itree_bind (itree_bind t k) k' = itree_bind t (\x. itree_bind (k x) k')`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[itree_bisimulation] THEN
  QEXISTS_TAC "\\x y. (?t. x = itree_bind (itree_bind t k) k' /\\
                         y = itree_bind t (\\x. itree_bind (k x) k')) \\/
                    x = y" THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  TRY(RENAME1 "itree_bind (itree_bind t0 _) _" THEN QCASES_ON "t0") THEN
  GVS[] THEN ASM_MESON_TAC[]);;

let itree_iter_def = cake_def
 `itree_iter (body:S->(A,E,S+R)itree) seed =
    itree_unfold
      (\x. match x with
             itree_Ret (INL seed') -> Tau' (body seed')
           | itree_Ret (INR v) -> Ret' v
           | Tau u -> Tau' u
           | Vis e g -> Vis' e g)
      (body seed)`;;

(* an unfold that behaves like itree_iter is a bind (helper for            *)
(* itree_iter_thm; HOL4 proves it inline by the same bisimulation)         *)

let ITREEAUX_unfold_iter = prove
 (`!(hn:(A,E,S+R)itree->(A,E,R,(A,E,S+R)itree)itree_next)
    (kn:S+R->(A,E,R)itree) (bd:S->(A,E,S+R)itree).
     (!s. hn (itree_Ret (INL s)) = Tau' (bd s)) /\
     (!v. hn (itree_Ret (INR v)) = Ret' v) /\
     (!u. hn (Tau u) = Tau' u) /\
     (!e k. hn (Vis e k) = Vis' e k) /\
     (!s. kn (INL s) = Tau (itree_unfold hn (bd s))) /\
     (!v. kn (INR v) = itree_Ret v)
     ==> !t. itree_unfold hn t = itree_bind t kn`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(!s. itree_unfold hn (itree_Ret (INL s):(A,E,S+R)itree) =
         Tau (itree_unfold hn (bd s))) /\
    (!v. itree_unfold hn (itree_Ret (INR v):(A,E,S+R)itree) = itree_Ret v) /\
    (!u. itree_unfold hn (Tau u:(A,E,S+R)itree) = Tau (itree_unfold hn u)) /\
    (!e k. itree_unfold hn (Vis e k:(A,E,S+R)itree) =
           Vis e (itree_unfold hn o k))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [itree_unfold] THEN SIMP[];
    ALL_TAC] THEN
  GEN_TAC THEN ONCE_REWRITE_TAC[itree_bisimulation] THEN
  QEXISTS_TAC "\\x y. (?t0. x = itree_unfold hn t0 /\\ y = itree_bind t0 kn) \\/
                     x = y" THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  TRY(NAMED_CASES_ON "t0" ["r0"; "u0"; "e0 k0"] THEN
      TRY(NAMED_CASES_ON "r0" ["s1"; "v1"])) THEN
  GVS[o_THM] THEN ASM_MESON_TAC[]);;

let itree_iter_thm = prove(CASE_TERM
 `!(body:S->(A,E,S+R)itree) seed.
    itree_iter body seed =
    itree_bind (body seed)
               (\x. match x with INL a -> Tau (itree_iter body a)
                               | INR b -> itree_Ret b)`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [itree_iter_def] THEN
  SPEC_TAC(`(body:S->(A,E,S+R)itree) seed`,`t:(A,E,S+R)itree`) THEN
  MATCH_MP_TAC ITREEAUX_unfold_iter THEN QEXISTS_TAC "body" THEN
  SIMP[itree_iter_def]);;

let itree_loop_def = cake_def
 `itree_loop (body:C+D->(A,E,C+R)itree) (seed:D) =
    itree_iter (\x. itree_bind (body x)
                      (\cb. match cb with INL c -> itree_Ret (INL (INL c))
                                       | INR b -> itree_Ret (INR b)))
               (INR seed)`;;

(* ------------------------------------------------------------------------- *)
(* weak termination-sensitive bisimulation                                   *)
(* ------------------------------------------------------------------------- *)

let strip_tau_rules,strip_tau_ind,strip_tau_cases,strip_tau_strongind =
  cake_inductive
 `(!t t':(A,E,R)itree. strip_tau t t' ==> strip_tau (Tau t) t') /\
  (!e k. strip_tau (Vis e k) (Vis e k)) /\
  (!v. strip_tau (itree_Ret v) (itree_Ret v))`;;

let strip_tau_simps = prove
 (`(!t' t:(A,E,R)itree. strip_tau t' (Tau t) <=> F) /\
   (!v (e:E) (k:A->(A,E,R)itree). strip_tau (itree_Ret v) (Vis e k) <=> F) /\
   (!(e:E) (k:A->(A,E,R)itree) v. strip_tau (Vis e k) (itree_Ret v) <=> F) /\
   (!t t':(A,E,R)itree. strip_tau (Tau t) t' <=> strip_tau t t')`,
  CONJ_TAC THENL
   [SUBGOAL_THEN `!t t':(A,E,R)itree. strip_tau t t' ==> !t''. ~(t' = Tau t'')`
      (fun th -> MESON_TAC[th]) THEN
    MATCH_MP_TAC strip_tau_ind THEN SIMP[itree_distinct];
    REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [strip_tau_cases] THEN
    SIMP[itree_distinct; itree_11] THEN MESON_TAC[]]);;
let _ = cake_add_simps [strip_tau_simps];;

let strip_tau_simps2 = prove
 (`!v v':R. strip_tau (itree_Ret v:(A,E,R)itree) (itree_Ret v') <=> v = v'`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [strip_tau_cases] THEN
  SIMP[itree_distinct; itree_11] THEN MESON_TAC[]);;
let _ = cake_add_simps [strip_tau_simps2];;

let strip_tau_simps3 = prove
 (`!(e:E) (k:A->(A,E,R)itree) e' k'.
     strip_tau (Vis e k) (Vis e' k') <=> e = e' /\ k = k'`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [strip_tau_cases] THEN
  SIMP[itree_distinct; itree_11] THEN MESON_TAC[]);;
let _ = cake_add_simps [strip_tau_simps3];;

let strip_tau_inj = prove
 (`!t t' t'':(A,E,R)itree. strip_tau t t' /\ strip_tau t t'' ==> t' = t''`,
  REWRITE_TAC[GSYM IMP_IMP; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC strip_tau_ind THEN SIMP[] THEN
  CONJ_TAC THEN REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [strip_tau_cases] THEN
  SIMP[itree_distinct; itree_11] THEN MESON_TAC[]);;

let itree_wbisim_rules,itree_wbisim_coind,itree_wbisim_cases =
  new_coinductive_definition
 `(!t t':(A,E,R)itree. itree_wbisim t t' ==> itree_wbisim (Tau t) (Tau t')) /\
  (!t t' e k k'.
     strip_tau t (Vis e k) /\ strip_tau t' (Vis e k') /\
     (!r. itree_wbisim (k r) (k' r)) ==>
     itree_wbisim t t') /\
  (!t t' r. strip_tau t (itree_Ret r) /\ strip_tau t' (itree_Ret r) ==>
            itree_wbisim t t')`;;

(* HOL4's fixedPoint theory (an ancestor of itreeTau, not in the port):     *)
(* monotone and gfp of set functions, with the facts used below; local     *)
(* copies under the helper prefix                                           *)

let ITREEAUX_monotone_def = new_definition
 `ITREEAUX_monotone (f:(A->bool)->(B->bool)) <=>
    !X Y. X SUBSET Y ==> f X SUBSET f Y`;;

let ITREEAUX_gfp_def = new_definition
 `ITREEAUX_gfp (f:(A->bool)->(A->bool)) = UNIONS {X | X SUBSET f X}`;;

let ITREEAUX_gfp_greatest_fixedpoint = prove
 (`!f:(A->bool)->(A->bool).
     ITREEAUX_monotone f ==>
     f (ITREEAUX_gfp f) = ITREEAUX_gfp f /\
     !X. f X = X ==> X SUBSET ITREEAUX_gfp f`,
  GEN_TAC THEN REWRITE_TAC[ITREEAUX_monotone_def] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!X. X SUBSET (f:(A->bool)->(A->bool)) X ==> X SUBSET ITREEAUX_gfp f`
  ASSUME_TAC THENL
   [REWRITE_TAC[ITREEAUX_gfp_def] THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `ITREEAUX_gfp f SUBSET (f:(A->bool)->(A->bool)) (ITREEAUX_gfp f)`
  ASSUME_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [ITREEAUX_gfp_def] THEN
    REWRITE_TAC[UNIONS_SUBSET; IN_ELIM_THM] THEN
    ASM_MESON_TAC[SUBSET_TRANS];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_MESON_TAC[];
    ASM_MESON_TAC[SUBSET_REFL]]);;

let ITREEAUX_gfp_coinduction = prove
 (`!f:(A->bool)->(A->bool).
     ITREEAUX_monotone f ==> !X. X SUBSET f X ==> X SUBSET ITREEAUX_gfp f`,
  REWRITE_TAC[ITREEAUX_gfp_def] THEN SET_TAC[]);;

(* HOL4's rel_to_reln R (the set of pairs of R) is UNCURRY R and           *)
(* reln_to_rel r (the relation of a set of pairs) is CURRY r               *)

let wbisim_functional_def = cake_def
 `wbisim_functional (R:(A,E,R)itree#(A,E,R)itree->bool) =
    {(t,t') | t,t' | ?r. strip_tau t (itree_Ret r) /\ strip_tau t' (itree_Ret r)}
    UNION
    {(t,t') | t,t' | ?e k k'. strip_tau t (Vis e k) /\ strip_tau t' (Vis e k') /\
                              !r. (k r,k' r) IN R}
    UNION
    {(Tau t,Tau t') | t,t' | (t,t') IN R}`;;

let wbisim_functional_mono = prove
 (`ITREEAUX_monotone
     (wbisim_functional:((A,E,R)itree#(A,E,R)itree->bool)->
                        (A,E,R)itree#(A,E,R)itree->bool)`,
  REWRITE_TAC[ITREEAUX_monotone_def; wbisim_functional_def; SUBSET; IN_UNION;
              IN_ELIM_THM] THEN
  MESON_TAC[]);;
let _ = cake_add_simps [wbisim_functional_mono];;

let wbisim_functional_cancel = prove
 (`!X Y:(A,E,R)itree#(A,E,R)itree->bool.
     X SUBSET Y ==> wbisim_functional X SUBSET wbisim_functional Y`,
  MESON_TAC[wbisim_functional_mono; ITREEAUX_monotone_def]);;

(* HOL4's in_rel_to_reln *)

let ITREEAUX_IN_UNCURRY = prove
 (`!(R:A->B->bool) x y. (x,y) IN UNCURRY R <=> R x y`,
  REWRITE_TAC[IN; UNCURRY_DEF]);;

let wbisim_functional_gfp = prove
 (`ITREEAUX_gfp (wbisim_functional:((A,E,R)itree#(A,E,R)itree->bool)->
                                 (A,E,R)itree#(A,E,R)itree->bool) =
   UNCURRY itree_wbisim`,
  MP_TAC(ISPEC `wbisim_functional:((A,E,R)itree#(A,E,R)itree->bool)->
                                  (A,E,R)itree#(A,E,R)itree->bool`
               ITREEAUX_gfp_greatest_fixedpoint) THEN
  REWRITE_TAC[wbisim_functional_mono] THEN STRIP_TAC THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_PAIR_THM; ITREEAUX_IN_UNCURRY] THEN
    MATCH_MP_TAC itree_wbisim_coind THEN REPEAT GEN_TAC THEN
    FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM th]) THEN
    REWRITE_TAC[wbisim_functional_def; IN_UNION; IN_ELIM_THM; PAIR_EQ] THEN
    MESON_TAC[];
    MATCH_MP_TAC(MP (ISPEC `wbisim_functional:((A,E,R)itree#(A,E,R)itree->bool)->
                                             (A,E,R)itree#(A,E,R)itree->bool`
                           ITREEAUX_gfp_coinduction) wbisim_functional_mono) THEN
    REWRITE_TAC[SUBSET; FORALL_PAIR_THM; ITREEAUX_IN_UNCURRY;
                wbisim_functional_def; IN_UNION; IN_ELIM_THM; PAIR_EQ] THEN
    REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [itree_wbisim_cases] THEN
    MESON_TAC[]]);;

let itree_wbisim_refl = prove
 (`!t:(A,E,R)itree. itree_wbisim t t`,
  SUBGOAL_THEN `!t t':(A,E,R)itree. t = t' ==> itree_wbisim t t'`
    (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC itree_wbisim_coind THEN GEN_TAC THEN QCASES_ON "t" THEN
  SIMP[] THEN MESON_TAC[strip_tau_rules]);;

let itree_wbisim_sym = prove
 (`!t t':(A,E,R)itree. itree_wbisim t t' ==> itree_wbisim t' t`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN MATCH_MP_TAC itree_wbisim_coind THEN
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [itree_wbisim_cases] THEN
  MESON_TAC[]);;

let itree_wbisim_tau_eq = prove
 (`!t:(A,E,R)itree. itree_wbisim (Tau t) t`,
  SUBGOAL_THEN `!t t':(A,E,R)itree. t = Tau t' \/ t = t' ==> itree_wbisim t t'`
    (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC itree_wbisim_coind THEN REPEAT GEN_TAC THEN
  QCASES_ON "t'" THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SIMP[] THEN MESON_TAC[strip_tau_rules]);;

let itree_wbisim_strong_coind = prove
 (`!R. (!t t':(A,E,R)itree.
          R t t' ==>
          (?t2 t3. t = Tau t2 /\ t' = Tau t3 /\
                   (R t2 t3 \/ itree_wbisim t2 t3)) \/
          (?e k k'.
             strip_tau t (Vis e k) /\ strip_tau t' (Vis e k') /\
             !r. R (k r) (k' r) \/ itree_wbisim (k r) (k' r)) \/
          ?r. strip_tau t (itree_Ret r) /\ strip_tau t' (itree_Ret r)) ==>
       !t t'. R t t' ==> itree_wbisim t t'`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!t t':(A,E,R)itree. R t t' \/ itree_wbisim t t' ==> itree_wbisim t t'`
    (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC itree_wbisim_coind THEN REPEAT GEN_TAC THEN STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`t:(A,E,R)itree`; `t':(A,E,R)itree`]) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [itree_wbisim_cases]) THEN
    MESON_TAC[]]);;

let itree_wbisim_coind_upto_equiv = prove
 (`!R t t':(A,E,R)itree.
     itree_wbisim t t' ==>
     (?t2 t3. t = Tau t2 /\ t' = Tau t3 /\ (R t2 t3 \/ itree_wbisim t2 t3)) \/
     (?e k k'.
        strip_tau t (Vis e k) /\ strip_tau t' (Vis e k') /\
        !r. R (k r) (k' r) \/ itree_wbisim (k r) (k' r)) \/
     ?r. strip_tau t (itree_Ret r) /\ strip_tau t' (itree_Ret r)`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [itree_wbisim_cases] THEN
  MESON_TAC[]);;

let itree_wbisim_coind_upto = prove
 (`!R. (!t t':(A,E,R)itree.
          R t t' ==>
          (?t2 t3. t = Tau t2 /\ t' = Tau t3 /\
                   (R t2 t3 \/ itree_wbisim t2 t3)) \/
          (?e k k'.
             strip_tau t (Vis e k) /\ strip_tau t' (Vis e k') /\
             !r. R (k r) (k' r) \/ itree_wbisim (k r) (k' r)) \/
          (?r. strip_tau t (itree_Ret r) /\ strip_tau t' (itree_Ret r)) \/
          itree_wbisim t t')
       ==> !t t'. R t t' ==> itree_wbisim t t'`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC itree_wbisim_strong_coind THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL
    [`t:(A,E,R)itree`; `t':(A,E,R)itree`]) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`R:(A,E,R)itree->(A,E,R)itree->bool`; `t:(A,E,R)itree`;
                 `t':(A,E,R)itree`] itree_wbisim_coind_upto_equiv) THEN
  MESON_TAC[]);;

(* HOL4's companion theory (an ancestor of itreeTau, not in the port): the *)
(* companion of a monotone set function, after D. Pous, with the facts     *)
(* used below; local copies under the helper prefix                         *)

let ITREEAUX_set_compatible_def = new_definition
 `ITREEAUX_set_compatible (b:(A->bool)->(A->bool)) f <=>
    ITREEAUX_monotone f /\ !X. f (b X) SUBSET b (f X)`;;

let ITREEAUX_set_companion_def = new_definition
 `ITREEAUX_set_companion (b:(A->bool)->(A->bool)) X =
    UNIONS {f X | f | ITREEAUX_set_compatible b f}`;;

let ITREEAUX_set_compatible_enhance = prove
 (`!b f X Y:A->bool.
     ITREEAUX_monotone b /\ ITREEAUX_set_compatible b f /\ Y SUBSET f X
     ==> Y SUBSET ITREEAUX_set_companion b X`,
  REWRITE_TAC[ITREEAUX_set_companion_def] THEN SET_TAC[]);;

let ITREEAUX_set_gfp_sub_companion = prove
 (`!b x:A->bool.
     ITREEAUX_monotone b ==> ITREEAUX_gfp b SUBSET ITREEAUX_set_companion b x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ITREEAUX_set_compatible_enhance THEN
  EXISTS_TAC `\X:A->bool. ITREEAUX_gfp (b:(A->bool)->(A->bool))` THEN
  ASM_REWRITE_TAC[ITREEAUX_set_compatible_def; ITREEAUX_monotone_def;
                  SUBSET_REFL] THEN
  ASM_MESON_TAC[ITREEAUX_gfp_greatest_fixedpoint; SUBSET_REFL]);;

let ITREEAUX_set_companion_compatible = prove
 (`!b:(A->bool)->(A->bool).
     ITREEAUX_monotone b ==>
     ITREEAUX_set_compatible b (ITREEAUX_set_companion b)`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `!f X:A->bool. ITREEAUX_set_compatible b f ==>
                              f X SUBSET ITREEAUX_set_companion b X`
  ASSUME_TAC THENL
   [REWRITE_TAC[ITREEAUX_set_companion_def] THEN SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[ITREEAUX_set_compatible_def; ITREEAUX_monotone_def] THEN
  CONJ_TAC THEN REPEAT GEN_TAC THENL [DISCH_TAC; ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [ITREEAUX_set_companion_def] THEN
  REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
  X_GEN_TAC `f:(A->bool)->(A->bool)` THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[ITREEAUX_set_compatible_def;
                                              ITREEAUX_monotone_def]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ITREEAUX_monotone_def]) THEN
  MATCH_MP_TAC SUBSET_TRANS THENL
   [EXISTS_TAC `(f:(A->bool)->(A->bool)) Y`;
    EXISTS_TAC `(b:(A->bool)->(A->bool)) ((f:(A->bool)->(A->bool)) X)`] THEN
  ASM_SIMP_TAC[]);;

let ITREEAUX_set_companion_coinduct = prove
 (`!b X:A->bool.
     ITREEAUX_monotone b /\ X SUBSET (b o ITREEAUX_set_companion b) X
     ==> X SUBSET ITREEAUX_gfp b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[o_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!X Y:A->bool. X SUBSET Y ==> (b:(A->bool)->(A->bool)) X SUBSET b Y`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[ITREEAUX_monotone_def]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ITREEAUX_set_companion_compatible) THEN
  REWRITE_TAC[ITREEAUX_set_compatible_def; ITREEAUX_monotone_def] THEN
  STRIP_TAC THEN
  ABBREV_TAC `t = ITREEAUX_set_companion (b:(A->bool)->(A->bool))` THEN
  SUBGOAL_THEN `!Y:A->bool. t ((t:(A->bool)->(A->bool)) Y) SUBSET t Y`
  ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "t" THEN
    MATCH_MP_TAC ITREEAUX_set_compatible_enhance THEN
    EXISTS_TAC `(t:(A->bool)->(A->bool)) o t` THEN
    ASM_REWRITE_TAC[ITREEAUX_set_compatible_def; ITREEAUX_monotone_def;
                    o_THM; SUBSET_REFL] THEN
    CONJ_TAC THEN REPEAT STRIP_TAC THENL
     [ASM_SIMP_TAC[];
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `(t:(A->bool)->(A->bool)) (b (t (X':A->bool)))` THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!Y:A->bool. Y SUBSET (t:(A->bool)->(A->bool)) Y` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "t" THEN
    MATCH_MP_TAC ITREEAUX_set_compatible_enhance THEN
    EXISTS_TAC `\Y:A->bool. Y` THEN
    ASM_REWRITE_TAC[ITREEAUX_set_compatible_def; ITREEAUX_monotone_def;
                    SUBSET_REFL];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `(t:(A->bool)->(A->bool)) X` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `b:(A->bool)->(A->bool)` ITREEAUX_gfp_coinduction) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `(t:(A->bool)->(A->bool)) (b (t (X:A->bool)))` THEN
  ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `(b:(A->bool)->(A->bool)) (t (t (X:A->bool)))` THEN
  ASM_SIMP_TAC[]);;

(* more compositional variant using the enhanced functional (bt) *)

let itree_wbisim_coind_upto' = prove
 (`!R:(A,E,R)itree->(A,E,R)itree->bool.
     UNCURRY R SUBSET
       UNCURRY itree_wbisim UNION
       wbisim_functional (ITREEAUX_set_companion wbisim_functional (UNCURRY R))
     ==> UNCURRY R SUBSET UNCURRY itree_wbisim`,
  GEN_TAC THEN REWRITE_TAC[GSYM wbisim_functional_gfp] THEN DISCH_TAC THEN
  MATCH_MP_TAC ITREEAUX_set_companion_coinduct THEN
  REWRITE_TAC[wbisim_functional_mono; o_THM] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
    `X SUBSET (G:A->bool) UNION Y ==> G SUBSET Y ==> X SUBSET Y`)) THEN
  MP_TAC(ISPEC `wbisim_functional:((A,E,R)itree#(A,E,R)itree->bool)->
                                  (A,E,R)itree#(A,E,R)itree->bool`
               ITREEAUX_gfp_greatest_fixedpoint) THEN
  REWRITE_TAC[wbisim_functional_mono] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC LAND_CONV [GSYM(CONJUNCT1 th)]) THEN
  MATCH_MP_TAC wbisim_functional_cancel THEN
  MATCH_MP_TAC ITREEAUX_set_gfp_sub_companion THEN
  REWRITE_TAC[wbisim_functional_mono]);;

let itree_wbisim_vis = prove
 (`!(e:E) (k1:A->(A,E,R)itree) k2.
     (!r. itree_wbisim (k1 r) (k2 r)) ==> itree_wbisim (Vis e k1) (Vis e k2)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[itree_wbisim_cases] THEN
  SIMP[] THEN ASM_MESON_TAC[]);;

let itree_wbisim_vis_vis = prove
 (`!(a:E) (g:A->(A,E,R)itree) a' g'.
     itree_wbisim (Vis a g) (Vis a' g') <=>
     a = a' /\ !r. itree_wbisim (g r) (g' r)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [itree_wbisim_cases] THEN
    SIMP[itree_distinct] THEN MESON_TAC[];
    MESON_TAC[itree_wbisim_vis]]);;

let itree_wbisim_tau = prove
 (`!t t':(A,E,R)itree. itree_wbisim (Tau t) t' ==> itree_wbisim t t'`,
  MATCH_MP_TAC itree_wbisim_strong_coind THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [itree_wbisim_cases] THEN
  SIMP[itree_11; itree_distinct] THEN STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [itree_wbisim_cases]) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN SIMP[] THEN
    ASM_MESON_TAC[itree_wbisim_rules];
    ASM_MESON_TAC[];
    ASM_MESON_TAC[]]);;

let itree_wbisim_tau_eqn0 = prove
 (`!t t':(A,E,R)itree.
     (?t0. t = Tau t0 /\ itree_wbisim t0 t') ==> itree_wbisim t t'`,
  MATCH_MP_TAC itree_wbisim_strong_coind THEN REPEAT GEN_TAC THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [itree_wbisim_cases]) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN SIMP[itree_11] THEN
  ASM_MESON_TAC[]);;

let itree_wbisim_tau_eqn = prove
 (`(!t1 t2:(A,E,R)itree. itree_wbisim (Tau t1) t2 <=> itree_wbisim t1 t2) /\
   (!t1 t2:(A,E,R)itree. itree_wbisim t1 (Tau t2) <=> itree_wbisim t1 t2)`,
  MESON_TAC[itree_wbisim_sym; itree_wbisim_tau_eqn0; itree_wbisim_tau]);;
let _ = cake_add_simps [itree_wbisim_tau_eqn];;

let itree_wbisim_strip_tau = prove
 (`!t t' t'':(A,E,R)itree.
     itree_wbisim t t' /\ strip_tau t t'' ==> itree_wbisim t'' t'`,
  SUBGOAL_THEN `!t t'':(A,E,R)itree.
                  strip_tau t t'' ==> !t'. itree_wbisim t t' ==> itree_wbisim t'' t'`
    (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC strip_tau_ind THEN SIMP[]);;

let itree_wbisim_strip_tau_sym = prove
 (`!t t' t'':(A,E,R)itree.
     itree_wbisim t t' /\ strip_tau t' t'' ==> itree_wbisim t t''`,
  MESON_TAC[itree_wbisim_sym; itree_wbisim_strip_tau]);;

let itree_wbisim_strip_tau_Ret = prove
 (`!t t':(A,E,R)itree v.
     itree_wbisim t t' /\ strip_tau t (itree_Ret v) ==> strip_tau t' (itree_Ret v)`,
  SUBGOAL_THEN `!t x:(A,E,R)itree. strip_tau t x ==>
                  !t' v. x = itree_Ret v /\ itree_wbisim t t' ==>
                         strip_tau t' (itree_Ret v)`
    (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC strip_tau_ind THEN SIMP[itree_distinct; itree_11] THEN
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [itree_wbisim_cases] THEN
  SIMP[itree_distinct] THEN MESON_TAC[]);;

let itree_wbisim_strip_tau_Vis = prove
 (`!t t':(A,E,R)itree e k.
     itree_wbisim t t' /\ strip_tau t (Vis e k)
     ==> ?k'. strip_tau t' (Vis e k') /\ !r. itree_wbisim (k r) (k' r)`,
  SUBGOAL_THEN `!t x:(A,E,R)itree. strip_tau t x ==>
                  !t' e k. x = Vis e k /\ itree_wbisim t t' ==>
                           ?k'. strip_tau t' (Vis e k') /\
                                !r. itree_wbisim (k r) (k' r)`
    (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC strip_tau_ind THEN SIMP[itree_distinct; itree_11] THEN
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [itree_wbisim_cases] THEN
  SIMP[itree_distinct] THEN MESON_TAC[]);;

let itree_wbisim_trans = prove
 (`!t t' t'':(A,E,R)itree.
     itree_wbisim t t' /\ itree_wbisim t' t'' ==> itree_wbisim t t''`,
  SUBGOAL_THEN `!t t'':(A,E,R)itree.
                  (?t'. itree_wbisim t t' /\ itree_wbisim t' t'') ==>
                  itree_wbisim t t''`
    (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC itree_wbisim_coind THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  QCASES_ON "t" THENL
   [SIMP[itree_distinct; itree_11] THEN
    MATCH_MP_TAC itree_wbisim_strip_tau_Ret THEN
    EXISTS_TAC `t':(A,E,R)itree` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC itree_wbisim_strip_tau_Ret THEN
    EXISTS_TAC `itree_Ret x:(A,E,R)itree` THEN
    ASM_REWRITE_TAC[strip_tau_simps2];
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      free_in `u:(A,E,R)itree` (concl th))) THEN
    REWRITE_TAC[itree_wbisim_tau_eqn] THEN DISCH_TAC THEN
    SIMP[itree_distinct; itree_11] THEN QCASES_ON "t''" THENL
     [SIMP[itree_distinct; itree_11] THEN
      ASM_MESON_TAC[itree_wbisim_strip_tau_Ret; itree_wbisim_sym;
                    strip_tau_rules];
      FS[itree_distinct; itree_11] THEN ASM_MESON_TAC[];
      SIMP[itree_distinct; itree_11] THEN
      MP_TAC(ISPECL [`Vis a g:(A,E,R)itree`; `t':(A,E,R)itree`; `a:E`;
                     `g:A->(A,E,R)itree`] itree_wbisim_strip_tau_Vis) THEN
      ASM_SIMP_TAC[itree_wbisim_sym; strip_tau_simps3] THEN
      DISCH_THEN(X_CHOOSE_THEN `k1:A->(A,E,R)itree` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPECL [`t':(A,E,R)itree`; `u:(A,E,R)itree`; `a:E`;
                     `k1:A->(A,E,R)itree`] itree_wbisim_strip_tau_Vis) THEN
      ASM_SIMP_TAC[itree_wbisim_sym] THEN
      DISCH_THEN(X_CHOOSE_THEN `k2:A->(A,E,R)itree` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `k2:A->(A,E,R)itree` THEN ASM_MESON_TAC[itree_wbisim_sym]];
    SIMP[itree_distinct; itree_11] THEN
    MP_TAC(ISPECL [`Vis a g:(A,E,R)itree`; `t':(A,E,R)itree`; `a:E`;
                   `g:A->(A,E,R)itree`] itree_wbisim_strip_tau_Vis) THEN
    ASM_SIMP_TAC[strip_tau_simps3] THEN
    DISCH_THEN(X_CHOOSE_THEN `k1:A->(A,E,R)itree` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`t':(A,E,R)itree`; `t'':(A,E,R)itree`; `a:E`;
                   `k1:A->(A,E,R)itree`] itree_wbisim_strip_tau_Vis) THEN
    ASM_SIMP_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `k2:A->(A,E,R)itree` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `k2:A->(A,E,R)itree` THEN ASM_MESON_TAC[]]);;

(* common bind base case *)

let itree_bind_ret_inv = prove
 (`!(t:(A,E,R)itree) (k:R->(A,E,B)itree) r.
     itree_bind t k = itree_Ret r ==> ?r'. t = itree_Ret r' /\ k r' = itree_Ret r`,
  GEN_TAC THEN QCASES_ON "t" THEN SIMP[itree_bind_thm; itree_distinct; itree_11]);;

(* combinators respect weak bisimilarity *)

let itree_bind_strip_tau_wbisim = prove
 (`!(u:(A,E,R)itree) u' (k:R->(A,E,B)itree).
     strip_tau u u' ==> itree_wbisim (itree_bind u k) (itree_bind u' k)`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN MATCH_MP_TAC strip_tau_ind THEN
  SIMP[itree_bind_thm; itree_wbisim_refl]);;

let itree_bind_vis_strip_tau = prove
 (`!(u:(A,E,R)itree) (k:R->(A,E,B)itree) k' e.
     strip_tau u (Vis e k') ==>
     strip_tau (itree_bind u k) (Vis e (\x. itree_bind (k' x) k))`,
  SUBGOAL_THEN `!u x:(A,E,R)itree. strip_tau u x ==>
                  !(k:R->(A,E,B)itree) k' e. x = Vis e k' ==>
                  strip_tau (itree_bind u k) (Vis e (\x. itree_bind (k' x) k))`
    (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC strip_tau_ind THEN
  SIMP[itree_bind_thm; itree_distinct; itree_11]);;

let itree_bind_vis_tau_wbisim = prove
 (`!(a:E) (g:A->(A,E,R)itree) u (k:R->(A,E,B)itree).
     itree_wbisim (Vis a g) (Tau u) ==>
     ?e k' k''.
       strip_tau (itree_bind (Vis a g) k) (Vis e k') /\
       strip_tau (itree_bind (Tau u) k) (Vis e k'') /\
       !r. (?t1 t2. itree_wbisim t1 t2 /\
                    k' r = itree_bind t1 k /\ k'' r = itree_bind t2 k) \/
           itree_wbisim (k' r) (k'' r)`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [itree_wbisim_cases] THEN
  SIMP[itree_distinct; itree_bind_thm] THEN STRIP_TAC THEN
  EXISTS_TAC `\x. itree_bind ((k':A->(A,E,R)itree) x) (k:R->(A,E,B)itree)` THEN
  ASM_SIMP_TAC[itree_bind_vis_strip_tau] THEN ASM_MESON_TAC[]);;

let itree_bind_resp_t_wbisim = prove
 (`!a b (k:R->(A,E,B)itree).
     itree_wbisim (a:(A,E,R)itree) b ==>
     itree_wbisim (itree_bind a k) (itree_bind b k)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `\a b. ?s1 s2:(A,E,R)itree. itree_wbisim s1 s2 /\
                        a = itree_bind s1 (k:R->(A,E,B)itree) /\
                        b = itree_bind s2 k` itree_wbisim_coind_upto) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [itree_wbisim_cases]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[itree_bind_thm] THENL
   [DISJ1_TAC THEN SIMP[itree_11] THEN ASM_MESON_TAC[];
    DISJ2_TAC THEN DISJ1_TAC THEN
    MAP_EVERY EXISTS_TAC
     [`e:E`;
      `\x. itree_bind ((k':A->(A,E,R)itree) x) (k:R->(A,E,B)itree)`;
      `\x. itree_bind ((k'':A->(A,E,R)itree) x) (k:R->(A,E,B)itree)`] THEN
    ASM_SIMP_TAC[itree_bind_vis_strip_tau] THEN ASM_MESON_TAC[];
    DISJ2_TAC THEN DISJ2_TAC THEN DISJ2_TAC THEN
    ASM_MESON_TAC[itree_bind_strip_tau_wbisim; itree_wbisim_trans;
                  itree_wbisim_sym]]);;

let itree_bind_resp_k_wbisim = prove
 (`!(t:(A,E,R)itree) (k1:R->(A,E,B)itree) k2.
     (!r. itree_wbisim (k1 r) (k2 r)) ==>
     itree_wbisim (itree_bind t k1) (itree_bind t k2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `\a b. ?s:(A,E,R)itree. a = itree_bind s (k1:R->(A,E,B)itree) /\
                                     b = itree_bind s (k2:R->(A,E,B)itree)`
               itree_wbisim_coind_upto) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  QCASES_ON "s" THEN REWRITE_TAC[itree_bind_thm] THEN SIMP[itree_11] THEN
  ASM_MESON_TAC[]);;

let itree_bind_resp_wbisim = prove
 (`!a b (k1:R->(A,E,B)itree) k2.
     itree_wbisim (a:(A,E,R)itree) b /\ (!r. itree_wbisim (k1 r) (k2 r)) ==>
     itree_wbisim (itree_bind a k1) (itree_bind b k2)`,
  MESON_TAC[itree_bind_resp_t_wbisim; itree_bind_resp_k_wbisim;
            itree_wbisim_trans]);;

(* binds of trees that strip to a return (helpers) *)

let ITREEAUX_bind_strip_tau_Ret = prove
 (`!(u:(A,E,R)itree) v (k:R->(A,E,B)itree) z.
     strip_tau u (itree_Ret v) /\ strip_tau (k v) z
     ==> strip_tau (itree_bind u k) z`,
  SUBGOAL_THEN `!u y:(A,E,R)itree. strip_tau u y ==>
                  !v (k:R->(A,E,B)itree) z. y = itree_Ret v /\ strip_tau (k v) z
                     ==> strip_tau (itree_bind u k) z`
    (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC strip_tau_ind THEN
  SIMP[itree_bind_thm; itree_distinct; itree_11] THEN MESON_TAC[]);;

let ITREEAUX_bind_strip_tau_Ret_eq = prove
 (`!(u:(A,E,R)itree) v (k:R->(A,E,B)itree) s.
     strip_tau u (itree_Ret v) /\ k v = itree_bind s k
     ==> ?s'. itree_wbisim s s' /\ itree_bind u k = itree_bind s' k`,
  SUBGOAL_THEN `!u y:(A,E,R)itree. strip_tau u y ==>
                  !v (k:R->(A,E,B)itree) s. y = itree_Ret v /\ k v = itree_bind s k
                     ==> ?s'. itree_wbisim s s' /\ itree_bind u k = itree_bind s' k`
    (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC strip_tau_ind THEN
  SIMP[itree_bind_thm; itree_distinct; itree_11] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`v:R`; `k:R->(A,E,B)itree`; `s:(A,E,R)itree`]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN EXISTS_TAC `Tau s':(A,E,R)itree` THEN
    ASM_REWRITE_TAC[itree_wbisim_tau_eqn; itree_bind_thm];
    MESON_TAC[itree_wbisim_refl]]);;

let itree_iter_ret_tau_wbisim = prove(CASE_TERM
 `!itcb1 itcb2 (k1:S->(A,E,S+R)itree) k2 x u.
   itcb1 = (\x. match x with INL a -> Tau (itree_iter k1 a)
                           | INR b -> itree_Ret b) /\
   itcb2 = (\x. match x with INL a -> Tau (itree_iter k2 a)
                           | INR b -> itree_Ret b) /\
   itree_wbisim (itree_Ret x) (Tau u) /\ (!r. itree_wbisim (k1 r) (k2 r))
   ==>
   (?t2 t3.
      itree_bind (itree_Ret x) itcb1 = Tau t2 /\
      itree_bind (Tau u) itcb2 = Tau t3 /\
      ((?sa sb. itree_wbisim sa sb /\
                t2 = itree_bind sa itcb1 /\ t3 = itree_bind sb itcb2) \/
       itree_wbisim t2 t3)) \/
   (?e k k'.
      strip_tau (itree_bind (itree_Ret x) itcb1) (Vis e k) /\
      strip_tau (itree_bind (Tau u) itcb2) (Vis e k') /\
      !r. (?sa sb. itree_wbisim sa sb /\
                   k r = itree_bind sa itcb1 /\ k' r = itree_bind sb itcb2) \/
          itree_wbisim (k r) (k' r)) \/
   (?r. strip_tau (itree_bind (itree_Ret x) itcb1) (itree_Ret r) /\
        strip_tau (itree_bind (Tau u) itcb2) (itree_Ret r))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(!a. itcb1 (INL a) = Tau (itree_bind ((k1:S->(A,E,S+R)itree) a) itcb1)) /\
    (!a. itcb2 (INL a) = Tau (itree_bind ((k2:S->(A,E,S+R)itree) a) itcb2)) /\
    (!b. itcb1 (INR b) = itree_Ret b:(A,E,R)itree) /\
    (!b. itcb2 (INR b) = itree_Ret b:(A,E,R)itree)`
  STRIP_ASSUME_TAC THENL
   [REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl))) THEN
    SIMP[] THEN REPEAT STRIP_TAC THEN MATCH_ACCEPT_TAC itree_iter_thm;
    ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (is_var o lhs o concl))) THEN
  SUBGOAL_THEN `strip_tau (u:(A,E,S+R)itree) (itree_Ret x)` ASSUME_TAC THENL
   [UNDISCH_TAC `itree_wbisim (itree_Ret x) (Tau (u:(A,E,S+R)itree))` THEN
    GEN_REWRITE_TAC LAND_CONV [itree_wbisim_cases] THEN
    SIMP[itree_distinct] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[itree_bind_thm] THEN NAMED_CASES_ON "x" ["a"; "b"] THEN
  ASM_REWRITE_TAC[] THENL
   [DISJ1_TAC THEN
    MP_TAC(ISPECL [`u:(A,E,S+R)itree`; `INL a:S+R`; `itcb2:S+R->(A,E,R)itree`;
                   `Tau ((k2:S->(A,E,S+R)itree) a)`]
                  ITREEAUX_bind_strip_tau_Ret_eq) THEN
    ASM_REWRITE_TAC[itree_bind_thm] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC
     [`itree_bind ((k1:S->(A,E,S+R)itree) a) (itcb1:S+R->(A,E,R)itree)`;
      `itree_bind (u:(A,E,S+R)itree) (itcb2:S+R->(A,E,R)itree)`] THEN
    REWRITE_TAC[] THEN DISJ1_TAC THEN
    MAP_EVERY EXISTS_TAC [`(k1:S->(A,E,S+R)itree) a`; `s':(A,E,S+R)itree`] THEN
    ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[itree_wbisim_trans; itree_wbisim_tau_eqn];
    DISJ2_TAC THEN DISJ2_TAC THEN EXISTS_TAC `b:R` THEN
    REWRITE_TAC[strip_tau_simps2; strip_tau_simps] THEN
    MATCH_MP_TAC ITREEAUX_bind_strip_tau_Ret THEN EXISTS_TAC `INR b:S+R` THEN
    ASM_REWRITE_TAC[strip_tau_simps2]]);;

let itree_iter_resp_wbisim = prove
 (`!t (k1:S->(A,E,S+R)itree) k2.
     (!r. itree_wbisim (k1 r) (k2 r)) ==>
     itree_wbisim (itree_iter k1 t) (itree_iter k2 t)`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC BINOP_CONV [itree_iter_thm] THEN
  MATCH_GOALSUB_ABBREV_TAC "itree_bind (k1 t) itcb1" THEN
  MATCH_GOALSUB_ABBREV_TAC "itree_bind (k2 t) itcb2" THEN
  SUBGOAL_THEN
   `(!a. itcb1 (INL a) = Tau (itree_bind ((k1:S->(A,E,S+R)itree) a) itcb1)) /\
    (!a. itcb2 (INL a) = Tau (itree_bind ((k2:S->(A,E,S+R)itree) a) itcb2)) /\
    (!b. itcb1 (INR b) = itree_Ret b:(A,E,R)itree) /\
    (!b. itcb2 (INR b) = itree_Ret b:(A,E,R)itree)`
  STRIP_ASSUME_TAC THENL
   [REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (is_var o rhs o concl))) THEN
    SIMP[] THEN REPEAT STRIP_TAC THEN MATCH_ACCEPT_TAC itree_iter_thm;
    ALL_TAC] THEN
  MP_TAC(ISPEC `\ia ib. ?sa sb. itree_wbisim sa sb /\
                         ia = itree_bind sa (itcb1:S+R->(A,E,R)itree) /\
                         ib = itree_bind sb (itcb2:S+R->(A,E,R)itree)`
               itree_wbisim_strong_coind) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  MAP_EVERY X_GEN_TAC [`ia:(A,E,R)itree`; `ib:(A,E,R)itree`] THEN
  DISCH_THEN(X_CHOOSE_THEN `sa:(A,E,S+R)itree`
    (X_CHOOSE_THEN `sb:(A,E,S+R)itree` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN
  NAMED_CASES_ON "sa" ["x1"; "u1"; "e1 g1"] THEN
  NAMED_CASES_ON "sb" ["x2"; "u2"; "e2 g2"] THENL
   [(* Ret, Ret *)
    SUBGOAL_THEN `x1:S+R = x2` SUBST_ALL_TAC THENL
     [QPAT_X_ASSUM "itree_wbisim (itree_Ret _) _"
        (MP_TAC o ONCE_REWRITE_RULE[itree_wbisim_cases]) THEN
      SIMP[itree_distinct] THEN MESON_TAC[];
      ALL_TAC] THEN
    NAMED_CASES_ON "x2" ["a"; "b"] THEN
    ASM_REWRITE_TAC[itree_bind_thm; itree_11; strip_tau_simps2] THEN
    ASM_MESON_TAC[];
    (* Ret, Tau *)
    MP_TAC(ISPECL [`itcb1:S+R->(A,E,R)itree`; `itcb2:S+R->(A,E,R)itree`;
                   `k1:S->(A,E,S+R)itree`; `k2:S->(A,E,S+R)itree`;
                   `x1:S+R`; `u2:(A,E,S+R)itree`] itree_iter_ret_tau_wbisim) THEN
    ASM_REWRITE_TAC[];
    (* Ret, Vis *)
    QPAT_X_ASSUM "itree_wbisim (itree_Ret _) _"
      (MP_TAC o ONCE_REWRITE_RULE[itree_wbisim_cases]) THEN
    SIMP[itree_distinct];
    (* Tau, Ret *)
    MP_TAC(ISPECL [`itcb2:S+R->(A,E,R)itree`; `itcb1:S+R->(A,E,R)itree`;
                   `k2:S->(A,E,S+R)itree`; `k1:S->(A,E,S+R)itree`;
                   `x2:S+R`; `u1:(A,E,S+R)itree`] itree_iter_ret_tau_wbisim) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_MESON_TAC[itree_wbisim_sym]; MESON_TAC[itree_wbisim_sym]];
    (* Tau, Tau *)
    RULE_ASSUM_TAC(REWRITE_RULE[itree_wbisim_tau_eqn]) THEN
    REWRITE_TAC[itree_bind_thm; itree_11] THEN ASM_MESON_TAC[];
    (* Tau, Vis *)
    SUBGOAL_THEN `?k'. strip_tau (u1:(A,E,S+R)itree) (Vis e2 k') /\
                       !r. itree_wbisim ((g2:A->(A,E,S+R)itree) r) (k' r)`
    STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC itree_wbisim_strip_tau_Vis THEN
      EXISTS_TAC `Vis e2 g2:(A,E,S+R)itree` THEN REWRITE_TAC[strip_tau_simps3] THEN
      ASM_MESON_TAC[itree_wbisim_sym; itree_wbisim_tau_eqn];
      ALL_TAC] THEN
    DISJ2_TAC THEN DISJ1_TAC THEN
    MAP_EVERY EXISTS_TAC
     [`e2:E`;
      `\x. itree_bind ((k':A->(A,E,S+R)itree) x) (itcb1:S+R->(A,E,R)itree)`;
      `\x. itree_bind ((g2:A->(A,E,S+R)itree) x) (itcb2:S+R->(A,E,R)itree)`] THEN
    ASM_SIMP_TAC[itree_bind_thm; strip_tau_simps; strip_tau_simps3;
                 itree_bind_vis_strip_tau] THEN
    ASM_MESON_TAC[itree_wbisim_sym];
    (* Vis, Ret *)
    QPAT_X_ASSUM "itree_wbisim (Vis _ _) _"
      (MP_TAC o ONCE_REWRITE_RULE[itree_wbisim_cases]) THEN
    SIMP[itree_distinct];
    (* Vis, Tau *)
    SUBGOAL_THEN `?k'. strip_tau (u2:(A,E,S+R)itree) (Vis e1 k') /\
                       !r. itree_wbisim ((g1:A->(A,E,S+R)itree) r) (k' r)`
    STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC itree_wbisim_strip_tau_Vis THEN
      EXISTS_TAC `Vis e1 g1:(A,E,S+R)itree` THEN REWRITE_TAC[strip_tau_simps3] THEN
      ASM_MESON_TAC[itree_wbisim_tau_eqn];
      ALL_TAC] THEN
    DISJ2_TAC THEN DISJ1_TAC THEN
    MAP_EVERY EXISTS_TAC
     [`e1:E`;
      `\x. itree_bind ((g1:A->(A,E,S+R)itree) x) (itcb1:S+R->(A,E,R)itree)`;
      `\x. itree_bind ((k':A->(A,E,S+R)itree) x) (itcb2:S+R->(A,E,R)itree)`] THEN
    ASM_SIMP_TAC[itree_bind_thm; strip_tau_simps; strip_tau_simps3;
                 itree_bind_vis_strip_tau] THEN
    ASM_MESON_TAC[];
    (* Vis, Vis *)
    RULE_ASSUM_TAC(REWRITE_RULE[itree_wbisim_vis_vis]) THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
    DISJ2_TAC THEN DISJ1_TAC THEN
    MAP_EVERY EXISTS_TAC
     [`e1:E`;
      `\x. itree_bind ((g1:A->(A,E,S+R)itree) x) (itcb1:S+R->(A,E,R)itree)`;
      `\x. itree_bind ((g2:A->(A,E,S+R)itree) x) (itcb2:S+R->(A,E,R)itree)`] THEN
    ASM_SIMP_TAC[itree_bind_thm; strip_tau_simps3] THEN ASM_MESON_TAC[]]);;

let itree_iter_seed_wbisim = prove
 (`!(body:(B,C,D)itree->(A,E,(B,C,D)itree+R)itree) seed seed'.
     itree_wbisim seed seed' /\ itree_wbisim (body seed) (body seed') ==>
     itree_wbisim (itree_iter body seed) (itree_iter body seed')`,
  REPEAT STRIP_TAC THEN PURE_ONCE_REWRITE_TAC[itree_iter_thm] THEN
  MATCH_MP_TAC itree_bind_resp_wbisim THEN
  ASM_REWRITE_TAC[itree_wbisim_refl]);;

let itree_iter_body_seed_wbisim = prove
 (`!(body:(B,C,D)itree->(A,E,(B,C,D)itree+R)itree) body' seed seed'.
     itree_wbisim seed seed' /\
     (!seed seed'. itree_wbisim (body seed) (body' seed')) ==>
     itree_wbisim (itree_iter body seed) (itree_iter body' seed')`,
  REPEAT STRIP_TAC THEN PURE_ONCE_REWRITE_TAC[itree_iter_thm] THEN
  MATCH_MP_TAC itree_bind_resp_wbisim THEN ASM_REWRITE_TAC[] THEN
  GEN_TAC THEN QCASES_ON "r" THEN
  SIMP[itree_wbisim_refl; itree_wbisim_tau_eqn] THEN
  MATCH_MP_TAC itree_iter_resp_wbisim THEN ASM_REWRITE_TAC[]);;

(* coinduction upto stripping finite taus, useful for iter and friends *)

let after_taus_rules,after_taus_ind,after_taus_cases,after_taus_strongind =
  cake_inductive
 `(!(x:(A,E,R)itree) (y:(A,E,R)itree). R x y ==> after_taus R x y) /\
  (!x y. after_taus R x y ==> after_taus R (Tau x) y) /\
  (!x y. after_taus R x y ==> after_taus R x (Tau y))`;;

(* HOL4's rule names [~rel:], [~tauL:], [~tauR:] *)

let after_taus_rel,after_taus_tauL,after_taus_tauR =
  let ths = map (GEN `R:(A,E,R)itree->(A,E,R)itree->bool`)
             (CONJUNCTS (SPEC `R:(A,E,R)itree->(A,E,R)itree->bool`
                              after_taus_rules)) in
  el 0 ths,el 1 ths,el 2 ths;;

let after_taus_FUNPOW_TauL = prove
 (`!R x y:(A,E,R)itree n.
     after_taus R x y ==> after_taus R (ITER n Tau x) y`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN SPEC_TAC(`n:num`,`n:num`) THEN
  INDUCT_TAC THEN ASM_SIMP_TAC[ITER; after_taus_tauL]);;

let after_taus_FUNPOW_TauR = prove
 (`!R x y:(A,E,R)itree n.
     after_taus R x y ==> after_taus R x (ITER n Tau y)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN SPEC_TAC(`n:num`,`n:num`) THEN
  INDUCT_TAC THEN ASM_SIMP_TAC[ITER; after_taus_tauR]);;

let upto_taus_func_def = cake_def
 `upto_taus_func (R:(A,E,R)itree#(A,E,R)itree->bool) =
    R UNION UNCURRY (after_taus (CURRY R))`;;

(* HOL4's reln_to_rel_app *)

let ITREEAUX_CURRY_IN = prove
 (`!(X:A#B->bool) a b. CURRY X a b <=> (a,b) IN X`,
  REWRITE_TAC[CURRY_DEF; IN]);;

(* after_taus is monotone in its relation (helper) *)

let ITREEAUX_after_taus_mono = prove
 (`!R R':(A,E,R)itree->(A,E,R)itree->bool.
     (!x y. R x y ==> R' x y) ==>
     !x y. after_taus R x y ==> after_taus R' x y`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC after_taus_ind THEN
  ASM_MESON_TAC[after_taus_rules]);;

let upto_taus_compatible = prove
 (`ITREEAUX_set_compatible
     (wbisim_functional:((A,E,R)itree#(A,E,R)itree->bool)->
                        (A,E,R)itree#(A,E,R)itree->bool)
     upto_taus_func`,
  REWRITE_TAC[ITREEAUX_set_compatible_def; ITREEAUX_monotone_def] THEN
  CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    REWRITE_TAC[upto_taus_func_def; SUBSET; IN_UNION; FORALL_PAIR_THM;
                ITREEAUX_IN_UNCURRY] THEN
    REPEAT STRIP_TAC THENL
     [ASM_MESON_TAC[SUBSET];
      DISJ2_TAC THEN
      MP_TAC(ISPECL [`CURRY (X:(A,E,R)itree#(A,E,R)itree->bool)`;
                     `CURRY (Y:(A,E,R)itree#(A,E,R)itree->bool)`]
                    ITREEAUX_after_taus_mono) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[ITREEAUX_CURRY_IN] THEN ASM_MESON_TAC[SUBSET];
        ASM_MESON_TAC[]]];
    ALL_TAC] THEN
  GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [upto_taus_func_def] THEN
  REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THENL
   [MATCH_MP_TAC wbisim_functional_cancel THEN
    REWRITE_TAC[upto_taus_func_def] THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; FORALL_PAIR_THM; ITREEAUX_IN_UNCURRY] THEN
  MATCH_MP_TAC after_taus_ind THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[ITREEAUX_CURRY_IN] THEN
    MP_TAC(ISPECL [`X:(A,E,R)itree#(A,E,R)itree->bool`;
                   `upto_taus_func (X:(A,E,R)itree#(A,E,R)itree->bool)`]
                  wbisim_functional_cancel) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[upto_taus_func_def] THEN SET_TAC[];
      REWRITE_TAC[SUBSET] THEN MESON_TAC[]];
    ALL_TAC; ALL_TAC] THEN
  REWRITE_TAC[upto_taus_func_def; wbisim_functional_def; IN_UNION; IN_ELIM_THM;
              PAIR_EQ; ITREEAUX_IN_UNCURRY; strip_tau_simps; itree_11] THEN
  SIMP[] THEN MESON_TAC[after_taus_rules; ITREEAUX_CURRY_IN]);;

(* example: compatibility can be used like so *)

let itree_coind_upto_taus = prove
 (`!R:(A,E,R)itree->(A,E,R)itree->bool.
     UNCURRY R SUBSET
       UNCURRY itree_wbisim UNION
       wbisim_functional (upto_taus_func (UNCURRY R) UNION UNCURRY itree_wbisim)
     ==> UNCURRY R SUBSET UNCURRY itree_wbisim`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC itree_wbisim_coind_upto' THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
    `X SUBSET (G:A->bool) UNION Y ==> Y SUBSET Z ==> X SUBSET G UNION Z`)) THEN
  MATCH_MP_TAC wbisim_functional_cancel THEN REWRITE_TAC[UNION_SUBSET] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ITREEAUX_set_compatible_enhance THEN
    EXISTS_TAC `upto_taus_func:((A,E,R)itree#(A,E,R)itree->bool)->
                               (A,E,R)itree#(A,E,R)itree->bool` THEN
    REWRITE_TAC[wbisim_functional_mono; upto_taus_compatible; SUBSET_REFL];
    REWRITE_TAC[GSYM wbisim_functional_gfp] THEN
    MATCH_MP_TAC ITREEAUX_set_gfp_sub_companion THEN
    REWRITE_TAC[wbisim_functional_mono]]);;

(* misc.  HOL4's definition spin is rebound to the theorem spin below; the  *)
(* definition is ITREEAUX_spin_def (HOL4 () is one)                          *)

let ITREEAUX_spin_def = cake_def
 `spin = itree_unfold (K (Tau' one)) one:(A,E,R)itree`;;

let spin = prove
 (`spin:(A,E,R)itree = Tau spin`,
  REWRITE_TAC[ITREEAUX_spin_def] THEN GEN_REWRITE_TAC LAND_CONV [itree_unfold] THEN
  SIMP[K_THM]);;

(* relation to tauless itrees *)

let strip_tau_spin = prove
 (`!t:(A,E,R)itree. (!t'. ~strip_tau t t') ==> t = spin`,
  GEN_TAC THEN DISCH_TAC THEN ONCE_REWRITE_TAC[itree_bisimulation] THEN
  QEXISTS_TAC "\\t t'. (!t''. ~strip_tau t t'') /\\ t' = spin" THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  STRIP_TAC THENL
   [ASM_MESON_TAC[strip_tau_simps2];
    EXISTS_TAC `spin:(A,E,R)itree` THEN ASM_MESON_TAC[spin; strip_tau_simps];
    ASM_MESON_TAC[strip_tau_simps3]]);;

let spin_strip_tau = prove
 (`!t:(A,E,R)itree. strip_tau spin t ==> F`,
  SUBGOAL_THEN `!x t:(A,E,R)itree. strip_tau x t ==> x = spin ==> F`
    (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC strip_tau_ind THEN GEN_REWRITE_TAC ONCE_DEPTH_CONV [spin] THEN
  REWRITE_TAC[itree_11; itree_distinct] THEN MESON_TAC[spin]);;

(* ------------------------------------------------------------------------- *)
(* FUNPOW (HOL4 FUNPOW Tau n t is ITER n Tau t)                              *)
(* ------------------------------------------------------------------------- *)

let Tau_INJ = prove
 (`INJ (Tau:(A,E,R)itree->(A,E,R)itree) (:(A,E,R)itree) (:(A,E,R)itree)`,
  REWRITE_TAC[INJ; IN_UNIV; itree_11]);;
let _ = cake_add_simps [Tau_INJ];;

let FUNPOW_Tau_neq = prove
 (`(!(x:R) (a:E) (g:A->(A,E,R)itree) n. ~(itree_Ret x = ITER n Tau (Vis a g))) /\
   (!(x:R) (a:E) (g:A->(A,E,R)itree) n. ~(Vis a g = ITER n Tau (itree_Ret x)))`,
  CONJ_TAC THEN REPEAT GEN_TAC THEN SPEC_TAC(`n:num`,`n:num`) THEN
  INDUCT_TAC THEN SIMP[ITER]);;
let _ = cake_add_simps [FUNPOW_Tau_neq];;

let FUNPOW_Tau_neq2 = prove
 (`!n' (x:R) n (a:E) (g:A->(A,E,R)itree).
     ~(ITER n' Tau (itree_Ret x) = ITER n Tau (Vis a g))`,
  INDUCT_TAC THEN GEN_TAC THEN INDUCT_TAC THEN SIMP[ITER]);;
let _ = cake_add_simps [FUNPOW_Tau_neq2];;

let strip_tau_FUNPOW = prove
 (`!t1 t2:(A,E,R)itree. strip_tau t1 t2 ==> ?n. t1 = ITER n Tau t2`,
  MATCH_MP_TAC strip_tau_ind THEN MESON_TAC[ITER]);;

let FUNPOW_Tau_wbisim = prove
 (`!n x:(A,E,R)itree. itree_wbisim (ITER n Tau x) x`,
  INDUCT_TAC THEN SIMP[ITER; itree_wbisim_refl; itree_wbisim_tau_eqn]);;

let FUNPOW_Tau_wbisim_intro = prove
 (`!x y:(A,E,R)itree n n'.
     itree_wbisim x y ==> itree_wbisim (ITER n Tau x) (ITER n' Tau y)`,
  MESON_TAC[FUNPOW_Tau_wbisim; itree_wbisim_trans; itree_wbisim_sym]);;

let strip_tau_vis_wbisim = prove
 (`!t t':(A,E,R)itree e k k'.
     strip_tau t (Vis e k) /\ strip_tau t' (Vis e k') /\
     (!r. itree_wbisim (k r) (k' r)) ==>
     itree_wbisim t t'`,
  REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(CHOOSE_THEN SUBST1_TAC o MATCH_MP strip_tau_FUNPOW)) THEN
  MATCH_MP_TAC FUNPOW_Tau_wbisim_intro THEN SIMP[itree_wbisim_vis]);;

let itree_wbisim_Ret_FUNPOW = prove
 (`!t:(A,E,R)itree x.
     itree_wbisim t (itree_Ret x) ==> ?n. t = ITER n Tau (itree_Ret x)`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [itree_wbisim_cases] THEN
  SIMP[itree_distinct] THEN MESON_TAC[strip_tau_FUNPOW]);;

let FUNPOW_Tau_imp_wbisim = prove
 (`!t n t':(A,E,R)itree. t = ITER n Tau t' ==> itree_wbisim t t'`,
  MESON_TAC[FUNPOW_Tau_wbisim]);;

let itree_wbisim_Vis_FUNPOW = prove
 (`!t:(A,E,R)itree a g.
     itree_wbisim t (Vis a g) ==>
     ?n k. t = ITER n Tau (Vis a k) /\ (!r. itree_wbisim (k r) (g r))`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [itree_wbisim_cases] THEN
  SIMP[itree_distinct] THEN MESON_TAC[strip_tau_FUNPOW]);;

let wbisim_FUNPOW_Tau = prove
 (`(!t n ht:(A,E,R)itree.
      itree_wbisim t (ITER n Tau ht) <=> itree_wbisim t ht) /\
   (!n ht t:(A,E,R)itree.
      itree_wbisim (ITER n Tau ht) t <=> itree_wbisim ht t)`,
  MESON_TAC[FUNPOW_Tau_wbisim; itree_wbisim_trans; itree_wbisim_sym]);;

let FUNPOW_Tau_bind = prove
 (`!n t (g:R->(A,E,B)itree).
     itree_bind (ITER n Tau t) g = ITER n Tau (itree_bind t g)`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[ITER; itree_bind_thm]);;

let strip_tau_FUNPOW_cancel = prove
 (`!t:(A,E,R)itree n. (!u. ~(t = Tau u)) ==> strip_tau (ITER n Tau t) t`,
  GEN_TAC THEN INDUCT_TAC THEN SIMP[ITER] THEN QCASES_ON "t" THEN
  SIMP[] THEN MESON_TAC[]);;

let FUNPOW_Tau_Vis_eq = prove
 (`!n (a:E) (g:A->(A,E,R)itree) m e k.
     ITER n Tau (Vis a g) = ITER m Tau (Vis e k) ==> n = m /\ a = e /\ g = k`,
  INDUCT_TAC THEN REPEAT GEN_TAC THEN QCASES_ON "m" THEN
  SIMP[ITER; NOT_SUC; SUC_INJ] THEN ASM_MESON_TAC[]);;

let FUNPOW_Tau_Ret_eq = prove
 (`!n (x:R) m y.
     ITER n Tau (itree_Ret x:(A,E,R)itree) = ITER m Tau (itree_Ret y) ==>
     n = m /\ x = y`,
  INDUCT_TAC THEN REPEAT GEN_TAC THEN QCASES_ON "m" THEN
  SIMP[ITER; NOT_SUC; SUC_INJ] THEN ASM_MESON_TAC[]);;

(* more on spin *)

let spin_bind = prove
 (`!k:R->(A,E,B)itree. itree_bind spin k = spin`,
  GEN_TAC THEN ONCE_REWRITE_TAC[itree_bisimulation] THEN
  QEXISTS_TAC "\\x y. x = itree_bind spin k /\\ y = spin" THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV o LAND_CONV) [spin] THEN
  REWRITE_TAC[itree_bind_thm; itree_distinct; itree_11] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `spin:(A,E,B)itree` THEN
  ASM_MESON_TAC[spin]);;

let spin_FUNPOW_Tau = prove
 (`!n. spin:(A,E,R)itree = ITER n Tau spin`,
  INDUCT_TAC THEN REWRITE_TAC[ITER] THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM th]) THEN
  ACCEPT_TAC spin);;

let wbisim_spin_eq = prove
 (`!t:(A,E,R)itree. itree_wbisim t spin <=> t = spin`,
  GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN ONCE_REWRITE_TAC[itree_bisimulation] THEN
    QEXISTS_TAC "\\x y. itree_wbisim x spin /\\ y = spin" THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
     [GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [itree_wbisim_cases] THEN
      SIMP[itree_distinct; REWRITE_RULE[IMP_CLAUSES] spin_strip_tau];
      STRIP_TAC THEN EXISTS_TAC `spin:(A,E,R)itree` THEN
      ASM_MESON_TAC[spin; itree_wbisim_tau_eqn];
      GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [itree_wbisim_cases] THEN
      SIMP[itree_distinct; REWRITE_RULE[IMP_CLAUSES] spin_strip_tau]];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[itree_wbisim_refl]]);;

let strip_tau_FUNPOW_strip_tau = prove
 (`!t t':(A,E,R)itree n. strip_tau t t' ==> strip_tau (ITER n Tau t) t'`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN SPEC_TAC(`n:num`,`n:num`) THEN
  INDUCT_TAC THEN SIMP[ITER]);;

let FUNPOW_Ret_spin_F = prove
 (`!n (x:R). ITER n Tau (itree_Ret x) = spin:(A,E,R)itree ==> F`,
  INDUCT_TAC THEN GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [spin] THEN
  ASM_REWRITE_TAC[ITER; itree_11; itree_distinct] THEN ASM_MESON_TAC[]);;

let FUNPOW_Vis_spin_F = prove
 (`!n (e:E) (k:A->(A,E,R)itree). ITER n Tau (Vis e k) = spin ==> F`,
  INDUCT_TAC THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [spin] THEN
  ASM_REWRITE_TAC[ITER; itree_11; itree_distinct] THEN ASM_MESON_TAC[]);;

let FUNPOW_Tau_SUC_cyclic_spin = prove
 (`!t:(A,E,R)itree n. t = ITER (SUC n) Tau t <=> t = spin`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN
    ASM_CASES_TAC `?t':(A,E,R)itree. strip_tau t t'` THENL
     [FIRST_X_ASSUM(X_CHOOSE_TAC `t':(A,E,R)itree`) THEN
      FIRST_ASSUM(X_CHOOSE_TAC `m:num` o MATCH_MP strip_tau_FUNPOW) THEN
      SUBGOAL_THEN `?x. t':(A,E,R)itree = itree_Ret x \/ ?e k. t' = Vis e k`
        STRIP_ASSUME_TAC THENL
       [QCASES_ON "t'" THEN ASM_MESON_TAC[strip_tau_simps];
        ALL_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM SUBST_ALL_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
      FIRST_X_ASSUM(MP_TAC o check (is_eq o concl)) THEN
      REWRITE_TAC[ITER_ADD] THEN
      MESON_TAC[FUNPOW_Tau_Ret_eq; FUNPOW_Tau_Vis_eq;
                ARITH_RULE `~(m = SUC n + m)`];
      ASM_MESON_TAC[strip_tau_spin]];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[GSYM spin_FUNPOW_Tau]]);;

(* HOL4's variable abs is ab (abs is a HOL Light constant) *)

let FUNPOW_Tau_abs_cyclic_spin = prove
 (`!ab:B->(A,E,R)itree.
     (!r. ?n r'. ab r = ITER (SUC n) Tau (ab r')) <=> (!r. ab r = spin)`,
  GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN GEN_TAC THEN REWRITE_TAC[GSYM wbisim_spin_eq] THEN
    SUBGOAL_THEN `!x y:(A,E,R)itree.
                    (?n r. x = ITER n Tau ((ab:B->(A,E,R)itree) r)) /\ y = spin
                    ==> itree_wbisim x y`
      (fun th -> MESON_TAC[th; ITER]) THEN
    MATCH_MP_TAC itree_wbisim_coind THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    DISJ1_TAC THEN ASM_REWRITE_TAC[] THEN QCASES_ON "n" THEN
    REWRITE_TAC[ITER] THENL
     [FIRST_X_ASSUM(X_CHOOSE_THEN `m:num` (X_CHOOSE_TAC `r':B`) o
                    SPEC `r:B`) THEN
      ASM_REWRITE_TAC[ITER];
      ALL_TAC] THEN
    GEN_REWRITE_TAC (BINDER_CONV o BINDER_CONV o RAND_CONV o LAND_CONV o
                     LAND_CONV) [spin] THEN
    REWRITE_TAC[itree_11] THEN MESON_TAC[];
    DISCH_TAC THEN GEN_TAC THEN MAP_EVERY EXISTS_TAC [`0`; `r:B`] THEN
    ASM_REWRITE_TAC[GSYM spin_FUNPOW_Tau]]);;

let itree_wbisim_strip_tau_cases = prove
 (`!t t':(A,E,R)itree.
     itree_wbisim t t' <=>
     (t = spin /\ t' = spin) \/
     (?r. strip_tau t (itree_Ret r) /\ strip_tau t' (itree_Ret r)) \/
     (?e k k'. strip_tau t (Vis e k) /\ strip_tau t' (Vis e k') /\
               !l. itree_wbisim (k l) (k' l))`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN ASM_CASES_TAC `?t'':(A,E,R)itree. strip_tau t t''` THENL
     [FIRST_X_ASSUM(X_CHOOSE_TAC `t'':(A,E,R)itree`) THEN
      QCASES_ON "t''" THENL
       [ASM_MESON_TAC[itree_wbisim_strip_tau_Ret];
        ASM_MESON_TAC[strip_tau_simps];
        ASM_MESON_TAC[itree_wbisim_strip_tau_Vis]];
      DISJ1_TAC THEN
      SUBGOAL_THEN `t:(A,E,R)itree = spin` SUBST_ALL_TAC THENL
       [ASM_MESON_TAC[strip_tau_spin]; ALL_TAC] THEN
      ASM_MESON_TAC[wbisim_spin_eq; itree_wbisim_sym]];
    STRIP_TAC THEN ASM_REWRITE_TAC[itree_wbisim_refl] THEN
    ASM_MESON_TAC[itree_wbisim_rules]]);;

let after_taus_itree_strong_bisim_spin_spin = prove
 (`!t t':(A,E,R)itree. after_taus (=) t t' ==> t' = spin ==> t = spin`,
  MATCH_MP_TAC after_taus_ind THEN MESON_TAC[spin; itree_11]);;

let after_taus_itree_strong_bisim_strip_tau = prove
 (`!t t':(A,E,R)itree.
     after_taus (=) t t' <=>
     (?t''. strip_tau t t'' /\ strip_tau t' t'') \/ (t = spin /\ t' = spin)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [SPEC_TAC(`t':(A,E,R)itree`,`t':(A,E,R)itree`) THEN
    SPEC_TAC(`t:(A,E,R)itree`,`t:(A,E,R)itree`) THEN
    MATCH_MP_TAC after_taus_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
     [DISCH_THEN SUBST1_TAC THEN MESON_TAC[strip_tau_spin];
      REWRITE_TAC[strip_tau_simps] THEN MESON_TAC[spin];
      REWRITE_TAC[strip_tau_simps] THEN MESON_TAC[spin]];
    STRIP_TAC THENL
     [REPEAT(FIRST_X_ASSUM(CHOOSE_THEN SUBST1_TAC o MATCH_MP strip_tau_FUNPOW)) THEN
      MATCH_MP_TAC after_taus_FUNPOW_TauL THEN
      MATCH_MP_TAC after_taus_FUNPOW_TauR THEN
      MATCH_MP_TAC after_taus_rel THEN REWRITE_TAC[];
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC after_taus_rel THEN REWRITE_TAC[]]]);;

let after_taus_itree_wbisim_spin_spin = prove
 (`!t t':(A,E,R)itree. after_taus itree_wbisim t t' ==> t' = spin ==> t = spin`,
  MATCH_MP_TAC after_taus_ind THEN MESON_TAC[spin; itree_11; wbisim_spin_eq]);;

let after_taus_itree_wbisim_itree_wbisim = prove
 (`!t t':(A,E,R)itree. after_taus itree_wbisim t t' <=> itree_wbisim t t'`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [SPEC_TAC(`t':(A,E,R)itree`,`t':(A,E,R)itree`) THEN
    SPEC_TAC(`t:(A,E,R)itree`,`t:(A,E,R)itree`) THEN
    MATCH_MP_TAC after_taus_ind THEN SIMP[];
    MESON_TAC[after_taus_rel]]);;

(* strong bisimulation from an instance up to full tree of an abstraction.  *)
(* HOL4's variables abs, abs' are ab, ab' (abs is a HOL Light constant)      *)

let strong_bisim_upfrom_abs_rules,strong_bisim_upfrom_abs_coind,
    strong_bisim_upfrom_abs_cases =
  new_coinductive_definition
 `(!(ab:B->(A,E,R)itree) ab' x.
     strong_bisim_upfrom_abs (ab,ab') (itree_Ret x) (itree_Ret x)) /\
  (!ab ab' e k k'.
     (!l. strong_bisim_upfrom_abs (ab,ab') (k l) (k' l) \/
          ?r. k l = ab r /\ k' l = ab' r) ==>
     strong_bisim_upfrom_abs (ab,ab') (Vis e k) (Vis e k')) /\
  (!ab ab' t t'.
     (?r. t = ab r /\ t' = ab' r) ==>
     strong_bisim_upfrom_abs (ab,ab') (Tau t) (Tau t')) /\
  (!ab ab' t t'.
     strong_bisim_upfrom_abs (ab,ab') t t' ==>
     strong_bisim_upfrom_abs (ab,ab') (Tau t) (Tau t'))`;;

let strong_bisim_upfrom_abs_FUNPOW_Tau = prove
 (`!(ab:B->(A,E,R)itree) ab' t t' n.
     strong_bisim_upfrom_abs (ab,ab') t t' ==>
     strong_bisim_upfrom_abs (ab,ab') (ITER n Tau t) (ITER n Tau t')`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN SPEC_TAC(`n:num`,`n:num`) THEN
  INDUCT_TAC THEN ASM_SIMP_TAC[ITER; strong_bisim_upfrom_abs_rules]);;

let strong_bisim_upfrom_abs_FUNPOW_Tau_SUC_abs = prove
 (`!(ab:B->(A,E,R)itree) ab' n r.
     strong_bisim_upfrom_abs (ab,ab') (ITER (SUC n) Tau (ab r))
                                      (ITER (SUC n) Tau (ab' r))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ITER_ALT] THEN
  MATCH_MP_TAC strong_bisim_upfrom_abs_FUNPOW_Tau THEN
  MESON_TAC[strong_bisim_upfrom_abs_rules]);;

let strong_bisim_upfrom_abs_strong = prove
 (`!(ab:B->(A,E,R)itree) t t'.
     strong_bisim_upfrom_abs (ab,ab) t t' <=> t = t'`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN ONCE_REWRITE_TAC[itree_strong_bisimulation] THEN
    EXISTS_TAC `\t t':(A,E,R)itree.
                  strong_bisim_upfrom_abs (ab:B->(A,E,R)itree,ab) t t'` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [strong_bisim_upfrom_abs_cases] THEN
    REWRITE_TAC[PAIR_EQ; itree_distinct; itree_11] THEN MESON_TAC[];
    DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `!ap t t':(A,E,R)itree.
                    ap = (ab:B->(A,E,R)itree,ab) /\ t = t' ==>
                    strong_bisim_upfrom_abs ap t t'`
      (fun th -> MESON_TAC[th]) THEN
    MATCH_MP_TAC strong_bisim_upfrom_abs_coind THEN REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC SUBST1_TAC) THEN
    QCASES_ON "t'" THEN REWRITE_TAC[PAIR_EQ; itree_distinct; itree_11] THEN
    MESON_TAC[]]);;

let cyclic_strong_bisim_upfrom_abs = prove
 (`!(ab:B->(A,E,R)itree) ab'.
     (!r. strong_bisim_upfrom_abs (ab,ab') (ab r) (ab' r)) <=> ab = ab'`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `r0:B` THEN
    ONCE_REWRITE_TAC[itree_strong_bisimulation] THEN
    EXISTS_TAC `\t t':(A,E,R)itree.
                  strong_bisim_upfrom_abs (ab:B->(A,E,R)itree,ab') t t'` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [strong_bisim_upfrom_abs_cases] THEN
    REWRITE_TAC[PAIR_EQ; itree_distinct; itree_11] THEN ASM_MESON_TAC[];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[strong_bisim_upfrom_abs_strong]]);;

let strong_bisim_upfrom_abs_strong_bind = prove
 (`!(ab:B->(A,E,R)itree) ab' (k:C->(A,E,R)itree) k' t.
     (!r. strong_bisim_upfrom_abs (ab,ab') (k r) (k' r)) ==>
     strong_bisim_upfrom_abs (ab,ab') (itree_bind t k) (itree_bind t k')`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!ap x0 y0:(A,E,R)itree.
      ap = (ab:B->(A,E,R)itree,ab') /\
      ((?t0:(A,E,C)itree. x0 = itree_bind t0 k /\ y0 = itree_bind t0 k') \/
       strong_bisim_upfrom_abs (ab,ab') x0 y0)
      ==> strong_bisim_upfrom_abs ap x0 y0`
    (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC strong_bisim_upfrom_abs_coind THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[PAIR_EQ] THENL
   [NAMED_CASES_ON "t0" ["r0"; "u0"; "e0 g0"] THEN
    REWRITE_TAC[itree_bind_thm; itree_distinct; itree_11] THENL
     [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [strong_bisim_upfrom_abs_cases] o
                    SPEC `r0:C`) THEN
      REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[];
      MESON_TAC[];
      MESON_TAC[]];
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [strong_bisim_upfrom_abs_cases]) THEN
    REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[]]);;

let cyclic_strong_bisim_upfrom_abs_strong_upfrom = prove
 (`!(ab:B->(A,E,R)itree) ab' t t'.
     (!r. strong_bisim_upfrom_abs (ab,ab') (ab r) (ab' r)) /\
     strong_bisim_upfrom_abs (ab,ab') t t' ==> t = t'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cyclic_strong_bisim_upfrom_abs] THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ASM_MESON_TAC[strong_bisim_upfrom_abs_strong]);;

let itree_strong_bisim_upfrom_abs = prove
 (`!(ab:B->(A,E,R)itree) ab' t. strong_bisim_upfrom_abs (ab,ab') t t`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `!ap t t':(A,E,R)itree.
                  ap = (ab:B->(A,E,R)itree,ab') /\ t = t' ==>
                  strong_bisim_upfrom_abs ap t t'`
    (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC strong_bisim_upfrom_abs_coind THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC SUBST1_TAC) THEN
  QCASES_ON "t'" THEN REWRITE_TAC[PAIR_EQ; itree_distinct; itree_11] THEN
  MESON_TAC[]);;

(* weak bisimulation from an instance up to full tree of an abstraction     *)
(* (HOL4's comment says strong)                                              *)

let weak_bisim_upfrom_abs_rules,weak_bisim_upfrom_abs_coind,
    weak_bisim_upfrom_abs_cases =
  new_coinductive_definition
 `(!(ab:B->(A,E,R)itree) ab' t t' x.
     strip_tau t (itree_Ret x) /\ strip_tau t' (itree_Ret x) ==>
     weak_bisim_upfrom_abs (ab,ab') t t') /\
  (!ab ab' t t' e k k' n n' r.
     strip_tau t (Vis e k) /\ strip_tau t' (Vis e k') /\
     (!l. weak_bisim_upfrom_abs (ab,ab') (k l) (k' l) \/
          k l = ITER n Tau (ab r) /\ k' l = ITER n' Tau (ab' r)) ==>
     weak_bisim_upfrom_abs (ab,ab') t t') /\
  (!ab ab' n n' r.
     weak_bisim_upfrom_abs (ab,ab') (ITER (SUC n) Tau (ab r))
                                    (ITER (SUC n') Tau (ab' r))) /\
  (!ab ab' t t' n n'.
     weak_bisim_upfrom_abs (ab,ab') t t' ==>
     weak_bisim_upfrom_abs (ab,ab') (ITER (SUC n) Tau t) (ITER (SUC n') Tau t'))`;;

let weak_bisim_upfrom_abs_spin = prove
 (`!(ab:B->(A,E,R)itree) ab'. weak_bisim_upfrom_abs (ab,ab') spin spin`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `!ap t t':(A,E,R)itree.
                  ap = (ab:B->(A,E,R)itree,ab') /\ t = spin /\ t' = spin ==>
                  weak_bisim_upfrom_abs ap t t'`
    (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC weak_bisim_upfrom_abs_coind THEN REPEAT GEN_TAC THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
  DISJ2_TAC THEN DISJ2_TAC THEN DISJ2_TAC THEN
  MAP_EVERY EXISTS_TAC [`ab:B->(A,E,R)itree`; `ab':B->(A,E,R)itree`;
                        `spin:(A,E,R)itree`; `spin:(A,E,R)itree`; `0`; `0`] THEN
  REWRITE_TAC[ITER; GSYM spin]);;

let weak_bisim_upfrom_abs_tauL = prove
 (`!(ab:B->(A,E,R)itree) ab' t'' t'''.
     weak_bisim_upfrom_abs (ab,ab') t'' t''' ==>
     weak_bisim_upfrom_abs (ab,ab') (Tau t'') t'''`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o GEN_REWRITE_RULE I [weak_bisim_upfrom_abs_cases]) THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM(CONJUNCT2 ITER)] THEN
  ASM_MESON_TAC[weak_bisim_upfrom_abs_rules; strip_tau_simps]);;

let weak_bisim_upfrom_abs_tauR = prove
 (`!(ab:B->(A,E,R)itree) ab' t'' t'''.
     weak_bisim_upfrom_abs (ab,ab') t'' t''' ==>
     weak_bisim_upfrom_abs (ab,ab') t'' (Tau t''')`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o GEN_REWRITE_RULE I [weak_bisim_upfrom_abs_cases]) THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM(CONJUNCT2 ITER)] THEN
  ASM_MESON_TAC[weak_bisim_upfrom_abs_rules; strip_tau_simps]);;

let weak_bisim_upfrom_cyclic_abs_FUNPOW_Tau = prove
 (`!(ab:B->(A,E,R)itree) ab' t'' t''' n n'.
     weak_bisim_upfrom_abs (ab,ab') t'' t''' ==>
     weak_bisim_upfrom_abs (ab,ab') (ITER n Tau t'') (ITER n' Tau t''')`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN SPEC_TAC(`n':num`,`n':num`) THEN
  INDUCT_TAC THEN REWRITE_TAC[ITER] THEN
  ASM_SIMP_TAC[weak_bisim_upfrom_abs_tauR] THEN
  SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THEN REWRITE_TAC[ITER] THEN
  ASM_SIMP_TAC[weak_bisim_upfrom_abs_tauL]);;

let weak_bisim_upfrom_abs_wbisim_bind = prove
 (`!(ab:B->(A,E,R)itree) ab' t t' (k:C->(A,E,R)itree) k'.
     itree_wbisim t t' /\ (!r. weak_bisim_upfrom_abs (ab,ab') (k r) (k' r)) ==>
     weak_bisim_upfrom_abs (ab,ab') (itree_bind t k) (itree_bind t' k')`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!ap x0 y0:(A,E,R)itree.
      ap = (ab:B->(A,E,R)itree,ab') /\
      ((?u u':(A,E,C)itree. x0 = itree_bind u k /\ y0 = itree_bind u' k' /\
                            itree_wbisim u u') \/
       weak_bisim_upfrom_abs (ab,ab') x0 y0)
      ==> weak_bisim_upfrom_abs ap x0 y0`
    (fun th -> ASM_MESON_TAC[th]) THEN
  MATCH_MP_TAC weak_bisim_upfrom_abs_coind THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[PAIR_EQ] THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [itree_wbisim_strip_tau_cases]) THEN
    STRIP_TAC THENL
     [ASM_REWRITE_TAC[spin_bind] THEN DISJ2_TAC THEN DISJ2_TAC THEN DISJ2_TAC THEN
      MAP_EVERY EXISTS_TAC [`ab:B->(A,E,R)itree`; `ab':B->(A,E,R)itree`;
                            `spin:(A,E,R)itree`; `spin:(A,E,R)itree`; `0`; `0`] THEN
      REWRITE_TAC[ITER; GSYM spin] THEN
      DISJ2_TAC THEN MATCH_ACCEPT_TAC weak_bisim_upfrom_abs_spin;
      SUBGOAL_THEN `weak_bisim_upfrom_abs (ab:B->(A,E,R)itree,ab')
                      (itree_bind (u:(A,E,C)itree) (k:C->(A,E,R)itree))
                      (itree_bind (u':(A,E,C)itree) k')` MP_TAC THENL
       [REPEAT(FIRST_X_ASSUM(CHOOSE_THEN SUBST1_TAC o
                             MATCH_MP strip_tau_FUNPOW)) THEN
        REWRITE_TAC[FUNPOW_Tau_bind; itree_bind_thm] THEN
        MATCH_MP_TAC weak_bisim_upfrom_cyclic_abs_FUNPOW_Tau THEN
        ASM_REWRITE_TAC[];
        GEN_REWRITE_TAC LAND_CONV [weak_bisim_upfrom_abs_cases] THEN
        REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[]];
      DISJ2_TAC THEN DISJ1_TAC THEN
      MAP_EVERY EXISTS_TAC
       [`ab:B->(A,E,R)itree`; `ab':B->(A,E,R)itree`; `e:E`;
        `\x. itree_bind ((k'':A->(A,E,C)itree) x) (k:C->(A,E,R)itree)`;
        `\x. itree_bind ((k''':A->(A,E,C)itree) x) (k':C->(A,E,R)itree)`] THEN
      ASM_SIMP_TAC[itree_bind_vis_strip_tau] THEN ASM_MESON_TAC[]];
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [weak_bisim_upfrom_abs_cases]) THEN
    REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[]]);;

let itree_wbisim_weak_upfrom_abs = prove
 (`!(ab:B->(A,E,R)itree) t' t''.
     itree_wbisim t' t'' ==> weak_bisim_upfrom_abs (ab,ab) t' t''`,
  GEN_TAC THEN
  SUBGOAL_THEN `!ap t t':(A,E,R)itree.
                  ap = (ab:B->(A,E,R)itree,ab) /\ itree_wbisim t t' ==>
                  weak_bisim_upfrom_abs ap t t'`
    (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC weak_bisim_upfrom_abs_coind THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC MP_TAC) THEN
  GEN_REWRITE_TAC LAND_CONV [itree_wbisim_strip_tau_cases] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THENL
   [ASM_REWRITE_TAC[] THEN DISJ2_TAC THEN DISJ2_TAC THEN DISJ2_TAC THEN
    MAP_EVERY EXISTS_TAC [`ab:B->(A,E,R)itree`; `ab:B->(A,E,R)itree`;
                          `spin:(A,E,R)itree`; `spin:(A,E,R)itree`; `0`; `0`] THEN
    REWRITE_TAC[ITER; GSYM spin; itree_wbisim_refl];
    ASM_MESON_TAC[];
    ASM_MESON_TAC[]]);;

let weak_bisim_upfrom_weak_abs = prove
 (`!(ab:B->(A,E,R)itree) t' t''.
     weak_bisim_upfrom_abs (ab,ab) t' t'' <=> itree_wbisim t' t''`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [ALL_TAC; REWRITE_TAC[itree_wbisim_weak_upfrom_abs]] THEN
  SPEC_TAC(`t'':(A,E,R)itree`,`t'':(A,E,R)itree`) THEN
  SPEC_TAC(`t':(A,E,R)itree`,`t':(A,E,R)itree`) THEN
  MATCH_MP_TAC itree_wbisim_strong_coind THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [weak_bisim_upfrom_abs_cases] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN ASM_REWRITE_TAC[ITER; itree_11] THEN
  ASM_MESON_TAC[FUNPOW_Tau_wbisim_intro; itree_wbisim_refl;
                weak_bisim_upfrom_cyclic_abs_FUNPOW_Tau]);;

(* the last three theorems of HOL4's script are proved in the order          *)
(* itree_wbisim_weak_bisim_upfrom_abs, cyclic_weak_bisim_upfrom_abs_weak_upfrom, *)
(* cyclic_weak_bisim_upfrom_abs (HOL4: the reverse order), so that the third *)
(* follows from the first two                                                 *)

let itree_wbisim_weak_bisim_upfrom_abs = prove
 (`!(ab:B->(A,E,R)itree) ab' t t'.
     itree_wbisim t t' ==> weak_bisim_upfrom_abs (ab,ab') t t'`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `!ap t t':(A,E,R)itree.
                  ap = (ab:B->(A,E,R)itree,ab') /\ itree_wbisim t t' ==>
                  weak_bisim_upfrom_abs ap t t'`
    (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC weak_bisim_upfrom_abs_coind THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC MP_TAC) THEN
  GEN_REWRITE_TAC LAND_CONV [itree_wbisim_strip_tau_cases] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THENL
   [ASM_REWRITE_TAC[] THEN DISJ2_TAC THEN DISJ2_TAC THEN DISJ2_TAC THEN
    MAP_EVERY EXISTS_TAC [`ab:B->(A,E,R)itree`; `ab':B->(A,E,R)itree`;
                          `spin:(A,E,R)itree`; `spin:(A,E,R)itree`; `0`; `0`] THEN
    REWRITE_TAC[ITER; GSYM spin; itree_wbisim_refl];
    ASM_MESON_TAC[];
    ASM_MESON_TAC[]]);;

let cyclic_weak_bisim_upfrom_abs_weak_upfrom = prove
 (`!(ab:B->(A,E,R)itree) ab' t t'.
     (!r. weak_bisim_upfrom_abs (ab,ab') (ab r) (ab' r)) /\
     weak_bisim_upfrom_abs (ab,ab') t t' ==> itree_wbisim t t'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM IMP_IMP] THEN DISCH_TAC THEN
  SPEC_TAC(`t':(A,E,R)itree`,`t':(A,E,R)itree`) THEN
  SPEC_TAC(`t:(A,E,R)itree`,`t:(A,E,R)itree`) THEN
  MATCH_MP_TAC itree_wbisim_strong_coind THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [weak_bisim_upfrom_abs_cases] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN ASM_REWRITE_TAC[ITER; itree_11] THEN
  ASM_MESON_TAC[weak_bisim_upfrom_cyclic_abs_FUNPOW_Tau]);;

let cyclic_weak_bisim_upfrom_abs = prove
 (`!(ab:B->(A,E,R)itree) ab'.
     (!r. weak_bisim_upfrom_abs (ab,ab') (ab r) (ab' r)) <=>
     (!r. itree_wbisim (ab r) (ab' r))`,
  MESON_TAC[cyclic_weak_bisim_upfrom_abs_weak_upfrom;
            itree_wbisim_weak_bisim_upfrom_abs]);;
