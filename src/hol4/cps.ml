(* ========================================================================= *)
(* cps: port of HOL4 src/transfer/examples/cpsScript.sml (HOL4 library used *)
(* by CakeML v3479; the cps theory that tcallUnif and CakeML's unify use,   *)
(* not examples/dev/sw/cpsScript.sml): the continuation combinators cwc and *)
(* contify and the theorems that push contify through terms.                *)
(*                                                                           *)
(* Notes: HOL4's cpsLib (contify_CONV, cwcp) is ML automation and is not    *)
(* ported.  HOL4 case expressions are the kit's case constants (list_CASE,  *)
(* pair_CASE, option_CASE).  HOL4 h::t is CONS h t and ++ is APPEND.        *)
(* HOL4 cwc is cps_cwc (a short name), and cwc_def is cps_cwc_def.           *)
(* ========================================================================= *)

needs "hol4/vocab.ml";;

type_invention_error := true;;

let cps_cwc_def = new_definition
  `cps_cwc (v:A) (k:A->B) = k v`;;

let contify_def = new_definition
  `contify (k:A->B) (v:A) = k v`;;

let contify_app = prove
 (`!(k:B->C) (f:A->B) x.
     contify k (f x) = contify (\fk. contify (\xk. cps_cwc (fk xk) k) x) f`,
  REWRITE_TAC[contify_def; cps_cwc_def]);;

let contify_COND = prove
 (`!(k:A->B) g t e.
     contify k (if g then t else e) =
     contify (\gk. if gk then contify k t else contify k e) g`,
  REPEAT GEN_TAC THEN REWRITE_TAC[contify_def] THEN COND_CASES_TAC THEN
  REWRITE_TAC[]);;

let FACTk_def = new_definition
  `FACTk x (k:num->A) = cps_cwc (FACT x) k`;;

let FACT_EQN = prove
 (`!n. FACT n = if n < 2 then 1 else n * FACT (n - 1)`,
  GEN_TAC THEN COND_CASES_TAC THENL
   [SUBGOAL_THEN `n = 0 \/ n = SUC 0` (DISJ_CASES_THEN SUBST1_TAC) THENL
     [ASM_ARITH_TAC; ALL_TAC; ALL_TAC] THEN REWRITE_TAC[FACT] THEN ARITH_TAC;
    MP_TAC(SPEC `n:num` num_CASES) THEN STRIP_TAC THENL
     [ASM_MESON_TAC[ARITH_RULE `0 < 2`];
      ASM_REWRITE_TAC[FACT; SUC_SUB1]]]);;

let REVERSE_EQN = prove
 (CASE_TERM `!l:A list. REVERSE l =
     (match l with [] -> [] | CONS h t -> APPEND (REVERSE t) [h])`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[REVERSE; list_CASE]);;

let contify_cwc = prove
 (`!(k:A->B) x. contify k x = cps_cwc x k`,
  REWRITE_TAC[contify_def; cps_cwc_def]);;

let kREVERSE_def = new_definition
  `REVERSEk (x:A list) (k:A list->B) = cps_cwc (REVERSE x) k`;;

let contify_list_case = prove
 (CASE_TERM `!(k:B->C) (x:A list) n c.
     contify k (list_CASE x n c) =
     contify (\xk. match xk with [] -> contify k n
                               | CONS h t -> contify k (c h t)) x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[contify_def] THEN
  STRUCT_CASES_TAC(ISPEC `x:A list` list_CASES) THEN REWRITE_TAC[list_CASE]);;

let contify_pair_case = prove
 (`!(k:C->D) (p:A#B) f.
     contify k (pair_CASE p f) =
     contify (\p. pair_CASE p (\x y. contify k (f x y))) p`,
  REPEAT GEN_TAC THEN REWRITE_TAC[contify_def] THEN
  STRUCT_CASES_TAC(ISPEC `p:A#B` PAIR_SURJECTIVE) THEN REWRITE_TAC[pair_CASE]);;

let contify_option_case = prove
 (`!(k:B->C) (ov:A option) n sf.
     contify k (option_CASE ov n sf) =
     contify (\ov. option_CASE ov (contify k n) (\x. contify k (sf x))) ov`,
  REPEAT GEN_TAC THEN REWRITE_TAC[contify_def] THEN
  STRUCT_CASES_TAC(ISPEC `ov:A option` (cases "option")) THEN
  REWRITE_TAC[option_CASE]);;
