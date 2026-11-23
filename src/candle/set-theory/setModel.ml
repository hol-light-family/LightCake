(* ========================================================================= *)
(* setModel: port of HOL4 candle/set-theory/setModelScript.sml (CakeML      *)
(* v3479).  An example universe satisfying is_set_theory and (assuming the   *)
(* existence of an infinite set) is_model.                                   *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - HOL4's type alpha + num is the HOL Light sum type A+num.                *)
(* - l_model_exists: as in HOL4, the model is the hereditarily finite sets   *)
(*   coded by numbers, INR n with membership numbit (HOL4 BIT).  The         *)
(*   witness predicate is \x. ?n. x = INR n (HOL4 ISR), and the sets are     *)
(*   built with HOL Light's bits_of_num (Library/words.ml) instead of HOL4's *)
(*   digit lists (l2n, n2l, GENLIST): the same witnesses, a shorter proof.   *)
(* - The type V is made by new_type_definition "V" ("mk_V","dest_V");        *)
(*   V_TY_DEF states HOL4's TYPE_DEFINITION is_V rep with TYPE_DEFINITION    *)
(*   unfolded (HOL Light has no such constant).                              *)
(* - is_model_V: HOL4's bound variable I (a HOL Light constant) is i.        *)
(* - Helpers that are not HOL4 theorems have the prefix CSETAUX_.            *)
(* ========================================================================= *)

needs "candle/set-theory/setSpec.ml";;

prioritize_num();;
type_invention_error := true;;

let is_set_theory_pred_def = cake_def
  `is_set_theory_pred (is_v_rep:A->bool) in_rep <=>
   (?x. is_v_rep x) /\
   (!x y. is_v_rep x /\ is_v_rep y ==>
          ((x = y) <=> (!a. is_v_rep a ==> (in_rep a x <=> in_rep a y)))) /\
   (!x P. is_v_rep x ==>
          ?y. is_v_rep y /\
              !a. is_v_rep a ==> (in_rep a y <=> (in_rep a x /\ P a))) /\
   (!x. is_v_rep x ==>
        ?y. is_v_rep y /\
            (!a. is_v_rep a ==>
                 (in_rep a y <=> (!b. is_v_rep b ==> in_rep b a ==> in_rep b x)))) /\
   (!x. is_v_rep x ==>
        ?y. is_v_rep y /\
            (!a. is_v_rep a ==>
                 (in_rep a y <=> (?b. is_v_rep b /\ in_rep a b /\ in_rep b x)))) /\
   (!x y. is_v_rep x /\ is_v_rep y ==>
          ?z. is_v_rep z /\
              (!a. is_v_rep a ==> (in_rep a z <=> (a = x \/ a = y)))) /\
   (!x. is_v_rep x ==>
        ?y. is_v_rep y /\ (!a. is_v_rep a /\ in_rep a x ==> in_rep y x))`;;

(* ------------------------------------------------------------------------- *)
(* Numbers as finite sets of numbers: numbit k n means that k is in n.       *)
(* ------------------------------------------------------------------------- *)

let CSETAUX_numbit_exists = prove
 (`!P. FINITE {k | P k} ==> ?n. !k. numbit k n <=> P k`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `nsum {k | P k} (\i. 2 EXP i)` THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP BITS_OF_NUM_NSUM) THEN
  REWRITE_TAC[EXTENSION; bits_of_num; IN_ELIM_THM]);;

let CSETAUX_numbit_lt = prove
 (`!k n. numbit k n ==> k < n`,
  MP_TAC BITS_OF_NUM_SUBSET_NUMSEG_LT THEN
  REWRITE_TAC[SUBSET; bits_of_num; IN_ELIM_THM] THEN MESON_TAC[]);;

let CSETAUX_numbit_le = prove
 (`!m n. (!k. numbit k m ==> numbit k n) ==> m <= n`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`bits_of_num m`; `bits_of_num n`; `\i:num. 2 EXP i`]
    NSUM_SUBSET_SIMPLE) THEN
  ASM_REWRITE_TAC[NSUM_BITS_OF_NUM; FINITE_BITS_OF_NUM; SUBSET; bits_of_num;
                  IN_ELIM_THM]);;

(* HOL4 proves each part with explicit digit lists; here each set is the     *)
(* number whose bits are a finite set of numbers (CSETAUX_numbit_exists).    *)

let l_model_exists = prove
 (`?(P:A+num->bool) (mem:A+num->A+num->bool). is_set_theory_pred P mem`,
  QEXISTS_TAC "\\x:A+num. ?n. x = INR n" THEN
  REWRITE_TAC[is_set_theory_pred_def] THEN
  QEXISTS_TAC "\\l1 l2:A+num. numbit (OUTR l1) (OUTR l2)" THEN
  SIMP[PULL_EXISTS; OUTR] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM NUMBIT_EQ];
    REPEAT GEN_TAC THEN MATCH_MP_TAC CSETAUX_numbit_exists THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{k:num | k < n}` THEN
    REWRITE_TAC[FINITE_NUMSEG_LT; SUBSET; IN_ELIM_THM] THEN
    MESON_TAC[CSETAUX_numbit_lt];
    REPEAT GEN_TAC THEN MATCH_MP_TAC CSETAUX_numbit_exists THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{k:num | k <= n}` THEN
    REWRITE_TAC[FINITE_NUMSEG_LE; SUBSET; IN_ELIM_THM] THEN
    MESON_TAC[CSETAUX_numbit_le];
    REPEAT GEN_TAC THEN MATCH_MP_TAC CSETAUX_numbit_exists THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{k:num | k < n}` THEN
    REWRITE_TAC[FINITE_NUMSEG_LT; SUBSET; IN_ELIM_THM] THEN
    MESON_TAC[CSETAUX_numbit_lt; LT_TRANS];
    REPEAT GEN_TAC THEN MATCH_MP_TAC CSETAUX_numbit_exists THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{n:num, n'}` THEN
    REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; SUBSET; IN_ELIM_THM;
                IN_INSERT; NOT_IN_EMPTY];
    MESON_TAC[]]);;

let is_V_def = new_specification ["is_V"]
  (REWRITE_RULE[is_set_theory_pred_def] l_model_exists);;

(* HOL4: the type definition theorem V_tyax, ?x. is_V x (an ML value) *)

let CSETAUX_V_inhabited = prove
 (`?x:A+num. is_V x`,
  MP_TAC is_V_def THEN MESON_TAC[]);;

let setModel_V_bij =
  new_type_definition "V" ("mk_V","dest_V") CSETAUX_V_inhabited;;

let V_TY_DEF = prove
 (`?rep:A V->A+num. (!x' x''. rep x' = rep x'' ==> x' = x'') /\
                    (!x. is_V x <=> ?x'. x = rep x')`,
  EXISTS_TAC `dest_V:A V->A+num` THEN MESON_TAC[setModel_V_bij]);;

(* HOL4: dest_V_11 = prove_rep_fn_one_one V_bij (an ML value) *)

let CSETAUX_dest_V_11 = prove
 (`!a a':A V. dest_V a = dest_V a' <=> a = a'`,
  MESON_TAC[setModel_V_bij]);;

let setModel_V_mem_rep_def = new_specification ["V_mem_rep"] is_V_def;;

let setModel_V_mem_def = cake_def
  `V_mem (x:A V) y <=> V_mem_rep (dest_V x) (dest_V y)`;;

(* quantifiers over is_V as quantifiers over the type V *)

let CSETAUX_FORALL_is_V = prove
 (`!P. (!r:A+num. is_V r ==> P r) <=> (!a:A V. P (dest_V a))`,
  MESON_TAC[setModel_V_bij]);;

let CSETAUX_EXISTS_is_V = prove
 (`!P. (?r:A+num. is_V r /\ P r) <=> (?a:A V. P (dest_V a))`,
  MESON_TAC[setModel_V_bij]);;

(* the properties of V_mem_rep as properties of V_mem *)

let CSETAUX_V_mem_props = prove
 (`(?x:A+num. is_V x) /\
   (!a a':A V. a = a' <=> (!a''. V_mem a'' a <=> V_mem a'' a')) /\
   (!a:A V P'. ?a'. !a''. V_mem a'' a' <=> V_mem a'' a /\ P' (dest_V a'')) /\
   (!a:A V. ?a'. !a''. V_mem a'' a' <=> (!a'. V_mem a' a'' ==> V_mem a' a)) /\
   (!a:A V. ?a'. !a''. V_mem a'' a' <=> (?a'. V_mem a'' a' /\ V_mem a' a)) /\
   (!a a':A V. ?a''. !a'''. V_mem a''' a'' <=> a''' = a \/ a''' = a') /\
   (!a:A V. ?a'. !a''. V_mem a'' a ==> V_mem a' a)`,
  MP_TAC setModel_V_mem_rep_def THEN
  REWRITE_TAC[GSYM IMP_IMP; RIGHT_FORALL_IMP_THM; CSETAUX_FORALL_is_V;
              CSETAUX_EXISTS_is_V; GSYM setModel_V_mem_def; CSETAUX_dest_V_11] THEN
  REPEAT DISCH_TAC THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

(* HOL4 proves each part from V_mem_rep_def with metis and V_bij; the        *)
(* separation part takes P o mk_V for P.                                     *)

let is_set_theory_V = prove
 (`is_set_theory (V_mem:A V->A V->bool)`,
  STRIP_ASSUME_TAC CSETAUX_V_mem_props THEN
  REWRITE_TAC[is_set_theory_def; extensional_def; is_separation_def;
              is_power_def; is_union_def; is_upair_def; GSYM SKOLEM_THM] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`x:A V`; `P:A V->bool`] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:A V`; `\r:A+num. P (mk_V r):bool`]) THEN
  REWRITE_TAC[setModel_V_bij]);;

let setModel_V_choice_exists = prove
 (`?ch. is_choice (V_mem:A V->A V->bool) ch`,
  STRIP_ASSUME_TAC CSETAUX_V_mem_props THEN
  REWRITE_TAC[is_choice_def; GSYM SKOLEM_THM] THEN ASM_MESON_TAC[]);;

let setModel_V_choice_def =
  new_specification ["V_choice"] setModel_V_choice_exists;;

let setModel_V_indset_def = new_specification ["V_indset"]
  (prove(`?i:A V. (?x:A V. is_infinite V_mem x) ==> is_infinite V_mem i`,
         MESON_TAC[]));;

let is_model_V = prove
 (`(?i:A V. is_infinite V_mem i) ==>
   is_model (V_mem,V_indset:A V,V_choice)`,
  SIMP[is_model_def; is_set_theory_V; setModel_V_choice_def;
       setModel_V_indset_def]);;
