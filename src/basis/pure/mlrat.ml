(* ========================================================================= *)
(* mlrat: port of HOL4 basis/pure/mlratScript.sml (CakeML v3479).            *)
(* Pure functions for the Rat module.                                        *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - rat is hol4/rat.ml's (the rationals inside real; see its header), with  *)
(*   the overloaded & -- + - / < <= and the infix multiplication; HOL4's     *)
(*   intreal real_of_int is HOL Light's real_of_int, INT_FLOOR is            *)
(*   hol4/binary_ieee.ml's (HOL4 intreal).                                   *)
(* - Integers: HOL4 Num (ABS n) is num_of_int (abs n); gcd a b is            *)
(*   num_gcd(a,b); ~&n is --(&n); the strlit "/" is implode "/" and concat   *)
(*   is mlstring_concat; mlint$toString is mlint's toString, this theory's   *)
(*   toString is mlrat_toString (names.tsv).                                 *)
(* - Proofs: real_of_rat r is rep_rat r (BASRAUX_REAL_OF_RAT_REP), so the    *)
(*   facts about real_of_rat follow from the transfer lemmas of hol4/rat.ml, *)
(*   not from RATN_DIV_RATD and the rat field laws as in HOL4;               *)
(*   rat_of_int_eq is the uniqueness of the representation in lowest terms   *)
(*   (BASRAUX_RATND_UNIQUE of hol4/rat.ml); the real_to_str facts go through *)
(*   BASRAUX_REAL_TO_RATIONAL (real_to_rational of a fraction in lowest      *)
(*   terms) and BASRAUX_GCD_DIV (the lowest terms of n / d by dividing by    *)
(*   their gcd; HOL4 uses FACTOR_OUT_GCD of its gcd library).                *)
(* - The free variables of a HOL4 statement are universally quantified.      *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "basis/pure/mlstring.ml";;
needs "basis/pure/mlint.ml";;
needs "hol4/gcd.ml";;
needs "hol4/rat.ml";;
needs "hol4/binary_ieee.ml";;

type_invention_error := true;;

(* representation type *)

let rational_INDUCT,rational_RECURSION = cake_type "rational = RatPair int num";;

let rational_of_num_def = cake_def
  `rational_of_num (n:num) = RatPair (&n) 1`;;

let rational_of_int_def = cake_def
  `rational_of_int (n:int) = RatPair n 1`;;

(* connection between real and rat *)

let real_of_rat_def = cake_def
  `real_of_rat (r:rat) = real_of_int (RATN r) / &(RATD r)`;;

let BASRAUX_REAL_OF_RAT_REP = prove
 (`!r. real_of_rat r = rep_rat r`,
  GEN_TAC THEN REWRITE_TAC[real_of_rat_def] THEN
  MP_TAC(AP_TERM `rep_rat` (SPEC `r:rat` RATN_DIV_RATD)) THEN
  REWRITE_TAC[BASRAUX_REP_RAT_CLAUSES; BASRAUX_REP_RAT_OF_INT]);;

let real_of_rat_int = prove
 (`!x. real_of_rat (&x) = &x`,
  REWRITE_TAC[BASRAUX_REAL_OF_RAT_REP; BASRAUX_REP_RAT_CLAUSES]);;

let real_of_rat_le = prove
 (`!r1 r2. real_of_rat r1 <= real_of_rat r2 <=> r1 <= r2`,
  REWRITE_TAC[BASRAUX_REAL_OF_RAT_REP; BASRAUX_RAT_ORDER]);;

let real_of_rat_eq = prove
 (`!r1 r2. real_of_rat r1 = real_of_rat r2 <=> r1 = r2`,
  REWRITE_TAC[BASRAUX_REAL_OF_RAT_REP; BASRAUX_REP_RAT_11]);;

let _ = cake_add_simps [real_of_rat_le; real_of_rat_eq];;

let real_of_rat_lt = prove
 (`!r1 r2. real_of_rat r1 < real_of_rat r2 <=> r1 < r2`,
  REWRITE_TAC[BASRAUX_REAL_OF_RAT_REP; BASRAUX_RAT_ORDER]);;

let real_of_rat_add = prove
 (`!r1 r2. real_of_rat (r1 + r2) = real_of_rat r1 + real_of_rat r2`,
  REWRITE_TAC[BASRAUX_REAL_OF_RAT_REP; BASRAUX_REP_RAT_CLAUSES]);;

let real_of_rat_mul = prove
 (`!r1 r2. real_of_rat (r1 * r2) = real_of_rat r1 * real_of_rat r2`,
  REWRITE_TAC[BASRAUX_REAL_OF_RAT_REP; BASRAUX_REP_RAT_CLAUSES]);;

let real_of_rat_ainv = prove
 (`!r. real_of_rat (--r) = --(real_of_rat r)`,
  REWRITE_TAC[BASRAUX_REAL_OF_RAT_REP; BASRAUX_REP_RAT_CLAUSES]);;

let real_of_rat_sub = prove
 (`!r1 r2. real_of_rat (r1 - r2) = real_of_rat r1 - real_of_rat r2`,
  REWRITE_TAC[BASRAUX_REAL_OF_RAT_REP; BASRAUX_REP_RAT_CLAUSES]);;

(* HOL4: inv_div [local] *)

let inv_div = prove
 (`!x y. ~(x = &0) /\ ~(y = &0) ==> inv (x / y) = y / x`,
  SIMP_TAC[REAL_INV_DIV]);;

let real_of_int_eq_num = prove
 (`!i n. ((real_of_int i = &n) <=> (i = &n)) /\
         ((&n = real_of_int i) <=> (i = &n))`,
  REWRITE_TAC[int_eq; int_of_num_th] THEN REAL_ARITH_TAC);;

let rat_of_int_eq_num = prove
 (`!i n. ((rat_of_int i = &n) <=> (i = &n)) /\
         ((&n = rat_of_int i) <=> (i = &n))`,
  BASRAUX_RAT_TRANSFER_TAC THEN REAL_ARITH_TAC);;

let _ = cake_add_simps [real_of_int_eq_num; rat_of_int_eq_num];;

let real_of_rat_inv = prove
 (`!r. ~(r = &0) ==> real_of_rat (rat_minv r) = inv (real_of_rat r)`,
  REWRITE_TAC[BASRAUX_REAL_OF_RAT_REP; BASRAUX_REP_RAT_CLAUSES]);;

let real_of_rat_div = prove
 (`!x x'. ~(x = &0) ==> real_of_rat (x' / x) = real_of_rat x' / real_of_rat x`,
  REWRITE_TAC[BASRAUX_REAL_OF_RAT_REP; BASRAUX_REP_RAT_CLAUSES]);;

let real_of_int_of_rat = prove
 (`!i. real_of_int i = real_of_rat (rat_of_int i)`,
  REWRITE_TAC[BASRAUX_REAL_OF_RAT_REP; BASRAUX_REP_RAT_OF_INT]);;

let rat_of_int_eq = prove
 (`!n1 d1 n2 d2.
     num_gcd(num_of_int (abs n1),d1) = 1 /\ ~(d1 = 0) /\
     num_gcd(num_of_int (abs n2),d2) = 1 /\ ~(d2 = 0) /\
     rat_of_int n1 / &d1 = rat_of_int n2 / &d2
     ==> n1 = n2 /\ d1 = d2`,
  REWRITE_TAC[BASRAUX_NUM_GCD_ABS; GSYM LT_NZ] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`n1:int`; `d1:num`] BASRAUX_RATND_UNIQUE) THEN
  MP_TAC(SPECL [`n2:int`; `d2:num`] BASRAUX_RATND_UNIQUE) THEN
  ASM_MESON_TAC[]);;

let mlrat_toString_def = cake_def
  `mlrat_toString (RatPair i n) =
     if n = 1 then toString i
     else mlstring_concat [toString i; implode "/"; toString (&n)]`;;

(* HOL4: real_to_rational_def [nocompute] *)

let real_to_rational_def = cake_def
  `real_to_rational (r:real) =
     let (n,d) = (@x. ?n d. x = (n,d) /\
                            r = real_of_int n / &d /\
                            num_gcd(num_of_int (abs n),d) = 1 /\
                            ~(d = 0)) in
       RatPair n d`;;

let real_to_str_def = cake_def
  `real_to_str r = mlrat_toString (real_to_rational r)`;;

let real_of_int_div_eq = prove
 (`!n d n' d'.
     num_gcd(num_of_int (abs n'),d') = 1 /\ ~(d' = 0) /\
     num_gcd(num_of_int (abs n),d) = 1 /\ ~(d = 0)
     ==> (real_of_int n / &d = real_of_int n' / &d' <=> n = n' /\ d = d')`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN MATCH_MP_TAC rat_of_int_eq THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[BASRAUX_RAT_EQ; BASRAUX_REP_RAT_CLAUSES;
                    BASRAUX_REP_RAT_OF_INT];
    STRIP_TAC THEN ASM_REWRITE_TAC[]]);;

(* real_to_rational of a fraction in lowest terms, and the lowest terms of   *)
(* &n / &d (HOL4's proofs use FACTOR_OUT_GCD of the gcd library)            *)

let BASRAUX_REAL_TO_RATIONAL = prove
 (`!n d. num_gcd(num_of_int (abs n),d) = 1 /\ ~(d = 0)
         ==> real_to_rational (real_of_int n / &d) = RatPair n d`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_to_rational_def] THEN
  HOL4_SELECT_ELIM_TAC THEN CONJ_TAC THENL
   [ASM_MESON_TAC[];
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:int#num`; `a:int`; `b:num`] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[pair_CASE; injectivity "rational"] THEN
    ASM_MESON_TAC[real_of_int_div_eq]]);;

let BASRAUX_GCD_DIV = prove
 (`!n d. ~(d = 0)
         ==> ~(num_gcd(n,d) = 0) /\
             n DIV num_gcd(n,d) * num_gcd(n,d) = n /\
             d DIV num_gcd(n,d) * num_gcd(n,d) = d /\
             ~(d DIV num_gcd(n,d) = 0) /\
             num_gcd(n DIV num_gcd(n,d),d DIV num_gcd(n,d)) = 1`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN ABBREV_TAC `k = num_gcd(n,d)` THEN
  SUBGOAL_THEN `~(k = 0) /\ k divides n /\ k divides d` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "k" THEN UNDISCH_TAC `~(d = 0)` THEN CONV_TAC NUMBER_RULE;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DIVIDES_DIV_MULT]) THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `d DIV k * k = d` THEN
    ASM_REWRITE_TAC[MULT_CLAUSES] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[NUMBER_RULE `!a b. num_gcd(a,b) = 1 <=> coprime(a,b)`] THEN
  MP_TAC(SPECL [`n:num`; `d:num`; `n DIV k`; `d DIV k`] (NUMBER_RULE
    `!n d p q. ~(num_gcd(n,d) = 0) /\ n = p * num_gcd(n,d) /\
               d = q * num_gcd(n,d) ==> coprime(p,q)`)) THEN
  ASM_REWRITE_TAC[]);;

let real_to_str_num = prove
 (`!n. real_to_str (&n) = mlrat_toString (RatPair (&n) 1)`,
  GEN_TAC THEN REWRITE_TAC[real_to_str_def] THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `(&n:real) = real_of_int (&n) / &1` SUBST1_TAC THENL
   [REWRITE_TAC[int_of_num_th; REAL_DIV_1];
    MATCH_MP_TAC BASRAUX_REAL_TO_RATIONAL THEN
    REWRITE_TAC[ARITH; NUMBER_RULE `!a. num_gcd(a,1) = 1`]]);;

let real_to_str_neg_num = prove
 (`!n. real_to_str (--(&n)) = mlrat_toString (RatPair (--(&n)) 1)`,
  GEN_TAC THEN REWRITE_TAC[real_to_str_def] THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `--(&n:real) = real_of_int (--(&n)) / &1` SUBST1_TAC THENL
   [REWRITE_TAC[int_neg_th; int_of_num_th; REAL_DIV_1];
    MATCH_MP_TAC BASRAUX_REAL_TO_RATIONAL THEN
    REWRITE_TAC[ARITH; NUMBER_RULE `!a. num_gcd(a,1) = 1`]]);;

let real_to_str_rat = prove
 (`!n d. real_to_str (&n / &d) =
         mlrat_toString (if d = 0 then real_to_rational (&n / &d)
                         else let k = num_gcd(n,d) in
                              RatPair (&(n DIV k)) (d DIV k))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_to_str_def] THEN AP_TERM_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  MP_TAC(MP (SPECL [`n:num`; `d:num`] BASRAUX_GCD_DIV) (ASSUME `~(d = 0)`)) THEN
  ABBREV_TAC `k = num_gcd(n,d)` THEN ABBREV_TAC `p = n DIV k` THEN
  ABBREV_TAC `q = d DIV k` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(&n:real) / &d = real_of_int (&p) / &q` SUBST1_TAC THENL
   [UNDISCH_TAC `p * k = n` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `q * k = d` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL; int_of_num_th] THEN
    SUBGOAL_THEN `~(&k:real = &0) /\ ~(&q:real = &0)` MP_TAC THENL
     [ASM_REWRITE_TAC[REAL_OF_NUM_EQ]; CONV_TAC REAL_FIELD];
    MATCH_MP_TAC BASRAUX_REAL_TO_RATIONAL THEN
    ASM_REWRITE_TAC[INT_ABS_NUM; NUM_OF_INT_OF_NUM]]);;

let real_to_str_neg_rat = prove
 (`!n d. real_to_str ((--(&n)) / &d) =
         mlrat_toString (if d = 0 then real_to_rational ((--(&n)) / &d)
                         else let k = num_gcd(n,d) in
                              RatPair (--(&(n DIV k))) (d DIV k))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_to_str_def] THEN AP_TERM_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  MP_TAC(MP (SPECL [`n:num`; `d:num`] BASRAUX_GCD_DIV) (ASSUME `~(d = 0)`)) THEN
  ABBREV_TAC `k = num_gcd(n,d)` THEN ABBREV_TAC `p = n DIV k` THEN
  ABBREV_TAC `q = d DIV k` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(--(&n:real)) / &d = real_of_int (--(&p)) / &q` SUBST1_TAC THENL
   [UNDISCH_TAC `p * k = n` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `q * k = d` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL; int_neg_th; int_of_num_th] THEN
    SUBGOAL_THEN `~(&k:real = &0) /\ ~(&q:real = &0)` MP_TAC THENL
     [ASM_REWRITE_TAC[REAL_OF_NUM_EQ]; CONV_TAC REAL_FIELD];
    MATCH_MP_TAC BASRAUX_REAL_TO_RATIONAL THEN
    ASM_REWRITE_TAC[INT_ABS_NEG; INT_ABS_NUM; NUM_OF_INT_OF_NUM]]);;

let INT_FLOOR_real_of_int = prove
 (`!i. INT_FLOOR (real_of_int i) = i`,
  REWRITE_TAC[INT_FLOOR; int_add_th; int_of_num_th] THEN REAL_ARITH_TAC);;
