(* ========================================================================= *)
(* rat: the rational numbers of HOL4 src/rational/ratScript.sml (a HOL4      *)
(* library theory of CakeML v3479), the part that basis/pure/mlratScript.sml *)
(* and basis/RatProgScript.sml use, with HOL4's names and statements.        *)
(*                                                                           *)
(* Construction (differs from HOL4's; decision D6 of 2026-11-23).  HOL4      *)
(* builds rat as a quotient of fracTheory's fractions (pairs of an integer   *)
(* and a positive integer, identified by cross-multiplication), on frac,     *)
(* intExtension and primeFactor (about 5.8K lines).  Here rat is the subtype *)
(* of HOL Light's real of the rational numbers (rational, Library/floor.ml): *)
(* the bijections are abs_rat : real -> rat and rep_rat : rat -> real        *)
(* (HOL4's names, there over frac), rat_type_thm is the bijection theorem,   *)
(* and each operation is the real one carried over: rat_of_num n =           *)
(* abs_rat (&n), rat_ainv r1 = abs_rat (--rep_rat r1), rat_minv r1 =         *)
(* abs_rat (inv (rep_rat r1)), rat_add r1 r2 = abs_rat (rep_rat r1 +         *)
(* rep_rat r2) (so also rat_sub, rat_mul, rat_div), rat_les r1 r2 <=>        *)
(* rep_rat r1 < rep_rat r2.  rat_gre, rat_leq, rat_geq, rat_of_int, rat_min  *)
(* and rat_max have HOL4's definitions, and RATN and RATD HOL4's             *)
(* specification RATND_THM (the numerator of least absolute value, a         *)
(* positive denominator, 1 for 0), by new_specification as in HOL4.          *)
(*                                                                           *)
(* Why the theorems are HOL4's.  Both types are the field of the rational    *)
(* numbers with its only order; here rep_rat embeds it in real as an         *)
(* injective homomorphism of ordered fields (BASRAUX_REP_RAT_CLAUSES,        *)
(* BASRAUX_RAT_EQ, BASRAUX_RAT_ORDER, BASRAUX_REP_RAT_OF_INT).  A statement  *)
(* over rat built from the operations, the numerals and rat_of_int holds     *)
(* exactly when its image under rep_rat holds in real, and that is how the   *)
(* theorems below are proved (BASRAUX_RAT_TRANSFER_TAC, then real            *)
(* arithmetic); RATN and RATD are characterised by the same statement as in  *)
(* HOL4, from which they are unique (BASRAUX_RATND_UNIQUE).  The one value   *)
(* that the constructions may give differently is the inverse of 0: HOL4's   *)
(* rat_minv 0 is abs_rat of frac_minv of the zero fraction, a pair with      *)
(* denominator 0, on which frac's abstraction function is unconstrained, so  *)
(* HOL4 proves nothing about it; here rat_minv 0 = 0 and r / 0 = 0 (HOL      *)
(* Light's inv 0 = 0).  The statements keep HOL4's nonzero hypotheses.       *)
(*                                                                           *)
(* Notation: on rat the overloaded symbols & -- + - / < <= > >= and the      *)
(* infix multiplication are rat_of_num, rat_ainv, rat_add, rat_sub, rat_div, *)
(* rat_les, rat_leq, rat_gre, rat_geq and rat_mul (HOL4's 0q is &0:rat, its  *)
(* ~r and -r are --r; HOL4's Num on a non-negative integer is num_of_int,    *)
(* ABS is abs, gcd a b is num_gcd(a,b)).                                     *)
(* At the end of the file the rat entries of the interface are put after the *)
(* others, so that an unannotated numeral or operator in a later file is     *)
(* read as before this file.  The free variables of a HOL4 statement are     *)
(* universally quantified.                                                   *)
(*                                                                           *)
(* Besides the 40 facts the two scripts name, the file has HOL4's [simp]     *)
(* theorems over these operations (registered with cake_add_simps, as HOL4's *)
(* srw_ss has them), except those about rat_sgn, frac and powers, gcd_RATND  *)
(* (a RatProg name here) and rat_of_int_EQN (mlrat's rat_of_int_eq_num has   *)
(* its statement).  Helpers that are not HOL4 theorems are BASRAUX_: the     *)
(* transfer lemmas and tactic, BASRAUX_RATND_COPRIME (lowest terms),         *)
(* BASRAUX_RATND_UNIQUE (RatProg's gcd_RATND in integer form) and            *)
(* BASRAUX_NUM_GCD_ABS.                                                      *)
(* ========================================================================= *)

needs "hol4/vocab.ml";;

(* The overloading of the arithmetic symbols as it was before this file, so  *)
(* that it can be restored at the end with the rat entries appended          *)
(* (overload_interface puts a new entry first, which would make an          *)
(* unannotated numeral of a later file a rat).                               *)

let basraux_interface_before = !the_interface;;

(* HOL Light's rational reals: rational and RATIONAL_CLOSED, Library/floor.ml *)
(* (a HOL Light library file written for type_invention_error := false).    *)

type_invention_error := false;;
needs "Library/floor.ml";;
type_invention_error := true;;

prioritize_real();;

(* ------------------------------------------------------------------------- *)
(* The type.  HOL4: rat_type_thm (the quotient theorem of rat over frac).    *)
(* ------------------------------------------------------------------------- *)

let rat_type_thm = new_type_definition "rat" ("abs_rat","rep_rat")
  (prove(`?x:real. rational x`, MESON_TAC[RATIONAL_NUM]));;

let BASRAUX_RATIONAL_REP_RAT = prove
 (`!r:rat. rational (rep_rat r)`,
  MESON_TAC[rat_type_thm]);;

let BASRAUX_REP_ABS_RAT = prove
 (`!x:real. rational x ==> rep_rat (abs_rat x) = x`,
  MESON_TAC[rat_type_thm]);;

let BASRAUX_REP_RAT_11 = prove
 (`!r s:rat. rep_rat r = rep_rat s <=> r = s`,
  MESON_TAC[rat_type_thm]);;

(* ------------------------------------------------------------------------- *)
(* The operations: the real ones carried over (HOL4: over frac).            *)
(* ------------------------------------------------------------------------- *)

let rat_of_num_def = new_definition
  `rat_of_num n = abs_rat (&n)`;;

let rat_ainv_def = new_definition
  `rat_ainv r1 = abs_rat (--(rep_rat r1))`;;

let rat_minv_def = new_definition
  `rat_minv r1 = abs_rat (inv (rep_rat r1))`;;

let rat_add_def = new_definition
  `rat_add r1 r2 = abs_rat (rep_rat r1 + rep_rat r2)`;;

let rat_sub_def = new_definition
  `rat_sub r1 r2 = abs_rat (rep_rat r1 - rep_rat r2)`;;

let rat_mul_def = new_definition
  `rat_mul r1 r2 = abs_rat (rep_rat r1 * rep_rat r2)`;;

let rat_div_def = new_definition
  `rat_div r1 r2 = abs_rat (rep_rat r1 / rep_rat r2)`;;

let rat_les_def = new_definition
  `rat_les r1 r2 <=> rep_rat r1 < rep_rat r2`;;

let rat_gre_def = new_definition
  `rat_gre r1 r2 <=> rat_les r2 r1`;;

let rat_leq_def = new_definition
  `rat_leq r1 r2 <=> rat_les r1 r2 \/ r1 = r2`;;

let rat_geq_def = new_definition
  `rat_geq r1 r2 <=> rat_leq r2 r1`;;

overload_interface ("&", `rat_of_num:num->rat`);;
overload_interface ("--", `rat_ainv:rat->rat`);;
overload_interface ("+", `rat_add:rat->rat->rat`);;
overload_interface ("-", `rat_sub:rat->rat->rat`);;
overload_interface ("*", `rat_mul:rat->rat->rat`);;
overload_interface ("/", `rat_div:rat->rat->rat`);;
overload_interface ("<", `rat_les:rat->rat->bool`);;
overload_interface ("<=", `rat_leq:rat->rat->bool`);;
overload_interface (">", `rat_gre:rat->rat->bool`);;
overload_interface (">=", `rat_geq:rat->rat->bool`);;

(* within this file an unannotated arithmetic term is real *)

prioritize_real();;

(* HOL4: rat_of_num_ind (the induction of its definition by three clauses) *)

let rat_of_num_ind = prove
 (`!P. P 0 /\ P (SUC 0) /\ (!n. P (SUC n) ==> P (SUC (SUC n))) ==> !v. P v`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!v. P v /\ P (SUC v)` (fun th -> MESON_TAC[th]) THEN
  INDUCT_TAC THEN ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Transfer to real: rep_rat is an injective ordered-field homomorphism.     *)
(* ------------------------------------------------------------------------- *)

let BASRAUX_REP_RAT_CLAUSES = prove
 (`(!n. rep_rat (&n) = &n) /\
   (!r:rat. rep_rat (--r) = --(rep_rat r)) /\
   (!r:rat. rep_rat (rat_minv r) = inv (rep_rat r)) /\
   (!r s:rat. rep_rat (r + s) = rep_rat r + rep_rat s) /\
   (!r s:rat. rep_rat (r - s) = rep_rat r - rep_rat s) /\
   (!r s:rat. rep_rat (r * s) = rep_rat r * rep_rat s) /\
   (!r s:rat. rep_rat (r / s) = rep_rat r / rep_rat s)`,
  REWRITE_TAC[rat_of_num_def; rat_ainv_def; rat_minv_def; rat_add_def;
              rat_sub_def; rat_mul_def; rat_div_def] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC BASRAUX_REP_ABS_RAT THEN
  SIMP_TAC[RATIONAL_CLOSED; BASRAUX_RATIONAL_REP_RAT]);;

let BASRAUX_RAT_EQ = prove
 (`!r s:rat. r = s <=> rep_rat r = rep_rat s`,
  REWRITE_TAC[BASRAUX_REP_RAT_11]);;

let BASRAUX_RAT_ORDER = prove
 (`(!r s:rat. r < s <=> rep_rat r < rep_rat s) /\
   (!r s:rat. r <= s <=> rep_rat r <= rep_rat s) /\
   (!r s:rat. r > s <=> rep_rat r > rep_rat s) /\
   (!r s:rat. r >= s <=> rep_rat r >= rep_rat s)`,
  REWRITE_TAC[rat_les_def; rat_leq_def; rat_gre_def; rat_geq_def;
              BASRAUX_RAT_EQ; real_gt; real_ge] THEN
  REAL_ARITH_TAC);;

(* HOL4: rat_of_int_def (Num i is num_of_int i here: both are used on        *)
(* non-negative integers only)                                               *)

let rat_of_int_def = new_definition
  `rat_of_int (i:int) =
     if i < &0 then --(&(num_of_int (--i))) else (&(num_of_int i):rat)`;;

let BASRAUX_REP_RAT_OF_INT = prove
 (`!i. rep_rat (rat_of_int i) = real_of_int i`,
  GEN_TAC THEN REWRITE_TAC[rat_of_int_def] THEN COND_CASES_TAC THEN
  REWRITE_TAC[BASRAUX_REP_RAT_CLAUSES; GSYM int_of_num_th] THENL
   [SUBGOAL_THEN `&(num_of_int (--i)) = --i` SUBST1_TAC THENL
     [MATCH_MP_TAC INT_OF_NUM_OF_INT THEN ASM_INT_ARITH_TAC;
      REWRITE_TAC[int_neg_th; REAL_NEG_NEG]];
    SUBGOAL_THEN `&(num_of_int i) = i` SUBST1_TAC THENL
     [MATCH_MP_TAC INT_OF_NUM_OF_INT THEN ASM_INT_ARITH_TAC;
      REFL_TAC]]);;

(* The transfer: rat equations and inequalities become real ones over       *)
(* rep_rat; rat_of_int i becomes real_of_int i and the integer operations   *)
(* real ones too (the list, for REWRITE_RULE on assumptions, and the tactic  *)
(* on the goal).                                                             *)

let basraux_rat_transfer_thms =
  [BASRAUX_RAT_EQ; BASRAUX_RAT_ORDER; BASRAUX_REP_RAT_CLAUSES;
   BASRAUX_REP_RAT_OF_INT; int_eq; int_le; int_lt; int_ge; int_gt;
   int_of_num_th; int_neg_th; int_add_th; int_sub_th; int_mul_th];;

let BASRAUX_RAT_TRANSFER_TAC = REWRITE_TAC basraux_rat_transfer_thms;;

let rat_min_def = new_definition
  `rat_min (r1:rat) r2 = if r1 < r2 then r1 else r2`;;

let rat_max_def = new_definition
  `rat_max (r1:rat) r2 = if r1 > r2 then r1 else r2`;;

(* ------------------------------------------------------------------------- *)
(* The field laws that the two scripts use (HOL4 statements).                *)
(* ------------------------------------------------------------------------- *)

let RAT_MUL_ASSOC = prove
 (`!a b c:rat. a * (b * c) = (a * b) * c`,
  BASRAUX_RAT_TRANSFER_TAC THEN REAL_ARITH_TAC);;

let RAT_MUL_COMM = prove
 (`!a b:rat. a * b = b * a`,
  BASRAUX_RAT_TRANSFER_TAC THEN REAL_ARITH_TAC);;

let RAT_MUL_RID = prove
 (`!a:rat. a * &1 = a`,
  BASRAUX_RAT_TRANSFER_TAC THEN REAL_ARITH_TAC);;

let RAT_MUL_LINV = prove
 (`!a:rat. ~(a = &0) ==> rat_minv a * a = &1`,
  BASRAUX_RAT_TRANSFER_TAC THEN CONV_TAC REAL_FIELD);;

let RAT_SUB_ADDAINV = prove
 (`!r1 r2:rat. r1 - r2 = r1 + --r2`,
  BASRAUX_RAT_TRANSFER_TAC THEN REAL_ARITH_TAC);;

let RAT_DIV_MULMINV = prove
 (`!r1 r2:rat. r1 / r2 = r1 * rat_minv r2`,
  BASRAUX_RAT_TRANSFER_TAC THEN REWRITE_TAC[real_div]);;

let RAT_AINV_RMUL = prove
 (`!r1 r2:rat. --(r1 * r2) = r1 * --r2`,
  BASRAUX_RAT_TRANSFER_TAC THEN REAL_ARITH_TAC);;

let RAT_AINV_LMUL = prove
 (`!r1 r2:rat. --(r1 * r2) = --r1 * r2`,
  BASRAUX_RAT_TRANSFER_TAC THEN REAL_ARITH_TAC);;

let RAT_AINV_MINV = prove
 (`!r1:rat. ~(r1 = &0) ==> --(rat_minv r1) = rat_minv (--r1)`,
  BASRAUX_RAT_TRANSFER_TAC THEN REWRITE_TAC[REAL_INV_NEG]);;

let RAT_LES_REF = prove
 (`!r1:rat. ~(r1 < r1)`,
  BASRAUX_RAT_TRANSFER_TAC THEN REAL_ARITH_TAC);;

let RAT_LES_ANTISYM = prove
 (`!r1 r2:rat. r1 < r2 ==> ~(r2 < r1)`,
  BASRAUX_RAT_TRANSFER_TAC THEN REAL_ARITH_TAC);;

let RAT_LES_TOTAL = prove
 (`!r1 r2:rat. r1 < r2 \/ r1 = r2 \/ r2 < r1`,
  BASRAUX_RAT_TRANSFER_TAC THEN REAL_ARITH_TAC);;

let RAT_LDIV_EQ = prove
 (`!r1 r2 r3:rat. ~(r2 = &0) ==> (r1 / r2 = r3 <=> r1 = r2 * r3)`,
  BASRAUX_RAT_TRANSFER_TAC THEN CONV_TAC REAL_FIELD);;

let RAT_RDIV_EQ = prove
 (`!r1 r2 r3:rat. ~(r3 = &0) ==> (r1 = r2 / r3 <=> r1 * r3 = r2)`,
  BASRAUX_RAT_TRANSFER_TAC THEN CONV_TAC REAL_FIELD);;

let RAT_EQ_RMUL = prove
 (`!r1 r2 r3:rat. ~(r3 = &0) ==> (r1 * r3 = r2 * r3 <=> r1 = r2)`,
  BASRAUX_RAT_TRANSFER_TAC THEN CONV_TAC REAL_FIELD);;

let RAT_LDIV_LES_POS = prove
 (`!r1 r2 r3:rat. &0 < r2 ==> (r1 / r2 < r3 <=> r1 < r2 * r3)`,
  BASRAUX_RAT_TRANSFER_TAC THEN SIMP_TAC[REAL_LT_LDIV_EQ; REAL_MUL_SYM]);;

let RAT_RDIV_LES_POS = prove
 (`!r1 r2 r3:rat. &0 < r3 ==> (r1 < r2 / r3 <=> r1 * r3 < r2)`,
  BASRAUX_RAT_TRANSFER_TAC THEN SIMP_TAC[REAL_LT_RDIV_EQ]);;

let RAT_LDIV_LEQ_POS = prove
 (`!r1 r2 r3:rat. &0 < r2 ==> (r1 / r2 <= r3 <=> r1 <= r2 * r3)`,
  BASRAUX_RAT_TRANSFER_TAC THEN SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_SYM]);;

let RAT_RDIV_LEQ_POS = prove
 (`!r1 r2 r3:rat. &0 < r3 ==> (r1 <= r2 / r3 <=> r1 * r3 <= r2)`,
  BASRAUX_RAT_TRANSFER_TAC THEN SIMP_TAC[REAL_LE_RDIV_EQ]);;

let RAT_NO_ZERODIV = prove
 (`!r1 r2:rat. r1 = &0 \/ r2 = &0 <=> r1 * r2 = &0`,
  BASRAUX_RAT_TRANSFER_TAC THEN REWRITE_TAC[REAL_ENTIRE]);;

let RDIV_MUL_OUT = prove
 (`!r1 r2 r3:rat. r1 * (r2 / r3) = (r1 * r2) / r3`,
  BASRAUX_RAT_TRANSFER_TAC THEN REWRITE_TAC[real_div; REAL_MUL_ASSOC]);;

let LDIV_MUL_OUT = prove
 (`!r1 r2 r3:rat. (r1 / r2) * r3 = (r1 * r3) / r2`,
  BASRAUX_RAT_TRANSFER_TAC THEN REWRITE_TAC[real_div] THEN REAL_ARITH_TAC);;

let RAT_DIVDIV_MUL = prove
 (`!a b c d:rat. ~(b = &0) /\ ~(d = &0) ==> (a / b) * (c / d) = (a * c) / (b * d)`,
  BASRAUX_RAT_TRANSFER_TAC THEN CONV_TAC REAL_FIELD);;

let RAT_DIVDIV_ADD = prove
 (`!x y a b:rat. ~(y = &0) /\ ~(b = &0)
                 ==> x / y + a / b = (x * b + a * y) / (y * b)`,
  BASRAUX_RAT_TRANSFER_TAC THEN CONV_TAC REAL_FIELD);;

let RAT_DIV_AINV = prove
 (`!x y:rat. --(x / y) = (--x) / y`,
  BASRAUX_RAT_TRANSFER_TAC THEN REWRITE_TAC[real_div] THEN REAL_ARITH_TAC);;

let RAT_MINV_EQ_0 = prove
 (`!r:rat. ~(r = &0) ==> ~(rat_minv r = &0)`,
  BASRAUX_RAT_TRANSFER_TAC THEN REWRITE_TAC[REAL_INV_EQ_0]);;

let RAT_DIV_MINV = prove
 (`!x y:rat. ~(x = &0) /\ ~(y = &0) ==> rat_minv (x / y) = y / x`,
  BASRAUX_RAT_TRANSFER_TAC THEN CONV_TAC REAL_FIELD);;

let RAT_DIV_EQ0 = prove
 (`!d n:rat. ~(d = &0)
             ==> ((n / d = &0) <=> (n = &0)) /\ ((&0 = n / d) <=> (n = &0))`,
  BASRAUX_RAT_TRANSFER_TAC THEN CONV_TAC REAL_FIELD);;

(* ------------------------------------------------------------------------- *)
(* Numerals and rat_of_int (HOL4 statements).                                *)
(* ------------------------------------------------------------------------- *)

let RAT_MUL_NUM_CALCULATE = prove
 (`(!n m. (&n:rat) * &m = &(n * m)) /\
   (!n m. --(&n:rat) * &m = --(&(n * m))) /\
   (!n m. (&n:rat) * --(&m) = --(&(n * m))) /\
   (!n m. --(&n:rat) * --(&m) = &(n * m))`,
  BASRAUX_RAT_TRANSFER_TAC THEN REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
  REAL_ARITH_TAC);;

let RAT_EQ_NUM_CALCULATE = prove
 (`(!n m. (&n:rat) = &m <=> n = m) /\
   (!n m. (&n:rat) = --(&m) <=> n = 0 /\ m = 0) /\
   (!n m. --(&n:rat) = &m <=> n = 0 /\ m = 0) /\
   (!n m. --(&n:rat) = --(&m) <=> n = m)`,
  BASRAUX_RAT_TRANSFER_TAC THEN REWRITE_TAC[REAL_EQ_NEG2; REAL_OF_NUM_EQ] THEN
  REWRITE_TAC[REAL_ARITH `(&n:real) = --(&m) <=> &n + &m = &0`;
              REAL_ARITH `--(&n:real) = &m <=> &n + &m = &0`] THEN
  REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_EQ; ADD_EQ_0]);;

let rat_of_int_11 = prove
 (`!i1 i2. rat_of_int i1 = rat_of_int i2 <=> i1 = i2`,
  BASRAUX_RAT_TRANSFER_TAC);;

let rat_of_int_of_num = prove
 (`!x. rat_of_int (&x) = &x`,
  BASRAUX_RAT_TRANSFER_TAC);;

let rat_of_int_MUL = prove
 (`!x y. rat_of_int x * rat_of_int y = rat_of_int (x * y)`,
  BASRAUX_RAT_TRANSFER_TAC);;

let rat_of_int_ADD = prove
 (`!x y. rat_of_int x + rat_of_int y = rat_of_int (x + y)`,
  BASRAUX_RAT_TRANSFER_TAC);;

let rat_of_int_LE = prove
 (`!i j. rat_of_int i <= rat_of_int j <=> i <= j`,
  BASRAUX_RAT_TRANSFER_TAC);;

let rat_of_int_LT = prove
 (`!i j. rat_of_int i < rat_of_int j <=> i < j`,
  BASRAUX_RAT_TRANSFER_TAC);;

let rat_of_int_ainv = prove
 (`!i. rat_of_int (--i) = --(rat_of_int i)`,
  BASRAUX_RAT_TRANSFER_TAC);;

(* ------------------------------------------------------------------------- *)
(* RATN and RATD.  HOL4 specifies them by RATND_THM (new_specification): the *)
(* numerator of least absolute value with a positive denominator, the        *)
(* denominator 1 for 0.  Here: the same statement, proved from the           *)
(* representations rep_rat r = real_of_int n / &d of a rational real.        *)
(* ------------------------------------------------------------------------- *)

let BASRAUX_RAT_REPRESENTED = prove
 (`!r:rat. ?n d. r = rat_of_int n / &d /\ 0 < d`,
  GEN_TAC THEN MP_TAC(SPEC `r:rat` BASRAUX_RATIONAL_REP_RAT) THEN
  REWRITE_TAC[RATIONAL_ALT; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`p:num`; `q:num`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `rep_rat r = &p / &q \/ rep_rat r = --(&p) / &q`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[real_div; REAL_MUL_LNEG] THEN REWRITE_TAC[GSYM real_div] THEN
    ASM_REAL_ARITH_TAC;
    MAP_EVERY EXISTS_TAC [`&p:int`; `q:num`];
    MAP_EVERY EXISTS_TAC [`--(&p):int`; `q:num`]] THEN
  ASM_REWRITE_TAC[LT_NZ] THEN BASRAUX_RAT_TRANSFER_TAC THEN ASM_REWRITE_TAC[]);;

let BASRAUX_RAT_NUMDENOM_EXISTS = prove
 (`!r:rat. ?n d. r = rat_of_int n / &d /\ 0 < d /\ (n = &0 ==> d = 1) /\
                 (!n' d'. r = rat_of_int n' / &d' /\ 0 < d' ==> abs n <= abs n')`,
  GEN_TAC THEN ASM_CASES_TAC `r:rat = &0` THENL
   [MAP_EVERY EXISTS_TAC [`&0:int`; `1`] THEN
    ASM_REWRITE_TAC[ARITH; INT_ABS_NUM; INT_ABS_POS] THEN
    BASRAUX_RAT_TRANSFER_TAC THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MP_TAC(fst(EQ_IMP_RULE(BETA_RULE(ISPEC
    `\k. ?n d. r = rat_of_int n / &d /\ 0 < d /\ num_of_int (abs n) = k`
    num_WOP)))) THEN
  ANTS_TAC THENL
   [MP_TAC(SPEC `r:rat` BASRAUX_RAT_REPRESENTED) THEN MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `n:int` (X_CHOOSE_THEN `d:num` STRIP_ASSUME_TAC)) MP_TAC)) THEN
  UNDISCH_TAC `num_of_int (abs n) = k` THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC [`n:int`; `d:num`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `~(r:rat = &0)` THEN
    ASM_REWRITE_TAC[] THEN BASRAUX_RAT_TRANSFER_TAC THEN CONV_TAC REAL_FIELD;
    MAP_EVERY X_GEN_TAC [`n':int`; `d':num`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `num_of_int (abs n')`) THEN
    MATCH_MP_TAC(TAUT `b /\ (~a ==> c) ==> (a ==> ~b) ==> c`) THEN
    CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [`n':int`; `d':num`] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[NOT_LT] THEN ONCE_REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN
      SIMP_TAC[INT_OF_NUM_OF_INT; INT_ABS_POS]]]);;

let RATND_THM = new_specification ["RATN"; "RATD"]
  (REWRITE_RULE[SKOLEM_THM] BASRAUX_RAT_NUMDENOM_EXISTS);;

(* HOL4: RATN_DIV_RATD [simp], RATD_NZERO [simp] *)

let RATN_DIV_RATD = prove
 (`!r. rat_of_int (RATN r) / &(RATD r) = r`,
  MESON_TAC[RATND_THM]);;

let RATD_NZERO = prove
 (`!r. 0 < RATD r /\ ~(RATD r = 0)`,
  MESON_TAC[RATND_THM; LT_NZ]);;

(* lowest terms (HOL4 ratTheory's gcd_RATND, gcd (Num (RATN r)) (RATD r) =  *)
(* 1; the name is RatProg's theorem here)                                    *)

let BASRAUX_RATND_COPRIME = prove
 (`!r. coprime(RATN r,&(RATD r))`,
  GEN_TAC THEN MP_TAC(SPEC `r:rat` RATND_THM) THEN
  MAP_EVERY ABBREV_TAC [`N = RATN r`; `D = RATD r`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "min")))) THEN
  ASM_CASES_TAC `N:int = &0` THENL
   [FIRST_X_ASSUM(fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th) THEN
    UNDISCH_TAC `N:int = &0 ==> D = 1` THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN CONV_TAC INTEGER_RULE;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`N:int`; `&D:int`] int_gcd) THEN
  ABBREV_TAC `g = gcd(N:int,&D)` THEN REWRITE_TAC[int_divides] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (X_CHOOSE_TAC `n1:int`) (CONJUNCTS_THEN2 (X_CHOOSE_TAC `d1:int`)
    ASSUME_TAC))) THEN
  SUBGOAL_THEN `g:int = &1` SUBST_ALL_TAC THENL
   [ALL_TAC; REWRITE_TAC[int_coprime] THEN ASM_MESON_TAC[]] THEN
  SUBGOAL_THEN `&0 < (g:int) /\ &0 < (d1:int)` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < (g:int) * d1` MP_TAC THENL
     [UNDISCH_TAC `&D:int = g * d1` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      ASM_REWRITE_TAC[INT_OF_NUM_LT];
      ALL_TAC] THEN
    ASM_CASES_TAC `g:int = &0` THEN
    ASM_REWRITE_TAC[INT_MUL_LZERO; INT_LT_REFL] THEN
    SUBGOAL_THEN `&0 < (g:int)` (fun th -> SIMP_TAC[th; INT_LT_MUL_EQ]) THEN
    ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&(num_of_int d1) = d1` ASSUME_TAC THENL
   [ASM_SIMP_TAC[INT_OF_NUM_OF_INT; INT_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `abs(N:int) <= abs n1` MP_TAC THENL
   [REMOVE_THEN "min" MATCH_MP_TAC THEN EXISTS_TAC `num_of_int d1` THEN
    ASM_REWRITE_TAC[GSYM INT_OF_NUM_LT] THEN
    UNDISCH_TAC `r = rat_of_int N / &D` THEN
    REWRITE_TAC[GSYM rat_of_int_of_num] THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN BASRAUX_RAT_TRANSFER_TAC THEN
    SUBGOAL_THEN `~(real_of_int g = &0) /\ ~(real_of_int d1 = &0)` MP_TAC THENL
     [REWRITE_TAC[GSYM int_of_num_th; GSYM int_eq] THEN ASM_INT_ARITH_TAC;
      CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[INT_ABS_MUL] THEN
  SUBGOAL_THEN `&0 < abs(n1:int)` MP_TAC THENL
   [REWRITE_TAC[INT_ARITH `&0 < abs(x:int) <=> ~(x = &0)`] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `~(N:int = &0)` THEN ASM_REWRITE_TAC[INT_MUL_RZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(g:int) = g` SUBST1_TAC THENL
   [ASM_INT_ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(g:int) * abs(n1:int) <= &1 * abs n1` MP_TAC THENL
   [ASM_REWRITE_TAC[INT_MUL_LID]; ASM_SIMP_TAC[INT_LE_RMUL_EQ]] THEN
  ASM_INT_ARITH_TAC);;

(* RATN and RATD are the only representation in lowest terms: RatProg's     *)
(* gcd_RATND, with its hypothesis gcd (Num (ABS n)) d = 1 in integer form    *)
(* (BASRAUX_NUM_GCD_ABS below relates the two).                              *)

let BASRAUX_RATND_UNIQUE = prove
 (`!n d. coprime(n,&d) /\ 0 < d
         ==> RATN (rat_of_int n / &d) = n /\ RATD (rat_of_int n / &d) = d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `r = rat_of_int n / &d` THEN
  MP_TAC(SPEC `r:rat` RATND_THM) THEN MP_TAC(SPEC `r:rat` BASRAUX_RATND_COPRIME) THEN
  MAP_EVERY ABBREV_TAC [`N = RATN r`; `D = RATD r`] THEN
  DISCH_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  SUBGOAL_THEN `n * &D = N * &d:int` ASSUME_TAC THENL
   [SUBGOAL_THEN `rat_of_int n / &d = rat_of_int N / &D` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    BASRAUX_RAT_TRANSFER_TAC THEN
    SUBGOAL_THEN `~(&d = &0) /\ ~(&D = &0)` MP_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN `D:num = d` SUBST_ALL_TAC THENL
   [REWRITE_TAC[GSYM DIVIDES_ANTISYM; num_divides] THEN
    MP_TAC(SPECL [`n:int`; `&d:int`; `N:int`; `&D:int`] (INTEGER_RULE
     `!n d N D:int. coprime(n,d) /\ coprime(N,D) /\ n * D = N * d
                    ==> d divides D /\ D divides d`)) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `n * &d = N * &d:int` THEN
  REWRITE_TAC[INT_EQ_MUL_RCANCEL; INT_OF_NUM_EQ] THEN ASM_MESON_TAC[LT_NZ]);;

let RATN_RATD_RAT_OF_INT = prove
 (`!i. RATN (rat_of_int i) = i /\ RATD (rat_of_int i) = 1`,
  GEN_TAC THEN MP_TAC(SPECL [`i:int`; `1`] BASRAUX_RATND_UNIQUE) THEN
  REWRITE_TAC[ARITH; INTEGER_RULE `!i:int. coprime(i,&1)`] THEN
  SUBGOAL_THEN `rat_of_int i / &1 = rat_of_int i` (fun th -> REWRITE_TAC[th]) THEN
  BASRAUX_RAT_TRANSFER_TAC THEN REWRITE_TAC[REAL_DIV_1]);;

let RATND_RAT_OF_NUM = prove
 (`!n. RATN (&n) = &n /\ RATD (&n) = 1`,
  GEN_TAC THEN MP_TAC(SPEC `&n:int` RATN_RATD_RAT_OF_INT) THEN
  REWRITE_TAC[rat_of_int_of_num]);;

let RATN_EQ0 = prove
 (`!r. ((RATN r = &0) <=> (r = &0)) /\ ((&0 = RATN r) <=> (r = &0))`,
  GEN_TAC THEN
  SUBGOAL_THEN `(RATN r = &0) <=> (r = &0)` (fun th -> MESON_TAC[th]) THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [GSYM RATN_DIV_RATD] THEN
  MP_TAC(SPEC `r:rat` RATD_NZERO) THEN BASRAUX_RAT_TRANSFER_TAC THEN
  STRIP_TAC THEN SUBGOAL_THEN `~(&(RATD r) = &0)` MP_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_EQ]; CONV_TAC REAL_FIELD]);;

let BASRAUX_RATND_NEG = prove
 (`!r. RATN (--r) = --(RATN r) /\ RATD (--r) = RATD r`,
  GEN_TAC THEN MP_TAC(SPECL [`--(RATN r)`; `RATD r`] BASRAUX_RATND_UNIQUE) THEN
  REWRITE_TAC[RATD_NZERO; BASRAUX_RATND_COPRIME;
              INTEGER_RULE `!a b:int. coprime(--a,b) <=> coprime(a,b)`] THEN
  REWRITE_TAC[rat_of_int_ainv; GSYM RAT_DIV_AINV; RATN_DIV_RATD]);;

let RATN_NEG = prove
 (`!r. RATN (--r) = --(RATN r)`,
  REWRITE_TAC[BASRAUX_RATND_NEG]);;

let RATD_NEG = prove
 (`!r. RATD (--r) = RATD r`,
  REWRITE_TAC[BASRAUX_RATND_NEG]);;

let RATN_SIGN = prove
 (`!x. (&0 < RATN x <=> &0 < x) /\ (&0 <= RATN x <=> &0 <= x) /\
       (RATN x < &0 <=> x < &0) /\ (RATN x <= &0 <=> x <= &0)`,
  GEN_TAC THEN MP_TAC(SPEC `x:rat` RATN_DIV_RATD) THEN
  MP_TAC(SPEC `x:rat` RATD_NZERO) THEN BASRAUX_RAT_TRANSFER_TAC THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LT] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_LE_RDIV_EQ; REAL_LT_LDIV_EQ;
               REAL_LE_LDIV_EQ; REAL_MUL_LZERO]);;

(* the integer form of HOL4's gcd (Num (ABS n)) d = 1 (RatProg's RAT_TYPE) *)

let BASRAUX_NUM_GCD_ABS = prove
 (`!n d. num_gcd(num_of_int (abs n),d) = 1 <=> coprime(n,&d)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[NUMBER_RULE `!a b:num. num_gcd(a,b) = 1 <=> coprime(a,b)`;
              num_coprime] THEN
  SIMP_TAC[INT_OF_NUM_OF_INT; INT_ABS_POS] THEN
  DISJ_CASES_THEN SUBST1_TAC (INT_ARITH `abs(n:int) = n \/ abs n = --n`) THEN
  REWRITE_TAC[INTEGER_RULE `!a b:int. coprime(--a,b) <=> coprime(a,b)`]);;

(* ------------------------------------------------------------------------- *)
(* HOL4's [simp] theorems over these operations (those about rat_sgn, frac   *)
(* and powers aside), registered with cake_add_simps as in HOL4.             *)
(* ------------------------------------------------------------------------- *)

let RAT_OF_NUM_LEQ = prove
 (`!a b. (&a:rat) <= &b <=> a <= b`,
  BASRAUX_RAT_TRANSFER_TAC THEN REWRITE_TAC[REAL_OF_NUM_LE]);;

let RAT_OF_NUM_LES = prove
 (`!a b. (&a:rat) < &b <=> a < b`,
  BASRAUX_RAT_TRANSFER_TAC THEN REWRITE_TAC[REAL_OF_NUM_LT]);;

let RAT_ADD_RID = prove
 (`!a:rat. a + &0 = a`,
  BASRAUX_RAT_TRANSFER_TAC THEN REAL_ARITH_TAC);;

let RAT_ADD_LID = prove
 (`!a:rat. &0 + a = a`,
  BASRAUX_RAT_TRANSFER_TAC THEN REAL_ARITH_TAC);;

let RAT_MUL_LID = prove
 (`!a:rat. &1 * a = a`,
  BASRAUX_RAT_TRANSFER_TAC THEN REAL_ARITH_TAC);;

let RAT_MUL_LZERO = prove
 (`!r1:rat. &0 * r1 = &0`,
  BASRAUX_RAT_TRANSFER_TAC THEN REAL_ARITH_TAC);;

let RAT_MUL_RZERO = prove
 (`!r1:rat. r1 * &0 = &0`,
  BASRAUX_RAT_TRANSFER_TAC THEN REAL_ARITH_TAC);;

let RAT_DIV_0 = prove
 (`!x:rat. &0 / x = &0`,
  BASRAUX_RAT_TRANSFER_TAC THEN REWRITE_TAC[real_div; REAL_MUL_LZERO]);;

let RAT_AINV_0 = prove
 (`--(&0:rat) = &0`,
  BASRAUX_RAT_TRANSFER_TAC THEN REAL_ARITH_TAC);;

let RAT_AINV_AINV = prove
 (`!r1:rat. --(--r1) = r1`,
  BASRAUX_RAT_TRANSFER_TAC THEN REAL_ARITH_TAC);;

let RAT_EQ_AINV = prove
 (`!r1 r2:rat. --r1 = --r2 <=> r1 = r2`,
  BASRAUX_RAT_TRANSFER_TAC THEN REAL_ARITH_TAC);;

let RAT_SUB_LID = prove
 (`!r1:rat. &0 - r1 = --r1`,
  BASRAUX_RAT_TRANSFER_TAC THEN REAL_ARITH_TAC);;

let RAT_SUB_RID = prove
 (`!r1:rat. r1 - &0 = r1`,
  BASRAUX_RAT_TRANSFER_TAC THEN REAL_ARITH_TAC);;

let RAT_SUB_ID = prove
 (`!r:rat. r - r = &0`,
  BASRAUX_RAT_TRANSFER_TAC THEN REAL_ARITH_TAC);;

let RAT_NO_ZERODIV_THM = prove
 (`!r1 r2:rat. r1 * r2 = &0 <=> r1 = &0 \/ r2 = &0`,
  BASRAUX_RAT_TRANSFER_TAC THEN REWRITE_TAC[REAL_ENTIRE]);;

let RAT_MINV_1 = prove
 (`rat_minv (&1) = &1`,
  BASRAUX_RAT_TRANSFER_TAC THEN REWRITE_TAC[REAL_INV_1]);;

let RAT_DIV_1 = prove
 (`!r:rat. r / &1 = r`,
  BASRAUX_RAT_TRANSFER_TAC THEN REWRITE_TAC[REAL_DIV_1]);;

let RAT_DIV_NEG1 = prove
 (`!r:rat. r / --(&1) = --r`,
  BASRAUX_RAT_TRANSFER_TAC THEN CONV_TAC REAL_FIELD);;

let RAT_DIV_INV = prove
 (`!r:rat. ~(r = &0) ==> r / r = &1`,
  BASRAUX_RAT_TRANSFER_TAC THEN CONV_TAC REAL_FIELD);;

let RAT_LT_NUM_CALCULATE = prove
 (`(!a b. (&a:rat) < &b <=> a < b) /\
   (!m n. --(&m:rat) < &n <=> 0 < m \/ 0 < n) /\
   (!m n. (&m:rat) < --(&n) <=> F) /\
   (!m n. --(&m:rat) < --(&n) <=> n < m)`,
  BASRAUX_RAT_TRANSFER_TAC THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LT] THEN REAL_ARITH_TAC);;

let RAT_LE_NUM_CALCULATE = prove
 (`(!a b. (&a:rat) <= &b <=> a <= b) /\
   (!m n. --(&m:rat) <= &n <=> T) /\
   (!m n. (&m:rat) <= --(&n) <=> m = 0 /\ n = 0) /\
   (!m n. --(&m:rat) <= --(&n) <=> n <= m)`,
  BASRAUX_RAT_TRANSFER_TAC THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_EQ] THEN REAL_ARITH_TAC);;

let RAT_AINV_SGN = prove
 (`!r:rat. (&0 < --r <=> r < &0) /\ (--r < &0 <=> &0 < r)`,
  BASRAUX_RAT_TRANSFER_TAC THEN REAL_ARITH_TAC);;

let RAT_AINV_EQ_NUM = prove
 (`!x n. --x = &n <=> x = rat_of_int (--(&n))`,
  BASRAUX_RAT_TRANSFER_TAC THEN REAL_ARITH_TAC);;

let _ = cake_add_simps
  [RAT_OF_NUM_LEQ; RAT_OF_NUM_LES; RAT_ADD_RID; RAT_ADD_LID; RAT_MUL_RID;
   RAT_MUL_LID; RAT_MUL_LZERO; RAT_MUL_RZERO; RAT_DIV_0; RAT_AINV_0;
   RAT_AINV_AINV; RAT_EQ_AINV; RAT_SUB_LID; RAT_SUB_RID; RAT_SUB_ID;
   RAT_NO_ZERODIV_THM; RAT_MINV_1; RAT_DIV_1; RAT_DIV_NEG1; RAT_DIV_INV;
   RAT_MINV_EQ_0; RAT_DIV_EQ0; RAT_EQ_NUM_CALCULATE; RAT_LT_NUM_CALCULATE;
   RAT_LE_NUM_CALCULATE; rat_of_int_11; rat_of_int_of_num; rat_of_int_LE;
   rat_of_int_LT; RATD_NZERO; RATND_RAT_OF_NUM; RATN_EQ0; RATN_SIGN;
   RAT_AINV_SGN; RATN_NEG; RATD_NEG; RATN_RATD_RAT_OF_INT; RATN_DIV_RATD;
   RAT_AINV_EQ_NUM];;

(* ------------------------------------------------------------------------- *)
(* The interface as before this file, with the rat entries last.            *)
(* ------------------------------------------------------------------------- *)

let () =
  let rat_consts = ["rat_of_num"; "rat_ainv"; "rat_add"; "rat_sub"; "rat_mul";
                    "rat_div"; "rat_les"; "rat_leq"; "rat_gre"; "rat_geq"] in
  let now = !the_interface in
  let rats = filter (fun (_,(c,_)) -> mem c rat_consts) now in
  let others = filter (fun e -> not (mem e rats) &&
                                not (mem e basraux_interface_before)) now in
  the_interface := others @ basraux_interface_before @ rats;;
