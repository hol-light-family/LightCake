(* ========================================================================= *)
(* RatProg: port of HOL4 basis/RatProgScript.sml (CakeML v3479).             *)
(* Module for computing over the rational numbers.                           *)
(*                                                                           *)
(* rat is hol4/rat.ml's (decision D6: the subtype of real of the rationals,  *)
(* with HOL4's names); HOL4's gcd a b is num_gcd (a,b), translated through   *)
(* IntProg's certificate for mlint_num_gcd (num_gcd_eq_gcd); HOL4's          *)
(* num_of_int (ml_translator) is ml_num_of_int, its int / is int_div.        *)
(* HOL4's intreal INT_FLOOR and INT_CEILING are hol4/binary_ieee.ml's, its   *)
(* is_int is HOL Light's integer.                                            *)
(* ========================================================================= *)

needs "translator/ml_translator.ml";;
needs "basis/pure/mlvector.ml";;
needs "basis/IntProg.ml";;
needs "hol4/gcd.ml";;
needs "hol4/rat.ml";;
needs "basis/pure/mlrat.ml";;
needs "basis/PrettyPrinterProg.ml";;
needs "basis/basisFunctionsLib.ml";;

type_invention_error := true;;

translation_extends "PrettyPrinterProg";;

ml_prog_update ml_prog_open_local_block;;

use_full_type_names := false;;
register_type `:rational`;;
use_full_type_names := true;;

let div_gcd_def = new_definition
  `div_gcd a b =
     let d = num_gcd (ml_num_of_int a, b) in
       if d = 0 \/ d = 1 then RatPair a b else RatPair (int_div a (&d)) (b DIV d)`;;

let _ = translate (REWRITE_RULE [GSYM num_gcd_eq_gcd] div_gcd_def);;

ml_prog_update ml_prog_open_local_in_block;;

ml_prog_update (ml_prog_open_module "Rat");;

(* provides the Map.map name for the map type *)
ml_prog_update (ml_prog_add_dec
  `Dtabbrev unknown_loc [] (implode "rat") (Atapp [] (Short (implode "rational")))` I);;

(* refinement invariants *)

let RAT_TYPE_def = new_definition
  `RAT_TYPE (r:rat) =
     \v. ?(n:int) (d:num). (r = rat_div (rat_of_int n) (rat_of_num d)) /\
                           num_gcd (num_of_int (abs n), d) = 1 /\ ~(d = 0) /\
                           RATIONAL_TYPE (RatPair n d) v`;;

add_type_inv `RAT_TYPE` `:rational`;;

let REAL_TYPE_def = new_definition
  `REAL_TYPE (r:real) =
     \v. ?x:rat. RAT_TYPE x v /\ (real_of_rat x = r)`;;

add_type_inv `REAL_TYPE` `:rational`;;

(* transfer *)

(* Arrow certificates: after unfolding, the hypothesis is applied to the   *)
(* argument values first, then MESON closes the goal with the given facts   *)
let BAS1AUX_ARROW_TAC thl =
  REWRITE_TAC[ml_Arrow_def; ml_AppReturns_def; REAL_TYPE_def] THEN
  CONV_TAC (DEPTH_CONV BETA_CONV) THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM (fun th -> FIRST_X_ASSUM (fun th2 ->
    STRIP_ASSUME_TAC (SPEC_ALL (MATCH_MP th th2)))) THEN
  ASM_MESON_TAC thl;;

let RAT_RAT = prove
 (`(!r1. real_of_rat ((f1:rat->rat) r1) = f2 (real_of_rat r1)) ==>
   !v. (RAT_TYPE --> RAT_TYPE) f1 v ==>
       (REAL_TYPE --> REAL_TYPE) f2 v`,
  DISCH_TAC THEN BAS1AUX_ARROW_TAC []);;

let RAT_RAT_RAT = prove
 (`(!r1 r2. real_of_rat ((f1:rat->rat->rat) r1 r2) =
            f2 (real_of_rat r1) (real_of_rat r2)) ==>
   !v. (RAT_TYPE --> RAT_TYPE --> RAT_TYPE) f1 v ==>
       (REAL_TYPE --> REAL_TYPE --> REAL_TYPE) f2 v`,
  DISCH_TAC THEN BAS1AUX_ARROW_TAC []);;

let RAT_RAT_BOOL = prove
 (`(!r1 r2. (f1:rat->rat->bool) r1 r2 <=> f2 (real_of_rat r1) (real_of_rat r2)) ==>
   !v. (RAT_TYPE --> RAT_TYPE --> ml_BOOL) f1 v ==>
       (REAL_TYPE --> REAL_TYPE --> ml_BOOL) f2 v`,
  DISCH_THEN (fun th ->
    ASSUME_TAC (GEN_ALL (AP_THM (AP_TERM `ml_BOOL` (SPEC_ALL th)) `u:v`))) THEN
  BAS1AUX_ARROW_TAC []);;

let RAT_BOOL = prove
 (`(!r1. ((f1:rat->bool) r1) = f2 (real_of_rat r1)) ==>
   !v. (RAT_TYPE --> ml_BOOL) f1 v ==>
       (REAL_TYPE --> ml_BOOL) f2 v`,
  DISCH_THEN (fun th ->
    ASSUME_TAC (GEN_ALL (AP_THM (AP_TERM `ml_BOOL` (SPEC_ALL th)) `u:v`))) THEN
  BAS1AUX_ARROW_TAC []);;

let RAT_INT = prove
 (`(!r1. ((f1:rat->int) r1) = f2 (real_of_rat r1)) ==>
   !v. (RAT_TYPE --> ml_INT) f1 v ==>
       (REAL_TYPE --> ml_INT) f2 v`,
  DISCH_THEN (fun th ->
    ASSUME_TAC (GEN_ALL (AP_THM (AP_TERM `ml_INT` (SPEC_ALL th)) `u:v`))) THEN
  BAS1AUX_ARROW_TAC []);;

(* -- *)

next_ml_names := ["fromInt"];;
let rational_of_int_v_thm = translate rational_of_int_def;;

let Eval_RAT_INT = add_user_proved_v_thm (MATCH_MP (prove
 (`!v. (ml_INT --> RATIONAL_TYPE) rational_of_int v ==>
       (ml_INT --> RAT_TYPE) rat_of_int v`,
  MP_TAC (prove
   (`!x u. RATIONAL_TYPE (rational_of_int x) u ==>
           ?n d. rat_of_int x = rat_div (rat_of_int n) (rat_of_num d) /\
                 num_gcd (num_of_int (abs n), d) = 1 /\ ~(d = 0) /\
                 RATIONAL_TYPE (RatPair n d) u`,
    REPEAT STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`x:int`; `1`] THEN
    ASM_REWRITE_TAC[GSYM rational_of_int_def; RAT_DIV_1; ARITH_EQ] THEN NUMBER_TAC)) THEN
  REWRITE_TAC[ml_Arrow_def; ml_AppReturns_def; RAT_TYPE_def] THEN
  CONV_TAC (DEPTH_CONV BETA_CONV) THEN MESON_TAC[])) rational_of_int_v_thm);;

let Eval_RAT_NUM = add_user_proved_v_thm (prove
 (`(ml_NUM --> RAT_TYPE) rat_of_num rational_of_int_v`,
  MP_TAC Eval_RAT_INT THEN REWRITE_TAC[ml_Arrow_def; ml_NUM_def] THEN
  CONV_TAC (DEPTH_CONV BETA_CONV) THEN DISCH_TAC THEN X_GEN_TAC `n:num` THEN
  FIRST_ASSUM (MP_TAC o SPEC `&n:int`) THEN REWRITE_TAC[rat_of_int_of_num]));;

let Eval_REAL_INT = add_user_proved_v_thm (MATCH_MP (prove
 (`!v. (ml_INT --> RAT_TYPE) rat_of_int v ==>
       (ml_INT --> REAL_TYPE) real_of_int v`,
  BAS1AUX_ARROW_TAC [real_of_int_of_rat])) Eval_RAT_INT);;

let Eval_REAL_NUM = add_user_proved_v_thm (prove
 (`(ml_NUM --> REAL_TYPE) real_of_num rational_of_int_v`,
  MP_TAC Eval_REAL_INT THEN REWRITE_TAC[ml_Arrow_def; ml_NUM_def] THEN
  CONV_TAC (DEPTH_CONV BETA_CONV) THEN DISCH_TAC THEN X_GEN_TAC `n:num` THEN
  FIRST_ASSUM (MP_TAC o SPEC `&n:int`) THEN REWRITE_TAC[int_of_num_th]));;

let BAS1AUX_RAT_DIV_POS = prove
 (`!d. ~(d = 0) ==> &0 < &d`,
  REWRITE_TAC[REAL_OF_NUM_LT; LT_NZ]);;
let BAS1AUX_DIV_MUL = REAL_FIELD `&0 < d ==> y / d * e = (y * e) / d`;;
let BAS1AUX_RAT_LE = prove
 (`!n1 d1 n2 d2. ~(d1 = 0) /\ ~(d2 = 0) ==>
     (rat_leq (rat_div (rat_of_int n1) (rat_of_num d1)) (rat_div (rat_of_int n2) (rat_of_num d2)) <=>
      n1 * &d2 <= n2 * &d1)`,
  BASRAUX_RAT_TRANSFER_TAC THEN REWRITE_TAC[int_le; int_mul_th; int_of_num_th] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[BAS1AUX_RAT_DIV_POS; REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ; BAS1AUX_DIV_MUL]);;

(* (RATIONAL_TYPE --> RATIONAL_TYPE --> B) f v ==> (RAT_TYPE --> RAT_TYPE --> B) g v  *)
(* from the lemma about f and g on the pairs (the antecedent of the goal): a direct  *)
(* proof through a transfer lemma, proved once (ASM_MESON_TAC on the unfolded      *)
(* Arrow, as before, took about 11 s per goal)                                     *)
let BAS1AUX_RAT_ARROW_TAC =
  let transfer = prove
   (`!(R:X->Y->bool) (A:X->v->bool) (A':Y->v->bool) (B:Z->v->bool) (B':W->v->bool) f g.
       (!r v. A' r v ==> ?x. R x r /\ A x v) /\
       (!x1 x2 r1 r2 u. R x1 r1 /\ R x2 r2 /\ B (f x1 x2) u ==> B' (g r1 r2) u)
       ==> !v. (A --> A --> B) f v ==> (A' --> A' --> B') g v`,
    REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "rep") (LABEL_TAC "rel")) THEN
    X_GEN_TAC `v:v` THEN REWRITE_TAC[ml_Arrow_def; ml_AppReturns_def] THEN
    CONV_TAC (DEPTH_CONV BETA_CONV) THEN DISCH_THEN (LABEL_TAC "h") THEN
    X_GEN_TAC `r1:Y` THEN X_GEN_TAC `v1:v` THEN
    DISCH_THEN (fun a -> USE_THEN "rep" (fun rep ->
      X_CHOOSE_THEN `x1:X` STRIP_ASSUME_TAC (MATCH_MP rep a))) THEN
    X_GEN_TAC `refs1:(v store_v)list` THEN
    USE_THEN "h" (fun h -> FIRST_X_ASSUM (fun a ->
      MP_TAC (SPEC `refs1:(v store_v)list` (MATCH_MP (SPEC `x1:X` h) a)))) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`env1:v sem_env`; `exp1:exp`; `refs1':(v store_v)list`; `u1:v`] THEN
    STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`env1:v sem_env`; `exp1:exp`; `refs1':(v store_v)list`; `u1:v`] THEN
    ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `r2:Y` THEN X_GEN_TAC `v2:v` THEN
    DISCH_THEN (fun a -> USE_THEN "rep" (fun rep ->
      X_CHOOSE_THEN `x2:X` STRIP_ASSUME_TAC (MATCH_MP rep a))) THEN
    X_GEN_TAC `refs2:(v store_v)list` THEN
    FIRST_X_ASSUM (fun h6 -> FIRST_X_ASSUM (fun a ->
      MP_TAC (SPEC `refs2:(v store_v)list` (MATCH_MP (SPEC `x2:X` h6) a)))) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`env2:v sem_env`; `exp2:exp`; `refs2':(v store_v)list`; `u2:v`] THEN
    STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`env2:v sem_env`; `exp2:exp`; `refs2':(v store_v)list`; `u2:v`] THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "rel" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`x1:X`; `x2:X`] THEN ASM_REWRITE_TAC[]) in
  let rep = ISPEC `\(x:rational) (r:rat). ?n d. x = RatPair n d /\
                     r = rat_div (rat_of_int n) (rat_of_num d) /\ ~(d = 0)` transfer in
  fun (thl:thm list) ->
    DISCH_TAC THEN MATCH_MP_TAC rep THEN CONV_TAC (DEPTH_CONV BETA_CONV) THEN CONJ_TAC THENL
     [REWRITE_TAC[RAT_TYPE_def] THEN CONV_TAC (DEPTH_CONV BETA_CONV) THEN MESON_TAC[];
      REPEAT STRIP_TAC THEN ASM_MESON_TAC thl];;

let RatProg_pair_le_def = cake_def
  `RatProg_pair_le (RatPair n1 d1) (RatPair n2 d2) <=> (n1 * &d2 <= n2 * &d1:int)`;;

next_ml_names := ["<="];;
let pair_le_v_thm = translate RatProg_pair_le_def;;

let Eval_RAT_LE = add_user_proved_v_thm (MATCH_MP (prove
 (`!v. (RATIONAL_TYPE --> RATIONAL_TYPE --> ml_BOOL) RatProg_pair_le v ==>
       (RAT_TYPE --> RAT_TYPE --> ml_BOOL) rat_leq v`,
  MP_TAC (prove
   (`!n1 d1 n2 d2 u. ~(d1 = 0) /\ ~(d2 = 0) ==>
       (ml_BOOL (RatProg_pair_le (RatPair n1 d1) (RatPair n2 d2)) u <=>
        ml_BOOL (rat_leq (rat_div (rat_of_int n1) (rat_of_num d1))
                         (rat_div (rat_of_int n2) (rat_of_num d2))) u)`,
    SIMP_TAC[BAS1AUX_RAT_LE; RatProg_pair_le_def])) THEN
  BAS1AUX_RAT_ARROW_TAC [])) pair_le_v_thm);;

let Eval_REAL_LE = add_user_proved_v_thm (MATCH_MP (prove
 (`!v. (RAT_TYPE --> RAT_TYPE --> ml_BOOL) rat_leq v ==>
       (REAL_TYPE --> REAL_TYPE --> ml_BOOL) real_le v`,
  MATCH_MP_TAC (GEN_ALL RAT_RAT_BOOL) THEN REWRITE_TAC[real_of_rat_le])) Eval_RAT_LE);;

next_ml_names := [">="];;
let Eval_RAT_GE = translate rat_geq_def;;

let Eval_REAL_GE = add_user_proved_v_thm (MATCH_MP (prove
 (`!v. (RAT_TYPE --> RAT_TYPE --> ml_BOOL) rat_geq v ==>
       (REAL_TYPE --> REAL_TYPE --> ml_BOOL) real_ge v`,
  MATCH_MP_TAC (GEN_ALL RAT_RAT_BOOL) THEN
  REWRITE_TAC[real_of_rat_le; rat_geq_def; real_ge])) Eval_RAT_GE);;

let BAS1AUX_RAT_LT = prove
 (`!n1 d1 n2 d2. ~(d1 = 0) /\ ~(d2 = 0) ==>
     (rat_les (rat_div (rat_of_int n1) (rat_of_num d1)) (rat_div (rat_of_int n2) (rat_of_num d2)) <=>
      n1 * &d2 < n2 * &d1)`,
  BASRAUX_RAT_TRANSFER_TAC THEN REWRITE_TAC[int_lt; int_mul_th; int_of_num_th] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[BAS1AUX_RAT_DIV_POS; REAL_LT_LDIV_EQ; REAL_LT_RDIV_EQ; BAS1AUX_DIV_MUL]);;

let RatProg_pair_lt_def = cake_def
  `RatProg_pair_lt (RatPair n1 d1) (RatPair n2 d2) <=> (n1 * &d2 < n2 * &d1:int)`;;

next_ml_names := ["<"];;
let pair_lt_v_thm = translate RatProg_pair_lt_def;;

let Eval_RAT_LT = add_user_proved_v_thm (MATCH_MP (prove
 (`!v. (RATIONAL_TYPE --> RATIONAL_TYPE --> ml_BOOL) RatProg_pair_lt v ==>
       (RAT_TYPE --> RAT_TYPE --> ml_BOOL) rat_les v`,
  MP_TAC (prove
   (`!n1 d1 n2 d2 u. ~(d1 = 0) /\ ~(d2 = 0) ==>
       (ml_BOOL (RatProg_pair_lt (RatPair n1 d1) (RatPair n2 d2)) u <=>
        ml_BOOL (rat_les (rat_div (rat_of_int n1) (rat_of_num d1))
                         (rat_div (rat_of_int n2) (rat_of_num d2))) u)`,
    SIMP_TAC[BAS1AUX_RAT_LT; RatProg_pair_lt_def])) THEN
  BAS1AUX_RAT_ARROW_TAC [])) pair_lt_v_thm);;

let Eval_REAL_LT = add_user_proved_v_thm (MATCH_MP (prove
 (`!v. (RAT_TYPE --> RAT_TYPE --> ml_BOOL) rat_les v ==>
       (REAL_TYPE --> REAL_TYPE --> ml_BOOL) real_lt v`,
  MATCH_MP_TAC (GEN_ALL RAT_RAT_BOOL) THEN REWRITE_TAC[real_of_rat_lt])) Eval_RAT_LT);;

next_ml_names := [">"];;
let Eval_RAT_GT = translate rat_gre_def;;

let Eval_REAL_GT = add_user_proved_v_thm (MATCH_MP (prove
 (`!v. (RAT_TYPE --> RAT_TYPE --> ml_BOOL) rat_gre v ==>
       (REAL_TYPE --> REAL_TYPE --> ml_BOOL) real_gt v`,
  MATCH_MP_TAC (GEN_ALL RAT_RAT_BOOL) THEN
  REWRITE_TAC[real_of_rat_lt; rat_gre_def; real_gt])) Eval_RAT_GT);;

let RatProg_pair_compare_def = cake_def
  `RatProg_pair_compare (RatPair n1 d1) (RatPair n2 d2) =
     let x1 = n1 * &d2 in
     let x2 = n2 * &d1 in
       if x1 < x2 then LESS else
       if x2 < x1 then GREATER else EQUAL`;;

let rat_compare_def = new_definition
  `rat_compare (r1:rat) r2 =
     if rat_les r1 r2 then LESS else if rat_les r2 r1 then GREATER else EQUAL`;;

next_ml_names := ["compare"];;
let pair_compare_v_thm = translate RatProg_pair_compare_def;;

let Eval_RAT_COMPARE = add_user_proved_v_thm (MATCH_MP (prove
 (`!v. (RATIONAL_TYPE --> RATIONAL_TYPE --> ORDERING_TYPE) RatProg_pair_compare v ==>
       (RAT_TYPE --> RAT_TYPE --> ORDERING_TYPE) rat_compare v`,
  MP_TAC (prove
   (`!n1 d1 n2 d2 u. ~(d1 = 0) /\ ~(d2 = 0) ==>
       (ORDERING_TYPE (RatProg_pair_compare (RatPair n1 d1) (RatPair n2 d2)) u <=>
        ORDERING_TYPE (rat_compare (rat_div (rat_of_int n1) (rat_of_num d1))
                                   (rat_div (rat_of_int n2) (rat_of_num d2))) u)`,
    SIMP_TAC[BAS1AUX_RAT_LT; RatProg_pair_compare_def; rat_compare_def; LET_DEF;
             LET_END_DEF])) THEN
  BAS1AUX_RAT_ARROW_TAC [])) pair_compare_v_thm);;

next_ml_names := ["min"];;
let Eval_RAT_MIN = translate rat_min_def;;

let Eval_REAL_MIN = add_user_proved_v_thm (MATCH_MP (prove
 (`!v. (RAT_TYPE --> RAT_TYPE --> RAT_TYPE) rat_min v ==>
       (REAL_TYPE --> REAL_TYPE --> REAL_TYPE) real_min v`,
  MATCH_MP_TAC (GEN_ALL RAT_RAT_RAT) THEN
  REWRITE_TAC[real_min; rat_min_def; GSYM real_of_rat_lt] THEN REPEAT GEN_TAC THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC)) Eval_RAT_MIN);;

next_ml_names := ["max"];;
let Eval_RAT_MAX = translate rat_max_def;;

let Eval_REAL_MAX = add_user_proved_v_thm (MATCH_MP (prove
 (`!v. (RAT_TYPE --> RAT_TYPE --> RAT_TYPE) rat_max v ==>
       (REAL_TYPE --> REAL_TYPE --> REAL_TYPE) real_max v`,
  MATCH_MP_TAC (GEN_ALL RAT_RAT_RAT) THEN
  REWRITE_TAC[real_max; rat_max_def; rat_gre_def; GSYM real_of_rat_lt] THEN REPEAT GEN_TAC THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC)) Eval_RAT_MAX);;

let gcd_LESS_EQ = prove
 (`!m n. ~(n = 0) ==> num_gcd(m,n) <= n`,
  REPEAT STRIP_TAC THEN MP_TAC (SPECL [`num_gcd(m,n)`; `n:num`] DIVIDES_LE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[GCD]);;

let RatProg_DIV_EQ_0 = prove
 (`0 < n ==> ((m DIV n = 0) <=> m < n)`,
  SIMP_TAC[DIV_EQ_0; LT_NZ]);;

let DIV_GCD_NONZERO = prove
 (`(0 < m ==> 0 < m DIV num_gcd(m,n)) /\ (0 < n ==> 0 < n DIV num_gcd(m,n))`,
  REWRITE_TAC[LT_NZ] THEN CONJ_TAC THEN DISCH_TAC THENL
   [MP_TAC (SPECL [`n:num`; `m:num`] BASRAUX_GCD_DIV) THEN ASM_REWRITE_TAC[] THEN
    SUBST1_TAC (NUMBER_RULE `num_gcd(n,m) = num_gcd(m,n)`) THEN SIMP_TAC[];
    MP_TAC (SPECL [`m:num`; `n:num`] BASRAUX_GCD_DIV) THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[]]);;

let INT_NEG_DIV_FACTOR = prove
 (`0 < (x:num) ==> (int_div (--(&(x * y))) (&x) = --(&y))`,
  REWRITE_TAC[LT_NZ] THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM INT_OF_NUM_MUL; INT_ARITH `--(a * b:int) = a * --b`] THEN
  MATCH_MP_TAC INT_DIV_LMUL THEN ASM_REWRITE_TAC[INT_OF_NUM_EQ]);;

let PAIR_TYPE_IMP_RAT_TYPE = prove
 (`r = rat_div (rat_of_int m) (rat_of_num n) /\ ~(n = 0) ==>
   RATIONAL_TYPE (div_gcd m n) v ==> RAT_TYPE r v`,
  REWRITE_TAC[RAT_TYPE_def; div_gcd_def; ml_num_of_int_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC (DEPTH_CONV BETA_CONV) THEN REPEAT STRIP_TAC THEN
  ABBREV_TAC `k = num_of_int (abs m)` THEN
  SUBGOAL_THEN `abs (m:int) = &k` ASSUME_TAC THENL
   [EXPAND_TAC "k" THEN SIMP_TAC[INT_OF_NUM_OF_INT; INT_ABS_POS]; ALL_TAC] THEN
  MP_TAC (SPECL [`k:num`; `n:num`] BASRAUX_GCD_DIV) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `g = num_gcd(k,n)` THEN STRIP_TAC THEN
  UNDISCH_TAC `RATIONAL_TYPE (if g = 0 \/ g = 1 then RatPair m n
                              else RatPair (int_div m (&g)) (n DIV g)) v` THEN
  ASM_CASES_TAC `g = 1` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THENL
   [MAP_EVERY EXISTS_TAC [`m:int`; `n:num`] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`int_div m (&g)`; `n DIV g`] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `int_div m (&g) * &g = m /\ abs (int_div m (&g)) = &(k DIV g)`
    STRIP_ASSUME_TAC THENL
   [DISJ_CASES_TAC (SPEC `m:int` INT_IMAGE) THEN
    FIRST_X_ASSUM (X_CHOOSE_THEN `j:num` SUBST_ALL_TAC) THEN
    RULE_ASSUM_TAC (REWRITE_RULE [INT_ABS_NUM; INT_ABS_NEG; INT_OF_NUM_EQ]) THEN
    UNDISCH_TAC `j:num = k` THEN DISCH_THEN SUBST_ALL_TAC THENL
     [ASM_SIMP_TAC[INT_DIV; INT_OF_NUM_MUL; INT_ABS_NUM];
      MP_TAC (INST [`g:num`,`x:num`; `k DIV g`,`y:num`] INT_NEG_DIV_FACTOR) THEN
      ASM_REWRITE_TAC[LT_NZ; ONCE_REWRITE_RULE[MULT_SYM] (ASSUME `k DIV g * g = k`)] THEN
      DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[INT_ABS_NEG; INT_ABS_NUM; INT_MUL_LNEG; INT_OF_NUM_MUL] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[NUM_OF_INT_OF_NUM]] THEN
  BASRAUX_RAT_TRANSFER_TAC THEN
  MP_TAC (AP_TERM `real_of_int` (ASSUME `int_div m (&g) * &g = m`)) THEN
  MP_TAC (AP_TERM `real_of_num` (ASSUME `n DIV g * g = n`)) THEN
  MP_TAC (ASSUME `~(g = 0)`) THEN MP_TAC (ASSUME `~(n DIV g = 0)`) THEN
  REWRITE_TAC[int_mul_th; int_of_num_th; GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_EQ] THEN
  CONV_TAC REAL_FIELD);;

let RatProg_pair_add_def = cake_def
  `RatProg_pair_add (RatPair n1 d1) (RatPair n2 d2) =
     div_gcd ((n1 * &d2) + (n2 * &d1)) (d1 * d2)`;;

next_ml_names := ["+"];;
let pair_add_v_thm = translate RatProg_pair_add_def;;

let abs_rat_ONTO = prove
 (`!r. ?f. abs_rat f = r`,
  GEN_TAC THEN EXISTS_TAC `rep_rat r` THEN REWRITE_TAC[rat_type_thm]);;

let BAS1AUX_RAT_NZ = prove
 (`!d. ~(d = 0) ==> ~(&d = &0:real)`,
  REWRITE_TAC[REAL_OF_NUM_EQ]);;

let BAS1AUX_RAT_ARG_TAC n d =
  DISCH_THEN (MP_TAC o CONV_RULE (REWRITE_CONV[RAT_TYPE_def] THENC DEPTH_CONV BETA_CONV)) THEN
  DISCH_THEN (X_CHOOSE_THEN n (X_CHOOSE_THEN d STRIP_ASSUME_TAC));;

let BAS1AUX_ARROW2_TAC helper =
  REWRITE_TAC[ml_Arrow_def; ml_AppReturns_def] THEN
  CONV_TAC (DEPTH_CONV BETA_CONV) THEN GEN_TAC THEN
  DISCH_TAC THEN X_GEN_TAC `r1:rat` THEN X_GEN_TAC `w1:v` THEN
  BAS1AUX_RAT_ARG_TAC `n1:int` `d1:num` THEN
  X_GEN_TAC `refs:(v store_v)list` THEN
  FIRST_X_ASSUM (MP_TAC o SPECL [`RatPair n1 d1`; `w1:v`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN (MP_TAC o SPEC `refs:(v store_v)list`) THEN
  DISCH_THEN (X_CHOOSE_THEN `env1:v sem_env` (X_CHOOSE_THEN `exp1:exp`
    (X_CHOOSE_THEN `refs1:(v store_v)list` (X_CHOOSE_THEN `u1:v` STRIP_ASSUME_TAC)))) THEN
  MAP_EVERY EXISTS_TAC [`env1:v sem_env`; `exp1:exp`; `refs1:(v store_v)list`; `u1:v`] THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `r2:rat` THEN X_GEN_TAC `w2:v` THEN
  BAS1AUX_RAT_ARG_TAC `n2:int` `d2:num` THEN
  X_GEN_TAC `refs2:(v store_v)list` THEN
  FIRST_X_ASSUM (MP_TAC o SPECL [`RatPair n2 d2`; `w2:v`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN (MP_TAC o SPEC `refs2:(v store_v)list`) THEN
  DISCH_THEN (X_CHOOSE_THEN `env2:v sem_env` (X_CHOOSE_THEN `exp2:exp`
    (X_CHOOSE_THEN `refs3:(v store_v)list` (X_CHOOSE_THEN `u2:v` STRIP_ASSUME_TAC)))) THEN
  MAP_EVERY EXISTS_TAC [`env2:v sem_env`; `exp2:exp`; `refs3:(v store_v)list`; `u2:v`] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC helper THEN
  MAP_EVERY EXISTS_TAC [`n1:int`; `d1:num`; `n2:int`; `d2:num`] THEN ASM_REWRITE_TAC[];;

let Eval_RAT_ADD = add_user_proved_v_thm (MATCH_MP (prove
 (`!v. (RATIONAL_TYPE --> RATIONAL_TYPE --> RATIONAL_TYPE) RatProg_pair_add v ==>
       (RAT_TYPE --> RAT_TYPE --> RAT_TYPE) rat_add v`,
  BAS1AUX_ARROW2_TAC (prove
   (`!n1 d1 n2 d2 r1 r2 u.
       r1 = rat_div (rat_of_int n1) (rat_of_num d1) /\
       r2 = rat_div (rat_of_int n2) (rat_of_num d2) /\ ~(d1 = 0) /\ ~(d2 = 0) /\
       RATIONAL_TYPE (RatProg_pair_add (RatPair n1 d1) (RatPair n2 d2)) u ==>
       RAT_TYPE (rat_add r1 r2) u`,
    REWRITE_TAC[RatProg_pair_add_def] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC (REWRITE_RULE[IMP_IMP] (GEN_ALL PAIR_TYPE_IMP_RAT_TYPE)) THEN
    MAP_EVERY EXISTS_TAC [`(n1:int) * &d2 + (n2:int) * &d1`; `(d1:num) * d2`] THEN
    ASM_REWRITE_TAC[MULT_EQ_0] THEN
    BASRAUX_RAT_TRANSFER_TAC THEN
    REWRITE_TAC[int_add_th; int_mul_th; int_of_num_th; GSYM REAL_OF_NUM_MUL] THEN
    MP_TAC (SPEC `d1:num` BAS1AUX_RAT_NZ) THEN MP_TAC (SPEC `d2:num` BAS1AUX_RAT_NZ) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_FIELD)))) pair_add_v_thm);;

let Eval_REAL_ADD = add_user_proved_v_thm (MATCH_MP (prove
 (`!v. (RAT_TYPE --> RAT_TYPE --> RAT_TYPE) rat_add v ==>
       (REAL_TYPE --> REAL_TYPE --> REAL_TYPE) real_add v`,
  MATCH_MP_TAC (GEN_ALL RAT_RAT_RAT) THEN REWRITE_TAC[real_of_rat_add])) Eval_RAT_ADD);;

let RatProg_pair_sub_def = cake_def
  `RatProg_pair_sub (RatPair n1 d1) (RatPair n2 d2) =
     div_gcd ((n1 * &d2) - (n2 * &d1)) (d1 * d2)`;;

next_ml_names := ["-"];;
let pair_sub_v_thm = translate RatProg_pair_sub_def;;

let Eval_RAT_SUB = add_user_proved_v_thm (MATCH_MP (prove
 (`!v. (RATIONAL_TYPE --> RATIONAL_TYPE --> RATIONAL_TYPE) RatProg_pair_sub v ==>
       (RAT_TYPE --> RAT_TYPE --> RAT_TYPE) rat_sub v`,
  BAS1AUX_ARROW2_TAC (prove
   (`!n1 d1 n2 d2 r1 r2 u.
       r1 = rat_div (rat_of_int n1) (rat_of_num d1) /\
       r2 = rat_div (rat_of_int n2) (rat_of_num d2) /\ ~(d1 = 0) /\ ~(d2 = 0) /\
       RATIONAL_TYPE (RatProg_pair_sub (RatPair n1 d1) (RatPair n2 d2)) u ==>
       RAT_TYPE (rat_sub r1 r2) u`,
    REWRITE_TAC[RatProg_pair_sub_def] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC (REWRITE_RULE[IMP_IMP] (GEN_ALL PAIR_TYPE_IMP_RAT_TYPE)) THEN
    MAP_EVERY EXISTS_TAC [`(n1:int) * &d2 - (n2:int) * &d1`; `(d1:num) * d2`] THEN
    ASM_REWRITE_TAC[MULT_EQ_0] THEN
    BASRAUX_RAT_TRANSFER_TAC THEN
    REWRITE_TAC[int_sub_th; int_mul_th; int_of_num_th; GSYM REAL_OF_NUM_MUL] THEN
    MP_TAC (SPEC `d1:num` BAS1AUX_RAT_NZ) THEN MP_TAC (SPEC `d2:num` BAS1AUX_RAT_NZ) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_FIELD)))) pair_sub_v_thm);;

let Eval_REAL_SUB = add_user_proved_v_thm (MATCH_MP (prove
 (`!v. (RAT_TYPE --> RAT_TYPE --> RAT_TYPE) rat_sub v ==>
       (REAL_TYPE --> REAL_TYPE --> REAL_TYPE) real_sub v`,
  MATCH_MP_TAC (GEN_ALL RAT_RAT_RAT) THEN REWRITE_TAC[real_of_rat_sub])) Eval_RAT_SUB);;

let rat_neg_lem = prove
 (`!(x:rat). rat_ainv x = rat_sub (rat_of_num 0) x`,
  BASRAUX_RAT_TRANSFER_TAC THEN REAL_ARITH_TAC);;

next_ml_names := ["~"];;
let Eval_RAT_NEG = translate rat_neg_lem;;

let Eval_REAL_NEG = add_user_proved_v_thm (MATCH_MP (prove
 (`!v. (RAT_TYPE --> RAT_TYPE) (rat_ainv) v ==>
       (REAL_TYPE --> REAL_TYPE) real_neg v`,
  MATCH_MP_TAC (GEN_ALL RAT_RAT) THEN REWRITE_TAC[real_of_rat_ainv])) Eval_RAT_NEG);;

let RatProg_pair_mul_def = cake_def
  `RatProg_pair_mul (RatPair n1 d1) (RatPair n2 d2) = div_gcd (n1 * n2:int) (d1 * d2:num)`;;

next_ml_names := ["*"];;
let pair_mul_v_thm = translate RatProg_pair_mul_def;;

let Eval_RAT_MUL = add_user_proved_v_thm (MATCH_MP (prove
 (`!v. (RATIONAL_TYPE --> RATIONAL_TYPE --> RATIONAL_TYPE) RatProg_pair_mul v ==>
       (RAT_TYPE --> RAT_TYPE --> RAT_TYPE) rat_mul v`,
  BAS1AUX_ARROW2_TAC (prove
   (`!n1 d1 n2 d2 r1 r2 u.
       r1 = rat_div (rat_of_int n1) (rat_of_num d1) /\
       r2 = rat_div (rat_of_int n2) (rat_of_num d2) /\ ~(d1 = 0) /\ ~(d2 = 0) /\
       RATIONAL_TYPE (RatProg_pair_mul (RatPair n1 d1) (RatPair n2 d2)) u ==>
       RAT_TYPE (rat_mul r1 r2) u`,
    REWRITE_TAC[RatProg_pair_mul_def] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC (REWRITE_RULE[IMP_IMP] (GEN_ALL PAIR_TYPE_IMP_RAT_TYPE)) THEN
    MAP_EVERY EXISTS_TAC [`(n1:int) * (n2:int)`; `(d1:num) * d2`] THEN
    ASM_REWRITE_TAC[MULT_EQ_0] THEN
    BASRAUX_RAT_TRANSFER_TAC THEN
    REWRITE_TAC[int_mul_th; int_of_num_th; GSYM REAL_OF_NUM_MUL] THEN
    MP_TAC (SPEC `d1:num` BAS1AUX_RAT_NZ) THEN MP_TAC (SPEC `d2:num` BAS1AUX_RAT_NZ) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_FIELD)))) pair_mul_v_thm);;

let Eval_REAL_MUL = add_user_proved_v_thm (MATCH_MP (prove
 (`!v. (RAT_TYPE --> RAT_TYPE --> RAT_TYPE) rat_mul v ==>
       (REAL_TYPE --> REAL_TYPE --> REAL_TYPE) real_mul v`,
  MATCH_MP_TAC (GEN_ALL RAT_RAT_RAT) THEN REWRITE_TAC[real_of_rat_mul])) Eval_RAT_MUL);;

let RatProg_pair_inv_def = cake_def
  `RatProg_pair_inv (RatPair n1 d1) =
     RatPair (if n1 < &0 then --(&d1) else (&d1:int)) (ml_num_of_int n1)`;;

next_ml_names := ["inv"];;
let pair_inv_v_thm = translate RatProg_pair_inv_def;;

let BAS1AUX_INV_FINISH_TAC =
  SUBGOAL_THEN `~(j = 0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `~(r = rat_of_num 0)` THEN
    ASM_REWRITE_TAC[INT_NEG_0] THEN BASRAUX_RAT_TRANSFER_TAC THEN
    REWRITE_TAC[int_of_num_th; real_div; REAL_MUL_LZERO];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[INT_OF_NUM_LT; LT_NZ; INT_ABS_NEG; INT_ABS_NUM; NUM_OF_INT_OF_NUM] THEN
  BASRAUX_RAT_TRANSFER_TAC THEN REWRITE_TAC[int_of_num_th; int_neg_th] THEN
  MP_TAC (SPEC `d:num` BAS1AUX_RAT_NZ) THEN MP_TAC (SPEC `j:num` BAS1AUX_RAT_NZ) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_FIELD;;

let BAS1AUX_RAT_INV = prove
 (`!n d r u. r = rat_div (rat_of_int n) (rat_of_num d) /\
             num_gcd (num_of_int (abs n), d) = 1 /\ ~(d = 0) /\ ~(r = rat_of_num 0) /\
             RATIONAL_TYPE (RatProg_pair_inv (RatPair n d)) u ==>
             RAT_TYPE (rat_minv r) u`,
  REWRITE_TAC[RatProg_pair_inv_def; RAT_TYPE_def; ml_num_of_int_def] THEN
  CONV_TAC (DEPTH_CONV BETA_CONV) THEN REPEAT STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`if (n:int) < &0 then --(&d) else (&d:int)`; `num_of_int (abs (n:int))`] THEN
  ASM_REWRITE_TAC[] THEN
  DISJ_CASES_TAC (SPEC `n:int` INT_IMAGE) THEN
  FIRST_X_ASSUM (X_CHOOSE_THEN `j:num` SUBST_ALL_TAC) THEN
  RULE_ASSUM_TAC (REWRITE_RULE [INT_ABS_NUM; INT_ABS_NEG; NUM_OF_INT_OF_NUM]) THEN
  ASM_REWRITE_TAC[INT_ABS_NUM; INT_ABS_NEG; NUM_OF_INT_OF_NUM; INT_OF_NUM_LT;
                  INT_ARITH `--(&j:int) < &0 <=> &0 < (&j:int)`; INT_ARITH `~((&j:int) < &0)`] THEN
  ONCE_REWRITE_TAC[NUMBER_RULE `num_gcd(a,b) = num_gcd(b,a)`] THEN ASM_REWRITE_TAC[] THEN
  BAS1AUX_INV_FINISH_TAC);;

let Eval_RAT_INV = add_user_proved_v_thm (MATCH_MP (UNDISCH (prove
 (`ml_PRECONDITION (~(r = rat_of_num 0)) ==>
   !v. (RATIONAL_TYPE --> RATIONAL_TYPE) RatProg_pair_inv v ==>
       (ml_Eq RAT_TYPE r --> RAT_TYPE) rat_minv v`,
  REWRITE_TAC[ml_PRECONDITION_def; ml_Arrow_def; ml_AppReturns_def; ml_Eq_def] THEN
  CONV_TAC (DEPTH_CONV BETA_CONV) THEN
  DISCH_TAC THEN GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `r1:rat` THEN X_GEN_TAC `w1:v` THEN
  DISCH_THEN (CONJUNCTS_THEN2 SUBST_ALL_TAC MP_TAC) THEN
  BAS1AUX_RAT_ARG_TAC `n1:int` `d1:num` THEN
  X_GEN_TAC `refs:(v store_v)list` THEN
  FIRST_X_ASSUM (MP_TAC o SPECL [`RatPair n1 d1`; `w1:v`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN (MP_TAC o SPEC `refs:(v store_v)list`) THEN
  DISCH_THEN (X_CHOOSE_THEN `env1:v sem_env` (X_CHOOSE_THEN `exp1:exp`
    (X_CHOOSE_THEN `refs1:(v store_v)list` (X_CHOOSE_THEN `u1:v` STRIP_ASSUME_TAC)))) THEN
  MAP_EVERY EXISTS_TAC [`env1:v sem_env`; `exp1:exp`; `refs1:(v store_v)list`; `u1:v`] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC BAS1AUX_RAT_INV THEN
  MAP_EVERY EXISTS_TAC [`n1:int`; `d1:num`] THEN ASM_MESON_TAC[]))) pair_inv_v_thm);;

let Eval_REAL_INV = add_user_proved_v_thm (UNDISCH_ALL (SPEC `r:real` (MATCH_MP (prove
 (`(!r. (ml_PRECONDITION (~(r = rat_of_num 0)) ==> (ml_Eq RAT_TYPE r --> RAT_TYPE) rat_minv v)) ==>
   (!x. (ml_PRECONDITION (~(x = &0)) ==> (ml_Eq REAL_TYPE x --> REAL_TYPE) real_inv v))`,
  REWRITE_TAC[ml_PRECONDITION_def; ml_Arrow_def; ml_AppReturns_def; ml_Eq_def; REAL_TYPE_def] THEN
  CONV_TAC (DEPTH_CONV BETA_CONV) THEN
  DISCH_TAC THEN X_GEN_TAC `x:real` THEN DISCH_TAC THEN X_GEN_TAC `x1:real` THEN X_GEN_TAC `w1:v` THEN
  DISCH_THEN (CONJUNCTS_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `q:rat` STRIP_ASSUME_TAC)) THEN
  X_GEN_TAC `refs:(v store_v)list` THEN
  FIRST_X_ASSUM (MP_TAC o SPEC `q:rat`) THEN
  SUBGOAL_THEN `~(q = rat_of_num 0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `~(x1 = &0)` THEN
    FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN REWRITE_TAC[real_of_rat_int];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN (MP_TAC o SPECL [`q:rat`; `w1:v`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN (MP_TAC o SPEC `refs:(v store_v)list`) THEN
  DISCH_THEN (X_CHOOSE_THEN `env1:v sem_env` (X_CHOOSE_THEN `exp1:exp`
    (X_CHOOSE_THEN `refs1:(v store_v)list` (X_CHOOSE_THEN `u1:v` STRIP_ASSUME_TAC)))) THEN
  MAP_EVERY EXISTS_TAC [`env1:v sem_env`; `exp1:exp`; `refs1:(v store_v)list`; `u1:v`] THEN
  ASM_REWRITE_TAC[] THEN EXISTS_TAC `rat_minv q` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM (SUBST1_TAC o SYM o check (fun th -> rand (concl th) = `x1:real`)) THEN
  ASM_SIMP_TAC[real_of_rat_inv])) (GEN_ALL (DISCH_ALL Eval_RAT_INV)))));;

next_ml_names := ["/"];;
let Eval_RAT_DIV = translate RAT_DIV_MULMINV;;

let rat_div_side_def = update_precondition (tr_fetch "rat_div_side_def");;

let real_of_rat_eq_0 = prove
 (`~(real_of_rat r = &0) ==> ~(r = rat_of_num 0)`,
  MESON_TAC[real_of_rat_int]);;


let Eval_REAL_DIV_lemma = prove
 (`!v. (!v1 v2. ml_PRECONDITION (rat_div_side v1 v2) ==>
                (ml_Eq RAT_TYPE v1 --> ml_Eq RAT_TYPE v2 --> RAT_TYPE) rat_div v) ==>
       ml_PRECONDITION (~(r = &0)) ==>
       (REAL_TYPE --> ml_Eq REAL_TYPE r --> REAL_TYPE) real_div v`,
  REWRITE_TAC[rat_div_side_def; ml_PRECONDITION_def; ml_Arrow_def; ml_AppReturns_def;
               ml_Eq_def; REAL_TYPE_def] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
   X_GEN_TAC `x1:real` THEN X_GEN_TAC `w1:v` THEN
   DISCH_THEN (X_CHOOSE_THEN `q1:rat` STRIP_ASSUME_TAC) THEN
   X_GEN_TAC `refs:(v store_v)list` THEN
   FIRST_ASSUM (MP_TAC o SPECL [`q1:rat`; `rat_of_num 1`]) THEN
   REWRITE_TAC[RAT_EQ_NUM_CALCULATE; ARITH_EQ] THEN
  DISCH_THEN (MP_TAC o SPECL [`q1:rat`; `w1:v`]) THEN ASM_REWRITE_TAC[] THEN
   DISCH_THEN (MP_TAC o SPEC `refs:(v store_v)list`) THEN
   DISCH_THEN (X_CHOOSE_THEN `env1:v sem_env` (X_CHOOSE_THEN `exp1:exp`
     (X_CHOOSE_THEN `refs1:(v store_v)list` (X_CHOOSE_THEN `u1:v` STRIP_ASSUME_TAC)))) THEN
   MAP_EVERY EXISTS_TAC [`env1:v sem_env`; `exp1:exp`; `refs1:(v store_v)list`; `u1:v`] THEN
   ASM_REWRITE_TAC[] THEN
   X_GEN_TAC `x2:real` THEN X_GEN_TAC `w2:v` THEN
   DISCH_THEN (CONJUNCTS_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `q2:rat` STRIP_ASSUME_TAC)) THEN
   X_GEN_TAC `refs2:(v store_v)list` THEN
   SUBGOAL_THEN `~(q2 = rat_of_num 0)` ASSUME_TAC THENL
    [MATCH_MP_TAC real_of_rat_eq_0 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   FIRST_X_ASSUM (MP_TAC o SPECL [`q1:rat`; `q2:rat`]) THEN ASM_REWRITE_TAC[] THEN
   DISCH_THEN (MP_TAC o SPECL [`q1:rat`; `w1:v`]) THEN ASM_REWRITE_TAC[] THEN
   DISCH_THEN (MP_TAC o SPEC `refs:(v store_v)list`) THEN
   DISCH_THEN (X_CHOOSE_THEN `env1':v sem_env` (X_CHOOSE_THEN `exp1':exp`
     (X_CHOOSE_THEN `refs1':(v store_v)list` (X_CHOOSE_THEN `u1':v` STRIP_ASSUME_TAC)))) THEN
  RULE_ASSUM_TAC (REWRITE_RULE [injectivity "option"; PAIR_EQ]) THEN
   FIRST_X_ASSUM (CONJUNCTS_THEN (SUBST_ALL_TAC o SYM) o
     check (fun th -> is_conj (concl th) && is_eq (fst (dest_conj (concl th))) &&
                      type_of (lhs (fst (dest_conj (concl th)))) = `:v sem_env`)) THEN
   MP_TAC (MATCH_MP eval_rel_11 (CONJ
     (ASSUME `eval_rel (state_refs_fupd (combin_K refs) ml_empty_state) env1 exp1
              (state_refs_fupd (combin_K (APPEND refs refs1)) ml_empty_state) u1`)
     (ASSUME `eval_rel (state_refs_fupd (combin_K refs) ml_empty_state) env1 exp1
              (state_refs_fupd (combin_K (APPEND refs refs1')) ml_empty_state) u1'`))) THEN
   DISCH_THEN (SUBST_ALL_TAC o SYM o CONJUNCT2) THEN
   FIRST_X_ASSUM (MP_TAC o SPECL [`q2:rat`; `w2:v`]) THEN ASM_REWRITE_TAC[] THEN
   DISCH_THEN (MP_TAC o SPEC `refs2:(v store_v)list`) THEN
   DISCH_THEN (X_CHOOSE_THEN `env2:v sem_env` (X_CHOOSE_THEN `exp2:exp`
     (X_CHOOSE_THEN `refs3:(v store_v)list` (X_CHOOSE_THEN `u2:v` STRIP_ASSUME_TAC)))) THEN
   MAP_EVERY EXISTS_TAC [`env2:v sem_env`; `exp2:exp`; `refs3:(v store_v)list`; `u2:v`] THEN
   ASM_REWRITE_TAC[] THEN EXISTS_TAC `rat_div q1 q2` THEN ASM_REWRITE_TAC[] THEN
   ASM_SIMP_TAC[real_of_rat_div]);;

let Eval_REAL_DIV = add_user_proved_v_thm (UNDISCH_ALL (MATCH_MP Eval_REAL_DIV_lemma
  (GENL [`v2:rat`; `v1:rat`] (DISCH_ALL Eval_RAT_DIV))));;

next_ml_names := ["toString"];;
let RatProg_toString_v_thm = translate mlrat_toString_def;;

(* HOL4 real_to_str_lemma [local]: real_to_str of a fraction in lowest terms *)
let BAS1AUX_REAL_TO_STR = prove
 (`!n d. num_gcd (num_of_int (abs n), d) = 1 /\ ~(d = 0)
         ==> real_to_str (real_of_rat (rat_div (rat_of_int n) (rat_of_num d))) =
             mlrat_toString (RatPair n d)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_to_str_def] THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[real_of_rat_div; RAT_EQ_NUM_CALCULATE; GSYM real_of_int_of_rat;
               real_of_rat_int] THEN
  MATCH_MP_TAC BASRAUX_REAL_TO_RATIONAL THEN ASM_REWRITE_TAC[]);;

let real_to_str_lemma = prove
 (`!v. (RATIONAL_TYPE --> STRING_TYPE) mlrat_toString v ==>
       (REAL_TYPE --> STRING_TYPE) real_to_str v`,
  REWRITE_TAC[ml_Arrow_def; ml_AppReturns_def; REAL_TYPE_def; RAT_TYPE_def] THEN
  CONV_TAC (DEPTH_CONV BETA_CONV) THEN
  GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `x:real` THEN X_GEN_TAC `w:v` THEN
  DISCH_THEN (X_CHOOSE_THEN `q:rat` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `n:int` (X_CHOOSE_THEN `d:num` STRIP_ASSUME_TAC))
    (SUBST_ALL_TAC o SYM))) THEN
  X_GEN_TAC `refs:(v store_v)list` THEN
  FIRST_X_ASSUM (MP_TAC o SPECL [`RatPair n d`; `w:v`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN (MP_TAC o SPEC `refs:(v store_v)list`) THEN
  ASM_SIMP_TAC[BAS1AUX_REAL_TO_STR]);;

let real_to_str_v_thm = add_user_proved_v_thm (MATCH_MP real_to_str_lemma RatProg_toString_v_thm);;

let pp_rat_def = new_definition
  `pp_rat (r:rational) = pp_token (mlrat_toString r)`;;

next_ml_names := ["pp_rat"];;
let pp_rat_v_thm = translate pp_rat_def;;

let rat_of_int_MUL_num = prove
 (`!n m. rat_mul (rat_of_int n) (rat_of_num m) = rat_of_int (n * &m) /\
         rat_mul (rat_of_num m) (rat_of_int n) = rat_of_int (&m * n)`,
  BASRAUX_RAT_TRANSFER_TAC THEN REWRITE_TAC[int_mul_th; int_of_num_th]);;

(* HOL4 SGN_ABS is the library's INT_SGN_ABS *)
let SGN_ABS = INT_SGN_ABS;;

let Int_Num_ABS = prove
 (`!n. &(num_of_int (abs n)) = abs (n:int)`,
  SIMP_TAC[INT_OF_NUM_OF_INT; INT_ABS_POS]);;

let RatProg_Num_le = prove
 (`!x y:int. x <= y /\ x >= &0 ==> num_of_int x <= num_of_int y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN
  SUBGOAL_THEN `&0 <= (x:int) /\ &0 <= (y:int)` STRIP_ASSUME_TAC THENL
   [ASM_INT_ARITH_TAC; ASM_SIMP_TAC[INT_OF_NUM_OF_INT]]);;

let int_divides_ABS = prove
 (`!x y:int. x divides y ==> x divides (abs y)`,
  REWRITE_TAC[INT_DIVIDES_RABS]);;

(* HOL4's proof derives the lowest terms from the RATND_THM minimality;     *)
(* here hol4/rat.ml's uniqueness of RATN and RATD gives it                   *)
let gcd_RATND = prove
 (`!n d. num_gcd (num_of_int (abs n), d) = 1 /\ 0 < d
         ==> RATN (rat_div (rat_of_int n) (rat_of_num d)) = n /\
             RATD (rat_div (rat_of_int n) (rat_of_num d)) = d`,
  REWRITE_TAC[BASRAUX_NUM_GCD_ABS] THEN MATCH_ACCEPT_TAC BASRAUX_RATND_UNIQUE);;

(* certificates (RATIONAL_TYPE --> a) f v ==> (RAT_TYPE --> a) g v with      *)
(* g (n / d) = f (RatPair n d) for n / d in lowest terms: the hypothesis is *)
(* applied to the pair, then the simplifier with the given equations and    *)
(* gcd_RATND identifies the two results                                     *)
let BAS1AUX_RAT_PROJ_TAC thl =
  REWRITE_TAC[ml_Arrow_def; ml_AppReturns_def; RAT_TYPE_def] THEN
  CONV_TAC (DEPTH_CONV BETA_CONV) THEN
  GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `r:rat` THEN X_GEN_TAC `w:v` THEN
  DISCH_THEN (X_CHOOSE_THEN `n:int` (X_CHOOSE_THEN `d:num` STRIP_ASSUME_TAC)) THEN
  X_GEN_TAC `refs:(v store_v)list` THEN
  FIRST_X_ASSUM (MP_TAC o SPECL [`RatPair n d`; `w:v`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN (MP_TAC o SPEC `refs:(v store_v)list`) THEN
  ASM_SIMP_TAC (thl @ [gcd_RATND; LT_NZ]);;

let RatProg_pair_num_def = cake_def
  `RatProg_pair_num (RatPair i n) = i`;;

next_ml_names := ["numerator"];;
let pair_num_v_thm = translate RatProg_pair_num_def;;

let Eval_RAT_RATN = add_user_proved_v_thm (MATCH_MP (prove
 (`!v. (RATIONAL_TYPE --> ml_INT) RatProg_pair_num v ==>
       (RAT_TYPE --> ml_INT) RATN v`,
  BAS1AUX_RAT_PROJ_TAC [RatProg_pair_num_def])) pair_num_v_thm);;

let RatProg_pair_denom_def = cake_def
  `RatProg_pair_denom (RatPair i n) = n`;;

next_ml_names := ["denominator"];;
let pair_denom_v_thm = translate RatProg_pair_denom_def;;

let Eval_RAT_RATD = add_user_proved_v_thm (MATCH_MP (prove
 (`!v. (RATIONAL_TYPE --> ml_NUM) RatProg_pair_denom v ==>
       (RAT_TYPE --> ml_NUM) RATD v`,
  BAS1AUX_RAT_PROJ_TAC [RatProg_pair_denom_def])) pair_denom_v_thm);;

let RatProg_pair_floor_def = cake_def
  `RatProg_pair_floor (RatPair n d) = int_div n (&d)`;;

next_ml_names := ["floor"];;
let pair_floor_v_thm = translate RatProg_pair_floor_def;;

(* HOL4: RAT_INT_FLOOR_def [nocompute] *)
let RAT_INT_FLOOR_def = new_definition
  `RAT_INT_FLOOR (r:rat) = INT_FLOOR (real_of_rat r)`;;

let RAT_INT_FLOOR_compute = prove
 (`!r. RAT_INT_FLOOR r = int_div (RATN r) (&(RATD r))`,
  GEN_TAC THEN REWRITE_TAC[RAT_INT_FLOOR_def; real_of_rat_def; INT_FLOOR; int_div_DEF;
                           INT_ARITH `~(&m:int < &0)`] THEN
  MP_TAC (SPEC `r:rat` RATD_NZERO) THEN
  SPEC_TAC (`RATN r`, `n:int`) THEN SPEC_TAC (`RATD r`, `d:num`) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC (SPECL [`n:int`; `&d:int`] INT_DIVISION) THEN
  ASM_REWRITE_TAC[INT_OF_NUM_EQ; INT_ABS_NUM] THEN
  SPEC_TAC (`(n:int) rem &(d:num)`, `s:int`) THEN SPEC_TAC (`(n:int) div &(d:num)`, `q:int`) THEN
  REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[int_add_th; int_mul_th; int_of_num_th] THEN
  RULE_ASSUM_TAC (REWRITE_RULE[int_le; int_lt; int_of_num_th]) THEN
  SUBGOAL_THEN `&0 < (&d:real)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LT]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC);;

let Eval_RAT_FLOOR = add_user_proved_v_thm (MATCH_MP (prove
 (`!v. (!r. ml_PRECONDITION (pair_floor_side r) ==>
            (ml_Eq RATIONAL_TYPE r --> ml_INT) RatProg_pair_floor v) ==>
       (RAT_TYPE --> ml_INT) RAT_INT_FLOOR v`,
  REWRITE_TAC[ml_PRECONDITION_def; ml_Arrow_def; ml_AppReturns_def; ml_Eq_def;
              RAT_TYPE_def] THEN
  CONV_TAC (DEPTH_CONV BETA_CONV) THEN
  GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `r:rat` THEN X_GEN_TAC `w:v` THEN
  DISCH_THEN (X_CHOOSE_THEN `n:int` (X_CHOOSE_THEN `d:num` STRIP_ASSUME_TAC)) THEN
  X_GEN_TAC `refs:(v store_v)list` THEN
  FIRST_X_ASSUM (MP_TAC o SPEC `RatPair n d`) THEN
  REWRITE_TAC[tr_fetch "pair_floor_side_def"; injectivity "rational"; INT_OF_NUM_EQ] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN (MP_TAC o SPECL [`RatPair n d`; `w:v`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN (MP_TAC o SPEC `refs:(v store_v)list`) THEN
  ASM_SIMP_TAC[RatProg_pair_floor_def; RAT_INT_FLOOR_compute; gcd_RATND; LT_NZ]))
  (GEN_ALL (DISCH_ALL pair_floor_v_thm)));;

let Eval_REAL_FLOOR = add_user_proved_v_thm (MATCH_MP (prove
 (`!v. (RAT_TYPE --> ml_INT) RAT_INT_FLOOR v ==>
       (REAL_TYPE --> ml_INT) INT_FLOOR v`,
  MATCH_MP_TAC (GEN_ALL RAT_INT) THEN REWRITE_TAC[RAT_INT_FLOOR_def])) Eval_RAT_FLOOR);;

(* HOL4: RAT_INT_CEILING_def [nocompute] *)
let RAT_INT_CEILING_def = new_definition
  `RAT_INT_CEILING (r:rat) = INT_CEILING (real_of_rat r)`;;

(* HOL4's proof uses intreal's INT_CEILING_INT_FLOOR; here the bounds of    *)
(* INT_FLOOR and the characterization INT_CEILING of hol4/binary_ieee.ml    *)
let RAT_INT_CEILING_compute = prove
 (`!r. RAT_INT_CEILING r =
       let i = RAT_INT_FLOOR r in
       if rat_of_int i = r then i else i + &1`,
  GEN_TAC THEN CONV_TAC (TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[RAT_INT_CEILING_def; RAT_INT_FLOOR_def] THEN
  SUBGOAL_THEN `!i. rat_of_int i = r <=> real_of_int i = real_of_rat r`
   (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[real_of_int_of_rat; real_of_rat_eq]; ALL_TAC] THEN
  MP_TAC (SPEC `real_of_rat r` INT_FLOOR_BOUNDS) THEN
  SPEC_TAC (`INT_FLOOR (real_of_rat r)`, `i:int`) THEN
  SPEC_TAC (`real_of_rat r`, `x:real`) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[int_add_th; int_of_num_th] THEN STRIP_TAC THEN
  COND_CASES_TAC THEN
  REWRITE_TAC[INT_CEILING; int_sub_th; int_add_th; int_of_num_th] THEN
  ASM_REAL_ARITH_TAC);;

next_ml_names := ["ceiling"];;
let rat_int_ceiling_v_thm = translate RAT_INT_CEILING_compute;;

let Eval_REAL_CEILING = add_user_proved_v_thm (MATCH_MP (prove
 (`!v. (RAT_TYPE --> ml_INT) RAT_INT_CEILING v ==>
       (REAL_TYPE --> ml_INT) INT_CEILING v`,
  MATCH_MP_TAC (GEN_ALL RAT_INT) THEN REWRITE_TAC[RAT_INT_CEILING_def]))
  rat_int_ceiling_v_thm);;

let RatProg_pair_is_int_def = cake_def
  `RatProg_pair_is_int (RatPair n d) <=> d = 1`;;

next_ml_names := ["is_int"];;
let pair_is_int_v_thm = translate RatProg_pair_is_int_def;;

let RAT_is_int_def = new_definition
  `RAT_is_int (x:rat) <=> x = rat_of_int (RAT_INT_FLOOR x)`;;

let RAT_is_int_compute = prove
 (`!x. RAT_is_int x <=> RATD x = 1`,
  GEN_TAC THEN REWRITE_TAC[RAT_is_int_def] THEN EQ_TAC THENL
   [DISCH_THEN (fun th -> ONCE_REWRITE_TAC[th]) THEN REWRITE_TAC[RATN_RATD_RAT_OF_INT];
    DISCH_TAC THEN
    REWRITE_TAC[RAT_INT_FLOOR_def; real_of_rat_def] THEN
    ASM_REWRITE_TAC[REAL_DIV_1; INT_FLOOR_real_of_int] THEN
    MP_TAC (SPEC `x:rat` RATN_DIV_RATD) THEN ASM_REWRITE_TAC[RAT_DIV_1] THEN
    MESON_TAC[]]);;

let Eval_RAT_is_int = add_user_proved_v_thm (MATCH_MP (prove
 (`!v. (RATIONAL_TYPE --> ml_BOOL) RatProg_pair_is_int v ==>
       (RAT_TYPE --> ml_BOOL) RAT_is_int v`,
  BAS1AUX_RAT_PROJ_TAC [RatProg_pair_is_int_def; RAT_is_int_compute])) pair_is_int_v_thm);;

(* HOL4's intreal is_int is HOL Light's integer *)
let Eval_REAL_is_int = add_user_proved_v_thm (MATCH_MP (prove
 (`!v. (RAT_TYPE --> ml_BOOL) RAT_is_int v ==>
       (REAL_TYPE --> ml_BOOL) integer v`,
  MATCH_MP_TAC (GEN_ALL RAT_BOOL) THEN
  REWRITE_TAC[RAT_is_int_def; RAT_INT_FLOOR_def] THEN GEN_TAC THEN
  REWRITE_TAC[GSYM real_of_rat_eq; GSYM real_of_int_of_rat] THEN
  SPEC_TAC (`real_of_rat r1`, `x:real`) THEN GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[INTEGER_REAL_OF_INT];
    REWRITE_TAC[int_rep] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
    REWRITE_TAC[INT_FLOOR_real_of_int]])) Eval_RAT_is_int);;

(* HOL4 unfolds RATIONAL_TYPE_def and evaluates no_closures and types_match; *)
(* here they come from the translator's EqualityType RATIONAL_TYPE           *)
let EqualityType_RAT_TYPE = store_eq_thm (prove
 (`EqualityType RAT_TYPE`,
  MP_TAC (EqualityType_rule [] `:rational`) THEN
  REWRITE_TAC[EqualityType_def; RAT_TYPE_def] THEN CONV_TAC (DEPTH_CONV BETA_CONV) THEN
  DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "nc")
    (CONJUNCTS_THEN2 (LABEL_TAC "eq") (LABEL_TAC "tm"))) THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "nc" (fun th -> MESON_TAC[th]);
    REPEAT GEN_TAC THEN
    DISCH_THEN (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `n1:int` (X_CHOOSE_THEN `d1:num` STRIP_ASSUME_TAC))
      (X_CHOOSE_THEN `n2:int` (X_CHOOSE_THEN `d2:num` STRIP_ASSUME_TAC))) THEN
    USE_THEN "eq" (fun th -> MP_TAC (MATCH_MP th (CONJ
      (ASSUME `RATIONAL_TYPE (RatPair n1 d1) v1`)
      (ASSUME `RATIONAL_TYPE (RatPair n2 d2) v2`)))) THEN
    REWRITE_TAC[injectivity "rational"] THEN DISCH_THEN SUBST1_TAC THEN
    EQ_TAC THENL
     [STRIP_TAC THEN ASM_REWRITE_TAC[];
      DISCH_TAC THEN MATCH_MP_TAC rat_of_int_eq THEN ASM_MESON_TAC[]];
    USE_THEN "tm" (fun th -> MESON_TAC[th])]));;

let EqualityType_REAL_TYPE = store_eq_thm (prove
 (`EqualityType REAL_TYPE`,
  MP_TAC EqualityType_RAT_TYPE THEN
  REWRITE_TAC[EqualityType_def; REAL_TYPE_def] THEN CONV_TAC (DEPTH_CONV BETA_CONV) THEN
  DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "nc")
    (CONJUNCTS_THEN2 (LABEL_TAC "eq") (LABEL_TAC "tm"))) THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "nc" (fun th -> MESON_TAC[th]);
    REPEAT GEN_TAC THEN
    DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_THEN `q1:rat` STRIP_ASSUME_TAC)
                                (X_CHOOSE_THEN `q2:rat` STRIP_ASSUME_TAC)) THEN
    USE_THEN "eq" (fun th -> MP_TAC (MATCH_MP th (CONJ
      (ASSUME `RAT_TYPE q1 v1`) (ASSUME `RAT_TYPE q2 v2`)))) THEN
    DISCH_THEN SUBST1_TAC THEN
    MAP_EVERY EXPAND_TAC ["x1"; "x2"] THEN REWRITE_TAC[real_of_rat_eq];
    USE_THEN "tm" (fun th -> MESON_TAC[th])]));;

ml_prog_update (ml_prog_close_module None);;

ml_prog_update (ml_prog_add_dec
  `Dtabbrev unknown_loc [] (implode "rat") (Atapp [] (Short (implode "rational")))` I);;

ml_prog_update ml_prog_close_local_block;;

finalise_translation ();;
