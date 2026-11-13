(* ========================================================================= *)
(* gcd: port of HOL4 src/num/extra_theories/gcdScript.sml (HOL4 library     *)
(* used by CakeML v3479): only GCD_EFFICIENTLY, the one theorem of the       *)
(* theory that the closure uses (basis/pure/mlintScript.sml).               *)
(*                                                                           *)
(* HOL4's curried gcd a b is HOL Light's num_gcd(a,b) (int.ml; HOL Light    *)
(* also reads gcd(a,b) on num as num_gcd through an overloaded interface).  *)
(* ========================================================================= *)

needs "hol4/vocab.ml";;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Euclid's algorithm (HOL4 gives it to computeLib, not to the simpset).     *)
(* ------------------------------------------------------------------------- *)

let GCD_EFFICIENTLY = prove
 (`!a b. num_gcd(a,b) = if a = 0 then b else num_gcd(b MOD a,a)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC NUMBER_RULE;
    FIRST_ASSUM(MP_TAC o SPEC `b:num` o MATCH_MP DIVISION) THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV)
                           [CONJUNCT1 th]) THEN
    MP_TAC(NUMBER_RULE `!q r a:num. num_gcd(a,q * a + r) = num_gcd(r,a)`) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th])]);;
