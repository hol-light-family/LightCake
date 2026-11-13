(* ========================================================================= *)
(* binary_ieee: port of HOL4 src/floating-point/binary_ieeeScript.sml.      *)
(* Theory of IEEE-754 (base 2) floating-point (basic) arithmetic: the float  *)
(* record, its value, rounding, the arithmetic operations and comparisons.   *)
(*                                                                           *)
(* Vocabulary (HOL4 -> HOL Light):                                           *)
(*   ('t,'w) float = (T,W)float (T: significand width, W: exponent width);   *)
(*   word1 = 1 word; x.Sign = float_Sign x (etc.); x with Sign := v =        *)
(*   float_Sign_fupd (K v) x; <| Sign := s; Exponent := e;                    *)
(*   Significand := m |> = float_REC s e m; (:'t # 'w) = (:T#W);             *)
(*   n2w = word, w2n = val, ~ = word_not, ?? = word_xor, <=+ = word_ule,     *)
(*   -1w = word_neg (word 1), UINT_MAXw = word_UINT_MAX;                     *)
(*   precision (:'t) = dimindex(:T);                                         *)
(*   bias (:'w) = INT_MAX (:'w) = 2 EXP (dimindex(:W) - 1) - 1;              *)
(*   UINT_MAX (:'w) = 2 EXP dimindex(:W) - 1;                                *)
(*   INT_MIN (:'w) = 2 EXP (dimindex(:W) - 1);                               *)
(*   word_msb w = bit (dimindex(:N) - 1) w; word_lsb w = bit 0 w;            *)
(*   'w + 1 (as an index type) = (W,1)finite_sum;                            *)
(*   is_integral = integer (HOL Light, same definition); EXISTS = EX;        *)
(*   Num = num_of_int (on non-negative arguments); real sqrt = sqrt (HOL     *)
(*   Light's sqrt agrees with HOL4's on [0,inf), the only arguments          *)
(*   float_sqrt gives it: LIEEE_FLOAT_SQRT_ARG_NONNEG).                      *)
(* The words are those of Library/words.ml only (no dependency on words4).   *)
(* HOL4 constants with an itself argument (:'t # 'w) are defined with a      *)
(* set argument (s:(T#W)->bool) as NAME_DEF; NAME_def is the HOL4 form.      *)
(* Renamed (clash with fpSem): the fp_op constructors FP_Sqrt FP_Add FP_Sub  *)
(* FP_Mul FP_Div are binary_ieee_FP_Sqrt ... binary_ieee_FP_Div.             *)
(* Also defined here (HOL4 intreal, used by float_to_int): INT_FLOOR,        *)
(* INT_CEILING (with LEAST_INT unfolded), with their characterizations.      *)
(* All definitions are ported; of the theorems, the basic ones are (see the  *)
(* theorem section).  Not ported (not used by the closure): the ULP and      *)
(* rounding-error lemmas (diff_float_ULP ... round_roundTiesToEven,          *)
(* round_roundTiesToEven_is_zero ...) and the bounds on next_hi, next_lo     *)
(* and float_ulp (next_hi_difference, abs_float_bounds ...).                 *)
(* ========================================================================= *)

needs "hol4/vocab.ml";;

(* ------------------------------------------------------------------------- *)
(* Binary floating point representation                                      *)
(* ------------------------------------------------------------------------- *)

let float_INFO = cake_record "float"
  ["Sign","1 word"; "Exponent","W word"; "Significand","T word"];;

let float_accessors = float_INFO.ri_accessors;;
let float_fn_updates = float_INFO.ri_fupds;;
let float_accfupds = float_INFO.ri_accfupds;;
let float_fupdfupds = float_INFO.ri_fupdfupds;;
let float_component_equality = float_INFO.ri_component_equality;;
let float_11 = injectivity "float";;
let float_nchotomy = cases "float";;

(* ------------------------------------------------------------------------- *)
(* Maps to other representations                                            *)
(* ------------------------------------------------------------------------- *)

let float_value_INDUCT,float_value_RECURSION =
  cake_type "float_value = Float real | Infinity | NaN";;

let float_value_distinct = distinctness "float_value";;
let float_value_11 = injectivity "float_value";;
let float_value_CASE = case_def "float_value";;
let float_value_case_eq = case_eq "float_value";;
let float_value_nchotomy = cases "float_value";;

let float_to_real_def = new_definition
  `float_to_real (x:(T,W)float) =
     if float_Exponent x = word 0
     then (--(&1) pow val (float_Sign x) *
           (&2 / &2 pow (2 EXP (dimindex(:W) - 1) - 1))) *
          (&(val (float_Significand x)) / &2 pow dimindex(:T))
     else (--(&1) pow val (float_Sign x) *
           (&2 pow val (float_Exponent x) /
            &2 pow (2 EXP (dimindex(:W) - 1) - 1))) *
          (&1 + &(val (float_Significand x)) / &2 pow dimindex(:T))`;;

let float_value_def = new_definition
  `float_value (x:(T,W)float) =
     if float_Exponent x = word_UINT_MAX
     then if float_Significand x = word 0 then Infinity else NaN
     else Float (float_to_real x)`;;

(* ------------------------------------------------------------------------- *)
(* Tests                                                                     *)
(* ------------------------------------------------------------------------- *)

let float_is_nan_def = cake_def
  `float_is_nan (x:(T,W)float) <=>
     match float_value x with NaN -> T | _ -> F`;;

let float_is_signalling_def = new_definition
  `float_is_signalling (x:(T,W)float) <=>
     float_is_nan x /\ ~bit (dimindex(:T) - 1) (float_Significand x)`;;

let float_is_infinite_def = cake_def
  `float_is_infinite (x:(T,W)float) <=>
     match float_value x with Infinity -> T | _ -> F`;;

let float_is_normal_def = new_definition
  `float_is_normal (x:(T,W)float) <=>
     ~(float_Exponent x = word 0) /\ ~(float_Exponent x = word_UINT_MAX)`;;

let float_is_subnormal_def = new_definition
  `float_is_subnormal (x:(T,W)float) <=>
     float_Exponent x = word 0 /\ ~(float_Significand x = word 0)`;;

let float_is_zero_def = cake_def
  `float_is_zero (x:(T,W)float) <=>
     match float_value x with Float r -> r = &0 | _ -> F`;;

let float_is_finite_def = cake_def
  `float_is_finite (x:(T,W)float) <=>
     match float_value x with Float _ -> T | _ -> F`;;

let float_is_finite_thm = prove
 (`!f:(T,W)float. float_is_finite f <=> ?r. float_value f = Float r`,
  GEN_TAC THEN REWRITE_TAC[float_is_finite_def] THEN
  STRUCT_CASES_TAC(ISPEC `float_value (f:(T,W)float)` float_value_nchotomy) THEN
  REWRITE_TAC[float_value_CASE; float_value_distinct; float_value_11] THEN
  MESON_TAC[]);;

(* HOL4 is_integral is HOL Light's integer (the same definition)            *)

let is_integral_def = prove
 (`!r. integer r <=> ?n. abs r = &n`,
  REWRITE_TAC[integer]);;

let float_is_integral_def = cake_def
  `float_is_integral (x:(T,W)float) <=>
     match float_value x with Float r -> integer r | _ -> F`;;

(* ------------------------------------------------------------------------- *)
(* Abs and Negate                                                            *)
(* ------------------------------------------------------------------------- *)

let float_negate_def = new_definition
  `float_negate (x:(T,W)float) =
     float_Sign_fupd (K (word_not (float_Sign x))) x`;;

let float_abs_def = new_definition
  `float_abs (x:(T,W)float) = float_Sign_fupd (K (word 0)) x`;;

(* ------------------------------------------------------------------------- *)
(* Some constants                                                            *)
(* ------------------------------------------------------------------------- *)

let float_plus_infinity_DEF = new_definition
  `float_plus_infinity (s:(T#W)->bool) =
     float_REC (word 0) (word_UINT_MAX:W word) (word 0:T word)`;;

let float_plus_infinity_def = prove
 (`float_plus_infinity(:T#W) =
     float_REC (word 0) (word_UINT_MAX:W word) (word 0:T word)`,
  REWRITE_TAC[float_plus_infinity_DEF]);;

let float_plus_zero_DEF = new_definition
  `float_plus_zero (s:(T#W)->bool) =
     float_REC (word 0) (word 0:W word) (word 0:T word)`;;

let float_plus_zero_def = prove
 (`float_plus_zero(:T#W) = float_REC (word 0) (word 0:W word) (word 0:T word)`,
  REWRITE_TAC[float_plus_zero_DEF]);;

let float_top_DEF = new_definition
  `float_top (s:(T#W)->bool) =
     float_REC (word 0) (word_sub word_UINT_MAX (word 1):W word)
               (word_UINT_MAX:T word)`;;

let float_top_def = prove
 (`float_top(:T#W) =
     float_REC (word 0) (word_sub word_UINT_MAX (word 1):W word)
               (word_UINT_MAX:T word)`,
  REWRITE_TAC[float_top_DEF]);;

let float_plus_min_DEF = new_definition
  `float_plus_min (s:(T#W)->bool) =
     float_REC (word 0) (word 0:W word) (word 1:T word)`;;

let float_plus_min_def = prove
 (`float_plus_min(:T#W) = float_REC (word 0) (word 0:W word) (word 1:T word)`,
  REWRITE_TAC[float_plus_min_DEF]);;

let float_minus_infinity_DEF = new_definition
  `float_minus_infinity (s:(T#W)->bool) =
     float_negate (float_plus_infinity(:T#W))`;;

let float_minus_infinity_def = prove
 (`float_minus_infinity(:T#W) = float_negate (float_plus_infinity(:T#W))`,
  REWRITE_TAC[float_minus_infinity_DEF]);;

let float_minus_zero_DEF = new_definition
  `float_minus_zero (s:(T#W)->bool) = float_negate (float_plus_zero(:T#W))`;;

let float_minus_zero_def = prove
 (`float_minus_zero(:T#W) = float_negate (float_plus_zero(:T#W))`,
  REWRITE_TAC[float_minus_zero_DEF]);;

let float_bottom_DEF = new_definition
  `float_bottom (s:(T#W)->bool) = float_negate (float_top(:T#W))`;;

let float_bottom_def = prove
 (`float_bottom(:T#W) = float_negate (float_top(:T#W))`,
  REWRITE_TAC[float_bottom_DEF]);;

let float_minus_min_DEF = new_definition
  `float_minus_min (s:(T#W)->bool) = float_negate (float_plus_min(:T#W))`;;

let float_minus_min_def = prove
 (`float_minus_min(:T#W) = float_negate (float_plus_min(:T#W))`,
  REWRITE_TAC[float_minus_min_DEF]);;

(* ------------------------------------------------------------------------- *)
(* Rounding reals to floating-point values                                   *)
(* ------------------------------------------------------------------------- *)

let flags_INFO = cake_record "flags"
  ["DivideByZero","bool"; "InvalidOp","bool"; "Overflow","bool";
   "Precision","bool"; "Underflow_BeforeRounding","bool";
   "Underflow_AfterRounding","bool"];;

let flags_accessors = flags_INFO.ri_accessors;;
let flags_fn_updates = flags_INFO.ri_fupds;;
let flags_component_equality = flags_INFO.ri_component_equality;;

let clear_flags_def = new_definition
  `clear_flags = flags_REC F F F F F F`;;

let invalidop_flags_def = new_definition
  `invalidop_flags = flags_InvalidOp_fupd (K T) clear_flags`;;

let dividezero_flags_def = new_definition
  `dividezero_flags = flags_DivideByZero_fupd (K T) clear_flags`;;

let rounding_INDUCT,rounding_RECURSION = cake_type
  "rounding = roundTiesToEven | roundTowardPositive | roundTowardNegative |
              roundTowardZero";;

let rounding_distinct = distinctness "rounding";;
let rounding_CASE = case_def "rounding";;
let rounding_case_eq = case_eq "rounding";;
let rounding_nchotomy = cases "rounding";;

let is_closest_def = new_definition
  `is_closest (s:(T,W)float->bool) (x:real) (a:(T,W)float) <=>
     a IN s /\
     !b. b IN s ==> abs (float_to_real a - x) <= abs (float_to_real b - x)`;;

let closest_such_def = new_definition
  `closest_such (p:(T,W)float->bool) (s:(T,W)float->bool) (x:real) =
     @a. is_closest s x a /\ !b. is_closest s x b /\ p b ==> p a`;;

let closest_def = new_definition
  `closest = closest_such (K T:(T,W)float->bool)`;;

let largest_DEF = new_definition
  `largest (s:(T#W)->bool) =
     (&2 pow ((2 EXP dimindex(:W) - 1) - 1) /
      &2 pow (2 EXP (dimindex(:W) - 1) - 1)) *
     (&2 - inv (&2 pow dimindex(:T)))`;;

let largest_def = prove
 (`largest(:T#W) =
     (&2 pow ((2 EXP dimindex(:W) - 1) - 1) /
      &2 pow (2 EXP (dimindex(:W) - 1) - 1)) *
     (&2 - inv (&2 pow dimindex(:T)))`,
  REWRITE_TAC[largest_DEF]);;

let threshold_DEF = new_definition
  `threshold (s:(T#W)->bool) =
     (&2 pow ((2 EXP dimindex(:W) - 1) - 1) /
      &2 pow (2 EXP (dimindex(:W) - 1) - 1)) *
     (&2 - inv (&2 pow SUC (dimindex(:T))))`;;

let threshold_def = prove
 (`threshold(:T#W) =
     (&2 pow ((2 EXP dimindex(:W) - 1) - 1) /
      &2 pow (2 EXP (dimindex(:W) - 1) - 1)) *
     (&2 - inv (&2 pow SUC (dimindex(:T))))`,
  REWRITE_TAC[threshold_DEF]);;

(* Unit in the Last Place (of least precision), for a given exponent        *)

let ULP_DEF = new_definition
  `ULP (e:W word,s:T->bool) =
     &2 pow (if e = word 0 then 1 else val e) /
     &2 pow ((2 EXP (dimindex(:W) - 1) - 1) + dimindex(:T))`;;

let ULP_def = prove
 (`!e. ULP (e:W word,(:T)) =
       &2 pow (if e = word 0 then 1 else val e) /
       &2 pow ((2 EXP (dimindex(:W) - 1) - 1) + dimindex(:T))`,
  REWRITE_TAC[ULP_DEF]);;

(* Smallest ULP                                                              *)

let ulp_DEF = new_definition
  `ulp (s:(T#W)->bool) = ULP (word 0:W word,(:T))`;;

let ulp_def = prove
 (`ulp(:T#W) = ULP (word 0:W word,(:T))`,
  REWRITE_TAC[ulp_DEF]);;

(* rounding                                                                  *)

let round_def = cake_def
  `round mode (x:real) =
     match mode with
       roundTiesToEven ->
         (let t = threshold(:T#W) in
          if x <= --t then float_minus_infinity(:T#W)
          else if x >= t then float_plus_infinity(:T#W)
          else closest_such (\a:(T,W)float. ~bit 0 (float_Significand a))
                 float_is_finite x)
     | roundTowardZero ->
         (let t = largest(:T#W) in
          if x < --t then float_bottom(:T#W)
          else if x > t then float_top(:T#W)
          else closest {a:(T,W)float | float_is_finite a /\
                                       abs (float_to_real a) <= abs x} x)
     | roundTowardPositive ->
         (let t = largest(:T#W) in
          if x < --t then float_bottom(:T#W)
          else if x > t then float_plus_infinity(:T#W)
          else closest {a:(T,W)float | float_is_finite a /\
                                       float_to_real a >= x} x)
     | roundTowardNegative ->
         (let t = largest(:T#W) in
          if x < --t then float_minus_infinity(:T#W)
          else if x > t then float_top(:T#W)
          else closest {a:(T,W)float | float_is_finite a /\
                                       float_to_real a <= x} x)`;;

let integral_round_def = cake_def
  `integral_round mode (x:real) =
     match mode with
       roundTiesToEven ->
         (let t = threshold(:T#W) in
          if x <= --t then float_minus_infinity(:T#W)
          else if x >= t then float_plus_infinity(:T#W)
          else closest_such
                 (\a:(T,W)float. ?n. EVEN n /\ abs (float_to_real a) = &n)
                 float_is_integral x)
     | roundTowardZero ->
         (let t = largest(:T#W) in
          if x < --t then float_bottom(:T#W)
          else if x > t then float_top(:T#W)
          else closest {a:(T,W)float | float_is_integral a /\
                                       abs (float_to_real a) <= abs x} x)
     | roundTowardPositive ->
         (let t = largest(:T#W) in
          if x < --t then float_bottom(:T#W)
          else if x > t then float_plus_infinity(:T#W)
          else closest {a:(T,W)float | float_is_integral a /\
                                       float_to_real a >= x} x)
     | roundTowardNegative ->
         (let t = largest(:T#W) in
          if x < --t then float_minus_infinity(:T#W)
          else if x > t then float_top(:T#W)
          else closest {a:(T,W)float | float_is_integral a /\
                                       float_to_real a <= x} x)`;;

(* ------------------------------------------------------------------------- *)
(* NaNs                                                                      *)
(* ------------------------------------------------------------------------- *)

let fp_op_INDUCT,fp_op_RECURSION = cake_type
  "fp_op =
     binary_ieee_FP_Sqrt rounding ((T,W)float)
   | binary_ieee_FP_Add rounding ((T,W)float) ((T,W)float)
   | binary_ieee_FP_Sub rounding ((T,W)float) ((T,W)float)
   | binary_ieee_FP_Mul rounding ((T,W)float) ((T,W)float)
   | binary_ieee_FP_Div rounding ((T,W)float) ((T,W)float)
   | FP_MulAdd rounding ((T,W)float) ((T,W)float) ((T,W)float)
   | FP_MulSub rounding ((T,W)float) ((T,W)float) ((T,W)float)";;

let fp_op_distinct = distinctness "fp_op";;
let fp_op_11 = injectivity "fp_op";;
let fp_op_CASE = case_def "fp_op";;
let fp_op_case_eq = case_eq "fp_op";;

let float_some_qnan_def = new_definition
  `float_some_qnan (fp_op:(T,W)fp_op) =
     (@f:(T,W)fp_op->(T,W)float.
        let qnan = f fp_op in float_is_nan qnan /\ ~float_is_signalling qnan)
     fp_op`;;

(* ------------------------------------------------------------------------- *)
(* Some arithmetic operations                                                *)
(* ------------------------------------------------------------------------- *)

(* Round, choosing between -0.0 or +0.0                                      *)

let float_round_def = new_definition
  `float_round mode toneg (r:real) =
     let x = round mode r :(T,W)float in
     if float_is_zero x
     then if toneg then float_minus_zero(:T#W) else float_plus_zero(:T#W)
     else x`;;

(* IEEE-754 permits a number of ways to detect underflow; HOL4 gives two    *)
(* (before and after rounding).                                              *)

let float_round_with_flags_def = new_definition
  `float_round_with_flags mode to_neg (r:real) =
     let x = float_round mode to_neg r :(T,W)float and a = abs r in
     let inexact = ~(float_value x = Float r) in
     (flags_Overflow_fupd
        (K (float_is_infinite x \/ &2 pow (2 EXP (dimindex(:W) - 1)) <= a))
        (flags_Precision_fupd (K inexact)
          (flags_Underflow_BeforeRounding_fupd
             (K (inexact /\ a < &2 / &2 pow (2 EXP (dimindex(:W) - 1) - 1)))
             (flags_Underflow_AfterRounding_fupd
                (K (inexact /\
                    word_ule
                      (float_Exponent
                         (float_round mode to_neg r :(T,(W,1)finite_sum)float))
                      (word (2 EXP (dimindex(:W) - 1)))))
                clear_flags))),
      x)`;;

let check_for_signalling_def = new_definition
  `check_for_signalling (l:((T,W)float)list) =
     flags_InvalidOp_fupd (K (EX float_is_signalling l)) clear_flags`;;

let real_to_float_def = new_definition
  `real_to_float m =
     (float_round m (m = roundTowardNegative) :real->(T,W)float)`;;

let real_to_float_with_flags_def = new_definition
  `real_to_float_with_flags m =
     (float_round_with_flags m (m = roundTowardNegative)
        :real->flags#(T,W)float)`;;

let float_round_to_integral_def = cake_def
  `float_round_to_integral mode (x:(T,W)float) =
     match float_value x with Float r -> integral_round mode r | _ -> x`;;

(* HOL4 intreal: INT_FLOOR x = LEAST_INT i. x < real_of_int (i + 1) and      *)
(* INT_CEILING x = LEAST_INT i. x <= real_of_int i, with LEAST_INT P =       *)
(* @i. P i /\ !j. j < i ==> ~P j (integer) unfolded.                         *)

let INT_FLOOR_def = new_definition
  `INT_FLOOR (x:real) =
     @i:int. x < real_of_int (i + &1) /\
             !j. j < i ==> ~(x < real_of_int (j + &1))`;;

let INT_CEILING_def = new_definition
  `INT_CEILING (x:real) =
     @i:int. x <= real_of_int i /\ !j. j < i ==> ~(x <= real_of_int j)`;;

let float_to_int_def = cake_def
  `float_to_int mode (x:(T,W)float) =
     match float_value x with
       Float r ->
         SOME (match mode with
                 roundTiesToEven ->
                   (let f = INT_FLOOR r in
                    let df = abs (r - real_of_int f) in
                    if df < &1 / &2 \/ df = &1 / &2 /\ EVEN (num_of_int (abs f))
                    then f else INT_CEILING r)
               | roundTowardPositive -> INT_CEILING r
               | roundTowardNegative -> INT_FLOOR r
               | roundTowardZero ->
                   (if float_Sign x = word 1 then INT_CEILING r
                    else INT_FLOOR r))
     | _ -> NONE`;;

let float_sqrt_def = cake_def
  `float_sqrt mode (x:(T,W)float) =
     if float_Sign x = word 0 then
       (match float_value x with
          NaN -> (check_for_signalling [x],
                  float_some_qnan (binary_ieee_FP_Sqrt mode x))
        | Infinity -> (clear_flags, float_plus_infinity(:T#W))
        | Float r -> float_round_with_flags mode F (sqrt r))
     else if x = float_minus_zero(:T#W) then
       (clear_flags, float_minus_zero(:T#W))
     else (invalidop_flags, float_some_qnan (binary_ieee_FP_Sqrt mode x))`;;

let float_add_def = cake_def
  `float_add mode (x:(T,W)float) (y:(T,W)float) =
     match float_value x, float_value y with
       (NaN, _) -> (check_for_signalling [x; y],
                    float_some_qnan (binary_ieee_FP_Add mode x y))
     | (_, NaN) -> (check_for_signalling [y],
                    float_some_qnan (binary_ieee_FP_Add mode x y))
     | (Infinity, Infinity) ->
         (if float_Sign x = float_Sign y then (clear_flags, x)
          else (invalidop_flags, float_some_qnan (binary_ieee_FP_Add mode x y)))
     | (Infinity, _) -> (clear_flags, x)
     | (_, Infinity) -> (clear_flags, y)
     | (Float r1, Float r2) ->
         float_round_with_flags mode
           (if r1 = &0 /\ r2 = &0 /\ float_Sign x = float_Sign y
            then float_Sign x = word 1
            else mode = roundTowardNegative) (r1 + r2)`;;

let float_sub_def = cake_def
  `float_sub mode (x:(T,W)float) (y:(T,W)float) =
     match float_value x, float_value y with
       (NaN, _) -> (check_for_signalling [x; y],
                    float_some_qnan (binary_ieee_FP_Sub mode x y))
     | (_, NaN) -> (check_for_signalling [y],
                    float_some_qnan (binary_ieee_FP_Sub mode x y))
     | (Infinity, Infinity) ->
         (if float_Sign x = float_Sign y
          then (invalidop_flags, float_some_qnan (binary_ieee_FP_Sub mode x y))
          else (clear_flags, x))
     | (Infinity, _) -> (clear_flags, x)
     | (_, Infinity) -> (clear_flags, float_negate y)
     | (Float r1, Float r2) ->
         float_round_with_flags mode
           (if r1 = &0 /\ r2 = &0 /\ ~(float_Sign x = float_Sign y)
            then float_Sign x = word 1
            else mode = roundTowardNegative) (r1 - r2)`;;

let float_mul_def = cake_def
  `float_mul mode (x:(T,W)float) (y:(T,W)float) =
     match float_value x, float_value y with
       (NaN, _) -> (check_for_signalling [x; y],
                    float_some_qnan (binary_ieee_FP_Mul mode x y))
     | (_, NaN) -> (check_for_signalling [y],
                    float_some_qnan (binary_ieee_FP_Mul mode x y))
     | (Infinity, Float r) ->
         (if r = &0
          then (invalidop_flags, float_some_qnan (binary_ieee_FP_Mul mode x y))
          else (clear_flags,
                if float_Sign x = float_Sign y then float_plus_infinity(:T#W)
                else float_minus_infinity(:T#W)))
     | (Float r, Infinity) ->
         (if r = &0
          then (invalidop_flags, float_some_qnan (binary_ieee_FP_Mul mode x y))
          else (clear_flags,
                if float_Sign x = float_Sign y then float_plus_infinity(:T#W)
                else float_minus_infinity(:T#W)))
     | (Infinity, Infinity) ->
         (clear_flags,
          if float_Sign x = float_Sign y then float_plus_infinity(:T#W)
          else float_minus_infinity(:T#W))
     | (Float r1, Float r2) ->
         float_round_with_flags mode (~(float_Sign x = float_Sign y))
           (r1 * r2)`;;

let float_div_def = cake_def
  `float_div mode (x:(T,W)float) (y:(T,W)float) =
     match float_value x, float_value y with
       (NaN, _) -> (check_for_signalling [x; y],
                    float_some_qnan (binary_ieee_FP_Div mode x y))
     | (_, NaN) -> (check_for_signalling [y],
                    float_some_qnan (binary_ieee_FP_Div mode x y))
     | (Infinity, Infinity) ->
         (invalidop_flags, float_some_qnan (binary_ieee_FP_Div mode x y))
     | (Infinity, _) ->
         (clear_flags,
          if float_Sign x = float_Sign y then float_plus_infinity(:T#W)
          else float_minus_infinity(:T#W))
     | (_, Infinity) ->
         (clear_flags,
          if float_Sign x = float_Sign y then float_plus_zero(:T#W)
          else float_minus_zero(:T#W))
     | (Float r1, Float r2) ->
         (if r2 = &0
          then if r1 = &0
               then (invalidop_flags,
                     float_some_qnan (binary_ieee_FP_Div mode x y))
               else (dividezero_flags,
                     if float_Sign x = float_Sign y
                     then float_plus_infinity(:T#W)
                     else float_minus_infinity(:T#W))
          else float_round_with_flags mode (~(float_Sign x = float_Sign y))
                 (r1 / r2))`;;

(* HOL4 writes the last let of float_mul_add with sequential bindings        *)
(* (let r1 = ..; r2 = ..; r = r1 + r2; in ..): nested lets here.             *)

let float_mul_add_def = new_definition
  `float_mul_add mode (x:(T,W)float) (y:(T,W)float) (z:(T,W)float) =
     let signP = word_xor (float_Sign x) (float_Sign y) in
     let infP = (float_is_infinite x \/ float_is_infinite y) in
     if float_is_nan x \/ float_is_nan y \/ float_is_nan z then
       (check_for_signalling [x; y; z], float_some_qnan (FP_MulAdd mode x y z))
     else if float_is_infinite x /\ float_is_zero y \/
             float_is_zero x /\ float_is_infinite y \/
             float_is_infinite z /\ infP /\ ~(signP = float_Sign z) then
       (invalidop_flags, float_some_qnan (FP_MulAdd mode x y z))
     else if float_is_infinite z /\ float_Sign z = word 0 \/
             infP /\ signP = word 0 then
       (clear_flags, float_plus_infinity(:T#W))
     else if float_is_infinite z /\ float_Sign z = word 1 \/
             infP /\ signP = word 1 then
       (clear_flags, float_minus_infinity(:T#W))
     else
       let r1 = float_to_real x * float_to_real y in
       let r2 = float_to_real z in
       let r = r1 + r2 in
       float_round_with_flags mode
         (r = &0 /\
          (if r1 = &0 /\ r2 = &0 /\ signP = float_Sign z then signP = word 1
           else mode = roundTowardNegative) \/
          r < &0)
         r`;;

(* As in HOL4, the invalid case of float_mul_sub returns the NaN of          *)
(* FP_MulAdd.                                                                *)

let float_mul_sub_def = new_definition
  `float_mul_sub mode (x:(T,W)float) (y:(T,W)float) (z:(T,W)float) =
     let signP = word_xor (float_Sign x) (float_Sign y) in
     let infP = (float_is_infinite x \/ float_is_infinite y) in
     if float_is_nan x \/ float_is_nan y \/ float_is_nan z then
       (check_for_signalling [x; y; z], float_some_qnan (FP_MulSub mode x y z))
     else if float_is_infinite x /\ float_is_zero y \/
             float_is_zero x /\ float_is_infinite y \/
             float_is_infinite z /\ infP /\ signP = float_Sign z then
       (invalidop_flags, float_some_qnan (FP_MulAdd mode x y z))
     else if float_is_infinite z /\ float_Sign z = word 1 \/
             infP /\ signP = word 0 then
       (clear_flags, float_plus_infinity(:T#W))
     else if float_is_infinite z /\ float_Sign z = word 0 \/
             infP /\ signP = word 1 then
       (clear_flags, float_minus_infinity(:T#W))
     else
       let r1 = float_to_real x * float_to_real y
       and r2 = float_to_real z in
       float_round_with_flags mode
         (if r1 = &0 /\ r2 = &0 /\ ~(signP = float_Sign z) then signP = word 1
          else mode = roundTowardNegative)
         (r1 - r2)`;;

(* ------------------------------------------------------------------------- *)
(* Some comparison operations                                                *)
(* ------------------------------------------------------------------------- *)

let float_compare_INDUCT,float_compare_RECURSION =
  cake_type "float_compare = LT | EQ | GT | UN";;

let float_compare_distinct = distinctness "float_compare";;
let float_compare_CASE = case_def "float_compare";;
let float_compare_case_eq = case_eq "float_compare";;
let float_compare_nchotomy = cases "float_compare";;

let float_compare_def = cake_def
  `float_compare (x:(T,W)float) (y:(T,W)float) =
     match float_value x, float_value y with
       (NaN, _) -> UN
     | (_, NaN) -> UN
     | (Infinity, Infinity) ->
         (if float_Sign x = float_Sign y then EQ
          else if float_Sign x = word 1 then LT
          else GT)
     | (Infinity, _) -> (if float_Sign x = word 1 then LT else GT)
     | (_, Infinity) -> (if float_Sign y = word 1 then GT else LT)
     | (Float r1, Float r2) ->
         (if r1 < r2 then LT else if r1 = r2 then EQ else GT)`;;

let float_less_than_def = new_definition
  `float_less_than (x:(T,W)float) y <=> float_compare x y = LT`;;

let float_less_equal_def = cake_def
  `float_less_equal (x:(T,W)float) y <=>
     match float_compare x y with LT -> T | EQ -> T | _ -> F`;;

let float_greater_than_def = new_definition
  `float_greater_than (x:(T,W)float) y <=> float_compare x y = GT`;;

let float_greater_equal_def = cake_def
  `float_greater_equal (x:(T,W)float) y <=>
     match float_compare x y with GT -> T | EQ -> T | _ -> F`;;

let float_equal_def = new_definition
  `float_equal (x:(T,W)float) y <=> float_compare x y = EQ`;;

let float_unordered_def = new_definition
  `float_unordered (x:(T,W)float) y <=> float_compare x y = UN`;;

let exponent_boundary_def = new_definition
  `exponent_boundary (y:(T,W)float) (x:(T,W)float) <=>
     float_Sign x = float_Sign y /\
     val (float_Exponent x) = val (float_Exponent y) + 1 /\
     ~(float_Exponent x = word 1) /\
     float_Significand y = word_neg (word 1) /\
     float_Significand x = word 0`;;

(* HOL4 defines these three among its ULP lemmas; <+ (word_lo) = word_ult    *)

let float_ulp_def = new_definition
  `float_ulp (f:(T,W)float) = ULP (float_Exponent f,(:T))`;;

let next_hi_def = new_definition
  `next_hi (x:(T,W)float) =
     if word_ult (float_Significand x) word_UINT_MAX
     then float_Significand_fupd (K (word_add (float_Significand x) (word 1))) x
     else float_REC (float_Sign x) (word_add (float_Exponent x) (word 1))
                    (word 0)`;;

let next_lo_def = new_definition
  `next_lo (x:(T,W)float) =
     if word_ult (word 0) (float_Significand x)
     then float_Significand_fupd (K (word_sub (float_Significand x) (word 1))) x
     else float_REC (float_Sign x) (word_sub (float_Exponent x) (word 1))
                    word_UINT_MAX`;;

(* ------------------------------------------------------------------------- *)
(* Some theorems: a selection of the basic HOL4 ones (properties of the      *)
(* constants, classification, negation and abs, existence of closest        *)
(* floats, overflow of rounding, evaluation of add/sub/mul/div on NaNs and   *)
(* infinities, injectivity of float_to_real).  HOL4 states some of them      *)
(* between the definitions; here they follow the definitions.  LIEEE_ names  *)
(* are local helpers (not HOL4), LIEEEAUX_ names are word lemmas.            *)
(* ------------------------------------------------------------------------- *)

let LIEEEAUX_WORD1_CASES = prove
 (`!w:1 word. w = word 0 \/ w = word 1`,
  GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_1] THEN
  MP_TAC(ISPEC `w:1 word` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_1] THEN
  ARITH_TAC);;

let LIEEEAUX_WORD_1_NE_0 = prove
 (`~(word 1:N word = word 0)`,
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_1; VAL_WORD_0] THEN ARITH_TAC);;

let LIEEEAUX_WORD_UINT_MAX_NE_0 = prove
 (`~(word_UINT_MAX:N word = word 0)`,
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_UINT_MAX; VAL_WORD_0] THEN
  MP_TAC(ISPECL [`2`; `1`; `dimindex(:N)`] LE_EXP) THEN
  REWRITE_TAC[DIMINDEX_GE_1] THEN ARITH_TAC);;

let LIEEEAUX_WORD_SUB_1_NE = prove
 (`!w:N word. ~(word_sub w (word 1) = w)`,
  GEN_TAC THEN ONCE_REWRITE_TAC[GSYM WORD_SUB_EQ_0] THEN
  REWRITE_TAC[WORD_RULE `word_sub (word_sub (w:N word) x) w = word_neg x`] THEN
  REWRITE_TAC[WORD_NEG_EQ_0; LIEEEAUX_WORD_1_NE_0]);;

let LIEEEAUX_WORD_NOT_NE = prove
 (`!w:N word. ~(word_not w = w)`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o AP_TERM `bit 0:N word->bool`) THEN
  REWRITE_TAC[BIT_WORD_NOT; DIMINDEX_GE_1; ARITH_RULE `0 < n <=> 1 <= n`] THEN
  CONV_TAC TAUT);;

let LIEEEAUX_WORD_NEG_1 = prove
 (`word_neg (word 1):N word = word_UINT_MAX`,
  MESON_TAC[VAL_EQ_MAX_MASK; VAL_WORD_UINT_MAX]);;

let LIEEEAUX_WORD_UINT_MAX_SUB_1_EQ_0 = prove
 (`word_sub word_UINT_MAX (word 1) = (word 0:N word) <=> dimindex(:N) = 1`,
  REWRITE_TAC[WORD_SUB_EQ_0; GSYM VAL_EQ; VAL_WORD_UINT_MAX; VAL_WORD_1] THEN
  MP_TAC(ISPECL [`2`; `2`; `dimindex(:N)`] LE_EXP) THEN
  ASM_CASES_TAC `dimindex(:N) = 1` THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPEC `(:N)` DIMINDEX_GE_1) THEN ASM_ARITH_TAC);;

let LIEEEAUX_WORD_FINITE = prove
 (`!s:N word->bool. FINITE s`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `IMAGE (word:num->N word) {n | n < 2 EXP dimindex(:N)}` THEN
  SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG_LT] THEN
  REWRITE_TAC[SUBSET; IN_IMAGE; IN_ELIM_THM] THEN
  MESON_TAC[WORD_VAL; VAL_BOUND]);;

(* the quiet NaN chosen by float_some_qnan exists                            *)

let LIEEE_SOME_QNAN_SELECT = prove
 (`!fp_op:(T,W)fp_op.
     float_some_qnan fp_op =
     (@f:(T,W)fp_op->(T,W)float.
        float_is_nan (f fp_op) /\ ~float_is_signalling (f fp_op)) fp_op`,
  REWRITE_TAC[float_some_qnan_def; LET_DEF; LET_END_DEF]);;

let LIEEE_SOME_QNAN_SPEC = prove
 (`!fp_op:(T,W)fp_op.
     float_is_nan (float_some_qnan fp_op) /\
     ~float_is_signalling (float_some_qnan fp_op)`,
  GEN_TAC THEN REWRITE_TAC[LIEEE_SOME_QNAN_SELECT] THEN
  CONV_TAC SELECT_CONV THEN
  EXISTS_TAC `\x:(T,W)fp_op.
                float_REC (word 0) (word_UINT_MAX:W word) (word_INT_MIN:T word)` THEN
  REWRITE_TAC[float_is_signalling_def; float_is_nan_def; float_value_def;
              float_accessors; BIT_WORD_INT_MIN] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_INT_MIN; VAL_WORD_0; EXP_EQ_0; ARITH_EQ;
              float_value_CASE]);;

let some_nan_components = prove
 (`!fp_op:(T,W)fp_op.
     float_Exponent (float_some_qnan fp_op) = word_UINT_MAX /\
     ~(float_Significand (float_some_qnan fp_op) = word 0)`,
  GEN_TAC THEN MP_TAC(ISPEC `fp_op:(T,W)fp_op` LIEEE_SOME_QNAN_SPEC) THEN
  REWRITE_TAC[float_is_nan_def; float_value_def] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[float_value_CASE]));;

let float_components = prove
 (`float_Sign (float_plus_infinity(:T#W)) = word 0 /\
   float_Exponent (float_plus_infinity(:T#W)) = word_UINT_MAX /\
   float_Significand (float_plus_infinity(:T#W)) = word 0 /\
   float_Sign (float_minus_infinity(:T#W)) = word 1 /\
   float_Exponent (float_minus_infinity(:T#W)) = word_UINT_MAX /\
   float_Significand (float_minus_infinity(:T#W)) = word 0 /\
   float_Sign (float_plus_zero(:T#W)) = word 0 /\
   float_Exponent (float_plus_zero(:T#W)) = word 0 /\
   float_Significand (float_plus_zero(:T#W)) = word 0 /\
   float_Sign (float_minus_zero(:T#W)) = word 1 /\
   float_Exponent (float_minus_zero(:T#W)) = word 0 /\
   float_Significand (float_minus_zero(:T#W)) = word 0 /\
   float_Sign (float_plus_min(:T#W)) = word 0 /\
   float_Exponent (float_plus_min(:T#W)) = word 0 /\
   float_Significand (float_plus_min(:T#W)) = word 1 /\
   float_Sign (float_minus_min(:T#W)) = word 1 /\
   float_Exponent (float_minus_min(:T#W)) = word 0 /\
   float_Significand (float_minus_min(:T#W)) = word 1 /\
   float_Sign (float_top(:T#W)) = word 0 /\
   float_Exponent (float_top(:T#W)) = word_sub word_UINT_MAX (word 1) /\
   float_Significand (float_top(:T#W)) = word_UINT_MAX /\
   float_Sign (float_bottom(:T#W)) = word 1 /\
   float_Exponent (float_bottom(:T#W)) = word_sub word_UINT_MAX (word 1) /\
   float_Significand (float_bottom(:T#W)) = word_UINT_MAX /\
   (!fp_op:(T,W)fp_op. float_Exponent (float_some_qnan fp_op) = word_UINT_MAX) /\
   (!fp_op:(T,W)fp_op. ~(float_Significand (float_some_qnan fp_op) = word 0)) /\
   (!x:(T,W)float. float_Sign (float_negate x) = word_not (float_Sign x)) /\
   (!x:(T,W)float. float_Exponent (float_negate x) = float_Exponent x) /\
   (!x:(T,W)float. float_Significand (float_negate x) = float_Significand x)`,
  REWRITE_TAC[float_plus_infinity_def; float_minus_infinity_def;
              float_plus_zero_def; float_minus_zero_def; float_plus_min_def;
              float_minus_min_def; float_top_def; float_bottom_def;
              some_nan_components; float_negate_def; float_accessors;
              float_accfupds; float_fn_updates; K_THM] THEN
  CONV_TAC WORD_REDUCE_CONV);;

let float_distinct = prove
 (`~(float_plus_infinity(:T#W) = float_minus_infinity(:T#W)) /\
   ~(float_plus_infinity(:T#W) = float_plus_zero(:T#W)) /\
   ~(float_plus_infinity(:T#W) = float_minus_zero(:T#W)) /\
   ~(float_plus_infinity(:T#W) = float_top(:T#W)) /\
   ~(float_plus_infinity(:T#W) = float_bottom(:T#W)) /\
   ~(float_plus_infinity(:T#W) = float_plus_min(:T#W)) /\
   ~(float_plus_infinity(:T#W) = float_minus_min(:T#W)) /\
   (!fp_op. ~(float_plus_infinity(:T#W) = float_some_qnan fp_op)) /\
   ~(float_minus_infinity(:T#W) = float_plus_zero(:T#W)) /\
   ~(float_minus_infinity(:T#W) = float_minus_zero(:T#W)) /\
   ~(float_minus_infinity(:T#W) = float_top(:T#W)) /\
   ~(float_minus_infinity(:T#W) = float_bottom(:T#W)) /\
   ~(float_minus_infinity(:T#W) = float_plus_min(:T#W)) /\
   ~(float_minus_infinity(:T#W) = float_minus_min(:T#W)) /\
   (!fp_op. ~(float_minus_infinity(:T#W) = float_some_qnan fp_op)) /\
   ~(float_plus_zero(:T#W) = float_minus_zero(:T#W)) /\
   ~(float_plus_zero(:T#W) = float_top(:T#W)) /\
   ~(float_plus_zero(:T#W) = float_bottom(:T#W)) /\
   ~(float_plus_zero(:T#W) = float_plus_min(:T#W)) /\
   ~(float_plus_zero(:T#W) = float_minus_min(:T#W)) /\
   (!fp_op. ~(float_plus_zero(:T#W) = float_some_qnan fp_op)) /\
   ~(float_minus_zero(:T#W) = float_top(:T#W)) /\
   ~(float_minus_zero(:T#W) = float_bottom(:T#W)) /\
   ~(float_minus_zero(:T#W) = float_plus_min(:T#W)) /\
   ~(float_minus_zero(:T#W) = float_minus_min(:T#W)) /\
   (!fp_op. ~(float_minus_zero(:T#W) = float_some_qnan fp_op)) /\
   ~(float_top(:T#W) = float_minus_min(:T#W)) /\
   ~(float_top(:T#W) = float_bottom(:T#W)) /\
   (!fp_op. ~(float_top(:T#W) = float_some_qnan fp_op)) /\
   ~(float_bottom(:T#W) = float_plus_min(:T#W)) /\
   (!fp_op. ~(float_bottom(:T#W) = float_some_qnan fp_op)) /\
   (!fp_op. ~(float_plus_min(:T#W) = float_some_qnan fp_op)) /\
   ~(float_plus_min(:T#W) = float_minus_min(:T#W)) /\
   (!fp_op. ~(float_minus_min(:T#W) = float_some_qnan fp_op)) /\
   (!x:(T,W)float. ~(float_negate x = x))`,
  REWRITE_TAC[float_component_equality; float_components] THEN
  REWRITE_TAC[LIEEEAUX_WORD_1_NE_0; GSYM LIEEEAUX_WORD_1_NE_0;
              LIEEEAUX_WORD_UINT_MAX_NE_0; GSYM LIEEEAUX_WORD_UINT_MAX_NE_0;
              LIEEEAUX_WORD_SUB_1_NE; GSYM LIEEEAUX_WORD_SUB_1_NE;
              LIEEEAUX_WORD_NOT_NE; some_nan_components] THEN
  MESON_TAC[some_nan_components; LIEEEAUX_WORD_SUB_1_NE;
            LIEEEAUX_WORD_UINT_MAX_NE_0]);;

let float_values = prove
 (`float_value (float_plus_infinity(:T#W)) = Infinity /\
   float_value (float_minus_infinity(:T#W)) = Infinity /\
   (!fp_op:(T,W)fp_op. float_value (float_some_qnan fp_op) = NaN) /\
   float_value (float_plus_zero(:T#W)) = Float (&0) /\
   float_value (float_minus_zero(:T#W)) = Float (&0) /\
   float_value (float_plus_min(:T#W)) =
     Float (&2 / &2 pow ((2 EXP (dimindex(:W) - 1) - 1) + dimindex(:T))) /\
   float_value (float_minus_min(:T#W)) =
     Float (-- &2 / &2 pow ((2 EXP (dimindex(:W) - 1) - 1) + dimindex(:T)))`,
  REWRITE_TAC[float_value_def; float_to_real_def; float_components;
              some_nan_components; GSYM LIEEEAUX_WORD_UINT_MAX_NE_0;
              float_value_11; VAL_WORD_0; VAL_WORD_1] THEN
  REWRITE_TAC[REAL_POW_ADD; real_div; REAL_INV_MUL; real_pow; REAL_POW_1] THEN
  REAL_ARITH_TAC);;

let zero_to_real = prove
 (`float_to_real (float_plus_zero(:T#W)) = &0 /\
   float_to_real (float_minus_zero(:T#W)) = &0`,
  REWRITE_TAC[float_to_real_def; float_components; VAL_WORD_0] THEN
  REAL_ARITH_TAC);;

let float_to_real_zeroes = zero_to_real;;

let sign_not_zero = prove
 (`!s:1 word. ~(--(&1) pow val s = &0)`,
  REWRITE_TAC[REAL_POW_EQ_0] THEN REAL_ARITH_TAC);;

let LIEEE_FLOAT_TESTS = [float_is_zero_def; float_is_finite_def;
  float_is_integral_def; float_is_nan_def; float_is_infinite_def;
  float_is_normal_def; float_is_subnormal_def];;

let infinity_properties = prove
 (`~float_is_zero (float_plus_infinity(:T#W)) /\
   ~float_is_zero (float_minus_infinity(:T#W)) /\
   ~float_is_finite (float_plus_infinity(:T#W)) /\
   ~float_is_finite (float_minus_infinity(:T#W)) /\
   ~float_is_integral (float_plus_infinity(:T#W)) /\
   ~float_is_integral (float_minus_infinity(:T#W)) /\
   ~float_is_nan (float_plus_infinity(:T#W)) /\
   ~float_is_nan (float_minus_infinity(:T#W)) /\
   ~float_is_normal (float_plus_infinity(:T#W)) /\
   ~float_is_normal (float_minus_infinity(:T#W)) /\
   ~float_is_subnormal (float_plus_infinity(:T#W)) /\
   ~float_is_subnormal (float_minus_infinity(:T#W)) /\
   float_is_infinite (float_plus_infinity(:T#W)) /\
   float_is_infinite (float_minus_infinity(:T#W))`,
  REWRITE_TAC(LIEEE_FLOAT_TESTS @ [float_values; float_value_CASE;
    float_components; LIEEEAUX_WORD_UINT_MAX_NE_0]));;

let zero_properties = prove
 (`float_is_zero (float_plus_zero(:T#W)) /\
   float_is_zero (float_minus_zero(:T#W)) /\
   float_is_finite (float_plus_zero(:T#W)) /\
   float_is_finite (float_minus_zero(:T#W)) /\
   float_is_integral (float_plus_zero(:T#W)) /\
   float_is_integral (float_minus_zero(:T#W)) /\
   ~float_is_nan (float_plus_zero(:T#W)) /\
   ~float_is_nan (float_minus_zero(:T#W)) /\
   ~float_is_normal (float_plus_zero(:T#W)) /\
   ~float_is_normal (float_minus_zero(:T#W)) /\
   ~float_is_subnormal (float_plus_zero(:T#W)) /\
   ~float_is_subnormal (float_minus_zero(:T#W)) /\
   ~float_is_infinite (float_plus_zero(:T#W)) /\
   ~float_is_infinite (float_minus_zero(:T#W))`,
  REWRITE_TAC(LIEEE_FLOAT_TESTS @ [float_values; float_value_CASE;
    float_components]) THEN
  MESON_TAC[integer; REAL_ABS_NUM]);;

let zeroes_are_finite_floats = prove
 (`float_is_finite (float_plus_zero(:T#W)) /\
   float_is_finite (float_minus_zero(:T#W))`,
  REWRITE_TAC[zero_properties]);;

let some_nan_properties = prove
 (`!fp_op:(T,W)fp_op.
     ~float_is_zero (float_some_qnan fp_op) /\
     ~float_is_finite (float_some_qnan fp_op) /\
     ~float_is_integral (float_some_qnan fp_op) /\
     float_is_nan (float_some_qnan fp_op) /\
     ~float_is_signalling (float_some_qnan fp_op) /\
     ~float_is_normal (float_some_qnan fp_op) /\
     ~float_is_subnormal (float_some_qnan fp_op) /\
     ~float_is_infinite (float_some_qnan fp_op)`,
  REWRITE_TAC[LIEEE_SOME_QNAN_SPEC] THEN
  REWRITE_TAC(LIEEE_FLOAT_TESTS @ [float_values; float_value_CASE;
    float_components; LIEEEAUX_WORD_UINT_MAX_NE_0]));;

let LIEEE_SIG_POS = prove
 (`!m:T word. &0 <= &(val m) / &2 pow dimindex(:T)`,
  GEN_TAC THEN MATCH_MP_TAC REAL_LE_DIV THEN
  SIMP_TAC[REAL_POS; REAL_POW_LE; REAL_ARITH `&0 <= &2`]);;

let float_is_zero = prove
 (`!x:(T,W)float.
     float_is_zero x <=>
     float_Exponent x = word 0 /\ float_Significand x = word 0`,
  GEN_TAC THEN REWRITE_TAC[float_is_zero_def; float_value_def] THEN
  COND_CASES_TAC THENL
   [COND_CASES_TAC THEN
    ASM_REWRITE_TAC[float_value_CASE; LIEEEAUX_WORD_UINT_MAX_NE_0];
    ALL_TAC] THEN
  REWRITE_TAC[float_value_CASE; float_to_real_def] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_ENTIRE; real_div; REAL_INV_EQ_0; REAL_POW_EQ_0;
              REAL_OF_NUM_EQ; ARITH_EQ; VAL_EQ_0] THEN
  REWRITE_TAC[REAL_ARITH `~(--(&1) = &0)`; GSYM real_div] THEN
  MP_TAC(ISPEC `float_Significand (x:(T,W)float)` LIEEE_SIG_POS) THEN
  REAL_ARITH_TAC);;

let LIEEE_FLOAT_TO_REAL_EQ_0 = prove
 (`!x:(T,W)float.
     float_to_real x = &0 <=>
     float_Exponent x = word 0 /\ float_Significand x = word 0`,
  GEN_TAC THEN REWRITE_TAC[float_to_real_def] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_ENTIRE; real_div; REAL_INV_EQ_0; REAL_POW_EQ_0;
              REAL_OF_NUM_EQ; ARITH_EQ; VAL_EQ_0] THEN
  REWRITE_TAC[REAL_ARITH `~(--(&1) = &0)`; GSYM real_div] THEN
  MP_TAC(ISPEC `float_Significand (x:(T,W)float)` LIEEE_SIG_POS) THEN
  REAL_ARITH_TAC);;

let float_is_zero_to_real = prove
 (`!x:(T,W)float. float_is_zero x <=> float_to_real x = &0`,
  REWRITE_TAC[float_is_zero; LIEEE_FLOAT_TO_REAL_EQ_0]);;

let float_to_real_EQ0 = prove
 (`!f:(T,W)float.
     float_to_real f = &0 <=>
     f = float_plus_zero(:T#W) \/ f = float_minus_zero(:T#W)`,
  GEN_TAC THEN REWRITE_TAC[LIEEE_FLOAT_TO_REAL_EQ_0] THEN
  REWRITE_TAC[float_component_equality; float_components] THEN
  MP_TAC(ISPEC `float_Sign (f:(T,W)float)` LIEEEAUX_WORD1_CASES) THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC[LIEEEAUX_WORD_1_NE_0; GSYM LIEEEAUX_WORD_1_NE_0]);;

let float_is_finite = prove
 (`!x:(T,W)float.
     float_is_finite x <=>
     float_is_normal x \/ float_is_subnormal x \/ float_is_zero x`,
  GEN_TAC THEN
  REWRITE_TAC[float_is_finite_def; float_is_normal_def; float_is_subnormal_def;
              float_is_zero; float_value_def] THEN
  ASM_CASES_TAC `float_Exponent (x:(T,W)float) = word 0` THEN
  ASM_REWRITE_TAC[GSYM LIEEEAUX_WORD_UINT_MAX_NE_0; float_value_CASE] THENL
   [CONV_TAC TAUT;
    REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[float_value_CASE]]);;

let float_is_finite_Exponent = prove
 (`!f:(T,W)float. float_is_finite f <=> ~(float_Exponent f = word_UINT_MAX)`,
  GEN_TAC THEN REWRITE_TAC[float_is_finite_def; float_value_def] THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[float_value_CASE]);;

let float_cases_finite = prove
 (`!x:(T,W)float. float_is_nan x \/ float_is_infinite x \/ float_is_finite x`,
  GEN_TAC THEN
  REWRITE_TAC[float_is_nan_def; float_is_infinite_def; float_is_finite_def] THEN
  STRUCT_CASES_TAC(ISPEC `float_value (x:(T,W)float)` float_value_nchotomy) THEN
  REWRITE_TAC[float_value_CASE]);;

let float_distinct_finite = prove
 (`!x:(T,W)float.
     ~(float_is_nan x /\ float_is_infinite x) /\
     ~(float_is_nan x /\ float_is_finite x) /\
     ~(float_is_infinite x /\ float_is_finite x)`,
  GEN_TAC THEN
  REWRITE_TAC[float_is_nan_def; float_is_infinite_def; float_is_finite_def] THEN
  STRUCT_CASES_TAC(ISPEC `float_value (x:(T,W)float)` float_value_nchotomy) THEN
  REWRITE_TAC[float_value_CASE]);;

let float_cases = prove
 (`!x:(T,W)float.
     float_is_nan x \/ float_is_infinite x \/ float_is_normal x \/
     float_is_subnormal x \/ float_is_zero x`,
  MESON_TAC[float_cases_finite; float_is_finite]);;

let float_is_distinct = prove
 (`!x:(T,W)float.
     ~(float_is_nan x /\ float_is_infinite x) /\
     ~(float_is_nan x /\ float_is_normal x) /\
     ~(float_is_nan x /\ float_is_subnormal x) /\
     ~(float_is_nan x /\ float_is_zero x) /\
     ~(float_is_infinite x /\ float_is_normal x) /\
     ~(float_is_infinite x /\ float_is_subnormal x) /\
     ~(float_is_infinite x /\ float_is_zero x) /\
     ~(float_is_normal x /\ float_is_subnormal x) /\
     ~(float_is_normal x /\ float_is_zero x) /\
     ~(float_is_subnormal x /\ float_is_zero x)`,
  GEN_TAC THEN
  MP_TAC(ISPEC `x:(T,W)float` float_distinct_finite) THEN
  MP_TAC(ISPEC `x:(T,W)float` float_is_finite) THEN
  REWRITE_TAC[float_is_normal_def; float_is_subnormal_def; float_is_zero] THEN
  CONV_TAC TAUT);;

let float_infinities = prove
 (`!x:(T,W)float.
     float_is_infinite x <=>
     x = float_plus_infinity(:T#W) \/ x = float_minus_infinity(:T#W)`,
  GEN_TAC THEN
  REWRITE_TAC[float_is_infinite_def; float_value_def;
              float_component_equality; float_components] THEN
  MP_TAC(ISPEC `float_Sign (x:(T,W)float)` LIEEEAUX_WORD1_CASES) THEN
  REPEAT COND_CASES_TAC THEN
  ASM_REWRITE_TAC[float_value_CASE] THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC[LIEEEAUX_WORD_1_NE_0; GSYM LIEEEAUX_WORD_1_NE_0]);;

let float_infinities_distinct = prove
 (`!x:(T,W)float.
     ~(x = float_plus_infinity(:T#W) /\ x = float_minus_infinity(:T#W))`,
  MESON_TAC[float_distinct]);;

let NMUL_EQ_2 = prove
 (`!m n. m * n = 2 <=> m = 1 /\ n = 2 \/ m = 2 /\ n = 1`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [ALL_TAC; STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC] THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[MULT_CLAUSES; ARITH_EQ] THEN
  MP_TAC(ARITH_RULE `m = 0 \/ m = 1 \/ m = 2 \/ 3 <= m`) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN TRY ARITH_TAC THEN
  MP_TAC(SPECL [`3`; `m:num`; `n:num`] LE_MULT_RCANCEL) THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let LIEEE_INTEGER_NEG = prove
 (`!x. integer(--x) <=> integer x`,
  REWRITE_TAC[integer; REAL_ABS_NEG]);;

let LIEEE_INTEGER_TWO_DIV_POW = prove
 (`!k. integer (&2 / &2 pow k) <=> k <= 1`,
  GEN_TAC THEN ASM_CASES_TAC `k <= 1` THEN ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o
      MATCH_MP (ARITH_RULE `k <= 1 ==> k = 0 \/ k = 1`)) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[integer] THEN
    MESON_TAC[REAL_ABS_NUM];
    ALL_TAC] THEN
  REWRITE_TAC[integer] THEN
  SUBGOAL_THEN `&0 < &2 / &2 pow k /\ &2 / &2 pow k < &1` MP_TAC THENL
   [SIMP_TAC[REAL_LT_DIV; REAL_LT_POW2; REAL_ARITH `&0 < &2`] THEN
    SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LT_POW2; REAL_MUL_LID] THEN
    REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_LT] THEN
    MP_TAC(ISPECL [`2`; `2`; `k:num`] LE_EXP) THEN
    ASM_REWRITE_TAC[ARITH_RULE `2 <= k <=> ~(k <= 1)`] THEN ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP (REAL_ARITH
    `&0 < x /\ x < &1 ==> abs x = x`) th] THEN MP_TAC th) THEN
  STRIP_TAC THEN REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `n:num` THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_OF_NUM_LT]) THEN ASM_ARITH_TAC);;

let min_properties = prove
 (`~float_is_zero (float_plus_min(:T#W)) /\
   float_is_finite (float_plus_min(:T#W)) /\
   (float_is_integral (float_plus_min(:T#W)) <=>
    dimindex(:W) = 1 /\ dimindex(:T) = 1) /\
   ~float_is_nan (float_plus_min(:T#W)) /\
   ~float_is_normal (float_plus_min(:T#W)) /\
   float_is_subnormal (float_plus_min(:T#W)) /\
   ~float_is_infinite (float_plus_min(:T#W)) /\
   ~float_is_zero (float_minus_min(:T#W)) /\
   float_is_finite (float_minus_min(:T#W)) /\
   (float_is_integral (float_minus_min(:T#W)) <=>
    dimindex(:W) = 1 /\ dimindex(:T) = 1) /\
   ~float_is_nan (float_minus_min(:T#W)) /\
   ~float_is_normal (float_minus_min(:T#W)) /\
   float_is_subnormal (float_minus_min(:T#W)) /\
   ~float_is_infinite (float_minus_min(:T#W))`,
  REWRITE_TAC[float_is_zero; float_is_finite_Exponent; float_is_normal_def;
              float_is_subnormal_def; float_components;
              LIEEEAUX_WORD_1_NE_0; GSYM LIEEEAUX_WORD_UINT_MAX_NE_0] THEN
  REWRITE_TAC[float_is_nan_def; float_is_infinite_def; float_is_integral_def;
              float_values; float_value_CASE] THEN
  REWRITE_TAC[REAL_ARITH `-- &2 / x = --(&2 / x)`; LIEEE_INTEGER_NEG;
              LIEEE_INTEGER_TWO_DIV_POW] THEN
  MP_TAC(ISPEC `(:W)` DIMINDEX_GE_1) THEN MP_TAC(ISPEC `(:T)` DIMINDEX_GE_1) THEN
  MP_TAC(ISPECL [`2`; `dimindex(:W) - 1`] EXP_EQ_1) THEN
  MP_TAC(ISPECL [`2`; `dimindex(:W) - 1`] EXP_EQ_0) THEN
  ARITH_TAC);;

let top_properties = prove
 (`~float_is_zero (float_top(:T#W)) /\
   float_is_finite (float_top(:T#W)) /\
   ~float_is_nan (float_top(:T#W)) /\
   (float_is_normal (float_top(:T#W)) <=> ~(dimindex(:W) = 1)) /\
   (float_is_subnormal (float_top(:T#W)) <=> dimindex(:W) = 1) /\
   ~float_is_infinite (float_top(:T#W))`,
  REWRITE_TAC[float_is_zero; float_is_finite_Exponent; float_is_normal_def;
              float_is_subnormal_def; float_components;
              LIEEEAUX_WORD_SUB_1_NE; LIEEEAUX_WORD_UINT_MAX_NE_0;
              LIEEEAUX_WORD_UINT_MAX_SUB_1_EQ_0] THEN
  REWRITE_TAC[float_is_nan_def; float_is_infinite_def; float_value_def;
              float_components; LIEEEAUX_WORD_SUB_1_NE; float_value_CASE]);;

let bottom_properties = prove
 (`~float_is_zero (float_bottom(:T#W)) /\
   float_is_finite (float_bottom(:T#W)) /\
   ~float_is_nan (float_bottom(:T#W)) /\
   (float_is_normal (float_bottom(:T#W)) <=> ~(dimindex(:W) = 1)) /\
   (float_is_subnormal (float_bottom(:T#W)) <=> dimindex(:W) = 1) /\
   ~float_is_infinite (float_bottom(:T#W))`,
  REWRITE_TAC[float_is_zero; float_is_finite_Exponent; float_is_normal_def;
              float_is_subnormal_def; float_components;
              LIEEEAUX_WORD_SUB_1_NE; LIEEEAUX_WORD_UINT_MAX_NE_0;
              LIEEEAUX_WORD_UINT_MAX_SUB_1_EQ_0] THEN
  REWRITE_TAC[float_is_nan_def; float_is_infinite_def; float_value_def;
              float_components; LIEEEAUX_WORD_SUB_1_NE; float_value_CASE]);;

let float_to_real_negate = prove
 (`!x:(T,W)float. float_to_real (float_negate x) = --float_to_real x`,
  GEN_TAC THEN REWRITE_TAC[float_to_real_def; float_components] THEN
  MP_TAC(ISPEC `float_Sign (x:(T,W)float)` LIEEEAUX_WORD1_CASES) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV THEN
  REWRITE_TAC[VAL_WORD_0; VAL_WORD_1] THEN
  COND_CASES_TAC THEN REAL_ARITH_TAC);;

let float_negate_negate = prove
 (`!x:(T,W)float. float_negate (float_negate x) = x`,
  REWRITE_TAC[float_component_equality; float_components; WORD_NOT_NOT]);;

let float_negate_11 = prove
 (`!f1 f2:(T,W)float. float_negate f1 = float_negate f2 <=> f1 = f2`,
  MESON_TAC[float_negate_negate]);;

let float_negate = prove
 (`!a:(T,W)float r.
     float_value (float_negate a) = Float r <=> float_value a = Float (--r)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[float_value_def; float_components; float_to_real_negate] THEN
  REPEAT(COND_CASES_TAC THEN
         ASM_REWRITE_TAC[float_value_distinct; GSYM float_value_distinct;
                         float_value_11]) THEN
  REAL_ARITH_TAC);;

let float_is_finite_float_negate = prove
 (`!f:(T,W)float. float_is_finite (float_negate f) <=> float_is_finite f`,
  REWRITE_TAC[float_is_finite_Exponent; float_components]);;

let float_is_zero_float_value_EQ0 = prove
 (`!f:(T,W)float. float_is_zero f <=> float_value f = Float (&0)`,
  GEN_TAC THEN REWRITE_TAC[float_is_zero_def] THEN
  STRUCT_CASES_TAC(ISPEC `float_value (f:(T,W)float)` float_value_nchotomy) THEN
  REWRITE_TAC[float_value_CASE; float_value_distinct; float_value_11]);;

let float_is_zero_float_is_finite = prove
 (`!f:(T,W)float. float_is_zero f ==> float_is_finite f`,
  REWRITE_TAC[float_is_zero_float_value_EQ0; float_is_finite_thm] THEN
  MESON_TAC[]);;

let float_is_zero_float_negate = prove
 (`!f:(T,W)float. float_is_zero (float_negate f) <=> float_is_zero f`,
  REWRITE_TAC[float_is_zero; float_components]);;

let float_to_real_float_abs = prove
 (`!f:(T,W)float. float_to_real (float_abs f) = abs (float_to_real f)`,
  GEN_TAC THEN
  SUBGOAL_THEN `&0 <= &2 / &2 pow (2 EXP (dimindex(:W) - 1) - 1) /\
                &0 <= &2 pow val(float_Exponent (f:(T,W)float)) /
                      &2 pow (2 EXP (dimindex(:W) - 1) - 1)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_DIV THEN
    SIMP_TAC[REAL_POW_LE; REAL_ARITH `&0 <= &2`];
    ALL_TAC] THEN
  MP_TAC(ISPEC `float_Significand (f:(T,W)float)` LIEEE_SIG_POS) THEN
  REWRITE_TAC[float_to_real_def; float_abs_def; float_accfupds; K_THM;
              VAL_WORD_0; real_pow; REAL_MUL_LID] THEN
  DISCH_TAC THEN
  MP_TAC(ISPEC `float_Sign (f:(T,W)float)` LIEEEAUX_WORD1_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN
  REWRITE_TAC[VAL_WORD_0; VAL_WORD_1; REAL_POW_1; real_pow] THEN
  COND_CASES_TAC THEN
  REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NEG; REAL_ABS_NUM] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`;
               REAL_ARITH `&0 <= x ==> abs(&1 + x) = &1 + x`] THEN
  REAL_ARITH_TAC);;

let float_is_finite_float_value = prove
 (`!f:(T,W)float. float_is_finite f ==> float_value f = Float (float_to_real f)`,
  REWRITE_TAC[float_is_finite_Exponent; float_value_def] THEN MESON_TAC[]);;

let sign_float_abs = prove
 (`!f:(T,W)float. --(&1) pow val (float_Sign (float_abs f)) = &1`,
  REWRITE_TAC[float_abs_def; float_accfupds; K_THM; VAL_WORD_0; real_pow]);;

let float_abs_Exponent = prove
 (`!f:(T,W)float. float_Exponent (float_abs f) = float_Exponent f`,
  REWRITE_TAC[float_abs_def; float_accfupds]);;

let float_abs_Significand = prove
 (`!f:(T,W)float. float_Significand (float_abs f) = float_Significand f`,
  REWRITE_TAC[float_abs_def; float_accfupds]);;

let float_is_finite_float_abs = prove
 (`!f:(T,W)float. float_is_finite (float_abs f) <=> float_is_finite f`,
  REWRITE_TAC[float_is_finite_Exponent; float_abs_Exponent]);;

(* closest floats                                                            *)

let FINITE_floatsets = prove
 (`!s:(T,W)float->bool. FINITE s`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `IMAGE (\p:1 word#W word#T word.
                       float_REC (FST p) (FST(SND p)) (SND(SND p)))
                    (:1 word#W word#T word)` THEN
  SIMP_TAC[FINITE_IMAGE; FINITE_CROSS_UNIV; LIEEEAUX_WORD_FINITE] THEN
  REWRITE_TAC[SUBSET; IN_IMAGE; IN_UNIV; EXISTS_PAIR_THM] THEN
  X_GEN_TAC `x:(T,W)float` THEN DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC [`float_Sign (x:(T,W)float)`;
    `float_Exponent (x:(T,W)float)`; `float_Significand (x:(T,W)float)`] THEN
  REWRITE_TAC[float_component_equality; float_accessors]);;

let is_closest_exists = prove
 (`!s:(T,W)float->bool r. ~(s = {}) ==> ?a. is_closest s r a`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[is_closest_def] THEN
  MP_TAC(ISPEC `IMAGE (\b:(T,W)float. abs(float_to_real b - r)) s`
               INF_FINITE_LEMMA) THEN
  ASM_SIMP_TAC[FINITE_IMAGE; FINITE_floatsets; IMAGE_EQ_EMPTY] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; EXISTS_IN_IMAGE] THEN MESON_TAC[]);;

let is_closestP_finite_float_exists = prove
 (`!P r. ?a:(T,W)float.
     is_closest float_is_finite r a /\
     !b. is_closest float_is_finite r b /\ P b ==> P a`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`float_is_finite:(T,W)float->bool`; `r:real`]
                is_closest_exists) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    EXISTS_TAC `float_plus_zero(:T#W)` THEN
    REWRITE_TAC[IN; zeroes_are_finite_floats];
    MESON_TAC[]]);;

let is_closest_float_is_finite_0 = prove
 (`!f:(T,W)float.
     is_closest float_is_finite (&0) f <=>
     f = float_plus_zero(:T#W) \/ f = float_minus_zero(:T#W)`,
  GEN_TAC THEN REWRITE_TAC[is_closest_def; IN] THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o SPEC `float_plus_zero(:T#W)` o CONJUNCT2) THEN
    REWRITE_TAC[zeroes_are_finite_floats; zero_to_real;
                GSYM float_to_real_EQ0] THEN
    REAL_ARITH_TAC;
    STRIP_TAC THEN
    ASM_REWRITE_TAC[zeroes_are_finite_floats; zero_to_real] THEN
    REAL_ARITH_TAC]);;

(* ulp, largest and threshold                                                *)

let ULP_positive = prove
 (`!e:W word s:T->bool.
     &0 < ULP (e,s) /\ &0 <= ULP (e,s) /\ ~(ULP (e,s) < &0) /\
     ~(ULP (e,s) <= &0)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `&0 < ULP (e:W word,s:T->bool)` MP_TAC THENL
   [REWRITE_TAC[ULP_DEF] THEN MATCH_MP_TAC REAL_LT_DIV THEN
    REWRITE_TAC[REAL_LT_POW2];
    REAL_ARITH_TAC]);;

let ULP_nonzero = prove
 (`!e:W word. ~(ULP (e,(:T)) = &0)`,
  MESON_TAC[ULP_positive; REAL_LT_REFL]);;

let ulp_positive = prove
 (`&0 < ulp(:T#W) /\ &0 <= ulp(:T#W) /\ ~(ulp(:T#W) < &0) /\
   ~(ulp(:T#W) <= &0)`,
  REWRITE_TAC[ulp_def; ULP_positive]);;

let ulp_nonzero = prove
 (`~(ulp(:T#W) = &0)`,
  REWRITE_TAC[ulp_def; ULP_nonzero]);;

let largest_is_positive = prove
 (`&0 <= largest(:T#W)`,
  REWRITE_TAC[largest_def] THEN MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN SIMP_TAC[REAL_POW_LE; REAL_POS];
    MATCH_MP_TAC(REAL_ARITH `x <= &1 ==> &0 <= &2 - x`) THEN
    MATCH_MP_TAC REAL_INV_LE_1 THEN
    MATCH_MP_TAC REAL_POW_LE_1 THEN REAL_ARITH_TAC]);;

let threshold_is_positive = prove
 (`&0 < threshold(:T#W)`,
  REWRITE_TAC[threshold_def] THEN MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN REWRITE_TAC[REAL_LT_POW2];
    MATCH_MP_TAC(REAL_ARITH `x <= &1 ==> &0 < &2 - x`) THEN
    MATCH_MP_TAC REAL_INV_LE_1 THEN
    MATCH_MP_TAC REAL_POW_LE_1 THEN REAL_ARITH_TAC]);;

(* rounding beyond the largest float or the threshold                       *)

let LIEEE_ROUND_TAC =
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC threshold_is_positive THEN MP_TAC largest_is_positive THEN
  REPEAT DISCH_TAC THEN
  REWRITE_TAC[round_def; rounding_CASE; LET_DEF; LET_END_DEF] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  ASM_REAL_ARITH_TAC;;

let round_roundTiesToEven_plus_infinity = prove
 (`!y:(T,W)float x.
     threshold(:T#W) <= x
     ==> round roundTiesToEven x = float_plus_infinity(:T#W)`,
  LIEEE_ROUND_TAC);;

let round_roundTiesToEven_minus_infinity = prove
 (`!y:(T,W)float x.
     x <= --threshold(:T#W)
     ==> round roundTiesToEven x = float_minus_infinity(:T#W)`,
  LIEEE_ROUND_TAC);;

let round_roundTowardZero_top = prove
 (`!y:(T,W)float x.
     largest(:T#W) < x ==> round roundTowardZero x = float_top(:T#W)`,
  LIEEE_ROUND_TAC);;

let round_roundTowardZero_bottom = prove
 (`!y:(T,W)float x.
     x < --largest(:T#W) ==> round roundTowardZero x = float_bottom(:T#W)`,
  LIEEE_ROUND_TAC);;

let round_roundTowardPositive_plus_infinity = prove
 (`!y:(T,W)float x.
     largest(:T#W) < x
     ==> round roundTowardPositive x = float_plus_infinity(:T#W)`,
  LIEEE_ROUND_TAC);;

let round_roundTowardPositive_bottom = prove
 (`!y:(T,W)float x.
     x < --largest(:T#W) ==> round roundTowardPositive x = float_bottom(:T#W)`,
  LIEEE_ROUND_TAC);;

let round_roundTowardNegative_top = prove
 (`!y:(T,W)float x.
     largest(:T#W) < x ==> round roundTowardNegative x = float_top(:T#W)`,
  LIEEE_ROUND_TAC);;

let round_roundTowardNegative_minus_infinity = prove
 (`!y:(T,W)float x.
     x < --largest(:T#W)
     ==> round roundTowardNegative x = float_minus_infinity(:T#W)`,
  LIEEE_ROUND_TAC);;

let LIEEE_FLOAT_ROUND_TAC thl =
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[float_round_def; LET_DEF; LET_END_DEF] THEN
  ASM_SIMP_TAC(thl @ [top_properties; bottom_properties; infinity_properties]);;

let float_round_roundTowardZero_top = prove
 (`!b y:(T,W)float x.
     largest(:T#W) < x ==> float_round roundTowardZero b x = float_top(:T#W)`,
  LIEEE_FLOAT_ROUND_TAC[round_roundTowardZero_top]);;

let float_round_roundTowardZero_bottom = prove
 (`!b y:(T,W)float x.
     x < --largest(:T#W)
     ==> float_round roundTowardZero b x = float_bottom(:T#W)`,
  LIEEE_FLOAT_ROUND_TAC[round_roundTowardZero_bottom]);;

let float_round_roundTowardPositive_plus_infinity = prove
 (`!b y:(T,W)float x.
     largest(:T#W) < x
     ==> float_round roundTowardPositive b x = float_plus_infinity(:T#W)`,
  LIEEE_FLOAT_ROUND_TAC[round_roundTowardPositive_plus_infinity]);;

let float_round_roundTowardPositive_bottom = prove
 (`!b y:(T,W)float x.
     x < --largest(:T#W)
     ==> float_round roundTowardPositive b x = float_bottom(:T#W)`,
  LIEEE_FLOAT_ROUND_TAC[round_roundTowardPositive_bottom]);;

let float_round_roundTowardNegative_top = prove
 (`!b y:(T,W)float x.
     largest(:T#W) < x
     ==> float_round roundTowardNegative b x = float_top(:T#W)`,
  LIEEE_FLOAT_ROUND_TAC[round_roundTowardNegative_top]);;

let float_round_roundTowardNegative_minus_infinity = prove
 (`!b y:(T,W)float x.
     x < --largest(:T#W)
     ==> float_round roundTowardNegative b x = float_minus_infinity(:T#W)`,
  LIEEE_FLOAT_ROUND_TAC[round_roundTowardNegative_minus_infinity]);;

(* theorem support for evaluation                                            *)

let float_minus_zero = prove
 (`float_minus_zero(:T#W) = float_REC (word 1) (word 0) (word 0)`,
  REWRITE_TAC[float_component_equality; float_components; float_accessors]);;

let float_minus_infinity = prove
 (`float_minus_infinity(:T#W) = float_REC (word 1) word_UINT_MAX (word 0)`,
  REWRITE_TAC[float_component_equality; float_components; float_accessors]);;

let float_round_non_zero = prove
 (`!mode toneg r s e f.
     round mode r = float_REC s e f /\ (~(e = word 0) \/ ~(f = word 0))
     ==> float_round mode toneg r = (float_REC s e f:(T,W)float)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[float_round_def; LET_DEF; LET_END_DEF; float_is_zero;
                  float_accessors]);;

let float_round_plus_infinity = prove
 (`!mode toneg r.
     round mode r = float_plus_infinity(:T#W)
     ==> float_round mode toneg r = float_plus_infinity(:T#W)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[float_round_def; LET_DEF; LET_END_DEF; infinity_properties]);;

let float_round_minus_infinity = prove
 (`!mode toneg r.
     round mode r = float_minus_infinity(:T#W)
     ==> float_round mode toneg r = float_minus_infinity(:T#W)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[float_round_def; LET_DEF; LET_END_DEF; infinity_properties]);;

let float_round_top = prove
 (`!mode toneg r.
     round mode r = float_top(:T#W)
     ==> float_round mode toneg r = float_top(:T#W)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[float_round_def; LET_DEF; LET_END_DEF; top_properties]);;

let float_round_bottom = prove
 (`!mode toneg r.
     round mode r = float_bottom(:T#W)
     ==> float_round mode toneg r = float_bottom(:T#W)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[float_round_def; LET_DEF; LET_END_DEF; bottom_properties]);;

let float_to_real = prove
 (`!s e:W word f:T word.
     float_to_real (float_REC s e f) =
     let r = if e = word 0
             then &2 / &(2 EXP (2 EXP (dimindex(:W) - 1) - 1)) *
                  (&(val f) / &(2 EXP dimindex(:T)))
             else &(2 EXP val e) / &(2 EXP (2 EXP (dimindex(:W) - 1) - 1)) *
                  (&1 + &(val f) / &(2 EXP dimindex(:T))) in
     if s = word 1 then --r else r`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[float_to_real_def; float_accessors; LET_DEF; LET_END_DEF;
              GSYM REAL_OF_NUM_POW] THEN
  MP_TAC(ISPEC `s:1 word` LIEEEAUX_WORD1_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN
  REWRITE_TAC[VAL_WORD_0; VAL_WORD_1; LIEEEAUX_WORD_1_NE_0; real_pow;
              REAL_POW_1] THEN
  COND_CASES_TAC THEN REAL_ARITH_TAC);;

(* HOL4 states largest and threshold with dimword (:'t) = 2 EXP dimindex(:T) *)

let largest = prove
 (`largest(:T#W) =
     (&(2 EXP ((2 EXP dimindex(:W) - 1) - 1)) *
      (&2 - &1 / &(2 EXP dimindex(:T)))) /
     &(2 EXP (2 EXP (dimindex(:W) - 1) - 1))`,
  REWRITE_TAC[largest_def; GSYM REAL_OF_NUM_POW; real_div] THEN
  CONV_TAC REAL_RING);;

let threshold = prove
 (`threshold(:T#W) =
     (&(2 EXP ((2 EXP dimindex(:W) - 1) - 1)) *
      (&2 - &1 / &(2 * 2 EXP dimindex(:T)))) /
     &(2 EXP (2 EXP (dimindex(:W) - 1) - 1))`,
  REWRITE_TAC[threshold_def; GSYM REAL_OF_NUM_POW; GSYM REAL_OF_NUM_MUL;
              real_pow; real_div] THEN
  CONV_TAC REAL_RING);;

let largest_is_top = prove
 (`1 < dimindex(:W) ==> largest(:T#W) = float_to_real (float_top(:T#W))`,
  DISCH_TAC THEN
  SUBGOAL_THEN `~(word_sub word_UINT_MAX (word 1) = (word 0:W word))`
  ASSUME_TAC THENL
   [REWRITE_TAC[LIEEEAUX_WORD_UINT_MAX_SUB_1_EQ_0] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `val(word_sub word_UINT_MAX (word 1):W word) =
                (2 EXP dimindex(:W) - 1) - 1`
  ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD_SUB_CASES; VAL_WORD_UINT_MAX; VAL_WORD_1] THEN
    MP_TAC(ISPECL [`2`; `1`; `dimindex(:W)`] LE_EXP) THEN
    MP_TAC(ISPEC `(:W)` DIMINDEX_GE_1) THEN
    REWRITE_TAC[ARITH_RULE `~(2 = 0)`] THEN
    ASM_SIMP_TAC[ARITH_RULE `1 <= n ==> 1 <= n`; EXP_1] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[largest_def; float_to_real_def; float_components;
                  VAL_WORD_0; real_pow; REAL_MUL_LID; VAL_WORD_UINT_MAX] THEN
  SUBGOAL_THEN `&(2 EXP dimindex(:T) - 1) = &2 pow dimindex(:T) - &1`
  SUBST1_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_POW] THEN
    MATCH_MP_TAC(GSYM REAL_OF_NUM_SUB) THEN
    REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; EXP_EQ_0; ARITH_EQ];
    ALL_TAC] THEN
  AP_TERM_TAC THEN
  SUBGOAL_THEN `~(&2 pow dimindex(:T) = &0)` MP_TAC THENL
   [REWRITE_TAC[REAL_POW_EQ_0] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC REAL_FIELD);;

let largest_lt_threshold = prove
 (`largest(:T#W) < threshold(:T#W)`,
  REWRITE_TAC[largest_def; threshold_def] THEN
  MATCH_MP_TAC REAL_LT_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN REWRITE_TAC[REAL_LT_POW2];
    MATCH_MP_TAC(REAL_ARITH `y < x ==> &2 - x < &2 - y`) THEN
    MATCH_MP_TAC REAL_LT_INV2 THEN REWRITE_TAC[REAL_LT_POW2] THEN
    MATCH_MP_TAC REAL_POW_MONO_LT THEN ARITH_TAC]);;

let float_sets = prove
 (`float_is_zero = {float_minus_zero(:T#W), float_plus_zero(:T#W)} /\
   float_is_infinite = {float_minus_infinity(:T#W), float_plus_infinity(:T#W)}`,
  REWRITE_TAC[EXTENSION; IN_INSERT; NOT_IN_EMPTY] THEN REWRITE_TAC[IN] THEN
  REWRITE_TAC[float_is_zero_to_real; float_to_real_EQ0; float_infinities] THEN
  MESON_TAC[]);;

(* HOL4 writes -1w for the all-ones exponent                                 *)

let float_tests = prove
 (`(!s e f.
      float_is_nan (float_REC s e f:(T,W)float) <=>
      e = word_neg (word 1) /\ ~(f = word 0)) /\
   (!s e f.
      float_is_signalling (float_REC s e f:(T,W)float) <=>
      e = word_neg (word 1) /\ ~bit (dimindex(:T) - 1) f /\ ~(f = word 0)) /\
   (!s e f.
      float_is_infinite (float_REC s e f:(T,W)float) <=>
      e = word_neg (word 1) /\ f = word 0) /\
   (!s e f.
      float_is_normal (float_REC s e f:(T,W)float) <=>
      ~(e = word 0) /\ ~(e = word_neg (word 1))) /\
   (!s e f.
      float_is_subnormal (float_REC s e f:(T,W)float) <=>
      e = word 0 /\ ~(f = word 0)) /\
   (!s e f.
      float_is_zero (float_REC s e f:(T,W)float) <=>
      e = word 0 /\ f = word 0) /\
   (!s e f.
      float_is_finite (float_REC s e f:(T,W)float) <=>
      ~(e = word_neg (word 1)))`,
  REWRITE_TAC[LIEEEAUX_WORD_NEG_1] THEN
  REWRITE_TAC[float_is_zero; float_is_finite_Exponent; float_is_normal_def;
              float_is_subnormal_def; float_accessors] THEN
  REWRITE_TAC[float_is_signalling_def; float_is_nan_def;
              float_is_infinite_def; float_value_def; float_accessors] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[float_value_CASE]) THEN
  CONV_TAC TAUT);;

let float_infinity_negate_abs = prove
 (`float_negate (float_plus_infinity(:T#W)) = float_minus_infinity(:T#W) /\
   float_negate (float_minus_infinity(:T#W)) = float_plus_infinity(:T#W) /\
   float_abs (float_plus_infinity(:T#W)) = float_plus_infinity(:T#W) /\
   float_abs (float_minus_infinity(:T#W)) = float_plus_infinity(:T#W)`,
  REWRITE_TAC[float_component_equality; float_components; float_abs_def;
              float_accfupds; K_THM; WORD_NOT_NOT] THEN
  CONV_TAC WORD_REDUCE_CONV);;

let float_round_to_integral_compute = prove
 (`(!m. float_round_to_integral m (float_minus_infinity(:T#W)) =
        float_minus_infinity(:T#W)) /\
   (!m. float_round_to_integral m (float_plus_infinity(:T#W)) =
        float_plus_infinity(:T#W)) /\
   (!m fp_op:(T,W)fp_op.
        float_round_to_integral m (float_some_qnan fp_op) =
        float_some_qnan fp_op)`,
  REWRITE_TAC[float_round_to_integral_def; float_values; float_value_CASE]);;

(* add, sub, mul and div on NaNs, infinities and finite values               *)

let LIEEE_CHECK_NONSIG = prove
 (`!x:(T,W)float fp_op.
     check_for_signalling [float_some_qnan fp_op; x] =
     check_for_signalling [x] /\
     check_for_signalling [x; float_some_qnan fp_op] =
     check_for_signalling [x]`,
  REWRITE_TAC[check_for_signalling_def; EX; some_nan_properties]);;

let LIEEE_CHECK_NONNAN = prove
 (`!x:(T,W)float. ~(float_value x = NaN)
     ==> check_for_signalling [x] = clear_flags`,
  REWRITE_TAC[check_for_signalling_def; EX; float_is_signalling_def;
              float_is_nan_def] THEN
  GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `float_value (x:(T,W)float)` float_value_nchotomy) THEN
  REWRITE_TAC[float_value_CASE; float_value_distinct] THEN
  REWRITE_TAC[clear_flags_def; flags_fn_updates; K_THM]);;

let LIEEE_COMPUTE_TAC def =
  REWRITE_TAC[def; float_values; float_value_CASE; float_components;
              LIEEE_CHECK_NONSIG; LIEEEAUX_WORD_1_NE_0;
              GSYM LIEEEAUX_WORD_1_NE_0] THEN
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `float_value (x:(T,W)float) = NaN` THEN
  ASM_REWRITE_TAC[float_value_CASE; LIEEE_CHECK_NONSIG] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP LIEEE_CHECK_NONNAN) THEN
  REWRITE_TAC[check_for_signalling_def; EX; some_nan_properties] THEN
  REWRITE_TAC[clear_flags_def; flags_fn_updates; K_THM] THEN
  STRUCT_CASES_TAC(ISPEC `float_value (x:(T,W)float)` float_value_nchotomy) THEN
  REWRITE_TAC[float_value_CASE];;

let LIEEE_NAN_TAC def =
  REPEAT GEN_TAC THEN
  REWRITE_TAC[def; check_for_signalling_def; EX; float_is_signalling_def;
              float_is_nan_def] THEN
  STRUCT_CASES_TAC(ISPEC `float_value (x:(T,W)float)` float_value_nchotomy) THEN
  STRUCT_CASES_TAC(ISPEC `float_value (y:(T,W)float)` float_value_nchotomy) THEN
  REWRITE_TAC[float_value_CASE; float_value_distinct; GSYM float_value_distinct];;

let LIEEE_INF_TAC def =
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[def; float_values; float_value_CASE; float_components] THEN
  MP_TAC(ISPEC `float_Sign (x:(T,W)float)` LIEEEAUX_WORD1_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN
  REWRITE_TAC[LIEEEAUX_WORD_1_NE_0; GSYM LIEEEAUX_WORD_1_NE_0];;

let float_add_compute = prove
 (`(!mode x fp_op:(T,W)fp_op.
      float_add mode (float_some_qnan fp_op) x =
      (check_for_signalling [x],
       float_some_qnan (binary_ieee_FP_Add mode (float_some_qnan fp_op) x))) /\
   (!mode x fp_op:(T,W)fp_op.
      float_add mode x (float_some_qnan fp_op) =
      (check_for_signalling [x],
       float_some_qnan (binary_ieee_FP_Add mode x (float_some_qnan fp_op)))) /\
   (!mode.
      float_add mode (float_minus_infinity(:T#W)) (float_minus_infinity(:T#W)) =
      (clear_flags, float_minus_infinity(:T#W))) /\
   (!mode.
      float_add mode (float_minus_infinity(:T#W)) (float_plus_infinity(:T#W)) =
      (invalidop_flags,
       float_some_qnan (binary_ieee_FP_Add mode (float_minus_infinity(:T#W))
                                                (float_plus_infinity(:T#W))))) /\
   (!mode.
      float_add mode (float_plus_infinity(:T#W)) (float_plus_infinity(:T#W)) =
      (clear_flags, float_plus_infinity(:T#W))) /\
   (!mode.
      float_add mode (float_plus_infinity(:T#W)) (float_minus_infinity(:T#W)) =
      (invalidop_flags,
       float_some_qnan (binary_ieee_FP_Add mode (float_plus_infinity(:T#W))
                                                (float_minus_infinity(:T#W)))))`,
  LIEEE_COMPUTE_TAC float_add_def);;

let float_add_nan = prove
 (`!mode x y:(T,W)float.
     float_value x = NaN \/ float_value y = NaN
     ==> float_add mode x y =
         (check_for_signalling [x; y],
          float_some_qnan (binary_ieee_FP_Add mode x y))`,
  LIEEE_NAN_TAC float_add_def);;

let float_add_finite = prove
 (`!mode x y:(T,W)float r1 r2.
     float_value x = Float r1 /\ float_value y = Float r2
     ==> float_add mode x y =
         float_round_with_flags mode
           (if r1 = &0 /\ r2 = &0 /\ float_Sign x = float_Sign y
            then float_Sign x = word 1
            else mode = roundTowardNegative) (r1 + r2)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[float_add_def; float_value_CASE]);;

let float_add_finite_plus_infinity = prove
 (`!mode x:(T,W)float r.
     float_value x = Float r
     ==> float_add mode x (float_plus_infinity(:T#W)) =
         (clear_flags, float_plus_infinity(:T#W))`,
  LIEEE_INF_TAC float_add_def);;

let float_add_plus_infinity_finite = prove
 (`!mode x:(T,W)float r.
     float_value x = Float r
     ==> float_add mode (float_plus_infinity(:T#W)) x =
         (clear_flags, float_plus_infinity(:T#W))`,
  LIEEE_INF_TAC float_add_def);;

let float_add_finite_minus_infinity = prove
 (`!mode x:(T,W)float r.
     float_value x = Float r
     ==> float_add mode x (float_minus_infinity(:T#W)) =
         (clear_flags, float_minus_infinity(:T#W))`,
  LIEEE_INF_TAC float_add_def);;

let float_add_minus_infinity_finite = prove
 (`!mode x:(T,W)float r.
     float_value x = Float r
     ==> float_add mode (float_minus_infinity(:T#W)) x =
         (clear_flags, float_minus_infinity(:T#W))`,
  LIEEE_INF_TAC float_add_def);;

let float_sub_compute = prove
 (`(!mode x fp_op:(T,W)fp_op.
      float_sub mode (float_some_qnan fp_op) x =
      (check_for_signalling [x],
       float_some_qnan (binary_ieee_FP_Sub mode (float_some_qnan fp_op) x))) /\
   (!mode x fp_op:(T,W)fp_op.
      float_sub mode x (float_some_qnan fp_op) =
      (check_for_signalling [x],
       float_some_qnan (binary_ieee_FP_Sub mode x (float_some_qnan fp_op)))) /\
   (!mode.
      float_sub mode (float_minus_infinity(:T#W)) (float_minus_infinity(:T#W)) =
      (invalidop_flags,
       float_some_qnan (binary_ieee_FP_Sub mode (float_minus_infinity(:T#W))
                                                (float_minus_infinity(:T#W))))) /\
   (!mode.
      float_sub mode (float_minus_infinity(:T#W)) (float_plus_infinity(:T#W)) =
      (clear_flags, float_minus_infinity(:T#W))) /\
   (!mode.
      float_sub mode (float_plus_infinity(:T#W)) (float_plus_infinity(:T#W)) =
      (invalidop_flags,
       float_some_qnan (binary_ieee_FP_Sub mode (float_plus_infinity(:T#W))
                                                (float_plus_infinity(:T#W))))) /\
   (!mode.
      float_sub mode (float_plus_infinity(:T#W)) (float_minus_infinity(:T#W)) =
      (clear_flags, float_plus_infinity(:T#W)))`,
  LIEEE_COMPUTE_TAC float_sub_def);;

let float_sub_nan = prove
 (`!mode x y:(T,W)float.
     float_value x = NaN \/ float_value y = NaN
     ==> float_sub mode x y =
         (check_for_signalling [x; y],
          float_some_qnan (binary_ieee_FP_Sub mode x y))`,
  LIEEE_NAN_TAC float_sub_def);;

let float_sub_finite = prove
 (`!mode x y:(T,W)float r1 r2.
     float_value x = Float r1 /\ float_value y = Float r2
     ==> float_sub mode x y =
         float_round_with_flags mode
           (if r1 = &0 /\ r2 = &0 /\ ~(float_Sign x = float_Sign y)
            then float_Sign x = word 1
            else mode = roundTowardNegative) (r1 - r2)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[float_sub_def; float_value_CASE]);;

let float_sub_finite_plus_infinity = prove
 (`!mode x:(T,W)float r.
     float_value x = Float r
     ==> float_sub mode x (float_plus_infinity(:T#W)) =
         (clear_flags, float_minus_infinity(:T#W))`,
  LIEEE_INF_TAC float_sub_def THEN REWRITE_TAC[float_minus_infinity_def]);;

let float_sub_plus_infinity_finite = prove
 (`!mode x:(T,W)float r.
     float_value x = Float r
     ==> float_sub mode (float_plus_infinity(:T#W)) x =
         (clear_flags, float_plus_infinity(:T#W))`,
  LIEEE_INF_TAC float_sub_def);;

let float_sub_finite_minus_infinity = prove
 (`!mode x:(T,W)float r.
     float_value x = Float r
     ==> float_sub mode x (float_minus_infinity(:T#W)) =
         (clear_flags, float_plus_infinity(:T#W))`,
  LIEEE_INF_TAC float_sub_def THEN
  REWRITE_TAC[float_minus_infinity_def; float_negate_negate]);;

let float_sub_minus_infinity_finite = prove
 (`!mode x:(T,W)float r.
     float_value x = Float r
     ==> float_sub mode (float_minus_infinity(:T#W)) x =
         (clear_flags, float_minus_infinity(:T#W))`,
  LIEEE_INF_TAC float_sub_def);;

let float_mul_compute = prove
 (`(!mode x fp_op:(T,W)fp_op.
      float_mul mode (float_some_qnan fp_op) x =
      (check_for_signalling [x],
       float_some_qnan (binary_ieee_FP_Mul mode (float_some_qnan fp_op) x))) /\
   (!mode x fp_op:(T,W)fp_op.
      float_mul mode x (float_some_qnan fp_op) =
      (check_for_signalling [x],
       float_some_qnan (binary_ieee_FP_Mul mode x (float_some_qnan fp_op)))) /\
   (!mode.
      float_mul mode (float_minus_infinity(:T#W)) (float_minus_infinity(:T#W)) =
      (clear_flags, float_plus_infinity(:T#W))) /\
   (!mode.
      float_mul mode (float_minus_infinity(:T#W)) (float_plus_infinity(:T#W)) =
      (clear_flags, float_minus_infinity(:T#W))) /\
   (!mode.
      float_mul mode (float_plus_infinity(:T#W)) (float_plus_infinity(:T#W)) =
      (clear_flags, float_plus_infinity(:T#W))) /\
   (!mode.
      float_mul mode (float_plus_infinity(:T#W)) (float_minus_infinity(:T#W)) =
      (clear_flags, float_minus_infinity(:T#W)))`,
  LIEEE_COMPUTE_TAC float_mul_def);;

let float_mul_nan = prove
 (`!mode x y:(T,W)float.
     float_value x = NaN \/ float_value y = NaN
     ==> float_mul mode x y =
         (check_for_signalling [x; y],
          float_some_qnan (binary_ieee_FP_Mul mode x y))`,
  LIEEE_NAN_TAC float_mul_def);;

let float_mul_finite = prove
 (`!mode x y:(T,W)float r1 r2.
     float_value x = Float r1 /\ float_value y = Float r2
     ==> float_mul mode x y =
         float_round_with_flags mode (~(float_Sign x = float_Sign y)) (r1 * r2)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[float_mul_def; float_value_CASE]);;

let float_mul_finite_plus_infinity = prove
 (`!mode x:(T,W)float r.
     float_value x = Float r
     ==> float_mul mode x (float_plus_infinity(:T#W)) =
         if r = &0 then
           (invalidop_flags,
            float_some_qnan
              (binary_ieee_FP_Mul mode x (float_plus_infinity(:T#W))))
         else (clear_flags,
               if float_Sign x = word 0 then float_plus_infinity(:T#W)
               else float_minus_infinity(:T#W))`,
  LIEEE_INF_TAC float_mul_def);;

let float_mul_plus_infinity_finite = prove
 (`!mode x:(T,W)float r.
     float_value x = Float r
     ==> float_mul mode (float_plus_infinity(:T#W)) x =
         if r = &0 then
           (invalidop_flags,
            float_some_qnan
              (binary_ieee_FP_Mul mode (float_plus_infinity(:T#W)) x))
         else (clear_flags,
               if float_Sign x = word 0 then float_plus_infinity(:T#W)
               else float_minus_infinity(:T#W))`,
  LIEEE_INF_TAC float_mul_def);;

let float_mul_finite_minus_infinity = prove
 (`!mode x:(T,W)float r.
     float_value x = Float r
     ==> float_mul mode x (float_minus_infinity(:T#W)) =
         if r = &0 then
           (invalidop_flags,
            float_some_qnan
              (binary_ieee_FP_Mul mode x (float_minus_infinity(:T#W))))
         else (clear_flags,
               if float_Sign x = word 0 then float_minus_infinity(:T#W)
               else float_plus_infinity(:T#W))`,
  LIEEE_INF_TAC float_mul_def);;

let float_mul_minus_infinity_finite = prove
 (`!mode x:(T,W)float r.
     float_value x = Float r
     ==> float_mul mode (float_minus_infinity(:T#W)) x =
         if r = &0 then
           (invalidop_flags,
            float_some_qnan
              (binary_ieee_FP_Mul mode (float_minus_infinity(:T#W)) x))
         else (clear_flags,
               if float_Sign x = word 0 then float_minus_infinity(:T#W)
               else float_plus_infinity(:T#W))`,
  LIEEE_INF_TAC float_mul_def);;

let float_div_compute = prove
 (`(!mode x fp_op:(T,W)fp_op.
      float_div mode (float_some_qnan fp_op) x =
      (check_for_signalling [x],
       float_some_qnan (binary_ieee_FP_Div mode (float_some_qnan fp_op) x))) /\
   (!mode x fp_op:(T,W)fp_op.
      float_div mode x (float_some_qnan fp_op) =
      (check_for_signalling [x],
       float_some_qnan (binary_ieee_FP_Div mode x (float_some_qnan fp_op)))) /\
   (!mode.
      float_div mode (float_minus_infinity(:T#W)) (float_minus_infinity(:T#W)) =
      (invalidop_flags,
       float_some_qnan (binary_ieee_FP_Div mode (float_minus_infinity(:T#W))
                                                (float_minus_infinity(:T#W))))) /\
   (!mode.
      float_div mode (float_minus_infinity(:T#W)) (float_plus_infinity(:T#W)) =
      (invalidop_flags,
       float_some_qnan (binary_ieee_FP_Div mode (float_minus_infinity(:T#W))
                                                (float_plus_infinity(:T#W))))) /\
   (!mode.
      float_div mode (float_plus_infinity(:T#W)) (float_plus_infinity(:T#W)) =
      (invalidop_flags,
       float_some_qnan (binary_ieee_FP_Div mode (float_plus_infinity(:T#W))
                                                (float_plus_infinity(:T#W))))) /\
   (!mode.
      float_div mode (float_plus_infinity(:T#W)) (float_minus_infinity(:T#W)) =
      (invalidop_flags,
       float_some_qnan (binary_ieee_FP_Div mode (float_plus_infinity(:T#W))
                                                (float_minus_infinity(:T#W)))))`,
  LIEEE_COMPUTE_TAC float_div_def);;

let float_div_nan = prove
 (`!mode x y:(T,W)float.
     float_value x = NaN \/ float_value y = NaN
     ==> float_div mode x y =
         (check_for_signalling [x; y],
          float_some_qnan (binary_ieee_FP_Div mode x y))`,
  LIEEE_NAN_TAC float_div_def);;

let float_div_finite = prove
 (`!mode x y:(T,W)float r1 r2.
     float_value x = Float r1 /\ float_value y = Float r2
     ==> float_div mode x y =
         if r2 = &0
         then if r1 = &0
              then (invalidop_flags,
                    float_some_qnan (binary_ieee_FP_Div mode x y))
              else (dividezero_flags,
                    if float_Sign x = float_Sign y
                    then float_plus_infinity(:T#W)
                    else float_minus_infinity(:T#W))
         else float_round_with_flags mode (~(float_Sign x = float_Sign y))
                (r1 / r2)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[float_div_def; float_value_CASE]);;

let float_div_finite_plus_infinity = prove
 (`!mode x:(T,W)float r.
     float_value x = Float r
     ==> float_div mode x (float_plus_infinity(:T#W)) =
         (clear_flags,
          if float_Sign x = word 0 then float_plus_zero(:T#W)
          else float_minus_zero(:T#W))`,
  LIEEE_INF_TAC float_div_def);;

let float_div_plus_infinity_finite = prove
 (`!mode x:(T,W)float r.
     float_value x = Float r
     ==> float_div mode (float_plus_infinity(:T#W)) x =
         (clear_flags,
          if float_Sign x = word 0 then float_plus_infinity(:T#W)
          else float_minus_infinity(:T#W))`,
  LIEEE_INF_TAC float_div_def);;

let float_div_finite_minus_infinity = prove
 (`!mode x:(T,W)float r.
     float_value x = Float r
     ==> float_div mode x (float_minus_infinity(:T#W)) =
         (clear_flags,
          if float_Sign x = word 0 then float_minus_zero(:T#W)
          else float_plus_zero(:T#W))`,
  LIEEE_INF_TAC float_div_def);;

let float_div_minus_infinity_finite = prove
 (`!mode x:(T,W)float r.
     float_value x = Float r
     ==> float_div mode (float_minus_infinity(:T#W)) x =
         (clear_flags,
          if float_Sign x = word 0 then float_minus_infinity(:T#W)
          else float_plus_infinity(:T#W))`,
  LIEEE_INF_TAC float_div_def);;

let float_is_nan_impl = prove
 (`!x:(T,W)float. float_is_nan x <=> ~float_equal x x`,
  GEN_TAC THEN
  REWRITE_TAC[float_is_nan_def; float_equal_def; float_compare_def] THEN
  STRUCT_CASES_TAC(ISPEC `float_value (x:(T,W)float)` float_value_nchotomy) THEN
  REWRITE_TAC[float_value_CASE; float_compare_distinct; REAL_LT_REFL]);;

let float_is_zero_impl = prove
 (`!x:(T,W)float. float_is_zero x <=> float_equal (float_plus_zero(:T#W)) x`,
  GEN_TAC THEN
  REWRITE_TAC[float_is_zero_def; float_equal_def; float_compare_def;
              float_values; float_value_CASE] THEN
  STRUCT_CASES_TAC(ISPEC `float_value (x:(T,W)float)` float_value_nchotomy) THEN
  REWRITE_TAC[float_value_CASE; float_compare_distinct;
              GSYM float_compare_distinct] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[float_compare_distinct;
              GSYM float_compare_distinct] THENL
   [ASM_REAL_ARITH_TAC;
    COND_CASES_TAC THEN
    ASM_REWRITE_TAC[float_compare_distinct; GSYM float_compare_distinct] THEN
    ASM_REAL_ARITH_TAC]);;

(* float_to_real is injective except on the two zeroes (HOL4 proves this    *)
(* through its ULP lemmas; here through the integer n with                  *)
(* abs (float_to_real x) = &n / 2 pow (bias + precision)).                   *)

let LIEEE_FLOAT_TO_REAL_N = prove
 (`!x:(T,W)float.
     float_to_real x =
     --(&1) pow val(float_Sign x) *
     &(if float_Exponent x = word 0 then 2 * val(float_Significand x)
       else 2 EXP val(float_Exponent x) *
            (2 EXP dimindex(:T) + val(float_Significand x))) /
     &2 pow ((2 EXP (dimindex(:W) - 1) - 1) + dimindex(:T))`,
  GEN_TAC THEN REWRITE_TAC[float_to_real_def] THEN
  SUBGOAL_THEN `~(&2 pow dimindex(:T) = &0) /\
                ~(&2 pow (2 EXP (dimindex(:W) - 1) - 1) = &0)`
  MP_TAC THENL [REWRITE_TAC[REAL_POW_EQ_0] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  COND_CASES_TAC THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW;
              GSYM REAL_OF_NUM_ADD; REAL_POW_ADD] THEN
  CONV_TAC REAL_FIELD);;

let LIEEE_N_INJ = prove
 (`!p e1 e2 m1 m2.
     m1 < 2 EXP p /\ m2 < 2 EXP p /\
     (if e1 = 0 then 2 * m1 else 2 EXP e1 * (2 EXP p + m1)) =
     (if e2 = 0 then 2 * m2 else 2 EXP e2 * (2 EXP p + m2))
     ==> e1 = e2 /\ m1 = m2`,
  SUBGOAL_THEN
   `!p e m1 m2. m1 < 2 EXP p /\ ~(e = 0) ==>
                ~(2 * m1 = 2 EXP e * (2 EXP p + m2))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`2`; `1`; `e:num`] LE_EXP) THEN
    ASM_REWRITE_TAC[ARITH_RULE `1 <= e <=> ~(e = 0)`; EXP_1; ARITH_EQ] THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`2`; `2 EXP e`; `2 EXP p + m2`] LE_MULT_RCANCEL) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!p e1 e2 m1 m2. m1 < 2 EXP p /\ e1 < e2 ==>
                    ~(2 EXP e1 * (2 EXP p + m1) = 2 EXP e2 * (2 EXP p + m2))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (is_eq o concl)) THEN
    FIRST_ASSUM(CHOOSE_THEN SUBST1_TAC o REWRITE_RULE[LT_EXISTS]) THEN
    REWRITE_TAC[EXP_ADD; GSYM MULT_ASSOC; EQ_MULT_LCANCEL; EXP_EQ_0;
                ARITH_EQ; EXP] THEN
    MP_TAC(ISPECL [`1`; `2 EXP d`; `2 EXP p + m2`] LE_MULT_RCANCEL) THEN
    REWRITE_TAC[MULT_CLAUSES] THEN
    REWRITE_TAC[ARITH_RULE `1 <= x <=> ~(x = 0)`; EXP_EQ_0; ARITH_EQ] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `e1 = 0` THEN ASM_CASES_TAC `e2 = 0` THEN
  ASM_REWRITE_TAC[] THENL
   [ARITH_TAC;
    ASM_MESON_TAC[];
    ASM_MESON_TAC[];
    STRIP_TAC THEN
    MP_TAC(ARITH_RULE `e1 < e2 \/ e2 < e1 \/ e1 = e2:num`) THEN
    STRIP_TAC THENL [ASM_MESON_TAC[]; ASM_MESON_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (is_eq o concl)) THEN
    REWRITE_TAC[EQ_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ] THEN ARITH_TAC]);;

let LIEEE_SIGN_MAG_EQ = prove
 (`!KK nx ny s1 s2:1 word.
     &0 < KK /\
     --(&1) pow val s1 * &nx / KK = --(&1) pow val s2 * &ny / KK /\
     ~(--(&1) pow val s1 * &nx / KK = &0)
     ==> s1 = s2 /\ nx = ny`,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_div] THEN
  ASM_CASES_TAC `&0 < KK` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < inv KK` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_INV]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &nx * inv KK /\ &0 <= &ny * inv KK` MP_TAC
  THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[REAL_POS; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MP_TAC(ISPEC `s1:1 word` LIEEEAUX_WORD1_CASES) THEN
  MP_TAC(ISPEC `s2:1 word` LIEEEAUX_WORD1_CASES) THEN
  REPEAT(DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC)) THEN
  REWRITE_TAC[VAL_WORD_0; VAL_WORD_1; real_pow; REAL_POW_1;
              LIEEEAUX_WORD_1_NE_0; GSYM LIEEEAUX_WORD_1_NE_0] THEN
  REWRITE_TAC[REAL_MUL_LID; REAL_MUL_LNEG; REAL_EQ_NEG2; REAL_EQ_MUL_RCANCEL;
              REAL_OF_NUM_EQ; REAL_NEG_EQ_0] THEN
  ASM_SIMP_TAC[REAL_LT_IMP_NZ] THEN REAL_ARITH_TAC);;

let float_to_real_eq = prove
 (`!x y:(T,W)float.
     float_to_real x = float_to_real y <=>
     x = y \/ float_is_zero x /\ float_is_zero y`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [ALL_TAC; MESON_TAC[float_is_zero_to_real]] THEN
  ASM_CASES_TAC `float_to_real (x:(T,W)float) = &0` THENL
   [ASM_MESON_TAC[float_is_zero_to_real]; ALL_TAC] THEN
  DISCH_TAC THEN DISJ1_TAC THEN
  MP_TAC(ISPECL
   [`&2 pow ((2 EXP (dimindex(:W) - 1) - 1) + dimindex(:T))`;
    `if float_Exponent (x:(T,W)float) = word 0
     then 2 * val(float_Significand x)
     else 2 EXP val(float_Exponent x) *
          (2 EXP dimindex(:T) + val(float_Significand x))`;
    `if float_Exponent (y:(T,W)float) = word 0
     then 2 * val(float_Significand y)
     else 2 EXP val(float_Exponent y) *
          (2 EXP dimindex(:T) + val(float_Significand y))`;
    `float_Sign (x:(T,W)float)`; `float_Sign (y:(T,W)float)`]
   LIEEE_SIGN_MAG_EQ) THEN
  REWRITE_TAC[GSYM LIEEE_FLOAT_TO_REAL_N; REAL_LT_POW2] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`dimindex(:T)`; `val(float_Exponent (x:(T,W)float))`;
                 `val(float_Exponent (y:(T,W)float))`;
                 `val(float_Significand (x:(T,W)float))`;
                 `val(float_Significand (y:(T,W)float))`] LIEEE_N_INJ) THEN
  ASM_REWRITE_TAC[VAL_BOUND; VAL_EQ_0] THEN
  ASM_REWRITE_TAC[float_component_equality; VAL_EQ]);;

(* Rounding a representable value (ties to even) gives that float back: a   *)
(* sanity check of round, closest_such and is_closest (not a HOL4 theorem). *)

let LIEEE_LARGEST_N = prove
 (`largest(:T#W) =
   &(2 EXP ((2 EXP dimindex(:W) - 1) - 1) *
     (2 EXP (dimindex(:T) + 1) - 1)) /
   &2 pow ((2 EXP (dimindex(:W) - 1) - 1) + dimindex(:T))`,
  REWRITE_TAC[largest_def] THEN
  SUBGOAL_THEN `1 <= 2 EXP (dimindex(:T) + 1)` ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; EXP_EQ_0; ARITH_EQ];
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_SUB] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_POW; REAL_POW_ADD; REAL_POW_1] THEN
  SUBGOAL_THEN `~(&2 pow dimindex(:T) = &0) /\
                ~(&2 pow (2 EXP (dimindex(:W) - 1) - 1) = &0)`
  MP_TAC THENL [REWRITE_TAC[REAL_POW_EQ_0] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC REAL_FIELD);;

let LIEEE_ABS_FLOAT_LE_LARGEST = prove
 (`!a:(T,W)float. float_is_finite a ==> abs(float_to_real a) <= largest(:T#W)`,
  GEN_TAC THEN REWRITE_TAC[float_is_finite_Exponent] THEN DISCH_TAC THEN
  REWRITE_TAC[LIEEE_FLOAT_TO_REAL_N; LIEEE_LARGEST_N] THEN
  REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_DIV; REAL_ABS_POW; REAL_ABS_NEG;
              REAL_ABS_NUM; REAL_POW_ONE; REAL_MUL_LID] THEN
  SIMP_TAC[REAL_LE_DIV2_EQ; REAL_LT_POW2; REAL_OF_NUM_LE] THEN
  SUBGOAL_THEN
   `val(float_Exponent (a:(T,W)float)) <= (2 EXP dimindex(:W) - 1) - 1`
  ASSUME_TAC THENL
   [MP_TAC(ISPEC `float_Exponent (a:(T,W)float)` VAL_BOUND) THEN
    UNDISCH_TAC `~(float_Exponent (a:(T,W)float) = word_UINT_MAX)` THEN
    REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_UINT_MAX] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPEC `float_Significand (a:(T,W)float)` VAL_BOUND) THEN
  REWRITE_TAC[EXP_ADD; EXP_1] THEN
  ABBREV_TAC `P = 2 EXP dimindex(:T)` THEN
  ABBREV_TAC `m = val(float_Significand (a:(T,W)float))` THEN
  ABBREV_TAC `e = val(float_Exponent (a:(T,W)float))` THEN
  ABBREV_TAC `U = (2 EXP dimindex(:W) - 1) - 1` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `1 <= 2 EXP U /\ 2 EXP e <= 2 EXP U` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LE_EXP; ARITH_EQ] THEN
    REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; EXP_EQ_0; ARITH_EQ];
    ALL_TAC] THEN
  COND_CASES_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `1 * (P * 2 - 1)` THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC LE_MULT2 THEN ASM_REWRITE_TAC[LE_REFL];
    MATCH_MP_TAC LE_MULT2 THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

let LIEEE_IS_CLOSEST_FLOAT = prove
 (`!a b:(T,W)float.
     float_is_finite a /\ ~float_is_zero a
     ==> (is_closest float_is_finite (float_to_real a) b <=> b = a)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[is_closest_def; IN] THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `a:(T,W)float`)) THEN
    ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0] THEN
    REWRITE_TAC[REAL_ARITH `abs(x - y) <= &0 <=> x = y`; float_to_real_eq] THEN
    ASM_MESON_TAC[];
    DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0; REAL_ABS_POS]]);;

let LIEEE_ROUND_FINITE_FLOAT = prove
 (`!a:(T,W)float.
     float_is_finite a /\ ~float_is_zero a
     ==> round roundTiesToEven (float_to_real a) = a`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `a:(T,W)float` LIEEE_ABS_FLOAT_LE_LARGEST) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC largest_lt_threshold THEN MP_TAC threshold_is_positive THEN
  REPEAT DISCH_TAC THEN
  REWRITE_TAC[round_def; rounding_CASE; LET_DEF; LET_END_DEF] THEN
  SUBGOAL_THEN `~(float_to_real (a:(T,W)float) <= --threshold(:T#W)) /\
                ~(float_to_real (a:(T,W)float) >= threshold(:T#W))`
  STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[closest_such_def] THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN
  ASM_SIMP_TAC[LIEEE_IS_CLOSEST_FLOAT] THEN MESON_TAC[]);;

let LIEEE_FLOAT_ROUND_FINITE_FLOAT = prove
 (`!a:(T,W)float b.
     float_is_finite a /\ ~float_is_zero a
     ==> float_round roundTiesToEven b (float_to_real a) = a`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[float_round_def; LET_DEF; LET_END_DEF;
               LIEEE_ROUND_FINITE_FLOAT]);;

(* the square root is only taken of non-negative values (where HOL Light's   *)
(* sqrt and HOL4's agree)                                                    *)

let LIEEE_FLOAT_SQRT_ARG_NONNEG = prove
 (`!x:(T,W)float r. float_Sign x = word 0 /\ float_value x = Float r ==> &0 <= r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[float_value_def] THEN
  REPEAT(COND_CASES_TAC THEN
         REWRITE_TAC[float_value_distinct; GSYM float_value_distinct]) THEN
  REWRITE_TAC[float_value_11] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
  ASM_REWRITE_TAC[LIEEE_FLOAT_TO_REAL_N; VAL_WORD_0; real_pow; REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS] THEN
  MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC);;

let LIEEE_SND_FLOAT_ROUND_WITH_FLAGS = prove
 (`!mode toneg r.
     SND (float_round_with_flags mode toneg r :flags#(T,W)float) =
     float_round mode toneg r`,
  REWRITE_TAC[float_round_with_flags_def; LET_DEF; LET_END_DEF]);;

let LIEEE_ROUND_TIES_ZERO = prove
 (`float_is_zero (round roundTiesToEven (&0):(T,W)float)`,
  MP_TAC threshold_is_positive THEN DISCH_TAC THEN
  REWRITE_TAC[round_def; rounding_CASE; LET_DEF; LET_END_DEF] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < t ==> ~(&0 <= --t) /\ ~(&0 >= t)`] THEN
  MP_TAC(BETA_RULE(SELECT_RULE(ISPECL
    [`\a:(T,W)float. ~bit 0 (float_Significand a)`; `&0`]
    is_closestP_finite_float_exists))) THEN
  REWRITE_TAC[closest_such_def] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  REWRITE_TAC[is_closest_float_is_finite_0] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[zero_properties]);;

(* HOL4 intreal: the characterizations of INT_FLOOR and INT_CEILING          *)

let LIEEE_FLOOR_EXISTS = prove
 (`!x. ?i:int. real_of_int i <= x /\ x < real_of_int i + &1`,
  GEN_TAC THEN
  X_CHOOSE_TAC `N:num` (SPEC `--x` REAL_ARCH_SIMPLE) THEN
  MP_TAC(fst(EQ_IMP_RULE(BETA_RULE(SPEC `\n. x + &N < &(SUC n)` num_WOP)))) THEN
  ANTS_TAC THENL
   [X_CHOOSE_TAC `M:num` (SPEC `x + &N` REAL_ARCH_SIMPLE) THEN
    EXISTS_TAC `M:num` THEN REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `&n - &N:int` THEN
  REWRITE_TAC[int_sub_th; int_of_num_th] THEN
  ASM_CASES_TAC `n = 0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_SUC]) THEN
    ASM_REAL_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPEC `n - 1`) THEN
    ASM_SIMP_TAC[ARITH_RULE `~(n = 0) ==> n - 1 < n /\ SUC(n - 1) = n`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_SUC]) THEN
    ASM_REAL_ARITH_TAC]);;

let LIEEE_FLOOR_UNIQUE = prove
 (`!r i j:int.
     real_of_int i <= r /\ r < real_of_int i + &1 /\
     real_of_int j <= r /\ r < real_of_int j + &1 ==> i = j`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(i:int < j) /\ ~(j < i)` MP_TAC THENL
   [REWRITE_TAC[INT_LT_DISCRETE; int_le; int_add_th; int_of_num_th] THEN
    ASM_REAL_ARITH_TAC;
    INT_ARITH_TAC]);;

let INT_FLOOR = prove
 (`!r i. INT_FLOOR r = i <=>
         real_of_int i <= r /\ r < real_of_int (i + &1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[int_add_th; int_of_num_th] THEN
  X_CHOOSE_TAC `k:int` (SPEC `r:real` LIEEE_FLOOR_EXISTS) THEN
  SUBGOAL_THEN `INT_FLOOR r = k` SUBST1_TAC THENL
   [REWRITE_TAC[INT_FLOOR_def] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
    X_GEN_TAC `y:int` THEN REWRITE_TAC[int_add_th; int_of_num_th] THEN
    EQ_TAC THENL
     [STRIP_TAC THEN
      SUBGOAL_THEN `~(k:int < y) /\ ~(y < k)` MP_TAC THENL
       [CONJ_TAC THEN DISCH_TAC THENL
         [FIRST_X_ASSUM(MP_TAC o SPEC `k:int`) THEN
          ASM_REWRITE_TAC[int_add_th; int_of_num_th];
          FIRST_ASSUM(MP_TAC o REWRITE_RULE[INT_LT_DISCRETE]) THEN
          REWRITE_TAC[int_le; int_add_th; int_of_num_th] THEN
          ASM_REAL_ARITH_TAC];
        INT_ARITH_TAC];
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `j:int` THEN REWRITE_TAC[INT_LT_DISCRETE; int_le] THEN
      REWRITE_TAC[int_add_th; int_of_num_th] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_MESON_TAC[LIEEE_FLOOR_UNIQUE]);;

let INT_FLOOR_BOUNDS = prove
 (`!r. real_of_int (INT_FLOOR r) <= r /\ r < real_of_int (INT_FLOOR r + &1)`,
  MESON_TAC[INT_FLOOR]);;

let INT_CEILING = prove
 (`!r i. INT_CEILING r = i <=>
         real_of_int (i - &1) < r /\ r <= real_of_int i`,
  REPEAT GEN_TAC THEN REWRITE_TAC[int_sub_th; int_of_num_th] THEN
  X_CHOOSE_TAC `f:int` (SPEC `--r:real` LIEEE_FLOOR_EXISTS) THEN
  SUBGOAL_THEN `INT_CEILING r = --f` SUBST1_TAC THENL
   [REWRITE_TAC[INT_CEILING_def] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
    X_GEN_TAC `y:int` THEN BETA_TAC THEN EQ_TAC THENL
     [STRIP_TAC THEN
      SUBGOAL_THEN `~(--f:int < y) /\ ~(y < --f)` MP_TAC THENL
       [CONJ_TAC THEN DISCH_TAC THENL
         [FIRST_X_ASSUM(MP_TAC o SPEC `--f:int`) THEN
          ASM_REWRITE_TAC[int_neg_th] THEN ASM_REAL_ARITH_TAC;
          FIRST_ASSUM(MP_TAC o REWRITE_RULE[INT_LT_DISCRETE]) THEN
          REWRITE_TAC[int_le; int_add_th; int_of_num_th; int_neg_th] THEN
          ASM_REAL_ARITH_TAC];
        INT_ARITH_TAC];
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[int_neg_th] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      X_GEN_TAC `j:int` THEN REWRITE_TAC[INT_LT_DISCRETE; int_le] THEN
      REWRITE_TAC[int_add_th; int_of_num_th; int_neg_th] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[int_neg_th] THEN EQ_TAC THENL
   [DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[int_neg_th] THEN
    ASM_REAL_ARITH_TAC;
    STRIP_TAC THEN
    MP_TAC(ISPECL [`--r:real`; `f:int`; `--i:int`] LIEEE_FLOOR_UNIQUE) THEN
    ASM_REWRITE_TAC[int_neg_th] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; INT_ARITH_TAC]]);;

let INT_CEILING_BOUNDS = prove
 (`!r. real_of_int (INT_CEILING r - &1) < r /\ r <= real_of_int (INT_CEILING r)`,
  MESON_TAC[INT_CEILING]);;

(* next_hi, next_lo and float_ulp                                            *)

let LIEEEAUX_WORD_ULT_UINT_MAX = prove
 (`!x:N word. word_ult x word_UINT_MAX <=> ~(x = word_UINT_MAX)`,
  GEN_TAC THEN REWRITE_TAC[WORD_ULT; GSYM VAL_EQ; VAL_WORD_UINT_MAX] THEN
  MP_TAC(ISPEC `x:N word` VAL_BOUND) THEN ARITH_TAC);;

let LIEEEAUX_WORD_ULT_0 = prove
 (`!x:N word. word_ult (word 0) x <=> ~(x = word 0)`,
  GEN_TAC THEN REWRITE_TAC[WORD_ULT; GSYM VAL_EQ; VAL_WORD_0] THEN ARITH_TAC);;

let LIEEEAUX_WORD_SUB_ADD_1 = prove
 (`(!x:N word. word_add (word_sub x (word 1)) (word 1) = x) /\
   (!x:N word. word_sub (word_add x (word 1)) (word 1) = x)`,
  CONJ_TAC THEN GEN_TAC THEN CONV_TAC WORD_RULE);;

let LIEEEAUX_WORD_ADD_1_NE = prove
 (`!x:N word. ~(word_add x (word 1) = x)`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o AP_TERM `\y:N word. word_sub y x`) THEN
  REWRITE_TAC[WORD_RULE `word_sub (word_add (x:N word) (word 1)) x = word 1`;
              WORD_SUB_REFL; LIEEEAUX_WORD_1_NE_0]);;

let LIEEE_FUPD_SELF = prove
 (`!f:(T,W)float. float_Significand_fupd (K (float_Significand f)) f = f`,
  REWRITE_TAC[float_component_equality; float_accfupds; K_THM]);;

let next_hilo = prove
 (`!f:(T,W)float. next_hi (next_lo f) = f`,
  GEN_TAC THEN REWRITE_TAC[next_lo_def; LIEEEAUX_WORD_ULT_0] THEN
  COND_CASES_TAC THEN
  REWRITE_TAC[next_hi_def; float_accessors; float_accfupds; K_THM;
              LIEEEAUX_WORD_ULT_UINT_MAX] THENL
   [SUBGOAL_THEN `~(word_sub (float_Significand (f:(T,W)float)) (word 1) =
                    word_UINT_MAX)` (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SUB_CASES; VAL_WORD_1;
                  VAL_WORD_UINT_MAX] THEN
      UNDISCH_TAC `~(float_Significand (f:(T,W)float) = word 0)` THEN
      REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_0] THEN
      MP_TAC(ISPEC `float_Significand (f:(T,W)float)` VAL_BOUND) THEN
      ARITH_TAC;
      REWRITE_TAC[float_fupdfupds; K_o_THM; LIEEEAUX_WORD_SUB_ADD_1;
                  LIEEE_FUPD_SELF]];
    REWRITE_TAC[float_component_equality; float_accessors;
                LIEEEAUX_WORD_SUB_ADD_1] THEN
    ASM_REWRITE_TAC[]]);;

let next_lohi = prove
 (`!f:(T,W)float. next_lo (next_hi f) = f`,
  GEN_TAC THEN REWRITE_TAC[next_hi_def; LIEEEAUX_WORD_ULT_UINT_MAX] THEN
  COND_CASES_TAC THEN
  REWRITE_TAC[next_lo_def; float_accessors; float_accfupds; K_THM;
              LIEEEAUX_WORD_ULT_0] THENL
   [SUBGOAL_THEN `~(word_add (float_Significand (f:(T,W)float)) (word 1) =
                    word 0)` (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ADD; VAL_WORD_1; VAL_WORD_0] THEN
      UNDISCH_TAC `~(float_Significand (f:(T,W)float) = word_UINT_MAX)` THEN
      REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_UINT_MAX] THEN
      MP_TAC(ISPEC `float_Significand (f:(T,W)float)` VAL_BOUND) THEN
      SIMP_TAC[MOD_LT; ARITH_RULE `x < n /\ ~(x = n - 1) ==> x + 1 < n`] THEN
      ARITH_TAC;
      REWRITE_TAC[float_fupdfupds; K_o_THM; LIEEEAUX_WORD_SUB_ADD_1;
                  LIEEE_FUPD_SELF]];
    REWRITE_TAC[float_component_equality; float_accessors;
                LIEEEAUX_WORD_SUB_ADD_1] THEN
    ASM_REWRITE_TAC[]]);;

let next_hi_11 = prove
 (`!f g:(T,W)float. next_hi f = next_hi g <=> f = g`,
  MESON_TAC[next_lohi]);;

let next_lo_11 = prove
 (`!f g:(T,W)float. next_lo f = next_lo g <=> f = g`,
  MESON_TAC[next_hilo]);;

let next_hi_idem = prove
 (`!f:(T,W)float. ~(next_hi f = f)`,
  GEN_TAC THEN REWRITE_TAC[next_hi_def] THEN COND_CASES_TAC THEN
  REWRITE_TAC[float_component_equality; float_accessors; float_accfupds;
              K_THM] THENL
   [REWRITE_TAC[LIEEEAUX_WORD_ADD_1_NE];
    POP_ASSUM MP_TAC THEN
    REWRITE_TAC[LIEEEAUX_WORD_ULT_UINT_MAX] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[GSYM LIEEEAUX_WORD_UINT_MAX_NE_0]]);;

let next_lo_idem = prove
 (`!f:(T,W)float. ~(next_lo f = f)`,
  MESON_TAC[next_hilo; next_hi_idem]);;

let next_hi_Sign = prove
 (`!f:(T,W)float. float_Sign (next_hi f) = float_Sign f`,
  GEN_TAC THEN REWRITE_TAC[next_hi_def] THEN COND_CASES_TAC THEN
  REWRITE_TAC[float_accessors; float_accfupds]);;

let next_lo_Sign = prove
 (`!f:(T,W)float. float_Sign (next_lo f) = float_Sign f`,
  GEN_TAC THEN REWRITE_TAC[next_lo_def] THEN COND_CASES_TAC THEN
  REWRITE_TAC[float_accessors; float_accfupds]);;

let float_ulp_negate = prove
 (`!f:(T,W)float. float_ulp (float_negate f) = float_ulp f`,
  REWRITE_TAC[float_ulp_def; float_components]);;

let float_ulp_updating_Significand = prove
 (`!f:(T,W)float s.
     float_ulp (float_Significand_fupd (K s) f) = float_ulp f`,
  REWRITE_TAC[float_ulp_def; float_accfupds]);;

let float_ulp_updating_Sign = prove
 (`!f:(T,W)float s. float_ulp (float_Sign_fupd (K s) f) = float_ulp f`,
  REWRITE_TAC[float_ulp_def; float_accfupds]);;

let float_ulp_abs = prove
 (`!a:(T,W)float. float_ulp (float_abs a) = float_ulp a`,
  REWRITE_TAC[float_ulp_def; float_abs_Exponent]);;

let float_ulp_GT0 = prove
 (`!f:(T,W)float. &0 < float_ulp f`,
  REWRITE_TAC[float_ulp_def; ULP_positive]);;

let float_ulp_EQ0 = prove
 (`!f:(T,W)float. ~(float_ulp f = &0)`,
  MESON_TAC[float_ulp_GT0; REAL_LT_REFL]);;

let abs_float_ulp = prove
 (`!f:(T,W)float. abs (float_ulp f) = float_ulp f`,
  MESON_TAC[float_ulp_GT0; REAL_ARITH `&0 < x ==> abs x = x`]);;

let abs_ULP = prove
 (`!x:W word y:T->bool. abs (ULP (x,y)) = ULP (x,y)`,
  MESON_TAC[ULP_positive; REAL_ARITH `&0 < x ==> abs x = x`]);;

let abs_ulp = prove
 (`abs (ulp(:T#W)) = ulp(:T#W)`,
  REWRITE_TAC[ulp_def; abs_ULP]);;

(* HOL4 [simp] theorems                                                      *)

let _ = cake_add_simps
  [FINITE_floatsets; zeroes_are_finite_floats; zero_to_real;
   ULP_positive; ULP_nonzero; ulp_positive; ulp_nonzero;
   float_components; float_distinct; float_values;
   infinity_properties; zero_properties; min_properties;
   top_properties; bottom_properties; largest_is_positive;
   threshold_is_positive; float_negate_negate; float_negate_11;
   float_is_finite_float_negate; float_is_zero_float_negate;
   float_to_real_float_abs; sign_float_abs; float_abs_Exponent;
   float_abs_Significand; float_is_finite_float_abs;
   next_hilo; next_lohi; next_hi_11; next_lo_11; next_hi_idem; next_lo_idem;
   next_hi_Sign; next_lo_Sign; float_ulp_negate;
   float_ulp_updating_Significand; float_ulp_updating_Sign; float_ulp_abs;
   float_ulp_GT0; float_ulp_EQ0; abs_float_ulp; abs_ULP; abs_ulp];;
