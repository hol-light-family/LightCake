(* ========================================================================= *)
(* IntProg: port of HOL4 basis/IntProgScript.sml (CakeML v3479).             *)
(* Module about the built-in integer type.  Note that CakeML uses            *)
(* arbitrary precision integers (the mathematical integers).                 *)
(*                                                                           *)
(* HOL4's gcd$gcd (curried) is HOL Light's gcd on pairs, num_gcd (a,b); the *)
(* certificate gcd_v_thm is stated for mlint_num_gcd (mlint's num_gcd, equal *)
(* to it by num_gcd_eq_gcd).  HOL4's num_cmp is num_compare.                  *)
(* ========================================================================= *)

needs "basis/pure/mlint.ml";;
needs "basis/mlbasicsProg.ml";;
needs "basis/basisFunctionsLib.ml";;

type_invention_error := true;;

translation_extends "mlbasicsProg";;

ml_prog_update (ml_prog_open_module "Int");;

ml_prog_update (ml_prog_add_dec
  `Dtabbrev unknown_loc [] (implode "int") (Atapp [] (Short (implode "int")))` I);;

let _ = trans "+" `int_add`;;
let IntProg_Int_plus_def = tr_fetch "Int_plus_def";;
let _ = trans "-" `int_sub`;;
let IntProg_Int_minus_def = tr_fetch "Int_minus_def";;
let _ = trans "*" `int_mul`;;
let IntProg_Int_times_def = tr_fetch "Int_times_def";;
let _ = trans "div" `int_div`;;
let IntProg_Int_div_def = tr_fetch "Int_div_def";;
let _ = trans "mod" `integer_int_mod`;;
let IntProg_Int_mod_def = tr_fetch "Int_mod_def";;
let _ = trans "<" `int_lt`;;
let IntProg_Int_lt_def = tr_fetch "Int_lt_def";;
let _ = trans ">" `int_gt`;;
let IntProg_Int_gt_def = tr_fetch "Int_gt_def";;
let _ = trans "<=" `int_le`;;
let IntProg_Int_le_def = tr_fetch "Int_le_def";;
let _ = trans ">=" `int_ge`;;
let IntProg_Int_ge_def = tr_fetch "Int_ge_def";;
let _ = trans "~" `\i. --(i:int)`;;
let IntProg_Int_uminus_def = tr_fetch "Int_uminus_def";;

ml_prog_update ml_prog_open_local_block;;

let _ = translate exp_for_dec_enc_def;;
let _ = translate toChar_def;;

let _ = translate num_to_chars_def;;

let tochar_side_dec = prove
 (`i < 10 ==> tochar_side i`,
  REWRITE_TAC[tr_fetch "tochar_side_def"] THEN ARITH_TAC);;

let num_to_chars_side = prove
 (`!i j k acc. num_to_chars_side i j k acc`,
  MATCH_MP_TAC num_to_chars_ind THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[tr_fetch "num_to_chars_side_def"] THEN
  REWRITE_TAC[NOT_SUC; GSYM NOT_SUC; SUC_INJ; SUC_SUB1; ARITH_RULE `1 <= SUC x`; ARITH_EQ] THEN
  REPEAT STRIP_TAC THEN
  TRY (FIRST_X_ASSUM (SUBST_ALL_TAC o SYM o check (fun th -> is_var (rhs (concl th))))) THEN
  ASM_MESON_TAC[tochar_side_dec; MOD_LT_EQ; ARITH_RULE `~(10 = 0)`]);;
let _ = update_precondition num_to_chars_side;;

ml_prog_update ml_prog_open_local_in_block;;

let int_to_string_v_thm = translate int_to_string_def;;

next_ml_names := ["toString"];;
let toString_v_thm = translate toString_def1;;

let Eval_NUM_toString = add_user_proved_v_thm (MATCH_MP (prove
 (`!v. (ml_INT --> STRING_TYPE) toString v ==>
       (ml_NUM --> STRING_TYPE) num_to_str v`,
  REWRITE_TAC[ml_Arrow_def; ml_AppReturns_def; num_to_str_def; ml_NUM_def] THEN
  CONV_TAC (DEPTH_CONV BETA_CONV) THEN MESON_TAC[])) toString_v_thm);;

ml_prog_update ml_prog_close_local_blocks;;

ml_prog_update ml_prog_open_local_block;;

(* HOL4: val th = EVAL of ORD #"0", the code of the character 0 *)
let IntProg_ORD_0 = prove
 (`ORD (CHR 48) = 48`,
  MATCH_MP_TAC ORD_CHR_RWT THEN ARITH_TAC);;
let _ = translate (REWRITE_RULE [IntProg_ORD_0; GSYM sub_check_def] fromChar_unsafe_def);;
let _ = translate fromChars_range_unsafe_def;;

let _ = translate padLen_DEC_eq;;
let _ = translate maxSmall_DEC_def;;

(* HOL4 add_preferred_thy "-" and Theorem fromChars_unsafe_ind *)
let IntProg_fromChars_unsafe_ind =
  REWRITE_RULE [maxSmall_DEC_def; padLen_DEC_eq] fromChars_unsafe_ind;;
add_ind_thm "fromChars_unsafe" IntProg_fromChars_unsafe_ind;;
let _ = translate (REWRITE_RULE [maxSmall_DEC_def; padLen_DEC_eq] fromChars_unsafe_def);;

let _ = translate fromString_unsafe_def;;

let fromstring_unsafe_side_def = tr_fetch "fromstring_unsafe_side_def";;
let fromchars_unsafe_side_def = tr_fetch "fromchars_unsafe_side_def";;
let fromchars_range_unsafe_side_def = tr_fetch "fromchars_range_unsafe_side_def";;

let BAS1AUX_fromchars_range_unsafe_side = prove
 (`!n l s. l + n <= strlen s ==> fromchars_range_unsafe_side l n s`,
  BAS1AUX_SIDE_TAC "n" fromchars_range_unsafe_side_def);;

let BAS1AUX_fromchars_unsafe_side = prove
 (`!n s. n <= strlen s ==> fromchars_unsafe_side n s`,
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  X_GEN_TAC `s:mlstring` THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[fromchars_unsafe_side_def] THEN X_GEN_TAC `m:num` THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  REWRITE_TAC[SUC_SUB1; GSYM ADD1; ARITH_RULE `1 <= SUC x`] THEN
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC BAS1AUX_fromchars_range_unsafe_side THEN ASM_ARITH_TAC;
    MATCH_MP_TAC BAS1AUX_fromchars_range_unsafe_side THEN ASM_ARITH_TAC;
    FIRST_X_ASSUM (MATCH_MP_TAC o REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP]) THEN
    ASM_ARITH_TAC;
    ASM_ARITH_TAC]);;

let fromchars_unsafe_side_thm = prove
 (`!n s. n <= LENGTH s ==> fromchars_unsafe_side n (implode s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC BAS1AUX_fromchars_unsafe_side THEN
  ASM_REWRITE_TAC[strlen_def]);;

let fromString_unsafe_side = update_precondition (prove
 (`!x. fromstring_unsafe_side x = T`,
  GEN_TAC THEN REWRITE_TAC[fromstring_unsafe_side_def] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC BAS1AUX_fromchars_unsafe_side THEN
  REWRITE_TAC[strlen_substring] THEN
  REPEAT COND_CASES_TAC THEN ASM_ARITH_TAC));;

let fromChar_thm = prove
 (`fromChar char =
     let vc = ORD char in
     if 48 <= vc /\ vc <= 57 then
       SOME (vc - 48) else NONE`,
  SUBGOAL_THEN `!c n. n < 256 ==> (c = CHR n <=> ORD c = n)`
   (fun th -> SIMP_TAC[th; fromChar_def; ARITH; LET_DEF; LET_END_DEF]) THENL
   [MESON_TAC[ORD_11; ORD_CHR_RWT]; ALL_TAC] THEN
  SPEC_TAC (`ORD char`,`n:num`) THEN GEN_TAC THEN
  ASM_CASES_TAC `48 <= n /\ n <= 57` THEN ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM (DISJ_CASES_THEN2 SUBST1_TAC (DISJ_CASES_THEN2 SUBST1_TAC
      (DISJ_CASES_THEN2 SUBST1_TAC (DISJ_CASES_THEN2 SUBST1_TAC (DISJ_CASES_THEN2 SUBST1_TAC
      (DISJ_CASES_THEN2 SUBST1_TAC (DISJ_CASES_THEN2 SUBST1_TAC (DISJ_CASES_THEN2 SUBST1_TAC
      (DISJ_CASES_THEN2 SUBST1_TAC SUBST1_TAC)))))))) o
      MATCH_MP (ARITH_RULE `48 <= n /\ n <= 57 ==> n = 48 \/ n = 49 \/ n = 50 \/ n = 51 \/
                n = 52 \/ n = 53 \/ n = 54 \/ n = 55 \/ n = 56 \/ n = 57`)) THEN
    CONV_TAC NUM_REDUCE_CONV;
    SUBGOAL_THEN `~(n = 48) /\ ~(n = 49) /\ ~(n = 50) /\ ~(n = 51) /\ ~(n = 52) /\
                  ~(n = 53) /\ ~(n = 54) /\ ~(n = 55) /\ ~(n = 56) /\ ~(n = 57)`
      (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC]);;

let _ = translate fromChar_thm;;
let _ = translate fromChars_range_def;;

let IntProg_fromChars_ind = REWRITE_RULE [maxSmall_DEC_def; padLen_DEC_eq] fromChars_ind;;
add_ind_thm "fromChars" IntProg_fromChars_ind;;
let _ = translate (REWRITE_RULE [maxSmall_DEC_def; padLen_DEC_eq] fromChars_def);;

ml_prog_update ml_prog_open_local_in_block;;

next_ml_names := ["fromString"];;
let _ = translate mlint_fromString_def;;
let fromstring_side_def = tr_fetch "fromstring_side_def";;
let fromchars_side_def = tr_fetch "fromchars_side_def";;
let fromchars_range_side_def = tr_fetch "fromchars_range_side_def";;

let BAS1AUX_fromchars_range_side = prove
 (`!n l s. l + n <= strlen s ==> fromchars_range_side l n s`,
  BAS1AUX_SIDE_TAC "n" fromchars_range_side_def);;

let BAS1AUX_fromchars_side = prove
 (`!n s. n <= strlen s ==> fromchars_side n s`,
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  X_GEN_TAC `s:mlstring` THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[fromchars_side_def] THEN X_GEN_TAC `m:num` THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  REWRITE_TAC[SUC_SUB1; GSYM ADD1; ARITH_RULE `1 <= SUC x`] THEN
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC BAS1AUX_fromchars_range_side THEN ASM_ARITH_TAC;
    MATCH_MP_TAC BAS1AUX_fromchars_range_side THEN ASM_ARITH_TAC;
    FIRST_X_ASSUM (MATCH_MP_TAC o REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP]) THEN
    ASM_ARITH_TAC;
    ASM_ARITH_TAC]);;

let fromchars_side_thm = prove
 (`!n s. n <= LENGTH s ==> fromchars_side n (implode s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC BAS1AUX_fromchars_side THEN
  ASM_REWRITE_TAC[strlen_def]);;

let fromString_side = update_precondition (prove
 (`!x. fromstring_side x = T`,
  GEN_TAC THEN REWRITE_TAC[fromstring_side_def] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC BAS1AUX_fromchars_side THEN
  REWRITE_TAC[strlen_substring] THEN
  REPEAT COND_CASES_TAC THEN ASM_ARITH_TAC));;

next_ml_names := ["fromNatString"];;
let _ = translate fromNatString_def;;

(* GCD *)

ml_prog_update ml_prog_open_local_block;;

let _ = translate mlint_num_gcd_def;;

ml_prog_update ml_prog_open_local_in_block;;

next_ml_names := ["gcd"];;
let int_gcd_v_thm = translate mlint_int_gcd_def;;

let gcd_v_thm = prove
 (`(ml_NUM --> ml_NUM --> ml_NUM) mlint_num_gcd int_gcd_v`,
  MP_TAC int_gcd_v_thm THEN
  REWRITE_TAC[ml_Arrow_def; ml_AppReturns_def; ml_NUM_def] THEN
  CONV_TAC (DEPTH_CONV BETA_CONV) THEN
  SUBGOAL_THEN `!m n. &(mlint_num_gcd m n) = mlint_int_gcd (&m) (&n)`
   (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[mlint_int_gcd_def; INT_ABS_NUM; NUM_OF_INT_OF_NUM]; ALL_TAC] THEN
  MESON_TAC[]);;
let _ = add_user_proved_v_thm gcd_v_thm;;

(* compare *)

next_ml_names := ["compare"];;
let int_cmp_v_thm = translate mlint_int_cmp_def;;

let num_cmp_v_thm = prove
 (`(ml_NUM --> ml_NUM --> ORDERING_TYPE) num_compare int_cmp_v`,
  MP_TAC int_cmp_v_thm THEN
  REWRITE_TAC[ml_Arrow_def; ml_AppReturns_def; ml_NUM_def] THEN
  CONV_TAC (DEPTH_CONV BETA_CONV) THEN
  SUBGOAL_THEN `!m n. num_compare m n = mlint_int_cmp (&m) (&n)`
   (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[num_compare_def; mlint_int_cmp_def; INT_OF_NUM_LT] THEN
    REPEAT GEN_TAC THEN REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MESON_TAC[]);;
let _ = add_user_proved_v_thm num_cmp_v_thm;;

ml_prog_update ml_prog_close_local_blocks;;

ml_prog_update (ml_prog_close_module None);;

finalise_translation ();;
