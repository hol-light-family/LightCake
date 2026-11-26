(* ========================================================================= *)
(* std_prelude: port of HOL4 translator/std_preludeScript.sml (CakeML        *)
(* v3479).  Translations of various useful HOL functions and datatypes, to   *)
(* serve as a starting point for further translations.                       *)
(*                                                                           *)
(* HOL4's library functions are translated from the HOL4-shaped theorems of  *)
(* hol4/basic.ml (FUNPOW, MIN_DEF, MAX_DEF, ODD_EVEN, EVEN_MOD2, UNCURRY,    *)
(* WHILE, OWHILE_THM: HOL Light's own definitions of ITER, MIN, MAX, ...     *)
(* have other shapes), so that the code is HOL4's.  HOL4's FUNPOW f n x is   *)
(* ITER n f x and LEAST is minimal: the CakeML function funpow takes its     *)
(* arguments in ITER's order.                                                *)
(* ========================================================================= *)

needs "translator/ml_translatorLib.ml";;

type_invention_error := true;;

translation_reset ();;

(* type registration *)

use_full_type_names := false;;

register_type `:ordering`;;
register_type `:(A)option`;;
register_type `:(A)list`;;
register_type `:A#B`;;
register_type `:A+B`;;
register_type `:(A)app_list`;;

(* pair *)

let _ = translate FST;;
let _ = translate SND;;
let _ = translate CURRY_DEF;;
let _ = translate UNCURRY;;

(* combin *)

next_ml_names := ["o"];;
let _ = translate o_DEF;;
next_ml_names := ["id"];;
let _ = translate I_THM;;
next_ml_names := ["flip"];;
let _ = translate C_DEF;;
next_ml_names := ["const"];;
let _ = translate combin_K_DEF;;
let _ = translate UPDATE_DEF;;

(* arithmetic *)

let EXP_AUX_def = cake_def
  `EXP_AUX m n k = if n = 0 then k else EXP_AUX m (n - 1:num) (m * k:num)`;;

let EXP_AUX_THM =
  let th = prove
   (`!n k. EXP_AUX m n (m EXP k) = m EXP (k + n)`,
    INDUCT_TAC THEN ONCE_REWRITE_TAC[EXP_AUX_def] THEN
    REWRITE_TAC[NOT_SUC; SUC_SUB1; ADD_CLAUSES] THEN
    ASM_REWRITE_TAC[GSYM (CONJUNCT2 EXP); ADD_CLAUSES]) in
  GSYM (REWRITE_RULE [EXP; ADD_CLAUSES] (SPECL [`n:num`; `0`] th));;

next_ml_names := ["exp"];;
let _ = translate EXP_AUX_def;;

next_ml_names := ["exp"];;
let _ = translate EXP_AUX_THM;; (* tailrec version of EXP *)

let _ = translate MIN_DEF;;
let _ = translate MAX_DEF;;
let _ = translate EVEN_MOD2;;
let _ = translate (REWRITE_RULE [EVEN_MOD2; ARITH_RULE `~(n = 0) <=> 0 < n`] ODD_EVEN);;
let _ = translate FUNPOW;;

(* HOL4 arithmetic ABS_DIFF (not in the library layer) *)
let ABS_DIFF_def = new_definition
  `ABS_DIFF (m:num) n = if m < n then n - m else m - n`;;

let _ = translate ABS_DIFF_def;;

let _ = translate (REWRITE_RULE [GSYM sub_check_def] (ARITH_RULE `PRE n = n - 1`));;

(* while, owhile and least *)

let IS_SOME_OWHILE_THM = prove
 (`!(g:A->bool) f x. IS_SOME (OWHILE g f x) <=>
                     ?n. ~g (ITER n f x) /\ !m. m < n ==> g (ITER m f x)`,
  REPEAT GEN_TAC THEN
  MP_TAC (BETA_RULE (SPEC `\n. ~(g:A->bool) (ITER n f x)` num_WOP)) THEN
  REWRITE_TAC[OWHILE_DEF] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[IS_SOME_DEF] THEN MESON_TAC[]);;

let WHILE_ind = prove
 (`!P. (!(p:A->bool) g x. (p x ==> P p g (g x)) ==> P p g x) ==>
       !p g x. IS_SOME (OWHILE p g x) ==> P p g x`,
  GEN_TAC THEN DISCH_THEN (LABEL_TAC "step") THEN
  REWRITE_TAC[IS_SOME_OWHILE_THM; LEFT_IMP_EXISTS_THM] THEN
  SUBGOAL_THEN
   `!n (p:A->bool) g x. ~p (ITER n g x) /\ (!m. m < n ==> p (ITER m g x)) ==> P p g x`
   (fun th -> MESON_TAC[th]) THEN
  INDUCT_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  USE_THEN "step" MATCH_MP_TAC THEN DISCH_TAC THENL
   [ASM_MESON_TAC[FUNPOW];
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    RULE_ASSUM_TAC (REWRITE_RULE [FUNPOW]) THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC `SUC m`) THEN ASM_REWRITE_TAC[LT_SUC; FUNPOW]]);;

let OWHILE_ind = WHILE_ind;;

add_ind_thm "WHILE" WHILE_ind;;
add_ind_thm "OWHILE" OWHILE_ind;;

next_ml_names := ["while"];;
let _ = translate WHILE;;
let _ = translate OWHILE_THM;;

let SUC_LEMMA = prove
 (`SUC = \x. x + 1`,
  REWRITE_TAC[FUN_EQ_THM; ADD1]);;

let LEAST_LEMMA = prove
 (`(minimal) (P:num->bool) = WHILE (\x. ~(P x)) (\x. x + 1) 0`,
  SUBGOAL_THEN `!n. ITER n (\x. x + 1) 0 = n` ASSUME_TAC THENL
   [INDUCT_TAC THEN ASM_REWRITE_TAC[ITER] THEN ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[WHILE_DEF] THEN
  COND_CASES_TAC THENL
   [GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM ETA_AX] THEN REFL_TAC;
    REWRITE_TAC[minimal] THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
    ASM_MESON_TAC[]]);;

let _ = translate LEAST_LEMMA;;

let FUNPOW_LEMMA = prove
 (`!n m. ITER n (\x. x + 1) m = n + m`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[FUNPOW] THEN ARITH_TAC);;

let least_side_thm = update_precondition (prove
 (`!s. least_side s <=> ~(s = {})`,
  GEN_TAC THEN
  REWRITE_TAC[tr_fetch "least_side_def"; OWHILE_DEF; FUNPOW_LEMMA; ADD_CLAUSES] THEN
  REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN; NOT_FORALL_THM] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[IS_SOME_DEF]));;

(* app_list *)

ml_prog_update ml_prog_open_local_block;;
let _ = translate append_aux_def;;
ml_prog_update ml_prog_open_local_in_block;;

let _ = translate append_def;;

ml_prog_update ml_prog_close_local_blocks;;

(* HOL4 print_asts := true (printing of the generated code; not ported) *)

finalise_translation ();;
