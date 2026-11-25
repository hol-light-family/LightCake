(* ========================================================================= *)
(* MarshallingProg: port of HOL4 basis/MarshallingProgScript.sml (CakeML    *)
(* v3479), the code part.  Module with functions that aid converting to and *)
(* from the byte arrays that CakeML foreign-function interface (FFI) uses.  *)
(* The CakeML text of the Quote add_cakeml blocks is HOL4's, verbatim, at  *)
(* HOL4's source positions (add_cakeml_at).                                  *)
(* The four unicity theorems are ported (their attribute xlet_auto_match    *)
(* belongs to the CF automation); OPEN (M10, decision D2): the CF           *)
(* specifications n2w2_spec and w22n_spec.                                   *)
(* ========================================================================= *)

needs "basis/DoubleProg.ml";;
needs "basis/Marshalling.ml";;
needs "translator/ml_translator.ml";;
needs "basis/basisFunctionsLib.ml";;

type_invention_error := true;;

translation_extends "DoubleProg";;

(* Word8 module -- translated (HOL4 comment) *)

ml_prog_update (ml_prog_open_module "Marshalling");;

add_cakeml_at (17,18) {|
  fun n2w2 n bytes off =
    let val a = Word8Array.update bytes off     (Word8.fromInt (n div 256))
        val a = Word8Array.update bytes (off+1) (Word8.fromInt n)
    in () end
|};;

add_cakeml_at (24,18) {|
  fun w22n bytes off =
    let val b1 = Word8Array.sub bytes off
        val b0 = Word8Array.sub bytes (off+1)
    in Word8.toInt b1 * 256 + Word8.toInt b0 end
|};;

ml_prog_update (ml_prog_close_module None);;

(* if any more theorems get added here, probably should create             *)
(* Word8ProofTheory (HOL4 comment)                                          *)

(* two byte lists in the relation with one value are equal (HOL4's proofs:  *)
(* LIST_TYPE_def and WORD_UNICITY_L)                                        *)
let BAS1AUX_LIST_WORD_UNIQUE = prove
 (`!l1 l2 f. LIST_TYPE (ml_WORD:byte->v->bool) l1 f /\ LIST_TYPE ml_WORD l2 f
             ==> l1 = l2`,
  MP_TAC (EqualityType_rule [] `:byte list`) THEN
  REWRITE_TAC[EqualityType_def] THEN MESON_TAC[]);;

let n2w2_UNICITY_R = prove
 (`!n1 n2. n1 < 256 EXP 2 ==> ((n2w2 n1 = n2w2 n2 /\ n2 < 256 EXP 2) <=> n1 = n2)`,
  REPEAT GEN_TAC THEN CONV_TAC (ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN DISCH_TAC THEN
  EQ_TAC THENL
   [STRIP_TAC THEN
    MP_TAC (CONV_RULE (ONCE_DEPTH_CONV NUM_REDUCE_CONV) (SPEC `n1:num` w22n_n2w2)) THEN
    MP_TAC (CONV_RULE (ONCE_DEPTH_CONV NUM_REDUCE_CONV) (SPEC `n2:num` w22n_n2w2)) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    DISCH_THEN SUBST_ALL_TAC THEN ASM_REWRITE_TAC[]]);;

let WORD_n2w2_UNICITY_L = prove
 (`!n1 n2 f. n1 < 256 EXP 2 /\ LIST_TYPE ml_WORD (n2w2 n1) f ==>
             (LIST_TYPE ml_WORD (n2w2 n2) f /\ n2 < 256 EXP 2 <=> n1 = n2)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [STRIP_TAC THEN
    SUBGOAL_THEN `n2w2 n1 = n2w2 n2` ASSUME_TAC THENL
     [MATCH_MP_TAC BAS1AUX_LIST_WORD_UNIQUE THEN EXISTS_TAC `f:v` THEN
      ASM_REWRITE_TAC[];
      ASM_MESON_TAC[n2w2_UNICITY_R]];
    DISCH_THEN SUBST_ALL_TAC THEN ASM_REWRITE_TAC[]]);;

(* needed? (HOL4 comment) *)
let n2w8_UNICITY_R = prove
 (`!n1 n2. n1 < 256 EXP 8 ==> ((n2w8 n1 = n2w8 n2 /\ n2 < 256 EXP 8) <=> n1 = n2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN EQ_TAC THENL
   [STRIP_TAC THEN
    MP_TAC (SPEC `n1:num` w82n_n2w8) THEN MP_TAC (SPEC `n2:num` w82n_n2w8) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `n1 <= 256 EXP 8 - 1 /\ n2 <= 256 EXP 8 - 1` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `n1 < 256 EXP 8` THEN UNDISCH_TAC `n2 < 256 EXP 8` THEN
      CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
      ASM_REWRITE_TAC[] THEN MESON_TAC[]];
    DISCH_THEN SUBST_ALL_TAC THEN ASM_REWRITE_TAC[]]);;

let WORD_n2w8_UNICITY_L = prove
 (`!n1 n2 f. n1 < 256 EXP 8 /\ LIST_TYPE ml_WORD (n2w8 n1) f ==>
             (LIST_TYPE ml_WORD (n2w8 n2) f /\ n2 < 256 EXP 8 <=> n1 = n2)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [STRIP_TAC THEN
    SUBGOAL_THEN `n2w8 n1 = n2w8 n2` ASSUME_TAC THENL
     [MATCH_MP_TAC BAS1AUX_LIST_WORD_UNIQUE THEN EXISTS_TAC `f:v` THEN
      ASM_REWRITE_TAC[];
      ASM_MESON_TAC[n2w8_UNICITY_R]];
    DISCH_THEN SUBST_ALL_TAC THEN ASM_REWRITE_TAC[]]);;

(* n2w2_spec, w22n_spec: CF, MarshallingProg_part2.ml (M10) *)

finalise_translation ();;
