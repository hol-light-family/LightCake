(* ========================================================================= *)
(* simpleSexpParse: port of HOL4 examples/formal-languages/context-free/    *)
(* simpleSexpParseScript.sml (HOL4 library used by CakeML v3479).           *)
(* Printing and parsing of the s-expressions of simpleSexp.                  *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - CakeML uses only the definitions print_sexp and parse_sexp: they are    *)
(*   ported with the definitions they rest on (escape_string,                *)
(*   print_space_separated, strip_dot), the strip_dot theorems (two of them  *)
(*   prove the termination of print_sexp) and print_space_separated_cons.   *)
(*   Not ported: option_sequence and the theorems about the parser (up to    *)
(*   parse_print), which CakeML does not use.                                *)
(* - toString is num_to_dec_string (ASCIInumbers.ml); ++ is APPEND (left     *)
(*   associated as in HOL4); character literals #"(" are CHR 40; the         *)
(*   literal patterns of escape_string are equality tests in order, as HOL4  *)
(*   compiles them; let (ls,n) = strip_dot s in t is a match (pair_CASE).    *)
(* - Lemmas named LBMAPAUX_... are helpers of this unit (not HOL4 names).   *)
(* ========================================================================= *)

needs "hol4/vocab.ml";;
needs "hol4/ASCIInumbers.ml";;
needs "hol4/pegexec.ml";;
needs "hol4/simpleSexp.ml";;
needs "hol4/simpleSexpPEG.ml";;

type_invention_error := true;;

let parse_sexp_def = new_definition
  `parse_sexp (s:(char#locs)list) =
     OPTION_BIND (pegparse sexpPEG s)
       (\(rest,sx). OPTION_IGNORE_BIND (OPTION_GUARD (rest = []))
                                       (SOME (FST sx)))`;;

let escape_string_def = cake_def
  `escape_string s =
     match s with
       [] -> []
     | CONS c s ->
         if c = CHR 92 then APPEND "\\\\" (escape_string s)
         else if c = CHR 34 then APPEND "\\\"" (escape_string s)
         else CONS c (escape_string s)`;;

let print_space_separated_def = cake_def
  `(print_space_separated [] = "") /\
   (print_space_separated [x] = x) /\
   (print_space_separated (CONS x xs) =
      APPEND (APPEND x " ") (print_space_separated xs))`;;

let print_space_separated_cons = prove
 (`!x xs. print_space_separated (CONS x xs) =
          APPEND x (if NULL xs then "" else APPEND " " (print_space_separated xs))`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[print_space_separated_def; NULL; APPEND_NIL; APPEND_ASSOC]);;

let strip_dot_def = new_recursive_definition simpleSexp_sexp_RECURSION (CASE_TERM
  `(!n. strip_dot (SX_NUM n) = ([], SOME (SX_NUM n))) /\
   (!s. strip_dot (SX_STR s) = ([], SOME (SX_STR s))) /\
   (!s. strip_dot (SX_SYM s) =
          if s = "nil" then ([], NONE) else ([], SOME (SX_SYM s))) /\
   (!a d. strip_dot (SX_CONS a d) =
            match strip_dot d with (ls,n) -> (CONS a ls,n))`);;

let LBMAPAUX_strip_dot_CONS = prove
 (`!a d. strip_dot (SX_CONS a d) =
         (CONS a (FST (strip_dot d)), SND (strip_dot d))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[strip_dot_def] THEN
  MP_TAC(ISPEC `strip_dot d` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `ls:simpleSexp_sexp list`
    (X_CHOOSE_THEN `n:simpleSexp_sexp option` SUBST1_TAC)) THEN
  REWRITE_TAC[pair_CASE]);;

(* induction on the s-expression, with strip_dot d = (ls0,n0) in the case   *)
(* SX_CONS a d                                                               *)

let LBMAPAUX_SD_TAC =
  MATCH_MP_TAC simpleSexp_sexp_INDUCT THEN
  REWRITE_TAC[strip_dot_def; LBMAPAUX_strip_dot_CONS] THEN
  REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`a:simpleSexp_sexp`; `d:simpleSexp_sexp`] THEN
    MP_TAC(ISPEC `strip_dot d` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `ls0:simpleSexp_sexp list`
      (X_CHOOSE_THEN `n0:simpleSexp_sexp option`
        (fun th -> ASSUME_TAC th THEN REWRITE_TAC[th])));
    ALL_TAC; ALL_TAC; ALL_TAC];;

let LBMAPAUX_SUBST_EQS_TAC =
  DISCH_THEN(fun th -> MAP_EVERY (SUBST1_TAC o SYM) (CONJUNCTS th));;

let strip_dot_strip_sxcons = prove
 (`!s ls. strip_sxcons s = SOME ls <=> strip_dot s = (ls,NONE)`,
  LBMAPAUX_SD_TAC THEN
  REWRITE_TAC[simpleSexp_strip_sxcons_thm; option_DISTINCT; PAIR_EQ] THENL
   [STRIP_TAC THEN GEN_TAC THEN
    MP_TAC(ISPEC `strip_sxcons d` (cases "option")) THEN
    DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC
      (X_CHOOSE_TAC `l0:simpleSexp_sexp list`)) THEN
    ASM_REWRITE_TAC[OPTION_MAP_DEF; option_DISTINCT; option_INJ] THEN
    ASM_MESON_TAC[option_DISTINCT; option_INJ];
    REPEAT GEN_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ] THEN MESON_TAC[]]);;

let strip_dot_last_sizeleq = prove
 (`!x ls last. strip_dot x = (ls,SOME last)
               ==> simpleSexp_sexp_size last <= simpleSexp_sexp_size x`,
  LBMAPAUX_SD_TAC THEN REWRITE_TAC[PAIR_EQ; option_DISTINCT; option_INJ] THENL
   [STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`ls0:simpleSexp_sexp list`;
                                  `last:simpleSexp_sexp`]) THEN
    ASM_REWRITE_TAC[simpleSexp_sexp_size_def] THEN ARITH_TAC;
    REPEAT GEN_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC[PAIR_EQ; option_DISTINCT; option_INJ] THEN
    LBMAPAUX_SUBST_EQS_TAC THEN REWRITE_TAC[LE_REFL];
    REPEAT GEN_TAC THEN LBMAPAUX_SUBST_EQS_TAC THEN REWRITE_TAC[LE_REFL];
    REPEAT GEN_TAC THEN LBMAPAUX_SUBST_EQS_TAC THEN REWRITE_TAC[LE_REFL]]);;

let strip_dot_last_sizelt = prove
 (`!x ls last. strip_dot x = (ls,SOME last) /\ ~NULL ls
               ==> simpleSexp_sexp_size last < simpleSexp_sexp_size x`,
  LBMAPAUX_SD_TAC THEN REWRITE_TAC[PAIR_EQ; option_DISTINCT; option_INJ] THENL
   [STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`d:simpleSexp_sexp`; `ls0:simpleSexp_sexp list`;
                   `last:simpleSexp_sexp`] strip_dot_last_sizeleq) THEN
    ASM_REWRITE_TAC[simpleSexp_sexp_size_def] THEN ARITH_TAC;
    REPEAT GEN_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC[PAIR_EQ; option_DISTINCT; option_INJ] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
    ASM_MESON_TAC[NULL];
    REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
    ASM_MESON_TAC[NULL];
    REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
    ASM_MESON_TAC[NULL]]);;

let strip_dot_MEM_sizelt = prove
 (`!x ls n a. strip_dot x = (ls,n) /\ MEM a ls
              ==> simpleSexp_sexp_size a < simpleSexp_sexp_size x`,
  LBMAPAUX_SD_TAC THEN REWRITE_TAC[PAIR_EQ] THENL
   [STRIP_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_TAC THEN
    REWRITE_TAC[MEM; simpleSexp_sexp_size_def] THEN STRIP_TAC THENL
     [ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`ls0:simpleSexp_sexp list`;
                                  `n0:simpleSexp_sexp option`;
                                  `a':simpleSexp_sexp`]) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    REPEAT GEN_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[MEM];
    MESON_TAC[MEM];
    MESON_TAC[MEM]]);;

let strip_dot_valid_sexp = prove
 (CASE_TERM
  `!x ls n. strip_dot x = (ls,n) /\ valid_sexp x
            ==> ALL valid_sexp ls /\
                (match n with NONE -> T | SOME last -> valid_sexp last)`,
  LBMAPAUX_SD_TAC THEN REWRITE_TAC[PAIR_EQ; valid_sexp_def; IMP_CONJ] THENL
   [DISCH_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REPEAT DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`ls0:simpleSexp_sexp list`;
                                  `n0:simpleSexp_sexp option`]) THEN
    ASM_REWRITE_TAC[ALL] THEN MESON_TAC[];
    REPEAT GEN_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC[PAIR_EQ; IMP_CONJ] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[ALL; option_CASE; valid_sexp_def];
    REPEAT GEN_TAC THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[ALL; option_CASE; valid_sexp_def];
    REPEAT GEN_TAC THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[ALL; option_CASE; valid_sexp_def]]);;

(* ------------------------------------------------------------------------- *)
(* print_sexp (HOL4: WF_REL_TAC measure sexp_size; the termination          *)
(* conditions follow from strip_dot_MEM_sizelt and strip_dot_last_sizelt).  *)
(* ------------------------------------------------------------------------- *)

let LBMAPAUX_print_sexp_tc1 = prove
 (`!x ls n. (ls,n) = strip_dot x /\ LENGTH ls = 2
            ==> simpleSexp_sexp_size (EL 1 ls) < simpleSexp_sexp_size x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC strip_dot_MEM_sizelt THEN
  MAP_EVERY EXISTS_TAC [`ls:simpleSexp_sexp list`; `n:simpleSexp_sexp option`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MEM_EL THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let LBMAPAUX_print_sexp_tc2 = prove
 (`!x ls n y. (ls,n) = strip_dot x /\ MEM y ls
              ==> simpleSexp_sexp_size y < simpleSexp_sexp_size x`,
  MESON_TAC[strip_dot_MEM_sizelt]);;

let LBMAPAUX_print_sexp_tc3 = prove
 (`!a0 a1 ls last. (ls,SOME last) = strip_dot (SX_CONS a0 a1)
                   ==> simpleSexp_sexp_size last <
                       simpleSexp_sexp_size (SX_CONS a0 a1)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC strip_dot_last_sizelt THEN
  EXISTS_TAC `ls:simpleSexp_sexp list` THEN
  FIRST_ASSUM(MP_TAC o SYM) THEN REWRITE_TAC[LBMAPAUX_strip_dot_CONS; PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) ASSUME_TAC) THEN
  ASM_REWRITE_TAC[NULL]);;

let print_sexp_def = cake_def_wf `measure simpleSexp_sexp_size`
  (REWRITE_TAC[measure_THM] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
   ASM_MESON_TAC[LBMAPAUX_print_sexp_tc1; LBMAPAUX_print_sexp_tc2;
                 LBMAPAUX_print_sexp_tc3])
  `(print_sexp (SX_SYM s) = s) /\
   (print_sexp (SX_NUM n) = num_to_dec_string n) /\
   (print_sexp (SX_STR s) = APPEND (APPEND "\"" (escape_string s)) "\"") /\
   (print_sexp x =
      match strip_dot x with
        (ls,n0) ->
          match n0 with
            NONE ->
              if LENGTH ls = 2 /\ HD ls = SX_SYM "quote"
              then APPEND "'" (print_sexp (EL 1 ls))
              else APPEND (APPEND "(" (print_space_separated (MAP print_sexp ls)))
                          ")"
          | SOME last ->
              APPEND (APPEND (APPEND (APPEND "(" (print_space_separated
                                                    (MAP print_sexp ls)))
                                     " . ")
                             (print_sexp last))
                     ")")`;;

let print_sexp_ind = cake_ind "print_sexp";;

(* ------------------------------------------------------------------------- *)
(* HOL4 [simp] theorems.                                                     *)
(* ------------------------------------------------------------------------- *)

let _ = cake_add_simps [strip_dot_def];;
