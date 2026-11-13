(* ========================================================================= *)
(* string4: port of HOL4 src/string/stringScript.sml (the HOL4 library of    *)
(* CakeML v3479): characters and strings.                                    *)
(* "A theory of 8-bit characters and strings built from them."               *)
(*                                                                           *)
(* HOL Light's char is the datatype ASCII b7 b6 b5 b4 b3 b2 b1 b0 of         *)
(* lists.ml (the first argument is the most significant bit, as in the       *)
(* string literals of the HOL Light parser) and string = char list, as in    *)
(* HOL4.  ORD and CHR are defined here, with HOL4's bijection theorems       *)
(* (CHR n for n >= 256 is unspecified in HOL4; here it is CHR (n MOD 256)).  *)
(* A HOL4 character literal #"a" is CHR 97 (that is what HOL4's parser       *)
(* makes of it).  HOL4 overloads with no constant of their own:              *)
(*   STRING = CONS   EMPTYSTRING = []   STRCAT = APPEND   STRLEN = LENGTH    *)
(*   CONCAT = FLAT   c1 < c2 (chars) = char_lt   s1 < s2 (strings) =         *)
(*   string_lt (likewise <=, >, >=).                                         *)
(* IMPLODE and EXPLODE are constants (identities on char lists) as in HOL4.  *)
(* Helper lemmas that are not HOL4 theorems have the prefix LSTRAUX_.        *)
(* ========================================================================= *)

needs "hol4/vocab.ml";;

prioritize_num();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* ORD and CHR.                                                              *)
(* ------------------------------------------------------------------------- *)

let ORD_DEF = new_recursive_definition char_RECURSION
  `!a7 a6 a5 a4 a3 a2 a1 a0.
     ORD (ASCII a7 a6 a5 a4 a3 a2 a1 a0) =
     128 * bitval a7 + 64 * bitval a6 + 32 * bitval a5 + 16 * bitval a4 +
     8 * bitval a3 + 4 * bitval a2 + 2 * bitval a1 + bitval a0`;;

let CHR_DEF = new_definition
  `CHR n =
     ASCII (ODD (n DIV 128)) (ODD (n DIV 64)) (ODD (n DIV 32)) (ODD (n DIV 16))
           (ODD (n DIV 8)) (ODD (n DIV 4)) (ODD (n DIV 2)) (ODD n)`;;

let LSTRAUX_MOD_STEP = prove
 (`!n k. n MOD (2 * k) = k * (n DIV k) MOD 2 + n MOD k`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [MULT_SYM] THEN
  REWRITE_TAC[MOD_MULT_MOD]);;

let LSTRAUX_ORD_CHR_MOD = prove
 (`!n. ORD (CHR n) = n MOD 256`,
  GEN_TAC THEN REWRITE_TAC[CHR_DEF; ORD_DEF; BITVAL_ODD] THEN
  REWRITE_TAC(map (fun k -> CONV_RULE NUM_REDUCE_CONV
     (SPECL [`n:num`; mk_small_numeral k] LSTRAUX_MOD_STEP))
     [128;64;32;16;8;4;2]));;

(* the 256 characters one by one                                             *)

let CHR_ORD = prove
 (`!a. CHR (ORD a) = a`,
  MATCH_MP_TAC char_INDUCT THEN REWRITE_TAC[FORALL_BOOL_THM] THEN
  REWRITE_TAC[ORD_DEF; CHR_DEF; BITVAL_CLAUSES] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let ORD_BOUND = prove
 (`!c. ORD c < 256`,
  GEN_TAC THEN ONCE_REWRITE_TAC[GSYM CHR_ORD] THEN
  REWRITE_TAC[LSTRAUX_ORD_CHR_MOD; MOD_LT_EQ] THEN ARITH_TAC);;

let ORD_CHR_RWT = prove
 (`!r. r < 256 ==> ORD (CHR r) = r`,
  SIMP_TAC[LSTRAUX_ORD_CHR_MOD; MOD_LT]);;

let ORD_CHR = prove
 (`!r. r < 256 <=> ORD (CHR r) = r`,
  MESON_TAC[ORD_CHR_RWT; ORD_BOUND]);;

let ORD_11 = prove
 (`!a a'. ORD a = ORD a' <=> a = a'`,
  MESON_TAC[CHR_ORD]);;

let CHR_11 = prove
 (`!r r'. r < 256 ==> r' < 256 ==> (CHR r = CHR r' <=> r = r')`,
  MESON_TAC[ORD_CHR_RWT]);;

let ORD_ONTO = prove
 (`!r. r < 256 <=> ?a. r = ORD a`,
  MESON_TAC[ORD_CHR_RWT; ORD_BOUND]);;

let CHR_ONTO = prove
 (`!a. ?r. a = CHR r /\ r < 256`,
  MESON_TAC[CHR_ORD; ORD_BOUND]);;

let char_nchotomy = prove
 (`!c. ?n. c = CHR n`,
  MESON_TAC[CHR_ORD]);;

let ranged_char_nchotomy = prove
 (`!c. ?n. c = CHR n /\ n < 256`,
  MESON_TAC[CHR_ORD; ORD_BOUND]);;

(* ------------------------------------------------------------------------- *)
(* Character classes, case conversion, orders.                               *)
(* ------------------------------------------------------------------------- *)

let isLower_def = new_definition
  `isLower c <=> 97 <= ORD c /\ ORD c <= 122`;;

let isUpper_def = new_definition
  `isUpper c <=> 65 <= ORD c /\ ORD c <= 90`;;

let isDigit_def = new_definition
  `isDigit c <=> 48 <= ORD c /\ ORD c <= 57`;;

let isAlpha_def = new_definition
  `isAlpha c <=> isLower c \/ isUpper c`;;

let isHexDigit_def = new_definition
  `isHexDigit c <=> 48 <= ORD c /\ ORD c <= 57 \/
                    97 <= ORD c /\ ORD c <= 102 \/
                    65 <= ORD c /\ ORD c <= 70`;;

let isAlphaNum_def = new_definition
  `isAlphaNum c <=> isAlpha c \/ isDigit c`;;

let isPrint_def = new_definition
  `isPrint c <=> 32 <= ORD c /\ ORD c < 127`;;

let isAlphaNum_isPrint = prove
 (`!x. isAlphaNum x ==> isPrint x`,
  REWRITE_TAC[isAlphaNum_def; isAlpha_def; isLower_def; isUpper_def;
              isDigit_def; isPrint_def] THEN ARITH_TAC);;

let isHexDigit_isAlphaNum = prove
 (`!x. isHexDigit x ==> isAlphaNum x`,
  REWRITE_TAC[isAlphaNum_def; isAlpha_def; isLower_def; isUpper_def;
              isDigit_def; isHexDigit_def] THEN ARITH_TAC);;

let isHexDigit_isPrint = prove
 (`!x. isHexDigit x ==> isPrint x`,
  MESON_TAC[isAlphaNum_isPrint; isHexDigit_isAlphaNum]);;

let isSpace_def = new_definition
  `isSpace c <=> ORD c = 32 \/ 9 <= ORD c /\ ORD c <= 13`;;

let isGraph_def = new_definition
  `isGraph c <=> isPrint c /\ ~isSpace c`;;

let isPunct_def = new_definition
  `isPunct c <=> isGraph c /\ ~isAlphaNum c`;;

let isAscii_def = new_definition
  `isAscii c <=> ORD c <= 127`;;

let isCntrl_def = new_definition
  `isCntrl c <=> ORD c < 32 \/ 127 <= ORD c`;;

let toLower_def = new_definition
  `toLower c = if isUpper c then CHR (ORD c + 32) else c`;;

let toUpper_def = new_definition
  `toUpper c = if isLower c then CHR (ORD c - 32) else c`;;

let char_lt_def = new_definition
  `char_lt a b <=> ORD a < ORD b`;;

let char_le_def = new_definition
  `char_le a b <=> ORD a <= ORD b`;;

let char_gt_def = new_definition
  `char_gt a b <=> ORD a > ORD b`;;

let char_ge_def = new_definition
  `char_ge a b <=> ORD a >= ORD b`;;

let CHAR_EQ_THM = prove
 (`!c1 c2. c1 = c2 <=> ORD c1 = ORD c2`,
  MESON_TAC[ORD_11]);;

let CHAR_INDUCT_THM = prove
 (`!P. (!n. n < 256 ==> P (CHR n)) ==> !c. P c`,
  MESON_TAC[CHR_ORD; ORD_BOUND]);;

let char_size_def = new_definition
  `char_size (c:char) = 0`;;

let UNIV_IMAGE_CHR_count_256 = prove
 (`(UNIV:char->bool) = IMAGE CHR (count 256)`,
  REWRITE_TAC[EXTENSION; IN_UNIV; IN_IMAGE; count_DEF; IN_ELIM_THM] THEN
  MESON_TAC[ranged_char_nchotomy]);;

let FINITE_UNIV_char = prove
 (`FINITE (UNIV:char->bool)`,
  REWRITE_TAC[UNIV_IMAGE_CHR_count_256; count_DEF] THEN
  MATCH_MP_TAC FINITE_IMAGE THEN REWRITE_TAC[FINITE_NUMSEG_LT]);;

let RC_char_lt = prove
 (`RC char_lt = char_le`,
  REWRITE_TAC[FUN_EQ_THM; RC_CASES; char_lt_def; char_le_def; LE_LT] THEN
  MESON_TAC[ORD_11]);;

let WF_char_lt = prove
 (`WF char_lt`,
  SUBGOAL_THEN `char_lt = MEASURE ORD` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; char_lt_def; MEASURE]; REWRITE_TAC[WF_MEASURE]]);;

(* ------------------------------------------------------------------------- *)
(* TOKENS and FIELDS.  HOL4 defines them with let (l,r) = SPLITP P (h::t)    *)
(* in ...; the kit loses the guard NULL l of a recursive call inside such a  *)
(* match arm (and TL [] is unspecified in HOL Light), so the definitions     *)
(* are made with FST and SND and the HOL4 equations are proved from them.    *)
(* ------------------------------------------------------------------------- *)

let LSTRAUX_SPLITP_MONO = prove
 (`!(P:char->bool) l. LENGTH (SND (SPLITP P l)) <= LENGTH l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[SPLITP_DEF; LENGTH; LE_REFL] THEN
  COND_CASES_TAC THEN REWRITE_TAC[LENGTH; LE_REFL] THEN ASM_ARITH_TAC);;

let LSTRAUX_SPLITP_TC_TAC =
  REWRITE_TAC(o_THM::WF_REL_THMS) THEN REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`P:char->bool`; `t:char list`] LSTRAUX_SPLITP_MONO) THEN
  REWRITE_TAC[SPLITP_DEF] THEN
  COND_CASES_TAC THEN REWRITE_TAC[NULL; FST; SND; TL; LENGTH] THEN
  STRUCT_CASES_TAC(ISPEC `SND (SPLITP (P:char->bool) t)` list_CASES) THEN
  REWRITE_TAC[NULL; TL; LENGTH] THEN ARITH_TAC;;

let LSTRAUX_TOKENS_FST_SND = cake_def_wf
  `measure (LENGTH o (SND:(char->bool)#(char list)->char list))`
  LSTRAUX_SPLITP_TC_TAC
  `(TOKENS P ([]:char list) = []) /\
   (TOKENS P (CONS h t) =
      if NULL (FST (SPLITP P (CONS h t)))
      then TOKENS P (TL (SND (SPLITP P (CONS h t))))
      else CONS (FST (SPLITP P (CONS h t)))
                (TOKENS P (SND (SPLITP P (CONS h t)))))`;;

let LSTRAUX_FIELDS_FST_SND = cake_def_wf
  `measure (LENGTH o (SND:(char->bool)#(char list)->char list))`
  LSTRAUX_SPLITP_TC_TAC
  `(FIELDS P ([]:char list) = [[]]) /\
   (FIELDS P (CONS h t) =
      if NULL (FST (SPLITP P (CONS h t)))
      then CONS [] (FIELDS P (TL (SND (SPLITP P (CONS h t)))))
      else if NULL (SND (SPLITP P (CONS h t))) then [FST (SPLITP P (CONS h t))]
      else CONS (FST (SPLITP P (CONS h t)))
                (FIELDS P (TL (SND (SPLITP P (CONS h t))))))`;;

let LSTRAUX_PAIR_CASE_FST_SND = prove
 (`!(p:A#B) (f:A->B->C). pair_CASE p f = f (FST p) (SND p)`,
  REWRITE_TAC[FORALL_PAIR_THM; pair_CASE]);;

let TOKENS_def = prove
 (CASE_TERM `(!P. TOKENS P ([]:char list) = []) /\
   (!P h t. TOKENS P (CONS h t) =
      match SPLITP P (CONS h t) with (l,r) ->
        if NULL l then TOKENS P (TL r) else CONS l (TOKENS P r))`,
  REWRITE_TAC[LSTRAUX_PAIR_CASE_FST_SND] THEN
  REWRITE_TAC[LSTRAUX_TOKENS_FST_SND]);;

let FIELDS_def = prove
 (CASE_TERM `(!P. FIELDS P ([]:char list) = [[]]) /\
   (!P h t. FIELDS P (CONS h t) =
      match SPLITP P (CONS h t) with (l,r) ->
        if NULL l then CONS [] (FIELDS P (TL r))
        else if NULL r then [l] else CONS l (FIELDS P (TL r)))`,
  REWRITE_TAC[LSTRAUX_PAIR_CASE_FST_SND] THEN
  REWRITE_TAC[LSTRAUX_FIELDS_FST_SND]);;

let TOKENS_ind = prove
 (`!P'. (!P. P' P ([]:char list)) /\
        (!P h t. (!l r. (l,r) = SPLITP P (CONS h t) /\ NULL l ==> P' P (TL r)) /\
                 (!l r. (l,r) = SPLITP P (CONS h t) /\ ~NULL l ==> P' P r)
                 ==> P' P (CONS h t))
        ==> !v v1. P' v v1`,
  GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC (cake_ind "TOKENS") THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  CONJ_TAC THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) ASSUME_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FST; SND]) THEN ASM_MESON_TAC[]);;

let FIELDS_ind = prove
 (`!P'. (!P. P' P ([]:char list)) /\
        (!P h t. (!l r. (l,r) = SPLITP P (CONS h t) /\ NULL l ==> P' P (TL r)) /\
                 (!l r. (l,r) = SPLITP P (CONS h t) /\ ~NULL l /\ ~NULL r
                        ==> P' P (TL r))
                 ==> P' P (CONS h t))
        ==> !v v1. P' v v1`,
  GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC (cake_ind "FIELDS") THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  CONJ_TAC THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) ASSUME_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FST; SND]) THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* IMPLODE and EXPLODE (identities, as string = char list).                  *)
(* ------------------------------------------------------------------------- *)

let IMPLODE_def = new_recursive_definition list_RECURSION
  `(IMPLODE [] = []) /\
   (!c cs. IMPLODE (CONS (c:char) cs) = CONS c (IMPLODE cs))`;;

let EXPLODE_def = new_recursive_definition list_RECURSION
  `(EXPLODE [] = []) /\
   (!c s. EXPLODE (CONS (c:char) s) = CONS c (EXPLODE s))`;;

let IMPLODE_EXPLODE_I = prove
 (`!s. EXPLODE s = s /\ IMPLODE s = s`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[IMPLODE_def; EXPLODE_def]);;

let IMPLODE_EXPLODE = prove
 (`!s. IMPLODE (EXPLODE s) = s`,
  REWRITE_TAC[IMPLODE_EXPLODE_I]);;

let EXPLODE_IMPLODE = prove
 (`!cs. EXPLODE (IMPLODE cs) = cs`,
  REWRITE_TAC[IMPLODE_EXPLODE_I]);;

let EXPLODE_ONTO = prove
 (`!cs. ?s. cs = EXPLODE s`,
  MESON_TAC[IMPLODE_EXPLODE_I]);;

let IMPLODE_ONTO = prove
 (`!s. ?cs. s = IMPLODE cs`,
  MESON_TAC[IMPLODE_EXPLODE_I]);;

let EXPLODE_11 = prove
 (`!s1 s2. EXPLODE s1 = EXPLODE s2 <=> s1 = s2`,
  REWRITE_TAC[IMPLODE_EXPLODE_I]);;

let IMPLODE_11 = prove
 (`!cs1 cs2. IMPLODE cs1 = IMPLODE cs2 <=> cs1 = cs2`,
  REWRITE_TAC[IMPLODE_EXPLODE_I]);;

let STRING_ACYCLIC = prove
 (`!(s:string) c. ~(CONS c s = s) /\ ~(s = CONS c s)`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[NOT_CONS_NIL; CONS_11] THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* TOKENS lemmas.                                                            *)
(* ------------------------------------------------------------------------- *)

let LSTRAUX_SPLITP_APPEND = prove
 (`!(P:A->bool) l1 l2.
     SPLITP P (APPEND l1 l2) =
     if EX P l1 then (FST (SPLITP P l1), APPEND (SND (SPLITP P l1)) l2)
     else (APPEND l1 (FST (SPLITP P l2)), SND (SPLITP P l2))`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND; EX] THEN
  GEN_TAC THEN REWRITE_TAC[SPLITP_DEF] THEN
  ASM_CASES_TAC `(P:A->bool) h` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `EX (P:A->bool) t` THEN ASM_REWRITE_TAC[APPEND]);;

let LSTRAUX_SPLITP_NOT_EX = prove
 (`!(P:A->bool) l. ~EX P l ==> SPLITP P l = (l,[])`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[SPLITP_DEF; EX; DE_MORGAN_THM] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[]);;

let LSTRAUX_TOKENS_NIL_CLAUSE = CONJUNCT1 LSTRAUX_TOKENS_FST_SND;;

let LSTRAUX_TOKENS_CONS = prove
 (`!P h t. TOKENS P (CONS h t) =
     if P h then TOKENS P t
     else CONS (CONS h (FST (SPLITP P t))) (TOKENS P (SND (SPLITP P t)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LSTRAUX_TOKENS_FST_SND] THEN
  REWRITE_TAC[SPLITP_DEF] THEN ASM_CASES_TAC `(P:char->bool) h` THEN
  ASM_REWRITE_TAC[NULL; FST; SND; TL]);;

let TOKENS_APPEND = prove
 (`!P l1 x l2. P x ==>
     TOKENS P (APPEND l1 (CONS x l2)) = APPEND (TOKENS P l1) (TOKENS P l2)`,
  MATCH_MP_TAC (cake_ind "TOKENS") THEN CONJ_TAC THENL
   [SIMP_TAC[APPEND; LSTRAUX_TOKENS_CONS; LSTRAUX_TOKENS_NIL_CLAUSE]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[SPLITP_DEF] THEN
  ASM_CASES_TAC `(P:char->bool) h` THEN
  ASM_REWRITE_TAC[NULL; FST; SND; TL; APPEND; LSTRAUX_TOKENS_CONS] THEN
  DISCH_TAC THEN REPEAT STRIP_TAC THEN REWRITE_TAC[LSTRAUX_SPLITP_APPEND] THEN
  ASM_CASES_TAC `EX (P:char->bool) t` THEN ASM_SIMP_TAC[FST; SND] THEN
  ASM_SIMP_TAC[LSTRAUX_SPLITP_NOT_EX; SPLITP_DEF; APPEND_NIL; FST; SND;
               LSTRAUX_TOKENS_CONS; LSTRAUX_TOKENS_NIL_CLAUSE; APPEND]);;

let TOKENS_NIL = prove
 (`!f ls. TOKENS f ls = [] <=> ALL f ls`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[LSTRAUX_TOKENS_NIL_CLAUSE; ALL; LSTRAUX_TOKENS_CONS] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[NOT_CONS_NIL]);;

(* ------------------------------------------------------------------------- *)
(* More rewrites for IMPLODE and EXPLODE; prefixes.                          *)
(* ------------------------------------------------------------------------- *)

let IMPLODE_EQ_EMPTYSTRING = prove
 (`!l. (IMPLODE l = [] <=> l = []) /\ ([] = IMPLODE l <=> l = [])`,
  REWRITE_TAC[IMPLODE_EXPLODE_I] THEN MESON_TAC[]);;

let EXPLODE_EQ_NIL = prove
 (`!s. (EXPLODE s = [] <=> s = []) /\ ([] = EXPLODE s <=> s = [])`,
  REWRITE_TAC[IMPLODE_EXPLODE_I] THEN MESON_TAC[]);;

let isPREFIX_STRCAT = prove
 (`!s1 s2:string. isPREFIX s1 s2 <=> ?s3. s2 = APPEND s1 s3`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[isPREFIX; APPEND] THENL
   [MESON_TAC[]; ALL_TAC] THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[list_CASE; NOT_CONS_NIL; CONS_11] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Orderings.                                                                *)
(* ------------------------------------------------------------------------- *)

let string_lt_def = cake_def
  `(string_lt s ([]:char list) <=> F) /\
   (string_lt [] (CONS (c:char) s) <=> T) /\
   (string_lt (CONS c1 s1) (CONS c2 s2) <=>
      char_lt c1 c2 \/ c1 = c2 /\ string_lt s1 s2)`;;

let string_le_def = new_definition
  `string_le s1 s2 <=> s1 = s2 \/ string_lt s1 s2`;;

let string_gt_def = new_definition
  `string_gt s1 s2 <=> string_lt s2 s1`;;

let string_ge_def = new_definition
  `string_ge s1 s2 <=> string_le s2 s1`;;

let string_lt_ind = prove
 (`!P:string->string->bool.
       (!s. P s []) /\ (!c s. P [] (CONS c s)) /\
       (!c1 s1 c2 s2. P s1 s2 ==> P (CONS c1 s1) (CONS c2 s2))
       ==> !v v1. P v v1`,
  GEN_TAC THEN STRIP_TAC THEN LIST_INDUCT_TAC THEN
  X_GEN_TAC `w:char list` THEN
  STRUCT_CASES_TAC(ISPEC `w:char list` list_CASES) THEN ASM_MESON_TAC[]);;

let string_lt_nonrefl = prove
 (`!s:string. ~string_lt s s`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[string_lt_def; char_lt_def; LT_REFL]);;

let string_lt_antisym = prove
 (`!s t:string. ~(string_lt s t /\ string_lt t s)`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[string_lt_def; char_lt_def; GSYM ORD_11] THEN
  ASM_MESON_TAC[LT_ANTISYM; LT_REFL]);;

let string_lt_cases = prove
 (`!s t:string. s = t \/ string_lt s t \/ string_lt t s`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[string_lt_def; char_lt_def; NOT_CONS_NIL; CONS_11] THEN
  REWRITE_TAC[GSYM ORD_11] THEN ASM_MESON_TAC[LT_CASES]);;

let string_lt_trans = prove
 (`!s1 s2 s3:string. string_lt s1 s2 /\ string_lt s2 s3 ==> string_lt s1 s3`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[string_lt_def; char_lt_def; GSYM ORD_11] THEN
  ASM_MESON_TAC[LT_TRANS]);;

(* ------------------------------------------------------------------------- *)
(* HOL4 [simp] theorems.                                                     *)
(* ------------------------------------------------------------------------- *)

let _ = cake_add_simps
  [CHR_ORD; ORD_CHR_RWT; CHR_11; FINITE_UNIV_char; WF_char_lt; IMPLODE_def;
   EXPLODE_def; IMPLODE_EXPLODE; EXPLODE_IMPLODE; EXPLODE_11; IMPLODE_11;
   IMPLODE_EQ_EMPTYSTRING; EXPLODE_EQ_NIL];;
