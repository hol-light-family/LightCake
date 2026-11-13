(* ========================================================================= *)
(* simpleSexp: port of HOL4 examples/formal-languages/context-free/         *)
(* simpleSexpScript.sml (HOL4 library used by CakeML v3479).                *)
(* Simple s-expressions: symbols, numbers, strings and conses.               *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - The type sexp is simpleSexp_sexp (mlsexp has its own type sexp), so the *)
(*   HOL4 names sexp_size, sexp_CASE, sexp_11, sexp_size_def are             *)
(*   simpleSexp_sexp_size, simpleSexp_sexp_CASE, simpleSexp_sexp_11,         *)
(*   simpleSexp_sexp_size_def.  The constructors keep their names.          *)
(* - HOL4's overload nil (SX_SYM "nil") is the constant nil with nil_def    *)
(*   (a simp rule); the theorems below are stated with SX_SYM "nil", the    *)
(*   term HOL4 really has.  HOL4's numeral form 5s is SX_NUM 5.              *)
(* - HOL4 strip_sxcons_thm is simpleSexp_strip_sxcons_thm (fromSexp has     *)
(*   its own strip_sxcons_thm).                                              *)
(* - Character literals #"(" are CHR 40 (string4.ml).                        *)
(* - Not ported (not used by CakeML): the grammar sexpG of grammarLib and   *)
(*   the parse tree functions ptree_*; the type sexpNT of its nonterminals  *)
(*   (used by simpleSexpPEG) is defined with HOL4's constructor order.     *)
(* ========================================================================= *)

needs "hol4/vocab.ml";;
needs "hol4/string4.ml";;

type_invention_error := true;;

let simpleSexp_sexp_INDUCT,simpleSexp_sexp_RECURSION = cake_type
  "simpleSexp_sexp = SX_CONS simpleSexp_sexp simpleSexp_sexp
                   | SX_SYM string
                   | SX_NUM num
                   | SX_STR string";;

(* HOL4: sexp_11, sexp_distinct, sexp_case_def, sexp_nchotomy *)

let simpleSexp_sexp_11 = injectivity "simpleSexp_sexp";;

let simpleSexp_sexp_distinct = distinctness "simpleSexp_sexp";;

let simpleSexp_sexp_case_def = case_def "simpleSexp_sexp";;

let simpleSexp_sexp_nchotomy = cases "simpleSexp_sexp";;

(* HOL4: Overload nil = SX_SYM "nil" *)

let nil_def = new_definition `nil = SX_SYM "nil"`;;

let valid_first_symchar_def = new_definition
  `valid_first_symchar c <=>
     isGraph c /\ ~(c IN {CHR 39, CHR 40, CHR 41, CHR 46, CHR 34}) /\
     ~isDigit c`;;

let valid_symchar_def = new_definition
  `valid_symchar c <=> isGraph c /\ ~(c IN {CHR 39, CHR 40, CHR 41})`;;

let valid_symbol_def = cake_def
  `(valid_symbol "" <=> F) /\
   (valid_symbol (CONS c cs) <=> valid_first_symchar c /\ ALL valid_symchar cs)`;;

let valid_sexp_def = cake_def
  `(valid_sexp (SX_SYM s) <=> valid_symbol s) /\
   (valid_sexp (SX_CONS s1 s2) <=> valid_sexp s1 /\ valid_sexp s2) /\
   (valid_sexp (SX_STR s) <=> ALL isPrint s) /\
   (valid_sexp x <=> T)`;;

let arb_sexp_def = new_definition `arb_sexp = SX_NUM 0`;;

let destSXNUM_def = cake_def
  `(destSXNUM (SX_NUM n) = n) /\ (destSXNUM x = 0)`;;

let destSXSYM_def = cake_def
  `(destSXSYM (SX_SYM s) = s) /\ (destSXSYM x = "")`;;

let destSXCONS_def = cake_def
  `(destSXCONS (SX_CONS a d) = (a,d)) /\
   (destSXCONS x = (arb_sexp,arb_sexp))`;;

let strip_sxcons_def = cake_def
  `strip_sxcons s =
     match s with
       SX_CONS h t -> OPTION_MAP (CONS h) (strip_sxcons t)
     | SX_SYM s -> if s = "nil" then SOME [] else NONE
     | _ -> NONE`;;

let strip_sxcons_ind = prove
 (`!P. (!s. (!h t. s = SX_CONS h t ==> P t) ==> P s) ==> !v. P v`,
  GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC simpleSexp_sexp_INDUCT THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[simpleSexp_sexp_11; simpleSexp_sexp_distinct] THEN
  ASM_MESON_TAC[]);;

(* HOL4: strip_sxcons_thm *)

let simpleSexp_strip_sxcons_thm = prove
 (`(!n. strip_sxcons (SX_NUM n) = NONE) /\
   (!s. strip_sxcons (SX_SYM s) = if s = "nil" then SOME [] else NONE) /\
   (!s. strip_sxcons (SX_STR s) = NONE) /\
   (!h t. strip_sxcons (SX_CONS h t) = OPTION_MAP (CONS h) (strip_sxcons t))`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [strip_sxcons_def] THEN
  REWRITE_TAC[simpleSexp_sexp_case_def]);;

let sxMEM_def = new_definition
  `sxMEM e s <=> ?l. strip_sxcons s = SOME l /\ MEM e l`;;

(* HOL4: sexp_size_def (char_size is \c. 0, as in HOL4) *)

let simpleSexp_sexp_size_def = prove
 (`(!a0 a1. simpleSexp_sexp_size (SX_CONS a0 a1) =
            1 + simpleSexp_sexp_size a0 + simpleSexp_sexp_size a1) /\
   (!a. simpleSexp_sexp_size (SX_SYM a) = 1 + list_size char_size a) /\
   (!a. simpleSexp_sexp_size (SX_NUM a) = 1 + a) /\
   (!a. simpleSexp_sexp_size (SX_STR a) = 1 + list_size char_size a)`,
  SUBGOAL_THEN `char_size = (\x:char. 0)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; char_size_def]; ALL_TAC] THEN
  REWRITE_TAC[type_size_def "simpleSexp_sexp"]);;

let sxMEM_sizelt = prove
 (`!s1 s2. sxMEM s1 s2 ==> simpleSexp_sexp_size s1 < simpleSexp_sexp_size s2`,
  GEN_TAC THEN REWRITE_TAC[sxMEM_def; LEFT_IMP_EXISTS_THM] THEN
  MATCH_MP_TAC simpleSexp_sexp_INDUCT THEN
  REWRITE_TAC[simpleSexp_strip_sxcons_thm; option_DISTINCT] THEN REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`h:simpleSexp_sexp`; `t:simpleSexp_sexp`] THEN
    STRIP_TAC THEN X_GEN_TAC `l:simpleSexp_sexp list` THEN
    MP_TAC(ISPEC `strip_sxcons t` (cases "option")) THEN
    DISCH_THEN(DISJ_CASES_THEN2
      (fun th -> REWRITE_TAC[th; OPTION_MAP_DEF; option_DISTINCT])
      (X_CHOOSE_THEN `a:simpleSexp_sexp list`
        (fun th -> ASSUME_TAC th THEN
                   REWRITE_TAC[th; OPTION_MAP_DEF; option_INJ]))) THEN
    REWRITE_TAC[IMP_CONJ] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[MEM; simpleSexp_sexp_size_def] THEN
    STRIP_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `a:simpleSexp_sexp list`) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    GEN_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC[option_DISTINCT; option_INJ] THEN
    MESON_TAC[MEM]]);;

let dstrip_sexp_def = cake_def
  `(dstrip_sexp (SX_CONS sym args) =
      match sym with
        SX_SYM s -> OPTION_MAP (\t. (s,t)) (strip_sxcons args)
      | _ -> NONE) /\
   (dstrip_sexp _ = NONE)`;;

(* ------------------------------------------------------------------------- *)
(* The nonterminals of HOL4's grammar sexpG (made there by grammarLib's      *)
(* mk_grammar_def), used by simpleSexpPEG.                                   *)
(* ------------------------------------------------------------------------- *)

let sexpNT_INDUCT,sexpNT_RECURSION = cake_type
  "sexpNT = sxnt_symchars | sxnt_symchar | sxnt_strcontents | sxnt_strchar
          | sxnt_sexpsym | sxnt_sexpstr | sxnt_sexpseq | sxnt_sexpnum
          | sxnt_sexp0 | sxnt_sexp | sxnt_normstrchar | sxnt_grabWS
          | sxnt_first_symchar | sxnt_escapedstrchar | sxnt_escapablechar
          | sxnt_digit | sxnt_WSsexp | sxnt_WS";;

(* ------------------------------------------------------------------------- *)
(* HOL4 [simp] theorems.                                                     *)
(* ------------------------------------------------------------------------- *)

let _ = cake_add_simps
  [nil_def; valid_first_symchar_def; valid_symchar_def; valid_symbol_def;
   valid_sexp_def; simpleSexp_strip_sxcons_thm; simpleSexp_sexp_size_def];;
