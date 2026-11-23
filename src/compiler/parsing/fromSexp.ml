(* ========================================================================= *)
(* fromSexp: port of HOL4 compiler/parsing/fromSexpScript.sml (CakeML v3479).*)
(* Definitions of functions for conversion between an S-expression encoding *)
(* of the CakeML abstract syntax and the abstract syntax type itself.       *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - The s-expressions are simpleSexp_sexp (hol4/simpleSexp.ml): HOL4's      *)
(*   sexp_size is simpleSexp_sexp_size, nil is SX_SYM "nil", the list form   *)
(*   of a; b is SX_CONS a (SX_CONS b nil), and the numeral form is SX_NUM.  *)
(* - The option monad syntax of HOL4 is written out (comment below).        *)
(* - names.tsv: decode_test is fromSexp_decode_test, mem_size_lemma is      *)
(*   fromSexp_mem_size_lemma; HOL4's dec1_size is the kit's dec_size_aux1.  *)
(* - listsexp_def is eta-expanded (FOLDR f e l is ITLIST f l e).             *)
(* - opsexp and expsexp are made with sem1aux_def (many clauses); the        *)
(*   induction theorem of the six-function sexpexp_alt comes from            *)
(*   FSEXPAUX_MUTUAL_IND (the kit makes none for three or more functions).  *)
(* - Helpers that are not HOL4 theorems have the prefix FSEXPAUX_ (HOL4's   *)
(*   ML values type_ind, pat_ind, exp_ind, dec_ind are FSEXPAUX_type_ind,    *)
(*   FSEXPAUX_pat_ind, FSEXPAUX_exp_ind, FSEXPAUX_dec_ind).                  *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "hol4/simpleSexp.ml";;
needs "hol4/location.ml";;
needs "hol4/ASCIInumbers.ml";;
needs "hol4/numposrep.ml";;
needs "basis/pure/mlstring.ml";;
needs "semantics/ast.ml";;
needs "semantics/fpSem.ml";;
needs "semantics/sem1aux_tfl.ml";;

type_invention_error := true;;

(* HOL4 option_monadsyntax: do x <- m; r od is OPTION_BIND m (\x. r),     *)
(* do (a,b) <- m; r od is OPTION_BIND m (\p. match p with (a,b) -> r),    *)
(* assert b is OPTION_GUARD b, monad_unitbind (do m; r od) is            *)
(* OPTION_IGNORE_BIND, return is SOME, fail is NONE, ++ is OPTION_CHOICE  *)
(* (left associative), the applicative infix of HOL4 is OPTION_APPLY;    *)
(* the local overloads lift and guard b m are OPTION_MAP and              *)
(* OPTION_IGNORE_BIND (OPTION_GUARD b) m; lift2 (an overload of           *)
(* OPTION_MAP2 in HOL4) is OPTION_MAP2.  HOL4 nil is SX_SYM "nil", the     *)
(* mlstring literal of NONE is implode "NONE", a character literal is     *)
(* CHR n (#"\\" is CHR 92), Num is num_of_int, n2w is word, w2n is val.    *)

(* HOL4's srw_ss decides equations between string literals; the kit's     *)
(* simpset needs the injectivity of the character constructor for that    *)
(* when the strings have the same length                                   *)

let FSEXPAUX_ASCII_11 = injectivity "char";;
let _ = cake_add_simps [FSEXPAUX_ASCII_11];;

(* case splits on the free variables of the given types in the goal *)

let FSEXPAUX_SPLIT_TYPES_TAC (tys:hol_type list) : tactic =
  REPEAT (W(fun (asl,w) ->
    match filter (fun v -> mem (type_of v) tys) (frees w) with
      v::_ -> CASES_ON v
    | [] -> failwith "FSEXPAUX_SPLIT_TYPES_TAC"));;


(* TODO: this is duplicated in parserProgTheory *)

let monad_unitbind_assert = prove
 (`!b (x:A option). OPTION_IGNORE_BIND (OPTION_GUARD b) x =
                    if b then x else NONE`,
  GEN_TAC THEN CASES_ON `b:bool` THEN SIMP[]);;

(* TODO: move *)

let OPTION_APPLY_MAP3 = prove
 (`OPTION_APPLY (OPTION_APPLY (OPTION_MAP (f:A->B->C->D) x) y) z = SOME r <=>
   ?a b c. x = SOME a /\ y = SOME b /\ z = SOME c /\ f a b c = r`,
  CASES_ON `x:A option` THEN SIMP[] THEN
  CASES_ON `y:B option` THEN SIMP[] THEN
  CASES_ON `z:C option` THEN SIMP[] THEN MESON_TAC[]);;

let OPTION_APPLY_MAP4 = prove
 (`OPTION_APPLY (OPTION_APPLY (OPTION_APPLY (OPTION_MAP (f:A->B->C->D->E) x)
     y) z) t = SOME r <=>
   ?a b c d. x = SOME a /\ y = SOME b /\ z = SOME c /\ t = SOME d /\
             f a b c d = r`,
  CASES_ON `x:A option` THEN SIMP[] THEN
  CASES_ON `y:B option` THEN SIMP[] THEN
  CASES_ON `z:C option` THEN SIMP[] THEN
  CASES_ON `t:D option` THEN SIMP[] THEN MESON_TAC[]);;

(* HOL4 nil (an overload of SX_SYM "nil"), FOLDR f e l is ITLIST f l e *)

let FOLDR_SX_CONS_INJ = prove
 (`!l1 l2. ITLIST SX_CONS l1 (SX_SYM "nil") = ITLIST SX_CONS l2 (SX_SYM "nil")
           <=> l1 = l2`,
  LIST_INDUCT_TAC THENL
   [LIST_INDUCT_TAC THEN SIMP[ITLIST];
    LIST_INDUCT_TAC THEN SIMP[ITLIST]]);;

let strip_sxcons_11 = prove
 (`!s1 s2 x. strip_sxcons s1 = SOME x /\ strip_sxcons s2 = SOME x ==> s1 = s2`,
  MATCH_MP_TAC simpleSexp_sexp_INDUCT THEN REPEAT STRIP_TAC THEN
  CASES_ON `s2:simpleSexp_sexp` THEN GVS[] THEN
  REPEAT (FIRST_X_ASSUM (MP_TAC o check (is_cond o rand o lhand o concl))) THEN
  REPEAT COND_CASES_TAC THEN SIMP[] THEN ASM_MESON_TAC[]);;

let dstrip_sexp_size = prove
 (`!s sym args. dstrip_sexp s = SOME (sym,args) ==>
                !e. MEM e args ==> simpleSexp_sexp_size e < simpleSexp_sexp_size s`,
  GEN_TAC THEN CASES_ON `s:simpleSexp_sexp` THEN SIMP[dstrip_sexp_def] THEN
  CASES_ON `a0:simpleSexp_sexp` THEN SIMP[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `sxMEM e a1` (MP_TAC o MATCH_MP sxMEM_sizelt) THENL
   [REWRITE_TAC[sxMEM_def] THEN ASM_MESON_TAC[]; ARITH_TAC]);;

let dstrip_sexp_SOME = prove
 (`dstrip_sexp s = SOME x <=>
   ?sym sa args. s = SX_CONS (SX_SYM sym) sa /\ strip_sxcons sa = SOME args /\
                 x = (sym,args)`,
  CASES_ON `s:simpleSexp_sexp` THEN SIMP[dstrip_sexp_def] THEN
  CASES_ON `a0:simpleSexp_sexp` THEN SIMP[] THEN MESON_TAC[]);;

let strip_sxcons_SOME_NIL = prove
 (`strip_sxcons s = SOME [] <=> s = SX_SYM "nil"`,
  CASES_ON `s:simpleSexp_sexp` THEN SIMP[] THEN COND_CASES_TAC THEN SIMP[]);;
let _ = cake_add_simps [strip_sxcons_SOME_NIL];;

let strip_sxcons_EQ_CONS = prove
 (`strip_sxcons s = SOME (CONS h t) <=>
   ?s0. s = SX_CONS h s0 /\ strip_sxcons s0 = SOME t`,
  CASES_ON `s:simpleSexp_sexp` THEN SIMP[] THEN TRY COND_CASES_TAC THEN
  SIMP[] THEN MESON_TAC[]);;
let _ = cake_add_simps [strip_sxcons_EQ_CONS];;

(* HOL4 type_ind, pat_ind, exp_ind, dec_ind (ML values: the induction      *)
(* theorems of ast_t, pat, exp and dec with the list predicates EVERY P)   *)

let FSEXPAUX_type_ind = prove
 (`!P. (!s. P (Atvar s)) /\ (!a a'. P a /\ P a' ==> P (Atfun a a')) /\
       (!l. ALL P l ==> P (Attup l)) /\ (!l i. ALL P l ==> P (Atapp l i))
       ==> !a. P a`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC (ISPECL [`P:ast_t->bool`; `ALL (P:ast_t->bool)`] ast_t_INDUCT) THEN
  ASM_SIMP_TAC[ALL]);;

let FSEXPAUX_pat_ind = prove
 (`!P. P Pany /\ (!s. P (Pvar s)) /\ (!l. P (Plit l)) /\
       (!cn ps. ALL P ps ==> P (Pcon cn ps)) /\ (!p. P p ==> P (Pref p)) /\
       (!p i. P p ==> P (Pas p i)) /\ (!p t. P p ==> P (Ptannot p t))
       ==> !p. P p`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC (ISPECL [`P:pat->bool`; `ALL (P:pat->bool)`] pat_INDUCT) THEN
  ASM_SIMP_TAC[ALL]);;

let FSEXPAUX_exp_ind = prove
 (`!P. (!e. P e ==> P (Raise e)) /\
       (!e pes. P e /\ ALL (P o SND) pes ==> P (Handle e pes)) /\
       (!l. P (Lit l)) /\
       (!cn es. ALL P es ==> P (Con cn es)) /\
       (!v. P (Var v)) /\
       (!x e. P e ==> P (Fun x e)) /\
       (!op es. ALL P es ==> P (App op es)) /\
       (!lop e1 e2. P e1 /\ P e2 ==> P (Log lop e1 e2)) /\
       (!e1 e2 e3. P e1 /\ P e2 /\ P e3 ==> P (If e1 e2 e3)) /\
       (!e pes. P e /\ ALL (P o SND) pes ==> P (Mat e pes)) /\
       (!so e1 e2. P e1 /\ P e2 ==> P (Let so e1 e2)) /\
       (!funs e. ALL (P o SND o SND) funs /\ P e ==> P (Letrec funs e)) /\
       (!e t. P e ==> P (Tannot e t)) /\
       (!e l. P e ==> P (Lannot e l))
       ==> !e. P e`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC (ISPECL [`P:exp->bool`;
                  `ALL ((P:exp->bool) o SND o SND):(varN#varN#exp)list->bool`;
                  `((P:exp->bool) o SND o SND):varN#varN#exp->bool`;
                  `((P:exp->bool) o SND):varN#exp->bool`;
                  `ALL ((P:exp->bool) o SND):(pat#exp)list->bool`;
                  `((P:exp->bool) o SND):pat#exp->bool`;
                  `ALL (P:exp->bool)`] exp_INDUCT) THEN
  ASM_SIMP_TAC[ALL; o_THM]);;

let FSEXPAUX_dec_ind = prove
 (`!P. (!l p e. P (Dlet l p e)) /\ (!l funs. P (Dletrec l funs)) /\
       (!l td. P (Dtype l td)) /\ (!l ns x t. P (Dtabbrev l ns x t)) /\
       (!l x ts. P (Dexn l x ts)) /\ (!n ds. ALL P ds ==> P (Dmod n ds)) /\
       (!ds1 ds2. ALL P ds1 /\ ALL P ds2 ==> P (Dlocal ds1 ds2)) /\
       (!n. P (Denv n))
       ==> !d. P d`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC (ISPECL [`P:dec->bool`; `ALL (P:dec->bool)`] dec_INDUCT) THEN
  ASM_SIMP_TAC[ALL]);;

(* end TODO *)

(* character literals: #"\\" is CHR 92 (backslash); "0" is the string    *)
(* literal of HOL Light                                                    *)

let encode_control_def = cake_def
  `(encode_control "" = "") /\
   (encode_control (CONS c cs) =
      if c = CHR 92 then CONS c (CONS c (encode_control cs))
      else if isPrint c then CONS c (encode_control cs)
      else APPEND (CONS (CHR 92) (APPEND (if ORD c < 16 then "0" else "")
                                         (num_to_hex_string (ORD c))))
                  (encode_control cs))`;;

let decode_control_def = cake_def
  `(decode_control "" = SOME "") /\
   (decode_control (CONS c cs) =
      if c = CHR 92 then
        match cs with
          CONS (CHR 92) cs -> OPTION_MAP (CONS c) (decode_control cs)
        | CONS d1 (CONS d2 cs) ->
            OPTION_IGNORE_BIND
              (OPTION_GUARD
                 (isHexDigit d1 /\ isHexDigit d2 /\
                  (isAlpha d1 ==> isUpper d1) /\
                  (isAlpha d2 ==> isUpper d2) /\
                  ~isPrint (CHR (num_from_hex_string [d1; d2]))))
              (OPTION_MAP (CONS (CHR (num_from_hex_string [d1; d2])))
                          (decode_control cs))
        | _ -> NONE
      else OPTION_IGNORE_BIND (OPTION_GUARD (isPrint c))
             (OPTION_MAP (CONS c) (decode_control cs)))`;;

let decode_control_ind = cake_ind "decode_control";;

(* the string literal "0" is the character CHR 48 *)

let FSEXPAUX_STR0 = prove
 (`"0" = [CHR 48]`,
  REWRITE_TAC[CHR_DEF; CONS_11] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH]);;

(* the characters of a hexadecimal numeral *)

let FSEXPAUX_hex_string_lt16 = prove
 (`!n. n < 16 ==> num_to_hex_string n = [HEX n]`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[num_to_hex_string_def; n2s_def] THEN
  ONCE_REWRITE_TAC[n2l_def] THEN ASM_SIMP_TAC[MOD_LT; REVERSE; MAP; APPEND]);;

let FSEXPAUX_hex_string_lt256 = prove
 (`!n. 16 <= n /\ n < 256 ==>
       num_to_hex_string n = [HEX (n DIV 16); HEX (n MOD 16)]`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[num_to_hex_string_def; n2s_def] THEN
  ONCE_REWRITE_TAC[n2l_def] THEN
  SUBGOAL_THEN `n DIV 16 < 16` ASSUME_TAC THENL
   [ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[ARITH_RULE `16 <= n ==> ~(n < 16)`; ARITH_RULE `~(16 < 2)`] THEN
  ONCE_REWRITE_TAC[n2l_def] THEN ASM_SIMP_TAC[MOD_LT; REVERSE; MAP; APPEND]);;

let FSEXPAUX_num_from_hex_string2 = prove
 (`!d1 d2. num_from_hex_string [d1; d2] = 16 * (UNHEX d1 MOD 16) + UNHEX d2 MOD 16`,
  REWRITE_TAC[num_from_hex_string_def; s2n_def; REVERSE; APPEND; MAP; l2n_def] THEN
  ARITH_TAC);;

(* a hexadecimal digit that is not a lower case letter is HEX of its value *)

let FSEXPAUX_HEX_UNHEX = prove
 (`!c. isHexDigit c /\ (isAlpha c ==> isUpper c) ==> HEX (UNHEX c) = c`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[HEX_UNHEX; toUpper_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  POP_ASSUM MP_TAC THEN UNDISCH_TAC `isAlpha c ==> isUpper c` THEN
  REWRITE_TAC[isAlpha_def; isUpper_def; isLower_def] THEN ARITH_TAC);;

let FSEXPAUX_isHexDigit_not_backslash = prove
 (`!c. isHexDigit c ==> ~(c = CHR 92)`,
  GEN_TAC THEN REWRITE_TAC[isHexDigit_def] THEN
  DISCH_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
  POP_ASSUM MP_TAC THEN SIMP_TAC[ORD_CHR_RWT; ARITH]);;

let FSEXPAUX_hex_encode = prove
 (`!n. n < 256 ==>
       ?d1 d2. APPEND (if n < 16 then "0" else "") (num_to_hex_string n) = [d1; d2] /\
               isHexDigit d1 /\ isHexDigit d2 /\
               (isAlpha d1 ==> isUpper d1) /\ (isAlpha d2 ==> isUpper d2) /\
               num_from_hex_string [d1; d2] = n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FSEXPAUX_num_from_hex_string2] THEN
  ASM_CASES_TAC `n < 16` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[FSEXPAUX_STR0] THEN
    ASM_SIMP_TAC[FSEXPAUX_hex_string_lt16; APPEND] THEN
    MAP_EVERY EXISTS_TAC [`CHR 48`; `HEX n`] THEN
    ASM_SIMP_TAC[isHexDigit_HEX; UNHEX_HEX; UNHEX_def; MOD_LT] THEN
    SIMP_TAC[isHexDigit_def; isAlpha_def; isLower_def; isUpper_def;
             ORD_CHR_RWT; ARITH] THEN ARITH_TAC;
    SUBGOAL_THEN `16 <= n /\ n < 256` (fun th -> REWRITE_TAC[MATCH_MP
      FSEXPAUX_hex_string_lt256 th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[APPEND] THEN
    MAP_EVERY EXISTS_TAC [`HEX (n DIV 16)`; `HEX (n MOD 16)`] THEN
    SUBGOAL_THEN `n DIV 16 < 16 /\ n MOD 16 < 16` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_EQ; MOD_LT_EQ] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[isHexDigit_HEX; UNHEX_HEX; MOD_LT] THEN
    MP_TAC(SPECL [`n:num`; `16`] DIVISION) THEN ARITH_TAC]);;

let EVERY_isPrint_encode_control = prove
 (`!ls. ALL isPrint (encode_control ls)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[encode_control_def; ALL] THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[ALL; ALL_APPEND] THEN
  SIMP_TAC[isPrint_def; ORD_CHR_RWT; ORD_DEF; BITVAL_CLAUSES; ARITH] THEN
  MP_TAC(SPEC `ORD h` EVERY_isHexDigit_num_to_hex_string) THEN
  MATCH_MP_TAC MONO_ALL THEN SIMP_TAC[isHexDigit_isPrint]);;

let decode_encode_control = prove
 (`!ls. decode_control (encode_control ls) = SOME ls`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[encode_control_def; decode_control_def] THEN
  ASM_CASES_TAC `h = CHR 92` THEN ASM_REWRITE_TAC[] THENL
   [SIMP[decode_control_def]; ALL_TAC] THEN
  ASM_CASES_TAC `isPrint h` THEN ASM_REWRITE_TAC[] THENL
   [SIMP[decode_control_def]; ALL_TAC] THEN
  MP_TAC(MATCH_MP FSEXPAUX_hex_encode (SPEC `h:char` ORD_BOUND)) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`d1:char`; `d2:char`] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[APPEND; decode_control_def] THEN
  SIMP[FSEXPAUX_isHexDigit_not_backslash; CHR_ORD]);;
let _ = cake_add_simps [decode_encode_control];;

let isHexDigit_alt = prove
 (`isHexDigit c <=> c IN set_of_list "0123456789abcdefABCDEF"`,
  REWRITE_TAC[IN_SET_OF_LIST; MEM; isHexDigit_def] THEN
  ONCE_REWRITE_TAC[CHAR_EQ_THM] THEN
  REWRITE_TAC[ORD_DEF; BITVAL_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SPEC_TAC(`ORD c`,`n:num`) THEN GEN_TAC THEN
  ASM_CASES_TAC `n < 103` THENL
   [POP_ASSUM MP_TAC THEN SPEC_TAC(`n:num`,`n:num`) THEN
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV;
    EQ_TAC THEN STRIP_TAC THEN MATCH_MP_TAC(TAUT `F ==> p`) THEN
    ASM_ARITH_TAC]);;

let UNHEX_lt16 = prove
 (`isHexDigit c ==> UNHEX c < 16`,
  REWRITE_TAC[isHexDigit_def; UNHEX] THEN
  REPEAT COND_CASES_TAC THEN ASM_ARITH_TAC);;

let isAlpha_isUpper_isLower = prove
 (`isAlpha c ==> ~(isUpper c <=> isLower c)`,
  REWRITE_TAC[isAlpha_def; isUpper_def; isLower_def] THEN ARITH_TAC);;

let isLower_isAlpha = prove
 (`isLower c ==> isAlpha c`,
  SIMP_TAC[isLower_def; isAlpha_def]);;

let FSEXPAUX_hex_decode = prove
 (`!d1 d2. isHexDigit d1 /\ isHexDigit d2 /\
           (isAlpha d1 ==> isUpper d1) /\ (isAlpha d2 ==> isUpper d2)
           ==> APPEND (if num_from_hex_string [d1; d2] < 16 then "0" else "")
                      (num_to_hex_string (num_from_hex_string [d1; d2])) =
               [d1; d2]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FSEXPAUX_num_from_hex_string2] THEN
  MAP_EVERY (fun c -> MP_TAC(INST [c,`c:char`] UNHEX_lt16) THEN
                      ASM_REWRITE_TAC[] THEN DISCH_TAC) [`d1:char`; `d2:char`] THEN
  ASM_SIMP_TAC[MOD_LT] THEN
  ASM_CASES_TAC `UNHEX d1 = 0` THEN ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THENL
   [REWRITE_TAC[FSEXPAUX_STR0] THEN
    ASM_SIMP_TAC[FSEXPAUX_hex_string_lt16; APPEND; FSEXPAUX_HEX_UNHEX; CONS_11] THEN
    SUBGOAL_THEN `HEX (UNHEX d1) = d1` (SUBST1_TAC o SYM) THENL
     [ASM_SIMP_TAC[FSEXPAUX_HEX_UNHEX]; ASM_REWRITE_TAC[HEX_def]];
    ABBREV_TAC `m = 16 * UNHEX d1 + UNHEX d2` THEN
    SUBGOAL_THEN `16 <= m /\ m < 256` ASSUME_TAC THENL
     [EXPAND_TAC "m" THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[FSEXPAUX_hex_string_lt256;
                 ARITH_RULE `16 <= m ==> ~(m < 16)`; APPEND] THEN
    SUBGOAL_THEN `m DIV 16 = UNHEX d1 /\ m MOD 16 = UNHEX d2`
      (fun th -> REWRITE_TAC[th]) THENL
     [EXPAND_TAC "m" THEN CONJ_TAC THENL
       [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `UNHEX d2`;
        MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `UNHEX d1`] THEN
      ASM_ARITH_TAC;
      ASM_SIMP_TAC[FSEXPAUX_HEX_UNHEX]]]);;

let encode_decode_control = prove
 (`!ls r. decode_control ls = SOME r ==> ls = encode_control r`,
  MATCH_MP_TAC decode_control_ind THEN CONJ_TAC THENL
   [SIMP[decode_control_def; encode_control_def]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`c:char`; `cs:string`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1")
    (CONJUNCTS_THEN2 (LABEL_TAC "ih2") (LABEL_TAC "ih3"))) THEN
  X_GEN_TAC `r:string` THEN
  ASM_CASES_TAC `c = CHR 92` THENL
   [POP_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[decode_control_def] THEN
    CASES_ON `cs:string` THEN SIMP_NOASM[] THEN
    ASM_CASES_TAC `a0 = CHR 92` THENL
     [POP_ASSUM SUBST_ALL_TAC THEN SIMP_NOASM[] THEN STRIP_TAC THEN
      REMOVE_THEN "ih2" (MP_TAC o SPEC `a1:string`) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `z:string`) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      SIMP_NOASM[encode_control_def];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CASES_ON `a1:string` THEN SIMP_NOASM[] THEN
    REWRITE_TAC[EXISTS_ONE_THM; OPTION_GUARD_EQ_THM] THEN STRIP_TAC THEN
    REMOVE_THEN "ih1" (MP_TAC o SPECL [`a0:char`; `a0':char`; `a1':string`]) THEN
    ASM_REWRITE_TAC[EXISTS_ONE_THM; OPTION_GUARD_EQ_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `z:string`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[encode_control_def] THEN
    SUBGOAL_THEN `~(CHR (num_from_hex_string [a0; a0']) = CHR 92)` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `~isPrint (CHR 92)` THEN
      SIMP_TAC[isPrint_def; ORD_CHR_RWT; ARITH]; ALL_TAC] THEN
    MP_TAC(INST [`a0:char`,`d1:char`; `a0':char`,`d2:char`]
                num_from_hex_string_length_2) THEN
    SIMP_TAC[ORD_CHR_RWT] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`a0:char`; `a0':char`] FSEXPAUX_hex_decode) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[APPEND];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[decode_control_def] THEN
  SIMP_NOASM[EXISTS_ONE_THM; OPTION_GUARD_EQ_THM] THEN STRIP_TAC THEN
  REMOVE_THEN "ih3" MP_TAC THEN
  ASM_REWRITE_TAC[EXISTS_ONE_THM; OPTION_GUARD_EQ_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `z:string`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[encode_control_def]);;

let SEXSTR_def = cake_def
  `SEXSTR s = SX_STR (encode_control s)`;;

let SEXSTR_11 = prove
 (`SEXSTR s1 = SEXSTR s2 <=> s1 = s2`,
  REWRITE_TAC[SEXSTR_def; injectivity "simpleSexp_sexp"] THEN
  MESON_TAC[decode_encode_control; option_INJ]);;
let _ = cake_add_simps [SEXSTR_11];;

let SEXSTR_distinct = prove
 (`~(SEXSTR s = SX_SYM sym) /\
   ~(SEXSTR s = SX_NUM num) /\
   ~(SEXSTR s = SX_CONS a d) /\
   (SEXSTR s = SX_STR s' <=> s' = encode_control s)`,
  REWRITE_TAC[SEXSTR_def] THEN SIMP[] THEN MESON_TAC[]);;
let _ = cake_add_simps [SEXSTR_distinct];;

let odestSEXSTR_def = cake_def
  `(odestSEXSTR (SX_STR s) = OPTION_MAP implode (decode_control s)) /\
   (odestSEXSTR _ = NONE)`;;
let _ = cake_add_simps [odestSEXSTR_def];;

let encode_control_remove = prove
 (`!s. ALL isPrint s /\ ~(CHR 92 IN set_of_list s) ==> encode_control s = s`,
  LIST_INDUCT_TAC THEN
  SIMP[encode_control_def; ALL; set_of_list; IN_INSERT; DE_MORGAN_THM] THEN
  MESON_TAC[]);;

let SEXSTR_remove = prove
 (`ALL isPrint s /\ ~(CHR 92 IN set_of_list s) ==> SEXSTR s = SX_STR s`,
  SIMP_TAC[SEXSTR_def; encode_control_remove]);;

let odestSXSTR_def = cake_def
  `(odestSXSTR (SX_STR s) = SOME (implode s)) /\
   (odestSXSTR _ = NONE)`;;
let _ = cake_add_simps [odestSXSTR_def];;

let odestSXSYM_def = cake_def
  `(odestSXSYM (SX_SYM s) = SOME (implode s)) /\
   (odestSXSYM _ = NONE)`;;
let _ = cake_add_simps [odestSXSYM_def];;

let odestSXNUM_def = cake_def
  `(odestSXNUM (SX_NUM n) = SOME n) /\
   (odestSXNUM _ = NONE)`;;
let _ = cake_add_simps [odestSXNUM_def];;

let odestSXNUM_SEXSTR = prove
 (`odestSXNUM (SEXSTR str) = NONE`,
  SIMP[SEXSTR_def]);;
let _ = cake_add_simps [odestSXNUM_SEXSTR];;

(* the mlstring literal of NONE is implode "NONE" *)

let sexpopt_def = cake_def
  `sexpopt (p:simpleSexp_sexp->A option) s =
     OPTION_CHOICE
       (OPTION_BIND (odestSXSYM s)
          (\nm. OPTION_IGNORE_BIND (OPTION_GUARD (nm = implode "NONE"))
                  (SOME NONE)))
       (OPTION_BIND (dstrip_sexp s)
          (\na. match na with
                  (nm,args) ->
                    OPTION_IGNORE_BIND
                      (OPTION_GUARD (nm = "SOME" /\ LENGTH args = 1))
                      (OPTION_MAP SOME (p (HD args)))))`;;

let sexplist_def = cake_def
  `sexplist (p:simpleSexp_sexp->A option) s =
     match s with
       SX_CONS h t ->
         OPTION_BIND (p h)
           (\ph. OPTION_BIND (sexplist p t) (\pt. SOME (CONS ph pt)))
     | SX_SYM s -> if s = "nil" then SOME [] else NONE
     | _ -> NONE`;;

let sexplist_thm = prove
 (`sexplist (p:simpleSexp_sexp->A option) (SX_CONS h t) =
     OPTION_BIND (p h)
       (\ph. OPTION_BIND (sexplist p t) (\pt. SOME (CONS ph pt))) /\
   (sexplist p (SX_SYM s) = if s = "nil" then SOME [] else NONE) /\
   sexplist p (SX_NUM n) = NONE /\
   sexplist p (SX_STR str) = NONE`,
  REPEAT CONJ_TAC THEN GEN_REWRITE_TAC LAND_CONV [sexplist_def] THEN
  CASE_REWRITE_TAC[]);;
let _ = cake_add_simps [sexplist_thm];;

let sexppair_def = cake_def
  `sexppair (p1:simpleSexp_sexp->A option) (p2:simpleSexp_sexp->B option) s =
     match s with
       SX_CONS s1 s2 -> OPTION_MAP2 (,) (p1 s1) (p2 s2)
     | _ -> NONE`;;

let sexppair_CONG = prove
 (`!s1 s2 (p1:simpleSexp_sexp->A option) p1' (p2:simpleSexp_sexp->B option) p2'.
     s1 = s2 /\
     (!s. (?s'. s2 = SX_CONS s s') ==> p1 s = p1' s) /\
     (!s. (?s'. s2 = SX_CONS s' s) ==> p2 s = p2' s)
     ==> sexppair p1 p2 s1 = sexppair p1' p2' s2`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC MP_TAC) THEN
  CASES_ON `s2:simpleSexp_sexp` THEN REWRITE_TAC[sexppair_def] THEN
  CASE_REWRITE_TAC[] THEN MESON_TAC[]);;

let strip_sxcons_FAIL_sexplist_FAIL = prove
 (`!s. strip_sxcons s = NONE ==> sexplist (p:simpleSexp_sexp->A option) s = NONE`,
  MATCH_MP_TAC simpleSexp_sexp_INDUCT THEN SIMP[] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `(p:simpleSexp_sexp->A option) a0` option_CASES) THEN
  STRIP_TAC THEN SIMP[] THEN COND_CASES_TAC THEN SIMP[]);;

let monad_bind_FAIL = prove
 (`OPTION_BIND (m1:A option) (\x. NONE:B option) = NONE`,
  CASES_ON `m1:A option` THEN SIMP[]);;

let monad_unitbind_CONG = prove
 (`!m11 (m21:A option) m12 m22.
     m11 = m12 /\ (m12 = SOME one ==> m21 = m22)
     ==> OPTION_IGNORE_BIND m11 m21 = OPTION_IGNORE_BIND m12 m22`,
  REPEAT GEN_TAC THEN CASES_ON `m12:1 option` THEN SIMP[] THEN
  ONCE_REWRITE_TAC[one] THEN SIMP[]);;

let strip_sxcons_thm = prove
 (`strip_sxcons (SX_CONS h t) = OPTION_MAP (CONS h) (strip_sxcons t) /\
   strip_sxcons (SX_NUM n) = NONE /\
   strip_sxcons (SX_STR str) = NONE /\
   strip_sxcons (SX_SYM s) = (if s = "nil" then SOME [] else NONE)`,
  REWRITE_TAC[simpleSexp_strip_sxcons_thm]);;
let _ = cake_add_simps [strip_sxcons_thm];;

let sexplist_CONG = prove
 (`!s1 s2 (p1:simpleSexp_sexp->A option) p2.
     s1 = s2 /\ (!e. sxMEM e s2 ==> p1 e = p2 e)
     ==> sexplist p1 s1 = sexplist p2 s2`,
  REWRITE_TAC[sxMEM_def; LEFT_IMP_EXISTS_THM] THEN
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC MP_TAC) THEN
  SPEC_TAC(`s2:simpleSexp_sexp`,`s2:simpleSexp_sexp`) THEN
  MATCH_MP_TAC simpleSexp_sexp_INDUCT THEN SIMP[] THEN
  MAP_EVERY X_GEN_TAC [`a0:simpleSexp_sexp`; `a1:simpleSexp_sexp`] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `strip_sxcons a1` option_CASES) THEN STRIP_TAC THENL
   [SUBGOAL_THEN `(p1:simpleSexp_sexp->A option) a0 = p2 a0`
      (fun th -> REWRITE_TAC[th]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `CONS (a0:simpleSexp_sexp) x` THEN
    REWRITE_TAC[MEM] THEN ASM_MESON_TAC[];
    ASM_SIMP_TAC[strip_sxcons_FAIL_sexplist_FAIL; OPTION_BIND_DEF;
                 monad_bind_FAIL]]);;

(* HOL4 [defncong] sexplist_CONG, sexppair_CONG and monad_unitbind_CONG:   *)
(* the admissibility rules of the kit's recursion package (a recursive     *)
(* call in the parser argument of sexplist gets the context sxMEM y l, in  *)
(* an argument of sexppair the context l = SX_CONS y s' or SX_CONS s' y;   *)
(* OPTION_IGNORE_BIND has its rule in hol4/vocab.ml)                       *)

let FSEXPAUX_ADMISSIBLE_sexplist = prove
 (`!(<<) (p:(A->B)->P->bool) (s:P->A)
         (h:(A->B)->P->simpleSexp_sexp->C option) l.
        admissible(<<) p s l /\
        admissible (<<) (\f (y,x). p f x /\ sxMEM y (l f x))
                        (\(y,x). s x) (\f (y,x). h f x y)
        ==> admissible (<<) p s (\f x. sexplist (h f x) (l f x))`,
  REWRITE_TAC[admissible; FORALL_PAIR_THM] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(l:(A->B)->P->simpleSexp_sexp) g a = l f a` SUBST1_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC sexplist_CONG THEN REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]);;

cake_register_admissible "sexplist" FSEXPAUX_ADMISSIBLE_sexplist;;

let FSEXPAUX_ADMISSIBLE_sexppair = prove
 (`!(<<) (p:(A->B)->P->bool) (s:P->A)
         (h1:(A->B)->P->simpleSexp_sexp->C option)
         (h2:(A->B)->P->simpleSexp_sexp->D option) l.
        admissible(<<) p s l /\
        admissible (<<) (\f (y,x). p f x /\ ?s'. l f x = SX_CONS y s')
                        (\(y,x). s x) (\f (y,x). h1 f x y) /\
        admissible (<<) (\f (y,x). p f x /\ ?s'. l f x = SX_CONS s' y)
                        (\(y,x). s x) (\f (y,x). h2 f x y)
        ==> admissible (<<) p s (\f x. sexppair (h1 f x) (h2 f x) (l f x))`,
  REWRITE_TAC[admissible; FORALL_PAIR_THM] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(l:(A->B)->P->simpleSexp_sexp) g a = l f a` SUBST1_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC sexppair_CONG THEN REWRITE_TAC[] THEN
  CONJ_TAC THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_MESON_TAC[]);;

cake_register_admissible "sexppair" FSEXPAUX_ADMISSIBLE_sexppair;;

(* termination of the s-expression parsers: the arguments EL k args of a   *)
(* dstrip_sexp s = SOME (nm,args) (with LENGTH args known from the guard)  *)
(* are parts of s, an sxMEM y t makes y smaller than t                     *)

let FSEXPAUX_TC_TAC : tactic =
  REWRITE_TAC(WF_REL_THMS @ [o_THM; FST; SND; sum_CASE]) THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  GVS[EXISTS_ONE_THM; OPTION_GUARD_EQ_THM; dstrip_sexp_SOME;
      LENGTH_EQ_NUM_compute] THEN
  REPEAT (FIRST_X_ASSUM (MP_TAC o MATCH_MP sxMEM_sizelt)) THEN
  SIMP[simpleSexp_sexp_size_def] THEN ARITH_TAC;;


let sexpid_def = cake_def_wf
  `MEASURE ((simpleSexp_sexp_size o SND):
              (simpleSexp_sexp->A option)#simpleSexp_sexp->num)`
  FSEXPAUX_TC_TAC
  `sexpid (p:simpleSexp_sexp->A option) s =
     OPTION_BIND (dstrip_sexp s)
       (\na. match na with
               (nm,args) ->
                 OPTION_CHOICE
                   (OPTION_IGNORE_BIND
                      (OPTION_GUARD (nm = "Short" /\ LENGTH args = 1))
                      (OPTION_MAP Short (p (EL 0 args))))
                   (OPTION_IGNORE_BIND
                      (OPTION_GUARD (nm = "Long" /\ LENGTH args = 2))
                      (OPTION_MAP2 Long (odestSEXSTR (EL 0 args))
                                        (sexpid p (EL 1 args)))))`;;

let sexpid_ind = cake_ind "sexpid";;

let sexptype_def = cake_def_wf
  `MEASURE simpleSexp_sexp_size`
  FSEXPAUX_TC_TAC
  `sexptype s =
     OPTION_BIND (dstrip_sexp s)
       (\na. match na with
               (s,args) ->
                 OPTION_CHOICE
                   (OPTION_CHOICE
                      (OPTION_CHOICE
                         (OPTION_IGNORE_BIND
                            (OPTION_GUARD (s = "Atvar" /\ LENGTH args = 1))
                            (OPTION_MAP Atvar (odestSEXSTR (EL 0 args))))
                         (OPTION_IGNORE_BIND
                            (OPTION_GUARD (s = "Atfun" /\ LENGTH args = 2))
                            (OPTION_MAP2 Atfun (sexptype (EL 0 args))
                                               (sexptype (EL 1 args)))))
                      (OPTION_IGNORE_BIND
                         (OPTION_GUARD (s = "Attup" /\ LENGTH args = 1))
                         (OPTION_MAP Attup (sexplist sexptype (EL 0 args)))))
                   (OPTION_IGNORE_BIND
                      (OPTION_GUARD (s = "Atapp" /\ LENGTH args = 2))
                      (OPTION_MAP2 Atapp (sexplist sexptype (EL 0 args))
                                         (sexpid odestSEXSTR (EL 1 args)))))`;;

let sexptype_ind = cake_ind "sexptype";;

(* translator friendly version for bootstrapping *)

let sexptype_alt_def = cake_def_wf
  `inv_image (MEASURE simpleSexp_sexp_size)
     (\x:simpleSexp_sexp+simpleSexp_sexp. match x with INL y -> y | INR y -> y)`
  FSEXPAUX_TC_TAC
  `(sexptype_alt s =
      match dstrip_sexp s with
        NONE -> NONE
      | SOME (nm,args) ->
          if nm = "Atvar" /\ LENGTH args = 1 then
            OPTION_MAP Atvar (odestSEXSTR (EL 0 args))
          else if nm = "Atfun" /\ LENGTH args = 2 then
            OPTION_MAP2 Atfun (sexptype_alt (EL 0 args))
                              (sexptype_alt (EL 1 args))
          else if nm = "Attup" /\ LENGTH args = 1 then
            OPTION_MAP Attup (sexptype_list (EL 0 args))
          else if nm = "Atapp" /\ LENGTH args = 2 then
            OPTION_MAP2 Atapp (sexptype_list (EL 0 args))
                              (sexpid odestSEXSTR (EL 1 args))
          else NONE) /\
   (sexptype_list s =
      match s with
        SX_SYM nm -> if nm = "nil" then SOME [] else NONE
      | SX_CONS a d ->
          (match sexptype_alt a with
             NONE -> NONE
           | SOME h ->
               (match sexptype_list d with
                  NONE -> NONE
                | SOME t -> SOME (CONS h t)))
      | _ -> NONE)`;;

let sexptype_alt_ind = cake_ind "sexptype_alt";;

(* the guards of a parser after dstrip_sexp s = SOME (nm,args): a case     *)
(* split on the symbol nm (one of the names lits, or none of them)        *)

let rec FSEXPAUX_NAME_CASES_TAC (x:term) (lits:term list) : tactic =
  match lits with
    [] -> FS[]
  | l::ls -> ASM_CASES_TAC (mk_eq(x,l)) THENL
               [FS[] THEN REPEAT COND_CASES_TAC THEN FS[];
                FSEXPAUX_NAME_CASES_TAC x ls];;

let FSEXPAUX_DSTRIP_CASES_TAC (lits:term list) : tactic = fun (asl,w as g) ->
  let is_dstrip th =
    try let l,r = dest_eq(concl th) in
        fst(dest_const(rator l)) = "dstrip_sexp" && is_var(fst(dest_pair(rand r)))
    with Failure _ -> false in
  let th = find is_dstrip (map snd asl) in
  let v = fst(dest_pair(rand(rhs(concl th)))) in
  FSEXPAUX_NAME_CASES_TAC v lits g;;

let sexptype_alt_intro = prove
 (`(!s. sexptype s = sexptype_alt s) /\
   (!s. sexptype_list s = sexplist sexptype s)`,
  MATCH_MP_TAC sexptype_alt_ind THEN CONJ_TAC THEN GEN_TAC THEN STRIP_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [sexptype_def] THEN
    GEN_REWRITE_TAC RAND_CONV [CONJUNCT1 sexptype_alt_def] THEN
    TOP_CASE_TAC THEN SIMP[] THEN TOP_CASE_TAC THEN
    FS[monad_unitbind_assert] THEN
    FSEXPAUX_DSTRIP_CASES_TAC [`"Atvar"`; `"Atfun"`; `"Attup"`; `"Atapp"`];
    GEN_REWRITE_TAC LAND_CONV [CONJUNCT2 sexptype_alt_def] THEN
    CASES_ON `s:simpleSexp_sexp` THEN FS[] THEN
    TOP_CASE_TAC THEN SIMP[] THEN TOP_CASE_TAC THEN SIMP[]]);;

let sexptype_alt_intro1 = prove
 (`sexptype = sexptype_alt /\ sexplist sexptype = sexptype_list`,
  REWRITE_TAC[FUN_EQ_THM; sexptype_alt_intro]);;

(* HOL4 & (num to int) is int_of_num, written (&); n2w is word *)

let sexplit_def = cake_def
  `sexplit s =
     OPTION_CHOICE
       (OPTION_CHOICE (OPTION_MAP (IntLit o (&)) (odestSXNUM s))
                      (OPTION_MAP StrLit (odestSEXSTR s)))
       (OPTION_BIND (dstrip_sexp s)
          (\na. match na with
             (nm,args) ->
               OPTION_IGNORE_BIND (OPTION_GUARD (LENGTH args = 1))
                 (OPTION_CHOICE
                    (OPTION_CHOICE
                       (OPTION_CHOICE
                          (OPTION_CHOICE
                             (OPTION_IGNORE_BIND (OPTION_GUARD (nm = "-"))
                                (OPTION_BIND (odestSXNUM (HD args))
                                   (\n. if n = 0 then NONE
                                        else SOME (IntLit (-- &n)))))
                             (OPTION_IGNORE_BIND (OPTION_GUARD (nm = "char"))
                                (OPTION_BIND (odestSEXSTR (HD args))
                                   (\cs. OPTION_IGNORE_BIND
                                           (OPTION_GUARD (strlen cs = 1))
                                           (SOME (Char (strsub cs 0)))))))
                          (OPTION_IGNORE_BIND (OPTION_GUARD (nm = "word8"))
                             (OPTION_BIND (odestSXNUM (HD args))
                                (\n. OPTION_IGNORE_BIND (OPTION_GUARD (n < 256))
                                       (SOME (Word8 (word n)))))))
                       (OPTION_IGNORE_BIND (OPTION_GUARD (nm = "word64"))
                          (OPTION_BIND (odestSXNUM (HD args))
                             (\n. OPTION_IGNORE_BIND
                                    (OPTION_GUARD (n < 2 EXP 64))
                                    (SOME (Word64 (word n)))))))
                    (OPTION_IGNORE_BIND (OPTION_GUARD (nm = "float64"))
                       (OPTION_BIND (odestSXNUM (HD args))
                          (\n. OPTION_IGNORE_BIND (OPTION_GUARD (n < 2 EXP 64))
                                 (SOME (Float64 (word n)))))))))`;;

(* don't require Pvar constructors; bare strings can be pattern variables.
   Unclear if this sort of special-casing is ever likely to be helpful *)

let sexppat_def = cake_def_wf
  `MEASURE simpleSexp_sexp_size`
  FSEXPAUX_TC_TAC
  `sexppat s =
     OPTION_CHOICE
       (OPTION_MAP Pvar (odestSEXSTR s))
       (OPTION_BIND (dstrip_sexp s)
          (\na. match na with
             (nm,args) ->
               OPTION_CHOICE
                 (OPTION_CHOICE
                    (OPTION_CHOICE
                       (OPTION_CHOICE
                          (OPTION_CHOICE
                             (OPTION_IGNORE_BIND
                                (OPTION_GUARD (nm = "Pany" /\ LENGTH args = 0))
                                (SOME Pany))
                             (OPTION_IGNORE_BIND
                                (OPTION_GUARD (nm = "Plit" /\ LENGTH args = 1))
                                (OPTION_MAP Plit (sexplit (EL 0 args)))))
                          (OPTION_IGNORE_BIND
                             (OPTION_GUARD (nm = "Pcon" /\ LENGTH args = 2))
                             (OPTION_MAP2 Pcon
                                (sexpopt (sexpid odestSEXSTR) (EL 0 args))
                                (sexplist sexppat (EL 1 args)))))
                       (OPTION_IGNORE_BIND
                          (OPTION_GUARD (nm = "Pas" /\ LENGTH args = 2))
                          (OPTION_MAP2 Pas (sexppat (EL 0 args))
                                           (odestSEXSTR (EL 1 args)))))
                    (OPTION_IGNORE_BIND
                       (OPTION_GUARD (nm = "Pref" /\ LENGTH args = 1))
                       (OPTION_MAP Pref (sexppat (EL 0 args)))))
                 (OPTION_IGNORE_BIND
                    (OPTION_GUARD (nm = "Ptannot" /\ LENGTH args = 2))
                    (OPTION_MAP2 Ptannot (sexppat (EL 0 args))
                                         (sexptype (EL 1 args))))))`;;

let sexppat_ind = cake_ind "sexppat";;

(* translator friendly version for bootstrapping *)

let sexppat_alt_def = cake_def_wf
  `inv_image (MEASURE simpleSexp_sexp_size)
     (\x:simpleSexp_sexp+simpleSexp_sexp. match x with INL y -> y | INR y -> y)`
  FSEXPAUX_TC_TAC
  `(sexppat_alt s =
      OPTION_CHOICE (OPTION_MAP Pvar (odestSEXSTR s))
        (match dstrip_sexp s with
           NONE -> NONE
         | SOME (nm,args) ->
             if nm = "Pany" /\ LENGTH args = 0 then SOME Pany
             else if nm = "Plit" /\ LENGTH args = 1 then
               OPTION_MAP Plit (sexplit (EL 0 args))
             else if nm = "Pcon" /\ LENGTH args = 2 then
               OPTION_MAP2 Pcon (sexpopt (sexpid odestSEXSTR) (EL 0 args))
                 (sexppat_list (EL 1 args))
             else if nm = "Pas" /\ LENGTH args = 2 then
               OPTION_MAP2 Pas (sexppat_alt (EL 0 args))
                               (odestSEXSTR (EL 1 args))
             else if nm = "Pref" /\ LENGTH args = 1 then
               OPTION_MAP Pref (sexppat_alt (EL 0 args))
             else if nm = "Ptannot" /\ LENGTH args = 2 then
               OPTION_MAP2 Ptannot (sexppat_alt (EL 0 args))
                                   (sexptype_alt (EL 1 args))
             else NONE)) /\
   (sexppat_list s =
      match s with
        SX_SYM nm -> if nm = "nil" then SOME [] else NONE
      | SX_CONS a d ->
          (match sexppat_alt a with
             NONE -> NONE
           | SOME h ->
               (match sexppat_list d with
                  NONE -> NONE
                | SOME t -> SOME (CONS h t)))
      | _ -> NONE)`;;

let sexppat_alt_ind = cake_ind "sexppat_alt";;

let sexppat_alt_intro = prove
 (`(!s. sexppat s = sexppat_alt s) /\
   (!s. sexppat_list s = sexplist sexppat s)`,
  MATCH_MP_TAC sexppat_alt_ind THEN CONJ_TAC THEN GEN_TAC THEN STRIP_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [sexppat_def] THEN
    GEN_REWRITE_TAC RAND_CONV [CONJUNCT1 sexppat_alt_def] THEN
    AP_TERM_TAC THEN
    TOP_CASE_TAC THEN SIMP[] THEN TOP_CASE_TAC THEN
    FS[monad_unitbind_assert; sexptype_alt_intro1] THEN
    FSEXPAUX_DSTRIP_CASES_TAC [`"Pany"`; `"Plit"`; `"Pcon"`; `"Pas"`; `"Pref"`;
                               `"Ptannot"`];
    GEN_REWRITE_TAC LAND_CONV [CONJUNCT2 sexppat_alt_def] THEN
    CASES_ON `s:simpleSexp_sexp` THEN FS[] THEN
    TOP_CASE_TAC THEN SIMP[] THEN TOP_CASE_TAC THEN SIMP[]]);;

let sexppat_alt_intro1 = prove
 (`sexppat = sexppat_alt /\ sexplist sexppat = sexppat_list`,
  REWRITE_TAC[FUN_EQ_THM; sexppat_alt_intro]);;

let decode_thunk_mode_def = cake_def
  `decode_thunk_mode s =
     if s = "Evaluated" then SOME Evaluated
     else if s = "NotEvaluated" then SOME NotEvaluated
     else NONE`;;

let encode_thunk_mode_def = cake_def
  `(encode_thunk_mode Evaluated = "Evaluated") /\
   (encode_thunk_mode NotEvaluated = "NotEvaluated")`;;

(* HOL4: decode_test, decode_test_def *)

let fromSexp_decode_test_def = cake_def
  `(fromSexp_decode_test (SX_SYM s) =
      if s = "Equal" then SOME Equal else
      if s = "Less" then SOME (Compare Lt) else
      if s = "LessEq" then SOME (Compare Leq) else
      if s = "Greater" then SOME (Compare Gt) else
      if s = "GreaterEq" then SOME (Compare Geq) else
      if s = "AltLess" then SOME (AltCompare Lt) else
      if s = "AltLessEq" then SOME (AltCompare Leq) else
      if s = "AltGreater" then SOME (AltCompare Gt) else
      if s = "AltGreaterEq" then SOME (AltCompare Geq) else NONE) /\
   (fromSexp_decode_test _ = NONE)`;;

let decode_prim_type_def = cake_def
  `(decode_prim_type (SX_SYM s) =
      if s = "BoolT" then SOME BoolT else
      if s = "IntT" then SOME IntT else
      if s = "CharT" then SOME CharT else
      if s = "StrT" then SOME StrT else
      if s = "Word8T" then SOME (WordT W8) else
      if s = "Word64T" then SOME (WordT W64) else
      if s = "Float64T" then SOME Float64T else NONE) /\
   (decode_prim_type _ = NONE)`;;

let sexparith_def = cake_def
  `(sexparith (SX_SYM s) =
      if s = "Add" then SOME Add else
      if s = "Sub" then SOME Sub else
      if s = "Mul" then SOME Mul else
      if s = "Div" then SOME Div else
      if s = "Mod" then SOME Mod else
      if s = "Neg" then SOME Neg else
      if s = "Abs" then SOME Abs else
      if s = "And" then SOME And else
      if s = "Xor" then SOME Xor else
      if s = "Or" then SOME Or else
      if s = "Not" then SOME Not else
      if s = "Sqrt" then SOME Sqrt else
      if s = "FMA" then SOME FMA else NONE) /\
   (sexparith _ = NONE)`;;

let sexplog_def = cake_def
  `(sexplog (SX_SYM s) =
      if s = "Andalso" then SOME Andalso else
      if s = "Orelse" then SOME Orelse else NONE) /\
   (sexplog _ = NONE)`;;

let sexpop_def = cake_def
  `(sexpop (SX_SYM s) =
      if s = "Equality" then SOME Equality else
      if s = "Opapp" then SOME Opapp else
      if s = "Opassign" then SOME Opassign else
      if s = "Opref" then SOME Opref else
      if s = "Opderef" then SOME Opderef else
      if s = "Aw8alloc" then SOME Aw8alloc else
      if s = "Aw8sub" then SOME Aw8sub else
      if s = "Aw8length" then SOME Aw8length else
      if s = "Aw8update" then SOME Aw8update else
      if s = "Aw8subunsafe" then SOME Aw8sub_unsafe else
      if s = "Aw8updateunsafe" then SOME Aw8update_unsafe else
      if s = "CopyStrStr" then SOME CopyStrStr else
      if s = "CopyStrAw8" then SOME CopyStrAw8 else
      if s = "CopyAw8Str" then SOME CopyAw8Str else
      if s = "CopyAw8Aw8" then SOME CopyAw8Aw8 else
      if s = "XorAw8Strunsafe" then SOME XorAw8Str_unsafe else
      if s = "Implode" then SOME Implode else
      if s = "Explode" then SOME Explode else
      if s = "Strsub" then SOME Strsub else
      if s = "Strlen" then SOME Strlen else
      if s = "Strcat" then SOME Strcat else
      if s = "VfromList" then SOME VfromList else
      if s = "Vsub" then SOME Vsub else
      if s = "Vsubunsafe" then SOME Vsub_unsafe else
      if s = "Vlength" then SOME Vlength else
      if s = "ListAppend" then SOME ListAppend else
      if s = "Aalloc" then SOME Aalloc else
      if s = "AallocEmpty" then SOME AallocEmpty else
      if s = "AallocFixed" then SOME AallocFixed else
      if s = "Asub" then SOME Asub else
      if s = "Alength" then SOME Alength else
      if s = "Aupdate" then SOME Aupdate else
      if s = "Asubunsafe" then SOME Asub_unsafe else
      if s = "Aupdateunsafe" then SOME Aupdate_unsafe else
      if s = "ForceThunk" then SOME (ThunkOp ForceThunk) else
      if s = "ConfigGC" then SOME ConfigGC else
      if s = "Eval" then SOME Eval else
      if s = "Envid" then SOME Env_id else NONE) /\
   (sexpop (SX_CONS (SX_SYM s) (SX_STR s')) =
      if s = "FFI" then OPTION_MAP (FFI o implode) (decode_control s')
      else NONE) /\
   (sexpop (SX_CONS (SX_SYM s) (SX_SYM t)) =
      match decode_thunk_mode t with
        NONE -> NONE
      | SOME m ->
          if s = "AllocThunk" then SOME (ThunkOp (AllocThunk m)) else
          if s = "UpdateThunk" then SOME (ThunkOp (UpdateThunk m)) else NONE) /\
   (sexpop (SX_CONS (SX_SYM s) (SX_NUM n)) =
      if s = "Shift8Lsl" then SOME (Shift W8 Lsl n) else
      if s = "Shift8Lsr" then SOME (Shift W8 Lsr n) else
      if s = "Shift8Asr" then SOME (Shift W8 Asr n) else
      if s = "Shift8Ror" then SOME (Shift W8 Ror n) else
      if s = "Shift64Lsl" then SOME (Shift W64 Lsl n) else
      if s = "Shift64Lsr" then SOME (Shift W64 Lsr n) else
      if s = "Shift64Asr" then SOME (Shift W64 Asr n) else
      if s = "Shift64Ror" then SOME (Shift W64 Ror n) else NONE) /\
   (sexpop (SX_CONS (SX_SYM s) (SX_CONS x y)) =
      if s = "Arith" then
        (match (sexparith x, decode_prim_type y) with
           (SOME a, SOME prim_type) -> SOME (Arith a prim_type)
         | _ -> NONE)
      else if s = "FromTo" then
        (match (decode_prim_type x, decode_prim_type y) with
           (SOME ty1, SOME ty2) -> SOME (FromTo ty1 ty2)
         | _ -> NONE)
      else if s = "Test" then
        (match (fromSexp_decode_test x, decode_prim_type y) with
           (SOME test, SOME prim_type) -> SOME (Test test prim_type)
         | _ -> NONE)
      else NONE) /\
   (sexpop _ = NONE)`;;

let sexplocpt_def = cake_def_clauses
  [`sexplocpt (SX_SYM s) =
      if s = "unk" then SOME UNKNOWNpt
      else if s = "eof" then SOME EOFpt
      else NONE`;
   `sexplocpt s =
      OPTION_BIND (strip_sxcons s)
        (\ls. OPTION_IGNORE_BIND (OPTION_GUARD (LENGTH ls = 2))
                (OPTION_MAP2 POSN (odestSXNUM (EL 0 ls))
                                  (odestSXNUM (EL 1 ls))))`];;

let sexplocn_def = cake_def
  `sexplocn s =
     OPTION_BIND (strip_sxcons s)
       (\ls. OPTION_IGNORE_BIND (OPTION_GUARD (LENGTH ls = 2))
               (OPTION_MAP2 Locs (sexplocpt (EL 0 ls))
                                 (sexplocpt (EL 1 ls))))`;;

let sexpexp_def = cake_def_wf
  `MEASURE simpleSexp_sexp_size`
  FSEXPAUX_TC_TAC
  `sexpexp s =
     OPTION_BIND (dstrip_sexp s)
       (\na. match na with
          (nm,args) ->
             OPTION_CHOICE (OPTION_CHOICE (OPTION_CHOICE (OPTION_CHOICE (OPTION_CHOICE
             (OPTION_CHOICE (OPTION_CHOICE (OPTION_CHOICE (OPTION_CHOICE (OPTION_CHOICE
             (OPTION_CHOICE (OPTION_CHOICE (OPTION_CHOICE
               (OPTION_IGNORE_BIND (OPTION_GUARD (nm = "Raise" /\ LENGTH args = 1))
                  (OPTION_MAP Raise (sexpexp (EL 0 args))))
               (OPTION_IGNORE_BIND (OPTION_GUARD (nm = "Handle" /\ LENGTH args = 2))
                  (OPTION_MAP2 Handle (sexpexp (EL 0 args))
                      (sexplist (sexppair sexppat sexpexp) (EL 1 args)))))
               (OPTION_IGNORE_BIND (OPTION_GUARD (nm = "Lit" /\ LENGTH args = 1))
                  (OPTION_MAP Lit (sexplit (EL 0 args)))))
               (OPTION_IGNORE_BIND (OPTION_GUARD (nm = "Con" /\ LENGTH args = 2))
                  (OPTION_MAP2 Con (sexpopt (sexpid odestSEXSTR) (EL 0 args))
                      (sexplist sexpexp (EL 1 args)))))
               (OPTION_IGNORE_BIND (OPTION_GUARD (nm = "Var" /\ LENGTH args = 1))
                  (OPTION_MAP Var (sexpid odestSEXSTR (EL 0 args)))))
               (OPTION_IGNORE_BIND (OPTION_GUARD (nm = "Fun" /\ LENGTH args = 2))
                  (OPTION_MAP2 Fun (odestSEXSTR (EL 0 args)) (sexpexp (EL 1 args)))))
               (OPTION_IGNORE_BIND (OPTION_GUARD (nm = "App" /\ LENGTH args = 2))
                  (OPTION_MAP2 App (sexpop (EL 0 args)) (sexplist sexpexp (EL 1 args)))))
               (OPTION_IGNORE_BIND (OPTION_GUARD (nm = "Log" /\ LENGTH args = 3))
                  (OPTION_APPLY (OPTION_APPLY (OPTION_MAP Log (sexplog (EL 0 args)))
                      (sexpexp (EL 1 args))) (sexpexp (EL 2 args)))))
               (OPTION_IGNORE_BIND (OPTION_GUARD (nm = "If" /\ LENGTH args = 3))
                  (OPTION_APPLY (OPTION_APPLY (OPTION_MAP If (sexpexp (EL 0 args)))
                      (sexpexp (EL 1 args))) (sexpexp (EL 2 args)))))
               (OPTION_IGNORE_BIND (OPTION_GUARD (nm = "Mat" /\ LENGTH args = 2))
                  (OPTION_MAP2 Mat (sexpexp (EL 0 args))
                      (sexplist (sexppair sexppat sexpexp) (EL 1 args)))))
               (OPTION_IGNORE_BIND (OPTION_GUARD (nm = "Let" /\ LENGTH args = 3))
                  (OPTION_APPLY (OPTION_APPLY (OPTION_MAP Let (sexpopt odestSEXSTR (EL 0 args)))
                      (sexpexp (EL 1 args))) (sexpexp (EL 2 args)))))
               (OPTION_IGNORE_BIND (OPTION_GUARD (nm = "Letrec" /\ LENGTH args = 2))
                  (OPTION_MAP2 Letrec
                      (sexplist (sexppair odestSEXSTR (sexppair odestSEXSTR sexpexp)) (EL 0 args))
                      (sexpexp (EL 1 args)))))
               (OPTION_IGNORE_BIND (OPTION_GUARD (nm = "Tannot" /\ LENGTH args = 2))
                  (OPTION_MAP2 Tannot (sexpexp (EL 0 args)) (sexptype (EL 1 args)))))
               (OPTION_IGNORE_BIND (OPTION_GUARD (nm = "Lannot" /\ LENGTH args = 2))
                  (OPTION_MAP2 Lannot (sexpexp (EL 0 args)) (sexplocn (EL 1 args))))
          )`;;

let sexpexp_ind = cake_ind "sexpexp";;

(* translator friendly version for bootstrapping *)

let sexpexp_alt_def = cake_def_wf
  `inv_image (MEASURE simpleSexp_sexp_size)
     (\x:simpleSexp_sexp+simpleSexp_sexp+simpleSexp_sexp+simpleSexp_sexp+
         simpleSexp_sexp+simpleSexp_sexp.
        match x with
          INL y -> y
        | INR (INL y) -> y
        | INR (INR (INL y)) -> y
        | INR (INR (INR (INL y))) -> y
        | INR (INR (INR (INR (INL y)))) -> y
        | INR (INR (INR (INR (INR y)))) -> y)`
  FSEXPAUX_TC_TAC
  `(sexpexp_alt s =
      match dstrip_sexp s with
        NONE -> NONE
      | SOME (nm,args) ->
          if nm = "Raise" /\ LENGTH args = 1 then
            OPTION_MAP Raise (sexpexp_alt (EL 0 args)) else
          if nm = "Handle" /\ LENGTH args = 2 then
            OPTION_MAP2 Handle (sexpexp_alt (EL 0 args)) (sexppes (EL 1 args))
          else
          if nm = "Lit" /\ LENGTH args = 1 then
            OPTION_MAP Lit (sexplit (EL 0 args))
          else
          if nm = "Con" /\ LENGTH args = 2 then
            OPTION_MAP2 Con (sexpopt (sexpid odestSEXSTR) (EL 0 args))
              (sexpexp_list (EL 1 args))
          else
          if nm = "Var" /\ LENGTH args = 1 then
            OPTION_MAP Var (sexpid odestSEXSTR (EL 0 args))
          else
          if nm = "Fun" /\ LENGTH args = 2 then
            OPTION_MAP2 Fun (odestSEXSTR (EL 0 args)) (sexpexp_alt (EL 1 args))
          else
          if nm = "App" /\ LENGTH args = 2 then
            OPTION_MAP2 App (sexpop (EL 0 args)) (sexpexp_list (EL 1 args))
          else
          if nm = "Log" /\ LENGTH args = 3 then
            OPTION_APPLY (OPTION_APPLY (OPTION_MAP Log (sexplog (EL 0 args)))
              (sexpexp_alt (EL 1 args))) (sexpexp_alt (EL 2 args))
          else
          if nm = "If" /\ LENGTH args = 3 then
            OPTION_APPLY (OPTION_APPLY (OPTION_MAP If (sexpexp_alt (EL 0 args)))
              (sexpexp_alt (EL 1 args))) (sexpexp_alt (EL 2 args))
          else
          if nm = "Mat" /\ LENGTH args = 2 then
            OPTION_MAP2 Mat (sexpexp_alt (EL 0 args)) (sexppes (EL 1 args))
          else
          if nm = "Let" /\ LENGTH args = 3 then
            OPTION_APPLY (OPTION_APPLY
              (OPTION_MAP Let (sexpopt odestSEXSTR (EL 0 args)))
              (sexpexp_alt (EL 1 args))) (sexpexp_alt (EL 2 args))
          else
          if nm = "Letrec" /\ LENGTH args = 2 then
            OPTION_MAP2 Letrec (sexpfuns (EL 0 args)) (sexpexp_alt (EL 1 args))
          else
          if nm = "Tannot" /\ LENGTH args = 2 then
            OPTION_MAP2 Tannot (sexpexp_alt (EL 0 args)) (sexptype_alt (EL 1 args))
          else
          if nm = "Lannot" /\ LENGTH args = 2 then
            OPTION_MAP2 Lannot (sexpexp_alt (EL 0 args)) (sexplocn (EL 1 args))
          else NONE) /\
   (sexpexp_list s =
      match s with
        SX_SYM nm -> if nm = "nil" then SOME [] else NONE
      | SX_CONS a d ->
          (match sexpexp_alt a with
             NONE -> NONE
           | SOME h ->
               (match sexpexp_list d with
                  NONE -> NONE
                | SOME t -> SOME (CONS h t)))
      | _ -> NONE) /\
   (sexppes s =
      match s with
        SX_SYM nm -> if nm = "nil" then SOME [] else NONE
      | SX_CONS a d ->
          (match sexppatexp a with
             NONE -> NONE
           | SOME h ->
               (match sexppes d with
                  NONE -> NONE
                | SOME t -> SOME (CONS h t)))
      | _ -> NONE) /\
   (sexpfuns s =
      match s with
        SX_SYM nm -> if nm = "nil" then SOME [] else NONE
      | SX_CONS a d ->
          (match sexpfun a with
             NONE -> NONE
           | SOME h ->
               (match sexpfuns d with
                  NONE -> NONE
                | SOME t -> SOME (CONS h t)))
      | _ -> NONE) /\
   (sexppatexp s =
      match s with
        SX_CONS a d ->
          (match (sexppat_alt a, sexpexp_alt d) with
             (SOME p, SOME e) -> SOME (p,e)
           | _ -> NONE)
      | _ -> NONE) /\
   (sexpfun s =
      match s with
        SX_CONS a d ->
          (match d with
             SX_CONS b d ->
               (match (odestSEXSTR a, odestSEXSTR b, sexpexp_alt d) with
                  (SOME x, SOME y, SOME z) -> SOME (x,y,z)
                | _ -> NONE)
           | _ -> NONE)
      | _ -> NONE)`;;

(* KIT ISSUE workaround: for three or more mutually recursive functions    *)
(* the kit makes the definition but not the induction theorem (its        *)
(* split_conv does not beta-reduce after each SUM_CASE_FORALL step); this   *)
(* is the kit's derivation (define.ml, cake_def_mutual) with that step      *)
(* fixed, for unary functions; it stores the theorem for cake_ind.  A bound *)
(* variable that the kit names like the combined function is renamed.      *)

let FSEXPAUX_MUTUAL_IND (names:string list) =
  let fname = end_itlist (fun a b -> a^"_"^b) names ^ "_MUTREC" in
  let ind = cake_ind fname in
  let consts = map (fun n -> mk_const(n,[])) names in
  let fdefs = map (fun c ->
      let th = find (fun th ->
          try lhs(concl th) = c with Failure _ -> false) (definitions()) in
      CONV_RULE (ONCE_DEPTH_CONV BETA_CONV) (REWRITE_RULE[FUN_EQ_THM] th))
    consts in
  let fold_conv = PURE_REWRITE_CONV (map GSYM fdefs) in
  let argtys = map (fun c -> fst(dest_fun_ty(type_of c))) consts in
  let ps = map2 (fun n ty -> mk_var("P"^n,mk_fun_ty ty bool_ty)) names argtys in
  let rec qterm l = match l with
      [p] -> p
    | p::rest ->
        let sty = mk_sum_ty (map (fun p -> fst(dest_fun_ty(type_of p))) l) in
        let s = mk_var("s_mr",sty) in
        mk_abs(s,list_mk_icomb "sum_CASE" [s;p;qterm rest])
    | [] -> failwith "qterm" in
  let th1 = ISPEC (qterm ps) ind in
  let red = REPEATC (CHANGED_CONV (TOP_DEPTH_CONV BETA_CONV THENC
                                   PURE_REWRITE_CONV[sum_CASE])) in
  let th2 = CONV_RULE (red THENC fold_conv) th1 in
  let rec split_conv l = match l with
      [_] -> ALL_CONV
    | _::rest -> GEN_REWRITE_CONV I [SUM_CASE_FORALL] THENC
                 RAND_CONV (BINDER_CONV (TRY_CONV BETA_CONV) THENC
                            split_conv rest)
    | [] -> ALL_CONV in
  let th3 = CONV_RULE (RAND_CONV (split_conv ps THENC
                                  TOP_DEPTH_CONV BETA_CONV)) th2 in
  let th4 = GENL ps th3 in
  let rec fix tm = match tm with
      Abs(v,b) ->
        let n,ty = dest_var v in
        if n = fname then
          let v' = variant (frees tm @ variables b) (mk_var("b",ty)) in
          mk_abs(v',fix (vsubst [v',v] b))
        else mk_abs(v,fix b)
    | Comb(f,x) -> mk_comb(fix f,fix x)
    | _ -> tm in
  let th5 = EQ_MP (ALPHA (concl th4) (fix (concl th4))) th4 in
  do_list (fun n -> cake_ind_store := (n,th5) :: !cake_ind_store) names;
  th5;;

let sexpexp_alt_ind = FSEXPAUX_MUTUAL_IND
  ["sexpexp_alt"; "sexpexp_list"; "sexppes"; "sexpfuns"; "sexppatexp";
   "sexpfun"];;

(* the guards of a long parser after dstrip_sexp s = SOME (nm,args): a     *)
(* case split on nm (string literal comparison by conversion, as the       *)
(* simplifier is slow on the long chain of conditionals), then fin         *)

let FSEXPAUX_STRING_EQ_TAC =
  CONV_TAC (DEPTH_CONV STRING_EQ_CONV) THEN
  REWRITE_TAC[COND_CLAUSES; AND_CLAUSES; OPTION_CHOICE_DEF; OPTION_CHOICE_NONE];;

let rec FSEXPAUX_NAME_CASES2_TAC (x:term) (lits:term list) (fin:tactic) =
  match lits with
    [] -> ASM_REWRITE_TAC[COND_CLAUSES; AND_CLAUSES; OPTION_CHOICE_DEF;
                          OPTION_CHOICE_NONE]
  | l::ls -> ASM_CASES_TAC (mk_eq(x,l)) THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN FSEXPAUX_STRING_EQ_TAC THEN
        COND_CASES_TAC THEN REWRITE_TAC[] THEN fin;
        FSEXPAUX_NAME_CASES2_TAC x ls fin];;

let FSEXPAUX_DSTRIP_CASES2_TAC (lits:term list) (fin:tactic) : tactic =
  fun (asl,w as g) ->
    let is_dstrip th =
      try let l,r = dest_eq(concl th) in
          fst(dest_const(rator l)) = "dstrip_sexp" &&
          is_var(fst(dest_pair(rand r)))
      with Failure _ -> false in
    let th = find is_dstrip (map snd asl) in
    let v = fst(dest_pair(rand(rhs(concl th)))) in
    FSEXPAUX_NAME_CASES2_TAC v lits fin g;;

(* the induction hypotheses !args. dstrip_sexp s = SOME (l,args) /\ c ==>   *)
(* e in the case dstrip_sexp s = SOME (l,y): instantiated with y, the       *)
(* antecedent decided by rewriting with the assumptions and string literal  *)
(* comparison, then used to rewrite the goal                                *)

let FSEXPAUX_IH_TAC : tactic = fun (asl,w as g) ->
  let ths = map snd asl in
  let simple = filter (fun th -> not (is_forall (concl th)) &&
                                 not (is_imp (concl th))) ths in
  let decide tm =
    (REWRITE_CONV simple THENC DEPTH_CONV STRING_EQ_CONV THENC
     REWRITE_CONV[PAIR_EQ; option_INJ]) tm in
  let dst = find (fun t -> is_eq (concl t) &&
                   (try fst(dest_const(rator(lhs(concl t)))) = "dstrip_sexp"
                    with Failure _ -> false)) simple in
  let y = snd(dest_pair(rand(rhs(concl dst)))) in
  let use th =
    let c = concl th in
    if not (is_forall c) then failwith "use" else
    let th1 = SPEC y th in
    let ath = decide (lhand(concl th1)) in
    if rhs(concl ath) = `T` then MP th1 (EQT_ELIM ath) else failwith "use" in
  let eqs = mapfilter use ths in
  REWRITE_TAC eqs g;;

let sexpexp_alt_intro = prove
 (`(!s. sexpexp s = sexpexp_alt s) /\
   (!s. sexplist sexpexp s = sexpexp_list s) /\
   (!s. sexplist (sexppair sexppat sexpexp) s = sexppes s) /\
   (!s. sexplist (sexppair odestSEXSTR (sexppair odestSEXSTR sexpexp)) s =
        sexpfuns s) /\
   (!s. sexppair sexppat sexpexp s = sexppatexp s) /\
   (!s. sexppair odestSEXSTR (sexppair odestSEXSTR sexpexp) s = sexpfun s)`,
  MATCH_MP_TAC sexpexp_alt_ind THEN REPEAT CONJ_TAC THEN GEN_TAC THEN
  STRIP_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [sexpexp_def] THEN
    GEN_REWRITE_TAC RAND_CONV [CONJUNCT1 sexpexp_alt_def] THEN
    TOP_CASE_TAC THEN REWRITE_TAC[OPTION_BIND_DEF] THEN TOP_CASE_TAC THEN
    REWRITE_TAC[monad_unitbind_assert; sexptype_alt_intro1] THEN
    FSEXPAUX_DSTRIP_CASES2_TAC
      [`"Raise"`; `"Handle"`; `"Lit"`; `"Con"`; `"Var"`; `"Fun"`; `"App"`;
       `"Log"`; `"If"`; `"Mat"`; `"Let"`; `"Letrec"`; `"Tannot"`; `"Lannot"`]
      FSEXPAUX_IH_TAC;
    GEN_REWRITE_TAC RAND_CONV [CONJUNCT1 (CONJUNCT2 sexpexp_alt_def)] THEN
    CASES_ON `s:simpleSexp_sexp` THEN FS[] THEN
    TOP_CASE_TAC THEN SIMP[] THEN TOP_CASE_TAC THEN SIMP[];
    GEN_REWRITE_TAC RAND_CONV [CONJUNCT1 (funpow 2 CONJUNCT2 sexpexp_alt_def)] THEN
    CASES_ON `s:simpleSexp_sexp` THEN FS[] THEN
    TOP_CASE_TAC THEN SIMP[] THEN TOP_CASE_TAC THEN SIMP[];
    GEN_REWRITE_TAC RAND_CONV [CONJUNCT1 (funpow 3 CONJUNCT2 sexpexp_alt_def)] THEN
    CASES_ON `s:simpleSexp_sexp` THEN FS[] THEN
    TOP_CASE_TAC THEN SIMP[] THEN TOP_CASE_TAC THEN SIMP[];
    GEN_REWRITE_TAC RAND_CONV [CONJUNCT1 (funpow 4 CONJUNCT2 sexpexp_alt_def)] THEN
    REWRITE_TAC[sexppair_def] THEN
    CASES_ON `s:simpleSexp_sexp` THEN FS[sexppat_alt_intro1] THEN
    TOP_CASE_TAC THEN SIMP[] THEN TOP_CASE_TAC THEN SIMP[];
    GEN_REWRITE_TAC RAND_CONV [funpow 5 CONJUNCT2 sexpexp_alt_def] THEN
    REWRITE_TAC[sexppair_def] THEN
    CASES_ON `s:simpleSexp_sexp` THEN FS[] THEN
    CASES_ON `a1:simpleSexp_sexp` THEN FS[] THEN
    TOP_CASE_TAC THEN SIMP[] THEN TOP_CASE_TAC THEN SIMP[] THEN
    TOP_CASE_TAC THEN SIMP[]]);;

let sexpexp_alt_intro1 = prove
 (`sexpexp = sexpexp_alt /\
   sexplist (sexppair odestSEXSTR (sexppair odestSEXSTR sexpexp)) = sexpfuns`,
  REWRITE_TAC[FUN_EQ_THM; sexpexp_alt_intro]);;

let sexptype_def_def = cake_def
  `sexptype_def =
     sexplist
       (sexppair (sexplist odestSEXSTR)
          (sexppair odestSEXSTR
             (sexplist (sexppair odestSEXSTR (sexplist sexptype)))))`;;

let sexpdec_def = cake_def_wf
  `MEASURE simpleSexp_sexp_size`
  FSEXPAUX_TC_TAC
  `sexpdec s =
     OPTION_BIND (dstrip_sexp s)
       (\na. match na with
          (nm,args) ->
             OPTION_CHOICE (OPTION_CHOICE (OPTION_CHOICE (OPTION_CHOICE (OPTION_CHOICE
             (OPTION_CHOICE (OPTION_CHOICE
               (OPTION_IGNORE_BIND (OPTION_GUARD (nm = "Dlet" /\ LENGTH args = 3))
                  (OPTION_APPLY (OPTION_APPLY (OPTION_MAP Dlet (sexplocn (HD args)))
                      (sexppat (EL 1 args))) (sexpexp (EL 2 args))))
               (OPTION_IGNORE_BIND (OPTION_GUARD (nm = "Dletrec" /\ LENGTH args = 2))
                  (OPTION_MAP2 Dletrec (sexplocn (HD args))
                      (sexplist (sexppair odestSEXSTR (sexppair odestSEXSTR sexpexp))
                         (EL 1 args)))))
               (OPTION_IGNORE_BIND (OPTION_GUARD (nm = "Dtype" /\ LENGTH args = 2))
                  (OPTION_MAP2 Dtype (sexplocn (HD args)) (sexptype_def (EL 1 args)))))
               (OPTION_IGNORE_BIND (OPTION_GUARD (nm = "Dtabbrev" /\ LENGTH args = 4))
                  (OPTION_APPLY (OPTION_APPLY (OPTION_APPLY
                      (OPTION_MAP Dtabbrev (sexplocn (EL 0 args)))
                      (sexplist odestSEXSTR (EL 1 args))) (odestSEXSTR (EL 2 args)))
                      (sexptype (EL 3 args)))))
               (OPTION_IGNORE_BIND (OPTION_GUARD (nm = "Denv" /\ LENGTH args = 1))
                  (OPTION_MAP Denv (odestSEXSTR (EL 0 args)))))
               (OPTION_IGNORE_BIND (OPTION_GUARD (nm = "Dexn" /\ LENGTH args = 3))
                  (OPTION_APPLY (OPTION_APPLY (OPTION_MAP Dexn (sexplocn (EL 0 args)))
                      (odestSEXSTR (EL 1 args))) (sexplist sexptype (EL 2 args)))))
               (OPTION_IGNORE_BIND (OPTION_GUARD (nm = "Dmod" /\ LENGTH args = 2))
                  (OPTION_MAP2 Dmod (odestSEXSTR (EL 0 args)) (sexplist sexpdec (EL 1 args)))))
               (OPTION_IGNORE_BIND (OPTION_GUARD (nm = "Dlocal" /\ LENGTH args = 2))
                  (OPTION_MAP2 Dlocal (sexplist sexpdec (EL 0 args))
                      (sexplist sexpdec (EL 1 args))))
          )`;;

let sexpdec_ind = cake_ind "sexpdec";;

(* translator friendly version for bootstrapping *)

let sexpdec_alt_def = cake_def_wf
  `inv_image (MEASURE simpleSexp_sexp_size)
     (\x:simpleSexp_sexp+simpleSexp_sexp. match x with INL y -> y | INR y -> y)`
  FSEXPAUX_TC_TAC
  `(sexpdec_alt s =
      match dstrip_sexp s with
        NONE -> NONE
      | SOME (nm,args) ->
          if nm = "Dlet" /\ LENGTH args = 3 then
            OPTION_APPLY (OPTION_APPLY (OPTION_MAP Dlet (sexplocn (HD args)))
              (sexppat_alt (EL 1 args))) (sexpexp_alt (EL 2 args)) else
          if nm = "Dletrec" /\ LENGTH args = 2 then
            OPTION_MAP2 Dletrec (sexplocn (HD args)) (sexpfuns (EL 1 args)) else
          if nm = "Dtype" /\ LENGTH args = 2 then
            OPTION_MAP2 Dtype (sexplocn (HD args)) (sexptype_def (EL 1 args)) else
          if nm = "Dtabbrev" /\ LENGTH args = 4 then
            OPTION_APPLY (OPTION_APPLY (OPTION_APPLY
              (OPTION_MAP Dtabbrev (sexplocn (EL 0 args)))
              (sexplist odestSEXSTR (EL 1 args))) (odestSEXSTR (EL 2 args)))
              (sexptype_alt (EL 3 args)) else
          if nm = "Denv" /\ LENGTH args = 1 then
            OPTION_MAP Denv (odestSEXSTR (EL 0 args)) else
          if nm = "Dexn" /\ LENGTH args = 3 then
            OPTION_APPLY (OPTION_APPLY (OPTION_MAP Dexn (sexplocn (EL 0 args)))
              (odestSEXSTR (EL 1 args))) (sexptype_list (EL 2 args)) else
          if nm = "Dmod" /\ LENGTH args = 2 then
            OPTION_MAP2 Dmod (odestSEXSTR (EL 0 args)) (sexpdec_list (EL 1 args))
          else
          if nm = "Dlocal" /\ LENGTH args = 2 then
            OPTION_MAP2 Dlocal (sexpdec_list (EL 0 args))
              (sexpdec_list (EL 1 args))
          else NONE) /\
   (sexpdec_list s =
      match s with
        SX_SYM nm -> if nm = "nil" then SOME [] else NONE
      | SX_CONS a d ->
          (match sexpdec_alt a with
             NONE -> NONE
           | SOME h ->
               (match sexpdec_list d with
                  NONE -> NONE
                | SOME t -> SOME (CONS h t)))
      | _ -> NONE)`;;

let sexpdec_alt_ind = cake_ind "sexpdec_alt";;

let sexpdec_alt_intro = prove
 (`(!s. sexpdec s = sexpdec_alt s) /\
   (!s. sexplist sexpdec s = sexpdec_list s)`,
  MATCH_MP_TAC sexpdec_alt_ind THEN CONJ_TAC THEN GEN_TAC THEN STRIP_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [sexpdec_def] THEN
    GEN_REWRITE_TAC RAND_CONV [CONJUNCT1 sexpdec_alt_def] THEN
    TOP_CASE_TAC THEN REWRITE_TAC[OPTION_BIND_DEF] THEN TOP_CASE_TAC THEN
    REWRITE_TAC[monad_unitbind_assert; sexppat_alt_intro1; sexpexp_alt_intro1;
                sexptype_alt_intro1] THEN
    FSEXPAUX_DSTRIP_CASES2_TAC
      [`"Dlet"`; `"Dletrec"`; `"Dtype"`; `"Dtabbrev"`; `"Denv"`; `"Dexn"`;
       `"Dmod"`; `"Dlocal"`]
      FSEXPAUX_IH_TAC;
    GEN_REWRITE_TAC RAND_CONV [CONJUNCT2 sexpdec_alt_def] THEN
    CASES_ON `s:simpleSexp_sexp` THEN FS[] THEN
    TOP_CASE_TAC THEN SIMP[] THEN TOP_CASE_TAC THEN SIMP[]]);;

let sexpdec_alt_intro1 = prove
 (`sexpdec = sexpdec_alt /\ sexplist sexpdec = sexpdec_list`,
  REWRITE_TAC[FUN_EQ_THM; sexpdec_alt_intro]);;

(* now the reverse: toSexp *)

(* HOL4: listsexp = FOLDR SX_CONS nil (eta-expanded: FOLDR f e l is      *)
(* ITLIST f l e)                                                          *)

let listsexp_def = cake_def
  `listsexp l = ITLIST SX_CONS l (SX_SYM "nil")`;;

let listsexp_thm = prove
 (`listsexp [] = SX_SYM "nil" /\
   listsexp (CONS h t) = SX_CONS h (listsexp t)`,
  REWRITE_TAC[listsexp_def; ITLIST]);;
let _ = cake_add_simps [listsexp_thm];;

let listsexp_11 = prove
 (`!l1 l2. listsexp l1 = listsexp l2 <=> l1 = l2`,
  REWRITE_TAC[listsexp_def; FOLDR_SX_CONS_INJ]);;
let _ = cake_add_simps [listsexp_11];;

let optsexp_def = cake_def
  `(optsexp NONE = SX_SYM "NONE") /\
   (optsexp (SOME x) = listsexp [SX_SYM "SOME"; x])`;;

let optsexp_11 = prove
 (`optsexp o1 = optsexp o2 <=> o1 = o2`,
  CASES_ON `o1:simpleSexp_sexp option` THEN
  CASES_ON `o2:simpleSexp_sexp option` THEN SIMP[optsexp_def]);;
let _ = cake_add_simps [optsexp_11];;

let idsexp_def = cake_def_clauses
  [`idsexp (Short n:(mlstring,mlstring)id) = listsexp [SX_SYM "Short"; SEXSTR (explode n)]`;
   `idsexp (Long ns (n:(mlstring,mlstring)id)) =
      listsexp [SX_SYM "Long"; SEXSTR (explode ns); idsexp n]`];;

let idsexp_11 = prove
 (`!i1 i2. idsexp i1 = idsexp i2 <=> i1 = i2`,
  MATCH_MP_TAC id_INDUCT THEN REPEAT STRIP_TAC THEN
  CASES_ON `i2:(mlstring,mlstring)id` THEN SIMP[idsexp_def]);;
let _ = cake_add_simps [idsexp_11];;

let typesexp_def = cake_def
  `(typesexp (Atvar s) = listsexp [SX_SYM "Atvar"; SEXSTR (explode s)]) /\
   (typesexp (Atfun t1 t2) = listsexp [SX_SYM "Atfun"; typesexp t1; typesexp t2]) /\
   (typesexp (Attup ts) =
      listsexp [SX_SYM "Attup"; listsexp (MAP typesexp ts)]) /\
   (typesexp (Atapp ts tc) =
      listsexp [SX_SYM "Atapp"; listsexp (MAP typesexp ts); idsexp tc])`;;

let typesexp_ind = cake_ind "typesexp";;

(* a MAP of a function injective on the list *)

let FSEXPAUX_MAP_11 = prove
 (`!(f:A->B) xs ys. (!x y. MEM x xs ==> (f x = f y <=> x = y))
                    ==> (MAP f xs = MAP f ys <=> xs = ys)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP; MEM; NOT_CONS_NIL; CONS_11] THEN ASM_MESON_TAC[]);;

let typesexp_11 = prove
 (`!t1 t2. typesexp t1 = typesexp t2 <=> t1 = t2`,
  MATCH_MP_TAC typesexp_ind THEN REPEAT STRIP_TAC THEN
  W(fun (asl,w) -> CASES_ON (rand(rhs(lhand w)))) THEN
  SIMP[typesexp_def; FSEXPAUX_MAP_11]);;
let _ = cake_add_simps [typesexp_11];;

(* HOL4 Num is num_of_int, w2n is val *)

let litsexp_def = cake_def_clauses
  [`litsexp (IntLit i) =
      if i < &0 then listsexp [SX_SYM "-"; SX_NUM (num_of_int (--i))]
      else SX_NUM (num_of_int i)`;
   `litsexp (Char c) = listsexp [SX_SYM "char"; SEXSTR [c]]`;
   `litsexp (StrLit s) = SEXSTR (explode s)`;
   `litsexp (Word8 w) = listsexp [SX_SYM "word8"; SX_NUM (val w)]`;
   `litsexp (Word64 w) = listsexp [SX_SYM "word64"; SX_NUM (val w)]`;
   `litsexp (Float64 w) = listsexp [SX_SYM "float64"; SX_NUM (val w)]`];;

let FSEXPAUX_num_of_int_11 = prove
 (`!a b. &0 <= a /\ &0 <= b ==> (num_of_int a = num_of_int b <=> a = b)`,
  MESON_TAC[INT_OF_NUM_OF_INT]);;

let litsexp_11 = prove
 (`!l1 l2. litsexp l1 = litsexp l2 <=> l1 = l2`,
  GEN_TAC THEN CASES_ON `l1:lit` THEN GEN_TAC THEN CASES_ON `l2:lit` THEN
  SIMP[litsexp_def] THEN REPEAT COND_CASES_TAC THEN SIMP[VAL_EQ] THEN
  TRY ASM_INT_ARITH_TAC THENL
   [MP_TAC(SPECL [`--a:int`; `--a':int`] FSEXPAUX_num_of_int_11);
    MP_TAC(SPECL [`a:int`; `a':int`] FSEXPAUX_num_of_int_11)] THEN
  ANTS_TAC THEN TRY ASM_INT_ARITH_TAC THEN DISCH_THEN SUBST1_TAC THEN
  INT_ARITH_TAC);;
let _ = cake_add_simps [litsexp_11];;

let patsexp_def = cake_def
  `(patsexp Pany = listsexp [SX_SYM "Pany"]) /\
   (patsexp (Pvar s) = SEXSTR (explode s)) /\
   (patsexp (Plit l) = listsexp [SX_SYM "Plit"; litsexp l]) /\
   (patsexp (Pcon cn ps) =
      listsexp [SX_SYM "Pcon"; optsexp (OPTION_MAP idsexp cn);
                listsexp (MAP patsexp ps)]) /\
   (patsexp (Pas p i) = listsexp [SX_SYM "Pas"; patsexp p; SEXSTR (explode i)]) /\
   (patsexp (Pref p) = listsexp [SX_SYM "Pref"; patsexp p]) /\
   (patsexp (Ptannot p t) = listsexp [SX_SYM "Ptannot"; patsexp p; typesexp t])`;;

let patsexp_ind = cake_ind "patsexp";;

let patsexp_11 = prove
 (`!p1 p2. patsexp p1 = patsexp p2 <=> p1 = p2`,
  MATCH_MP_TAC patsexp_ind THEN REPEAT STRIP_TAC THEN
  W(fun (asl,w) -> CASES_ON (rand(rhs(lhand w)))) THEN
  SIMP[patsexp_def; FSEXPAUX_MAP_11] THEN
  MAP_EVERY (fun v -> CASES_ON v THEN SIMP[])
    [`cn:((mlstring,mlstring)id)option`; `a0:((mlstring,mlstring)id)option`]);;
let _ = cake_add_simps [patsexp_11];;

let testsexp_def = cake_def
  `(testsexp Equal = SX_SYM "Equal") /\
   (testsexp (Compare Lt) = SX_SYM "Less") /\
   (testsexp (Compare Leq) = SX_SYM "LessEq") /\
   (testsexp (Compare Gt) = SX_SYM "Greater") /\
   (testsexp (Compare Geq) = SX_SYM "GreaterEq") /\
   (testsexp (AltCompare Lt) = SX_SYM "AltLess") /\
   (testsexp (AltCompare Leq) = SX_SYM "AltLessEq") /\
   (testsexp (AltCompare Gt) = SX_SYM "AltGreater") /\
   (testsexp (AltCompare Geq) = SX_SYM "AltGreaterEq")`;;

(* the inverse first (HOL4 proves this theorem by cases on both sides) *)

let testsexp_11 = prove
 (`!l1 l2. testsexp l1 = testsexp l2 <=> l1 = l2`,
  SUBGOAL_THEN `!x. fromSexp_decode_test (testsexp x) = SOME x` MP_TAC THENL
   [GEN_TAC THEN CASES_ON `x:test` THEN FSEXPAUX_SPLIT_TYPES_TAC [`:opb`] THEN
    REWRITE_TAC[testsexp_def; fromSexp_decode_test_def] THEN
    CONV_TAC(DEPTH_CONV STRING_EQ_CONV) THEN REWRITE_TAC[];
    MESON_TAC[option_INJ]]);;
let _ = cake_add_simps [testsexp_11];;

let sexptest_testsexp = prove
 (`!x. fromSexp_decode_test (testsexp x) = SOME x`,
  GEN_TAC THEN CASES_ON `x:test` THEN FSEXPAUX_SPLIT_TYPES_TAC [`:opb`] THEN
  REWRITE_TAC[testsexp_def; fromSexp_decode_test_def] THEN
  CONV_TAC(DEPTH_CONV STRING_EQ_CONV) THEN REWRITE_TAC[]);;
let _ = cake_add_simps [sexptest_testsexp];;

let arithsexp_def = cake_def
  `(arithsexp Add = SX_SYM "Add") /\
   (arithsexp Sub = SX_SYM "Sub") /\
   (arithsexp Mul = SX_SYM "Mul") /\
   (arithsexp Div = SX_SYM "Div") /\
   (arithsexp Mod = SX_SYM "Mod") /\
   (arithsexp And = SX_SYM "And") /\
   (arithsexp Xor = SX_SYM "Xor") /\
   (arithsexp Or = SX_SYM "Or") /\
   (arithsexp Not = SX_SYM "Not") /\
   (arithsexp Neg = SX_SYM "Neg") /\
   (arithsexp Abs = SX_SYM "Abs") /\
   (arithsexp Sqrt = SX_SYM "Sqrt") /\
   (arithsexp FMA = SX_SYM "FMA")`;;

let arithsexp_11 = prove
 (`!l1 l2. arithsexp l1 = arithsexp l2 <=> l1 = l2`,
  SUBGOAL_THEN `!x. sexparith (arithsexp x) = SOME x` MP_TAC THENL
   [GEN_TAC THEN CASES_ON `x:arith` THEN
    REWRITE_TAC[arithsexp_def; sexparith_def] THEN
    CONV_TAC(DEPTH_CONV STRING_EQ_CONV) THEN REWRITE_TAC[];
    MESON_TAC[option_INJ]]);;
let _ = cake_add_simps [arithsexp_11];;

let arithsexp_sexparith = prove
 (`!x. sexparith (arithsexp x) = SOME x`,
  GEN_TAC THEN CASES_ON `x:arith` THEN
  REWRITE_TAC[arithsexp_def; sexparith_def] THEN
  CONV_TAC(DEPTH_CONV STRING_EQ_CONV) THEN REWRITE_TAC[]);;
let _ = cake_add_simps [arithsexp_sexparith];;

let prim_typesexp_def = cake_def
  `(prim_typesexp BoolT = SX_SYM "BoolT") /\
   (prim_typesexp IntT = SX_SYM "IntT") /\
   (prim_typesexp CharT = SX_SYM "CharT") /\
   (prim_typesexp StrT = SX_SYM "StrT") /\
   (prim_typesexp (WordT W8) = SX_SYM "Word8T") /\
   (prim_typesexp (WordT W64) = SX_SYM "Word64T") /\
   (prim_typesexp Float64T = SX_SYM "Float64T")`;;

let sexplist_listsexp_matchable = prove
 (`!g gl. (!x. MEM x l ==> (f:simpleSexp_sexp->A option) (g x) = SOME x) /\
          gl = MAP g l
          ==> sexplist f (listsexp gl) = SOME l`,
  SPEC_TAC(`l:A list`,`l:A list`) THEN LIST_INDUCT_TAC THEN
  SIMP[MAP; MEM] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `g:A->simpleSexp_sexp`) THEN SIMP[]);;

let dstrip_sexp_SX_STR = prove
 (`dstrip_sexp (SX_STR s) = NONE`,
  REWRITE_TAC[dstrip_sexp_def]);;
let _ = cake_add_simps [dstrip_sexp_SX_STR];;

let dstrip_sexp_SEXSTR = prove
 (`dstrip_sexp (SEXSTR s) = NONE`,
  REWRITE_TAC[SEXSTR_def; dstrip_sexp_def]);;
let _ = cake_add_simps [dstrip_sexp_SEXSTR];;

let odestSXSTR_SOME = prove
 (`(odestSXSTR s = SOME y <=> s = SX_STR (explode y)) /\
   (SOME y = odestSXSTR s <=> s = SX_STR (explode y))`,
  CASES_ON `s:simpleSexp_sexp` THEN SIMP[] THEN MESON_TAC[explode_implode;
    implode_explode]);;
let _ = cake_add_simps [odestSXSTR_SOME];;

let odestSEXSTR_SOME = prove
 (`(odestSEXSTR s = SOME y <=> s = SEXSTR (explode y)) /\
   (SOME y = odestSEXSTR s <=> s = SEXSTR (explode y))`,
  MATCH_MP_TAC(TAUT `(a <=> c) /\ (b <=> a) ==> (a <=> c) /\ (b <=> c)`) THEN
  CONJ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  CASES_ON `s:simpleSexp_sexp` THEN SIMP[SEXSTR_def] THEN
  MESON_TAC[decode_encode_control; encode_decode_control; explode_implode;
            implode_explode; option_INJ]);;
let _ = cake_add_simps [odestSEXSTR_SOME];;

let odestSXNUM_SOME = prove
 (`(odestSXNUM s = SOME n <=> s = SX_NUM n) /\
   (SOME n = odestSXNUM s <=> s = SX_NUM n)`,
  CASES_ON `s:simpleSexp_sexp` THEN SIMP[] THEN MESON_TAC[]);;
let _ = cake_add_simps [odestSXNUM_SOME];;

let odestSXSTR_SX_STR = prove
 (`odestSXSTR (SX_STR s) = SOME (implode s)`,
  SIMP[]);;
let _ = cake_add_simps [odestSXSTR_SX_STR];;

let odestSEXSTR_SEXSTR = prove
 (`odestSEXSTR (SEXSTR s) = SOME (implode s)`,
  SIMP[SEXSTR_def]);;
let _ = cake_add_simps [odestSEXSTR_SEXSTR];;

let odestSXNUM_SX_NUM = prove
 (`odestSXNUM (SX_NUM n) = SOME n`,
  SIMP[]);;
let _ = cake_add_simps [odestSXNUM_SX_NUM];;

let odestSXSYM_SX_SYM = prove
 (`odestSXSYM (SX_SYM s) = SOME (implode s)`,
  SIMP[]);;
let _ = cake_add_simps [odestSXSYM_SX_SYM];;

let odestSXSTR_listsexp = prove
 (`odestSXSTR (listsexp l) = NONE`,
  CASES_ON `l:simpleSexp_sexp list` THEN SIMP[]);;
let _ = cake_add_simps [odestSXSTR_listsexp];;

let odestSEXSTR_listsexp = prove
 (`odestSEXSTR (listsexp l) = NONE`,
  CASES_ON `l:simpleSexp_sexp list` THEN SIMP[]);;
let _ = cake_add_simps [odestSEXSTR_listsexp];;

let odestSXNUM_listsexp = prove
 (`odestSXNUM (listsexp l) = NONE`,
  CASES_ON `l:simpleSexp_sexp list` THEN SIMP[]);;
let _ = cake_add_simps [odestSXNUM_listsexp];;

let strip_sxcons_listsexp = prove
 (`strip_sxcons (listsexp ls) = SOME ls`,
  SPEC_TAC(`ls:simpleSexp_sexp list`,`ls:simpleSexp_sexp list`) THEN
  LIST_INDUCT_TAC THEN SIMP[]);;
let _ = cake_add_simps [strip_sxcons_listsexp];;

let dstrip_sexp_listsexp = prove
 (CASE_TERM
  `dstrip_sexp (listsexp ls) =
     match ls with CONS (SX_SYM x) xs -> SOME (x,xs) | _ -> NONE`,
  CASES_ON `ls:simpleSexp_sexp list` THEN SIMP[dstrip_sexp_def] THEN
  CASES_ON `a0:simpleSexp_sexp` THEN SIMP[dstrip_sexp_def]);;
let _ = cake_add_simps [dstrip_sexp_listsexp];;

let sexplist_listsexp_rwt = prove
 (`(!x. MEM x l ==> (f:simpleSexp_sexp->A option) (g x) = SOME x)
   ==> sexplist f (listsexp (MAP g l)) = SOME l`,
  MESON_TAC[sexplist_listsexp_matchable]);;
let _ = cake_add_simps [sexplist_listsexp_rwt];;

let sexplist_listsexp_imp = prove
 (`sexplist (f:simpleSexp_sexp->A option) (listsexp l1) = SOME l2
   ==> !n. n < LENGTH l1 ==> f (EL n l1) = SOME (EL n l2)`,
  SPEC_TAC(`l2:A list`,`l2:A list`) THEN
  SPEC_TAC(`l1:simpleSexp_sexp list`,`l1:simpleSexp_sexp list`) THEN
  LIST_INDUCT_TAC THEN SIMP[LENGTH] THEN REPEAT STRIP_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  CASES_ON `n:num` THEN REWRITE_TAC[EL; HD; TL] THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x':A list`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let sexpopt_optsexp = prove
 (`(!y. x = SOME y ==> (f:simpleSexp_sexp->A option) (g y) = x)
   ==> sexpopt f (optsexp (OPTION_MAP g x)) = SOME x`,
  CASES_ON `x:A option` THEN
  SIMP[sexpopt_def; optsexp_def; dstrip_sexp_def] THEN
  CONV_TAC(DEPTH_CONV STRING_EQ_CONV) THEN SIMP[]);;
let _ = cake_add_simps [sexpopt_optsexp];;

let sexpid_odestSEXSTR_idsexp = prove
 (`sexpid odestSEXSTR (idsexp i) = SOME i`,
  SPEC_TAC(`i:(mlstring,mlstring)id`,`i:(mlstring,mlstring)id`) THEN
  MATCH_MP_TAC id_INDUCT THEN REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [sexpid_def] THEN SIMP[idsexp_def; dstrip_sexp_def] THEN
  CONV_TAC(DEPTH_CONV STRING_EQ_CONV) THEN SIMP[]);;
let _ = cake_add_simps [sexpid_odestSEXSTR_idsexp];;

let dstrip_sexp_thm = prove
 (`dstrip_sexp (SX_CONS (SX_SYM s) args) =
     OPTION_MAP (\t. (s,t)) (strip_sxcons args) /\
   dstrip_sexp (SX_CONS (SX_NUM n) args) = NONE /\
   dstrip_sexp (SX_CONS (SX_STR str) args) = NONE /\
   dstrip_sexp (SX_CONS (SX_CONS s1 s2) args) = NONE /\
   dstrip_sexp (SX_NUM n) = NONE /\
   dstrip_sexp (SX_SYM s) = NONE /\
   dstrip_sexp (SX_STR str) = NONE`,
  SIMP[dstrip_sexp_def]);;
let _ = cake_add_simps [dstrip_sexp_thm];;

let sexptype_typesexp = prove
 (`sexptype (typesexp t) = SOME t`,
  SPEC_TAC(`t:ast_t`,`t:ast_t`) THEN MATCH_MP_TAC FSEXPAUX_type_ind THEN
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [sexptype_def] THEN
  SIMP[typesexp_def] THEN CONV_TAC(DEPTH_CONV STRING_EQ_CONV) THEN
  SIMP[] THEN MATCH_MP_TAC sexplist_listsexp_rwt THEN
  ASM_MESON_TAC[ALL_MEM]);;
let _ = cake_add_simps [sexptype_typesexp];;

let sexpprim_type_testsexp = prove
 (`!x. decode_prim_type (prim_typesexp x) = SOME x`,
  GEN_TAC THEN CASES_ON `x:prim_type` THEN FSEXPAUX_SPLIT_TYPES_TAC [`:word_size`] THEN
  REWRITE_TAC[prim_typesexp_def; decode_prim_type_def] THEN
  CONV_TAC(DEPTH_CONV STRING_EQ_CONV) THEN REWRITE_TAC[]);;
let _ = cake_add_simps [sexpprim_type_testsexp];;

let prim_typesexp_11 = prove
 (`!l1 l2. prim_typesexp l1 = prim_typesexp l2 <=> l1 = l2`,
  MESON_TAC[sexpprim_type_testsexp; option_INJ]);;
let _ = cake_add_simps [prim_typesexp_11];;

let opsexp_def = sem1aux_def
  `(opsexp (Shift W8 Lsl n) = SX_CONS (SX_SYM "Shift8Lsl") (SX_NUM n)) /\
   (opsexp (Shift W8 Lsr n) = SX_CONS (SX_SYM "Shift8Lsr") (SX_NUM n)) /\
   (opsexp (Shift W8 Asr n) = SX_CONS (SX_SYM "Shift8Asr") (SX_NUM n)) /\
   (opsexp (Shift W8 Ror n) = SX_CONS (SX_SYM "Shift8Ror") (SX_NUM n)) /\
   (opsexp (Shift W64 Lsl n) = SX_CONS (SX_SYM "Shift64Lsl") (SX_NUM n)) /\
   (opsexp (Shift W64 Lsr n) = SX_CONS (SX_SYM "Shift64Lsr") (SX_NUM n)) /\
   (opsexp (Shift W64 Asr n) = SX_CONS (SX_SYM "Shift64Asr") (SX_NUM n)) /\
   (opsexp (Shift W64 Ror n) = SX_CONS (SX_SYM "Shift64Ror") (SX_NUM n)) /\
   (opsexp Equality = SX_SYM "Equality") /\
   (opsexp Opapp = SX_SYM "Opapp") /\
   (opsexp Opassign = SX_SYM "Opassign") /\
   (opsexp Opref = SX_SYM "Opref") /\
   (opsexp Opderef = SX_SYM "Opderef") /\
   (opsexp Aw8alloc = SX_SYM "Aw8alloc") /\
   (opsexp Aw8sub = SX_SYM "Aw8sub") /\
   (opsexp Aw8length = SX_SYM "Aw8length") /\
   (opsexp Aw8update = SX_SYM "Aw8update") /\
   (opsexp Aw8sub_unsafe = SX_SYM "Aw8subunsafe") /\
   (opsexp Aw8update_unsafe = SX_SYM "Aw8updateunsafe") /\
   (opsexp CopyStrStr = SX_SYM "CopyStrStr") /\
   (opsexp CopyStrAw8 = SX_SYM "CopyStrAw8") /\
   (opsexp CopyAw8Str = SX_SYM "CopyAw8Str") /\
   (opsexp CopyAw8Aw8 = SX_SYM "CopyAw8Aw8") /\
   (opsexp XorAw8Str_unsafe = SX_SYM "XorAw8Strunsafe") /\
   (opsexp Implode = SX_SYM "Implode") /\
   (opsexp Explode = SX_SYM "Explode") /\
   (opsexp Strsub = SX_SYM "Strsub") /\
   (opsexp Strlen = SX_SYM "Strlen") /\
   (opsexp Strcat = SX_SYM "Strcat") /\
   (opsexp VfromList = SX_SYM "VfromList") /\
   (opsexp Vsub = SX_SYM "Vsub") /\
   (opsexp Vsub_unsafe = SX_SYM "Vsubunsafe") /\
   (opsexp Vlength = SX_SYM "Vlength") /\
   (opsexp ListAppend = SX_SYM "ListAppend") /\
   (opsexp Aalloc = SX_SYM "Aalloc") /\
   (opsexp AallocEmpty = SX_SYM "AallocEmpty") /\
   (opsexp AallocFixed = SX_SYM "AallocFixed") /\
   (opsexp Asub = SX_SYM "Asub") /\
   (opsexp Alength = SX_SYM "Alength") /\
   (opsexp Aupdate = SX_SYM "Aupdate") /\
   (opsexp Asub_unsafe = SX_SYM "Asubunsafe") /\
   (opsexp Aupdate_unsafe = SX_SYM "Aupdateunsafe") /\
   (opsexp ConfigGC = SX_SYM "ConfigGC") /\
   (opsexp Eval = SX_SYM "Eval") /\
   (opsexp Env_id = SX_SYM "Envid") /\
   (opsexp (FFI s) = SX_CONS (SX_SYM "FFI") (SEXSTR (explode s))) /\
   (opsexp (ThunkOp ForceThunk) = SX_SYM "ForceThunk") /\
   (opsexp (ThunkOp (AllocThunk m)) =
      SX_CONS (SX_SYM "AllocThunk") (SX_SYM (encode_thunk_mode m))) /\
   (opsexp (ThunkOp (UpdateThunk m)) =
      SX_CONS (SX_SYM "UpdateThunk") (SX_SYM (encode_thunk_mode m))) /\
   (opsexp (Arith a prim_type) =
      SX_CONS (SX_SYM "Arith") (SX_CONS (arithsexp a) (prim_typesexp prim_type))) /\
   (opsexp (FromTo ty1 ty2) =
      SX_CONS (SX_SYM "FromTo") (SX_CONS (prim_typesexp ty1) (prim_typesexp ty2))) /\
   (opsexp (Test test prim_type) =
      SX_CONS (SX_SYM "Test") (SX_CONS (testsexp test) (prim_typesexp prim_type)))`;;

let sexpop_opsexp = prove
 (`sexpop (opsexp op) = SOME op`,
  CASES_ON `op:op` THEN
  FSEXPAUX_SPLIT_TYPES_TAC [`:word_size`; `:shift`; `:thunk_op`; `:thunk_mode`] THEN
  REWRITE_TAC[opsexp_def; sexpop_def; encode_thunk_mode_def;
              decode_thunk_mode_def; SEXSTR_def] THEN
  CONV_TAC(DEPTH_CONV STRING_EQ_CONV) THEN
  REWRITE_TAC[COND_CLAUSES; option_CASE; sexptest_testsexp;
              arithsexp_sexparith; sexpprim_type_testsexp;
              decode_encode_control; OPTION_MAP_DEF; o_THM; implode_explode]);;
let _ = cake_add_simps [sexpop_opsexp];;

let opsexp_11 = prove
 (`!o1 o2. opsexp o1 = opsexp o2 <=> o1 = o2`,
  REPEAT GEN_TAC THEN EQ_TAC THEN SIMP[] THEN
  DISCH_THEN(MP_TAC o AP_TERM `sexpop`) THEN SIMP[]);;
let _ = cake_add_simps [opsexp_11];;

let logsexp_def = cake_def
  `(logsexp Andalso = SX_SYM "Andalso") /\
   (logsexp Orelse = SX_SYM "Orelse")`;;

let logsexp_11 = prove
 (`!l1 l2. logsexp l1 = logsexp l2 <=> l1 = l2`,
  REPEAT GEN_TAC THEN CASES_ON `l1:lop` THEN CASES_ON `l2:lop` THEN
  SIMP[logsexp_def]);;
let _ = cake_add_simps [logsexp_11];;

let locnsexp_def = cake_def
  `(locnsexp (POSN n1 n2) = listsexp (MAP SX_NUM [n1; n2])) /\
   (locnsexp UNKNOWNpt = SX_SYM "unk") /\
   (locnsexp EOFpt = SX_SYM "eof")`;;

let locnsexp_11 = prove
 (`locnsexp p1 = locnsexp p2 <=> p1 = p2`,
  CASES_ON `p1:locn` THEN CASES_ON `p2:locn` THEN SIMP[locnsexp_def]);;
let _ = cake_add_simps [locnsexp_11];;

let locssexp_def = cake_def
  `locssexp (Locs p1 p2) = listsexp (MAP locnsexp [p1; p2])`;;

let locssexp_11 = prove
 (`!l1 l2. locssexp l1 = locssexp l2 <=> l1 = l2`,
  REPEAT GEN_TAC THEN CASES_ON `l1:locs` THEN CASES_ON `l2:locs` THEN
  SIMP[locssexp_def]);;
let _ = cake_add_simps [locssexp_11];;

(* HOL4's list form <<a; b; c>> of simpleSexp is SX_CONS a (SX_CONS b       *)
(* (SX_CONS c nil)), written out; the paired lambdas (\(p,e). t) are       *)
(* (\pe. match pe with (p,e) -> t)                                         *)

let expsexp_def = sem1aux_def
  `(expsexp (Raise e) = SX_CONS (SX_SYM "Raise") (SX_CONS (expsexp e) (SX_SYM "nil"))) /\
   (expsexp (Handle e pes) =
      SX_CONS (SX_SYM "Handle") (SX_CONS (expsexp e) (SX_CONS
        (listsexp (MAP (\pe. match pe with (p,e) -> SX_CONS (patsexp p) (expsexp e)) pes))
        (SX_SYM "nil")))) /\
   (expsexp (Lit l) = listsexp [SX_SYM "Lit"; litsexp l]) /\
   (expsexp (Con cn es) =
      listsexp [SX_SYM "Con"; optsexp (OPTION_MAP idsexp cn);
                listsexp (MAP expsexp es)]) /\
   (expsexp (Var id) = listsexp [SX_SYM "Var"; idsexp id]) /\
   (expsexp (Fun x e) = listsexp [SX_SYM "Fun"; SEXSTR (explode x); expsexp e]) /\
   (expsexp (App op es) =
      listsexp [SX_SYM "App"; opsexp op; listsexp (MAP expsexp es)]) /\
   (expsexp (Log lop e1 e2) =
      SX_CONS (SX_SYM "Log") (SX_CONS (logsexp lop) (SX_CONS (expsexp e1)
        (SX_CONS (expsexp e2) (SX_SYM "nil"))))) /\
   (expsexp (If e1 e2 e3) =
      SX_CONS (SX_SYM "If") (SX_CONS (expsexp e1) (SX_CONS (expsexp e2)
        (SX_CONS (expsexp e3) (SX_SYM "nil"))))) /\
   (expsexp (Mat e pes) =
      SX_CONS (SX_SYM "Mat") (SX_CONS (expsexp e) (SX_CONS
        (listsexp (MAP (\pe. match pe with (p,e) -> SX_CONS (patsexp p) (expsexp e)) pes))
        (SX_SYM "nil")))) /\
   (expsexp (Let so e1 e2) =
      SX_CONS (SX_SYM "Let") (SX_CONS (optsexp (OPTION_MAP (SEXSTR o explode) so))
        (SX_CONS (expsexp e1) (SX_CONS (expsexp e2) (SX_SYM "nil"))))) /\
   (expsexp (Letrec funs e) =
      SX_CONS (SX_SYM "Letrec") (SX_CONS
        (listsexp (MAP (\xyz. match xyz with
                         (x,y,z) -> SX_CONS (SEXSTR (explode x))
                                      (SX_CONS (SEXSTR (explode y)) (expsexp z)))
                       funs))
        (SX_CONS (expsexp e) (SX_SYM "nil")))) /\
   (expsexp (Tannot e t) =
      SX_CONS (SX_SYM "Tannot") (SX_CONS (expsexp e) (SX_CONS (typesexp t)
        (SX_SYM "nil")))) /\
   (expsexp (Lannot e loc) =
      SX_CONS (SX_SYM "Lannot") (SX_CONS (expsexp e) (SX_CONS (locssexp loc)
        (SX_SYM "nil"))))`;;

let expsexp_ind = cake_ind "expsexp";;

let SEXSTR_explode_11 = prove
 (`(SEXSTR o explode) s1 = (SEXSTR o explode) s2 ==> s1 = s2`,
  SIMP[o_THM]);;

(* from an assumption MAP f xs = MAP f ys, xs = ys (MAP_EQ_MAP_IMP, with   *)
(* inj_tac for the injectivity of f on the elements)                       *)

let FSEXPAUX_MAP_EQ_TAC (inj_tac:tactic) : tactic = fun (asl,w as g) ->
  let is_map t = try fst(dest_const(fst(strip_comb t))) = "MAP"
                 with Failure _ -> false in
  let th = find (fun th -> is_eq(concl th) && is_map(lhs(concl th)) &&
                           is_map(rhs(concl th))) (map snd asl) in
  let l,r = dest_eq(concl th) in
  let f,xs = dest_comb l in
  let ys = rand r in
  let f = rand f in
  (UNDISCH_THEN (concl th) (fun th ->
     MP_TAC (ISPECL [xs; ys; f] MAP_EQ_MAP_IMP) THEN ANTS_TAC THENL
      [inj_tac; DISCH_THEN (fun imp -> ASSUME_TAC (MP imp th))])) g;;

let expsexp_11 = prove
 (`!e1 e2. expsexp e1 = expsexp e2 ==> e1 = e2`,
  MATCH_MP_TAC expsexp_ind THEN REPEAT STRIP_TAC THEN
  W(fun (asl,w) -> CASES_ON (rhs w)) THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[expsexp_def] THEN SIMP_NOASM[] THEN
  STRIP_TAC THEN
  REPEAT (FSEXPAUX_MAP_EQ_TAC
    (REWRITE_TAC[FORALL_PAIR_THM] THEN SIMP_NOASM[] THEN ASM_MESON_TAC[])) THEN
  ASM_MESON_TAC[OPTION_MAP_INJ; idsexp_11; SEXSTR_explode_11]);;

let type_defsexp_def = cake_def
  `type_defsexp =
     listsexp o
     MAP (\xxl. match xxl with
            (xs,x,ls) ->
              SX_CONS (listsexp (MAP (SEXSTR o explode) xs))
                (SX_CONS (SEXSTR (explode x))
                   (listsexp (MAP (\yts. match yts with
                                     (y,ts) -> SX_CONS (SEXSTR (explode y))
                                                 (listsexp (MAP typesexp ts)))
                                  ls))))`;;

(* a MAP of an injective function (as a conditional rewrite) *)

let FSEXPAUX_MAP_INJ_EQ = prove
 (`!(f:A->B). (!x y. f x = f y <=> x = y)
              ==> !xs ys. MAP f xs = MAP f ys <=> xs = ys`,
  MESON_TAC[FSEXPAUX_MAP_11]);;

let type_defsexp_11 = prove
 (`!t1 t2. type_defsexp t1 = type_defsexp t2 <=> t1 = t2`,
  SIMP[type_defsexp_def; o_THM; FSEXPAUX_MAP_INJ_EQ; FORALL_PAIR_THM]);;
let _ = cake_add_simps [type_defsexp_11];;

(* HOL4 dec1_size is the kit's dec_size_aux1 *)

let dec1_size_eq = prove
 (`dec_size_aux1 xs = list_size dec_size xs`,
  REWRITE_TAC(size_aux_eqs "dec"));;

(* HOL4: mem_size_lemma *)

let fromSexp_mem_size_lemma = prove
 (`list_size (sz:A->num) xs < N ==> (MEM x xs ==> sz x < N)`,
  SPEC_TAC(`xs:A list`,`xs:A list`) THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[list_size_def; MEM] THEN DISCH_TAC THEN
  DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THEN ASM_ARITH_TAC]);;

let decsexp_def = cake_def
  `(decsexp (Dlet locs p e) =
      SX_CONS (SX_SYM "Dlet") (SX_CONS (locssexp locs) (SX_CONS (patsexp p)
        (SX_CONS (expsexp e) (SX_SYM "nil"))))) /\
   (decsexp (Dletrec locs funs) =
      listsexp [SX_SYM "Dletrec"; locssexp locs;
                listsexp (MAP (\fxe. match fxe with
                                 (f,x,e) -> SX_CONS (SEXSTR (explode f))
                                              (SX_CONS (SEXSTR (explode x))
                                                 (expsexp e)))
                              funs)]) /\
   (decsexp (Dtype locs td) =
      SX_CONS (SX_SYM "Dtype") (SX_CONS (locssexp locs)
        (SX_CONS (type_defsexp td) (SX_SYM "nil")))) /\
   (decsexp (Dtabbrev locs ns x t) =
      SX_CONS (SX_SYM "Dtabbrev") (SX_CONS (locssexp locs)
        (SX_CONS (listsexp (MAP (SEXSTR o explode) ns))
           (SX_CONS (SEXSTR (explode x)) (SX_CONS (typesexp t) (SX_SYM "nil")))))) /\
   (decsexp (Denv name) =
      SX_CONS (SX_SYM "Denv") (SX_CONS (SEXSTR (explode name)) (SX_SYM "nil"))) /\
   (decsexp (Dexn locs x ts) =
      SX_CONS (SX_SYM "Dexn") (SX_CONS (locssexp locs)
        (SX_CONS (SEXSTR (explode x))
           (SX_CONS (listsexp (MAP typesexp ts)) (SX_SYM "nil"))))) /\
   (decsexp (Dmod name decs) =
      SX_CONS (SX_SYM "Dmod") (SX_CONS (SEXSTR (explode name))
        (SX_CONS (listsexp (MAP decsexp decs)) (SX_SYM "nil")))) /\
   (decsexp (Dlocal ldecs decs) =
      listsexp [SX_SYM "Dlocal"; listsexp (MAP decsexp ldecs);
                listsexp (MAP decsexp decs)])`;;

let decsexp_ind = cake_ind "decsexp";;

let decsexp_11 = prove
 (`!d1 d2. decsexp d1 = decsexp d2 <=> d1 = d2`,
  MATCH_MP_TAC decsexp_ind THEN REPEAT STRIP_TAC THEN
  EQ_TAC THEN SIMP_NOASM[] THEN
  W(fun (asl,w) -> CASES_ON (rhs(rand w))) THEN
  REWRITE_TAC[decsexp_def] THEN SIMP_NOASM[] THEN
  STRIP_TAC THEN
  REPEAT (FSEXPAUX_MAP_EQ_TAC
    (REWRITE_TAC[FORALL_PAIR_THM] THEN SIMP_NOASM[o_THM] THEN
     ASM_MESON_TAC[expsexp_11])) THEN
  ASM_MESON_TAC[expsexp_11]);;
let _ = cake_add_simps [decsexp_11];;

(* round trip *)

(* HOL4's exists_g_tac (an ML tactic) is not needed: sexplist_listsexp_rwt *)
(* is used instead of sexplist_listsexp_matchable with its existential     *)

let sexptype_def_type_defsexp = prove
 (`sexptype_def (type_defsexp l) = SOME l`,
  REWRITE_TAC[type_defsexp_def; sexptype_def_def; o_THM] THEN
  MATCH_MP_TAC sexplist_listsexp_rwt THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN SIMP[sexppair_def] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC sexplist_listsexp_rwt THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN SIMP[sexppair_def; o_THM]);;
let _ = cake_add_simps [sexptype_def_type_defsexp];;

let sexplit_litsexp = prove
 (`sexplit (litsexp l) = SOME l`,
  CASES_ON `l:lit` THEN REWRITE_TAC[litsexp_def] THEN TRY COND_CASES_TAC THEN
  SIMP[sexplit_def; dstrip_sexp_def] THEN
  CONV_TAC(DEPTH_CONV STRING_EQ_CONV) THEN SIMP[] THEN
  REWRITE_TAC[EXISTS_ONE_THM; OPTION_GUARD_EQ_THM] THENL
   [SUBGOAL_THEN `&(num_of_int (--a)) = --a` ASSUME_TAC THENL
     [MATCH_MP_TAC INT_OF_NUM_OF_INT THEN ASM_INT_ARITH_TAC; ALL_TAC] THEN
    ONCE_REWRITE_TAC[GSYM INT_OF_NUM_EQ] THEN ASM_REWRITE_TAC[] THEN
    ASM_INT_ARITH_TAC;
    ASM_INT_ARITH_TAC;
    ALL_TAC; ALL_TAC; ALL_TAC] THEN
  W(fun (asl,w) -> MP_TAC (ISPEC (rand(lhand w)) VAL_BOUND)) THEN
  REWRITE_TAC[DIMINDEX_8; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV);;
let _ = cake_add_simps [sexplit_litsexp];;

let sexppat_patsexp = prove
 (`sexppat (patsexp p) = SOME p`,
  SPEC_TAC(`p:pat`,`p:pat`) THEN MATCH_MP_TAC FSEXPAUX_pat_ind THEN
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [sexppat_def] THEN
  SIMP[patsexp_def; dstrip_sexp_def] THEN
  CONV_TAC(DEPTH_CONV STRING_EQ_CONV) THEN SIMP[] THEN
  MATCH_MP_TAC sexplist_listsexp_rwt THEN ASM_MESON_TAC[ALL_MEM]);;
let _ = cake_add_simps [sexppat_patsexp];;

let sexplocpt_locnsexp = prove
 (`sexplocpt (locnsexp p) = SOME p`,
  CASES_ON `p:locn` THEN SIMP[sexplocpt_def; locnsexp_def; MAP]);;
let _ = cake_add_simps [sexplocpt_locnsexp];;

let sexplocn_locnsexp = prove
 (`sexplocn (locssexp l) = SOME l`,
  CASES_ON `l:locs` THEN SIMP[sexplocn_def; locssexp_def; MAP]);;
let _ = cake_add_simps [sexplocn_locnsexp];;

let sexplog_logsexp = prove
 (`sexplog (logsexp l) = SOME l`,
  CASES_ON `l:lop` THEN SIMP[sexplog_def; logsexp_def] THEN
  CONV_TAC(DEPTH_CONV STRING_EQ_CONV) THEN SIMP[]);;
let _ = cake_add_simps [sexplog_logsexp];;

let sexpexp_expsexp = prove
 (`sexpexp (expsexp e) = SOME e`,
  SPEC_TAC(`e:exp`,`e:exp`) THEN MATCH_MP_TAC FSEXPAUX_exp_ind THEN
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [sexpexp_def] THEN
  SIMP[expsexp_def; dstrip_sexp_def] THEN
  CONV_TAC(DEPTH_CONV STRING_EQ_CONV) THEN SIMP[] THEN
  MATCH_MP_TAC sexplist_listsexp_rwt THEN
  RULE_ASSUM_TAC(BETA_RULE o REWRITE_RULE[GSYM ALL_MEM; o_THM]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FORALL_PAIR_THM]) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN SIMP[sexppair_def] THEN ASM_MESON_TAC[]);;
let _ = cake_add_simps [sexpexp_expsexp];;

let sexpdec_decsexp = prove
 (`!d. sexpdec (decsexp d) = SOME d`,
  MATCH_MP_TAC FSEXPAUX_dec_ind THEN
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [sexpdec_def] THEN
  SIMP[decsexp_def; dstrip_sexp_def] THEN
  CONV_TAC(DEPTH_CONV STRING_EQ_CONV) THEN SIMP[] THEN
  REPEAT CONJ_TAC THEN MATCH_MP_TAC sexplist_listsexp_rwt THEN
  RULE_ASSUM_TAC(BETA_RULE o REWRITE_RULE[GSYM ALL_MEM; o_THM]) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN SIMP[sexppair_def; o_THM] THEN
  ASM_MESON_TAC[]);;
let _ = cake_add_simps [sexpdec_decsexp];;

let odestSXSYM_EQ_SOME = prove
 (`(odestSXSYM s = SOME str <=> s = SX_SYM (explode str)) /\
   (SOME str = odestSXSYM s <=> s = SX_SYM (explode str))`,
  CASES_ON `s:simpleSexp_sexp` THEN SIMP[odestSXSYM_def] THEN
  MESON_TAC[implode_explode; explode_implode]);;
let _ = cake_add_simps [odestSXSYM_EQ_SOME];;

let sexpopt_SOME = prove
 (`sexpopt (f:simpleSexp_sexp->A option) s = SOME opt <=>
   opt = NONE /\ s = SX_SYM "NONE" \/
   ?x s0. opt = SOME x /\ f s0 = SOME x /\ s = listsexp [SX_SYM "SOME"; s0]`,
  REWRITE_TAC[sexpopt_def] THEN CASES_ON `s:simpleSexp_sexp` THEN
  SIMP[dstrip_sexp_def; OPTION_CHOICE_EQUALS_OPTION] THENL
   [CASES_ON `a0:simpleSexp_sexp` THEN
    SIMP[EXISTS_ONE_THM; OPTION_GUARD_EQ_THM; LENGTH_EQ_NUM_compute] THEN
    EQ_TAC THEN REPEAT STRIP_TAC THEN GVS[EXISTS_ONE_THM; OPTION_GUARD_EQ_THM];
    SIMP[EXISTS_ONE_THM; OPTION_GUARD_EQ_THM] THEN MESON_TAC[]]);;

let listsexp_MAP_EQ_f = prove
 (`(!x. MEM x ls ==> (f1:A->simpleSexp_sexp) x = f2 x)
   ==> listsexp (MAP f1 ls) = listsexp (MAP f2 ls)`,
  DISCH_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC MAP_EQ THEN
  ASM_SIMP_TAC[GSYM ALL_MEM]);;

let sexplist_SOME = prove
 (`sexplist (f:simpleSexp_sexp->A option) s = SOME ls <=>
   ?l. s = listsexp l /\ MAP f l = MAP SOME ls`,
  MAP_EVERY (fun t -> SPEC_TAC(t,t)) [`s:simpleSexp_sexp`; `ls:A list`] THEN
  LIST_INDUCT_TAC THEN GEN_TAC THEN CASES_ON `s:simpleSexp_sexp` THEN
  SIMP[MAP_EQ_NIL; MAP_EQ_CONS; RIGHT_AND_EXISTS_THM] THEN MESON_TAC[]);;

let sexppair_SOME = prove
 (`sexppair (f1:simpleSexp_sexp->A option) (f2:simpleSexp_sexp->B option) s =
     SOME p <=>
   ?x y a b. f1 x = SOME a /\ f2 y = SOME b /\ s = SX_CONS x y /\ p = (a,b)`,
  CASES_ON `s:simpleSexp_sexp` THEN SIMP[sexppair_def] THEN MESON_TAC[]);;

let OPTION_CHOICE_EQ_SOME = OPTION_CHOICE_EQUALS_OPTION;;

let odestSXNUM_EQ_SOME = prove
 (`(odestSXNUM s = SOME n <=> s = SX_NUM n) /\
   (SOME n = odestSXNUM s <=> s = SX_NUM n)`,
  CASES_ON `s:simpleSexp_sexp` THEN SIMP[odestSXNUM_def] THEN MESON_TAC[]);;
let _ = cake_add_simps [odestSXNUM_EQ_SOME];;

let FSEXPAUX_litsexp_sexplit0 = prove
 (`sexplit s = SOME l ==> litsexp l = s`,
  CASES_ON `s:simpleSexp_sexp` THEN SIMP[sexplit_def; dstrip_sexp_def] THENL
   [CASES_ON `a0:simpleSexp_sexp` THEN SIMP[] THEN STRIP_TAC THEN
    GVS[EXISTS_ONE_THM; OPTION_GUARD_EQ_THM; LENGTH_EQ_NUM_compute;
        OPTION_CHOICE_EQUALS_OPTION] THEN
    FSEXPAUX_SPLIT_TYPES_TAC [`:mlstring`] THEN
    GVS[litsexp_def; VAL_WORD; DIMINDEX_8; DIMINDEX_64; MOD_LT;
        LENGTH_EQ_NUM_compute; INT_NEG_NEG; NUM_OF_INT_OF_NUM] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN POP_ASSUM MP_TAC THEN
    REWRITE_TAC[INT_ARITH `~(-- &x < &0) <=> &x <= &0`; INT_OF_NUM_LE] THEN
    ASM_ARITH_TAC;
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    SIMP[litsexp_def; INT_OF_NUM_LT; NUM_OF_INT_OF_NUM] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_ARITH_TAC;
    STRIP_TAC THEN RVEQ_TAC THEN
    IMP_RES_TAC encode_decode_control THEN SIMP[litsexp_def; SEXSTR_def]]);;

let litsexp_sexplit = prove
 (`(sexplit s = SOME l <=> litsexp l = s) /\
   (SOME l = sexplit s <=> litsexp l = s)`,
  MESON_TAC[FSEXPAUX_litsexp_sexplit0; sexplit_litsexp]);;

let idsexp_sexpid_odestSEXSTR = prove
 (`!y x. sexpid odestSEXSTR x = SOME y <=> x = idsexp y`,
  MATCH_MP_TAC id_INDUCT THEN REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [sexpid_def] THEN
  SIMP[OPTION_BIND_EQUALS_OPTION; dstrip_sexp_SOME; PULL_EXISTS; idsexp_def;
       OPTION_CHOICE_EQUALS_OPTION; LENGTH_EQ_NUM_compute; EXISTS_ONE_THM;
       OPTION_GUARD_EQ_THM; RIGHT_AND_EXISTS_THM] THEN
  MESON_TAC[]);;

let idsexp_sexpid_odestSEXSTR' = prove
 (`(sexpid odestSEXSTR x = SOME y <=> x = idsexp y) /\
   (SOME y = sexpid odestSEXSTR x <=> x = idsexp y)`,
  MESON_TAC[idsexp_sexpid_odestSEXSTR]);;
let _ = cake_add_simps [idsexp_sexpid_odestSEXSTR'];;

(* the elements of a list parsed by f, with g a left inverse of f on them *)

let FSEXPAUX_MAP_SOME_INV = prove
 (`!(f:B->A option) (g:A->B) l ls.
     MAP f l = MAP SOME ls /\ (!e t. MEM e l /\ f e = SOME t ==> g t = e)
     ==> MAP g ls = l`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP; NOT_CONS_NIL; CONS_11; MEM] THEN ASM_MESON_TAC[]);;

let FSEXPAUX_sxMEM_listsexp = prove
 (`sxMEM e (listsexp l) <=> MEM e l`,
  REWRITE_TAC[sxMEM_def; strip_sxcons_listsexp; option_INJ] THEN MESON_TAC[]);;

(* the induction hypotheses of the inverse theorems: kept in the goal (as  *)
(* an antecedent) while the parser's equation is simplified, so that the   *)
(* simplifier never uses them as rewrites                                   *)

let FSEXPAUX_IH_ANT_TAC (def:thm) (ths:thm list) : tactic =
  GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN POP_ASSUM MP_TAC THEN
  ONCE_REWRITE_TAC[TAUT `a ==> b ==> c <=> b ==> a ==> c`] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [def] THEN DISCH_TAC THEN
  GVS([OPTION_BIND_EQUALS_OPTION; OPTION_CHOICE_EQUALS_OPTION; dstrip_sexp_SOME;
       EXISTS_ONE_THM; OPTION_GUARD_EQ_THM; LENGTH_EQ_NUM_compute; sexplist_SOME;
       FSEXPAUX_sxMEM_listsexp] @ ths);;

let FSEXPAUX_typesexp_sexptype0 = prove
 (`!s t. sexptype s = SOME t ==> typesexp t = s`,
  MATCH_MP_TAC sexptype_ind THEN FSEXPAUX_IH_ANT_TAC sexptype_def [] THEN
  SIMP[typesexp_def] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC FSEXPAUX_MAP_SOME_INV THEN EXISTS_TAC `sexptype` THEN
  ASM_MESON_TAC[]);;

let typesexp_sexptype = prove
 (`!s t. (sexptype s = SOME t <=> typesexp t = s) /\
         (SOME t = sexptype s <=> typesexp t = s)`,
  MESON_TAC[FSEXPAUX_typesexp_sexptype0; sexptype_typesexp]);;

let patsexp_sexppat0 = prove
 (`!s p. sexppat s = SOME p ==> patsexp p = s`,
  MATCH_MP_TAC sexppat_ind THEN
  FSEXPAUX_IH_ANT_TAC sexppat_def
    [litsexp_sexplit; sexpopt_SOME; typesexp_sexptype] THEN
  SIMP[patsexp_def; optsexp_def] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC FSEXPAUX_MAP_SOME_INV THEN EXISTS_TAC `sexppat` THEN
  ASM_MESON_TAC[]);;

let patsexp_sexppat = prove
 (`(sexppat s = SOME p <=> patsexp p = s) /\
   (SOME p = sexppat s <=> patsexp p = s)`,
  MESON_TAC[patsexp_sexppat0; sexppat_patsexp]);;

let decode_test_testsexp = prove
 (`fromSexp_decode_test s = SOME test ==> testsexp test = s`,
  CASES_ON `s:simpleSexp_sexp` THEN REWRITE_TAC[fromSexp_decode_test_def] THEN
  REPEAT COND_CASES_TAC THEN
  REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[testsexp_def]);;

let sexparith_arithsexp = prove
 (`sexparith s = SOME arith ==> arithsexp arith = s`,
  CASES_ON `s:simpleSexp_sexp` THEN REWRITE_TAC[sexparith_def] THEN
  REPEAT COND_CASES_TAC THEN
  REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[arithsexp_def]);;

let decode_prim_type_prim_typesexp = prove
 (`decode_prim_type s0 = SOME prim_type ==> prim_typesexp prim_type = s0`,
  CASES_ON `s0:simpleSexp_sexp` THEN REWRITE_TAC[decode_prim_type_def] THEN
  REPEAT COND_CASES_TAC THEN
  REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[prim_typesexp_def]);;

let FSEXPAUX_decode_thunk_mode = prove
 (`decode_thunk_mode t = SOME m ==> encode_thunk_mode m = t`,
  REWRITE_TAC[decode_thunk_mode_def] THEN REPEAT COND_CASES_TAC THEN
  REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[encode_thunk_mode_def]);;

(* a case split on the string literals that a string variable of the goal  *)
(* is compared with (each case decided by string literal comparison)       *)

let FSEXPAUX_LIT_CASES_TAC (fin:tactic) : tactic = fun (asl,w as g) ->
  let is_lit t = try (ignore(dest_string t); true) with Failure _ -> false in
  let eqs = find_terms (fun t -> is_eq t && is_var (lhs t) &&
                                 type_of (lhs t) = `:string` && is_lit (rhs t)) w in
  if eqs = [] then fin g else
  let v = lhs (hd eqs) in
  let lits = setify (map rhs (filter (fun t -> lhs t = v) eqs)) in
  let rec go ls = match ls with
      [] -> ASM_REWRITE_TAC[] THEN fin
    | l::ls -> ASM_CASES_TAC (mk_eq(v,l)) THENL
         [FIRST_X_ASSUM SUBST_ALL_TAC THEN CONV_TAC(DEPTH_CONV STRING_EQ_CONV) THEN
          REWRITE_TAC[] THEN fin;
          go ls] in
  go lits g;;

let opsexp_sexpop = prove
 (`sexpop s = SOME p ==> opsexp p = s`,
  CASES_ON `s:simpleSexp_sexp` THENL
   [CASES_ON `a0:simpleSexp_sexp` THEN CASES_ON `a1:simpleSexp_sexp`;
    ALL_TAC; ALL_TAC; ALL_TAC] THEN
  REWRITE_TAC[sexpop_def; option_DISTINCT] THEN
  FSEXPAUX_LIT_CASES_TAC
   (REWRITE_TAC[option_DISTINCT] THEN DISCH_TAC THEN
    GVS[option_case_eq; o_THM] THEN
    TRY (IMP_RES_TAC encode_decode_control) THEN
    TRY (IMP_RES_TAC FSEXPAUX_decode_thunk_mode) THEN
    TRY (IMP_RES_TAC decode_test_testsexp) THEN
    TRY (IMP_RES_TAC sexparith_arithsexp) THEN
    TRY (IMP_RES_TAC decode_prim_type_prim_typesexp) THEN
    ASM_REWRITE_TAC[opsexp_def; SEXSTR_def; o_THM; explode_implode]));;

let locnsexp_sexplocpt0 = prove
 (`sexplocpt s = SOME z ==> locnsexp z = s`,
  CASES_ON `s:simpleSexp_sexp` THEN REWRITE_TAC[sexplocpt_def] THENL
   [SIMP[OPTION_BIND_EQUALS_OPTION; EXISTS_ONE_THM; OPTION_GUARD_EQ_THM;
         LENGTH_EQ_NUM_compute] THEN
    DISCH_TAC THEN GVS[] THEN SIMP[locnsexp_def; MAP];
    REPEAT COND_CASES_TAC THEN
    REWRITE_TAC[option_DISTINCT; option_INJ] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[locnsexp_def];
    SIMP[];
    SIMP[]]);;

let locnsexp_sexplocpt = prove
 (`(sexplocpt s = SOME z <=> locnsexp z = s) /\
   (SOME z = sexplocpt s <=> locnsexp z = s)`,
  MESON_TAC[locnsexp_sexplocpt0; sexplocpt_locnsexp]);;
let _ = cake_add_simps [locnsexp_sexplocpt];;

let locnsexp_sexplocn = prove
 (`(sexplocn s = SOME z <=> locssexp z = s) /\
   (SOME z = sexplocn s <=> locssexp z = s)`,
  MATCH_MP_TAC(TAUT `(a <=> c) /\ (b <=> a) ==> (a <=> c) /\ (b <=> c)`) THEN
  CONJ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  EQ_TAC THENL [ALL_TAC; DISCH_THEN(SUBST1_TAC o SYM) THEN
                REWRITE_TAC[sexplocn_locnsexp]] THEN
  REWRITE_TAC[sexplocn_def] THEN
  SIMP[OPTION_BIND_EQUALS_OPTION; EXISTS_ONE_THM; OPTION_GUARD_EQ_THM;
       LENGTH_EQ_NUM_compute] THEN
  DISCH_TAC THEN GVS[] THEN SIMP[locssexp_def; MAP]);;

let logsexp_sexplog = prove
 (`(sexplog s = SOME z <=> logsexp z = s) /\
   (SOME z = sexplog s <=> logsexp z = s)`,
  MATCH_MP_TAC(TAUT `(a <=> c) /\ (b <=> a) ==> (a <=> c) /\ (b <=> c)`) THEN
  CONJ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  EQ_TAC THENL [ALL_TAC; DISCH_THEN(SUBST1_TAC o SYM) THEN
                REWRITE_TAC[sexplog_logsexp]] THEN
  CASES_ON `s:simpleSexp_sexp` THEN REWRITE_TAC[sexplog_def] THEN
  REPEAT COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[logsexp_def]);;

(* the inverse theorems of the long parsers: after the case split on the   *)
(* symbol, the guards reduce to one alternative; the induction hypotheses  *)
(* are simplified with the facts of the case (FSEXPAUX_IH_SIMP_TAC) and     *)
(* kept in the goal while the parser's equation is decomposed               *)

let FSEXPAUX_GUARD_RWS = [COND_CLAUSES; AND_CLAUSES; OPTION_CHOICE_DEF;
  OPTION_CHOICE_NONE; OPTION_GUARD_def; OPTION_IGNORE_BIND_thm];;

let FSEXPAUX_IH_SIMP_TAC : tactic = fun (asl,w as g) ->
  let ths = map snd asl in
  let simple = filter (fun th -> not (is_forall (concl th)) &&
                                 not (is_imp (concl th))) ths in
  let rule th = if is_forall (concl th) then
                  CAKE_SIMP_RULE (simple @ [EXISTS_ONE_THM; OPTION_GUARD_EQ_THM]) th
                else th in
  RULE_ASSUM_TAC rule g;;

let FSEXPAUX_IH_TO_GOAL_TAC : tactic =
  REPEAT (FIRST_X_ASSUM (MP_TAC o check (fun th -> is_forall (concl th))));;

let FSEXPAUX_MAP_SOME_INV' = prove
 (`!(f:B->A option) (g:A->B) l ls.
     MAP f l = MAP SOME ls
     ==> (!e t. MEM e l /\ f e = SOME t ==> g t = e)
     ==> MAP g ls = l`,
  MESON_TAC[FSEXPAUX_MAP_SOME_INV]);;

(* the parse of dstrip_sexp s = SOME (nm,args) by the guards, then fin *)

let FSEXPAUX_PARSE_CASES_TAC (def:thm) (ths:thm list) (fin:tactic) : tactic =
  GEN_TAC THEN
  DISCH_THEN (fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [def] THEN
  MP_TAC (ISPEC `dstrip_sexp s` option_CASES) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[OPTION_BIND_DEF; option_DISTINCT] THEN
  MP_TAC (ISPEC `x:string#simpleSexp_sexp list` PAIR_SURJECTIVE) THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[pair_CASE] THEN
  FSEXPAUX_LIT_CASES_TAC
   (REWRITE_TAC FSEXPAUX_GUARD_RWS THEN
    REWRITE_TAC[OPTION_IGNORE_BIND_EQUALS_OPTION; EXISTS_ONE_THM;
                OPTION_GUARD_EQ_THM; option_DISTINCT] THEN
    STRIP_TAC THEN FSEXPAUX_IH_SIMP_TAC THEN FSEXPAUX_IH_TO_GOAL_TAC THEN
    GVS([dstrip_sexp_SOME; LENGTH_EQ_NUM_compute; sexplist_SOME;
         FSEXPAUX_sxMEM_listsexp; litsexp_sexplit; typesexp_sexptype;
         locnsexp_sexplocn; logsexp_sexplog; sexpopt_SOME; sexppair_SOME;
         OPTION_APPLY_MAP3; OPTION_APPLY_MAP4] @ ths) THEN
    fin);;

(* the encoding of the parts: the inverse lemmas, the induction            *)
(* hypotheses, and for lists FSEXPAUX_MAP_SOME_INV'                        *)

let FSEXPAUX_ENC_FIN_TAC (defs:thm list) (ths:thm list) : tactic =
  REPEAT DISCH_TAC THEN TRY (IMP_RES_TAC opsexp_sexpop) THEN RVEQ_TAC THEN
  SIMP_NOASM(defs @ [optsexp_def; o_THM]) THEN
  REPEAT CONJ_TAC THEN
  TRY (FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP FSEXPAUX_MAP_SOME_INV') THEN
       REWRITE_TAC[sexppair_SOME; FORALL_PAIR_THM; PAIR_EQ] THEN
       REPEAT STRIP_TAC THEN RVEQ_TAC THEN
       RULE_ASSUM_TAC (REWRITE_RULE[odestSEXSTR_SOME; PAIR_EQ]) THEN
       REPEAT (FIRST_X_ASSUM (STRIP_ASSUME_TAC o check (is_conj o concl))) THEN
       RVEQ_TAC THEN SIMP_NOASM[] THEN REPEAT CONJ_TAC THEN
       ASM_MESON_TAC ths);;

let FSEXPAUX_expsexp_sexpexp0 = prove
 (`!s e. sexpexp s = SOME e ==> expsexp e = s`,
  MATCH_MP_TAC sexpexp_ind THEN
  FSEXPAUX_PARSE_CASES_TAC sexpexp_def []
    (FSEXPAUX_ENC_FIN_TAC [expsexp_def] [patsexp_sexppat]));;

let expsexp_sexpexp = prove
 (`(sexpexp s = SOME e <=> expsexp e = s) /\
   (SOME e = sexpexp s <=> expsexp e = s)`,
  MESON_TAC[FSEXPAUX_expsexp_sexpexp0; sexpexp_expsexp]);;

(* one level of a list-of-tuples inverse: the element parsers decomposed  *)

let FSEXPAUX_LIST_INV_TAC : tactic =
  FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP FSEXPAUX_MAP_SOME_INV') THEN
  REWRITE_TAC[sexppair_SOME; sexplist_SOME; FORALL_PAIR_THM; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC (REWRITE_RULE[odestSEXSTR_SOME; PAIR_EQ]) THEN
  REPEAT (FIRST_X_ASSUM (STRIP_ASSUME_TAC o check (is_conj o concl))) THEN
  RVEQ_TAC THEN SIMP_NOASM[o_THM];;

let FSEXPAUX_type_defsexp_sexptype_def0 = prove
 (`sexptype_def s = SOME x ==> type_defsexp x = s`,
  REWRITE_TAC[sexptype_def_def; type_defsexp_def; o_THM; sexplist_SOME] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[listsexp_11] THEN
  FSEXPAUX_LIST_INV_TAC THEN CONJ_TAC THEN FSEXPAUX_LIST_INV_TAC THEN
  FSEXPAUX_LIST_INV_TAC THEN ASM_MESON_TAC[typesexp_sexptype]);;

let type_defsexp_sexptype_def = prove
 (`(sexptype_def s = SOME x <=> type_defsexp x = s) /\
   (SOME x = sexptype_def s <=> type_defsexp x = s)`,
  MESON_TAC[FSEXPAUX_type_defsexp_sexptype_def0; sexptype_def_type_defsexp]);;

let FSEXPAUX_decsexp_sexpdec0 = prove
 (`!s d. sexpdec s = SOME d ==> decsexp d = s`,
  MATCH_MP_TAC sexpdec_ind THEN
  FSEXPAUX_PARSE_CASES_TAC sexpdec_def
    [expsexp_sexpexp; patsexp_sexppat; type_defsexp_sexptype_def]
    (FSEXPAUX_ENC_FIN_TAC [decsexp_def]
       [expsexp_sexpexp; typesexp_sexptype]));;

let decsexp_sexpdec = prove
 (`(sexpdec s = SOME d <=> decsexp d = s) /\
   (SOME d = sexpdec s <=> decsexp d = s)`,
  MESON_TAC[FSEXPAUX_decsexp_sexpdec0; sexpdec_decsexp]);;

(* valid sexps *)

(* the validity of a symbol literal, by evaluation (HOL4: EVAL_TAC) *)

let FSEXPAUX_VALID_SYM_CONV : conv = fun tm ->
  let is_lit t = try (ignore(dest_string t); true) with Failure _ -> false in
  let ok = (try let f,x = dest_comb tm in
                (fst(dest_const f) = "valid_symbol" && is_lit x) ||
                (fst(dest_const f) = "valid_sexp" &&
                 (let g,y = dest_comb x in fst(dest_const g) = "SX_SYM" && is_lit y))
            with Failure _ -> false) in
  if not ok then failwith "FSEXPAUX_VALID_SYM_CONV" else
  let th = (REWRITE_CONV[valid_sexp_def; valid_symbol_def; ALL;
              valid_first_symchar_def; valid_symchar_def; isGraph_def;
              isPrint_def; isSpace_def; isDigit_def; IN_INSERT; NOT_IN_EMPTY;
              CHAR_EQ_THM; ORD_DEF; BITVAL_CLAUSES; LSTRAUX_ORD_CHR_MOD] THENC
            NUM_REDUCE_CONV THENC REWRITE_CONV[]) tm in
  if rhs(concl th) = `T` || rhs(concl th) = `F` then th
  else failwith "FSEXPAUX_VALID_SYM_CONV";;

let FSEXPAUX_VALID_SYM_TAC : tactic =
  CONV_TAC(DEPTH_CONV FSEXPAUX_VALID_SYM_CONV) THEN REWRITE_TAC[];;

let SEXSTR_valid = prove
 (`valid_sexp (SEXSTR s)`,
  REWRITE_TAC[SEXSTR_def; valid_sexp_def; EVERY_isPrint_encode_control]);;
let _ = cake_add_simps [SEXSTR_valid];;

let listsexp_valid = prove
 (`!ls. ALL valid_sexp ls ==> valid_sexp (listsexp ls)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[listsexp_thm; ALL] THEN
  FSEXPAUX_VALID_SYM_TAC THEN SIMP[]);;

(* the same as an equation, for rewriting *)

let FSEXPAUX_valid_listsexp = prove
 (`!ls. valid_sexp (listsexp ls) <=> ALL valid_sexp ls`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[listsexp_thm; ALL] THEN
  FSEXPAUX_VALID_SYM_TAC THEN ASM_REWRITE_TAC[valid_sexp_def]);;

let idsexp_valid = prove
 (`!i. valid_sexp (idsexp i)`,
  MATCH_MP_TAC id_INDUCT THEN
  REWRITE_TAC[idsexp_def; FSEXPAUX_valid_listsexp; ALL] THEN
  FSEXPAUX_VALID_SYM_TAC THEN SIMP[]);;
let _ = cake_add_simps [idsexp_valid];;

let typesexp_valid = prove
 (`!t. valid_sexp (typesexp t)`,
  MATCH_MP_TAC typesexp_ind THEN
  REWRITE_TAC[typesexp_def; FSEXPAUX_valid_listsexp; ALL] THEN
  FSEXPAUX_VALID_SYM_TAC THEN
  SIMP[ALL_MAP; GSYM ALL_MEM] THEN ASM_SIMP_TAC[]);;
let _ = cake_add_simps [typesexp_valid];;

let litsexp_valid = prove
 (`!l. valid_sexp (litsexp l)`,
  GEN_TAC THEN CASES_ON `l:lit` THEN REWRITE_TAC[litsexp_def] THEN
  TRY COND_CASES_TAC THEN
  REWRITE_TAC[FSEXPAUX_valid_listsexp; ALL] THEN FSEXPAUX_VALID_SYM_TAC THEN
  SIMP[]);;
let _ = cake_add_simps [litsexp_valid];;

let optsexp_valid = prove
 (`!x. (!y. x = SOME y ==> valid_sexp y) ==> valid_sexp (optsexp x)`,
  GEN_TAC THEN CASES_ON `x:simpleSexp_sexp option` THEN
  REWRITE_TAC[optsexp_def; FSEXPAUX_valid_listsexp; ALL] THEN
  FSEXPAUX_VALID_SYM_TAC THEN SIMP[]);;

let patsexp_valid = prove
 (`!p. valid_sexp (patsexp p)`,
  MATCH_MP_TAC patsexp_ind THEN
  REWRITE_TAC[patsexp_def; FSEXPAUX_valid_listsexp; ALL] THEN
  FSEXPAUX_VALID_SYM_TAC THEN
  SIMP[ALL_MAP; GSYM ALL_MEM] THEN REPEAT STRIP_TAC THEN
  TRY (MATCH_MP_TAC optsexp_valid THEN SIMP[] THEN REPEAT STRIP_TAC THEN
       RVEQ_TAC THEN SIMP[] THEN NO_TAC) THEN
  ASM_SIMP_TAC[]);;
let _ = cake_add_simps [patsexp_valid];;

let type_defsexp_valid = prove
 (`!t. valid_sexp (type_defsexp t)`,
  REWRITE_TAC[type_defsexp_def; o_THM; FSEXPAUX_valid_listsexp; ALL_MAP;
              GSYM ALL_MEM; FORALL_PAIR_THM] THEN
  SIMP[o_THM; FSEXPAUX_valid_listsexp; ALL_MAP; GSYM ALL_MEM; FORALL_PAIR_THM]);;
let _ = cake_add_simps [type_defsexp_valid];;

let valid_sexp_prim_typesexp = prove
 (`!t. valid_sexp (prim_typesexp t)`,
  GEN_TAC THEN CASES_ON `t:prim_type` THEN
  FSEXPAUX_SPLIT_TYPES_TAC [`:word_size`] THEN
  REWRITE_TAC[prim_typesexp_def] THEN FSEXPAUX_VALID_SYM_TAC);;
let _ = cake_add_simps [valid_sexp_prim_typesexp];;

let valid_sexp_arithsexp = prove
 (`valid_sexp (arithsexp a)`,
  CASES_ON `a:arith` THEN REWRITE_TAC[arithsexp_def] THEN FSEXPAUX_VALID_SYM_TAC);;
let _ = cake_add_simps [valid_sexp_arithsexp];;

let valid_sexp_logsexp = prove
 (`valid_sexp (logsexp a)`,
  CASES_ON `a:lop` THEN REWRITE_TAC[logsexp_def] THEN FSEXPAUX_VALID_SYM_TAC);;
let _ = cake_add_simps [valid_sexp_logsexp];;

let FSEXPAUX_valid_testsexp = prove
 (`valid_sexp (testsexp t)`,
  CASES_ON `t:test` THEN FSEXPAUX_SPLIT_TYPES_TAC [`:opb`] THEN
  REWRITE_TAC[testsexp_def] THEN FSEXPAUX_VALID_SYM_TAC);;

let opsexp_valid = prove
 (`!op. valid_sexp (opsexp op)`,
  GEN_TAC THEN CASES_ON `op:op` THEN
  FSEXPAUX_SPLIT_TYPES_TAC [`:word_size`; `:shift`; `:thunk_op`; `:thunk_mode`] THEN
  REWRITE_TAC[opsexp_def; encode_thunk_mode_def; valid_sexp_def] THEN
  FSEXPAUX_VALID_SYM_TAC THEN
  REWRITE_TAC[SEXSTR_valid; valid_sexp_arithsexp; valid_sexp_prim_typesexp;
              FSEXPAUX_valid_testsexp]);;
let _ = cake_add_simps [opsexp_valid];;

let locnsexp_valid = prove
 (`!p. valid_sexp (locnsexp p)`,
  GEN_TAC THEN CASES_ON `p:locn` THEN
  REWRITE_TAC[locnsexp_def; FSEXPAUX_valid_listsexp; MAP; ALL] THEN
  FSEXPAUX_VALID_SYM_TAC THEN REWRITE_TAC[valid_sexp_def]);;
let _ = cake_add_simps [locnsexp_valid];;

let locssexp_valid = prove
 (`!l. valid_sexp (locssexp l)`,
  GEN_TAC THEN CASES_ON `l:locs` THEN
  REWRITE_TAC[locssexp_def; FSEXPAUX_valid_listsexp; MAP; ALL; locnsexp_valid]);;
let _ = cake_add_simps [locssexp_valid];;

let expsexp_valid = prove
 (`!e. valid_sexp (expsexp e)`,
  MATCH_MP_TAC expsexp_ind THEN
  REWRITE_TAC[expsexp_def; FSEXPAUX_valid_listsexp; ALL; valid_sexp_def] THEN
  FSEXPAUX_VALID_SYM_TAC THEN
  SIMP[ALL_MAP; GSYM ALL_MEM; FORALL_PAIR_THM; o_THM] THEN REPEAT STRIP_TAC THEN
  TRY (MATCH_MP_TAC optsexp_valid THEN SIMP[] THEN REPEAT STRIP_TAC THEN
       RVEQ_TAC THEN SIMP[o_THM] THEN NO_TAC) THEN
  ASM_MESON_TAC[]);;
let _ = cake_add_simps [expsexp_valid];;

let decsexp_valid = prove
 (`!d. valid_sexp (decsexp d)`,
  MATCH_MP_TAC decsexp_ind THEN
  REWRITE_TAC[decsexp_def; FSEXPAUX_valid_listsexp; ALL; valid_sexp_def] THEN
  FSEXPAUX_VALID_SYM_TAC THEN
  SIMP[ALL_MAP; GSYM ALL_MEM; FORALL_PAIR_THM; o_THM]);;
let _ = cake_add_simps [decsexp_valid];;
