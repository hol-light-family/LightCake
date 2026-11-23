(* ========================================================================= *)
(* mlstring: port of HOL4 basis/pure/mlstringScript.sml (CakeML v3479).      *)
(* Pure functions for the String module.  Defines mlstring as a separate     *)
(* type from string in HOL's standard library (a synonym for char list).    *)
(*                                                                           *)
(* Notation: HOL4 strlit (an overload of the constructor implode) is        *)
(* implode; the literal of mlstring syntax is implode "..." (the empty one   *)
(* implode ""); s1 ^ s2 is strcat s1 s2 (left associative in HOL4);         *)
(* toString is chr_to_str; mlstring <, <=, >, >= are mlstring_lt, ...;       *)
(* on chars and strings < and <= are char_lt and string_lt, string_le       *)
(* (string4.ml); a character literal #"c" is CHR (ORD of c); flip_ord is     *)
(* invert_comparison; ## is PAIR_MAP (vocab.ml); word8 is byte, n2w is word *)
(* and w2n is val; HOL4 () is one.  Names (doc/names.tsv): concat,          *)
(* extract, compare, collate_aux and collate are mlstring_concat, ...        *)
(* Helper lemmas that are not HOL4 theorems are PURE1AUX_.                   *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "hol4/rich_list.ml";;
needs "hol4/basic.ml";;
needs "hol4/string4.ml";;
needs "hol4/toto.ml";;
needs "hol4/comparison.ml";;
needs "hol4/words4.ml";;
needs "basis/pure/mllist.ml";;

type_invention_error := true;;

(* Defines strings as a separate type from char list. *)

let mlstring_INDUCT,mlstring_RECURSION = cake_type "mlstring = implode string";;

let mlstring_case_def = case_def "mlstring";;

(* HOL4: Overload strlit[inferior] = implode (backwards compatibility: strlit *)
(* used to be the constructor); written implode here.                        *)

let strlen_def = cake_def
  `strlen (implode s) = LENGTH s`;;
let _ = cake_add_simps [strlen_def];;

let strsub_def = cake_def
  `strsub (implode s) n = EL n s`;;
let _ = cake_add_simps [strsub_def];;

(* the test here is because underspecification is annoying (and SEG is     *)
(* underspecified); the underlying primitive (CopyStrStr) raises an        *)
(* exception if the test is false                                          *)

let substring_def = cake_def
  `substring (implode s) off len =
     implode (if off + len <= LENGTH s then SEG len off s
              else if off <= LENGTH s then DROP off s
              else "")`;;

(* HOL4: concat *)

let mlstring_concat_def = cake_def
  `mlstring_concat l = implode (FLAT (MAP (\s. match s with implode x -> x) l))`;;

let concat_nil = prove
 (`mlstring_concat [] = implode ""`,
  REWRITE_TAC[mlstring_concat_def; MAP; FLAT]);;
let _ = cake_add_simps [concat_nil];;

let explode_aux_def = cake_def
  `(explode_aux s n 0 = []) /\
   (explode_aux s n (SUC len) = CONS (strsub s n) (explode_aux s (n + 1) len))`;;
let _ = cake_add_simps [explode_aux_def];;

(* HOL4 names the first variable max (a constant in HOL Light) *)

let explode_aux_thm = prove
 (`!max' n ls.
     (n + max' = LENGTH ls) ==> (explode_aux (implode ls) n max' = DROP n ls)`,
  INDUCT_TAC THEN REWRITE_TAC[explode_aux_def; ADD_CLAUSES] THENL
   [REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[DROP_LENGTH_NIL];
    REPEAT STRIP_TAC THEN REWRITE_TAC[strsub_def] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`n + 1`; `ls:string`]) THEN
    ANTS_TAC THENL [POP_ASSUM MP_TAC THEN ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC DROP_EL_CONS THEN
    POP_ASSUM MP_TAC THEN ARITH_TAC]);;

let explode_def = cake_def
  `explode s = explode_aux s 0 (strlen s)`;;

let explode_thm = prove
 (`explode (implode ls) = ls`,
  REWRITE_TAC[explode_def; strlen_def] THEN
  SIMP_TAC[explode_aux_thm; ADD_CLAUSES; DROP_0]);;
let _ = cake_add_simps [explode_thm];;

let explode_implode = prove
 (`!x. explode (implode x) = x`,
  REWRITE_TAC[explode_thm]);;
let _ = cake_add_simps [explode_implode];;

let implode_explode = prove
 (`!x. implode (explode x) = x`,
  MATCH_MP_TAC mlstring_INDUCT THEN REWRITE_TAC[explode_thm]);;
let _ = cake_add_simps [implode_explode];;

let explode_11 = prove
 (`!s1 s2. (explode s1 = explode s2) <=> (s1 = s2)`,
  MESON_TAC[implode_explode]);;
let _ = cake_add_simps [explode_11];;

let implode_BIJ = prove
 (`BIJ implode (UNIV:string->bool) (UNIV:mlstring->bool)`,
  REWRITE_TAC[BIJ; INJ; SURJ; IN_UNIV] THEN
  MESON_TAC[explode_implode; implode_explode]);;

let explode_BIJ = prove
 (`BIJ explode (UNIV:mlstring->bool) (UNIV:string->bool)`,
  REWRITE_TAC[BIJ; INJ; SURJ; IN_UNIV] THEN
  MESON_TAC[explode_implode; implode_explode]);;

let LENGTH_explode = prove
 (`LENGTH (explode s) = strlen s`,
  MP_TAC(SPEC `s:mlstring` (cases "mlstring")) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[explode_thm; strlen_def]);;
let _ = cake_add_simps [LENGTH_explode];;

let concat_thm = prove
 (`mlstring_concat l = implode (FLAT (MAP explode l))`,
  REWRITE_TAC[mlstring_concat_def; injectivity "mlstring"] THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN MATCH_MP_TAC mlstring_INDUCT THEN
  REWRITE_TAC[mlstring_case_def; explode_thm]);;

let strlen_implode = prove
 (`strlen (implode s) = LENGTH s`,
  REWRITE_TAC[strlen_def]);;
let _ = cake_add_simps [strlen_implode];;

let PURE1AUX_MLSTRING_CASES_TAC (v:term) =
  STRUCT_CASES_TAC (SPEC v (cases "mlstring"));;

let strlen_substring = prove
 (`strlen (substring s i j) = if i + j <= strlen s then j
                              else if i <= strlen s then strlen s - i
                              else 0`,
  PURE1AUX_MLSTRING_CASES_TAC `s:mlstring` THEN
  REWRITE_TAC[substring_def; strlen_def] THEN
  ASM_CASES_TAC `i + j <= LENGTH (a:string)` THEN ASM_REWRITE_TAC[] THENL
   [MATCH_MP_TAC LENGTH_SEG THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `i <= LENGTH (a:string)` THEN ASM_REWRITE_TAC[LENGTH_DROP; LENGTH]);;

(* HOL4: extract *)

let mlstring_extract_def = cake_def
  `mlstring_extract s i opt =
     if strlen s <= i then implode []
     else match opt with
            SOME x -> substring s i (MIN (strlen s - i) x)
          | NONE -> substring s i (strlen s - i)`;;

let strlen_extract_le = prove
 (`!s x y. strlen (mlstring_extract s x y) <= strlen s - x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mlstring_extract_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[strlen_def; LENGTH; LE_0] THEN
  CASES_ON `y:num option` THEN REWRITE_TAC[option_CASE; strlen_substring] THEN
  REPEAT COND_CASES_TAC THEN POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  ARITH_TAC);;

let strsub_substring_0_thm = prove
 (`!m n l. m < n ==> strsub (substring l 0 n) m = strsub l m`,
  REPEAT GEN_TAC THEN PURE1AUX_MLSTRING_CASES_TAC `l:mlstring` THEN
  REWRITE_TAC[strsub_def; substring_def; ADD_CLAUSES; LE_0; DROP_0] THEN
  COND_CASES_TAC THEN REWRITE_TAC[strsub_def] THEN
  SIMP_TAC[SEG_TAKE_DROP; ADD_CLAUSES; ASSUME `n <= LENGTH (a:string)`; DROP_0] THEN
  SIMP_TAC[EL_TAKE]);;

let substring_full = prove
 (`substring s 0 (strlen s) = s`,
  PURE1AUX_MLSTRING_CASES_TAC `s:mlstring` THEN
  REWRITE_TAC[substring_def; strlen_def; ADD_CLAUSES; LE_REFL; SEG_LENGTH_ID]);;
let _ = cake_add_simps [substring_full];;

let substring_too_long = prove
 (`strlen s <= i ==> substring s i j = implode ""`,
  PURE1AUX_MLSTRING_CASES_TAC `s:mlstring` THEN
  REWRITE_TAC[substring_def; strlen_def; injectivity "mlstring"] THEN
  DISCH_TAC THEN COND_CASES_TAC THENL
   [SUBGOAL_THEN `j = 0` SUBST1_TAC THENL
     [POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN ARITH_TAC;
      REWRITE_TAC[SEG]];
    COND_CASES_TAC THEN REWRITE_TAC[DROP_NIL] THEN ASM_REWRITE_TAC[]]);;

let strcat_def = cake_def
  `strcat s1 s2 = mlstring_concat [s1; s2]`;;

(* HOL4: infix ^ for strcat (written strcat here) *)

let concat_cons = prove
 (`mlstring_concat (CONS h t) = strcat h (mlstring_concat t)`,
  REWRITE_TAC[strcat_def; concat_thm; MAP; FLAT; explode_thm; APPEND_NIL]);;

let strcat_thm = prove
 (`strcat s1 s2 = implode (APPEND (explode s1) (explode s2))`,
  REWRITE_TAC[strcat_def; concat_thm; MAP; FLAT; APPEND_NIL]);;

let strcat_assoc = prove
 (`!s1 s2 s3. strcat s1 (strcat s2 s3) = strcat (strcat s1 s2) s3`,
  REWRITE_TAC[strcat_thm; explode_thm; APPEND_ASSOC]);;
let _ = cake_add_simps [strcat_assoc];;

let strcat_o = prove
 (`strcat x o strcat y = strcat (strcat x y)`,
  REWRITE_TAC[FUN_EQ_THM; o_THM; strcat_assoc]);;

let strcat_nil = prove
 (`(strcat (implode "") s = s) /\ (strcat s (implode "") = s)`,
  REWRITE_TAC[strcat_thm; explode_thm; APPEND; APPEND_NIL; implode_explode]);;
let _ = cake_add_simps [strcat_nil];;

let mlstring_common_prefix = prove
 (`!s t1 t2. strcat s t1 = strcat s t2 <=> t1 = t2`,
  REWRITE_TAC[strcat_thm; injectivity "mlstring"; APPEND_LCANCEL; explode_11]);;
let _ = cake_add_simps [mlstring_common_prefix];;

(* HOL4 states this with the binders c1 s1 s2 t2 t2 (t1 and c2 free) *)

let mlstring_common_char_prefix = prove
 (`!c1 s1 s2 (t2:mlstring) t2.
     (strcat (implode (CONS c1 s1)) t1 = strcat (implode (CONS c2 s2)) t2) <=>
     c1 = c2 /\ strcat (implode s1) t1 = strcat (implode s2) t2`,
  REWRITE_TAC[strcat_thm; injectivity "mlstring"; explode_thm; APPEND; CONS_11]);;
let _ = cake_add_simps [mlstring_common_char_prefix];;

let mlstring_common_suffix = prove
 (`!s t1 t2. strcat t1 s = strcat t2 s <=> t1 = t2`,
  REWRITE_TAC[strcat_thm; injectivity "mlstring"; APPEND_RCANCEL; explode_11]);;
let _ = cake_add_simps [mlstring_common_suffix];;

let concat_append = prove
 (`mlstring_concat (APPEND xs ys) =
   strcat (mlstring_concat xs) (mlstring_concat ys)`,
  REWRITE_TAC[concat_thm; strcat_thm; explode_thm; MAP_APPEND; FLAT_APPEND]);;

let implode_STRCAT = prove
 (`!l1 l2. implode (APPEND l1 l2) = strcat (implode l1) (implode l2)`,
  REWRITE_TAC[strcat_thm; explode_thm]);;

let explode_strcat = prove
 (`explode (strcat s1 s2) = APPEND (explode s1) (explode s2)`,
  REWRITE_TAC[strcat_thm; explode_thm]);;
let _ = cake_add_simps [explode_strcat];;

let strlen_strcat = prove
 (`strlen (strcat s1 s2) = strlen s1 + strlen s2`,
  REWRITE_TAC[strcat_thm; strlen_def; LENGTH_APPEND; LENGTH_explode]);;
let _ = cake_add_simps [strlen_strcat];;

let concatWith_def = cake_def
  `concatWith s l = mlstring_concat (intersperse s l)`;;

let chr_to_str_def = cake_def
  `chr_to_str (c:char) = implode [c]`;;

(* HOL4: Overload toString = chr_to_str *)

let explode_toString = prove
 (`explode (chr_to_str c) = [c]`,
  REWRITE_TAC[chr_to_str_def; explode_thm]);;
let _ = cake_add_simps [explode_toString];;

let strlen_toString = prove
 (`strlen (chr_to_str c) = 1`,
  REWRITE_TAC[chr_to_str_def; strlen_def; LENGTH; ONE]);;
let _ = cake_add_simps [strlen_toString];;

let translate_aux_def = cake_def
  `(translate_aux (f:char->A) s n 0 = []) /\
   (translate_aux f s n (SUC len) =
      CONS (f (strsub s n)) (translate_aux f s (n + 1) len))`;;

let translate_def = cake_def
  `translate (f:char->char) s = implode (translate_aux f s 0 (strlen s))`;;

let translate_aux_thm = prove
 (`!(f:char->A) s n len. (n + len = strlen s) ==>
               (translate_aux f s n len = MAP f (DROP n (explode s)))`,
  GEN_TAC THEN MATCH_MP_TAC mlstring_INDUCT THEN X_GEN_TAC `a:string` THEN
  REWRITE_TAC[strlen_def; explode_thm] THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN INDUCT_TAC THEN
  REWRITE_TAC[translate_aux_def; ADD_CLAUSES] THENL
   [SIMP_TAC[DROP_LENGTH_NIL; MAP];
    REPEAT STRIP_TAC THEN REWRITE_TAC[strsub_def] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n + 1`) THEN
    ANTS_TAC THENL [POP_ASSUM MP_TAC THEN ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(ISPECL [`a:string`; `n:num`] DROP_EL_CONS) THEN
    ANTS_TAC THENL [POP_ASSUM MP_TAC THEN ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[MAP]]);;

let translate_thm = prove
 (`!f s. translate f s = implode (MAP f (explode s))`,
  SIMP_TAC[translate_def; translate_aux_thm; ADD_CLAUSES; DROP_0]);;

let splitl_aux_def = cake_def_wf
  `inv_image (<) (\p:(char->bool)#mlstring#num. strlen (FST (SND p)) - SND (SND p))`
  (REWRITE_TAC[inv_image_THM] THEN ARITH_TAC)
  `splitl_aux P s i =
     if i < strlen s /\ P (strsub s i) then splitl_aux P s (i + 1)
     else (mlstring_extract s 0 (SOME i), mlstring_extract s i NONE)`;;

let splitl_aux_ind = cake_ind "splitl_aux";;

let splitl_def = cake_def
  `splitl P s = splitl_aux P s 0`;;

let PURE1AUX_strsub_EL = prove
 (`!s i. strsub s i = EL i (explode s)`,
  MATCH_MP_TAC mlstring_INDUCT THEN REWRITE_TAC[strsub_def; explode_thm]);;

let PURE1AUX_extract_SOME_0 = prove
 (`!s i. mlstring_extract s 0 (SOME i) = implode (TAKE i (explode s))`,
  MATCH_MP_TAC mlstring_INDUCT THEN X_GEN_TAC `l:string` THEN GEN_TAC THEN
  REWRITE_TAC[mlstring_extract_def; strlen_def; explode_thm; option_CASE;
              SUB_0; LE] THEN
  COND_CASES_TAC THENL
   [ASM_REWRITE_TAC[TAKE_DEF; injectivity "mlstring"] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_EQ_NIL]) THEN ASM_REWRITE_TAC[TAKE_DEF];
    ALL_TAC] THEN
  REWRITE_TAC[substring_def; ADD_CLAUSES; injectivity "mlstring"] THEN
  ASM_CASES_TAC `i <= LENGTH (l:string)` THENL
   [ASM_SIMP_TAC[ARITH_RULE `i <= n ==> MIN n i = i`] THEN
    ASM_SIMP_TAC[SEG_TAKE_DROP; ADD_CLAUSES; DROP_0];
    ASM_SIMP_TAC[ARITH_RULE `~(i <= n) ==> MIN n i = n`; LE_REFL] THEN
    ASM_SIMP_TAC[SEG_LENGTH_ID; TAKE_LENGTH_TOO_LONG;
                 ARITH_RULE `~(i <= n) ==> n <= i`]]);;

let PURE1AUX_extract_NONE = prove
 (`!s i. mlstring_extract s i NONE = implode (DROP i (explode s))`,
  MATCH_MP_TAC mlstring_INDUCT THEN X_GEN_TAC `l:string` THEN GEN_TAC THEN
  REWRITE_TAC[mlstring_extract_def; strlen_def; explode_thm; option_CASE] THEN
  COND_CASES_TAC THENL
   [ASM_SIMP_TAC[DROP_LENGTH_TOO_LONG; injectivity "mlstring"]; ALL_TAC] THEN
  REWRITE_TAC[substring_def; injectivity "mlstring"] THEN
  SUBGOAL_THEN `i + LENGTH (l:string) - i <= LENGTH l` (fun th -> REWRITE_TAC[th]) THENL
   [POP_ASSUM MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC DROP_SEG THEN POP_ASSUM MP_TAC THEN
  ARITH_TAC);;

let splitl_aux_SPLITP = prove
 (`!P s i.
     splitl_aux P s i =
     ((implode o APPEND (TAKE i (explode s))) ## implode)
       (SPLITP ((~) o P) (DROP i (explode s)))`,
  MATCH_MP_TAC splitl_aux_ind THEN
  MAP_EVERY X_GEN_TAC [`P:char->bool`; `s:mlstring`; `i:num`] THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[splitl_aux_def] THEN
  ASM_CASES_TAC `i < strlen s /\ P (strsub s i)` THEN ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[PURE1AUX_strsub_EL]) THEN
    MP_TAC(ISPECL [`explode s`; `i:num`] DROP_EL_CONS) THEN
    MP_TAC(ISPECL [`explode s`; `i:num`] TAKE_EL_SNOC) THEN
    ASM_REWRITE_TAC[LENGTH_explode] THEN
    REPEAT(DISCH_THEN SUBST1_TAC) THEN
    ASM_REWRITE_TAC[SPLITP_DEF; o_THM; PAIR_MAP_DEF; FST; SND; SNOC_APPEND;
                    GSYM APPEND_ASSOC; APPEND];
    REWRITE_TAC[PURE1AUX_extract_SOME_0; PURE1AUX_extract_NONE] THEN
    SUBGOAL_THEN
      `SPLITP ((~) o P) (DROP i (explode s)) = ([], DROP i (explode s))`
      SUBST1_TAC THENL
     [ASM_CASES_TAC `i < strlen s` THENL
       [MP_TAC(ISPECL [`explode s`; `i:num`] DROP_EL_CONS) THEN
        ASM_REWRITE_TAC[LENGTH_explode] THEN DISCH_THEN SUBST1_TAC THEN
        FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[PURE1AUX_strsub_EL] o
                      check (is_neg o concl)) THEN
        ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[SPLITP_DEF; o_THM];
        MP_TAC(ISPECL [`explode s`; `i:num`] DROP_LENGTH_TOO_LONG) THEN
        ASM_REWRITE_TAC[LENGTH_explode; GSYM NOT_LT] THEN
        DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[SPLITP_DEF]];
      REWRITE_TAC[PAIR_MAP_THM; o_THM; APPEND_NIL]]]);;

let splitl_SPLITL = prove
 (`splitl P s = (implode ## implode) (SPLITL P (explode s))`,
  REWRITE_TAC[splitl_def; splitl_aux_SPLITP; SPLITL_def; TAKE_0; DROP_0] THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM; APPEND]);;

(* termination by the last argument, given explicitly (HOL4 finds it; the  *)
(* measure search of cake_def took most of a minute here)                  *)
let tokens_aux_def = cake_def_wf
  `MEASURE (\t:(char->bool)#mlstring#(char list)#num#num. SND (SND (SND (SND t))))`
  (REWRITE_TAC WF_REL_THMS THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
   REWRITE_TAC[FST; SND] THEN REPEAT STRIP_TAC THEN ASM_ARITH_TAC)
  `(tokens_aux (f:char->bool) s [] n 0 = []) /\
   (tokens_aux f s (CONS h t) n 0 = [implode (REVERSE (CONS h t))]) /\
   (tokens_aux f s [] n (SUC len) =
      if f (strsub s n) then tokens_aux f s [] (n + 1) len
      else tokens_aux f s [strsub s n] (n + 1) len) /\
   (tokens_aux f s (CONS h t) n (SUC len) =
      if f (strsub s n)
      then CONS (implode (REVERSE (CONS h t))) (tokens_aux f s [] (n + 1) len)
      else tokens_aux f s (CONS (strsub s n) (CONS h t)) (n + 1) len)`;;

let tokens_aux_ind = cake_ind "tokens_aux";;

let tokens_def = cake_def
  `tokens f s = tokens_aux f s [] 0 (strlen s)`;;

let tokens_aux_filter = prove
 (`!f s ss n len. (n + len = strlen s) ==>
     (mlstring_concat (tokens_aux f s ss n len) =
      implode (APPEND (REVERSE ss) (FILTER ((~) o f) (DROP n (explode s)))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM LENGTH_explode] THEN
  SPEC_TAC(`ss:string`,`ss:string`) THEN
  SPEC_TAC(`n:num`,`n:num`) THEN SPEC_TAC(`len:num`,`len:num`) THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[ADD_CLAUSES] THEN REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[DROP_LENGTH_NIL; FILTER; APPEND_NIL] THEN
    STRUCT_CASES_TAC (ISPEC `ss:string` list_CASES) THEN
    REWRITE_TAC[tokens_aux_def; concat_nil; concat_cons; strcat_nil; REVERSE;
                APPEND];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `n < LENGTH (explode s)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(n + 1) + len = LENGTH (explode s)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`explode s`; `n:num`] DROP_EL_CONS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n + 1`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  STRUCT_CASES_TAC (ISPEC `ss:string` list_CASES) THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [tokens_aux_def] THEN
  REWRITE_TAC[PURE1AUX_strsub_EL] THEN
  ASM_CASES_TAC `(f:char->bool) (EL n (explode s))` THEN
  ASM_REWRITE_TAC[FILTER; o_THM; concat_cons; strcat_thm; explode_thm; REVERSE;
                  APPEND; GSYM APPEND_ASSOC]);;

let tokens_filter = prove
 (`!f s. mlstring_concat (tokens f s) = implode (FILTER ((~) o f) (explode s))`,
  SIMP_TAC[tokens_def; tokens_aux_filter; ADD_CLAUSES; REVERSE; APPEND; DROP_0]);;

let PURE1AUX_TEA_TAC =
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `n < LENGTH (explode ls)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(n + 1) + len = LENGTH (explode ls)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`explode ls`; `n:num`] DROP_EL_CONS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n + 1`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `k:num` SUBST_ALL_TAC)
    (SPEC `len:num` num_CASES) THENL
   [MP_TAC(ISPECL [`explode ls`; `n + 1`] DROP_LENGTH_TOO_LONG) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST_ALL_TAC];
    MP_TAC(ISPECL [`explode ls`; `n + 1`] DROP_EL_CONS) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST_ALL_TAC]] THEN
  STRUCT_CASES_TAC (ISPEC `ss:string` list_CASES) THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [tokens_aux_def] THEN
  REWRITE_TAC[PURE1AUX_strsub_EL; list_CASE; NOT_SUC] THEN
  ASM_CASES_TAC `(P:char->bool) (EL n (explode ls))` THEN
  ASM_REWRITE_TAC[LSTRAUX_TOKENS_CONS; LSTRAUX_TOKENS_NIL_CLAUSE; SPLITP_DEF;
                  FST; SND; HD; TL; MAP; explode_thm; REVERSE; APPEND;
                  GSYM APPEND_ASSOC; list_CASE; NOT_SUC] THEN
  TRY(ASM_CASES_TAC `(P:char->bool) (EL (n + 1) (explode ls))` THEN
      ASM_REWRITE_TAC[LSTRAUX_TOKENS_CONS; LSTRAUX_TOKENS_NIL_CLAUSE; SPLITP_DEF;
                      FST; SND; HD; TL; MAP; explode_thm; REVERSE; APPEND;
                      GSYM APPEND_ASSOC; list_CASE; NOT_SUC]);;

let TOKENS_eq_tokens_aux = prove
 (CASE_TERM `!P ls ss n len. (n + len = LENGTH (explode ls)) ==>
     (MAP explode (tokens_aux P ls ss n len) =
      match ss with
        CONS h t ->
          if ~(len = 0) /\ ~(P (EL n (explode ls)))
          then CONS (APPEND (REVERSE (CONS h t))
                            (HD (TOKENS P (DROP n (explode ls)))))
                    (TL (TOKENS P (DROP n (explode ls))))
          else if ~(len = 0)
          then CONS (REVERSE (CONS h t)) (TOKENS P (DROP n (explode ls)))
          else [REVERSE (CONS h t)]
      | [] -> TOKENS P (DROP n (explode ls)))`,
  REPEAT GEN_TAC THEN SPEC_TAC(`ss:string`,`ss:string`) THEN
  SPEC_TAC(`n:num`,`n:num`) THEN SPEC_TAC(`len:num`,`len:num`) THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[ADD_CLAUSES] THEN REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[DROP_LENGTH_NIL; LSTRAUX_TOKENS_NIL_CLAUSE] THEN
    STRUCT_CASES_TAC (ISPEC `ss:string` list_CASES) THEN
    REWRITE_TAC[tokens_aux_def; MAP; list_CASE; explode_thm];
    PURE1AUX_TEA_TAC]);;

let TOKENS_eq_tokens = prove
 (`!P ls. MAP explode (tokens P ls) = TOKENS P (explode ls)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tokens_def] THEN
  MP_TAC(SPECL [`P:char->bool`; `ls:mlstring`; `[]:string`; `0`; `strlen ls`]
               TOKENS_eq_tokens_aux) THEN
  REWRITE_TAC[ADD_CLAUSES; LENGTH_explode; list_CASE; DROP_0]);;

(* HOL4 derives it from TOKENS_eq_tokens by applying MAP implode to both sides *)

let TOKENS_eq_tokens_sym = prove
 (`tokens P ls = MAP implode (TOKENS P (explode ls))`,
  REWRITE_TAC[GSYM TOKENS_eq_tokens; MAP_MAP_o; o_DEF; implode_explode; MAP_ID]);;

let tokens_append = prove
 (`!P s1 x s2.
     P x ==>
       (tokens P (strcat (strcat s1 (chr_to_str x)) s2) =
        APPEND (tokens P s1) (tokens P s2))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[TOKENS_eq_tokens_sym] THEN
  REWRITE_TAC[GSYM MAP_APPEND] THEN AP_TERM_TAC THEN
  REWRITE_TAC[explode_strcat; explode_toString; GSYM APPEND_ASSOC; APPEND] THEN
  MATCH_MP_TAC TOKENS_APPEND THEN ASM_REWRITE_TAC[]);;

let tokens_alt_aux_def = cake_def_wf
  `MEASURE (\p:(char->bool)#mlstring#num#num#num.
              SND (SND (SND (SND p))) - FST (SND (SND (SND p))))`
  (REWRITE_TAC[measure_THM] THEN REPEAT STRIP_TAC THEN ASM_ARITH_TAC)
  `tokens_alt_aux f s i j n =
     if j < n then
       (if f (strsub s j) then
          (if i = j then tokens_alt_aux f s (i + 1) (j + 1) n
           else CONS (substring s i (j - i)) (tokens_alt_aux f s (j + 1) (j + 1) n))
        else tokens_alt_aux f s i (j + 1) n)
     else if i = j then [] else [substring s i (j - i)]`;;

let tokens_alt_aux_ind = cake_ind "tokens_alt_aux";;

let substring_1_strsub = prove
 (`i < strlen s ==> substring s i 1 = chr_to_str (strsub s i)`,
  PURE1AUX_MLSTRING_CASES_TAC `s:mlstring` THEN
  REWRITE_TAC[substring_def; strlen_def; strsub_def; chr_to_str_def;
              injectivity "mlstring"] THEN
  DISCH_TAC THEN SUBGOAL_THEN `i + 1 <= LENGTH (a:string)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ASM_SIMP_TAC[SEG1]]);;

let substring_0 = prove
 (`substring s i 0 = implode ""`,
  PURE1AUX_MLSTRING_CASES_TAC `s:mlstring` THEN
  REWRITE_TAC[substring_def; ADD_CLAUSES; SEG; injectivity "mlstring"] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN COND_CASES_TAC THEN
  ASM_MESON_TAC[]);;
let _ = cake_add_simps [substring_0];;

let substring_add = prove
 (`(i + x) + y <= strlen s ==>
   substring s i (x + y) =
   strcat (substring s i x) (substring s (i + x) y)`,
  PURE1AUX_MLSTRING_CASES_TAC `s:mlstring` THEN
  REWRITE_TAC[substring_def; strlen_def; strcat_thm; explode_thm;
              injectivity "mlstring"] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `i + x + y <= LENGTH (a:string) /\ i + x <= LENGTH a`
    STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(x + y) + i <= LENGTH (a:string) /\ x + i <= LENGTH a /\
                y + (i + x) <= LENGTH a` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[SEG_TAKE_DROP; TAKE_SUM; DROP_DROP_T] THEN
  REWRITE_TAC[ADD_SYM]);;

let PURE1AUX_tokens_aux_0 = prove
 (`!f s acc n. tokens_aux f s acc n 0 =
               if acc = [] then [] else [implode (REVERSE acc)]`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `acc:string` list_CASES) THEN
  REWRITE_TAC[tokens_aux_def; NOT_CONS_NIL]);;

let PURE1AUX_tokens_aux_SUC = prove
 (`!f s acc n len.
     tokens_aux f s acc n (SUC len) =
     if f (strsub s n)
     then (if acc = [] then tokens_aux f s [] (n + 1) len
           else CONS (implode (REVERSE acc)) (tokens_aux f s [] (n + 1) len))
     else tokens_aux f s (CONS (strsub s n) acc) (n + 1) len`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `acc:string` list_CASES) THEN
  REWRITE_TAC[tokens_aux_def; NOT_CONS_NIL]);;

let PURE1AUX_substring_nil = prove
 (`!s i j. i <= j /\ j <= strlen s
           ==> (explode (substring s i (j - i)) = [] <=> i = j)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM LENGTH_EQ_NIL; LENGTH_explode] THEN
  REWRITE_TAC[strlen_substring] THEN
  SUBGOAL_THEN `i + j - i <= strlen s` (fun th -> REWRITE_TAC[th]) THEN
  ASM_ARITH_TAC);;

let PURE1AUX_substring_snoc = prove
 (`!s i j. i <= j /\ j < strlen s
           ==> explode (substring s i ((j + 1) - i)) =
               APPEND (explode (substring s i (j - i))) [strsub s j]`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(j + 1) - i = (j - i) + 1` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(INST [`j - i`,`x:num`; `1`,`y:num`] substring_add) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `i + j - i = j` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[substring_1_strsub; explode_strcat; explode_toString]);;

let tokens_alt_tokens_alt_aux = prove
 (`!f s acc j l i.
     i <= j /\ j <= strlen s /\
     strlen s - j = l /\
     acc = REVERSE (explode (substring s i (j - i))) ==>
     tokens_aux f s acc j l =
     tokens_alt_aux f s i j (strlen s)`,
  REPEAT GEN_TAC THEN SPEC_TAC(`i:num`,`i:num`) THEN
  SPEC_TAC(`acc:string`,`acc:string`) THEN SPEC_TAC(`j:num`,`j:num`) THEN
  SPEC_TAC(`l:num`,`l:num`) THEN INDUCT_TAC THEN REPEAT GEN_TAC THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ONCE_REWRITE_TAC[tokens_alt_aux_def] THENL
   [SUBGOAL_THEN `j = strlen s` SUBST_ALL_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[LT_REFL; PURE1AUX_tokens_aux_0; REVERSE_EQ_NIL] THEN
    ASM_SIMP_TAC[PURE1AUX_substring_nil; LE_REFL] THEN
    COND_CASES_TAC THEN REWRITE_TAC[REVERSE_REVERSE; implode_explode];
    ALL_TAC] THEN
  SUBGOAL_THEN `j < strlen s` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[PURE1AUX_tokens_aux_SUC; REVERSE_EQ_NIL] THEN
  ASM_SIMP_TAC[PURE1AUX_substring_nil; LT_IMP_LE] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j + 1`) THEN
  SUBGOAL_THEN `j + 1 <= strlen s /\ strlen s - (j + 1) = l` STRIP_ASSUME_TAC
  THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `tokens_aux f s [] (j + 1) l = tokens_alt_aux f s (j + 1) (j + 1) (strlen s)`
    SUBST1_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[LE_REFL; SUB_REFL; substring_0; explode_thm; REVERSE];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `tokens_aux f s (CONS (strsub s j) (REVERSE (explode (substring s i (j - i)))))
                (j + 1) l = tokens_alt_aux f s i (j + 1) (strlen s)`
    SUBST1_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[PURE1AUX_substring_snoc; REVERSE_APPEND; REVERSE; APPEND] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REVERSE_REVERSE; implode_explode] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[]);;

let tokens_alt = prove
 (`tokens f s = tokens_alt_aux f s 0 0 (strlen s)`,
  REWRITE_TAC[tokens_def] THEN MATCH_MP_TAC tokens_alt_tokens_alt_aux THEN
  REWRITE_TAC[LE_REFL; LE_0; SUB_0; SUB_REFL; substring_0; explode_thm; REVERSE]);;

(* termination by the last argument, given explicitly (as tokens_aux) *)
let fields_aux_def = cake_def_wf
  `MEASURE (\t:(char->bool)#mlstring#(char list)#num#num. SND (SND (SND (SND t))))`
  (REWRITE_TAC WF_REL_THMS THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
   REWRITE_TAC[FST; SND] THEN REPEAT STRIP_TAC THEN ASM_ARITH_TAC)
  `(fields_aux (f:char->bool) s ss n 0 = [implode (REVERSE ss)]) /\
   (fields_aux f s ss n (SUC len) =
      if f (strsub s n)
      then CONS (implode (REVERSE ss)) (fields_aux f s [] (n + 1) len)
      else fields_aux f s (CONS (strsub s n) ss) (n + 1) len)`;;

let fields_def = cake_def
  `fields f s = fields_aux f s [] 0 (strlen s)`;;

let fields_aux_filter = prove
 (`!f s ss n len. (n + len = strlen s) ==>
     (mlstring_concat (fields_aux f s ss n len) =
      implode (APPEND (REVERSE ss) (FILTER ((~) o f) (DROP n (explode s)))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM LENGTH_explode] THEN
  SPEC_TAC(`ss:string`,`ss:string`) THEN
  SPEC_TAC(`n:num`,`n:num`) THEN SPEC_TAC(`len:num`,`len:num`) THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[ADD_CLAUSES] THEN REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[DROP_LENGTH_NIL; FILTER; APPEND_NIL; fields_aux_def;
                concat_cons; concat_nil; strcat_nil];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `n < LENGTH (explode s)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(n + 1) + len = LENGTH (explode s)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`explode s`; `n:num`] DROP_EL_CONS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n + 1`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [fields_aux_def] THEN
  REWRITE_TAC[PURE1AUX_strsub_EL] THEN
  ASM_CASES_TAC `(f:char->bool) (EL n (explode s))` THEN
  ASM_REWRITE_TAC[FILTER; o_THM; concat_cons; strcat_thm; explode_thm; REVERSE;
                  APPEND; GSYM APPEND_ASSOC]);;

let fields_filter = prove
 (`!f s. mlstring_concat (fields f s) = implode (FILTER ((~) o f) (explode s))`,
  SIMP_TAC[fields_def; fields_aux_filter; ADD_CLAUSES; REVERSE; APPEND; DROP_0]);;

let fields_aux_length = prove
 (`!f s ss n len. (n + len = strlen s) ==>
     (LENGTH (fields_aux f s ss n len) = LENGTH (FILTER f (DROP n (explode s))) + 1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM LENGTH_explode] THEN
  SPEC_TAC(`ss:string`,`ss:string`) THEN
  SPEC_TAC(`n:num`,`n:num`) THEN SPEC_TAC(`len:num`,`len:num`) THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[ADD_CLAUSES] THEN REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[DROP_LENGTH_NIL; FILTER; fields_aux_def; LENGTH] THEN ARITH_TAC;
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `n < LENGTH (explode s)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(n + 1) + len = LENGTH (explode s)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`explode s`; `n:num`] DROP_EL_CONS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n + 1`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [fields_aux_def] THEN
  REWRITE_TAC[PURE1AUX_strsub_EL] THEN
  ASM_CASES_TAC `(f:char->bool) (EL n (explode s))` THEN
  ASM_REWRITE_TAC[FILTER; LENGTH] THEN ARITH_TAC);;

let fields_length = prove
 (`!f s. LENGTH (fields f s) = (LENGTH (FILTER f (explode s)) + 1)`,
  SIMP_TAC[fields_def; fields_aux_length; ADD_CLAUSES; DROP_0]);;

let fields_alt_aux_def = cake_def_wf
  `MEASURE (\p:(char->bool)#mlstring#num#num#num.
              SND (SND (SND (SND p))) - FST (SND (SND (SND p))))`
  (REWRITE_TAC[measure_THM] THEN REPEAT STRIP_TAC THEN ASM_ARITH_TAC)
  `fields_alt_aux f s i j n =
     if j < n then
       (if f (strsub s j)
        then CONS (substring s i (j - i)) (fields_alt_aux f s (j + 1) (j + 1) n)
        else fields_alt_aux f s i (j + 1) n)
     else [substring s i (j - i)]`;;

let fields_alt_aux_ind = cake_ind "fields_alt_aux";;

let fields_alt_fields_alt_aux = prove
 (`!l acc j i.
     i <= j /\ j <= strlen s /\
     strlen s - j = l /\
     acc = REVERSE (explode (substring s i (j - i))) ==>
     fields_aux f s acc j l =
     fields_alt_aux f s i j (strlen s)`,
  INDUCT_TAC THEN REPEAT GEN_TAC THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ONCE_REWRITE_TAC[fields_alt_aux_def] THENL
   [SUBGOAL_THEN `j = strlen s` SUBST_ALL_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[LT_REFL; fields_aux_def; REVERSE_REVERSE; implode_explode];
    ALL_TAC] THEN
  SUBGOAL_THEN `j < strlen s` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[fields_aux_def; REVERSE_REVERSE; implode_explode] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j + 1` o ONCE_REWRITE_RULE[SWAP_FORALL_THM]) THEN
  SUBGOAL_THEN `j + 1 <= strlen s /\ strlen s - (j + 1) = l` STRIP_ASSUME_TAC
  THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `fields_aux f s [] (j + 1) l =
                fields_alt_aux f s (j + 1) (j + 1) (strlen s)`
    SUBST1_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[LE_REFL; SUB_REFL; substring_0; explode_thm; REVERSE];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `fields_aux f s (CONS (strsub s j) (REVERSE (explode (substring s i (j - i)))))
                (j + 1) l = fields_alt_aux f s i (j + 1) (strlen s)`
    SUBST1_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[PURE1AUX_substring_snoc; REVERSE_APPEND; REVERSE; APPEND] THEN
    ASM_ARITH_TAC;
    REWRITE_TAC[]]);;

let fields_alt = prove
 (`fields f s = fields_alt_aux f s 0 0 (strlen s)`,
  REWRITE_TAC[fields_def] THEN MATCH_MP_TAC fields_alt_fields_alt_aux THEN
  REWRITE_TAC[LE_REFL; LE_0; SUB_0; SUB_REFL; substring_0; explode_thm; REVERSE]);;

let str_findi_def = cake_def_wf
  `MEASURE (\p:(char->bool)#num#mlstring. strlen (SND (SND p)) - FST (SND p))`
  (REWRITE_TAC[measure_THM] THEN REPEAT STRIP_TAC THEN ASM_ARITH_TAC)
  `str_findi P i s =
     if i < strlen s
     then if P (strsub s i) then SOME i else str_findi P (i + 1) s
     else NONE`;;

let str_findi_ind = cake_ind "str_findi";;

let str_findi_range = prove
 (`!P i s. str_findi P i s = SOME j ==> i <= j /\ j < strlen s`,
  MATCH_MP_TAC str_findi_ind THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[str_findi_def] THEN
  ASM_CASES_TAC `i < strlen s` THEN ASM_REWRITE_TAC[distinctness "option"] THEN
  ASM_CASES_TAC `(P:char->bool) (strsub s i)` THEN
  ASM_REWRITE_TAC[injectivity "option"] THENL
   [DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[LE_REFL];
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC]);;

let OLEAST_LE_STEP = prove
 (`(OLEAST j. i <= j /\ P j) =
   (if P i then SOME i else (OLEAST j. i + 1 <= j /\ P j))`,
  COND_CASES_TAC THENL
   [REWRITE_TAC[OLEAST_EQ_SOME] THEN ASM_REWRITE_TAC[LE_REFL] THEN ARITH_TAC;
    AP_TERM_TAC THEN ABS_TAC THEN ASM_CASES_TAC `j:num = i` THEN
    ASM_REWRITE_TAC[] THEN ASM_CASES_TAC `(P:num->bool) j` THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

let str_findi_OLEAST = prove
 (`!P i s. str_findi P i s = (OLEAST j. i <= j /\ j < strlen s /\ P (strsub s j))`,
  MATCH_MP_TAC str_findi_ind THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [OLEAST_LE_STEP] THEN
  ONCE_REWRITE_TAC[str_findi_def] THEN
  ASM_CASES_TAC `i < strlen s` THEN ASM_REWRITE_TAC[] THENL
   [COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[];
    CONV_TAC SYM_CONV THEN REWRITE_TAC[OLEAST_EQ_NONE] THEN GEN_TAC THEN
    MATCH_MP_TAC(TAUT `~(a /\ b) ==> ~(a /\ b /\ c)`) THEN ASM_ARITH_TAC]);;

let isStringThere_aux_def = cake_def
  `(isStringThere_aux s1 s2 s1i s2i 0 = T) /\
   (isStringThere_aux s1 s2 s1i s2i (SUC len) =
      if strsub s1 s1i = strsub s2 s2i
      then isStringThere_aux s1 s2 (s1i + 1) (s2i + 1) len
      else F)`;;

let isPrefix_def = cake_def
  `isPrefix s1 s2 <=>
     if strlen s1 <= strlen s2
     then isStringThere_aux s1 s2 0 0 (strlen s1)
     else F`;;

let exists_mlstring = prove
 (`(?x:mlstring. P x) <=> (?s. P (implode s))`,
  MESON_TAC[cases "mlstring"]);;

let isprefix_thm_aux = prove
 (`!ys xs zs.
     LENGTH ys <= LENGTH zs ==>
     (isStringThere_aux (implode (APPEND xs ys)) (implode (APPEND xs zs))
        (LENGTH xs) (LENGTH xs) (LENGTH ys) <=>
      ys <<= zs)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[isStringThere_aux_def; LENGTH; isPREFIX] THEN
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; list_CASE; ARITH_RULE `~(SUC n <= 0)`; LE_SUC] THEN
  DISCH_TAC THEN REWRITE_TAC[strsub_def; EL_APPEND; LT_REFL; SUB_REFL; EL; HD] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`APPEND xs [h:char]`; `t':string`]) THEN
  ASM_REWRITE_TAC[GSYM APPEND_ASSOC; APPEND; LENGTH_APPEND; LENGTH; ONE;
                  ADD_CLAUSES] THEN
  DISCH_TAC THEN ASM_CASES_TAC `h:char = h'` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]]);;

let isprefix_thm = prove
 (`isPrefix s1 s2 <=> explode s1 <<= explode s2`,
  PURE1AUX_MLSTRING_CASES_TAC `s1:mlstring` THEN
  PURE1AUX_MLSTRING_CASES_TAC `s2:mlstring` THEN
  REWRITE_TAC[isPrefix_def; strlen_def; explode_thm] THEN
  COND_CASES_TAC THENL
   [MP_TAC(SPECL [`a:string`; `[]:string`; `a':string`] isprefix_thm_aux) THEN
    ASM_REWRITE_TAC[APPEND; LENGTH];
    ASM_MESON_TAC[IS_PREFIX_LENGTH]]);;

let isprefix_strcat = prove
 (`!s1 s2. isPrefix s1 s2 <=> ?s3. s2 = strcat s1 s3`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[isprefix_thm; strcat_thm; isPREFIX_STRCAT; exists_mlstring] THEN
  REWRITE_TAC[explode_thm] THEN
  MESON_TAC[implode_explode; explode_implode]);;

let isSuffix_def = cake_def
  `isSuffix s1 s2 <=>
     if strlen s1 <= strlen s2
     then isStringThere_aux s1 s2 0 (strlen s2 - strlen s1) (strlen s1)
     else F`;;

let isSubstring_aux_def = cake_def
  `(isSubstring_aux s1 s2 lens1 n 0 = F) /\
   (isSubstring_aux s1 s2 lens1 n (SUC len) =
      if isStringThere_aux s1 s2 0 n lens1 then T
      else isSubstring_aux s1 s2 lens1 (n + 1) len)`;;

let isSubstring_def = cake_def
  `isSubstring s1 s2 <=>
     if strlen s1 <= strlen s2
     then isSubstring_aux s1 s2 (strlen s1) 0 ((strlen s2 - strlen s1) + 1)
     else F`;;

(* proof that isSubstring has the right sort of properties *)

let isStringThere_SEG = prove
 (`!i1 i2.
     i1 + n <= LENGTH s1 /\ i2 + n <= LENGTH s2 ==>
     (isStringThere_aux (implode s1) (implode s2) i1 i2 n <=>
      (SEG n i1 s1 = SEG n i2 s2))`,
  SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THEN
  REWRITE_TAC[isStringThere_aux_def; SEG] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`n:num`; `i1:num`; `s1:string`] SEG_SUC_EL) THEN
  MP_TAC(ISPECL [`n:num`; `i2:num`; `s2:string`] SEG_SUC_EL) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[strsub_def; CONS_11] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`i1 + 1`; `i2 + 1`]) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

let isSubstring_aux_lemma = prove
 (`!i len.
     i + len <= strlen s2 ==>
     (isSubstring_aux s1 s2 lens1 i len <=>
      ?n. n < len /\ isStringThere_aux s1 s2 0 (n + i) lens1)`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  INDUCT_TAC THEN REWRITE_TAC[isSubstring_aux_def; CONJUNCT1 LT] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i + 1`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  EQ_TAC THENL
   [COND_CASES_TAC THEN REWRITE_TAC[] THENL
     [EXISTS_TAC `0` THEN ASM_REWRITE_TAC[ADD_CLAUSES; LT_0];
      DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `m + 1` THEN
      ASM_REWRITE_TAC[ARITH_RULE `m + 1 < SUC len <=> m < len`;
                      ARITH_RULE `(m + 1) + i = m + i + 1`]];
    DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `k:num` SUBST_ALL_TAC)
      (SPEC `m:num` num_CASES) THENL
     [ASM_MESON_TAC[ADD_CLAUSES];
      EXISTS_TAC `k:num` THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `isStringThere_aux s1 s2 0 (SUC k + i) lens1` THEN
      REWRITE_TAC[ARITH_RULE `SUC k + i = k + i + 1`]]]);;

let isSubstring_SEG = prove
 (`isSubstring (implode s1) (implode s2) <=>
   ?i. i + LENGTH s1 <= LENGTH s2 /\ SEG (LENGTH s1) i s2 = s1`,
  REWRITE_TAC[isSubstring_def; strlen_def] THEN
  ASM_CASES_TAC `LENGTH (s1:string) <= LENGTH (s2:string)` THEN
  ASM_REWRITE_TAC[] THENL
   [ALL_TAC; ASM_MESON_TAC[ARITH_RULE `i + a <= b ==> a <= b`]] THEN
  ASM_CASES_TAC `s1:string = []` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REWRITE_TAC[LENGTH; SUB_0; GSYM ADD1; isSubstring_aux_def;
                isStringThere_aux_def; SEG] THEN
    EXISTS_TAC `0` THEN REWRITE_TAC[LE_0; ADD_CLAUSES];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(LENGTH (s1:string) = 0)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_EQ_NIL]; ALL_TAC] THEN
  MP_TAC(INST [`implode s2`,`s2:mlstring`; `implode s1`,`s1:mlstring`;
               `LENGTH (s1:string)`,`lens1:num`]
           (SPECL [`0`; `(LENGTH (s2:string) - LENGTH (s1:string)) + 1`]
                  isSubstring_aux_lemma)) THEN
  REWRITE_TAC[strlen_def; ADD_CLAUSES] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  EQ_TAC THEN DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `m:num` THENL
   [MP_TAC(SPECL [`0`; `m:num`]
      (INST [`LENGTH (s1:string)`,`n:num`] isStringThere_SEG)) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE) THEN ASM_REWRITE_TAC[SEG_LENGTH_ID] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_ARITH_TAC;
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`0`; `m:num`]
      (INST [`LENGTH (s1:string)`,`n:num`] isStringThere_SEG)) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[SEG_LENGTH_ID]]);;

let strlit_STRCAT = prove
 (`strcat (implode a) (implode b) = implode (APPEND a b)`,
  REWRITE_TAC[strcat_thm; explode_thm]);;

let isSubString_spec = prove
 (`isSubstring s1 s2 <=> ?p s. s2 = strcat (strcat p s1) s`,
  PURE1AUX_MLSTRING_CASES_TAC `s1:mlstring` THEN
  PURE1AUX_MLSTRING_CASES_TAC `s2:mlstring` THEN
  REWRITE_TAC[isSubstring_SEG; exists_mlstring; strlit_STRCAT;
              injectivity "mlstring"] THEN
  EQ_TAC THEN STRIP_TAC THENL
   [MAP_EVERY EXISTS_TAC
      [`TAKE i (a':string)`; `DROP (i + LENGTH (a:string)) (a':string)`] THEN
    MP_TAC(ISPECL [`LENGTH (a:string)`; `i:num`; `a':string`] TAKE_SEG_DROP) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(ACCEPT_TAC o SYM);
    EXISTS_TAC `LENGTH (s:string)` THEN ASM_REWRITE_TAC[LENGTH_APPEND] THEN
    CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`LENGTH (a:string)`; `LENGTH (s:string)`;
                   `APPEND (s:string) a`] SEG_APPEND1) THEN
    REWRITE_TAC[LENGTH_APPEND; ADD_SYM; LE_REFL] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    MP_TAC(ISPECL [`s:string`; `LENGTH (s:string)`; `LENGTH (a:string)`; `a:string`]
                  SEG_APPEND2) THEN
    REWRITE_TAC[LE_REFL; SUB_REFL; SEG_LENGTH_ID] THEN
    DISCH_THEN ACCEPT_TAC]);;

(* String orderings *)

let compare_aux_def = cake_def_wf
  `MEASURE (\p:mlstring#mlstring#ordering#num#num. SND (SND (SND (SND p))))`
  (REWRITE_TAC[measure_THM] THEN REPEAT STRIP_TAC THEN ASM_ARITH_TAC)
  `compare_aux (s1:mlstring) s2 ord start len =
     if len = 0 then ord
     else if char_lt (strsub s2 start) (strsub s1 start) then GREATER
     else if char_lt (strsub s1 start) (strsub s2 start) then LESS
     else compare_aux s1 s2 ord (start + 1) (len - 1)`;;

(* HOL4: compare *)

let mlstring_compare_def = cake_def
  `mlstring_compare s1 s2 =
     if strlen s1 < strlen s2 then compare_aux s1 s2 LESS 0 (strlen s1)
     else if strlen s2 < strlen s1 then compare_aux s1 s2 GREATER 0 (strlen s2)
     else compare_aux s1 s2 EQUAL 0 (strlen s2)`;;

let mlstring_lt_def = cake_def
  `mlstring_lt s1 s2 <=> (mlstring_compare s1 s2 = LESS)`;;

let mlstring_le_def = cake_def
  `mlstring_le s1 s2 <=> ~(mlstring_compare s1 s2 = GREATER)`;;

let mlstring_gt_def = cake_def
  `mlstring_gt s1 s2 <=> (mlstring_compare s1 s2 = GREATER)`;;

let mlstring_ge_def = cake_def
  `mlstring_ge s1 s2 <=> ~(mlstring_compare s1 s2 = LESS)`;;

let compare_thm = prove
 (`mlstring_compare s1 s2 =
     if mlstring_lt s1 s2 then LESS else
     if mlstring_le s1 s2 then EQUAL else GREATER`,
  REWRITE_TAC[mlstring_lt_def; mlstring_le_def] THEN
  STRUCT_CASES_TAC (ISPEC `mlstring_compare s1 s2` (cases "ordering")) THEN
  REWRITE_TAC[distinctness "ordering"]);;

(* HOL4: Overload < <= > >= (mlstring) = mlstring_lt ... (written out here) *)

let fast_lt_def = cake_def
  `fast_lt s1 s2 <=>
     if strlen s1 = strlen s2 then mlstring_lt s1 s2 else strlen s1 < strlen s2`;;

let fast_le_def = cake_def
  `fast_le s1 s2 <=>
     if strlen s1 = strlen s2 then mlstring_le s1 s2 else strlen s1 <= strlen s2`;;

let fast_gt_def = cake_def
  `fast_gt s1 s2 <=>
     if strlen s1 = strlen s2 then mlstring_gt s1 s2 else strlen s1 > strlen s2`;;

let fast_ge_def = cake_def
  `fast_ge s1 s2 <=>
     if strlen s1 = strlen s2 then mlstring_ge s1 s2 else strlen s1 >= strlen s2`;;

(* Properties of string orderings *)

(* HOL4: val flip_ord_def = invert_comparison_def; Overload flip_ord =   *)
(* invert_comparison (written invert_comparison here)                    *)

let compare_aux_spec = prove
 (`!s1 s2 ord_in start len.
     len + start <= strlen s1 /\ len + start <= strlen s2 ==>
     (compare_aux s1 s2 ord_in start len =
        if TAKE len (DROP start (explode s1)) = TAKE len (DROP start (explode s2))
        then ord_in
        else if string_lt (TAKE len (DROP start (explode s1)))
                          (TAKE len (DROP start (explode s2)))
        then LESS
        else GREATER)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN INDUCT_TAC THEN
  ONCE_REWRITE_TAC[compare_aux_def] THEN REWRITE_TAC[TAKE_0; NOT_SUC] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUC_SUB1] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM LENGTH_explode]) THEN
  MP_TAC(ISPECL [`explode s1`; `start:num`] DROP_EL_CONS) THEN
  MP_TAC(ISPECL [`explode s2`; `start:num`] DROP_EL_CONS) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[TAKE_DEF; NOT_SUC; SUC_SUB1; CONS_11; string_lt_def;
              PURE1AUX_strsub_EL] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `start + 1`) THEN
  REWRITE_TAC[GSYM LENGTH_explode] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  ABBREV_TAC `c1 = EL start (explode s1)` THEN
  ABBREV_TAC `c2 = EL start (explode s2)` THEN
  ASM_CASES_TAC `char_lt c2 c1` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `~(c1:char = c2) /\ ~char_lt c1 c2` STRIP_ASSUME_TAC THENL
     [POP_ASSUM MP_TAC THEN REWRITE_TAC[char_lt_def; CHAR_EQ_THM] THEN ARITH_TAC;
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_CASES_TAC `char_lt c1 c2` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `~(c1:char = c2)` (fun th -> REWRITE_TAC[th]) THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC[char_lt_def; CHAR_EQ_THM] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `c1:char = c2` (fun th -> REWRITE_TAC[th]) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[char_lt_def; CHAR_EQ_THM] THEN
  ARITH_TAC);;

let compare_aux_refl = prove
 (`!s1 s2 start len.
     start + len <= strlen s1 /\ start + len <= strlen s2
     ==>
     ((compare_aux s1 s2 EQUAL start len = EQUAL)
      <=>
      (TAKE len (DROP start (explode s1)) = TAKE len (DROP start (explode s2))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`s1:mlstring`; `s2:mlstring`; `EQUAL`; `start:num`; `len:num`]
               compare_aux_spec) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[distinctness "ordering"]);;

let compare_aux_equal = prove
 (`!s1 s2 ord_in start len.
     (compare_aux s1 s2 ord_in start len = EQUAL) ==> (ord_in = EQUAL)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN INDUCT_TAC THEN
  ONCE_REWRITE_TAC[compare_aux_def] THEN REWRITE_TAC[NOT_SUC; SUC_SUB1] THEN
  GEN_TAC THEN REPEAT COND_CASES_TAC THEN
  ASM_REWRITE_TAC[distinctness "ordering"]);;

let PURE1AUX_invert_11 = prove
 (`!x y. invert_comparison x = invert_comparison y <=> x = y`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `x:ordering` (cases "ordering")) THEN
  STRUCT_CASES_TAC (SPEC `y:ordering` (cases "ordering")) THEN
  REWRITE_TAC[invert_comparison_def; distinctness "ordering"]);;

let compare_aux_sym = prove
 (`!s1 s2 ord_in start len ord_out.
     (compare_aux s1 s2 ord_in start len = ord_out)
     <=>
     (compare_aux s2 s1 (invert_comparison ord_in) start len =
      invert_comparison ord_out)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN INDUCT_TAC THEN
  ONCE_REWRITE_TAC[compare_aux_def] THEN
  REWRITE_TAC[NOT_SUC; SUC_SUB1; PURE1AUX_invert_11] THEN
  REPEAT GEN_TAC THEN
  ABBREV_TAC `c1 = strsub s1 start` THEN ABBREV_TAC `c2 = strsub s2 start` THEN
  ASM_CASES_TAC `char_lt c2 c1` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `~char_lt c1 c2` (fun th -> REWRITE_TAC[th]) THENL
     [POP_ASSUM MP_TAC THEN REWRITE_TAC[char_lt_def] THEN ARITH_TAC;
      ALL_TAC] THEN
    STRUCT_CASES_TAC (SPEC `ord_out:ordering` (cases "ordering")) THEN
    REWRITE_TAC[invert_comparison_def; distinctness "ordering"];
    ALL_TAC] THEN
  ASM_CASES_TAC `char_lt c1 c2` THEN ASM_REWRITE_TAC[] THEN
  STRUCT_CASES_TAC (SPEC `ord_out:ordering` (cases "ordering")) THEN
  REWRITE_TAC[invert_comparison_def; distinctness "ordering"]);;

let string_lt_take_mono = prove
 (`!s1 s2 x.
     string_lt s1 s2 ==> string_lt (TAKE x s1) (TAKE x s2) \/ (TAKE x s1 = TAKE x s2)`,
  MATCH_MP_TAC string_lt_ind THEN REWRITE_TAC[string_lt_def] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[TAKE_DEF] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[string_lt_def; CONS_11] THEN
  ASM_MESON_TAC[]);;

let string_lt_remove_take = prove
 (`!s1 s2 x. string_lt (TAKE x s1) (TAKE x s2) ==> string_lt s1 s2`,
  MATCH_MP_TAC string_lt_ind THEN REWRITE_TAC[string_lt_def; TAKE_DEF] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[string_lt_def] THEN ASM_MESON_TAC[]);;

let string_prefix_le = prove
 (`!s1 s2. s1 <<= s2 ==> string_le s1 s2`,
  MATCH_MP_TAC string_lt_ind THEN
  REWRITE_TAC[string_lt_def; string_le_def; isPREFIX; isPREFIX_NILR;
              list_CASE; CONS_11] THEN
  MESON_TAC[]);;

let take_prefix = prove
 (`!l (s:A list). TAKE l s <<= s`,
  GEN_TAC THEN SPEC_TAC(`l:num`,`l:num`) THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[TAKE_DEF; isPREFIX] THEN
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[isPREFIX; list_CASE]);;

let PURE1AUX_compare_explode = prove
 (`!s1 s2. mlstring_compare s1 s2 =
           if explode s1 = explode s2 then EQUAL
           else if string_lt (explode s1) (explode s2) then LESS
           else GREATER`,
  MATCH_MP_TAC mlstring_INDUCT THEN X_GEN_TAC `u:string` THEN
  MATCH_MP_TAC mlstring_INDUCT THEN X_GEN_TAC `v:string` THEN
  REWRITE_TAC[mlstring_compare_def; explode_thm; strlen_def] THEN
  SIMP_TAC[compare_aux_spec; ADD_CLAUSES; strlen_def; LE_REFL; LT_IMP_LE;
           explode_thm; DROP_0] THEN
  ASM_CASES_TAC `LENGTH (u:string) < LENGTH (v:string)` THEN
  ASM_REWRITE_TAC[TAKE_LENGTH_ID] THENL
   [SUBGOAL_THEN `~(u:string = v)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_MESON_TAC[LT_REFL]; ALL_TAC] THEN
    SUBGOAL_THEN `(u = TAKE (LENGTH u) (v:string) \/
                   string_lt u (TAKE (LENGTH u) v)) <=> string_lt u v`
     MP_TAC THENL
     [EQ_TAC THENL
       [STRIP_TAC THENL
         [MP_TAC(ISPECL [`LENGTH (u:string)`; `v:string`] take_prefix) THEN
          FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
          DISCH_THEN(MP_TAC o MATCH_MP string_prefix_le) THEN
          REWRITE_TAC[string_le_def] THEN ASM_MESON_TAC[LT_REFL];
          MATCH_MP_TAC string_lt_remove_take THEN
          EXISTS_TAC `LENGTH (u:string)` THEN ASM_REWRITE_TAC[TAKE_LENGTH_ID]];
        DISCH_THEN(MP_TAC o SPEC `LENGTH (u:string)` o
                   MATCH_MP string_lt_take_mono) THEN
        REWRITE_TAC[TAKE_LENGTH_ID] THEN MESON_TAC[]];
      DISCH_THEN(SUBST1_TAC o SYM) THEN COND_CASES_TAC THEN REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_CASES_TAC `LENGTH (v:string) < LENGTH (u:string)` THEN
  ASM_REWRITE_TAC[TAKE_LENGTH_ID] THENL
   [SUBGOAL_THEN `~(u:string = v)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_MESON_TAC[LT_REFL]; ALL_TAC] THEN
    SUBGOAL_THEN `(~(TAKE (LENGTH v) u = (v:string)) /\
                   string_lt (TAKE (LENGTH v) u) v) <=> string_lt u v`
     MP_TAC THENL
     [EQ_TAC THENL
       [STRIP_TAC THEN MATCH_MP_TAC string_lt_remove_take THEN
        EXISTS_TAC `LENGTH (v:string)` THEN ASM_REWRITE_TAC[TAKE_LENGTH_ID];
        DISCH_TAC THEN
        FIRST_ASSUM(MP_TAC o SPEC `LENGTH (v:string)` o
                    MATCH_MP string_lt_take_mono) THEN
        REWRITE_TAC[TAKE_LENGTH_ID] THEN STRIP_TAC THENL
         [ASM_MESON_TAC[string_lt_nonrefl]; ALL_TAC] THEN
        MP_TAC(ISPECL [`LENGTH (v:string)`; `u:string`] take_prefix) THEN
        ASM_REWRITE_TAC[] THEN
        DISCH_THEN(MP_TAC o MATCH_MP string_prefix_le) THEN
        REWRITE_TAC[string_le_def] THEN
        ASM_MESON_TAC[string_lt_antisym; LT_REFL]];
      DISCH_THEN(SUBST1_TAC o SYM) THEN COND_CASES_TAC THEN REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (u:string) = LENGTH (v:string)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`implode u`; `implode v`; `EQUAL`; `0`; `LENGTH (v:string)`]
               compare_aux_spec) THEN
  ASM_REWRITE_TAC[strlen_def; ADD_CLAUSES; LE_REFL; explode_thm; DROP_0] THEN
  DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[TAKE_LENGTH_TOO_LONG; LE_REFL]);;

let mlstring_lt_inv_image = prove
 (`mlstring_lt = inv_image string_lt explode`,
  REWRITE_TAC[FUN_EQ_THM; inv_image_THM; mlstring_lt_def;
              PURE1AUX_compare_explode] THEN
  REPEAT GEN_TAC THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[distinctness "ordering"] THEN
  ASM_MESON_TAC[string_lt_nonrefl]);;

let TotOrd_compare = prove
 (`TotOrd mlstring_compare`,
  REWRITE_TAC[TotOrd; PURE1AUX_compare_explode] THEN REPEAT CONJ_TAC THEN
  REPEAT GEN_TAC THEN REPEAT COND_CASES_TAC THEN
  ASM_REWRITE_TAC[distinctness "ordering"; explode_11] THEN
  ASM_MESON_TAC[explode_11; string_lt_antisym; string_lt_cases;
                string_lt_trans; string_lt_nonrefl]);;

let good_cmp_compare = prove
 (`good_cmp mlstring_compare`,
  MATCH_MP_TAC TotOrder_imp_good_cmp THEN MATCH_ACCEPT_TAC TotOrd_compare);;

let mlstring_lt_antisym = prove
 (`!s t. ~(mlstring_lt s t /\ mlstring_lt t s)`,
  REWRITE_TAC[mlstring_lt_def] THEN
  MESON_TAC[TotOrd_compare; TotOrd; distinctness "ordering"]);;

let mlstring_lt_cases = prove
 (`!s t. (s = t) \/ mlstring_lt s t \/ mlstring_lt t s`,
  REWRITE_TAC[mlstring_lt_def] THEN
  MESON_TAC[TotOrd_compare; TotOrd; cases "ordering"]);;

let mlstring_lt_nonrefl = prove
 (`!s. ~(mlstring_lt s s)`,
  REWRITE_TAC[mlstring_lt_def] THEN
  MESON_TAC[TotOrd_compare; TotOrd; distinctness "ordering"]);;

let mlstring_lt_trans = prove
 (`!s1 s2 s3. mlstring_lt s1 s2 /\ mlstring_lt s2 s3 ==> mlstring_lt s1 s3`,
  REWRITE_TAC[mlstring_lt_def] THEN MESON_TAC[TotOrd_compare; TotOrd]);;

let mlstring_le_thm = prove
 (`!s1 s2. mlstring_le s1 s2 <=> (s1 = s2) \/ mlstring_lt s1 s2`,
  REWRITE_TAC[mlstring_le_def; mlstring_lt_def] THEN
  MESON_TAC[TotOrd_compare; TotOrd; distinctness "ordering"; cases "ordering"]);;

let mlstring_gt_thm = prove
 (`!s1 s2. mlstring_gt s1 s2 <=> mlstring_lt s2 s1`,
  REWRITE_TAC[mlstring_gt_def; mlstring_lt_def] THEN
  MESON_TAC[TotOrd_compare; TotOrd]);;

let mlstring_ge_thm = prove
 (`!s1 s2. mlstring_ge s1 s2 <=> mlstring_le s2 s1`,
  REWRITE_TAC[mlstring_ge_def; mlstring_le_def] THEN
  MESON_TAC[TotOrd_compare; TotOrd]);;

let transitive_mlstring_le = prove
 (`transitive mlstring_le`,
  REWRITE_TAC[transitive_DEF; mlstring_le_thm; mlstring_lt_inv_image;
              inv_image_THM] THEN
  MESON_TAC[string_lt_trans]);;

let antisymmetric_mlstring_le = prove
 (`antisymmetric mlstring_le`,
  REWRITE_TAC[antisymmetric_DEF; mlstring_le_thm; mlstring_lt_inv_image;
              inv_image_THM] THEN
  MESON_TAC[string_lt_antisym]);;

let char_lt_total = prove
 (`!(c1:char) c2. ~(char_lt c1 c2) /\ ~(char_lt c2 c1) ==> c1 = c2`,
  REWRITE_TAC[char_lt_def; CHAR_EQ_THM] THEN ARITH_TAC);;

let string_lt_total = prove
 (`!(s1:string) s2. ~(string_lt s1 s2) /\ ~(string_lt s2 s1) ==> s1 = s2`,
  MESON_TAC[string_lt_cases]);;

let total_mlstring_le = prove
 (`total mlstring_le`,
  REWRITE_TAC[total_DEF; mlstring_le_thm] THEN MESON_TAC[mlstring_lt_cases]);;

let transitive_mlstring_lt = prove
 (`transitive mlstring_lt`,
  REWRITE_TAC[mlstring_lt_inv_image] THEN MATCH_MP_TAC transitive_inv_image THEN
  REWRITE_TAC[transitive_DEF] THEN MESON_TAC[string_lt_trans]);;

let strlit_le_strlit = prove
 (`mlstring_le (implode s1) (implode s2) <=> string_le s1 s2`,
  REWRITE_TAC[mlstring_le_thm; string_le_def; mlstring_lt_inv_image;
              inv_image_THM; explode_thm; injectivity "mlstring"]);;

let irreflexive_mlstring_lt = prove
 (`irreflexive mlstring_lt`,
  REWRITE_TAC[irreflexive_DEF; mlstring_lt_nonrefl]);;

let trichotomous_mlstring_lt = prove
 (`trichotomous mlstring_lt`,
  REWRITE_TAC[trichotomous_DEF] THEN MESON_TAC[mlstring_lt_cases]);;

let StrongLinearOrder_mlstring_lt = prove
 (`StrongLinearOrder mlstring_lt`,
  REWRITE_TAC[StrongLinearOrder; StrongOrder; trichotomous_mlstring_lt;
              irreflexive_mlstring_lt; transitive_mlstring_lt]);;

let fast_lt_nonrefl = prove
 (`!s. ~fast_lt s s`,
  REWRITE_TAC[fast_lt_def; mlstring_lt_nonrefl]);;

let fast_lt_trans = prove
 (`!s1 s2 s3. fast_lt s1 s2 /\ fast_lt s2 s3 ==> fast_lt s1 s3`,
  REWRITE_TAC[fast_lt_def] THEN REPEAT GEN_TAC THEN
  ASM_CASES_TAC `strlen s1 = strlen s2` THEN
  ASM_CASES_TAC `strlen s2 = strlen s3` THEN ASM_REWRITE_TAC[] THENL
   [MESON_TAC[mlstring_lt_trans];
    ARITH_TAC;
    ARITH_TAC;
    ASM_CASES_TAC `strlen s1 = strlen s3` THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC]);;

let fast_le_thm = prove
 (`!s1 s2. fast_le s1 s2 <=> s1 = s2 \/ fast_lt s1 s2`,
  REWRITE_TAC[fast_le_def; fast_lt_def] THEN REPEAT GEN_TAC THEN
  ASM_CASES_TAC `strlen s1 = strlen s2` THEN
  ASM_REWRITE_TAC[mlstring_le_thm] THEN
  ASM_CASES_TAC `s1:mlstring = s2` THEN ASM_REWRITE_TAC[] THEN
  ASM_ARITH_TAC);;

let fast_gt_thm = prove
 (`!s1 s2. fast_gt s1 s2 <=> fast_lt s2 s1`,
  REWRITE_TAC[fast_gt_def; fast_lt_def; mlstring_gt_thm] THEN
  REPEAT GEN_TAC THEN ASM_CASES_TAC `strlen s1 = strlen s2` THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let fast_ge_thm = prove
 (`!s1 s2. fast_ge s1 s2 <=> fast_le s2 s1`,
  REWRITE_TAC[fast_ge_def; fast_le_def; mlstring_ge_thm] THEN
  REPEAT GEN_TAC THEN ASM_CASES_TAC `strlen s1 = strlen s2` THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let transitive_fast_le = prove
 (`transitive fast_le`,
  REWRITE_TAC[transitive_DEF; fast_le_thm] THEN MESON_TAC[fast_lt_trans]);;

let antisymmetric_fast_le = prove
 (`antisymmetric fast_le`,
  REWRITE_TAC[antisymmetric_DEF; fast_le_thm] THEN
  MESON_TAC[fast_lt_trans; fast_lt_nonrefl]);;

let total_fast_le = prove
 (`total fast_le`,
  REWRITE_TAC[total_DEF; fast_le_def] THEN REPEAT GEN_TAC THEN
  ASM_CASES_TAC `strlen x = strlen y` THEN ASM_REWRITE_TAC[] THENL
   [MP_TAC total_mlstring_le THEN REWRITE_TAC[total_DEF] THEN MESON_TAC[];
    ASM_ARITH_TAC]);;

let transitive_fast_lt = prove
 (`transitive fast_lt`,
  REWRITE_TAC[transitive_DEF] THEN MESON_TAC[fast_lt_trans]);;

let irreflexive_fast_lt = prove
 (`irreflexive fast_lt`,
  REWRITE_TAC[irreflexive_DEF; fast_lt_nonrefl]);;

let trichotomous_fast_lt = prove
 (`trichotomous fast_lt`,
  REWRITE_TAC[trichotomous_DEF; fast_lt_def] THEN REPEAT GEN_TAC THEN
  ASM_CASES_TAC `strlen a = strlen b` THEN ASM_REWRITE_TAC[] THENL
   [MESON_TAC[mlstring_lt_cases]; ASM_ARITH_TAC]);;

let StrongLinearOrder_fast_lt = prove
 (`StrongLinearOrder fast_lt`,
  REWRITE_TAC[StrongLinearOrder; StrongOrder; trichotomous_fast_lt;
              irreflexive_fast_lt; transitive_fast_lt]);;

(* HOL4: collate_aux, collate *)

let mlstring_collate_aux_def = cake_def
  `(mlstring_collate_aux (f:char->char->ordering) (s1:mlstring) s2 ord n 0 = ord) /\
   (mlstring_collate_aux f s1 s2 ord n (SUC len) =
      if f (strsub s1 n) (strsub s2 n) = EQUAL
      then mlstring_collate_aux f s1 s2 ord (n + 1) len
      else f (strsub s1 n) (strsub s2 n))`;;

let mlstring_collate_def = cake_def
  `mlstring_collate (f:char->char->ordering) s1 s2 =
     if strlen s1 < strlen s2
     then mlstring_collate_aux f s1 s2 LESS 0 (strlen s1)
     else if strlen s2 < strlen s1
     then mlstring_collate_aux f s1 s2 GREATER 0 (strlen s2)
     else mlstring_collate_aux f s1 s2 EQUAL 0 (strlen s2)`;;

let PURE1AUX_COLLATE_TAC =
  GEN_TAC THEN MATCH_MP_TAC mlstring_INDUCT THEN X_GEN_TAC `l1:string` THEN
  MATCH_MP_TAC mlstring_INDUCT THEN X_GEN_TAC `l2:string` THEN
  REWRITE_TAC[strlen_def; explode_thm] THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN INDUCT_TAC THEN
  REWRITE_TAC[mlstring_collate_aux_def; strsub_def; ADD_CLAUSES] THEN
  REPEAT STRIP_TAC THENL
   [ASM_CASES_TAC `n < LENGTH (l1:string)` THEN
    ASM_CASES_TAC `n < LENGTH (l2:string)` THEN
    ASM_SIMP_TAC[DROP_EL_CONS; DROP_LENGTH_TOO_LONG; GSYM NOT_LT;
                 mllist_collate_def] THEN
    ASM_ARITH_TAC;
    SUBGOAL_THEN `n < LENGTH (l1:string) /\ n < LENGTH (l2:string)`
      STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[DROP_EL_CONS; mllist_collate_def] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC];;

let mlstring_collate_aux_less_thm = prove
 (`!f s1 s2 n len.
     n + len = strlen s1 /\ strlen s1 < strlen s2 ==>
     mlstring_collate_aux f s1 s2 LESS n len =
     mllist_collate f (DROP n (explode s1)) (DROP n (explode s2))`,
  PURE1AUX_COLLATE_TAC);;

let mlstring_collate_aux_equal_thm = prove
 (`!f s1 s2 n len.
     n + len = strlen s2 /\ strlen s1 = strlen s2 ==>
     mlstring_collate_aux f s1 s2 EQUAL n len =
     mllist_collate f (DROP n (explode s1)) (DROP n (explode s2))`,
  PURE1AUX_COLLATE_TAC);;

let mlstring_collate_aux_greater_thm = prove
 (`!f s1 s2 n len.
     n + len = strlen s2 /\ strlen s2 < strlen s1 ==>
     mlstring_collate_aux f s1 s2 GREATER n len =
     mllist_collate f (DROP n (explode s1)) (DROP n (explode s2))`,
  PURE1AUX_COLLATE_TAC);;

let mlstring_collate_thm = prove
 (`!f s1 s2. mlstring_collate f s1 s2 = mllist_collate f (explode s1) (explode s2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mlstring_collate_def] THEN
  REPEAT COND_CASES_TAC THEN
  ASM_SIMP_TAC[mlstring_collate_aux_greater_thm; mlstring_collate_aux_equal_thm;
               mlstring_collate_aux_less_thm; ADD_CLAUSES; DROP_0] THEN
  MP_TAC(SPECL [`f:char->char->ordering`; `s1:mlstring`; `s2:mlstring`; `0`;
                `strlen s2`] mlstring_collate_aux_equal_thm) THEN
  REWRITE_TAC[DROP_0; ADD_CLAUSES] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_ARITH_TAC);;

(* HOL4 character literals are CHR n: the tab is CHR 9, the newline       *)
(* CHR 10, the backslash CHR 92 and the double quote CHR 34                *)

let char_escape_seq_def = cake_def
  `char_escape_seq c =
     if c = CHR 9 then SOME (implode "\\t")
     else if c = CHR 10 then SOME (implode "\\n")
     else if c = CHR 92 then SOME (implode "\\\\")
     else if c = CHR 34 then SOME (implode "\\\"")
     else NONE`;;

let char_escaped_def = cake_def
  `char_escaped c =
     match char_escape_seq c with
       NONE -> [c]
     | SOME s -> explode s`;;

let escape_str_def = cake_def
  `escape_str s =
     implode (APPEND (APPEND "\"" (FLAT (MAP char_escaped (explode s)))) "\"")`;;

let escape_char_def = cake_def
  `escape_char c = implode (APPEND (APPEND "#\"" (char_escaped c)) "\"")`;;

let ALL_DISTINCT_MAP_implode = prove
 (`ALL_DISTINCT ls ==> ALL_DISTINCT (MAP implode ls)`,
  DISCH_TAC THEN MATCH_MP_TAC ALL_DISTINCT_MAP_INJ THEN
  ASM_REWRITE_TAC[injectivity "mlstring"] THEN MESON_TAC[]);;
let _ = cake_add_simps [ALL_DISTINCT_MAP_implode];;

let ALL_DISTINCT_MAP_explode = prove
 (`!ls. ALL_DISTINCT (MAP explode ls) <=> ALL_DISTINCT ls`,
  GEN_TAC THEN EQ_TAC THENL [MATCH_ACCEPT_TAC ALL_DISTINCT_MAP; ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC ALL_DISTINCT_MAP_INJ THEN
  ASM_REWRITE_TAC[explode_11] THEN MESON_TAC[]);;
let _ = cake_add_simps [ALL_DISTINCT_MAP_explode];;

(* optimising mlstring app_list *)

let app_list_ann_INDUCT,app_list_ann_RECURSION = cake_type
  "app_list_ann = BigList (A list) | BigAppend app_list_ann app_list_ann | Small (A app_list)";;

let sum_sizes_def = cake_def
  `(sum_sizes [] k = k) /\
   (sum_sizes (CONS l ls) k = sum_sizes ls (strlen l + k))`;;

(* HOL4: Overload size_limit[local] = 2048:num (written 2048 here) *)

let make_app_list_ann_def = cake_def
  `make_app_list_ann (input:mlstring app_list) =
     match input with
       Nil -> (Small input, 0)
     | misc_Append l1 l2 ->
         (match make_app_list_ann l1 with (x1,n1) ->
          match make_app_list_ann l2 with (x2,n2) ->
          let n = n1 + n2 in
          if n < 2048 then (Small input, n) else (BigAppend x1 x2, n))
     | misc_List ls ->
         (let n = sum_sizes ls 0 in
          if n < 2048 then (Small input, n) else (BigList ls, n))`;;

let shrink_def = cake_def
  `(shrink (Small t) = misc_List [mlstring_concat (append t)]) /\
   (shrink (BigList ls) = misc_List ls) /\
   (shrink (BigAppend l1 l2) = misc_Append (shrink l1) (shrink l2))`;;

let str_app_list_opt_def = cake_def
  `str_app_list_opt l = match make_app_list_ann l with (t,n) -> shrink t`;;

let str_app_list_opt_test = prove
 (`str_app_list_opt (misc_Append (misc_List [implode "Hello"; implode " there"])
                                 (misc_List [implode "!"])) =
   misc_List [implode "Hello there!"]`,
  REWRITE_TAC[str_app_list_opt_def] THEN
  ONCE_REWRITE_TAC[make_app_list_ann_def] THEN
  REWRITE_TAC[case_def "app_list"] THEN
  ONCE_REWRITE_TAC[make_app_list_ann_def] THEN
  REWRITE_TAC[case_def "app_list"; sum_sizes_def; strlen_def; LENGTH;
              LET_DEF; LET_END_DEF] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[pair_CASE] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[pair_CASE; shrink_def; append_thm; concat_thm; MAP; FLAT;
              explode_thm; APPEND; injectivity "app_list"; CONS_11;
              injectivity "mlstring"]);;

let str_app_list_opt_thm = prove
 (`mlstring_concat (append (str_app_list_opt l)) = mlstring_concat (append l)`,
  SUBGOAL_THEN `str_app_list_opt l = shrink (FST (make_app_list_ann l))`
    SUBST1_TAC THENL
   [REWRITE_TAC[str_app_list_opt_def] THEN
    MP_TAC(ISPEC `make_app_list_ann l` PAIR_SURJECTIVE) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[pair_CASE; FST];
    ALL_TAC] THEN
  SPEC_TAC(`l:mlstring app_list`,`l:mlstring app_list`) THEN
  MATCH_MP_TAC app_list_INDUCT THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[make_app_list_ann_def] THEN
  REWRITE_TAC[case_def "app_list"; LET_DEF; LET_END_DEF] THENL
   [COND_CASES_TAC THEN
    REWRITE_TAC[FST; shrink_def; append_thm; concat_cons; concat_nil; strcat_nil];
    MP_TAC(ISPEC `make_app_list_ann a0` PAIR_SURJECTIVE) THEN
    MP_TAC(ISPEC `make_app_list_ann a1` PAIR_SURJECTIVE) THEN
    REPEAT STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_pair o rand o concl))) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[FST]) THEN REWRITE_TAC[pair_CASE] THEN
    COND_CASES_TAC THEN
    ASM_REWRITE_TAC[FST; shrink_def; append_thm; concat_cons; concat_nil;
                    strcat_nil; concat_append];
    REWRITE_TAC[FST; shrink_def; append_thm; concat_cons; concat_nil;
                strcat_nil]]);;

let concat_sing = prove
 (`mlstring_concat [x] = x`,
  REWRITE_TAC[concat_cons; concat_nil; strcat_nil]);;
let _ = cake_add_simps [concat_sing];;

let char_to_word8_def = cake_def
  `char_to_word8 (c:char) = word (ORD c):byte`;;
let _ = cake_add_simps [char_to_word8_def];;

let word8_to_char_def = cake_def
  `word8_to_char (w:byte) = CHR (val w):char`;;
let _ = cake_add_simps [word8_to_char_def];;

(* The translator turns each empty_ffi s into a call to the FFI with an   *)
(* empty name and passing s as the argument.  The empty FFI is used for  *)
(* logging/timing purposes.  HOL4 () is one.                              *)

let empty_ffi_def = cake_def
  `empty_ffi (s:mlstring) = one`;;
