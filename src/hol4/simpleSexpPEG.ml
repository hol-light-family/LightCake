(* ========================================================================= *)
(* simpleSexpPEG: port of HOL4 examples/formal-languages/context-free/      *)
(* simpleSexpPEGScript.sml (HOL4 library used by CakeML v3479).             *)
(* A parsing expression grammar for the s-expressions of simpleSexp.        *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - tokeq, pnt, sumID, choicel and pegf are simpleSexpPEG_tokeq, ...        *)
(*   (cmlPEG defines its own), with their definitions; the theorems peg0_*  *)
(*   and peg_eval_choicel_NIL about them (names of cmlPEG and pegSound) get  *)
(*   the same prefix.  HOL4's overload mkNT is INL; the record literal of    *)
(*   sexpPEG is peg_REC (fields start, anyEOF, tokFALSE, tokEOF, notFAIL,    *)
(*   rules); ~> and <~ are ignoreL and ignoreR; FOLDR f e is                 *)
(*   \l. ITLIST f l e; ++ is APPEND; the list form of SX_CONS is written out *)
(*   (nil is SX_SYM "nil"); character literals #"(" are CHR 40.             *)
(* - Only the definitions (used by simpleSexpParse's parse_sexp) and a few  *)
(*   simple theorems are ported; the well-formedness theorem wfG_sexpPEG and *)
(*   the theorems for evaluation (sexpPEG_exec_thm, ...) are not (not used  *)
(*   by CakeML).                                                             *)
(* ========================================================================= *)

needs "hol4/vocab.ml";;
needs "hol4/finite_map.ml";;
needs "hol4/peg.ml";;
needs "hol4/simpleSexp.ml";;

type_invention_error := true;;

(* HOL4: tokeq_def *)

let simpleSexpPEG_tokeq_def = new_definition
  `simpleSexpPEG_tokeq (t:char) =
     (tok ((=) t) (K (SX_SYM [t])):(char,B,simpleSexp_sexp,E)pegsym)`;;

let grabWS_def = new_definition
  `grabWS (s:(char,B,simpleSexp_sexp,E)pegsym) =
     ignoreL (rpt (tok isSpace (K arb_sexp)) (K arb_sexp)) s`;;

let simpleSexpPEG_peg0_tokeq = prove
 (`!(G:(char,B,simpleSexp_sexp,E)peg) t. peg0 G (simpleSexpPEG_tokeq t) <=> F`,
  REWRITE_TAC[simpleSexpPEG_tokeq_def; peg0_tok]);;

(* HOL4: pnt_def *)

let simpleSexpPEG_pnt_def = new_definition
  `simpleSexpPEG_pnt (ntsym:sexpNT) = (nt (INL ntsym) I:(A,sexpNT,C,E)pegsym)`;;

let replace_nil_def = cake_def
  `(replace_nil (SX_SYM s) z = if s = "nil" then z else SX_SYM s) /\
   (replace_nil (SX_CONS x y) z = SX_CONS x (replace_nil y z)) /\
   (replace_nil x y = x)`;;

(* HOL4: sumID_def *)

let simpleSexpPEG_sumID_def = new_recursive_definition sum_RECURSION
  `(!x:A. simpleSexpPEG_sumID (INL x) = x) /\
   (!y:A. simpleSexpPEG_sumID (INR y) = y)`;;

(* HOL4: choicel_def *)

let simpleSexpPEG_choicel_def = new_recursive_definition list_RECURSION
  `(simpleSexpPEG_choicel [] =
      (not (empty arb_sexp) arb_sexp:(A,B,simpleSexp_sexp,E)pegsym)) /\
   (!h t. simpleSexpPEG_choicel (CONS h t) =
          choice h (simpleSexpPEG_choicel t) simpleSexpPEG_sumID)`;;

(* HOL4: pegf_def *)

let simpleSexpPEG_pegf_def = new_definition
  `simpleSexpPEG_pegf (sym:(A,B,simpleSexp_sexp,E)pegsym) f =
     seq sym (empty arb_sexp) (\l1 l2. f l1)`;;

(* HOL4: peg_eval_choicel_NIL *)

let simpleSexpPEG_peg_eval_choicel_NIL = prove
 (`!(G:(A,B,simpleSexp_sexp,E)peg) i0 x.
     peg_eval G (i0, simpleSexpPEG_choicel []) x <=>
     x = Failure (sloc i0) (peg_notFAIL G)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[simpleSexpPEG_choicel_def] THEN
  GEN_REWRITE_TAC LAND_CONV [peg_eval_cases] THEN
  REWRITE_TAC[PAIR_EQ; pegsym_distinct; pegsym_inject; peg_eval_empty] THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM; LEFT_EXISTS_AND_THM; UNWIND_THM1;
              UNWIND_THM2; GSYM CONJ_ASSOC] THEN
  REWRITE_TAC[peg_eval_empty; UNWIND_THM1; UNWIND_THM2; isSuccess_def;
              isFailure_def] THEN
  MESON_TAC[]);;

(* HOL4: peg0_choicel *)

let simpleSexpPEG_peg0_choicel = prove
 (`!(G:(A,B,simpleSexp_sexp,E)peg) h t.
     (peg0 G (simpleSexpPEG_choicel []) <=> F) /\
     (peg0 G (simpleSexpPEG_choicel (CONS h t)) <=>
      peg0 G h \/ pegfail G h /\ peg0 G (simpleSexpPEG_choicel t))`,
  REWRITE_TAC[simpleSexpPEG_choicel_def; peg0_not; peg0_choice; pegfail_empty]);;

(* HOL4: peg0_pegf *)

let simpleSexpPEG_peg0_pegf = prove
 (`!(G:(A,B,simpleSexp_sexp,E)peg) s f.
     peg0 G (simpleSexpPEG_pegf s f) <=> peg0 G s`,
  REWRITE_TAC[simpleSexpPEG_pegf_def; peg0_seq; peg0_empty]);;

(* ------------------------------------------------------------------------- *)
(* The grammar.                                                              *)
(* ------------------------------------------------------------------------- *)

let sexpPEG_def = new_definition
 `sexpPEG:(char,sexpNT,simpleSexp_sexp,(char)list)peg =
  peg_REC (simpleSexpPEG_pnt sxnt_sexp)
    "Unexpected EOF (any)"
    "Failed to see expected token"
    "Failed to see expected token because of EOF"
    "Failed to fail in a not rule"
    (FEMPTY |++
     [(INL sxnt_sexp,
       ignoreR (simpleSexpPEG_pnt sxnt_WSsexp)
         (seq (rpt (tok isSpace (K arb_sexp)) (K arb_sexp))
              (not (any (K arb_sexp)) arb_sexp)
              (K (K arb_sexp))));
      (INL sxnt_sexp0,
       simpleSexpPEG_choicel
        [simpleSexpPEG_pnt sxnt_sexpnum;
         ignoreL (simpleSexpPEG_tokeq (CHR 40)) (simpleSexpPEG_pnt sxnt_sexpseq);
         ignoreR
           (ignoreL (simpleSexpPEG_tokeq (CHR 34))
                    (simpleSexpPEG_pnt sxnt_strcontents))
           (choice (simpleSexpPEG_tokeq (CHR 34)) (error "Expected \"")
                   simpleSexpPEG_sumID);
         simpleSexpPEG_pegf
           (ignoreL (simpleSexpPEG_tokeq (CHR 39))
                    (grabWS (simpleSexpPEG_pnt sxnt_sexp0)))
           (\s. SX_CONS (SX_SYM "quote") (SX_CONS s (SX_SYM "nil")));
         simpleSexpPEG_pnt sxnt_sexpsym]);
      (INL sxnt_sexpseq,
       simpleSexpPEG_choicel
        [simpleSexpPEG_pegf (grabWS (simpleSexpPEG_tokeq (CHR 41)))
                            (K (SX_SYM "nil"));
         seq (grabWS (simpleSexpPEG_pnt sxnt_sexp0))
             (seq
               (rpt (grabWS (simpleSexpPEG_pnt sxnt_sexp0))
                    (\l. ITLIST SX_CONS l (SX_SYM "nil")))
               (simpleSexpPEG_choicel
                 [simpleSexpPEG_pegf (grabWS (simpleSexpPEG_tokeq (CHR 41)))
                                     (K (SX_SYM "nil"));
                  ignoreR
                    (ignoreL (grabWS (simpleSexpPEG_tokeq (CHR 46)))
                             (grabWS (simpleSexpPEG_pnt sxnt_sexp0)))
                    (grabWS (simpleSexpPEG_tokeq (CHR 41)))])
               replace_nil)
             SX_CONS]);
      (INL sxnt_WSsexp,
       ignoreL (rpt (tok isSpace (K arb_sexp)) (K arb_sexp))
               (simpleSexpPEG_pnt sxnt_sexp0));
      (INL sxnt_sexpnum,
       seq (simpleSexpPEG_pnt sxnt_digit)
           (rpt (simpleSexpPEG_pnt sxnt_digit)
                (UNCURRY SX_CONS o (SX_NUM ## SX_NUM) o
                 FOLDL (\(l,n) d. (10 * l, 10 * n + destSXNUM d)) (1,0)))
           (\s1. (\(l,n). SX_NUM (destSXNUM s1 * l + n)) o
                 (destSXNUM ## destSXNUM) o destSXCONS));
      (INL sxnt_digit,
       tok isDigit (\(c,l). SX_NUM (ORD c - ORD (CHR 48))));
      (INL sxnt_sexpsym,
       seq (tok valid_first_symchar (\(c,l). SX_SYM [c]))
           (rpt (tok valid_symchar (\(c,l). SX_SYM [c]))
                (SX_SYM o (\l. ITLIST (\s a. APPEND (destSXSYM s) a) l [])))
           (\s1 s2. SX_SYM (APPEND (destSXSYM s1) (destSXSYM s2))));
      (INL sxnt_strcontents,
       rpt (simpleSexpPEG_pnt sxnt_strchar)
           (SX_STR o (\l. ITLIST (\s a. APPEND (destSXSYM s) a) l [])));
      (INL sxnt_strchar,
       simpleSexpPEG_choicel
        [ignoreL (simpleSexpPEG_tokeq (CHR 92))
                 (simpleSexpPEG_pnt sxnt_escapedstrchar);
         simpleSexpPEG_pnt sxnt_normstrchar]);
      (INL sxnt_escapedstrchar,
       simpleSexpPEG_choicel
        [simpleSexpPEG_tokeq (CHR 92); simpleSexpPEG_tokeq (CHR 34);
         error "Illegal string-escape"]);
      (INL sxnt_normstrchar,
       tok (\c. isPrint c /\ ~(c = CHR 34) /\ ~(c = CHR 92))
           (\(c,l). SX_SYM [c]))])`;;

let sexpPEG_start = prove
 (`peg_start sexpPEG = simpleSexpPEG_pnt sxnt_sexp`,
  REWRITE_TAC[sexpPEG_def; (record_info "peg").ri_accessors]);;

let sexpPEG_notFAIL = prove
 (`peg_notFAIL sexpPEG = "Failed to fail in a not rule"`,
  REWRITE_TAC[sexpPEG_def; (record_info "peg").ri_accessors]);;

(* ------------------------------------------------------------------------- *)
(* HOL4 [simp] theorems.                                                     *)
(* ------------------------------------------------------------------------- *)

let _ = cake_add_simps
  [simpleSexpPEG_peg0_tokeq; simpleSexpPEG_sumID_def;
   simpleSexpPEG_peg_eval_choicel_NIL; simpleSexpPEG_peg0_choicel;
   simpleSexpPEG_peg0_pegf; sexpPEG_start; sexpPEG_notFAIL];;
