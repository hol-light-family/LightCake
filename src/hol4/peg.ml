(* ========================================================================= *)
(* peg: port of HOL4 examples/formal-languages/context-free/pegScript.sml   *)
(* (HOL4 library used by CakeML v3479).                                      *)
(* Parsing expression grammars: syntax, the evaluation relation, well-      *)
(* formedness and totality of evaluation (based on Koprowski and Binsztok,   *)
(* TRX: A Formally Verified Parser Interpreter, LMCS 7(2:18), 2011).         *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - The record fields G.start, G.rules, G.anyEOF, G.tokFALSE, G.tokEOF,     *)
(*   G.notFAIL are peg_start G, peg_rules G, ...; f ' x is FAPPLY f x;      *)
(*   HOL4's local overload EOF is Locs EOFpt EOFpt.                          *)
(* - peg_eval and peg_eval_list are one mutual inductive definition; the     *)
(*   rule theorems have the HOL4 names (peg_eval_nt, ..., peg_eval_list_cons) *)
(*   except the two that HOL4 rebinds to iff theorems (peg_eval_empty,       *)
(*   peg_eval_rpt), which are LPARSEAUX_peg_eval_empty_rule and              *)
(*   LPARSEAUX_peg_eval_rpt_rule.  peg_eval_strongind' is HOL4's curried     *)
(*   strong induction.  peg0_cases lists peg0, peggt0, pegfail in HOL4's     *)
(*   order; peg0_ind keeps the order HOL Light's package gives.              *)
(* - Renamed: the pegresult constructor Success is peg_Success (ffi keeps    *)
(*   Success for its outcome type); theorem names keep HOL4's spelling       *)
(*   (resultmap_EQ_Success, UNCURRY_Failure_EQ_Success, ...).  Gexprs_def    *)
(*   and Gexprs_subexprs are peg_Gexprs_def and                              *)
(*   peg_Gexprs_subexprs (OCaml reads Gexprs_def as a constructor);          *)
(*   IS_PREFIX_MEM is peg_IS_PREFIX_MEM (a rich_list name).  The derived     *)
(*   forms pegf and choicel are peg_pegf and peg_choicel (cmlPEG defines     *)
(*   its own pegf and choicel), with their theorems peg_peg0_pegf,           *)
(*   peg_peg0_choicel, peg_peg_eval_choicel_NIL, peg_peg_eval_choicel_CONS.  *)
(*   ignoreL and ignoreR are prefix constants (HOL4 infixes ~> and <~).      *)
(* - Lemmas named LPARSEAUX_... are helpers of this unit (not HOL4 names).   *)
(* ========================================================================= *)

needs "hol4/vocab.ml";;
needs "hol4/finite_map.ml";;
needs "hol4/location.ml";;
needs "hol4/grammar.ml";;

(* ------------------------------------------------------------------------- *)
(* Syntax: expressions, grammars, results.                                   *)
(* ------------------------------------------------------------------------- *)

let pegsym_INDUCT,pegsym_RECURSION = cake_type
  "pegsym = empty C
          | any (A # locs -> C)
          | tok (A -> bool) (A # locs -> C)
          | nt (B + num) (C -> C)
          | seq pegsym pegsym (C -> C -> C)
          | choice pegsym pegsym (C + C -> C)
          | rpt pegsym (C list -> C)
          | not pegsym C
          | error E";;

let pegsym_distinct = distinctness "pegsym";;
let pegsym_inject = injectivity "pegsym";;
let pegsym_CASE = case_def "pegsym";;
let pegsym_case_eq = case_eq "pegsym";;
let pegsym_nchotomy = cases "pegsym";;

let peg_FIELDS = cake_record "peg"
  ["start","(A,B,C,E)pegsym"; "anyEOF","E"; "tokFALSE","E"; "tokEOF","E";
   "notFAIL","E"; "rules","(B + num,(A,B,C,E)pegsym)fmap"];;

let pegresult_INDUCT,pegresult_RECURSION = cake_type
  "pegresult = peg_Success A C ((locs # E) option) | Failure locs E";;

let pegresult_distinct = distinctness "pegresult";;
let pegresult_inject = injectivity "pegresult";;
let pegresult_CASE = case_def "pegresult";;
let pegresult_case_eq = case_eq "pegresult";;
let pegresult_nchotomy = cases "pegresult";;

let isSuccess_def = cake_def
  `(isSuccess (peg_Success (a:A) (c:C) (eo:(locs#E)option)) <=> T) /\
   (isSuccess (Failure (l:locs) (e:E):(A,C,E)pegresult) <=> F)`;;
let isFailure_def = cake_def
  `(isFailure (peg_Success (a:A) (c:C) (eo:(locs#E)option)) <=> F) /\
   (isFailure (Failure (l:locs) (e:E):(A,C,E)pegresult) <=> T)`;;
let resultmap_def = cake_def
  `(resultmap (f:C->D) (peg_Success (a:A) c (eo:(locs#E)option)) =
      peg_Success a (f c) eo) /\
   (resultmap f (Failure fl fe:(A,C,E)pegresult) = Failure fl fe)`;;

let resultmap_EQ_Success = prove
 (`!(f:C->D) (r:(A,C,E)pegresult) a x eo.
     resultmap f r = peg_Success a x eo <=> ?x0. r = peg_Success a x0 eo /\ x = f x0`,
  GEN_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `r:(A,C,E)pegresult` pegresult_nchotomy) THEN
  REWRITE_TAC[resultmap_def; pegresult_distinct; pegresult_inject] THEN
  MESON_TAC[]);;

let resultmap_EQ_Failure = prove
 (`!(f:C->D) (r:(A,C,E)pegresult) fl fe.
     (resultmap f r = Failure fl fe <=> r = Failure fl fe) /\
     (Failure fl fe = resultmap f r <=> r = Failure fl fe)`,
  GEN_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `r:(A,C,E)pegresult` pegresult_nchotomy) THEN
  REWRITE_TAC[resultmap_def; pegresult_distinct; pegresult_inject] THEN
  MESON_TAC[]);;

let resultmap_I = prove
 (`!r:(A,C,E)pegresult. resultmap I r = r`,
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `r:(A,C,E)pegresult` pegresult_nchotomy) THEN
  REWRITE_TAC[resultmap_def; I_THM]);;

let MAXerr_def = cake_def
  `MAXerr (fl1,(fe1:E)) (fl2,fe2) =
     if locsle fl1 fl2 then (fl2,fe2) else (fl1,fe1)`;;
let optmax_def = cake_def
  `(optmax (f:A->A->A) NONE NONE = NONE) /\
   (optmax f NONE (SOME x) = SOME x) /\
   (optmax f (SOME x) NONE = SOME x) /\
   (optmax f (SOME x) (SOME y) = SOME (f x y))`;;

let sloc_def = cake_def
  `(sloc ([]:(A#locs)list) = Locs EOFpt EOFpt) /\
   (sloc (CONS (h:A#locs) t) = SND h)`;;

let sloc_thm = prove
 (`sloc ([]:(A#locs)list) = Locs EOFpt EOFpt /\
   (!(c:A) l t. sloc (CONS (c,l) t) = l)`,
  REWRITE_TAC[sloc_def]);;

(* ------------------------------------------------------------------------- *)
(* The evaluation relation.                                                  *)
(* ------------------------------------------------------------------------- *)

let peg_eval_rules,peg_eval_ind,peg_eval_cases = new_inductive_definition
 `(!s c. peg_eval (G:(A,B,C,E)peg) (s, empty c) (peg_Success s c NONE)) /\
  (!n s f res.
     n IN FDOM (peg_rules G) /\ peg_eval G (s, FAPPLY (peg_rules G) n) res
     ==> peg_eval G (s, nt n f) (resultmap f res)) /\
  (!h t f. peg_eval G (CONS h t, any f) (peg_Success t (f h) NONE)) /\
  (!f. peg_eval G ([], any f) (Failure (Locs EOFpt EOFpt) (peg_anyEOF G))) /\
  (!e t P f.
     P (FST e) ==> peg_eval G (CONS e t, tok P f) (peg_Success t (f e) NONE)) /\
  (!h t P f.
     ~P (FST h)
     ==> peg_eval G (CONS h t, tok P f) (Failure (SND h) (peg_tokFALSE G))) /\
  (!P f.
     peg_eval G ([], tok P f) (Failure (Locs EOFpt EOFpt) (peg_tokEOF G))) /\
  (!e s c fr.
     peg_eval G (s, e) fr /\ isFailure fr
     ==> peg_eval G (s, not e c) (peg_Success s c NONE)) /\
  (!e s r c.
     peg_eval G (s, e) r /\ isSuccess r
     ==> peg_eval G (s, not e c) (Failure (sloc s) (peg_notFAIL G))) /\
  (!e1 e2 s f fl fe.
     peg_eval G (s, e1) (Failure fl fe)
     ==> peg_eval G (s, seq e1 e2 f) (Failure fl fe)) /\
  (!e1 e2 f s0 eo s1 c1 fl fe.
     peg_eval G (s0, e1) (peg_Success s1 c1 eo) /\
     peg_eval G (s1, e2) (Failure fl fe)
     ==> peg_eval G (s0, seq e1 e2 f) (Failure fl fe)) /\
  (!e1 e2 s0 s1 s2 c1 c2 f eo1 eo2.
     peg_eval G (s0, e1) (peg_Success s1 c1 eo1) /\
     peg_eval G (s1, e2) (peg_Success s2 c2 eo2)
     ==> peg_eval G (s0, seq e1 e2 f) (peg_Success s2 (f c1 c2) eo2)) /\
  (!e1 e2 s f fl1 fe1 fl2 fe2.
     peg_eval G (s, e1) (Failure fl1 fe1) /\
     peg_eval G (s, e2) (Failure fl2 fe2)
     ==> peg_eval G (s, choice e1 e2 f)
                  (UNCURRY Failure (MAXerr (fl1,fe1) (fl2,fe2)))) /\
  (!e1 e2 s0 f s r eo.
     peg_eval G (s0, e1) (peg_Success s r eo)
     ==> peg_eval G (s0, choice e1 e2 f) (peg_Success s (f (INL r)) eo)) /\
  (!e1 e2 s0 s r eo f fl fe.
     peg_eval G (s0, e1) (Failure fl fe) /\
     peg_eval G (s0, e2) (peg_Success s r eo)
     ==> peg_eval G (s0, choice e1 e2 f)
                  (peg_Success s (f (INR r)) (optmax MAXerr (SOME (fl,fe)) eo))) /\
  (!e s. peg_eval G (s, error e) (Failure (sloc s) e)) /\
  (!e f s s1 list err.
     peg_eval_list G (s, e) (s1,list,err)
     ==> peg_eval G (s, rpt e f) (peg_Success s1 (f list) (SOME err))) /\
  (!e s fl fe.
     peg_eval G (s, e) (Failure fl fe)
     ==> peg_eval_list G (s, e) (s,[],(fl,fe))) /\
  (!e eo0 eo s0 s1 s2 c cs.
     peg_eval G (s0, e) (peg_Success s1 c eo0) /\
     peg_eval_list G (s1, e) (s2,cs,eo)
     ==> peg_eval_list G (s0, e) (s2,CONS c cs,eo))`;;

let LPARSEAUX_peg_eval_rules_list =
  map (GEN `G:(A,B,C,E)peg`) (CONJUNCTS (SPEC `G:(A,B,C,E)peg` peg_eval_rules));;

let LPARSEAUX_peg_eval_empty_rule = el 0 LPARSEAUX_peg_eval_rules_list;;
let peg_eval_nt = el 1 LPARSEAUX_peg_eval_rules_list;;
let peg_eval_any_success = el 2 LPARSEAUX_peg_eval_rules_list;;
let peg_eval_any_failure = el 3 LPARSEAUX_peg_eval_rules_list;;
let peg_eval_tok_success = el 4 LPARSEAUX_peg_eval_rules_list;;
let peg_eval_tok_failureF = el 5 LPARSEAUX_peg_eval_rules_list;;
let peg_eval_tok_failureEOF = el 6 LPARSEAUX_peg_eval_rules_list;;
let peg_eval_not_success = el 7 LPARSEAUX_peg_eval_rules_list;;
let peg_eval_not_failure = el 8 LPARSEAUX_peg_eval_rules_list;;
let peg_eval_seq_fail1 = el 9 LPARSEAUX_peg_eval_rules_list;;
let peg_eval_seq_fail2 = el 10 LPARSEAUX_peg_eval_rules_list;;
let peg_eval_seq_success = el 11 LPARSEAUX_peg_eval_rules_list;;
let peg_eval_choice_fail = el 12 LPARSEAUX_peg_eval_rules_list;;
let peg_eval_choice_success1 = el 13 LPARSEAUX_peg_eval_rules_list;;
let peg_eval_choice_success2 = el 14 LPARSEAUX_peg_eval_rules_list;;
let peg_eval_error = el 15 LPARSEAUX_peg_eval_rules_list;;
let LPARSEAUX_peg_eval_rpt_rule = el 16 LPARSEAUX_peg_eval_rules_list;;
let peg_eval_list_nil = el 17 LPARSEAUX_peg_eval_rules_list;;
let peg_eval_list_cons = el 18 LPARSEAUX_peg_eval_rules_list;;

let peg_eval_strongind = derive_strong_induction(peg_eval_rules,peg_eval_ind);;

let peg_eval_strongind' = prove
 (`!(G:(A,B,C,E)peg)
    (P1:(A#locs)list->(A,B,C,E)pegsym->((A#locs)list,C,E)pegresult->bool)
    (P2:(A#locs)list->(A,B,C,E)pegsym->(A#locs)list->C list->locs#E->bool).
     (!s c. P1 s (empty c) (peg_Success s c NONE)) /\
     (!n s f res.
        n IN FDOM (peg_rules G) /\ peg_eval G (s, FAPPLY (peg_rules G) n) res /\
        P1 s (FAPPLY (peg_rules G) n) res
        ==> P1 s (nt n f) (resultmap f res)) /\
     (!h t f. P1 (CONS h t) (any f) (peg_Success t (f h) NONE)) /\
     (!f. P1 [] (any f) (Failure (Locs EOFpt EOFpt) (peg_anyEOF G))) /\
     (!e t P f. P (FST e) ==> P1 (CONS e t) (tok P f) (peg_Success t (f e) NONE)) /\
     (!h t P f.
        ~P (FST h)
        ==> P1 (CONS h t) (tok P f) (Failure (SND h) (peg_tokFALSE G))) /\
     (!P f. P1 [] (tok P f) (Failure (Locs EOFpt EOFpt) (peg_tokEOF G))) /\
     (!e s c fr.
        peg_eval G (s, e) fr /\ P1 s e fr /\ isFailure fr
        ==> P1 s (not e c) (peg_Success s c NONE)) /\
     (!e s r c.
        peg_eval G (s, e) r /\ P1 s e r /\ isSuccess r
        ==> P1 s (not e c) (Failure (sloc s) (peg_notFAIL G))) /\
     (!e1 e2 s f fl fe.
        peg_eval G (s, e1) (Failure fl fe) /\ P1 s e1 (Failure fl fe)
        ==> P1 s (seq e1 e2 f) (Failure fl fe)) /\
     (!e1 e2 f s0 eo s1 c1 fl fe.
        peg_eval G (s0, e1) (peg_Success s1 c1 eo) /\ P1 s0 e1 (peg_Success s1 c1 eo) /\
        peg_eval G (s1, e2) (Failure fl fe) /\ P1 s1 e2 (Failure fl fe)
        ==> P1 s0 (seq e1 e2 f) (Failure fl fe)) /\
     (!e1 e2 s0 s1 s2 c1 c2 f eo1 eo2.
        peg_eval G (s0, e1) (peg_Success s1 c1 eo1) /\
        P1 s0 e1 (peg_Success s1 c1 eo1) /\
        peg_eval G (s1, e2) (peg_Success s2 c2 eo2) /\
        P1 s1 e2 (peg_Success s2 c2 eo2)
        ==> P1 s0 (seq e1 e2 f) (peg_Success s2 (f c1 c2) eo2)) /\
     (!e1 e2 s f fl1 fe1 fl2 fe2.
        peg_eval G (s, e1) (Failure fl1 fe1) /\ P1 s e1 (Failure fl1 fe1) /\
        peg_eval G (s, e2) (Failure fl2 fe2) /\ P1 s e2 (Failure fl2 fe2)
        ==> P1 s (choice e1 e2 f)
               (UNCURRY Failure (MAXerr (fl1,fe1) (fl2,fe2)))) /\
     (!e1 e2 s0 f s r eo.
        peg_eval G (s0, e1) (peg_Success s r eo) /\ P1 s0 e1 (peg_Success s r eo)
        ==> P1 s0 (choice e1 e2 f) (peg_Success s (f (INL r)) eo)) /\
     (!e1 e2 s0 s r eo f fl fe.
        peg_eval G (s0, e1) (Failure fl fe) /\ P1 s0 e1 (Failure fl fe) /\
        peg_eval G (s0, e2) (peg_Success s r eo) /\ P1 s0 e2 (peg_Success s r eo)
        ==> P1 s0 (choice e1 e2 f)
               (peg_Success s (f (INR r)) (optmax MAXerr (SOME (fl,fe)) eo))) /\
     (!e s. P1 s (error e) (Failure (sloc s) e)) /\
     (!e f s s1 list err.
        peg_eval_list G (s, e) (s1,list,err) /\ P2 s e s1 list err
        ==> P1 s (rpt e f) (peg_Success s1 (f list) (SOME err))) /\
     (!e s fl fe.
        peg_eval G (s, e) (Failure fl fe) /\ P1 s e (Failure fl fe)
        ==> P2 s e s [] (fl,fe)) /\
     (!e eo0 eo s0 s1 s2 c cs.
        peg_eval G (s0, e) (peg_Success s1 c eo0) /\ P1 s0 e (peg_Success s1 c eo0) /\
        peg_eval_list G (s1, e) (s2,cs,eo) /\ P2 s1 e s2 cs eo
        ==> P2 s0 e s2 (CONS c cs) eo)
     ==> (!s0 e sr. peg_eval G (s0,e) sr ==> P1 s0 e sr) /\
         (!s0 e s rl err. peg_eval_list G (s0,e) (s,rl,err) ==> P2 s0 e s rl err)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`G:(A,B,C,E)peg`;
    `\x:(A#locs)list#(A,B,C,E)pegsym. \r:((A#locs)list,C,E)pegresult.
       (P1:(A#locs)list->(A,B,C,E)pegsym->((A#locs)list,C,E)pegresult->bool)
         (FST x) (SND x) r`;
    `\x:(A#locs)list#(A,B,C,E)pegsym. \y:(A#locs)list#C list#locs#E.
       (P2:(A#locs)list->(A,B,C,E)pegsym->(A#locs)list->C list->locs#E->bool)
         (FST x) (SND x) (FST y) (FST (SND y)) (SND (SND y))`]
   peg_eval_strongind) THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[FST; SND] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN ASM_MESON_TAC[];
    REWRITE_TAC[FORALL_PAIR_THM] THEN SIMP_TAC[]]);;

let UNCURRY_Failure_EQ_Success = prove
 (`!(fle:locs#E) (s:A) (r:C) eo. ~(UNCURRY Failure fle = peg_Success s r eo)`,
  REWRITE_TAC[FORALL_PAIR_THM; UNCURRY_DEF; pegresult_distinct]);;

(* HOL4: IS_PREFIX_MEM (the rich_list theorem has the same statement) *)

let LPARSEAUX_isPREFIX_APPEND = prove
 (`!(l1:A list) l2. isPREFIX l1 l2 <=> ?s. l2 = APPEND l1 s`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[isPREFIX; APPEND] THENL
   [MESON_TAC[]; ALL_TAC] THEN
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[list_CASE; GSYM NOT_CONS_NIL; CONS_11] THEN
  MESON_TAC[]);;

let peg_IS_PREFIX_MEM = prove
 (`!(l1:A list) l2 e. isPREFIX l1 l2 /\ MEM e l1 ==> MEM e l2`,
  REWRITE_TAC[LPARSEAUX_isPREFIX_APPEND] THEN
  MESON_TAC[MEM_APPEND]);;

let LPARSEAUX_IS_SUFFIX_APPEND = prove
 (`!(l1:A list) l2. IS_SUFFIX l1 l2 <=> ?p. l1 = APPEND p l2`,
  REWRITE_TAC[IS_SUFFIX_DEF; LPARSEAUX_isPREFIX_APPEND] THEN
  REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o AP_TERM `REVERSE:A list->A list`) THEN
    REWRITE_TAC[REVERSE_REVERSE; REVERSE_APPEND] THEN MESON_TAC[];
    EXISTS_TAC `REVERSE (p:A list)` THEN
    ASM_REWRITE_TAC[REVERSE_APPEND]]);;

let LPARSEAUX_IS_SUFFIX_REFL = prove
 (`!l:A list. IS_SUFFIX l l`,
  REWRITE_TAC[LPARSEAUX_IS_SUFFIX_APPEND] THEN MESON_TAC[APPEND]);;

let LPARSEAUX_IS_SUFFIX_CONS = prove
 (`!(h:A) t. IS_SUFFIX (CONS h t) t`,
  REWRITE_TAC[LPARSEAUX_IS_SUFFIX_APPEND] THEN MESON_TAC[APPEND]);;

let LPARSEAUX_IS_SUFFIX_TRANS = prove
 (`!(l1:A list) l2 l3. IS_SUFFIX l1 l2 /\ IS_SUFFIX l2 l3 ==> IS_SUFFIX l1 l3`,
  REWRITE_TAC[LPARSEAUX_IS_SUFFIX_APPEND] THEN MESON_TAC[APPEND_ASSOC]);;

let LPARSEAUX_IS_SUFFIX_MEM = prove
 (`!(l1:A list) l2 x. IS_SUFFIX l1 l2 /\ MEM x l2 ==> MEM x l1`,
  REWRITE_TAC[LPARSEAUX_IS_SUFFIX_APPEND] THEN MESON_TAC[MEM_APPEND]);;

let LPARSEAUX_IS_SUFFIX_LENGTH = prove
 (`!(l1:A list) l2. IS_SUFFIX l1 l2 ==> LENGTH l2 <= LENGTH l1`,
  REWRITE_TAC[LPARSEAUX_IS_SUFFIX_APPEND] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[LENGTH_APPEND] THEN ARITH_TAC);;

let LPARSEAUX_IS_SUFFIX_LENGTH_EQ = prove
 (`!(l1:A list) l2. IS_SUFFIX l1 l2 /\ LENGTH l1 = LENGTH l2 ==> l1 = l2`,
  REWRITE_TAC[LPARSEAUX_IS_SUFFIX_APPEND] THEN REPEAT STRIP_TAC THEN
  UNDISCH_TAC `LENGTH (l1:A list) = LENGTH (l2:A list)` THEN
  ASM_REWRITE_TAC[LENGTH_APPEND; ARITH_RULE `a + b = b <=> a = 0`;
                  LENGTH_EQ_NIL] THEN
  SIMP_TAC[APPEND]);;

let LPARSEAUX_sloc_MEM = prove
 (`!s:(A#locs)list.
     ~(sloc s = Locs EOFpt EOFpt) ==> MEM (sloc s) (MAP SND s)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[sloc_def; MAP; MEM]);;

let LPARSEAUX_IS_SUFFIX_MEM_MAP = prove
 (`!(l1:A list) l2 (f:A->B) x.
     IS_SUFFIX l1 l2 /\ MEM x (MAP f l2) ==> MEM x (MAP f l1)`,
  REWRITE_TAC[LPARSEAUX_IS_SUFFIX_APPEND] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[MAP_APPEND; MEM_APPEND]);;

let LPARSEAUX_UNCURRY_Failure_MAXerr = prove
 (`!fl1 (fe1:E) fl2 fe2 fl fe.
     UNCURRY Failure (MAXerr (fl1,fe1) (fl2,fe2)) =
       (Failure fl fe:(A,C,E)pegresult) <=>
     (if locsle fl1 fl2 then fl = fl2 /\ fe = fe2 else fl = fl1 /\ fe = fe1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MAXerr_def] THEN COND_CASES_TAC THEN
  REWRITE_TAC[UNCURRY_DEF; pegresult_inject] THEN MESON_TAC[]);;

let LPARSEAUX_UNCURRY_Failure_MAXerr_Success = prove
 (`!fl1 (fe1:E) fl2 fe2 (s:A) (r:C) eo.
     ~(UNCURRY Failure (MAXerr (fl1,fe1) (fl2,fe2)) = peg_Success s r eo)`,
  REWRITE_TAC[UNCURRY_Failure_EQ_Success]);;

(* ------------------------------------------------------------------------- *)
(* Theorem 3.1: suffixes; Theorem 3.2: determinism; Lemma 3.3.               *)
(* ------------------------------------------------------------------------- *)

let LPARSEAUX_RESULT_RWS =
  [pegresult_distinct; pegresult_inject; isFailure_def; isSuccess_def;
   resultmap_EQ_Success; resultmap_EQ_Failure;
   LPARSEAUX_UNCURRY_Failure_MAXerr; LPARSEAUX_UNCURRY_Failure_MAXerr_Success];;

(* HOL4: peg_eval_suffix0 (local) and peg_eval_suffix (Theorem 3.1) *)

let peg_eval_suffix = prove
 (`!G:(A,B,C,E)peg.
     (!s0 e s r eo. peg_eval G (s0,e) (peg_Success s r eo) ==> IS_SUFFIX s0 s) /\
     (!s0 e fl fe.
        peg_eval G (s0,e) (Failure fl fe) /\ ~(fl = Locs EOFpt EOFpt)
        ==> MEM fl (MAP SND s0)) /\
     (!s0 e s rl err. peg_eval_list G (s0,e) (s,rl,err) ==> IS_SUFFIX s0 s)`,
  GEN_TAC THEN
  SUBGOAL_THEN
   `(!s0 e sr. peg_eval (G:(A,B,C,E)peg) (s0,e) sr ==>
       (!s r eo. sr = peg_Success s r eo ==> IS_SUFFIX s0 s) /\
       (!fl fe. sr = Failure fl fe /\ ~(fl = Locs EOFpt EOFpt)
                ==> MEM fl (MAP SND s0))) /\
    (!s0 e s rl err. peg_eval_list G (s0,e) (s,rl,err) ==> IS_SUFFIX s0 s)`
   (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC peg_eval_strongind' THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  TRY(DISCH_THEN STRIP_ASSUME_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE LPARSEAUX_RESULT_RWS) THEN
  REWRITE_TAC LPARSEAUX_RESULT_RWS THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  ASM_MESON_TAC[LPARSEAUX_IS_SUFFIX_REFL; LPARSEAUX_IS_SUFFIX_CONS;
                LPARSEAUX_IS_SUFFIX_TRANS; LPARSEAUX_IS_SUFFIX_MEM_MAP;
                LPARSEAUX_sloc_MEM; MAP; MEM]);;

let LPARSEAUX_isSuccess_isFailure = prove
 (`!r:(A,C,E)pegresult. isSuccess r <=> ~isFailure r`,
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `r:(A,C,E)pegresult` pegresult_nchotomy) THEN
  REWRITE_TAC[isSuccess_def; isFailure_def]);;

let LPARSEAUX_SR_TAC : tactic =
  FIRST_X_ASSUM(MP_TAC o check (fun th -> let c = concl th in
     is_comb c && is_var (rand c) &&
     (let n = fst(dest_var(rand c)) in n = "sr'" || n = "srl'")));;

let LPARSEAUX_F_TAC : tactic =
  FIRST_ASSUM(CONTR_TAC o check (fun th -> concl th = `F`));;

let LPARSEAUX_CONTRA_TAC : tactic =
  FIRST_ASSUM(fun th -> FIRST_ASSUM(fun th' ->
    if concl th' = mk_neg(concl th) then CONTR_TAC(MP (NOT_ELIM th') th)
    else failwith "LPARSEAUX_CONTRA_TAC"));;

let LPARSEAUX_DET_STEP_TAC : tactic =
  RES_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[pegresult_distinct; pegresult_inject; PAIR_EQ;
                              LPARSEAUX_isSuccess_isFailure]) THEN
  TRY LPARSEAUX_F_TAC THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj(concl th) then STRIP_ASSUME_TAC th
                                 else failwith "")) THEN
  RVEQ_TAC THEN ASM_REWRITE_TAC[pegresult_distinct; pegresult_inject; PAIR_EQ];;

let LPARSEAUX_peg_eval_unique = prove
 (`!G:(A,B,C,E)peg.
     (!s0 e sr. peg_eval G (s0,e) sr
                ==> !sr'. peg_eval G (s0,e) sr' ==> sr' = sr) /\
     (!s0 e s rl err. peg_eval_list G (s0,e) (s,rl,err)
                ==> !srl'. peg_eval_list G (s0,e) srl' ==> srl' = (s,rl,err))`,
  GEN_TAC THEN
  MATCH_MP_TAC peg_eval_strongind' THEN REPEAT CONJ_TAC THEN
  REPEAT STRIP_TAC THEN LPARSEAUX_SR_TAC THEN
  ONCE_REWRITE_TAC[peg_eval_cases] THEN
  REWRITE_TAC[PAIR_EQ; pegsym_distinct; pegsym_inject; NOT_CONS_NIL;
              GSYM NOT_CONS_NIL; CONS_11] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  LPARSEAUX_DET_STEP_TAC THEN TRY LPARSEAUX_DET_STEP_TAC THEN
  TRY LPARSEAUX_CONTRA_TAC);;

(* Theorem 3.2 *)

let peg_deterministic = prove
 (`!G:(A,B,C,E)peg.
     (!s0 e sr. peg_eval G (s0,e) sr
                ==> !sr'. peg_eval G (s0,e) sr' <=> sr' = sr) /\
     (!s0 e s rl err. peg_eval_list G (s0,e) (s,rl,err)
                ==> !srl'. peg_eval_list G (s0,e) srl' <=> srl' = (s,rl,err))`,
  MESON_TAC[LPARSEAUX_peg_eval_unique]);;

let LPARSEAUX_CONS_NEQ = prove
 (`!(h:A) t. ~(CONS h t = t)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o AP_TERM `LENGTH:A list->num`) THEN
  REWRITE_TAC[LENGTH] THEN ARITH_TAC);;

let LPARSEAUX_PEG_INV_TAC : tactic =
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [peg_eval_cases] THEN
  REWRITE_TAC[PAIR_EQ; pegsym_distinct; pegsym_inject; pegresult_distinct;
              pegresult_inject; NOT_CONS_NIL; GSYM NOT_CONS_NIL; CONS_11] THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM; LEFT_EXISTS_AND_THM; UNWIND_THM1;
              UNWIND_THM2; GSYM CONJ_ASSOC] THEN
  MESON_TAC[];;

let peg_eval_rpt = prove
 (`!(G:(A,B,C,E)peg) i0 s f x.
     peg_eval G (i0, rpt s f) x <=>
     ?i l err. peg_eval_list G (i0,s) (i,l,err) /\
               x = peg_Success i (f l) (SOME err)`,
  LPARSEAUX_PEG_INV_TAC);;

let peg_eval_list = prove
 (`!(G:(A,B,C,E)peg) i0 e i r err.
     peg_eval_list G (i0, e) (i, r, err) <=>
     (?fl fe. peg_eval G (i0, e) (Failure fl fe) /\ i = i0 /\ r = [] /\
              err = (fl,fe)) \/
     (?i1 rh rt eo0.
        peg_eval G (i0, e) (peg_Success i1 rh eo0) /\
        peg_eval_list G (i1, e) (i, rt, err) /\ r = CONS rh rt)`,
  LPARSEAUX_PEG_INV_TAC);;

(* Lemma 3.3 *)

let peg_badrpt = prove
 (`!(G:(A,B,C,E)peg) s0 e r eo f.
     peg_eval G (s0,e) (peg_Success s0 r eo) ==> !r. ~peg_eval G (s0, rpt e f) r`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
  REWRITE_TAC[peg_eval_rpt; NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`i:(A#locs)list`; `l:C list`; `err:locs#E`] THEN
  STRIP_TAC THEN
  MP_TAC(CONJUNCT2 (SPEC `G:(A,B,C,E)peg` peg_deterministic)) THEN
  DISCH_THEN(MP_TAC o SPECL [`s0:(A#locs)list`; `e:(A,B,C,E)pegsym`;
                             `i:(A#locs)list`; `l:C list`; `err:locs#E`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `(i:(A#locs)list),CONS (r:C) l,(err:locs#E)`) THEN
  REWRITE_TAC[PAIR_EQ; LPARSEAUX_CONS_NEQ] THEN
  ONCE_REWRITE_TAC[peg_eval_list] THEN DISJ2_TAC THEN
  MAP_EVERY EXISTS_TAC [`s0:(A#locs)list`; `r:C`; `l:C list`;
                        `eo:(locs#E)option`] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Expressions that may consume nothing, something, or fail.                 *)
(* ------------------------------------------------------------------------- *)

let peg0_rules,peg0_ind,LPARSEAUX_peg0_cases = new_inductive_definition
 `(!c. peg0 (G:(A,B,C,E)peg) (empty c)) /\
  (!f. peggt0 G (any f)) /\
  (!f. pegfail G (any f)) /\
  (!t f. peggt0 G (tok t f)) /\
  (!t f. pegfail G (tok t f)) /\
  (!e f. pegfail G e ==> peg0 G (rpt e f)) /\
  (!e f. peggt0 G e ==> peggt0 G (rpt e f)) /\
  (!n f. n IN FDOM (peg_rules G) /\ peg0 G (FAPPLY (peg_rules G) n)
         ==> peg0 G (nt n f)) /\
  (!n f. n IN FDOM (peg_rules G) /\ peggt0 G (FAPPLY (peg_rules G) n)
         ==> peggt0 G (nt n f)) /\
  (!n f. n IN FDOM (peg_rules G) /\ pegfail G (FAPPLY (peg_rules G) n)
         ==> pegfail G (nt n f)) /\
  (!e1 e2 f. pegfail G e1 \/ (peg0 G e1 /\ pegfail G e2) \/
             (peggt0 G e1 /\ pegfail G e2)
             ==> pegfail G (seq e1 e2 f)) /\
  (!e1 e2 f. peggt0 G e1 /\ (peg0 G e2 \/ peggt0 G e2) \/
             (peg0 G e1 \/ peggt0 G e1) /\ peggt0 G e2
             ==> peggt0 G (seq e1 e2 f)) /\
  (!e1 e2 f. peg0 G e1 /\ peg0 G e2 ==> peg0 G (seq e1 e2 f)) /\
  (!e1 e2 f. peg0 G e1 \/ (pegfail G e1 /\ peg0 G e2)
             ==> peg0 G (choice e1 e2 f)) /\
  (!e1 e2 f. pegfail G e1 /\ pegfail G e2 ==> pegfail G (choice e1 e2 f)) /\
  (!e1 e2 f. peggt0 G e1 \/ (pegfail G e1 /\ peggt0 G e2)
             ==> peggt0 G (choice e1 e2 f)) /\
  (!e c. pegfail G e ==> peg0 G (not e c)) /\
  (!e c. peg0 G e \/ peggt0 G e ==> pegfail G (not e c)) /\
  (!e. pegfail G (error e))`;;

let peg0_strongind = derive_strong_induction(peg0_rules,peg0_ind);;

(* HOL4's order of the three relations: peg0, peggt0, pegfail *)

let peg0_cases =
  let g = `G:(A,B,C,E)peg` in
  match CONJUNCTS (SPEC g LPARSEAUX_peg0_cases) with
    [a;b;c] -> GEN g (CONJ b (CONJ a c))
  | _ -> failwith "peg0_cases";;

let peg0_error = prove
 (`!(G:(A,B,C,E)peg) e. ~peg0 G (error e)`,
  ONCE_REWRITE_TAC[peg0_cases] THEN REWRITE_TAC[pegsym_distinct]);;

let LPARSEAUX_peg_eval_suffix_cases = prove
 (`!(G:(A,B,C,E)peg) s0 e s c eo.
     peg_eval G (s0,e) (peg_Success s c eo) ==> s0 = s \/ LENGTH s < LENGTH s0`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (CONJUNCT1 (SPEC_ALL peg_eval_suffix))) THEN
  MESON_TAC[LPARSEAUX_IS_SUFFIX_LENGTH; LPARSEAUX_IS_SUFFIX_LENGTH_EQ;
            ARITH_RULE `a <= b ==> a = b \/ a < b`]);;

let LPARSEAUX_peg_eval_list_suffix_cases = prove
 (`!(G:(A,B,C,E)peg) s0 e s rl err.
     peg_eval_list G (s0,e) (s,rl,err) ==> s0 = s \/ LENGTH s < LENGTH s0`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP
    (CONJUNCT2(CONJUNCT2 (SPEC_ALL peg_eval_suffix)))) THEN
  MESON_TAC[LPARSEAUX_IS_SUFFIX_LENGTH; LPARSEAUX_IS_SUFFIX_LENGTH_EQ;
            ARITH_RULE `a <= b ==> a = b \/ a < b`]);;

let peg_eval_suffix' = prove
 (`!(G:(A,B,C,E)peg) s0 e s c eo.
     peg_eval G (s0,e) (peg_Success s c eo)
     ==> s0 = s \/ IS_SUFFIX s0 s /\ LENGTH s < LENGTH s0`,
  MESON_TAC[LPARSEAUX_peg_eval_suffix_cases; peg_eval_suffix]);;

let peg_eval_list_suffix' = prove
 (`!(G:(A,B,C,E)peg) s0 e s rl err.
     peg_eval_list G (s0, e) (s,rl,err)
     ==> s0 = s \/ IS_SUFFIX s0 s /\ LENGTH s < LENGTH s0`,
  MESON_TAC[LPARSEAUX_peg_eval_list_suffix_cases; peg_eval_suffix]);;

let FORALL_result = prove
 (`!P:(A,C,E)pegresult->bool.
     (!r. P r) <=> (!a c eo. P (peg_Success a c eo)) /\ (!fl fe. P (Failure fl fe))`,
  GEN_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN STRIP_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `r:(A,C,E)pegresult` pegresult_nchotomy) THEN
  ASM_REWRITE_TAC[]);;

let EXISTS_result = prove
 (`!P:(A,C,E)pegresult->bool.
     (?r. P r) <=> (?a c eo. P (peg_Success a c eo)) \/ (?fl fe. P (Failure fl fe))`,
  GEN_TAC THEN EQ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:(A,C,E)pegresult` MP_TAC) THEN
  STRUCT_CASES_TAC(ISPEC `r:(A,C,E)pegresult` pegresult_nchotomy) THEN
  MESON_TAC[]);;

let LPARSEAUX_CONS_NEQ' = prove
 (`!(h:A) t. ~(t = CONS h t)`,
  MESON_TAC[LPARSEAUX_CONS_NEQ]);;

let LPARSEAUX_isFailure_resultmap = prove
 (`!(f:C->D) (r:(A,C,E)pegresult). isFailure (resultmap f r) <=> isFailure r`,
  GEN_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `r:(A,C,E)pegresult` pegresult_nchotomy) THEN
  REWRITE_TAC[resultmap_def; isFailure_def]);;

let LPARSEAUX_isSuccess_EXISTS = prove
 (`!r:(A,C,E)pegresult. isSuccess r <=> ?a c eo. r = peg_Success a c eo`,
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `r:(A,C,E)pegresult` pegresult_nchotomy) THEN
  REWRITE_TAC[isSuccess_def; pegresult_distinct; pegresult_inject] THEN
  MESON_TAC[]);;

let LPARSEAUX_isFailure_EXISTS = prove
 (`!r:(A,C,E)pegresult. isFailure r <=> ?fl fe. r = Failure fl fe`,
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `r:(A,C,E)pegresult` pegresult_nchotomy) THEN
  REWRITE_TAC[isFailure_def; pegresult_distinct; pegresult_inject] THEN
  MESON_TAC[]);;

let LPARSEAUX_ADD_SUFFIX_TAC : tactic =
  ASSUM_LIST(fun ths -> MAP_EVERY (fun th ->
     (try ASSUME_TAC(MATCH_MP LPARSEAUX_peg_eval_suffix_cases th)
      with Failure _ -> ALL_TAC) THEN
     (try ASSUME_TAC(MATCH_MP LPARSEAUX_peg_eval_list_suffix_cases th)
      with Failure _ -> ALL_TAC)) ths);;

let LPARSEAUX_STRIP_EX_TAC : tactic =
  REPEAT(FIRST_X_ASSUM(fun th -> if is_exists(concl th) then
                                   STRIP_ASSUME_TAC th else failwith ""));;

let LPARSEAUX_L41_RWS =
  [GSYM CONJ_ASSOC; IMP_CONJ; RIGHT_FORALL_IMP_THM;
   FORALL_UNWIND_THM1; FORALL_UNWIND_THM2; LEFT_IMP_EXISTS_THM;
   LENGTH; LT_REFL; LPARSEAUX_CONS_NEQ; LPARSEAUX_CONS_NEQ'] @
  LPARSEAUX_RESULT_RWS;;

(* HOL4: lemma4_1a0 (local) *)

let LPARSEAUX_lemma4_1a0 = prove
 (`!G:(A,B,C,E)peg.
     (!s0 e r. peg_eval G (s0, e) r ==>
        (!c eo. r = peg_Success s0 c eo ==> peg0 G e) /\
        (isFailure r ==> pegfail G e) /\
        (!s c eo. r = peg_Success s c eo /\ LENGTH s < LENGTH s0 ==> peggt0 G e)) /\
     (!s0 e s rl err. peg_eval_list G (s0,e) (s,rl,err) ==>
        (s0 = s ==> pegfail G e) /\
        (LENGTH s < LENGTH s0 ==> peggt0 G e))`,
  GEN_TAC THEN MATCH_MP_TAC peg_eval_strongind' THEN REPEAT CONJ_TAC THEN
  REPEAT GEN_TAC THEN TRY(DISCH_THEN STRIP_ASSUME_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LPARSEAUX_isSuccess_EXISTS;
                              LPARSEAUX_isFailure_EXISTS]) THEN
  REWRITE_TAC[LPARSEAUX_isSuccess_EXISTS; LPARSEAUX_isFailure_EXISTS] THEN
  RULE_ASSUM_TAC(REWRITE_RULE LPARSEAUX_L41_RWS) THEN
  REWRITE_TAC LPARSEAUX_L41_RWS THEN
  REPEAT STRIP_TAC THEN LPARSEAUX_STRIP_EX_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE LPARSEAUX_L41_RWS) THEN
  TRY LPARSEAUX_F_TAC THEN LPARSEAUX_ADD_SUFFIX_TAC THEN
  ASM_MESON_TAC[peg0_rules; LT_REFL; LT_TRANS]);;

let lemma4_1a = prove
 (`!G:(A,B,C,E)peg.
     (!s0 e c eo. peg_eval G (s0,e) (peg_Success s0 c eo) ==> peg0 G e) /\
     (!s0 e r. peg_eval G (s0,e) r /\ isFailure r ==> pegfail G e) /\
     (!s0 e s c eo.
        peg_eval G (s0,e) (peg_Success s c eo) /\ LENGTH s < LENGTH s0
        ==> peggt0 G e) /\
     (!s0 e rl err. peg_eval_list G (s0,e) (s0,rl,err) ==> pegfail G e) /\
     (!s0 e s rl err.
        peg_eval_list G (s0,e) (s,rl,err) /\ LENGTH s < LENGTH s0
        ==> peggt0 G e)`,
  GEN_TAC THEN MP_TAC(SPEC `G:(A,B,C,E)peg` LPARSEAUX_lemma4_1a0) THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Well-formed expressions and grammars; totality of evaluation.             *)
(* ------------------------------------------------------------------------- *)

let wfpeg_rules,wfpeg_ind,wfpeg_cases = new_inductive_definition
 `(!n f. n IN FDOM (peg_rules (G:(A,B,C,E)peg)) /\
         wfpeg G (FAPPLY (peg_rules G) n)
         ==> wfpeg G (nt n f)) /\
  (!c. wfpeg G (empty c)) /\
  (!f. wfpeg G (any f)) /\
  (!t f. wfpeg G (tok t f)) /\
  (!e. wfpeg G (error e)) /\
  (!e c. wfpeg G e ==> wfpeg G (not e c)) /\
  (!e1 e2 f. wfpeg G e1 /\ (peg0 G e1 ==> wfpeg G e2)
             ==> wfpeg G (seq e1 e2 f)) /\
  (!e1 e2 f. wfpeg G e1 /\ wfpeg G e2 ==> wfpeg G (choice e1 e2 f)) /\
  (!e f. wfpeg G e /\ ~peg0 G e ==> wfpeg G (rpt e f))`;;

let wfpeg_strongind = derive_strong_induction(wfpeg_rules,wfpeg_ind);;

let wfpeg__empty = prove
 (`!(G:(A,B,C,E)peg) c. wfpeg G (empty c)`,
  MESON_TAC[wfpeg_rules]);;

let wfpeg__any = prove
 (`!(G:(A,B,C,E)peg) f. wfpeg G (any f)`,
  MESON_TAC[wfpeg_rules]);;

let wfpeg_tok = prove
 (`!(G:(A,B,C,E)peg) t f. wfpeg G (tok t f)`,
  MESON_TAC[wfpeg_rules]);;

let wfpeg__error = prove
 (`!(G:(A,B,C,E)peg) e. wfpeg G (error e)`,
  MESON_TAC[wfpeg_rules]);;

let subexprs_def = cake_def
 `(subexprs (any (f1:A#locs->C)) = {any f1}:((A,B,C,E)pegsym)->bool) /\
  (subexprs (empty c) = {empty c}) /\
  (subexprs (tok t f2) = {tok t f2}) /\
  (subexprs (error err) = {error err}) /\
  (subexprs (nt s f) = {nt s f}) /\
  (subexprs (not e c) = not e c INSERT subexprs e) /\
  (subexprs (seq e1 e2 f3) =
     seq e1 e2 f3 INSERT (subexprs e1 UNION subexprs e2)) /\
  (subexprs (choice e1 e2 f4) =
     choice e1 e2 f4 INSERT (subexprs e1 UNION subexprs e2)) /\
  (subexprs (rpt e f5) = rpt e f5 INSERT subexprs e)`;;

let subexprs_included = prove
 (`!e:(A,B,C,E)pegsym. e IN subexprs e`,
  MATCH_MP_TAC pegsym_INDUCT THEN REWRITE_TAC[subexprs_def; IN_INSERT]);;

let peg_Gexprs_def = new_definition
  `Gexprs (G:(A,B,C,E)peg) =
     UNIONS (IMAGE subexprs (peg_start G INSERT FRANGE (peg_rules G)))`;;

let start_IN_Gexprs = prove
 (`!G:(A,B,C,E)peg. peg_start G IN Gexprs G`,
  REWRITE_TAC[peg_Gexprs_def; IN_UNIONS; IN_IMAGE; IN_INSERT] THEN
  MESON_TAC[subexprs_included]);;

let wfG_def = new_definition
  `wfG (G:(A,B,C,E)peg) <=> !e. e IN Gexprs G ==> wfpeg G e`;;

let IN_subexprs_TRANS = prove
 (`!a b c:(A,B,C,E)pegsym.
     a IN subexprs b /\ b IN subexprs c ==> a IN subexprs c`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC pegsym_INDUCT THEN
  REWRITE_TAC[subexprs_def; IN_INSERT; IN_UNION; NOT_IN_EMPTY] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[subexprs_def; IN_INSERT; IN_UNION;
                              NOT_IN_EMPTY]) THEN
  ASM_MESON_TAC[]);;

let peg_Gexprs_subexprs = prove
 (`!(G:(A,B,C,E)peg) e. e IN Gexprs G ==> subexprs e SUBSET Gexprs G`,
  REWRITE_TAC[peg_Gexprs_def; SUBSET; IN_UNIONS; IN_IMAGE] THEN
  MESON_TAC[IN_subexprs_TRANS]);;

let IN_Gexprs_E = prove
 (`!(G:(A,B,C,E)peg).
     (!e c. not e c IN Gexprs G ==> e IN Gexprs G) /\
     (!e1 e2 f. seq e1 e2 f IN Gexprs G ==> e1 IN Gexprs G /\ e2 IN Gexprs G) /\
     (!e1 e2 f2. choice e1 e2 f2 IN Gexprs G
                 ==> e1 IN Gexprs G /\ e2 IN Gexprs G) /\
     (!e f3. rpt e f3 IN Gexprs G ==> e IN Gexprs G)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP peg_Gexprs_subexprs) THEN
  REWRITE_TAC[subexprs_def; SUBSET; IN_INSERT; IN_UNION] THEN
  MESON_TAC[subexprs_included]);;

(* HOL4: reducing_peg_eval_makes_list (local) *)

let LPARSEAUX_reducing_peg_eval_makes_list = prove
 (`!(G:(A,B,C,E)peg) e n s0.
     (!s. LENGTH s < n ==> ?r. peg_eval G (s, e) r) /\ ~peg0 G e /\
     LENGTH s0 < n
     ==> ?s' rl err. peg_eval_list G (s0,e) (s',rl,err)`,
  REPEAT GEN_TAC THEN WF_INDUCT_TAC `LENGTH (s0:(A#locs)list)` THEN
  FIRST_X_ASSUM(LABEL_TAC "ih") THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "tot")
    (CONJUNCTS_THEN2 (LABEL_TAC "np") (LABEL_TAC "len"))) THEN
  SUBGOAL_THEN `?r. peg_eval (G:(A,B,C,E)peg) (s0,e) r` MP_TAC THENL
   [REMOVE_THEN "tot" (MP_TAC o SPEC `s0:(A#locs)list`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:((A#locs)list,C,E)pegresult` MP_TAC) THEN
  STRUCT_CASES_TAC(ISPEC `r:((A#locs)list,C,E)pegresult`
                     pegresult_nchotomy) THEN
  DISCH_TAC THENL
   [ALL_TAC;
    MAP_EVERY EXISTS_TAC [`s0:(A#locs)list`; `[]:C list`;
                          `(a0:locs,a1:E)`] THEN
    ONCE_REWRITE_TAC[peg_eval_list] THEN DISJ1_TAC THEN
    MAP_EVERY EXISTS_TAC [`a0:locs`; `a1:E`] THEN ASM_REWRITE_TAC[]] THEN
  MP_TAC(ISPECL [`G:(A,B,C,E)peg`; `s0:(A#locs)list`; `e:(A,B,C,E)pegsym`;
                 `a0:(A#locs)list`; `a1:C`; `a2:(locs#E)option`]
                LPARSEAUX_peg_eval_suffix_cases) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [RVEQ_TAC THEN ASM_MESON_TAC[lemma4_1a]; ALL_TAC] THEN
  REMOVE_THEN "ih" (MP_TAC o SPEC `a0:(A#locs)list`) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s':(A#locs)list` (X_CHOOSE_THEN `rl:C list`
    (X_CHOOSE_THEN `err:locs#E` ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`s':(A#locs)list`; `CONS (a1:C) rl`;
                        `err:locs#E`] THEN
  ONCE_REWRITE_TAC[peg_eval_list] THEN DISJ2_TAC THEN
  MAP_EVERY EXISTS_TAC [`a0:(A#locs)list`; `a1:C`; `rl:C list`;
                        `a2:(locs#E)option`] THEN
  ASM_REWRITE_TAC[]);;

let LPARSEAUX_rules_IN_Gexprs = prove
 (`!(G:(A,B,C,E)peg) n.
     n IN FDOM (peg_rules G) ==> FAPPLY (peg_rules G) n IN Gexprs G`,
  REWRITE_TAC[peg_Gexprs_def; IN_UNIONS; IN_IMAGE; IN_INSERT; FRANGE_DEF;
              IN_ELIM_THM] THEN
  MESON_TAC[subexprs_included]);;

let LPARSEAUX_RESULT_CASES_TAC (tm:term) =
  STRUCT_CASES_TAC(ISPEC tm pegresult_nchotomy);;

let peg_eval_total = prove
 (`!G:(A,B,C,E)peg. wfG G ==> !s e. e IN Gexprs G ==> ?r. peg_eval G (s,e) r`,
  GEN_TAC THEN REWRITE_TAC[wfG_def] THEN DISCH_TAC THEN GEN_TAC THEN
  WF_INDUCT_TAC `LENGTH (s:(A#locs)list)` THEN
  FIRST_X_ASSUM(LABEL_TAC "ih") THEN
  SUBGOAL_THEN
   `!e. wfpeg (G:(A,B,C,E)peg) e ==> e IN Gexprs G
        ==> ?r. peg_eval G (s,e) r`
   (fun th -> ASM_MESON_TAC[th]) THEN
  MATCH_MP_TAC wfpeg_ind THEN REPEAT CONJ_TAC THENL
   [(* nt *)
    REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    ASM_SIMP_TAC[LPARSEAUX_rules_IN_Gexprs] THEN
    DISCH_THEN(X_CHOOSE_TAC `r:((A#locs)list,C,E)pegresult`) THEN
    DISCH_TAC THEN EXISTS_TAC `resultmap (f:C->C) (r:((A#locs)list,C,E)pegresult)` THEN
    MATCH_MP_TAC peg_eval_nt THEN ASM_REWRITE_TAC[];
    (* empty *)
    MESON_TAC[LPARSEAUX_peg_eval_empty_rule];
    (* any *)
    REPEAT STRIP_TAC THEN
    STRUCT_CASES_TAC(ISPEC `s:(A#locs)list` list_CASES) THEN
    MESON_TAC[peg_eval_any_success; peg_eval_any_failure];
    (* tok *)
    REPEAT STRIP_TAC THEN
    STRUCT_CASES_TAC(ISPEC `s:(A#locs)list` list_CASES) THENL
     [MESON_TAC[peg_eval_tok_failureEOF]; ALL_TAC] THEN
    ASM_CASES_TAC `(t:A->bool) (FST (h:A#locs))` THEN
    ASM_MESON_TAC[peg_eval_tok_success; peg_eval_tok_failureF];
    (* error *)
    MESON_TAC[peg_eval_error];
    (* not *)
    REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "ihe") THEN DISCH_TAC THEN
    REMOVE_THEN "ihe" MP_TAC THEN ANTS_TAC THENL
     [ASM_MESON_TAC[IN_Gexprs_E]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:((A#locs)list,C,E)pegresult` ASSUME_TAC) THEN
    ASM_CASES_TAC `isSuccess (r:((A#locs)list,C,E)pegresult)` THEN
    ASM_MESON_TAC[peg_eval_not_success; peg_eval_not_failure;
                  LPARSEAUX_isSuccess_isFailure];
    (* seq *)
    REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `e1 IN Gexprs (G:(A,B,C,E)peg) /\ e2 IN Gexprs G`
      STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[IN_Gexprs_E]; ALL_TAC] THEN
    REMOVE_THEN "ih1" MP_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `r1:((A#locs)list,C,E)pegresult` MP_TAC) THEN
    LPARSEAUX_RESULT_CASES_TAC `r1:((A#locs)list,C,E)pegresult` THEN
    DISCH_TAC THENL
     [ALL_TAC; ASM_MESON_TAC[peg_eval_seq_fail1]] THEN
    SUBGOAL_THEN `?r2. peg_eval (G:(A,B,C,E)peg) (a0,e2) r2` MP_TAC THENL
     [MP_TAC(ISPECL [`G:(A,B,C,E)peg`; `s:(A#locs)list`; `e1:(A,B,C,E)pegsym`;
                     `a0:(A#locs)list`; `a1:C`; `a2:(locs#E)option`]
                    LPARSEAUX_peg_eval_suffix_cases) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
       [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
        SUBGOAL_THEN `peg0 (G:(A,B,C,E)peg) e1` ASSUME_TAC THENL
         [ASM_MESON_TAC[lemma4_1a]; ALL_TAC] THEN
        REMOVE_THEN "ih2" MP_TAC THEN ASM_REWRITE_TAC[];
        USE_THEN "ih" (MP_TAC o SPEC `a0:(A#locs)list`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        DISCH_THEN(MP_TAC o SPEC `e2:(A,B,C,E)pegsym`) THEN
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `r2:((A#locs)list,C,E)pegresult` MP_TAC) THEN
    LPARSEAUX_RESULT_CASES_TAC `r2:((A#locs)list,C,E)pegresult` THEN
    DISCH_TAC THEN
    ASM_MESON_TAC[peg_eval_seq_success; peg_eval_seq_fail2];
    (* choice *)
    REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `e1 IN Gexprs (G:(A,B,C,E)peg) /\ e2 IN Gexprs G`
      STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[IN_Gexprs_E]; ALL_TAC] THEN
    REMOVE_THEN "ih1" MP_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `r1:((A#locs)list,C,E)pegresult` MP_TAC) THEN
    REMOVE_THEN "ih2" MP_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `r2:((A#locs)list,C,E)pegresult` MP_TAC) THEN
    LPARSEAUX_RESULT_CASES_TAC `r1:((A#locs)list,C,E)pegresult` THEN
    LPARSEAUX_RESULT_CASES_TAC `r2:((A#locs)list,C,E)pegresult` THEN
    REPEAT DISCH_TAC THEN
    ASM_MESON_TAC[peg_eval_choice_success1; peg_eval_choice_success2;
                  peg_eval_choice_fail];
    (* rpt *)
    REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ihe") ASSUME_TAC) THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `e IN Gexprs (G:(A,B,C,E)peg)` ASSUME_TAC THENL
     [ASM_MESON_TAC[IN_Gexprs_E]; ALL_TAC] THEN
    REMOVE_THEN "ihe" MP_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:((A#locs)list,C,E)pegresult` MP_TAC) THEN
    LPARSEAUX_RESULT_CASES_TAC `r:((A#locs)list,C,E)pegresult` THEN
    DISCH_TAC THENL
     [ALL_TAC;
      ASM_MESON_TAC[peg_eval_list_nil; LPARSEAUX_peg_eval_rpt_rule]] THEN
    MP_TAC(ISPECL [`G:(A,B,C,E)peg`; `s:(A#locs)list`; `e:(A,B,C,E)pegsym`;
                   `a0:(A#locs)list`; `a1:C`; `a2:(locs#E)option`]
                  LPARSEAUX_peg_eval_suffix_cases) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
     [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN ASM_MESON_TAC[lemma4_1a];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`G:(A,B,C,E)peg`; `e:(A,B,C,E)pegsym`;
                   `LENGTH (s:(A#locs)list)`; `a0:(A#locs)list`]
                  LPARSEAUX_reducing_peg_eval_makes_list) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `s':(A#locs)list` THEN DISCH_TAC THEN
      USE_THEN "ih" (MP_TAC o SPEC `s':(A#locs)list`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `e:(A,B,C,E)pegsym`) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    STRIP_TAC THEN
    ASM_MESON_TAC[peg_eval_list_cons; LPARSEAUX_peg_eval_rpt_rule]]);;

(* ------------------------------------------------------------------------- *)
(* Derived forms and inversion theorems.                                     *)
(* ------------------------------------------------------------------------- *)

(* derived and useful PEG forms *)

let peg_pegf_def = new_definition
  `peg_pegf (sym:(A,B,C,E)pegsym) (f:C->C) =
     seq sym (empty ARB) (\l1 l2. f l1)`;;

let ignoreL_def = new_definition
  `ignoreL (s1:(A,B,C,E)pegsym) s2 = seq s1 s2 (\a b. b)`;;

let ignoreR_def = new_definition
  `ignoreR (s1:(A,B,C,E)pegsym) s2 = seq s1 s2 (\a b. a)`;;

let peg_choicel_def = new_recursive_definition list_RECURSION
  `(peg_choicel [] = not (empty ARB) ARB:(A,B,C,E)pegsym) /\
   (peg_choicel (CONS h t) = choice h (peg_choicel t) (\s. sum_CASE s I I))`;;

let checkAhead_def = new_definition
  `checkAhead (P:A->bool) (s:(A,B,C,E)pegsym) =
     ignoreL (not (not (tok P ARB) ARB) ARB) s`;;

let peg_eval_seq_SOME = prove
 (`!(G:(A,B,C,E)peg) i0 s1 s2 f i r eo.
     peg_eval G (i0, seq s1 s2 f) (peg_Success i r eo) <=>
     ?i1 r1 r2 eo1.
       peg_eval G (i0, s1) (peg_Success i1 r1 eo1) /\
       peg_eval G (i1, s2) (peg_Success i r2 eo) /\ r = f r1 r2`,
  LPARSEAUX_PEG_INV_TAC);;

let peg_eval_seq_NONE = prove
 (`!(G:(A,B,C,E)peg) i0 s1 s2 f fl fe.
     peg_eval G (i0, seq s1 s2 f) (Failure fl fe) <=>
     peg_eval G (i0, s1) (Failure fl fe) \/
     ?i r eo. peg_eval G (i0,s1) (peg_Success i r eo) /\
              peg_eval G (i,s2) (Failure fl fe)`,
  LPARSEAUX_PEG_INV_TAC);;

let peg_eval_tok_NONE = prove
 (`!(G:(A,B,C,E)peg) i P f fl fe.
     peg_eval G (i, tok P f) (Failure fl fe) <=>
     (?h t. i = CONS h t /\ fl = SND h /\ fe = peg_tokFALSE G /\ ~P (FST h)) \/
     (i = [] /\ fl = Locs EOFpt EOFpt /\ fe = peg_tokEOF G)`,
  LPARSEAUX_PEG_INV_TAC);;

let peg_eval_tok_SOME = prove
 (`!(G:(A,B,C,E)peg) i0 P f i r eo.
     peg_eval G (i0, tok P f) (peg_Success i r eo) <=>
     ?h l. P h /\ i0 = CONS (h,l) i /\ r = f (h,l) /\ eo = NONE`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [peg_eval_cases] THEN
  REWRITE_TAC[PAIR_EQ; pegsym_distinct; pegsym_inject; pegresult_distinct;
              pegresult_inject; EXISTS_PAIR_THM; FORALL_PAIR_THM] THEN
  MESON_TAC[]);;

let peg_eval_empty = prove
 (`!(G:(A,B,C,E)peg) i r x.
     peg_eval G (i, empty r) x <=> x = peg_Success i r NONE`,
  LPARSEAUX_PEG_INV_TAC);;

let LPARSEAUX_Success_EQ_resultmap = prove
 (`!(f:C->D) (r:(A,C,E)pegresult) a x eo.
     peg_Success a x eo = resultmap f r <=> ?x0. r = peg_Success a x0 eo /\ x = f x0`,
  MESON_TAC[resultmap_EQ_Success]);;

let peg_eval_NT_SOME = prove
 (`!(G:(A,B,C,E)peg) i0 N f i r eo.
     peg_eval G (i0,nt N f) (peg_Success i r eo) <=>
     ?r0. r = f r0 /\ N IN FDOM (peg_rules G) /\
          peg_eval G (i0,FAPPLY (peg_rules G) N) (peg_Success i r0 eo)`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [peg_eval_cases] THEN
  REWRITE_TAC[PAIR_EQ; pegsym_distinct; pegsym_inject; pegresult_distinct;
              pegresult_inject] THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM; LEFT_EXISTS_AND_THM; UNWIND_THM1;
              UNWIND_THM2; GSYM CONJ_ASSOC] THEN
  REWRITE_TAC[LPARSEAUX_Success_EQ_resultmap] THEN MESON_TAC[]);;

let LPARSEAUX_EXISTS_Success = prove
 (`!(P:(A,C,E)pegresult->bool) Q.
     (?sr. P sr /\ (?a c eo. sr = peg_Success a c eo) /\ Q sr) <=>
     (?a c eo. P (peg_Success a c eo) /\ Q (peg_Success a c eo))`,
  MESON_TAC[]);;

let peg_eval_choice = prove
 (`!(G:(A,B,C,E)peg) i0 s1 s2 f x.
     peg_eval G (i0, choice s1 s2 f) x <=>
      (?sr. peg_eval G (i0, s1) sr /\ isSuccess sr /\
            x = resultmap (f o INL) sr) \/
      (?i r eo fl fe.
         peg_eval G (i0, s1) (Failure fl fe) /\
         peg_eval G (i0, s2) (peg_Success i r eo) /\
         x = peg_Success i (f (INR r)) (optmax MAXerr (SOME (fl,fe)) eo)) \/
      (?fl1 fe1 fl2 fe2.
         peg_eval G (i0, s1) (Failure fl1 fe1) /\
         peg_eval G (i0, s2) (Failure fl2 fe2) /\
         x = UNCURRY Failure (MAXerr (fl1,fe1) (fl2,fe2)))`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [peg_eval_cases] THEN
  REWRITE_TAC[PAIR_EQ; pegsym_distinct; pegsym_inject;
              LPARSEAUX_isSuccess_EXISTS] THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM; LEFT_EXISTS_AND_THM; UNWIND_THM1;
              UNWIND_THM2; GSYM CONJ_ASSOC] THEN
  REWRITE_TAC[LPARSEAUX_EXISTS_Success; resultmap_def; o_THM] THEN
  MESON_TAC[]);;

let peg_peg_eval_choicel_NIL = prove
 (`!(G:(A,B,C,E)peg) i0 x.
     peg_eval G (i0, peg_choicel []) x <=>
     x = Failure (sloc i0) (peg_notFAIL G)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[peg_choicel_def] THEN
  GEN_REWRITE_TAC LAND_CONV [peg_eval_cases] THEN
  REWRITE_TAC[PAIR_EQ; pegsym_distinct; pegsym_inject; peg_eval_empty] THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM; LEFT_EXISTS_AND_THM; UNWIND_THM1;
              UNWIND_THM2; GSYM CONJ_ASSOC] THEN
  REWRITE_TAC[peg_eval_empty; UNWIND_THM1; UNWIND_THM2; isSuccess_def;
              isFailure_def] THEN
  MESON_TAC[]);;

let peg_peg_eval_choicel_CONS = prove
 (CASE_TERM
  `!(G:(A,B,C,E)peg) i0 h t x.
     peg_eval G (i0, peg_choicel (CONS h t)) x <=>
     ?y. peg_eval G (i0, h) y /\
         (match y with
            peg_Success i r eo -> x = peg_Success i r eo
          | Failure fl1 fe1 ->
              ?z. peg_eval G (i0, peg_choicel t) z /\
                  (match z with
                     peg_Success i r eo ->
                       x = peg_Success i r (optmax MAXerr (SOME (fl1,fe1)) eo)
                   | Failure fl2 fe2 ->
                       x = UNCURRY Failure (MAXerr (fl1,fe1) (fl2,fe2))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[peg_choicel_def] THEN
  GEN_REWRITE_TAC LAND_CONV [peg_eval_choice] THEN
  REWRITE_TAC[EXISTS_result; pegresult_CASE; LPARSEAUX_isSuccess_EXISTS;
              LPARSEAUX_EXISTS_Success; resultmap_def; o_THM; sum_CASE;
              I_THM] THEN
  MESON_TAC[]);;

let LPARSEAUX_PEG0_TAC : tactic =
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [peg0_cases] THEN
  REWRITE_TAC[pegsym_distinct; pegsym_inject] THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM; LEFT_EXISTS_AND_THM; UNWIND_THM1;
              UNWIND_THM2; GSYM CONJ_ASSOC; EXISTS_REFL] THEN
  MESON_TAC[];;

let pegfail_empty = prove
 (`!(G:(A,B,C,E)peg) r. pegfail G (empty r) <=> F`,
  LPARSEAUX_PEG0_TAC);;

let peg0_empty = prove
 (`!(G:(A,B,C,E)peg) r. peg0 G (empty r) <=> T`,
  LPARSEAUX_PEG0_TAC);;

let peg0_not = prove
 (`!(G:(A,B,C,E)peg) s r. peg0 G (not s r) <=> pegfail G s`,
  LPARSEAUX_PEG0_TAC);;

let peg0_choice = prove
 (`!(G:(A,B,C,E)peg) s1 s2 f.
     peg0 G (choice s1 s2 f) <=> peg0 G s1 \/ pegfail G s1 /\ peg0 G s2`,
  LPARSEAUX_PEG0_TAC);;

let peg_peg0_choicel = prove
 (`!(G:(A,B,C,E)peg) h t.
     (peg0 G (peg_choicel []) <=> F) /\
     (peg0 G (peg_choicel (CONS h t)) <=>
      peg0 G h \/ pegfail G h /\ peg0 G (peg_choicel t))`,
  REWRITE_TAC[peg_choicel_def; peg0_not; peg0_choice; pegfail_empty]);;

let peg0_seq = prove
 (`!(G:(A,B,C,E)peg) s1 s2 f. peg0 G (seq s1 s2 f) <=> peg0 G s1 /\ peg0 G s2`,
  LPARSEAUX_PEG0_TAC);;

let peg0_tok = prove
 (`!(G:(A,B,C,E)peg) P f. peg0 G (tok P f) <=> F`,
  LPARSEAUX_PEG0_TAC);;

let peg_peg0_pegf = prove
 (`!(G:(A,B,C,E)peg) s f. peg0 G (peg_pegf s f) <=> peg0 G s`,
  REWRITE_TAC[peg_pegf_def; peg0_seq; peg0_empty]);;

(* ------------------------------------------------------------------------- *)
(* The HOL4 [simp] theorems of this theory, for the project simpset.         *)
(* ------------------------------------------------------------------------- *)

let _ = cake_add_simps
  [isSuccess_def; isFailure_def; resultmap_def; resultmap_EQ_Failure;
   resultmap_I; sloc_thm; UNCURRY_Failure_EQ_Success; peg0_error;
   wfpeg__empty; wfpeg__any; wfpeg_tok; wfpeg__error; subexprs_def;
   subexprs_included; start_IN_Gexprs; peg_eval_empty;
   peg_peg_eval_choicel_NIL; pegfail_empty; peg0_empty; peg0_not;
   peg0_choice; peg_peg0_choicel; peg0_seq; peg0_tok; peg_peg0_pegf];;
