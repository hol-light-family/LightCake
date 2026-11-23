(* ========================================================================= *)
(* pegComplete: port of HOL4 compiler/parsing/proofs/pegCompleteScript.sml  *)
(* (CakeML v3479).                                                           *)
(* Completeness proof for the parser. If a successful parse exists,         *)
(* then the parser will find one.                                            *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "hol4/peg.ml";;
needs "hol4/grammar.ml";;
needs "hol4/NTproperties.ml";;
needs "semantics/gram.ml";;
needs "semantics/proofs/gramProps.ml";;
needs "compiler/parsing/cmlPEG.ml";;
needs "compiler/parsing/proofs/cmlNTProps.ml";;
needs "compiler/parsing/proofs/pegSound.ml";;

type_invention_error := true;;
(* HOL4 removes lift_disj_eq and lift_imp_disj from its simpset here and   *)
(* adds bindNT0_lemma (pegSound's) to it; the proofs below name what they  *)
(* use.                                                                     *)

(* Deviations from HOL4 (details at the theorems):                          *)
(* - names.tsv prefixes option_case_eq, disjImpI, Type_input_monotone,     *)
(*   Pattern_input_monotone0 and Pattern_input_monotone with pegComplete_;  *)
(*   MAP_EQ_CONS gets the prefix too (names.tsv: unique, but hol4/list.ml   *)
(*   binds the MAP_EQ_CONS of listTheory, another statement).               *)
(* - stoppers is defined by a match; stoppers_def is its clause form.       *)
(* - left_insert2 uses the helper PARSE3AUX_li2_tyop, and left_insert2_ind  *)
(*   has the hypothesis for every head of a non-empty subs.                 *)
(* - peg_eval_tok and peg_eval_NT_NONE (HOL4: values of SIMP_CONV) are      *)
(*   closed equivalences; free variables of HOL4 statements (master in      *)
(*   eapp_complete, papp_complete, dtype_complete, peg_linfix_complete)     *)
(*   are universally quantified.                                             *)
(* - completeness: the subgoals of the HOL4 proof, one per non-terminal of  *)
(*   the domain of cmlPEG, are the 69 lemmas PARSE3AUX_complete_nX, proved  *)
(*   by a symbolic evaluator of cmlPEG on the fringes of the subtrees       *)
(*   (PARSE3AUX_CCASE_TAC and variants); the induction PARSE3AUX_LEX_IND is *)
(*   on the length of the fringe, then NT_rank (the order of parsing_ind).  *)
(* - the input monotonicity lemmas invert the evaluation on the shorter     *)
(*   input and replay it on the longer one (PARSE3AUX_MONO_CASE_TAC).       *)

(* HOL4: option_case_eq [local] *)
let pegComplete_option_case_eq = prove
 (`!(optv:A option) (n:B) sf v.
     (option_CASE optv n sf = v) <=>
     optv = NONE /\ n = v \/ ?v0. optv = SOME v0 /\ sf v0 = v`,
  REWRITE_TAC[option_case_eq]);;

(* HOL4: MAP_EQ_CONS [local]; renamed, hol4/list.ml has another MAP_EQ_CONS *)
let pegComplete_MAP_EQ_CONS = prove
 (`!(f:A->B) l h t.
     MAP f l = CONS h t <=> ?h0 t0. l = CONS h0 t0 /\ f h0 = h /\ MAP f t0 = t`,
  REWRITE_TAC[LPARSEAUX_MAP_EQ_CONS]);;

let seql_cons = prove
 (`!(G:(A,B,(C)list,E)peg) i0 h t f x.
     peg_eval G (i0, seql (CONS h t) f) x <=>
       ?r. peg_eval G (i0, h) r /\
           ((?fl fe. r = Failure fl fe /\ x = r) \/
            (?i1 rh eo1 r2.
               r = peg_Success i1 rh eo1 /\ peg_eval G (i1, seql t I) r2 /\
               ((?fl fe. r2 = Failure fl fe /\ x = r2) \/
                ?i rt eopt2. r2 = peg_Success i rt eopt2 /\
                             x = peg_Success i (f (APPEND rh rt)) eopt2)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[peg_eval_seql_CONS] THEN EQ_TAC THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[RIGHT_AND_EXISTS_THM; LEFT_AND_EXISTS_THM; pegresult_distinct;
              pegresult_inject] THEN
  ASM_MESON_TAC[peg_deterministic]);;

let seql_cons_SOME = prove
 (`!(G:(A,B,(C)list,E)peg) i0 h t f i r eo.
     peg_eval G (i0, seql (CONS h t) f) (peg_Success i r eo) <=>
     ?i1 rh rt eo1.
       peg_eval G (i0, h) (peg_Success i1 rh eo1) /\
       peg_eval G (i1, seql t I) (peg_Success i rt eo) /\
       r = f (APPEND rh rt)`,
  REWRITE_TAC[PARSE3AUX_S_seql_CONS] THEN MESON_TAC[]);;

let choicel_cons = prove
 (`!(G:(A,B,(C)list,E)peg) i0 h t x.
     peg_eval G (i0, choicel (CONS h t)) x <=>
       ?r. peg_eval G (i0, h) r /\
           ((?i ptl eo. r = peg_Success i ptl eo /\ x = r) \/
            (?res2 fl1 fe1 i ptl eopt fl2 fe2.
               r = Failure fl1 fe1 /\
               peg_eval G (i0, choicel t) res2 /\
               (res2 = peg_Success i ptl eopt /\
                x = peg_Success i ptl (optmax MAXerr (SOME (fl1,fe1)) eopt) \/
                res2 = Failure fl2 fe2 /\
                x = UNCURRY Failure (MAXerr (fl1, fe1) (fl2,fe2)))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[peg_eval_choicel_CONS] THEN EQ_TAC THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[RIGHT_AND_EXISTS_THM; LEFT_AND_EXISTS_THM; pegresult_distinct;
              pegresult_inject] THEN
  ASM_MESON_TAC[peg_deterministic]);;

let choicel_cons_NONE = prove
 (`!(G:(A,B,(C)list,E)peg) i0 h t fl fe.
     peg_eval G (i0, choicel (CONS h t))
              (Failure fl fe:((A#locs)list,(C)list,E)pegresult) <=>
     ?fl1 fe1 fl2 fe2.
       peg_eval G (i0, h) (Failure fl1 fe1) /\
       peg_eval G (i0, choicel t) (Failure fl2 fe2) /\
       (Failure fl fe:((A#locs)list,(C)list,E)pegresult) =
       UNCURRY Failure (MAXerr (fl1,fe1) (fl2,fe2))`,
  REWRITE_TAC[peg_eval_choicel_CONS; pegresult_distinct] THEN MESON_TAC[]);;

let peg_eval_tok_CONS_NONE = prove
 (`!(G:(A,B,C,E)peg) h t P f fl fe.
     peg_eval G (CONS h t, peg_tok P f) (Failure fl fe) <=>
     ?tk l. h = (tk,l) /\ fl = l /\ fe = peg_tokFALSE G /\ ~P tk`,
  REWRITE_TAC[peg_eval_tok_NONE; NOT_CONS_NIL; CONS_11; EXISTS_PAIR_THM] THEN
  MESON_TAC[]);;
let _ = cake_add_simps [peg_eval_tok_CONS_NONE];;

(* HOL4: the value of SIMP_CONV (srw_ss()) [Once peg_eval_cases, EXISTS_PROD] *)
(* on peg_eval G (i0, tok P f) r                                            *)
let peg_eval_tok = prove
 (`!(G:(A,B,C,E)peg) i0 P f r.
     peg_eval G (i0, peg_tok P f) r <=>
     (?tk l t. i0 = CONS (tk,l) t /\ P tk /\ r = peg_Success t (f (tk,l)) NONE) \/
     (?tk l t. i0 = CONS (tk,l) t /\ ~P tk /\ r = Failure l (peg_tokFALSE G)) \/
     (i0 = [] /\ r = Failure (Locs EOFpt EOFpt) (peg_tokEOF G))`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [peg_eval_cases] THEN
  REWRITE_TAC[PAIR_EQ; pegsym_distinct; pegsym_inject; EXISTS_PAIR_THM] THEN
  MESON_TAC[]);;

let peg_eval_tok_NIL = prove
 (`!(G:(A,B,C,E)peg) P f r.
     peg_eval G ([], peg_tok P f) r <=> r = Failure (Locs EOFpt EOFpt) (peg_tokEOF G)`,
  REWRITE_TAC[peg_eval_tok; NOT_CONS_NIL]);;
let _ = cake_add_simps [peg_eval_tok_NIL];;

let peg_eval_tokSymP_NONE = prove
 (`!(G:(token,B,(mlptree)list,E)peg) i P fl fe.
     peg_eval G (i, tokSymP P) (Failure fl fe) <=>
     (!l tk t. i = CONS (tk, l) t ==>
               (!s. tk = SymbolT s ==> ~P s /\ fl = l /\ fe = peg_tokFALSE G) /\
               ((!s. ~(tk = SymbolT s)) ==> fl = l /\ fe = peg_tokFALSE G)) /\
     (i = [] ==> fl = Locs EOFpt EOFpt /\ fe = peg_tokEOF G)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[tokSymP_def; peg_eval_tok_NONE; OPTION_BIND_EQUALS_OPTION;
              OPTION_GUARD_EQ_THM; destSymbolT_EQ_SOME] THEN
  STRUCT_CASES_TAC(ISPEC `i:(token#locs)list` list_CASES) THEN
  REWRITE_TAC[NOT_CONS_NIL; CONS_11] THEN
  MP_TAC(ISPEC `h:token#locs` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `tk0:token` (X_CHOOSE_THEN `l0:locs` SUBST1_TAC)) THEN
  REWRITE_TAC[PAIR_EQ; FST; SND] THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM; LEFT_EXISTS_AND_THM; UNWIND_THM1;
              UNWIND_THM2; GSYM CONJ_ASSOC; EXISTS_PAIR_THM; PAIR_EQ; EXISTS_REFL] THEN
  EQ_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_MESON_TAC[];
    DISCH_THEN(MP_TAC o SPECL [`l0:locs`; `tk0:token`; `t:(token#locs)list`]) THEN
    REWRITE_TAC[] THEN
    ASM_CASES_TAC `?s. tk0 = SymbolT s` THENL
     [FIRST_X_ASSUM(X_CHOOSE_THEN `s0:mlstring` SUBST_ALL_TAC) THEN
      REWRITE_TAC[injectivity "token"] THEN MESON_TAC[];
      ASM_MESON_TAC[]]]);;
let _ = cake_add_simps [peg_eval_tokSymP_NONE];;

(* HOL4: disjImpI [local] *)
let pegComplete_disjImpI = prove
 (`!p q. ~p \/ q <=> p ==> q`,
  MESON_TAC[]);;

(* HOL4: [local] *)
let ptree_head_eq_tok0 = prove
 (`!(pt:(A,B,C)parsetree) tk. (ptree_head pt = TOK tk) <=> ?l. pt = Lf (TOK tk,l)`,
  MATCH_MP_TAC ptree_ind THEN
  REWRITE_TAC[FORALL_PAIR_THM; ptree_head_def; parsetree_distinct;
              parsetree_inject; PAIR_EQ; symbol_distinct] THEN
  MESON_TAC[]);;

let ptree_head_eq_tok = CONJ ptree_head_eq_tok0
  (CONV_RULE (BINDER_CONV (BINDER_CONV (LAND_CONV (REWR_CONV EQ_SYM_EQ))))
             ptree_head_eq_tok0);;
let _ = cake_add_simps [ptree_head_eq_tok];;

(* HOL4: the ML value cmlPEG_total *)
let PARSE3AUX_cmlPEG_total =
  MATCH_MP (ISPEC `cmlPEG` peg_eval_total) PEG_wellformed;;

(* HOL4: [local] *)
let FLAT_EQ_CONS = prove
 (`!(ll:(A list)list) h t.
     FLAT ll = CONS h t <=>
     ?p t0 s. ll = APPEND (APPEND p [CONS h t0]) s /\
              ALL ((=) []) p /\ FLAT (CONS t0 s) = t`,
  MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
   [REWRITE_TAC[FLAT; NOT_CONS_NIL] THEN MESON_TAC[APPEND_EQ_NIL; NOT_CONS_NIL];
    ALL_TAC] THEN
  X_GEN_TAC `a:A list` THEN X_GEN_TAC `ll:(A list)list` THEN DISCH_TAC THEN
  X_GEN_TAC `h:A` THEN X_GEN_TAC `t:A list` THEN REWRITE_TAC[FLAT] THEN
  EQ_TAC THENL
   [STRUCT_CASES_TAC(ISPEC `a:A list` list_CASES) THEN
    REWRITE_TAC[APPEND; CONS_11] THENL
     [ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `p:(A list)list` (X_CHOOSE_THEN `t0:A list`
        (X_CHOOSE_THEN `s:(A list)list` STRIP_ASSUME_TAC))) THEN
      MAP_EVERY EXISTS_TAC [`CONS ([]:A list) p`; `t0:A list`; `s:(A list)list`] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[FLAT]) THEN ASM_REWRITE_TAC[ALL; APPEND];
      STRIP_TAC THEN
      MAP_EVERY EXISTS_TAC [`[]:(A list)list`; `t':A list`; `ll:(A list)list`] THEN
      ASM_REWRITE_TAC[ALL; FLAT; APPEND]];
    DISCH_THEN(X_CHOOSE_THEN `p:(A list)list` (X_CHOOSE_THEN `t0:A list`
      (X_CHOOSE_THEN `s:(A list)list` STRIP_ASSUME_TAC))) THEN
    POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
    STRUCT_CASES_TAC(ISPEC `p:(A list)list` list_CASES) THEN
    REWRITE_TAC[APPEND; CONS_11; ALL; FLAT] THEN REPEAT STRIP_TAC THEN
    RVEQ_TAC THEN ASM_REWRITE_TAC[APPEND] THEN
    MAP_EVERY EXISTS_TAC [`t':(A list)list`; `t0:A list`; `s:(A list)list`] THEN
    ASM_REWRITE_TAC[FLAT]]);;

let rfirstSet_nonempty_fringe = prove
 (`!(G:(A,B)grammar) (pt:(A,B,locs)parsetree) t l rest.
     real_fringe pt = CONS (TOK t, l) rest /\ valid_lptree G pt ==>
     t IN firstSet G [ptree_head pt]`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC firstSet_nonempty_fringe THEN
  EXISTS_TAC `MAP FST (rest:((A,B)symbol#locs)list)` THEN
  ASM_REWRITE_TAC[ptree_fringe_real_fringe; MAP] THEN
  ASM_MESON_TAC[valid_lptree_def]);;

let peg_respects_firstSets = prove
 (`!N i0 t l.
     ~(t IN firstSet cmlG [NT N]) /\ ~peg0 cmlPEG (peg_nt N I) /\
     peg_nt N I IN Gexprs cmlPEG ==>
     ?fl fe. peg_eval cmlPEG (CONS (t,l) i0, peg_nt N I) (Failure fl fe)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `CONS (t:token,l:locs) i0` o
              MATCH_MP PARSE3AUX_cmlPEG_total) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:((token#locs)list,(mlptree)list,(char)list)pegresult`
    MP_TAC) THEN
  STRUCT_CASES_TAC(ISPEC `r:((token#locs)list,(mlptree)list,(char)list)pegresult`
                   pegresult_nchotomy) THENL
   [ALL_TAC; MESON_TAC[]] THEN
  DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (MATCH_MP not_peg0_LENGTH_decreases
    (ASSUME `~peg0 cmlPEG (peg_nt N I)`))) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP peg_sound) THEN
  DISCH_THEN(X_CHOOSE_THEN `pt:mlptree` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `real_fringe (pt:mlptree)` list_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC
   (X_CHOOSE_THEN `h:(token,MMLnonT)symbol#locs`
     (X_CHOOSE_THEN `rest:((token,MMLnonT)symbol#locs)list` ASSUME_TAC))) THEN
  FIRST_X_ASSUM(fun th ->
    if is_eq(concl th) && lhs(concl th) = `real_fringe (pt:mlptree)`
    then (RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th)
    else failwith "real_fringe") THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MAP; APPEND; CONS_11; PAIR_MAP_THM; I_THM]) THENL
   [FIRST_X_ASSUM(MP_TAC o AP_TERM `LENGTH:((token,MMLnonT)symbol#locs)list->num` o
      check (fun th -> is_eq(concl th) && is_cons(lhs(concl th)))) THEN
    REWRITE_TAC[LENGTH; LENGTH_MAP] THEN ARITH_TAC;
    DISCH_THEN(K ALL_TAC) THEN
    SUBGOAL_THEN `t IN firstSet cmlG [NT N]` (fun th -> ASM_MESON_TAC[th]) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      try lhand(concl th) = `ptree_head (pt:mlptree)` with Failure _ -> false)) THEN
    MATCH_MP_TAC rfirstSet_nonempty_fringe THEN
    MAP_EVERY EXISTS_TAC [`l:locs`; `rest:((token,MMLnonT)symbol#locs)list`] THEN
    ASM_MESON_TAC[]]);;

let fFail_def = new_specification ["fFAIL1"; "fFAIL2"]
 (prove
  (`?fFAIL1 fFAIL2.
      !N i0 t l.
        ~(t IN firstSet cmlG [NT N]) /\ ~peg0 cmlPEG (peg_nt N I) /\
        peg_nt N I IN Gexprs cmlPEG ==>
        peg_eval cmlPEG (CONS (t,l) i0, peg_nt N I)
                 (Failure (fFAIL1 N i0 t l) (fFAIL2 N i0 t l))`,
   REWRITE_TAC[GSYM SKOLEM_THM; RIGHT_EXISTS_IMP_THM] THEN
   REWRITE_TAC[peg_respects_firstSets]));;

let peg_respects_firstSets_rwt = prove
 (`!N i0 t l.
     ~(t IN firstSet cmlG [NT N]) /\ ~peg0 cmlPEG (peg_nt N I) /\
     peg_nt N I IN Gexprs cmlPEG ==>
     !sr'. peg_eval cmlPEG (CONS (t,l) i0, peg_nt N I) sr' <=>
           sr' = Failure (fFAIL1 N i0 t l) (fFAIL2 N i0 t l)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP fFail_def) THEN
  MESON_TAC[peg_deterministic]);;

let peg_eval_NIL_NT = prove
 (`!N i r eo.
     peg_eval cmlPEG ([], peg_nt N I) (peg_Success i r eo) ==>
     nullable cmlG [NT N] /\ i = []`,
  REPEAT GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP peg_sound) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MAP]) THEN
  FIRST_X_ASSUM(MP_TAC o SYM o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `[]:((token,MMLnonT)symbol#locs)list`)) THEN
  REWRITE_TAC[MAP; APPEND_EQ_NIL; MAP_EQ_NIL] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`cmlG`; `NT N:(token,MMLnonT)symbol`]
         rfringe_length_not_nullable) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `pt:mlptree`) THEN
  ASM_REWRITE_TAC[LENGTH] THEN ARITH_TAC);;

let not_nullable_input_CONS = prove
 (`!N i0 i r eo.
     ~nullable cmlG [NT N] ==>
     peg_eval cmlPEG (i0, peg_nt N I) (peg_Success i r eo) ==>
     ?ht l t. i0 = CONS (ht,l) t /\ LENGTH i <= LENGTH t`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  STRUCT_CASES_TAC(ISPEC `i0:(token#locs)list` list_CASES) THENL
   [ASM_MESON_TAC[peg_eval_NIL_NT]; ALL_TAC] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP peg_sound) THEN
  MP_TAC(ISPEC `h:token#locs` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `tk:token` (X_CHOOSE_THEN `lc:locs` SUBST_ALL_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`tk:token`; `lc:locs`; `t:(token#locs)list`] THEN
  REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`cmlG`; `NT N:(token,MMLnonT)symbol`]
         rfringe_length_not_nullable) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `pt:mlptree`) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `LENGTH:((token,MMLnonT)symbol#locs)list->num` o
    check (fun th -> is_eq(concl th) && is_comb(lhs(concl th)) &&
                     try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "MAP"
                     with Failure _ -> false)) THEN
  REWRITE_TAC[LENGTH; LENGTH_MAP; LENGTH_APPEND] THEN ARITH_TAC);;

let not_nullable_seql_input_CONS = prove
 (`!N i0 rest f i r eo.
     ~nullable cmlG [NT N] ==>
     peg_eval cmlPEG (i0, seql (CONS (peg_nt N I) rest) f) (peg_Success i r eo) ==>
     ?ht l t. i0 = CONS (ht,l) t /\ LENGTH i <= LENGTH t`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[seql_cons_SOME] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (MATCH_MP not_nullable_input_CONS
    (ASSUME `~nullable cmlG [NT N]`))) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP length_no_greater) THEN
  MESON_TAC[LE_TRANS]);;

let sym2peg_def = cake_def
  `(sym2peg (TOK tk) = tokeq tk:(token,MMLnonT,(mlptree)list,E)pegsym) /\
   (sym2peg (NT N) = peg_nt N I)`;;

let not_peg0_peg_eval_NIL_NONE = prove
 (`!(G:(A,B,C,E)peg) sym.
     ~peg0 G sym /\ sym IN Gexprs G /\ wfG G ==>
     ?fl fe. peg_eval G ([], sym) (Failure fl fe)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `G:(A,B,C,E)peg` peg_eval_total) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`[]:(A#locs)list`; `sym:(A,B,C,E)pegsym`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:((A#locs)list,C,E)pegresult` MP_TAC) THEN
  STRUCT_CASES_TAC(ISPEC `r:((A#locs)list,C,E)pegresult` pegresult_nchotomy) THENL
   [DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP (MATCH_MP not_peg0_LENGTH_decreases
      (ASSUME `~peg0 (G:(A,B,C,E)peg) sym`))) THEN
    REWRITE_TAC[LENGTH] THEN ARITH_TAC;
    MESON_TAC[]]);;

(* HOL4: [local] *)
let list_case_lemma = prove
 (`!(x:A) a (f:B->(B)list->(A)list).
     ([x] = list_CASE a [] f) <=> ~(a = []) /\ [x] = f (HD a) (TL a)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[list_CASE; NOT_CONS_NIL; HD; TL]);;
(* only the subs = [x] and subs = [x;y] cases are relevant *)
let left_insert1_def = cake_def
  `(left_insert1 (pt:(A,B,locs)parsetree) (Lf (tk, l)) =
      Lf (tk, merge_locs (ptree_loc pt) l)) /\
   (left_insert1 pt (Nd (n,l0) subs) =
      match subs with
        [] -> Nd (n, merge_locs (ptree_loc pt) l0) [pt]
      | [x] -> mkNd n [mkNd n [pt]; x]
      | CONS x xs -> mkNd n (CONS (left_insert1 pt x) xs))`;;

let left_insert1_ind = cake_ind "left_insert1";;

let leftmost_def = cake_def
  `(leftmost (Lf s) = Lf s:(token,MMLnonT,C)parsetree) /\
   (leftmost (Nd (n,l) args) =
      if ~(args = []) /\ n = INL nTbase then HD args
      else match args with
             [] -> Nd (n,l) args
           | CONS h _ -> leftmost h)`;;

(* pt is a Tbase, and n will be DType all the way down.  The kit cannot   *)
(* prove the termination of the HOL4 clauses (a nested pattern on the      *)
(* argument of the recursive call), so left_insert2 is defined through the *)
(* test PARSE3AUX_li2_tyop and the HOL4 equation is proved from it.        *)

let PARSE3AUX_li2_tyop_def = cake_def
  `PARSE3AUX_li2_tyop (subs:((A,B,C)parsetree)list) =
     match subs with [Nd _ [tyop]] -> SOME tyop | _ -> NONE`;;

let PARSE3AUX_left_insert2_def = cake_def
  `(left_insert2 (pt:(A,B,locs)parsetree) (Lf (tk, l)) =
      Lf (tk, merge_locs (ptree_loc pt) l)) /\
   (left_insert2 pt (Nd (n, l0) subs) =
      match subs with
        [] -> Nd (n,merge_locs (ptree_loc pt) l0) [pt]
      | CONS x ys ->
          (match PARSE3AUX_li2_tyop subs with
             SOME tyop -> mkNd n [mkNd n [pt]; tyop]
           | NONE -> mkNd n (CONS (left_insert2 pt x) ys)))`;;

let left_insert2_def = prove
 (CASE_TERM
  `(!(pt:(A,B,locs)parsetree) tk l.
      left_insert2 pt (Lf (tk, l)) = Lf (tk, merge_locs (ptree_loc pt) l)) /\
   (!(pt:(A,B,locs)parsetree) n l0 subs.
      left_insert2 pt (Nd (n, l0) subs) =
      match subs with
        [] -> Nd (n,merge_locs (ptree_loc pt) l0) [pt]
      | [Nd _ [tyop]] -> mkNd n [mkNd n [pt]; tyop]
      | CONS x ys -> mkNd n (CONS (left_insert2 pt x) ys))`,
  REWRITE_TAC[PARSE3AUX_left_insert2_def] THEN REPEAT GEN_TAC THEN
  CASES_ON `subs:((A,B,locs)parsetree)list` THEN
  CASE_REWRITE_TAC[PARSE3AUX_li2_tyop_def] THEN
  EVERY_CASE_TAC THEN CASE_REWRITE_TAC[]);;

(* HOL4: left_insert2_ind; here with the hypothesis for every head x of a *)
(* non-empty subs (the cases [Nd _ [tyop]] included)                       *)
let left_insert2_ind = prove
 (`!P:(A,B,locs)parsetree->(A,B,locs)parsetree->bool.
       (!pt tk l. P pt (Lf (tk,l))) /\
       (!pt n l0 subs. (!x ys. subs = CONS x ys ==> P pt x)
                       ==> P pt (Nd (n,l0) subs))
       ==> !x1 x2. P x1 x2`,
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "lf") (LABEL_TAC "nd")) THEN
  SUBGOAL_THEN `!(x2:(A,B,locs)parsetree) (x1:(A,B,locs)parsetree).
                 (P:(A,B,locs)parsetree->(A,B,locs)parsetree->bool) x1 x2`
    (fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC ptree_ind THEN CONJ_TAC THENL
   [REWRITE_TAC[FORALL_PAIR_THM] THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
    REPEAT GEN_TAC THEN USE_THEN "nd" MATCH_MP_TAC THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `x:(A,B,locs)parsetree`) THEN
    ASM_REWRITE_TAC[MEM] THEN SIMP_TAC[]]);;

let left_insert_def = cake_def_wf
  `MEASURE (\x:(A,B,locs)parsetree#(B+num)#(A,B,locs)parsetree#(A,B,locs)parsetree.
              parsetree_size (\x:A. 0) (\x:B. 0) (\x:locs. 0) (FST x))`
  TERM_TAC
  `(left_insert (Lf (tk,l)) (p:B+num) (sep:(A,B,locs)parsetree) c =
      Lf (tk,merge_locs (ptree_loc c) l)) /\
   (left_insert (Nd (n,l) subs) p sep c =
      if ~(n = p) then Nd (n,merge_locs (ptree_loc c) l) subs
      else match subs with
             [] -> Nd (n, merge_locs (ptree_loc c) l) subs
           | CONS c0 r ->
               (match r with
                  [] -> mkNd p [mkNd p [c]; sep; c0]
                | CONS s' r2 ->
                    (match r2 with
                       [] -> Nd (n, merge_locs (ptree_loc c) l) subs
                     | CONS c' r3 ->
                         (match r3 with
                            [] -> mkNd p [left_insert c0 p sep c; s'; c']
                          | CONS _ _ -> Nd (n, merge_locs (ptree_loc c) l) subs))))`;;

let left_insert_ind = cake_ind "left_insert";;

let left_insert1_FOLDL = prove
 (`!(pt:(A,B,locs)parsetree) P acc arg.
     left_insert1 pt (FOLDL (\a b. mkNd (INL P) [a; b]) acc arg) =
     FOLDL (\a b. mkNd (INL P) [a; b]) (left_insert1 pt acc) arg`,
  GEN_TAC THEN GEN_TAC THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[FOLDL] THEN GEN_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[mkNd_def; left_insert1_def] THEN CASE_REWRITE_TAC[]);;

(* HOL4 exports ptree_loc_def (grammar) as a rewrite here *)
let _ = cake_add_simps [ptree_loc_def];;

let ptree_loc_mkNd = prove
 (`!n (subs:((A,B,locs)parsetree)list).
     ptree_loc (mkNd n subs) = ptree_list_loc subs`,
  REWRITE_TAC[mkNd_def; ptree_loc_def]);;
let _ = cake_add_simps [ptree_loc_mkNd];;

let merge_list_locs_HDLAST = prove
 (`!t h. merge_list_locs (CONS h t) = merge_locs h (LAST (CONS h t))`,
  LIST_INDUCT_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[merge_list_locs_def; LAST] THEN
    STRUCT_CASES_TAC(ISPEC `h:locs` (cases "locs")) THEN
    REWRITE_TAC[merge_locs_def];
    ALL_TAC] THEN
  GEN_TAC THEN MP_TAC(ISPEC `t:locs list` list_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC
    (X_CHOOSE_THEN `h2:locs` (X_CHOOSE_THEN `t2:locs list` SUBST_ALL_TAC))) THEN
  ASM_REWRITE_TAC[merge_list_locs_def; LAST; NOT_CONS_NIL]);;

let PARSE3AUX_merge_locs_LR = prove
 (`(!x y z. merge_locs (merge_locs x y) z = merge_locs x z) /\
   (!x y z. merge_locs x (merge_locs y z) = merge_locs x z)`,
  CONJ_TAC THEN REPEAT GEN_TAC THEN
  MAP_EVERY (fun t -> STRUCT_CASES_TAC(ISPEC t (cases "locs")))
    [`x:locs`; `y:locs`; `z:locs`] THEN
  REWRITE_TAC[merge_locs_def]);;

let ptree_loc_left_insert1 = prove
 (`!(subpt:(A,B,locs)parsetree) pt.
     valid_locs pt ==>
     ptree_loc (left_insert1 subpt pt) =
     merge_locs (ptree_loc subpt) (ptree_loc pt)`,
  MATCH_MP_TAC left_insert1_ind THEN CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[left_insert1_def; ptree_loc_def] THEN
  DISCH_TAC THEN CASES_ON `subs:((A,B,locs)parsetree)list` THEN
  CASE_REWRITE_TAC[ptree_loc_def] THEN
  CASES_ON `a1:((A,B,locs)parsetree)list` THEN
  CASE_REWRITE_TAC[valid_locs_def; ptree_loc_mkNd; ptree_list_loc_def; MAP;
                   merge_list_locs_def; ptree_loc_def] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a0':(A,B,locs)parsetree`;
    `a1':((A,B,locs)parsetree)list`; `a0:(A,B,locs)parsetree`]) THEN
  ASM_SIMP_TAC[MEM] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[merge_list_locs_HDLAST; LAST; NOT_CONS_NIL; PARSE3AUX_merge_locs_LR]);;

let leftLoc_def = cake_def `leftLoc (Locs l1 _) = l1`;;
let _ = cake_add_simps [leftLoc_def];;

let rightLoc_def = cake_def `rightLoc (Locs _ l2) = l2`;;
let _ = cake_add_simps [rightLoc_def];;

let merge_locs_LR = prove
 (`!l1 l2. merge_locs l1 l2 = Locs (leftLoc l1) (rightLoc l2)`,
  REPEAT GEN_TAC THEN
  MAP_EVERY (fun t -> STRUCT_CASES_TAC(ISPEC t (cases "locs"))) [`l1:locs`; `l2:locs`] THEN
  REWRITE_TAC[merge_locs_def; leftLoc_def; rightLoc_def]);;

let leftLoc_merge_locs = prove
 (`!l1 l2. leftLoc (merge_locs l1 l2) = leftLoc l1`,
  REWRITE_TAC[merge_locs_LR; leftLoc_def]);;
let _ = cake_add_simps [leftLoc_merge_locs];;

let rightLoc_merge_locs = prove
 (`!l1 l2. rightLoc (merge_locs l1 l2) = rightLoc l2`,
  REWRITE_TAC[merge_locs_LR; rightLoc_def]);;
let _ = cake_add_simps [rightLoc_merge_locs];;

let PARSE3AUX_MAP_TKI_SING = prove
 (`!pf (s:(token,MMLnonT)symbol) (l:locs).
     [(s,l)] = MAP (TOK ## I) pf ==> ?t. s = TOK t`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; NOT_CONS_NIL; CONS_11] THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MP_TAC(ISPEC `h:token#locs` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:token` (X_CHOOSE_THEN `b:locs` SUBST1_TAC)) THEN
  REWRITE_TAC[PAIR_MAP_THM; I_THM; PAIR_EQ] THEN MESON_TAC[]);;

let PARSE3AUX_left_insert1_mkNd1 = prove
 (`!(x:(A,B,locs)parsetree) n a.
     left_insert1 x (mkNd n [a]) = mkNd n [mkNd n [x]; a]`,
  REWRITE_TAC[mkNd_def; left_insert1_def] THEN CASE_REWRITE_TAC[]);;

let PARSE3AUX_left_insert1_mkNd2 = prove
 (`!(x:(A,B,locs)parsetree) n a b.
     left_insert1 x (mkNd n [a; b]) = mkNd n [left_insert1 x a; b]`,
  REWRITE_TAC[mkNd_def; left_insert1_def] THEN CASE_REWRITE_TAC[]);;

let PARSE3AUX_Nd_mkNd = prove
 (`!n (subs:((A,B,locs)parsetree)list).
     Nd (n, merge_list_locs (MAP ptree_loc subs)) subs = mkNd n subs`,
  REWRITE_TAC[mkNd_def; ptree_list_loc_def]);;

(* the assumption MAP ptree_head subs IN FAPPLY (grammar_rules cmlG) n,     *)
(* with the rule of n unfolded                                              *)

let PARSE3AUX_is_grule_fact tm =
  try fst(dest_const(fst(strip_comb tm))) = "IN" &&
      fst(dest_const(fst(strip_comb(rand tm)))) = "FAPPLY"
  with Failure _ -> false;;

let PARSE3AUX_GRULE_CASES_TAC : tactic =
  FIRST_X_ASSUM(MP_TAC o check (PARSE3AUX_is_grule_fact o concl)) THEN
  CONV_TAC(ONCE_DEPTH_CONV PARSE3AUX_GRULE_CONV) THEN
  REWRITE_TAC[IN_INSERT; IN_UNION; NOT_IN_EMPTY; IN_ELIM_THM; pegComplete_MAP_EQ_CONS;
              MAP_EQ_NIL] THEN
  STRIP_TAC THEN RVEQ_TAC;;

let PARSE3AUX_GRULE_MEM_TAC : tactic =
  CONV_TAC(ONCE_DEPTH_CONV PARSE3AUX_GRULE_CONV) THEN
  REWRITE_TAC[IN_INSERT; IN_UNION; NOT_IN_EMPTY; IN_ELIM_THM] THEN
  CASE_REWRITE_TAC[];;

(* Problem with Eapp is that it's left-recursive in the grammar :           *)
(*   Eapp ::= Eapp Ebase | Ebase                                            *)
(* but the PEG parses it by calling Ebase >> rpt Ebase, and then doing a    *)
(* FOLDL on the resulting list to assemble it into a valid parse-tree.      *)
(* (HOL4's comment.)  If we have an Eapp (pt) to the left and an Ebase      *)
(* (bpt) to the right, we can reassociate: an Ebase bpt' to the left and   *)
(* an Eapp pt' to the right, such that left-inserting the former into the  *)
(* latter gives back what we started with.                                  *)

let eapp_reassociated = prove
 (`!pt bpt pf bf.
     valid_lptree cmlG pt /\ ptree_head pt = NT (INL nEapp) /\
     real_fringe pt = MAP (TOK ## I) pf /\
     valid_lptree cmlG bpt /\ ptree_head bpt = NT (INL nEbase) /\
     real_fringe bpt = MAP (TOK ## I) bf ==>
     ?pt' bpt'.
       valid_lptree cmlG pt' /\ valid_lptree cmlG bpt' /\
       leftLoc (ptree_loc bpt') = leftLoc (ptree_loc pt) /\
       rightLoc (ptree_loc pt') = rightLoc (ptree_loc bpt) /\
       ptree_head pt' = NT (INL nEapp) /\ ptree_head bpt' = NT (INL nEbase) /\
       APPEND (real_fringe bpt') (real_fringe pt') =
         MAP (TOK ## I) (APPEND pf bf) /\
       mkNd (INL nEapp) [pt; bpt] = left_insert1 bpt' pt'`,
  MATCH_MP_TAC ptree_ind THEN CONJ_TAC THENL
   [REWRITE_TAC[FORALL_PAIR_THM; ptree_head_def; real_fringe_def] THEN
    MESON_TAC[PARSE3AUX_MAP_TKI_SING; symbol_distinct];
    ALL_TAC] THEN
  X_GEN_TAC `subs:(mlptree)list` THEN DISCH_THEN(LABEL_TAC "ih") THEN
  REWRITE_TAC[FORALL_PAIR_THM; ptree_head_def; real_fringe_def; valid_lptree_thm;
              symbol_inject] THEN
  MAP_EVERY X_GEN_TAC [`n:MMLnonT+num`; `l:locs`; `bpt:mlptree`;
                       `pf:(token#locs)list`; `bf:(token#locs)list`] THEN
  STRIP_TAC THEN RVEQ_TAC THEN PARSE3AUX_GRULE_CASES_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th ->
      try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "FLAT"
      with Failure _ -> false)) THEN
    REWRITE_TAC[MAP; FLAT; APPEND_NIL] THEN
    GEN_REWRITE_TAC LAND_CONV [EQ_SYM_EQ] THEN
    REWRITE_TAC[LPARSEAUX_MAP_EQ_APPEND] THEN
    DISCH_THEN(X_CHOOSE_THEN `pf0:(token#locs)list`
      (X_CHOOSE_THEN `bf0:(token#locs)list`
        (CONJUNCTS_THEN2 SUBST_ALL_TAC (CONJUNCTS_THEN (ASSUME_TAC o SYM))))) THEN
    USE_THEN "ih" (MP_TAC o SPECL [`h0':mlptree`; `pf0:(token#locs)list`;
                                   `bf0:(token#locs)list`] o
      REWRITE_RULE[MEM] o SPEC `h0:mlptree`) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[MEM]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `ppt':mlptree` (X_CHOOSE_THEN `bpt':mlptree`
      STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`mkNd (INL nEapp) [ppt'; bpt]:mlptree`; `bpt':mlptree`] THEN
    SUBGOAL_THEN
     `Nd (INL nEapp,merge_list_locs [ptree_loc h0; ptree_loc h0']) [h0; h0'] =
      mkNd (INL nEapp) [h0; h0']:mlptree` SUBST1_TAC THENL
     [REWRITE_TAC[mkNd_def; ptree_list_loc_def; MAP]; ALL_TAC] THEN
    REWRITE_TAC[PARSE3AUX_left_insert1_mkNd2] THEN
    ASM_REWRITE_TAC[valid_lptree_mkNd; ptree_head_mkNd; real_fringe_mkNd;
      ptree_loc_mkNd; ptree_list_loc_def; ptree_loc_def; MAP; FLAT; APPEND_NIL;
      merge_list_locs_def; leftLoc_merge_locs; rightLoc_merge_locs; MAP_APPEND;
      MEM; PARSE1AUX_cmlG_FDOM_INL] THEN
    REPEAT CONJ_TAC THENL
     [PARSE3AUX_GRULE_MEM_TAC;
      REWRITE_TAC[DISJ_IMP_THM; FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[APPEND_ASSOC] THEN ASM_REWRITE_TAC[MAP_APPEND]];
    MAP_EVERY EXISTS_TAC [`mkNd (INL nEapp) [bpt]:mlptree`; `h0:mlptree`] THEN
    REWRITE_TAC[PARSE3AUX_Nd_mkNd; PARSE3AUX_left_insert1_mkNd1] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MAP; FLAT; APPEND_NIL; MEM]) THEN
    ASM_REWRITE_TAC[valid_lptree_mkNd; ptree_head_mkNd; real_fringe_mkNd;
      ptree_loc_mkNd; ptree_list_loc_SING; MAP; FLAT; APPEND_NIL; MAP_APPEND;
      MEM; PARSE1AUX_cmlG_FDOM_INL; DISJ_IMP_THM; FORALL_AND_THM;
      FORALL_UNWIND_THM2] THEN
    PARSE3AUX_GRULE_MEM_TAC THEN ASM_MESON_TAC[]]);;

(* split the pair variables v of Nd v subs in the goal and assumptions *)

let PARSE3AUX_dest_pair_ty ty =
  match dest_type ty with ("prod",[a;b]) -> a,b | _ -> failwith "dest_pair_ty";;

let PARSE3AUX_SPLIT_ND_PAIRS_TAC : tactic = fun (asl,w as g) ->
  let tms = w :: map (concl o snd) asl in
  let vs = setify (flat (map (fun t ->
    map (fun t -> rand(rator t))
      (find_terms (fun t -> is_comb t && is_comb(rator t) &&
                            is_const(rator(rator t)) &&
                            fst(dest_const(rator(rator t))) = "Nd" &&
                            is_var(rand(rator t))) t)) tms)) in
  (MAP_EVERY (fun v ->
     let a,b = PARSE3AUX_dest_pair_ty (type_of v) in
     let x' = mk_var(fst(dest_var v)^"_1",a)
     and y' = mk_var(fst(dest_var v)^"_2",b) in
     MP_TAC (ISPEC v PAIR_SURJECTIVE) THEN
     DISCH_THEN(X_CHOOSE_THEN x' (X_CHOOSE_THEN y' SUBST_ALL_TAC))) vs) g;;

let ptree_loc_left_insert2 = prove
 (`!(bpt:(A,B,locs)parsetree) dpt.
     valid_locs dpt ==>
     ptree_loc (left_insert2 bpt dpt) =
     merge_locs (ptree_loc bpt) (ptree_loc dpt)`,
  MATCH_MP_TAC left_insert2_ind THEN CONJ_TAC THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[left_insert2_def; ptree_loc_def]; ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "ih") THEN REWRITE_TAC[valid_locs_def] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[left_insert2_def; ptree_loc_def] THEN
  CASES_ON `subs:((A,B,locs)parsetree)list` THEN
  CASE_REWRITE_TAC[ptree_loc_def; ptree_loc_mkNd; ptree_list_loc_def; MAP] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MEM; DISJ_IMP_THM; FORALL_AND_THM;
                              FORALL_UNWIND_THM2]) THEN
  USE_THEN "ih" (MP_TAC o SPECL [`a0:(A,B,locs)parsetree`;
                                 `a1:((A,B,locs)parsetree)list`]) THEN
  REWRITE_TAC[] THEN DISCH_TAC THEN
  EVERY_CASE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[valid_locs_def; MEM; MAP; ptree_loc_def]) THEN
  ASM_SIMP_TAC[ptree_loc_def; ptree_loc_mkNd; ptree_list_loc_def; MAP;
               merge_list_locs_def; merge_list_locs_HDLAST; LAST; NOT_CONS_NIL;
               PARSE3AUX_merge_locs_LR; valid_locs_def; MEM] THEN
  PARSE3AUX_SPLIT_ND_PAIRS_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[valid_locs_def; MEM; MAP; ptree_loc_def;
                              merge_list_locs_def]) THEN
  ASM_REWRITE_TAC[ptree_loc_def]);;

let PARSE3AUX_left_insert2_mkNd2 = prove
 (`!(x:(A,B,locs)parsetree) n a b.
     left_insert2 x (mkNd n [a; b]) = mkNd n [left_insert2 x a; b]`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mkNd_def; left_insert2_def] THEN
  CASE_REWRITE_TAC[] THEN EVERY_CASE_TAC THEN CASE_REWRITE_TAC[]);;

let left_insert2_FOLDL = prove
 (`!(pt:(A,B,locs)parsetree) P acc arg.
     left_insert2 pt (FOLDL (\a b. mkNd (INL P) [a; b]) acc arg) =
     FOLDL (\a b. mkNd (INL P) [a; b]) (left_insert2 pt acc) arg`,
  GEN_TAC THEN GEN_TAC THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[FOLDL; PARSE3AUX_left_insert2_mkNd2]);;

let PARSE3AUX_leftmost_DType = prove
 (`!(c:mlptree) cs. leftmost (mkNd (INL nDType) (CONS c cs)) = leftmost c`,
  REWRITE_TAC[mkNd_def; leftmost_def; NOT_CONS_NIL; HD] THEN
  CASE_REWRITE_TAC[]);;

let PARSE3AUX_leftmost_Tbase = prove
 (`!(x:mlptree) xs. leftmost (mkNd (INL nTbase) (CONS x xs)) = x`,
  REWRITE_TAC[mkNd_def; leftmost_def; NOT_CONS_NIL; HD]);;

let PARSE3AUX_left_insert2_mkNd1 = prove
 (`!(x:(A,B,locs)parsetree) n m tyop.
     left_insert2 x (mkNd n [mkNd m [tyop]]) = mkNd n [mkNd n [x]; tyop]`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mkNd_def; left_insert2_def] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[GSYM mkNd_def]);;

(* the situation with DType is similar to that with Eapp and Ebase:         *)
(*   DType ::= DType TyOp | Tbase                                           *)
(* (HOL4's comment, abridged)                                               *)

let dtype_reassociated = prove
 (`!pt bpt pf bf.
     valid_lptree cmlG pt /\ ptree_head pt = NT (INL nDType) /\
     real_fringe pt = MAP (TOK ## I) pf /\
     valid_lptree cmlG bpt /\ ptree_head bpt = NT (INL nTyOp) /\
     real_fringe bpt = MAP (TOK ## I) bf ==>
     ?pt' bpt'.
       valid_lptree cmlG pt' /\ valid_lptree cmlG bpt' /\
       valid_lptree cmlG (leftmost pt') /\
       ptree_head (leftmost pt') = NT (INL nTyOp) /\
       ptree_head pt' = NT (INL nDType) /\ ptree_head bpt' = NT (INL nTbase) /\
       APPEND (real_fringe bpt') (real_fringe pt') =
         MAP (TOK ## I) (APPEND pf bf) /\
       leftLoc (ptree_loc bpt') = leftLoc (ptree_loc pt) /\
       rightLoc (ptree_loc pt') = rightLoc (ptree_loc bpt) /\
       mkNd (INL nDType) [pt; bpt] = left_insert2 bpt' pt'`,
  MATCH_MP_TAC ptree_ind THEN CONJ_TAC THENL
   [REWRITE_TAC[FORALL_PAIR_THM; ptree_head_def; real_fringe_def] THEN
    MESON_TAC[PARSE3AUX_MAP_TKI_SING; symbol_distinct];
    ALL_TAC] THEN
  X_GEN_TAC `subs:(mlptree)list` THEN DISCH_THEN(LABEL_TAC "ih") THEN
  REWRITE_TAC[FORALL_PAIR_THM; ptree_head_def; real_fringe_def; valid_lptree_thm;
              symbol_inject] THEN
  MAP_EVERY X_GEN_TAC [`n:MMLnonT+num`; `l:locs`; `bpt:mlptree`;
                       `pf:(token#locs)list`; `bf:(token#locs)list`] THEN
  STRIP_TAC THEN RVEQ_TAC THEN PARSE3AUX_GRULE_CASES_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th ->
      try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "FLAT"
      with Failure _ -> false)) THEN
    REWRITE_TAC[MAP; FLAT; APPEND_NIL] THEN
    GEN_REWRITE_TAC LAND_CONV [EQ_SYM_EQ] THEN
    REWRITE_TAC[LPARSEAUX_MAP_EQ_APPEND] THEN
    DISCH_THEN(X_CHOOSE_THEN `pf0:(token#locs)list`
      (X_CHOOSE_THEN `bf0:(token#locs)list`
        (CONJUNCTS_THEN2 SUBST_ALL_TAC (CONJUNCTS_THEN (ASSUME_TAC o SYM))))) THEN
    USE_THEN "ih" (MP_TAC o SPECL [`h0':mlptree`; `pf0:(token#locs)list`;
                                   `bf0:(token#locs)list`] o
      REWRITE_RULE[MEM] o SPEC `h0:mlptree`) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[MEM]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `ppt':mlptree` (X_CHOOSE_THEN `bpt':mlptree`
      STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`mkNd (INL nDType) [ppt'; bpt]:mlptree`; `bpt':mlptree`] THEN
    SUBGOAL_THEN
     `Nd (INL nDType,merge_list_locs [ptree_loc h0; ptree_loc h0']) [h0; h0'] =
      mkNd (INL nDType) [h0; h0']:mlptree` SUBST1_TAC THENL
     [REWRITE_TAC[mkNd_def; ptree_list_loc_def; MAP]; ALL_TAC] THEN
    REWRITE_TAC[PARSE3AUX_left_insert2_mkNd2; PARSE3AUX_leftmost_DType] THEN
    ASM_REWRITE_TAC[valid_lptree_mkNd; ptree_head_mkNd; real_fringe_mkNd;
      ptree_loc_mkNd; ptree_list_loc_def; ptree_loc_def; MAP; FLAT; APPEND_NIL;
      merge_list_locs_def; leftLoc_merge_locs; rightLoc_merge_locs; MAP_APPEND;
      MEM; PARSE1AUX_cmlG_FDOM_INL] THEN
    REPEAT CONJ_TAC THENL
     [PARSE3AUX_GRULE_MEM_TAC;
      REWRITE_TAC[DISJ_IMP_THM; FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[APPEND_ASSOC] THEN ASM_REWRITE_TAC[MAP_APPEND]];
    MAP_EVERY EXISTS_TAC [`mkNd (INL nDType) [mkNd (INL nTbase) [bpt]]:mlptree`;
                          `h0:mlptree`] THEN
    REWRITE_TAC[PARSE3AUX_Nd_mkNd; PARSE3AUX_left_insert2_mkNd1] THEN
    REWRITE_TAC[PARSE3AUX_leftmost_DType; PARSE3AUX_leftmost_Tbase] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MAP; FLAT; APPEND_NIL; MEM]) THEN
    ASM_REWRITE_TAC[valid_lptree_mkNd; ptree_head_mkNd; real_fringe_mkNd;
      ptree_loc_mkNd; ptree_list_loc_SING; MAP; FLAT; APPEND_NIL; MAP_APPEND;
      MEM; PARSE1AUX_cmlG_FDOM_INL; DISJ_IMP_THM; FORALL_AND_THM;
      FORALL_UNWIND_THM2] THEN
    REPEAT CONJ_TAC THEN TRY PARSE3AUX_GRULE_MEM_TAC THEN ASM_MESON_TAC[]]);;

let left_insert_mkNd = prove
 (`(!n (sep:(A,B,locs)parsetree) c c0.
      left_insert (mkNd n [c0]) n sep c = mkNd n [mkNd n [c]; sep; c0]) /\
   (!n (sep:(A,B,locs)parsetree) c p' s' c'.
      left_insert (mkNd n [p'; s'; c']) n sep c =
      mkNd n [left_insert p' n sep c; s'; c'])`,
  REWRITE_TAC[mkNd_def; left_insert_def] THEN CASE_REWRITE_TAC[]);;
let _ = cake_add_simps [left_insert_mkNd];;

let ptree_loc_left_insert = prove
 (`!(bpt:(A,B,locs)parsetree) n sep c.
     valid_locs bpt ==>
     ptree_loc (left_insert bpt n sep c) =
     merge_locs (ptree_loc c) (ptree_loc bpt)`,
  MATCH_MP_TAC left_insert_ind THEN CONJ_TAC THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[left_insert_def; ptree_loc_def]; ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "ih") THEN REWRITE_TAC[valid_locs_def] THEN
  STRIP_TAC THEN REWRITE_TAC[left_insert_def] THEN
  ASM_CASES_TAC `n:B+num = p` THEN ASM_REWRITE_TAC[ptree_loc_def] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  CASES_ON `subs:((A,B,locs)parsetree)list` THEN CASE_REWRITE_TAC[ptree_loc_def] THEN
  CASES_ON `a1:((A,B,locs)parsetree)list` THEN CASE_REWRITE_TAC[ptree_loc_def] THENL
   [ASM_REWRITE_TAC[ptree_loc_mkNd; ptree_list_loc_def; MAP; merge_list_locs_def;
                    ptree_list_loc_SING; merge_list_locs_HDLAST; LAST; NOT_CONS_NIL;
                    PARSE3AUX_merge_locs_LR];
    ALL_TAC] THEN
  CASES_ON `a1':((A,B,locs)parsetree)list` THEN CASE_REWRITE_TAC[ptree_loc_def] THEN
  CASES_ON `a1'':((A,B,locs)parsetree)list` THEN CASE_REWRITE_TAC[ptree_loc_def] THEN
  USE_THEN "ih" (MP_TAC o SPECL [`a0':(A,B,locs)parsetree`; `a0'':(A,B,locs)parsetree`;
                                 `a0:(A,B,locs)parsetree`]) THEN
  REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MEM; DISJ_IMP_THM; FORALL_AND_THM; FORALL_UNWIND_THM2]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[ptree_loc_mkNd; ptree_list_loc_def; MAP; merge_list_locs_def;
                  ptree_list_loc_SING; merge_list_locs_HDLAST; LAST; NOT_CONS_NIL;
                  PARSE3AUX_merge_locs_LR]);;

(* The next reassociation scenario is the general story of a left-          *)
(* associative binary operator, P ::= P SEP C | C: a valid P-tree to the    *)
(* right and a single C to the left can be combined by inserting the C-tree *)
(* into the P-tree in the leftmost position (HOL4's comment, abridged).     *)

let PARSE3AUX_MAP_TKI_SING_G = prove
 (`!pf (s:(A,B)symbol) (l:locs).
     [(s,l)] = MAP ((TOK:A->(A,B)symbol) ## I) pf ==> ?t. s = TOK t`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; NOT_CONS_NIL; CONS_11] THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MP_TAC(ISPEC `h:A#locs` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:A` (X_CHOOSE_THEN `b:locs` SUBST1_TAC)) THEN
  REWRITE_TAC[PAIR_MAP_THM; I_THM; PAIR_EQ] THEN MESON_TAC[]);;

let lassoc_reassociated = prove
 (`!(G:(A,B)grammar) P SEP C ppt spt cpt pf sf cf.
     FAPPLY (grammar_rules G) P = {[NT P; SEP; C], [C]} ==>
     valid_lptree G ppt /\ ptree_head ppt = NT P /\
       real_fringe ppt = MAP (TOK ## I) pf /\
     valid_lptree G spt /\ ptree_head spt = SEP /\
       real_fringe spt = MAP (TOK ## I) sf /\
     valid_lptree G cpt /\ ptree_head cpt = C /\
       real_fringe cpt = MAP (TOK ## I) cf ==>
     ?cpt' spt' ppt'.
       valid_lptree G ppt' /\ ptree_head ppt' = NT P /\
       valid_lptree G spt' /\ ptree_head spt' = SEP /\
       valid_lptree G cpt' /\ ptree_head cpt' = C /\
       APPEND (APPEND (real_fringe cpt') (real_fringe spt')) (real_fringe ppt') =
         MAP (TOK ## I) (APPEND (APPEND pf sf) cf) /\
       leftLoc (ptree_loc cpt') = leftLoc (ptree_loc ppt) /\
       rightLoc (ptree_loc ppt') = rightLoc (ptree_loc cpt) /\
       mkNd P [ppt; spt; cpt] = left_insert ppt' P spt' cpt'`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SPEC_TAC(`cf:(A#locs)list`,`cf:(A#locs)list`) THEN
  SPEC_TAC(`sf:(A#locs)list`,`sf:(A#locs)list`) THEN
  SPEC_TAC(`pf:(A#locs)list`,`pf:(A#locs)list`) THEN
  SPEC_TAC(`cpt:(A,B,locs)parsetree`,`cpt:(A,B,locs)parsetree`) THEN
  SPEC_TAC(`spt:(A,B,locs)parsetree`,`spt:(A,B,locs)parsetree`) THEN
  SPEC_TAC(`ppt:(A,B,locs)parsetree`,`ppt:(A,B,locs)parsetree`) THEN
  MATCH_MP_TAC ptree_ind THEN CONJ_TAC THENL
   [REWRITE_TAC[FORALL_PAIR_THM; ptree_head_def; real_fringe_def] THEN
    MESON_TAC[PARSE3AUX_MAP_TKI_SING_G; symbol_distinct];
    ALL_TAC] THEN
  X_GEN_TAC `subs:((A,B,locs)parsetree)list` THEN DISCH_THEN(LABEL_TAC "ih") THEN
  REWRITE_TAC[FORALL_PAIR_THM; ptree_head_def; real_fringe_def; valid_lptree_thm;
              symbol_inject] THEN
  MAP_EVERY X_GEN_TAC [`n:B+num`; `l:locs`; `spt:(A,B,locs)parsetree`;
                       `cpt:(A,B,locs)parsetree`; `pf:(A#locs)list`;
                       `sf:(A#locs)list`; `cf:(A#locs)list`] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (PARSE3AUX_is_grule_fact o concl)) THEN
  ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; pegComplete_MAP_EQ_CONS; MAP_EQ_NIL] THEN
  STRIP_TAC THEN RVEQ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th ->
      try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "FLAT"
      with Failure _ -> false)) THEN
    REWRITE_TAC[MAP; FLAT; APPEND_NIL] THEN
    GEN_REWRITE_TAC LAND_CONV [EQ_SYM_EQ] THEN
    REWRITE_TAC[LPARSEAUX_MAP_EQ_APPEND] THEN
    DISCH_THEN(X_CHOOSE_THEN `pf0:(A#locs)list` (X_CHOOSE_THEN `rest:(A#locs)list`
      (CONJUNCTS_THEN2 SUBST_ALL_TAC (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) MP_TAC)))) THEN
    REWRITE_TAC[LPARSEAUX_MAP_EQ_APPEND] THEN
    DISCH_THEN(X_CHOOSE_THEN `sf0:(A#locs)list` (X_CHOOSE_THEN `cf0:(A#locs)list`
      (CONJUNCTS_THEN2 SUBST_ALL_TAC (CONJUNCTS_THEN (ASSUME_TAC o SYM))))) THEN
    USE_THEN "ih" (MP_TAC o SPECL [`h0':(A,B,locs)parsetree`; `h0'':(A,B,locs)parsetree`;
                                   `pf0:(A#locs)list`; `sf0:(A#locs)list`;
                                   `cf0:(A#locs)list`] o
      REWRITE_RULE[MEM] o SPEC `h0:(A,B,locs)parsetree`) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[MEM]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `cpt':(A,B,locs)parsetree`
      (X_CHOOSE_THEN `spt':(A,B,locs)parsetree`
        (X_CHOOSE_THEN `ppt':(A,B,locs)parsetree` STRIP_ASSUME_TAC))) THEN
    MAP_EVERY EXISTS_TAC [`cpt':(A,B,locs)parsetree`; `spt':(A,B,locs)parsetree`;
                          `mkNd P [ppt'; spt; cpt]:(A,B,locs)parsetree`] THEN
    SUBGOAL_THEN
     `Nd (P,merge_list_locs [ptree_loc h0; ptree_loc h0'; ptree_loc h0''])
         [h0; h0'; h0''] = mkNd P [h0; h0'; h0'']:(A,B,locs)parsetree`
     SUBST1_TAC THENL [REWRITE_TAC[mkNd_def; ptree_list_loc_def; MAP]; ALL_TAC] THEN
    ASM_REWRITE_TAC[left_insert_mkNd; valid_lptree_mkNd; ptree_head_mkNd;
      real_fringe_mkNd; ptree_loc_mkNd; ptree_list_loc_def; ptree_loc_def; MAP;
      FLAT; APPEND_NIL; merge_list_locs_def; merge_list_locs_HDLAST; LAST;
      NOT_CONS_NIL; leftLoc_merge_locs; rightLoc_merge_locs; MAP_APPEND; MEM;
      IN_INSERT; DISJ_IMP_THM; FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
    REWRITE_TAC[GSYM APPEND_ASSOC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM APPEND_ASSOC; MAP_APPEND]) THEN
    ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[APPEND_ASSOC]) THEN REWRITE_TAC[APPEND_ASSOC] THEN
    ASM_REWRITE_TAC[];
    MAP_EVERY EXISTS_TAC [`h0:(A,B,locs)parsetree`; `spt:(A,B,locs)parsetree`;
                          `mkNd P [cpt]:(A,B,locs)parsetree`] THEN
    REWRITE_TAC[PARSE3AUX_Nd_mkNd; left_insert_mkNd] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MAP; FLAT; APPEND_NIL; MEM; FORALL_UNWIND_THM2]) THEN
    ASM_REWRITE_TAC[valid_lptree_mkNd; ptree_head_mkNd; real_fringe_mkNd;
      ptree_loc_mkNd; ptree_list_loc_SING; MAP; FLAT; APPEND_NIL; MAP_APPEND;
      MEM; IN_INSERT; DISJ_IMP_THM; FORALL_AND_THM; FORALL_UNWIND_THM2]]);;

let left_insert_mk_linfix = prove
 (`!N (acc:(A,B,locs)parsetree) arg s c.
     left_insert (mk_linfix N acc arg) N s c =
     mk_linfix N (left_insert acc N s c) arg`,
  MATCH_MP_TAC mk_linfix_ind THEN REWRITE_TAC[mk_linfix_def] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[left_insert_mkNd]);;

(* HOL4: [local] *)
let elim_disjineq = prove
 (`!p (x:A) y. p \/ ~(x = y) <=> (x = y ==> p)`,
  MESON_TAC[]);;

(* HOL4: [local] *)
let elim_det = prove
 (`!(P:A->bool) y. (!x. P x <=> (x = y)) ==> P y`,
  MESON_TAC[]);;

let peg_seql_NONE_det = prove
 (`!(G:(A,B,(C)list,E)peg) syms i0 f fl fe.
     peg_eval G (i0, seql syms f) (Failure fl fe) ==>
     !f' r. peg_eval G (i0, seql syms f') r <=> r = Failure fl fe`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  SUBGOAL_THEN `peg_eval (G:(A,B,(C)list,E)peg) (i0, seql syms f') (Failure fl fe)`
    (fun th -> MESON_TAC[th; peg_deterministic]) THEN
  POP_ASSUM MP_TAC THEN
  REWRITE_TAC[seql_def; PARSE3AUX_peg_eval_pegf; pegresult_distinct;
              pegresult_inject] THEN
  MESON_TAC[]);;

let firstSet_respect_peg_eval_not_success = prove
 (`!N i0 t l i r e0.
     ~(t IN firstSet cmlG [NT N]) /\ ~peg0 cmlPEG (peg_nt N I) /\
     peg_nt N I IN Gexprs cmlPEG ==>
     ~peg_eval cmlPEG (CONS (t,l) i0, peg_nt N I) (peg_Success i r e0)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP peg_respects_firstSets_rwt) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th; pegresult_distinct]));;

let PARSE3AUX_FIRSTSET_RWTS =
  [firstSet_nUQTyOp; firstSet_nTyOp; firstSet_nPTbase; firstSet_nTbaseList;
   firstSet_nTyVarList; firstSet_nLetDec; firstSet_nLetDecs; firstSet_nTypeDec;
   firstSet_nTypeAbbrevDec; firstSet_nStructure; firstSet_nDecl; firstSet_nDecls;
   firstSet_nMultOps; firstSet_nRelOps; firstSet_nAddOps; firstSet_nCompOps;
   firstSet_nListOps; firstSet_nSpecLine; firstSet_nSpecLineList; firstSet_nV;
   firstSet_nFQV; firstSet_nUQConstructorName; firstSet_nConstructorName;
   firstSet_nEtuple; firstSet_nEliteral; firstSet_nEbase; firstSet_nEapp;
   firstSet_nEmult; firstSet_nEadd; firstSet_nElistop; firstSet_nErel;
   firstSet_nEcomp; firstSet_nEbefore; firstSet_nEtyped; firstSet_nElogicAND;
   firstSet_nElogicOR; firstSet_nEhandle; firstSet_nE; firstSet_nTopLevelDecs;
   firstSet_nNonETopLevelDecs; firstSet_nEseq; firstSet_nElist1;
   firstSet_nElist2; firstSet_nPtuple; firstSet_nPbase; firstSet_nPConApp;
   firstSet_nPapp; firstSet_nPcons; firstSet_nPas; firstSet_nPattern;
   firstSet_nPatternList; firstSet_nPbaseList1; firstSet_nPEsfx];;

(* membership of a token in a first set or a union of first sets, decided *)
let PARSE3AUX_FIRSTSET_TAC : tactic =
  REWRITE_TAC PARSE3AUX_FIRSTSET_RWTS THEN
  REWRITE_TAC[IN_UNION; IN_INSERT; NOT_IN_EMPTY; IN_ELIM_THM; IN_DIFF; IN_UNIV;
              IN_DELETE] THEN
  CASE_REWRITE_TAC[];;

let eOR_wrongtok = prove
 (`!loc i0 i r eo.
     ~peg_eval cmlPEG (CONS (RaiseT,loc) i0, peg_nt (INL nElogicOR) I) (peg_Success i r eo) /\
     ~peg_eval cmlPEG (CONS (FnT,loc) i0, peg_nt (INL nElogicOR) I) (peg_Success i r eo) /\
     ~peg_eval cmlPEG (CONS (CaseT,loc) i0, peg_nt (INL nElogicOR) I) (peg_Success i r eo) /\
     ~peg_eval cmlPEG (CONS (IfT,loc) i0, peg_nt (INL nElogicOR) I) (peg_Success i r eo)`,
  REPEAT GEN_TAC THEN REPEAT CONJ_TAC THEN
  MATCH_MP_TAC firstSet_respect_peg_eval_not_success THEN
  REWRITE_TAC[peg0_nElogicOR; NTS_in_PEG_exprs] THEN PARSE3AUX_FIRSTSET_TAC);;

let peg_eval_seqempty = prove
 (`!(G:(A,B,(C)list,E)peg) i0 e1 f r.
     peg_eval G (i0, peg_seq e1 (empty []) f) r <=>
     ?r0. peg_eval G (i0, e1) r0 /\
          ((?fl fe. r0 = Failure fl fe /\ r = r0) \/
           (?i r00 eo. r0 = peg_Success i r00 eo /\
                       r = peg_Success i (f r00 []) NONE))`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [peg_eval_cases] THEN
  REWRITE_TAC[PAIR_EQ; pegsym_distinct; pegsym_inject; peg_eval_empty;
              pegresult_distinct; pegresult_inject] THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM; LEFT_EXISTS_AND_THM; UNWIND_THM1;
              UNWIND_THM2; GSYM CONJ_ASSOC] THEN
  REWRITE_TAC[peg_eval_empty; pegresult_distinct; pegresult_inject] THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM; LEFT_EXISTS_AND_THM; UNWIND_THM1;
              UNWIND_THM2; GSYM CONJ_ASSOC] THEN
  MESON_TAC[]);;

let peg_eval_NT = prove
 (`!(G:(A,B,C,E)peg) i0 N f r.
     peg_eval G (i0, peg_nt N f) r <=>
     ?r0. r = resultmap f r0 /\ N IN FDOM (peg_rules G) /\
          peg_eval G (i0, FAPPLY (peg_rules G) N) r0`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [peg_eval_cases] THEN
  REWRITE_TAC[PAIR_EQ; pegsym_distinct; pegsym_inject] THEN MESON_TAC[]);;

let nestoppers_def = new_definition
  `nestoppers =
     (:token) DIFF
     ((((((({AndalsoT, ArrowT, BarT, ColonT, HandleT, OrelseT,
             AlphaT (implode "before")} UNION
            firstSet cmlG [NT (INL nMultOps)]) UNION
           firstSet cmlG [NT (INL nRelOps)]) UNION
          firstSet cmlG [NT (INL nListOps)]) UNION
         firstSet cmlG [NT (INL nAddOps)]) UNION
        firstSet cmlG [NT (INL nCompOps)]) UNION
       firstSet cmlG [NT (INL nEbase)]) UNION firstSet cmlG [NT (INL nTyOp)])`;;

(* HOL4 writes stoppers as clauses with a catch-all, which TFL completes   *)
(* into one clause per constructor of MMLnonT; it is defined here by the   *)
(* equivalent match and stoppers_def is the clause form (tokenUtils'       *)
(* SEM2AUX_CASE_CLAUSES)                                                    *)

let PARSE3AUX_stoppers_def = cake_def
  `stoppers (n:MMLnonT) =
     match n with
         nAndFDecls -> nestoppers DELETE AndT
       | nDconstructor -> (:token) DIFF ((({StarT, OfT, ArrowT, LparT} UNION firstSet cmlG [NT (INL nTyOp)]) UNION {TyvarT s | s | T}))
       | nDecl -> nestoppers DIFF (({BarT, StarT, AndT, OfT} UNION {TyvarT s | s | T}))
       | nDecls -> nestoppers DIFF (({BarT, StarT, AndT, SemicolonT, FunT, ValT, DatatypeT, OfT, ExceptionT, TypeT, LocalT, StructureT} UNION {TyvarT s | s | T}))
       | nDType -> (:token) DIFF (firstSet cmlG [NT (INL nTyOp)])
       | nDtypeCons -> (:token) DIFF ((({ArrowT, BarT, StarT, OfT, LparT} UNION firstSet cmlG [NT (INL nTyOp)]) UNION {TyvarT s | s | T}))
       | nDtypeDecl -> (:token) DIFF ((({ArrowT, BarT, StarT, OfT, LparT} UNION firstSet cmlG [NT (INL nTyOp)]) UNION {TyvarT s | s | T}))
       | nDtypeDecls -> (:token) DIFF ((({AndT, ArrowT, BarT, StarT, OfT, LparT} UNION {TyvarT s | s | T}) UNION firstSet cmlG [NT (INL nTyOp)]))
       | nE -> nestoppers
       | nEadd -> (:token) DIFF (((firstSet cmlG [NT (INL nMultOps)] UNION firstSet cmlG [NT (INL nAddOps)]) UNION firstSet cmlG [NT (INL nEbase)]))
       | nEapp -> (:token) DIFF (firstSet cmlG [NT (INL nEbase)])
       | nEbefore -> (:token) DIFF ((((((({AlphaT (implode "before")} UNION firstSet cmlG [NT (INL nCompOps)]) UNION firstSet cmlG [NT (INL nRelOps)]) UNION firstSet cmlG [NT (INL nListOps)]) UNION firstSet cmlG [NT (INL nMultOps)]) UNION firstSet cmlG [NT (INL nAddOps)]) UNION firstSet cmlG [NT (INL nEbase)]))
       | nEcomp -> (:token) DIFF ((((((firstSet cmlG [NT (INL nCompOps)] UNION firstSet cmlG [NT (INL nRelOps)]) UNION firstSet cmlG [NT (INL nListOps)]) UNION firstSet cmlG [NT (INL nMultOps)]) UNION firstSet cmlG [NT (INL nAddOps)]) UNION firstSet cmlG [NT (INL nEbase)]))
       | nEhandle -> nestoppers
       | nElist1 -> nestoppers DELETE CommaT
       | nElist2 -> nestoppers DELETE CommaT
       | nElistop -> (:token) DIFF ((((firstSet cmlG [NT (INL nMultOps)] UNION firstSet cmlG [NT (INL nAddOps)]) UNION firstSet cmlG [NT (INL nListOps)]) UNION firstSet cmlG [NT (INL nEbase)]))
       | nElogicAND -> (:token) DIFF (((((((({AndalsoT, ColonT, ArrowT, AlphaT (implode "before")} UNION firstSet cmlG [NT (INL nCompOps)]) UNION firstSet cmlG [NT (INL nRelOps)]) UNION firstSet cmlG [NT (INL nListOps)]) UNION firstSet cmlG [NT (INL nMultOps)]) UNION firstSet cmlG [NT (INL nAddOps)]) UNION firstSet cmlG [NT (INL nEbase)]) UNION firstSet cmlG [NT (INL nTyOp)]))
       | nElogicOR -> (:token) DIFF (((((((({AndalsoT, ColonT, ArrowT, OrelseT, AlphaT (implode "before")} UNION firstSet cmlG [NT (INL nCompOps)]) UNION firstSet cmlG [NT (INL nRelOps)]) UNION firstSet cmlG [NT (INL nListOps)]) UNION firstSet cmlG [NT (INL nMultOps)]) UNION firstSet cmlG [NT (INL nAddOps)]) UNION firstSet cmlG [NT (INL nEbase)]) UNION firstSet cmlG [NT (INL nTyOp)]))
       | nEmult -> (:token) DIFF ((firstSet cmlG [NT (INL nEbase)] UNION firstSet cmlG [NT (INL nMultOps)]))
       | nErel -> (:token) DIFF (((((firstSet cmlG [NT (INL nRelOps)] UNION firstSet cmlG [NT (INL nListOps)]) UNION firstSet cmlG [NT (INL nMultOps)]) UNION firstSet cmlG [NT (INL nAddOps)]) UNION firstSet cmlG [NT (INL nEbase)]))
       | nEseq -> nestoppers DELETE SemicolonT
       | nEtyped -> (:token) DIFF (((((((({ColonT, ArrowT, AlphaT (implode "before")} UNION firstSet cmlG [NT (INL nCompOps)]) UNION firstSet cmlG [NT (INL nListOps)]) UNION firstSet cmlG [NT (INL nRelOps)]) UNION firstSet cmlG [NT (INL nMultOps)]) UNION firstSet cmlG [NT (INL nAddOps)]) UNION firstSet cmlG [NT (INL nEbase)]) UNION firstSet cmlG [NT (INL nTyOp)]))
       | nFDecl -> nestoppers
       | nLetDec -> nestoppers DELETE AndT
       | nLetDecs -> nestoppers DIFF ({AndT, FunT, ValT, SemicolonT})
       | nNonETopLevelDecs -> {}
       | nOptTypEqn -> (:token) DIFF (({ArrowT, StarT, EqualsT} UNION firstSet cmlG [NT (INL nTyOp)]))
       | nPcons -> (:token) DIFF (((((({LparT, UnderbarT, LbrackT, SymbolT (implode "::"), OpT} UNION {tokens_IntT i | i | T}) UNION {StringT s | s | T}) UNION {tokens_CharT c | c | T}) UNION firstSet cmlG [NT (INL nV)]) UNION firstSet cmlG [NT (INL nConstructorName)]))
       | nPas -> (:token) DIFF (((((({LparT, UnderbarT, LbrackT, SymbolT (implode "::"), AsT, OpT} UNION {tokens_IntT i | i | T}) UNION {StringT s | s | T}) UNION {tokens_CharT c | c | T}) UNION firstSet cmlG [NT (INL nV)]) UNION firstSet cmlG [NT (INL nConstructorName)]))
       | nPConApp -> (:token) DIFF (((((({LparT, UnderbarT, LbrackT, OpT} UNION {tokens_IntT i | i | T}) UNION {StringT s | s | T}) UNION {tokens_CharT c | c | T}) UNION firstSet cmlG [NT (INL nV)]) UNION firstSet cmlG [NT (INL nConstructorName)]))
       | nPapp -> (:token) DIFF (((((({LparT, UnderbarT, LbrackT, OpT} UNION {tokens_IntT i | i | T}) UNION {StringT s | s | T}) UNION {tokens_CharT c | c | T}) UNION firstSet cmlG [NT (INL nV)]) UNION firstSet cmlG [NT (INL nConstructorName)]))
       | nPattern -> (:token) DIFF ((((((((({LparT, UnderbarT, LbrackT, ColonT, ArrowT, StarT, AsT, OpT} UNION {AlphaT s | s | T}) UNION {SymbolT s | s | T}) UNION {LongidT s1 s2 | s1,s2 | T}) UNION {tokens_IntT i | i | T}) UNION {StringT s | s | T}) UNION {tokens_CharT c | c | T}) UNION firstSet cmlG [NT (INL nV)]) UNION firstSet cmlG [NT (INL nConstructorName)]))
       | nPatternList -> (:token) DIFF ((((((((({CommaT, LparT, UnderbarT, LbrackT, ColonT, ArrowT, StarT, AsT, OpT} UNION {AlphaT s | s | T}) UNION {SymbolT s | s | T}) UNION {LongidT s1 s2 | s1,s2 | T}) UNION {tokens_IntT i | i | T}) UNION {StringT s | s | T}) UNION {tokens_CharT c | c | T}) UNION firstSet cmlG [NT (INL nV)]) UNION firstSet cmlG [NT (INL nConstructorName)]))
       | nPbaseList1 -> (:token) DIFF (firstSet cmlG [NT (INL nPbase)])
       | nPE -> nestoppers
       | nPEs -> nestoppers
       | nPEsfx -> nestoppers
       | nPType -> (:token) DIFF (({StarT} UNION firstSet cmlG [NT (INL nTyOp)]))
       | nSpecLine -> (:token) DIFF ((({ArrowT, AndT, BarT, StarT, OfT, EqualsT, LparT} UNION firstSet cmlG [NT (INL nTyOp)]) UNION {TyvarT s | s | T}))
       | nSpecLineList -> (:token) DIFF ((({ValT, DatatypeT, TypeT, ExceptionT, SemicolonT, ArrowT, AndT, BarT, StarT, OfT, EqualsT, LparT} UNION firstSet cmlG [NT (INL nTyOp)]) UNION {TyvarT s | s | T}))
       | nTbaseList -> (:token) DIFF ((({LparT} UNION firstSet cmlG [NT (INL nTyOp)]) UNION {TyvarT s | s | T}))
       | nTopLevelDecs -> {}
       | nType -> (:token) DIFF (({ArrowT, StarT} UNION firstSet cmlG [NT (INL nTyOp)]))
       | nTypeAbbrevDec -> (:token) DIFF (({ArrowT, StarT} UNION firstSet cmlG [NT (INL nTyOp)]))
       | nTypeDec -> (:token) DIFF ((({AndT, ArrowT, StarT, BarT, OfT, LparT} UNION {TyvarT s | s | T}) UNION firstSet cmlG [NT (INL nTyOp)]))
       | nTypeList1 -> (:token) DIFF (({CommaT, ArrowT, StarT} UNION firstSet cmlG [NT (INL nTyOp)]))
       | nTypeList2 -> (:token) DIFF (({CommaT, ArrowT, StarT} UNION firstSet cmlG [NT (INL nTyOp)]))
       | nTyVarList -> {RparT}
       | nOptionalSignatureAscription -> (:token) DELETE SealT
       | _ -> (:token)`;;

let stoppers_def = SEM2AUX_CASE_CLAUSES PARSE3AUX_stoppers_def;;


(* ------------------------------------------------------------------------- *)
(* Completeness: the machinery and the lemmas of HOL4 lines 900-3589         *)
(* ------------------------------------------------------------------------- *)

(* the statement of the completeness case of non-terminal X: the induction *)
(* hypothesis (a shorter fringe, or the same fringe and a smaller rank) and *)
(* a valid tree mkNd (INL X) subs with the stopper condition on sfx         *)

let PARSE3AUX_complete_goal (x:string) =
  parse_term
   ("!subs pfx sfx.
      (!pt' N' pfx' sfx'.
         (LENGTH pfx' < LENGTH pfx \\/
          pfx' = pfx /\\ NT_rank (INL N') < NT_rank (INL " ^ x ^ ")) /\\
         valid_lptree cmlG pt' /\\ ptree_head pt' = NT (INL N') /\\
         INL N' IN FDOM (peg_rules cmlPEG) /\\
         (~(sfx' = []) ==> FST (HD sfx') IN stoppers N') /\\
         real_fringe pt' = MAP (TOK ## I) pfx' ==>
         ?eo. peg_eval cmlPEG (APPEND pfx' sfx', peg_nt (INL N') I)
                       (peg_Success sfx' [pt'] eo)) /\\
      valid_lptree cmlG (mkNd (INL " ^ x ^ ") subs) /\\
      (~(sfx = []) ==> FST (HD sfx) IN stoppers " ^ x ^ ") /\\
      real_fringe (mkNd (INL " ^ x ^ ") subs) = MAP (TOK ## I) pfx ==>
      ?eo. peg_eval cmlPEG (APPEND pfx sfx, peg_nt (INL " ^ x ^ ") I)
                    (peg_Success sfx [mkNd (INL " ^ x ^ ") subs] eo)");;

let PARSE3AUX_PAIR_MAP_TKI_EQ = prove
 (`!(x:token#locs) t l. (TOK ## I) x = (TOK t:(token,MMLnonT)symbol, l) <=> x = (t,l)`,
  REWRITE_TAC[FORALL_PAIR_THM; PAIR_MAP_THM; I_THM; PAIR_EQ; symbol_inject]);;

let PARSE3AUX_EX_TAC : tactic =
  REPEAT(CHANGED_TAC
   (REWRITE_TAC[LEFT_AND_EXISTS_THM; RIGHT_AND_EXISTS_THM] THEN
    CONV_TAC(TOP_DEPTH_CONV UNWIND_CONV) THEN
    CASE_REWRITE_TAC[PARSE3AUX_EXISTS_REFL']));;

(* split the fringe equation FLAT (MAP real_fringe subs) = MAP (TOK ## I) pfx *)
let PARSE3AUX_is_map_fact tm =
  is_eq tm && is_comb(rand tm) &&
  (try fst(dest_const(fst(strip_comb(rand tm)))) = "MAP" with Failure _ -> false);;

let PARSE3AUX_FRINGE_SPLIT_TAC : tactic =
  FIRST_X_ASSUM(MP_TAC o SYM o check (fun th -> PARSE3AUX_is_map_fact (concl th) &&
      not (is_var (lhs (concl th))))) THEN
  REWRITE_TAC[MAP; FLAT; APPEND; APPEND_NIL; real_fringe_def] THEN
  REWRITE_TAC[pegComplete_MAP_EQ_CONS; MAP_EQ_NIL; LPARSEAUX_MAP_EQ_APPEND;
              PARSE3AUX_PAIR_MAP_TKI_EQ] THEN
  DISCH_THEN(CAKE_STRIP_ASSUME_TAC) THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(fun th -> if PARSE3AUX_is_map_fact (concl th) then th
                           else if is_eq(concl th) && PARSE3AUX_is_map_fact (mk_eq(rand(concl th), lhand(concl th))) then SYM th else th);;

let PARSE3AUX_CSTART_TAC : tactic =
  REPEAT GEN_TAC THEN REWRITE_TAC[valid_lptree_mkNd; real_fringe_mkNd] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih") STRIP_ASSUME_TAC) THEN
  PARSE3AUX_GRULE_CASES_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ptree_head_eq_tok]) THEN
  REPEAT(FIRST_X_ASSUM(CHOOSE_THEN SUBST_ALL_TAC o check (is_exists o concl))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MEM; DISJ_IMP_THM; FORALL_AND_THM; FORALL_UNWIND_THM2;
                              valid_lptree_thm]) THEN
  PARSE3AUX_FRINGE_SPLIT_TAC;;

(* ------------------------------------------------------------------------- *)
(* A symbolic evaluator of cmlPEG for the cases of completeness: on an      *)
(* input made of tokens and of the fringes of the subtrees of the case, it  *)
(* proves the successful or failing evaluation of an expression, using the  *)
(* induction hypothesis (Skolemized, labelled "ihs") for the non-terminals  *)
(* of the subtrees, and fFail_def for non-terminals that cannot start with  *)
(* the next token.                                                          *)
(* ------------------------------------------------------------------------- *)

let PARSE3AUX_UNCURRY_Failure = prove
 (`!(p:locs#E). UNCURRY Failure p =
                (Failure (FST p) (SND p):((A#locs)list,C,E)pegresult)`,
  REWRITE_TAC[FORALL_PAIR_THM; UNCURRY_DEF; FST; SND]);;

(* the derived forms, unfolded to the primitive expressions *)
let PARSE3AUX_PRIM_CONV =
  PURE_REWRITE_CONV[seql_def; ITLIST; choicel_def; pegf_def; try_def;
                    tokeq_def; tokSymP_def; cmlPEG_pnt_def; MAP; peg_V_def;
                    peg_longV_def; peg_UQConstructorName_def;
                    peg_StructName_def; peg_TypeDec_def; peg_EbaseParen_def] THENC
  TOP_DEPTH_CONV BETA_CONV;;

(* deciding a boolean about concrete tokens and sets of tokens *)
let PARSE3AUX_SETS_RWTS =
  [stoppers_def; nestoppers_def; IN_DIFF; IN_UNION; IN_INSERT; IN_DELETE;
   IN_UNIV; NOT_IN_EMPTY; IN_ELIM_THM; IN_SING; firstSet_TOK; firstSet_NIL] @
  PARSE3AUX_FIRSTSET_RWTS;;

let PARSE3AUX_CHAR_11 = injectivity "char";;

(* the symbol classes of the grammar on string literals *)
let PARSE3AUX_VALIDSYM_LIT_CONV tm =
  let f,a = dest_comb tm in
  if not (mem (fst(dest_const f)) ["validMultSym"; "validAddSym"; "validRelSym";
                                    "validListSym"; "validPrefixSym"]) ||
     not (frees a = []) then failwith "PARSE3AUX_VALIDSYM_LIT_CONV"
  else
   (PURE_REWRITE_CONV[validMultSym_def; validAddSym_def; validRelSym_def;
                      validListSym_def; validPrefixSym_def] THENC
    DEPTH_CONV PARSE1AUX_CHR_CONV THENC
    REWRITE_CONV[isPREFIX_THM; HD; LENGTH; IN_INSERT; NOT_IN_EMPTY;
                 NOT_CONS_NIL; CONS_11; PARSE3AUX_CHAR_11] THENC
    NUM_REDUCE_CONV THENC REWRITE_CONV[]) tm;;

(* the character classes of character literals *)
let PARSE3AUX_ORD_CONV tm =
  match tm with
    Comb(Const("ORD",_), c) when frees c = [] ->
      let n = mk_small_numeral (Char.code (dest_char c)) in
      let cth = PARSE1AUX_CHR_CONV (mk_comb(`CHR`, n)) in
      let lt = EQT_ELIM (NUM_LT_CONV (mk_comb(mk_comb(`(<):num->num->bool`, n), `256`))) in
      let th1 = EQ_MP (SPEC n ORD_CHR) lt in
      CONV_RULE (LAND_CONV (RAND_CONV (K cth))) th1
  | _ -> failwith "PARSE3AUX_ORD_CONV";;

let PARSE3AUX_CHARPRED_CONV tm =
  let f,c = dest_comb tm in
  if not (is_const f &&
          mem (fst(dest_const f)) ["isUpper"; "isLower"; "isAlpha"; "isDigit"]) ||
     not (frees c = []) then failwith "PARSE3AUX_CHARPRED_CONV"
  else
   (REWRITE_CONV[isUpper_def; isLower_def; isAlpha_def; isDigit_def] THENC
    DEPTH_CONV PARSE3AUX_ORD_CONV THENC NUM_REDUCE_CONV THENC REWRITE_CONV[]) tm;;

let PARSE3AUX_DECIDE1_CONV : conv =
  TOP_DEPTH_CONV GEN_BETA_CONV THENC
  REWRITE_CONV(PARSE3AUX_TOKPRED_RWTS @ [FST; SND; o_THM; I_THM]) THENC
  REWRITE_CONV[LEFT_AND_EXISTS_THM; RIGHT_AND_EXISTS_THM] THENC
  TOP_DEPTH_CONV UNWIND_CONV THENC TOP_DEPTH_CONV GEN_BETA_CONV THENC
  REWRITE_CONV(PARSE3AUX_TOKPRED_RWTS @ [FST; SND; o_THM; I_THM]) THENC
  REWRITE_CONV PARSE3AUX_SETS_RWTS THENC
  REWRITE_CONV[explode_implode] THENC
  DEPTH_CONV PARSE3AUX_VALIDSYM_LIT_CONV THENC
  REWRITE_CONV[strsub_def; EL; HD] THENC
  DEPTH_CONV PARSE3AUX_CHARPRED_CONV THENC
  CASE_REWRITE_CONV[PARSE3AUX_EXISTS_REFL'; UNWIND_THM1; UNWIND_THM2] THENC
  TOP_DEPTH_CONV UNWIND_CONV THENC
  REWRITE_CONV[EXISTS_REFL; PARSE3AUX_EXISTS_REFL'; PARSE3AUX_CHAR_11];;

let PARSE3AUX_DECIDE_CONV : conv =
  PARSE3AUX_DECIDE1_CONV THENC
  TRY_CONV(CHANGED_CONV PARSE3AUX_DECIDE1_CONV THENC
           TRY_CONV(CHANGED_CONV PARSE3AUX_DECIDE1_CONV));;

let PARSE3AUX_decide tm =
  let th = PARSE3AUX_DECIDE_CONV tm in
  let r = rhs(concl th) in
  if r = `T` then (true, EQT_ELIM th)
  else if r = `F` then (false, EQF_ELIM th)
  else failwith ("PARSE3AUX_decide: " ^ string_of_term r);;

let PARSE3AUX_NORM_CONV = PURE_REWRITE_CONV[APPEND; APPEND_NIL; GSYM APPEND_ASSOC];;

let PARSE3AUX_norm tm = rhs(concl(PARSE3AUX_NORM_CONV tm));;

let PARSE3AUX_res th = rand(concl th);;

let PARSE3AUX_is_succ th =
  fst(dest_const(fst(strip_comb(PARSE3AUX_res th)))) = "peg_Success";;

let PARSE3AUX_succ_parts th =
  match snd(strip_comb(PARSE3AUX_res th)) with
    [x1;x2;x3] -> x1,x2,x3 | _ -> failwith "succ_parts";;

let PARSE3AUX_fail_parts th =
  match snd(strip_comb(PARSE3AUX_res th)) with
    [fl;fe] -> fl,fe | _ -> failwith "fail_parts";;

(* types and terms of the proof tools below, parsed once (a quotation in a  *)
(* function is parsed at each call: tens of thousands of parses here, of   *)
(* milliseconds each in a big session)                                      *)
let PARSE3AUX_token_ty = `:token`
and PARSE3AUX_locs_ty = `:locs`
and PARSE3AUX_inp_ty = `:(token#locs)list`
and PARSE3AUX_mlptree_ty = `:mlptree`
and PARSE3AUX_symbol_ty = `:(token,MMLnonT)symbol`
and PARSE3AUX_NIL_INP_TM = `[]:(token#locs)list`
and PARSE3AUX_CMLPEG_TM = `cmlPEG`
and PARSE3AUX_NULLABLE_TM = `nullable cmlG`
and PARSE3AUX_FIRSTSET_TM = `firstSet cmlG`
and PARSE3AUX_VALID_TM = `valid_lptree cmlG`
and PARSE3AUX_GEXPRS_TM = `Gexprs cmlPEG`
and PARSE3AUX_NT_TM = `NT:MMLnonT+num->(token,MMLnonT)symbol`
and PARSE3AUX_INL_TM = `INL:MMLnonT->MMLnonT+num`
and PARSE3AUX_PTREE_HEAD_TM = `ptree_head:mlptree->(token,MMLnonT)symbol`
and PARSE3AUX_REAL_FRINGE_TM =
  `real_fringe:mlptree->((token,MMLnonT)symbol#locs)list`
and PARSE3AUX_IN_TOKEN_TM = `(IN):token->(token->bool)->bool`
and PARSE3AUX_IN_NT_TM = `(IN):MMLnonT+num->(MMLnonT+num->bool)->bool`
and PARSE3AUX_IN_PEGSYM_TM =
  `(IN):(token,MMLnonT,(mlptree)list,(char)list)pegsym->
        ((token,MMLnonT,(mlptree)list,(char)list)pegsym->bool)->bool`
and PARSE3AUX_FDOM_RULES_TM = `FDOM (peg_rules cmlPEG)`
and PARSE3AUX_FST_TOKEN_TM = `FST:token#locs->token`
and PARSE3AUX_I_TM = `I:(mlptree)list->(mlptree)list`
and PARSE3AUX_NTSYM_TM =
  `peg_nt:MMLnonT+num->((mlptree)list->(mlptree)list)->
      (token,MMLnonT,(mlptree)list,(char)list)pegsym`;;

(* the nullability of the remaining non-terminals *)
let PARSE3AUX_nullable_more =
  map (fun c ->
     let t = mk_comb(`nullable cmlG`,
               mk_list([mk_comb(`NT:MMLnonT+num->(token,MMLnonT)symbol`,
                                mk_comb(`INL:MMLnonT->MMLnonT+num`, c))],
                       `:(token,MMLnonT)symbol`)) in
     try PARSE1AUX_NULLABLE_PROVE (mk_neg t)
     with Failure _ -> PARSE1AUX_NULLABLE_PROVE t)
   [`nTypeName`; `nTypeList2`; `nTypeList1`; `nStructName`; `nSpecLineList`;
    `nSignatureValue`; `nOptionalSignatureAscription`; `nOptTypEqn`; `nOpID`;
    `nNonETopLevelDecs`; `nLetDecs`; `nDtypeDecls`; `nDtypeCons`; `nDecls`;
    `nAndFDecls`];;

(* the non-nullable non-terminals (gramProps) *)
let PARSE3AUX_nonnull_ths =
  filter (fun th -> is_neg(concl th))
   ([nullable_UQConstructorName; nullable_ConstructorName; nullable_Eliteral;
    nullable_Etuple; nullable_V; nullable_FQV; nullable_Ebase; nullable_Eapp;
    nullable_Emult; nullable_Eadd; nullable_Elistop; nullable_Erel;
    nullable_Ecomp; nullable_Ebefore; nullable_Etyped; nullable_ElogicAND;
    nullable_ElogicOR; nullable_Ehandle; nullable_E; nullable_UQTyOp;
    nullable_TyOp; nullable_PTbase; nullable_TbaseList; nullable_Tbase;
    nullable_DType; nullable_PType; nullable_Type; nullable_TyvarN;
    nullable_TypeDec; nullable_SpecLine; nullable_Ptuple; nullable_Pbase;
    nullable_PConApp; nullable_LetDec; nullable_TyVarList; nullable_DtypeDecl;
    nullable_Structure; nullable_TypeAbbrevDec; nullable_Decl; nullable_PE;
    nullable_Elist1; nullable_CompOps; nullable_ListOps; nullable_PEsfx;
    nullable_Papp; nullable_Pcons; nullable_Pas; nullable_Pattern;
    nullable_PEs; nullable_RelOps; nullable_MultOps; nullable_AddOps;
    nullable_Dconstructor; nullable_FDecl; nullable_PatternList;
    nullable_PbaseList1; nullable_Elist2; nullable_Eseq;
    nullable_TopLevelDecs] @ PARSE3AUX_nullable_more);;

let PARSE3AUX_nonnull (y:term) =
  find (fun th -> rand(concl th) =
          mk_comb(PARSE3AUX_NULLABLE_TM, mk_list([mk_comb(PARSE3AUX_NT_TM,
                    mk_comb(PARSE3AUX_INL_TM, y))], PARSE3AUX_symbol_ty)))
       PARSE3AUX_nonnull_ths;;

let PARSE3AUX_FRINGE_CONS = prove
 (`!(x:mlptree) m y.
     real_fringe x = MAP (TOK ## I) m /\ ptree_head x = NT (INL y) /\
     valid_lptree cmlG x /\ ~nullable cmlG [NT (INL y)] ==>
     ?tk lk m'. m = CONS (tk,lk) m' /\ tk IN firstSet cmlG [NT (INL y)]`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`cmlG`; `NT (INL y):(token,MMLnonT)symbol`]
         rfringe_length_not_nullable) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `x:mlptree`) THEN
  ASM_REWRITE_TAC[LENGTH_MAP] THEN
  MP_TAC(ISPEC `m:(token#locs)list` list_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC
    (X_CHOOSE_THEN `h:token#locs` (X_CHOOSE_THEN `t:(token#locs)list`
      SUBST_ALL_TAC))) THEN
  REWRITE_TAC[LENGTH; LT_REFL; CONS_11] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `h:token#locs` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `tk:token` (X_CHOOSE_THEN `lk:locs` SUBST_ALL_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`tk:token`; `lk:locs`; `t:(token#locs)list`] THEN
  REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    try lhand(concl th) = `ptree_head (x:mlptree)` with Failure _ -> false)) THEN
  MATCH_MP_TAC rfirstSet_nonempty_fringe THEN
  MAP_EVERY EXISTS_TAC [`lk:locs`; `MAP ((TOK:token->(token,MMLnonT)symbol) ## (I:locs->locs)) t`] THEN
  ASM_REWRITE_TAC[MAP; PAIR_MAP_THM; I_THM]);;

let PARSE3AUX_FRINGE_CASES = prove
 (`!(x:mlptree) m y.
     real_fringe x = MAP (TOK ## I) m /\ ptree_head x = NT (INL y) /\
     valid_lptree cmlG x ==>
     m = [] \/
     ?tk lk m'. m = CONS (tk,lk) m' /\ tk IN firstSet cmlG [NT (INL y)]`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `m:(token#locs)list` list_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (fun th -> REWRITE_TAC[th])
    (X_CHOOSE_THEN `h:token#locs` (X_CHOOSE_THEN `t:(token#locs)list`
      SUBST_ALL_TAC))) THEN
  MP_TAC(ISPEC `h:token#locs` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `tk:token` (X_CHOOSE_THEN `lk:locs` SUBST_ALL_TAC)) THEN
  DISJ2_TAC THEN
  MAP_EVERY EXISTS_TAC [`tk:token`; `lk:locs`; `t:(token#locs)list`] THEN
  REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    try lhand(concl th) = `ptree_head (x:mlptree)` with Failure _ -> false)) THEN
  MATCH_MP_TAC rfirstSet_nonempty_fringe THEN
  MAP_EVERY EXISTS_TAC [`lk:locs`; `MAP ((TOK:token->(token,MMLnonT)symbol) ## (I:locs->locs)) t`] THEN
  ASM_REWRITE_TAC[MAP; PAIR_MAP_THM; I_THM]);;

(* destructure the fringe variables of the subtrees: CONS for the         *)
(* non-nullable ones, empty or CONS for the nullable ones                  *)
let PARSE3AUX_DESTRUCT_TAC : tactic = fun (asl,w as g) ->
  let cands = mapfilter (fun (_,th) ->
      let c = concl th in
      if is_eq c && is_comb(lhs c) &&
         fst(dest_const(rator(lhs c))) = "real_fringe" &&
         is_var(rand(rand c)) then (rand(lhs c), rand(rand c)) else failwith "") asl in
  let one (x,m) (asl,w as g) =
    let hd_th = snd(find (fun (_,th) -> let c = concl th in is_eq c &&
                  lhs c = mk_comb(PARSE3AUX_PTREE_HEAD_TM, x)) asl) in
    let y = rand(rand(rhs(concl hd_th))) in
    let fr = snd(find (fun (_,th) -> let c = concl th in is_eq c &&
               lhs c = mk_comb(PARSE3AUX_REAL_FRINGE_TM, x)) asl) in
    let vl = snd(find (fun (_,th) -> concl th = mk_comb(PARSE3AUX_VALID_TM, x)) asl) in
    let tkn = mk_var(fst(dest_var m)^"_t",PARSE3AUX_token_ty)
    and lkn = mk_var(fst(dest_var m)^"_l",PARSE3AUX_locs_ty)
    and mn = mk_var(fst(dest_var m)^"_r",PARSE3AUX_inp_ty) in
    let ctac = X_CHOOSE_THEN tkn (X_CHOOSE_THEN lkn (X_CHOOSE_THEN mn
                 (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC))) in
    (match (try Some(PARSE3AUX_nonnull y) with Failure _ -> None) with
       Some nn ->
         MP_TAC (MATCH_MP PARSE3AUX_FRINGE_CONS (CONJ fr (CONJ hd_th (CONJ vl nn)))) THEN
         DISCH_THEN ctac
     | None ->
         MP_TAC (MATCH_MP PARSE3AUX_FRINGE_CASES (CONJ fr (CONJ hd_th vl))) THEN
         DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC ctac)) g in
  EVERY (map (fun c -> TRY (one c)) cands) g;;

(* deciding a boolean about tokens, using the membership assumptions      *)
(* tk IN S of the token variables of the term                              *)
let PARSE3AUX_memfacts asl tm =
  let vs = filter (fun v -> type_of v = PARSE3AUX_token_ty) (frees tm) in
  mapfilter (fun (_,th) -> let c = concl th in
      if (try fst(dest_const(fst(strip_comb c))) = "IN" with Failure _ -> false) &&
         mem (lhand c) vs then th else failwith "") asl;;

(* the symbol classes are pairwise disjoint *)
let PARSE3AUX_VALIDSYM_EXCL = prove
 (`!s. (validAddSym s ==> ~validRelSym s /\ ~validListSym s /\
                          ~validPrefixSym s /\ ~validMultSym s) /\
       (validRelSym s ==> ~validAddSym s /\ ~validListSym s /\
                          ~validPrefixSym s /\ ~validMultSym s) /\
       (validListSym s ==> ~validAddSym s /\ ~validRelSym s /\
                           ~validPrefixSym s /\ ~validMultSym s) /\
       (validPrefixSym s ==> ~validAddSym s /\ ~validRelSym s /\
                             ~validListSym s /\ ~validMultSym s) /\
       (validMultSym s ==> ~validAddSym s /\ ~validRelSym s /\
                           ~validListSym s /\ ~validPrefixSym s)`,
  GEN_TAC THEN MP_TAC(SPEC `s:string` validSym_incompatibility) THEN
  CONV_TAC(fun tm -> EQT_INTRO(TAUT tm)));;

let PARSE3AUX_VALIDSYM_EXCLS =
  map GEN_ALL (CONJUNCTS (SPEC_ALL PARSE3AUX_VALIDSYM_EXCL));;

(* rewrite the compound assumptions with the literal ones *)
let PARSE3AUX_is_lit c =
  let comp d = is_conj d || is_disj d || is_imp d || is_forall d || is_exists d in
  not (comp c) && not (is_neg c && comp (rand c));;

(* complementary assumptions p and ~p *)
let PARSE3AUX_COMPL_TAC : tactic = fun (asl,w as g) ->
  let cs = map (concl o snd) asl in
  let _,th = find (fun (_,th) -> let c = concl th in is_neg c && mem (rand c) cs) asl in
  let _,th' = find (fun (_,t) -> concl t = rand(concl th)) asl in
  CONTR_TAC (MP (NOT_ELIM th) th') g;;

let PARSE3AUX_UNIT_PROP_TAC : tactic = fun (asl,w as g) ->
  let lits = filter (fun th -> PARSE3AUX_is_lit (concl th)) (map snd asl) in
  (TRY PARSE3AUX_COMPL_TAC THEN
   RULE_ASSUM_TAC(fun th -> if PARSE3AUX_is_lit (concl th) then th
                            else REWRITE_RULE lits th) THEN
   TRY(FIRST_ASSUM CONTR_TAC) THEN ASM_REWRITE_TAC[]) g;;

let PARSE3AUX_VALIDSYM_TAC : tactic = fun (asl,w as g) ->
  let ths = flat (map CONJUNCTS (flat (map (fun (_,th) ->
              mapfilter (fun imp -> MATCH_MP imp th) PARSE3AUX_VALIDSYM_EXCLS) asl))) in
  (MAP_EVERY ASSUME_TAC ths THEN PARSE3AUX_UNIT_PROP_TAC) g;;

let PARSE3AUX_CASES_DECIDE_TAC : tactic =
  REWRITE_TAC PARSE3AUX_SETS_RWTS THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(CONV_RULE PARSE3AUX_DECIDE_CONV) THEN
  TRY(FIRST_ASSUM CONTR_TAC) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  CONV_TAC PARSE3AUX_DECIDE_CONV THEN
  TRY(FIRST_ASSUM CONTR_TAC) THEN
  PARSE3AUX_VALIDSYM_TAC;;

(* the simple facts of the context (no quantifiers, implications, PEG or   *)
(* fringe facts)                                                           *)
let PARSE3AUX_ctxfacts asl =
  filter (fun th -> let c = concl th in
     not (is_forall c) && not (PARSE3AUX_is_evalfact c) &&
     not (can (find_term (fun t -> try mem (fst(dest_const t))
                                         ["real_fringe"; "ptree_head"; "valid_lptree"]
                                     with Failure _ -> false)) c))
    (map snd asl);;

(* a complete fallback: split the token variables of the decision on the   *)
(* constructors that the decision mentions, and the other constructors     *)
let PARSE3AUX_token_ctors =
  map (fun d -> let _,b = strip_exists d in fst(strip_comb(rand b)))
      (disjuncts(snd(dest_forall(concl(cases "token")))));;

let PARSE3AUX_ctor_atom avoid x c =
  let tys,_ = splitlist dest_fun_ty (type_of c) in
  if tys = [] then mk_eq(x,c) else
  let vs = itlist (fun ty vs ->
             variant (vs @ avoid)
               (mk_var("PARSE3AUX_a" ^ string_of_int (length vs),ty)) :: vs) tys [] in
  list_mk_exists(vs, mk_eq(x, list_mk_comb(c,vs)));;

let PARSE3AUX_LEAF_DECIDE_TAC : tactic =
  CONV_TAC PARSE3AUX_DECIDE_CONV THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(CONV_RULE PARSE3AUX_DECIDE_CONV) THEN
  TRY(FIRST_ASSUM CONTR_TAC) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  CONV_TAC PARSE3AUX_DECIDE_CONV THEN
  TRY(FIRST_ASSUM CONTR_TAC) THEN
  PARSE3AUX_VALIDSYM_TAC;;

let rec PARSE3AUX_TOKEN_SPLIT_TAC (dn:term list) : tactic = fun (asl,w as g) ->
  let th0 = PARSE3AUX_DECIDE_CONV w in
  let w' = rhs(concl th0) in
  if w' = `T` then ACCEPT_TAC (EQT_ELIM th0) g else
  let xs = filter (fun v -> type_of v = PARSE3AUX_token_ty && not (mem v dn)) (frees w') in
  if xs = [] then PARSE3AUX_LEAF_DECIDE_TAC g else
  let x = hd xs in
  let mentioned = filter (fun c -> can (find_term (fun t -> t = c)) w')
                         PARSE3AUX_token_ctors in
  let atoms = map (PARSE3AUX_ctor_atom (frees w') x) mentioned in
  if atoms = [] then PARSE3AUX_TOKEN_SPLIT_TAC (x::dn) g else
  let disj = list_mk_disj atoms in
  let th = PURE_REWRITE_RULE[DE_MORGAN_THM; NOT_EXISTS_THM]
             (TAUT (mk_disj(disj, mk_neg disj))) in
  (CONV_TAC (K th0) THEN MP_TAC th THEN
   DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN
   RVEQ_TAC THEN ASM_REWRITE_TAC[] THEN
   PARSE3AUX_TOKEN_SPLIT_TAC (x::dn)) g;;

let PARSE3AUX_prove_with_mems (mems:thm list) tm =
  let gl = mk_imp(list_mk_conj (map concl mems), tm) in
  let th = try TAC_PROOF(([], gl), PARSE3AUX_CASES_DECIDE_TAC)
           with Failure _ -> TAC_PROOF(([], gl), PARSE3AUX_TOKEN_SPLIT_TAC []) in
  MP th (end_itlist CONJ mems);;

let PARSE3AUX_decide_asm asl tm =
  try PARSE3AUX_decide tm with Failure _ ->
  let mems = PARSE3AUX_memfacts asl tm in
  if mems = [] then failwith "PARSE3AUX_decide_asm" else
  try (true, PARSE3AUX_prove_with_mems mems tm)
  with Failure _ -> (false, PARSE3AUX_prove_with_mems mems (mk_neg tm));;

(* a token test that the context does not decide: the tactics can split *)
(* on it (PARSE3AUX_SPLIT_RETRY_TAC)                                         *)
exception Parse3aux_undecided of term;;

(* an input list whose shape (empty or not) the evaluator needs *)
exception Parse3aux_lsplit of term;;

let PARSE3AUX_decide_ctx asl tm =
  try PARSE3AUX_decide_asm asl tm with Failure _ ->
  let th = PARSE3AUX_DECIDE_CONV tm in
  let r = rhs(concl th) in
  let facts = PARSE3AUX_ctxfacts asl in
  let prove_r r =
    TAC_PROOF((map (fun th -> ("",th)) facts, r),
              ASM_REWRITE_TAC[] THEN NO_TAC) in
  try (true, EQ_MP (SYM th) (prove_r r))
  with Failure _ ->
  try (false, CONV_RULE (RAND_CONV (K (SYM th))) (prove_r (mk_neg r)))
  with Failure _ -> raise (Parse3aux_undecided r);;

(* a membership of a token in a set that the decision procedure refutes *)
let PARSE3AUX_MEM_CONTR_TAC : tactic = fun (asl,w as g) ->
  let th = find (fun th -> let c = concl th in
      (try fst(dest_const(fst(strip_comb c))) = "IN" &&
           type_of(lhand c) = PARSE3AUX_token_ty with Failure _ -> false) &&
      (try rhs(concl(PARSE3AUX_DECIDE_CONV c)) = `F` with Failure _ -> false))
      (map snd asl) in
  CONTR_TAC (CONV_RULE PARSE3AUX_DECIDE_CONV th) g;;

(* the stopper condition ~(rest = []) ==> FST (HD rest) IN stoppers y *)
let PARSE3AUX_STOPPERS_TAC : tactic = fun (asl,w as g) ->
  (REWRITE_TAC[NOT_CONS_NIL; HD; FST] THEN
   (FIRST_ASSUM ACCEPT_TAC ORELSE
    (CONV_TAC PARSE3AUX_DECIDE_CONV THEN NO_TAC) ORELSE
    (fun (asl,w as g) ->
       let mems = PARSE3AUX_memfacts asl w in
       if mems = [] then failwith "no mems" else
       ACCEPT_TAC (PARSE3AUX_prove_with_mems mems w) g) ORELSE
    (FIRST_ASSUM(fun th -> if is_imp(concl th) &&
        (try fst(dest_const(fst(strip_comb(rand(rand(concl th)))))) = "stoppers"
         with Failure _ -> false) then MP_TAC th else failwith "") THEN
     REWRITE_TAC PARSE3AUX_SETS_RWTS THEN SET_TAC[]))) g;;

let PARSE3AUX_IHSIDE_TAC : tactic = fun (asl,w as g) ->
  let lenfacts = filter (fun th -> let c = concl th in
       (is_binary "<" c || is_binary "<=" c) &&
       (try fst(dest_const(rator(rand c))) = "LENGTH" with Failure _ -> false))
     (map snd asl) in
  (REPEAT CONJ_TAC THENL
    [(DISJ1_TAC THEN MAP_EVERY MP_TAC lenfacts THEN
      REWRITE_TAC[LENGTH; LENGTH_APPEND] THEN ARITH_TAC) ORELSE
     (DISJ2_TAC THEN CONJ_TAC THENL
       [CONV_TAC(BINOP_CONV PARSE3AUX_NORM_CONV) THEN REFL_TAC;
        PARSE3AUX_RANK_TAC]);
     ASM_REWRITE_TAC[];
     ASM_REWRITE_TAC[];
     REWRITE_TAC[FDOM_cmlPEG_nts];
     PARSE3AUX_STOPPERS_TAC;
     ASM_REWRITE_TAC[]]) g;;

let PARSE3AUX_NTS_GEXPRS e =
  REWRITE_RULE[cmlPEG_pnt_def]
   (TAC_PROOF(([], mk_comb(mk_comb(PARSE3AUX_IN_PEGSYM_TM,e),PARSE3AUX_GEXPRS_TM)),
              REWRITE_TAC[NTS_in_PEG_exprs]));;

(* the subtrees with their fringes, and the head of a subtree *)
let PARSE3AUX_fringe_pairs asl =
  mapfilter (fun (_,th) ->
      let c = concl th in
      if is_eq c && is_comb(lhs c) &&
         (try fst(dest_const(rator(lhs c))) = "real_fringe" with Failure _ -> false)
      then (rand(lhs c), rand(rand c)) else failwith "") asl;;

let PARSE3AUX_head_of asl x =
  let hd_th = snd(find (fun (_,th) -> let c = concl th in is_eq c &&
                  lhs c = mk_comb(PARSE3AUX_PTREE_HEAD_TM, x)) asl) in
  rand(rand(rhs(concl hd_th)));;

(* the rest of inp after the prefix fr (both in normal form) *)
let rec PARSE3AUX_split_prefix fr inp =
  if fr = PARSE3AUX_NIL_INP_TM then inp
  else if is_cons fr then
    let h,t = dest_cons fr and h',t' = dest_cons inp in
    if h <> h' then failwith "split_prefix" else PARSE3AUX_split_prefix t t'
  else if is_binary "APPEND" fr then
    let v,t = dest_binary "APPEND" fr and v',t' = dest_binary "APPEND" inp in
    if v <> v' then failwith "split_prefix" else PARSE3AUX_split_prefix t t'
  else if fr = inp then PARSE3AUX_NIL_INP_TM
  else
    let v',t' = dest_binary "APPEND" inp in
    if v' <> fr then failwith "split_prefix" else t';;

(* the subtrees of the goal, in order (set by PARSE3AUX_EVAL_TAC) *)
let PARSE3AUX_tree_order = ref ([]:term list);;

let PARSE3AUX_index x l =
  let rec ix n l = match l with [] -> n | h::t -> if h = x then n else ix (n+1) t in
  ix 0 l;;

let rec PARSE3AUX_vars_lr tm acc =
  match tm with
    Var(_,_) -> if mem tm acc then acc else acc @ [tm]
  | Comb(f,a) -> PARSE3AUX_vars_lr a (PARSE3AUX_vars_lr f acc)
  | Abs(v,b) -> subtract (PARSE3AUX_vars_lr b acc) [v]
  | Const(_,_) -> acc;;

let PARSE3AUX_trees_of tm =
  filter (fun v -> type_of v = PARSE3AUX_mlptree_ty) (PARSE3AUX_vars_lr tm []);;

(* the induction hypothesis for a subtree of head y whose fringe starts inp *)
(* (not one of the subtrees used already, the first one in the goal order)  *)
let PARSE3AUX_ih_apply asl used inp y =
  let ihs = assoc "ihs" asl in
  let try_fr (x,fr) =
    let y' = PARSE3AUX_head_of asl x in
    if y' <> y then failwith "head" else
    let rest = PARSE3AUX_split_prefix (PARSE3AUX_norm fr) inp in
    if PARSE3AUX_norm (mk_comb(mk_comb(`APPEND:(token#locs)list->(token#locs)list->(token#locs)list`, fr), rest)) <> inp
    then failwith "input" else
    let th1 = ISPECL [x; y; fr; rest] ihs in
    let side = lhand(concl th1) in
    let sth = TAC_PROOF((asl,side), PARSE3AUX_IHSIDE_TAC) in
    CONV_RULE (RATOR_CONV(RAND_CONV(LAND_CONV PARSE3AUX_NORM_CONV))) (MP th1 sth) in
  let cands = filter (fun (x,_) -> not (mem x used)) (PARSE3AUX_fringe_pairs asl) in
  let ord = !PARSE3AUX_tree_order in
  let cands = sort (fun (x1,_) (x2,_) -> PARSE3AUX_index x1 ord < PARSE3AUX_index x2 ord) cands in
  tryfind try_fr cands;;

(* the non-terminals whose rules the evaluator unfolds (instead of using  *)
(* the induction hypothesis)                                               *)
let PARSE3AUX_unfold_nts = ref ([]:term list);;

let PARSE3AUX_with_unfold (nts:term list) f x =
  let old = !PARSE3AUX_unfold_nts in
  PARSE3AUX_unfold_nts := nts;
  try let r = f x in PARSE3AUX_unfold_nts := old; r
  with e -> (PARSE3AUX_unfold_nts := old; raise e);;

(* from an evaluation of the rule of n to an evaluation of peg_nt n I *)
let PARSE3AUX_wrap_nt n inp th1 =
  let fdom = EQT_ELIM(REWRITE_CONV[FDOM_cmlPEG_nts]
               (mk_comb(mk_comb(PARSE3AUX_IN_NT_TM, n),
                        PARSE3AUX_FDOM_RULES_TM))) in
  let th2 = MP (ISPECL [PARSE3AUX_CMLPEG_TM; n; inp; PARSE3AUX_I_TM;
                        rand(concl th1)] peg_eval_nt) (CONJ fdom th1) in
  CONV_RULE (RAND_CONV (REWRITE_CONV[resultmap_def; I_THM])) th2;;

(* the failure of peg_nt n I on inp: on the empty input when it is not peg0,  *)
(* or when the first token cannot start n                                   *)
let PARSE3AUX_nt_failure asl inp e n =
      if inp = PARSE3AUX_NIL_INP_TM then
        let th = MP (ISPECL [PARSE3AUX_CMLPEG_TM; e] not_peg0_peg_eval_NIL_NONE)
                    (CONJ (REWRITE_RULE[cmlPEG_pnt_def]
                             (find (fun t -> rand(rand(concl t)) = e) PARSE3AUX_npeg0_ths))
                     (CONJ (PARSE3AUX_NTS_GEXPRS e) PEG_wellformed)) in
        SELECT_RULE (SELECT_RULE th)
      else if is_cons inp then
        let h,t = dest_cons inp in
        let tk,l = dest_pair h in
        let mem = mk_comb(mk_comb(PARSE3AUX_IN_TOKEN_TM, tk),
                   mk_comb(PARSE3AUX_FIRSTSET_TM, mk_list([mk_comb(PARSE3AUX_NT_TM, n)], PARSE3AUX_symbol_ty))) in
        let b,mth = PARSE3AUX_decide_asm asl mem in
        if b then failwith ("PARSE3AUX_eval nt: possible start " ^ string_of_term inp) else
        let sth = CONJ mth
                    (CONJ (REWRITE_RULE[cmlPEG_pnt_def]
                             (find (fun t -> rand(rand(concl t)) = e) PARSE3AUX_npeg0_ths))
                          (PARSE3AUX_NTS_GEXPRS e)) in
        MP (ISPECL [n; t; tk; l] fFail_def) sth
      else failwith ("PARSE3AUX_eval nt: " ^ string_of_term inp);;

(* ------------------------------------------------------------------------- *)
(* Mono mode: the evaluation on an input extended by the suffix             *)
(* !PARSE3AUX_mono_sfx, where the non-terminals and repetitions use the     *)
(* facts of the evaluation on the original input with the monotonicity      *)
(* lemmas of the tables below or the induction hypothesis labelled "mih"    *)
(* ------------------------------------------------------------------------- *)

let PARSE3AUX_mono_mode = ref false;;

let PARSE3AUX_mono_sfx = ref `[]:(token#locs)list`;;

let PARSE3AUX_mono_lemmas = ref ([]:(term*thm)list);;

let PARSE3AUX_mono_none_lemmas = ref ([]:(term*thm)list);;

let PARSE3AUX_mono_list_lemmas = ref ([]:(term*thm)list);;

let PARSE3AUX_with_mono sfx f x =
  let old = !PARSE3AUX_mono_mode and olds = !PARSE3AUX_mono_sfx in
  PARSE3AUX_mono_mode := true; PARSE3AUX_mono_sfx := sfx;
  try let r = f x in PARSE3AUX_mono_mode := old; PARSE3AUX_mono_sfx := olds; r
  with e -> (PARSE3AUX_mono_mode := old; PARSE3AUX_mono_sfx := olds; raise e);;

let PARSE3AUX_eval_parts c =
  let ie = rand(rator c) in
  let x,e = dest_pair ie in x, e, rand c;;

let PARSE3AUX_APPEND_TM =
  `APPEND:(token#locs)list->(token#locs)list->(token#locs)list`;;

(* the side conditions of the induction hypotheses and of the conditional *)
(* monotonicity lemmas: lengths and ranks, membership of the non-terminal, *)
(* stopper conditions and the evaluation fact                               *)
let PARSE3AUX_CLEN_TAC : tactic = fun (asl,w as g) ->
  let lenfacts = filter (fun th -> let c = concl th in
       is_binary "<" c || is_binary "<=" c) (map snd asl) in
  (MAP_EVERY MP_TAC lenfacts THEN REWRITE_TAC[LENGTH; LENGTH_APPEND] THEN
   ARITH_TAC) g;;

let PARSE3AUX_MONO_SIDE_TAC : tactic =
  REPEAT CONJ_TAC THEN
  FIRST [FIRST_ASSUM ACCEPT_TAC;
         DISJ1_TAC THEN PARSE3AUX_CLEN_TAC;
         DISJ2_TAC THEN CONJ_TAC THENL
          [CONV_TAC(BINOP_CONV PARSE3AUX_NORM_CONV) THEN REFL_TAC;
           PARSE3AUX_RANK_TAC];
         REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN CASE_REWRITE_TAC[] THEN NO_TAC;
         PARSE3AUX_STOPPERS_TAC];;

(* the conditional monotonicity lemmas: !N i0 i r sfx eo. side /\ ev ==> ev' *)
let PARSE3AUX_mono_cond_lemmas = ref ([]:(term*thm)list);;

let PARSE3AUX_mono_nt asl inp n =
  let y = rand n in
  let sfx = !PARSE3AUX_mono_sfx in
  let ntI = mk_comb(mk_comb(PARSE3AUX_NTSYM_TM, n),
                    PARSE3AUX_I_TM) in
  let facts = filter (fun th -> PARSE3AUX_is_evalfact (concl th) &&
                        (let _,e,_ = PARSE3AUX_eval_parts (concl th) in e = ntI))
                     (map snd asl) in
  let app x = PARSE3AUX_norm (mk_comb(mk_comb(PARSE3AUX_APPEND_TM, x), sfx)) in
  let try_fact f =
    let x,_,res = PARSE3AUX_eval_parts (concl f) in
    if app x <> inp then failwith "input" else
    if PARSE3AUX_is_succ f then
      let i',r',eo' = PARSE3AUX_succ_parts f in
      let cond ih =
        let th1 = ISPECL [y; x; i'; r'; sfx; eo'] ih in
        MP th1 (TAC_PROOF((asl, lhand(concl th1)), PARSE3AUX_MONO_SIDE_TAC)) in
      let th =
        try MP (ISPECL [x; i'; r'; eo'; sfx] (assoc y !PARSE3AUX_mono_lemmas)) f
        with Failure _ ->
        try cond (assoc y !PARSE3AUX_mono_cond_lemmas)
        with Failure _ -> cond (assoc "mih" asl) in
      CONV_RULE (RATOR_CONV(RAND_CONV(LAND_CONV PARSE3AUX_NORM_CONV)) THENC
                 RAND_CONV (RATOR_CONV(RATOR_CONV(RAND_CONV PARSE3AUX_NORM_CONV)))) th
    else if x = inp then f else
      let tl,t = try dest_cons x with Failure _ ->
                   if is_var x then raise (Parse3aux_lsplit x) else failwith "x" in
      let tk,l = dest_pair tl in
      let fl,fe = PARSE3AUX_fail_parts f in
      let th = MP (ISPECL [tk; l; t; sfx; fl; fe]
                          (assoc y !PARSE3AUX_mono_none_lemmas)) f in
      CONV_RULE (RATOR_CONV(RAND_CONV(LAND_CONV PARSE3AUX_NORM_CONV))) th in
  tryfind try_fact facts;;

let rec PARSE3AUX_strip_pair t =
  try let a,b = dest_pair t in a :: PARSE3AUX_strip_pair b with Failure _ -> [t];;

let PARSE3AUX_mono_rpt asl inp e1 f =
  let y = rand(rand(rator e1)) in
  let sfx = !PARSE3AUX_mono_sfx in
  let facts = filter (fun th -> PARSE3AUX_is_listfact (concl th) &&
                        snd(dest_pair(rand(rator(concl th)))) = e1)
                     (map snd asl) in
  let app x = PARSE3AUX_norm (mk_comb(mk_comb(PARSE3AUX_APPEND_TM, x), sfx)) in
  let try_fact fct =
    let x = fst(dest_pair(rand(rator(concl fct)))) in
    if app x <> inp then failwith "input" else
    let yy,l,err = (match PARSE3AUX_strip_pair (rand(concl fct)) with
                      [a;b;c;d] -> a,b,mk_pair(c,d) | [a;b;c] -> a,b,c
                    | _ -> failwith "list fact") in
    let eth =
      try
        let lemma = ISPECL [l; err; x; yy; sfx] (assoc y !PARSE3AUX_mono_list_lemmas) in
        let cnd = rand(lhand(concl lemma)) in
        let cth = TAC_PROOF((asl, cnd), PARSE3AUX_STOPPERS_TAC) in
        MP lemma (CONJ fct cth)
      with Failure _ ->
        (* the induction hypothesis on lists "mihl" *)
        let ih = ISPEC x (assoc "mihl" asl) in
        let ih1 = MP ih (TAC_PROOF((asl, lhand(concl ih)), PARSE3AUX_CLEN_TAC)) in
        let ih2 = ISPECL [l; yy; err; sfx] ih1 in
        MP ih2 (TAC_PROOF((asl, lhand(concl ih2)), PARSE3AUX_MONO_SIDE_TAC)) in
    let lth = CONV_RULE (RATOR_CONV(RAND_CONV(LAND_CONV PARSE3AUX_NORM_CONV)) THENC
                         RAND_CONV(LAND_CONV PARSE3AUX_NORM_CONV))
                (SELECT_RULE eth) in
    let s1,_ = dest_pair(rand(concl lth)) in
    let tl = rand(rand(rand(concl lth))) in
    MP (ISPECL [PARSE3AUX_CMLPEG_TM; e1; f; app x; s1; l; tl] LPARSEAUX_peg_eval_rpt_rule) lth in
  tryfind try_fact facts;;

(* an evaluation fact of the context for e on inp *)
let PARSE3AUX_fact_lookup asl inp e =
  CONV_RULE (RATOR_CONV(RAND_CONV(LAND_CONV PARSE3AUX_NORM_CONV)))
   (snd(find (fun (_,th) -> let c = concl th in
               PARSE3AUX_is_evalfact c &&
               (let x,e',_ = PARSE3AUX_eval_parts c in e' = e && PARSE3AUX_norm x = inp))
            asl));;

(* a list evaluation fact of the context for e on inp *)
let PARSE3AUX_list_fact_lookup asl inp e =
  CONV_RULE (RATOR_CONV(RAND_CONV(LAND_CONV PARSE3AUX_NORM_CONV)))
   (snd(find (fun (_,th) -> let c = concl th in
               PARSE3AUX_is_listfact c &&
               (let x,e' = dest_pair(rand(rator c)) in
                e' = e && PARSE3AUX_norm x = inp))
            asl));;

(* split abstract input lists at token tests (off in the completeness cases,  *)
(* where the suffix is split by PARSE3AUX_SFX_SPLIT_TAC)                      *)
let PARSE3AUX_lsplit_vars = ref false;;

let rec PARSE3AUX_eval_u (asl:(string*thm)list) (used:term list) (inp:term) (e:term) : thm =
  let fn,args = strip_comb e in
  let c = fst(dest_const fn) in
  match c, args with
    "empty", [r] ->
      ISPECL [PARSE3AUX_CMLPEG_TM; inp; r] LPARSEAUX_peg_eval_empty_rule
  | "peg_tok", [p;f] ->
      if inp = PARSE3AUX_NIL_INP_TM then
        ISPECL [PARSE3AUX_CMLPEG_TM; p; f] peg_eval_tok_failureEOF
      else if is_cons inp then
        let h,t = dest_cons inp in
        let b,th = PARSE3AUX_decide_ctx asl (mk_comb(p, mk_comb(PARSE3AUX_FST_TOKEN_TM, h))) in
        if b then MP (ISPECL [PARSE3AUX_CMLPEG_TM; h; t; p; f] peg_eval_tok_success) th
        else MP (ISPECL [PARSE3AUX_CMLPEG_TM; h; t; p; f] peg_eval_tok_failureF) th
      else if is_var inp && !PARSE3AUX_lsplit_vars then raise (Parse3aux_lsplit inp)
      else failwith ("PARSE3AUX_eval tok: " ^ string_of_term inp)
  | "peg_nt", [n;f] when mem (rand n) !PARSE3AUX_unfold_nts ->
      PARSE3AUX_eval_nt_unfold asl used inp n
  | "peg_nt", [n;f] when !PARSE3AUX_mono_mode ->
      (try PARSE3AUX_mono_nt asl inp n with Failure _ ->
         PARSE3AUX_nt_failure asl inp e n)
  | "peg_nt", [n;f] ->
      let y = rand n in
      (try PARSE3AUX_fact_lookup asl inp e with Failure _ ->
       try PARSE3AUX_ih_apply asl used inp y with Failure _ ->
         PARSE3AUX_nt_failure asl inp e n)
  | "peg_rpt", [e1;f] when !PARSE3AUX_mono_mode ->
      PARSE3AUX_mono_rpt asl inp e1 f
  | "peg_rpt", [e1;f] ->
      let lth = try PARSE3AUX_list_fact_lookup asl inp e1
                with Failure _ -> PARSE3AUX_eval_list asl used inp e1 in
      let s2,rest = dest_pair(rand(concl lth)) in
      let cs,err = dest_pair rest in
      MP (ISPECL [PARSE3AUX_CMLPEG_TM; e1; f; inp; s2; cs; err] LPARSEAUX_peg_eval_rpt_rule) lth
  | "peg_seq", [e1;e2;f] ->
      let th1 = PARSE3AUX_eval_u asl used inp e1 in
      if PARSE3AUX_is_succ th1 then
        let s1,c1,eo1 = PARSE3AUX_succ_parts th1 in
        let s1' = PARSE3AUX_norm s1 in
        let th1 = if s1' = s1 then th1 else
                  CONV_RULE (RAND_CONV (RATOR_CONV(RATOR_CONV(RAND_CONV
                     PARSE3AUX_NORM_CONV)))) th1 in
        let th2 = PARSE3AUX_eval_u asl (used @ PARSE3AUX_trees_of c1) s1' e2 in
        if PARSE3AUX_is_succ th2 then
          let s2,c2,eo2 = PARSE3AUX_succ_parts th2 in
          MP (ISPECL [PARSE3AUX_CMLPEG_TM; e1; e2; inp; s1'; s2; c1; c2; f; eo1; eo2]
                     peg_eval_seq_success) (CONJ th1 th2)
        else
          let fl,fe = PARSE3AUX_fail_parts th2 in
          MP (ISPECL [PARSE3AUX_CMLPEG_TM; e1; e2; f; inp; eo1; s1'; c1; fl; fe]
                     peg_eval_seq_fail2) (CONJ th1 th2)
      else
        let fl,fe = PARSE3AUX_fail_parts th1 in
        MP (ISPECL [PARSE3AUX_CMLPEG_TM; e1; e2; inp; f; fl; fe] peg_eval_seq_fail1) th1
  | "choice", [e1;e2;f] ->
      let th1 = PARSE3AUX_eval_u asl used inp e1 in
      if PARSE3AUX_is_succ th1 then
        let s,r,eo = PARSE3AUX_succ_parts th1 in
        MP (ISPECL [PARSE3AUX_CMLPEG_TM; e1; e2; inp; f; s; r; eo] peg_eval_choice_success1) th1
      else
        let fl,fe = PARSE3AUX_fail_parts th1 in
        let th2 = PARSE3AUX_eval_u asl used inp e2 in
        if PARSE3AUX_is_succ th2 then
          let s,r,eo = PARSE3AUX_succ_parts th2 in
          MP (ISPECL [PARSE3AUX_CMLPEG_TM; e1; e2; inp; s; r; eo; f; fl; fe]
                     peg_eval_choice_success2) (CONJ th1 th2)
        else
          let fl2,fe2 = PARSE3AUX_fail_parts th2 in
          CONV_RULE (RAND_CONV (REWR_CONV PARSE3AUX_UNCURRY_Failure))
            (MP (ISPECL [PARSE3AUX_CMLPEG_TM; e1; e2; inp; f; fl; fe; fl2; fe2]
                        peg_eval_choice_fail) (CONJ th1 th2))
  | "peg_not", [e1;c] ->
      let th1 = PARSE3AUX_eval_u asl used inp e1 in
      if PARSE3AUX_is_succ th1 then
        let r = PARSE3AUX_res th1 in
        CONV_RULE (RAND_CONV (REWRITE_CONV[peg_sloc_def; SND]))
          (MP (ISPECL [PARSE3AUX_CMLPEG_TM; e1; inp; r; c] peg_eval_not_failure)
             (CONJ th1 (EQT_ELIM (REWRITE_CONV[isSuccess_def]
                (mk_comb(`isSuccess:((token#locs)list,(mlptree)list,(char)list)pegresult->bool`, r))))))
      else failwith "PARSE3AUX_eval not: inner failure"
  | _ -> (try PARSE3AUX_fact_lookup asl inp e
          with Failure _ -> failwith ("PARSE3AUX_eval: " ^ c))

and PARSE3AUX_eval_list asl used inp e1 =
  let th1 = PARSE3AUX_eval_u asl used inp e1 in
  if PARSE3AUX_is_succ th1 then
    let s1,c1,eo1 = PARSE3AUX_succ_parts th1 in
    let s1' = PARSE3AUX_norm s1 in
    if s1' = inp then failwith "PARSE3AUX_eval_list: no progress" else
    let th1 = if s1' = s1 then th1 else
              CONV_RULE (RAND_CONV (RATOR_CONV(RATOR_CONV(RAND_CONV
                 PARSE3AUX_NORM_CONV)))) th1 in
    let lth = PARSE3AUX_eval_list asl (used @ PARSE3AUX_trees_of c1) s1' e1 in
    let s2,rest = dest_pair(rand(concl lth)) in
    let cs,eo = dest_pair rest in
    MP (ISPECL [PARSE3AUX_CMLPEG_TM; e1; eo1; eo; inp; s1'; s2; c1; cs] peg_eval_list_cons)
       (CONJ th1 lth)
  else
    let fl,fe = PARSE3AUX_fail_parts th1 in
    MP (ISPECL [PARSE3AUX_CMLPEG_TM; e1; inp; fl; fe] peg_eval_list_nil) th1

and PARSE3AUX_eval_nt_unfold asl used inp n =
  let rule_th = PARSE2AUX_rule (rand n) in
  let prim_th = PARSE3AUX_PRIM_CONV (rhs(concl rule_th)) in
  let th = PARSE3AUX_eval_u asl used inp (rhs(concl prim_th)) in
  let th1 = CONV_RULE (RATOR_CONV(RAND_CONV(RAND_CONV
              (REWR_CONV (SYM prim_th) THENC REWR_CONV (SYM rule_th))))) th in
  PARSE3AUX_wrap_nt n inp th1;;

let PARSE3AUX_eval asl inp e = PARSE3AUX_eval_u asl [] inp e;;

let PARSE3AUX_SKOLEM_IH_TAC : tactic =
  USE_THEN "ih" (MP_TAC o REWRITE_RULE[GSYM RIGHT_EXISTS_IMP_THM; SKOLEM_THM]) THEN
  DISCH_THEN(X_CHOOSE_THEN
    `ihf:mlptree->MMLnonT->(token#locs)list->(token#locs)list->(locs#(char)list)option`
    (LABEL_TAC "ihs"));;

(* the result functions that are matches (evaluated by CASE_REWRITE_CONV) *)
let PARSE3AUX_RESULT_CASE_RWTS = [peg_EbaseParenFn_def; destLf_def; destTOK_def];;

let PARSE3AUX_RESULT_RWTS =
  [sumID_def; bindNT_def; bindNT0_lemma; mktokLf_def; APPEND; APPEND_NIL; I_THM;
   o_THM; FST; SND; resultmap_def; FLAT; LENGTH; ARITH_RULE `SUC 0 = 1`;
   ARITH_RULE `~(SUC (SUC n) = 1)`];;

(* contradictory length facts *)
let PARSE3AUX_LEN_CONTR_TAC : tactic = fun (asl,w as g) ->
  let lenfacts = filter (fun th -> let c = concl th in
       is_binary "<" c || is_binary "<=" c) (map snd asl) in
  (SUBGOAL_THEN `F` CONTR_TAC THEN MAP_EVERY MP_TAC lenfacts THEN
   REWRITE_TAC[LENGTH; LENGTH_APPEND] THEN ARITH_TAC) g;;

(* run tac; when it meets an undecided token test, split on it and retry; *)
(* when it needs the shape of an input list, split it and retry            *)
let rec PARSE3AUX_SPLIT_RETRY_TAC (k:int) (tac:tactic) : tactic = fun g ->
  try tac g with
    Parse3aux_undecided r ->
      if k <= 0 then failwith ("PARSE3AUX_SPLIT_RETRY_TAC: " ^ string_of_term r) else
      (ASM_CASES_TAC r THENL
        [FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th -> concl th = r)) THEN
         RVEQ_TAC;
         FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[] o
                       check (fun th -> concl th = mk_neg r))] THEN
       PARSE3AUX_SPLIT_RETRY_TAC (k-1) tac) g
  | Parse3aux_lsplit x ->
      if k <= 0 then failwith ("PARSE3AUX_SPLIT_RETRY_TAC: " ^ string_of_term x) else
      let asl,w = g in
      let avoid = itlist (fun (_,th) l -> union (thm_frees th) l) asl (frees w) in
      let mk n ty = variant avoid (mk_var(n,ty)) in
      let hv = mk "PARSE3AUX_h" `:token#locs`
      and tv = mk "PARSE3AUX_t" PARSE3AUX_inp_ty
      and tkv = mk "PARSE3AUX_tk" PARSE3AUX_token_ty
      and lv = mk "PARSE3AUX_l" PARSE3AUX_locs_ty in
      (MP_TAC(ISPEC x list_CASES) THEN
       DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC
         (X_CHOOSE_THEN hv (X_CHOOSE_THEN tv SUBST_ALL_TAC))) THENL
        [ALL_TAC;
         MP_TAC(ISPEC hv PAIR_SURJECTIVE) THEN
         DISCH_THEN(X_CHOOSE_THEN tkv (X_CHOOSE_THEN lv SUBST_ALL_TAC))] THEN
       (PARSE3AUX_LEN_CONTR_TAC ORELSE PARSE3AUX_SPLIT_RETRY_TAC (k-1) tac)) g;;

let PARSE3AUX_EVAL0_TAC : tactic = fun (asl,w as g) ->
  let v,ev = dest_exists w in
  let pr = rand(rator ev) in
  let inp,nte = dest_pair pr in
  let n = rand(rator nte) in
  let x = rand n in
  let rule_th = PARSE2AUX_rule x in
  let prim_th = PARSE3AUX_PRIM_CONV (rhs(concl rule_th)) in
  let inp' = PARSE3AUX_norm inp in
  let tgt = hd(dest_list(rand(rator(rand ev)))) in
  PARSE3AUX_tree_order := PARSE3AUX_trees_of tgt;
  let th = PARSE3AUX_eval asl inp' (rhs(concl prim_th)) in
  let th1 = CONV_RULE (RATOR_CONV(RAND_CONV(RAND_CONV
              (REWR_CONV (SYM prim_th) THENC REWR_CONV (SYM rule_th))))) th in
  let fdom = EQT_ELIM(REWRITE_CONV[FDOM_cmlPEG_nts]
               (mk_comb(mk_comb(PARSE3AUX_IN_NT_TM, n),
                        PARSE3AUX_FDOM_RULES_TM))) in
  let th2 = MP (ISPECL [PARSE3AUX_CMLPEG_TM; n; inp'; PARSE3AUX_I_TM;
                        PARSE3AUX_res th1] peg_eval_nt) (CONJ fdom th1) in
  let th3 = CONV_RULE (RAND_CONV (REWRITE_CONV PARSE3AUX_RESULT_RWTS THENC
                                  CASE_REWRITE_CONV PARSE3AUX_RESULT_CASE_RWTS THENC
                                  REWRITE_CONV PARSE3AUX_RESULT_RWTS)) th2 in
  let _,_,eo = PARSE3AUX_succ_parts th3 in
  (EXISTS_TAC eo THEN
   CONV_TAC(LAND_CONV(LAND_CONV PARSE3AUX_NORM_CONV)) THEN
   MP_TAC th3 THEN REWRITE_TAC PARSE3AUX_RESULT_RWTS THEN
   DISCH_THEN ACCEPT_TAC) g;;

let PARSE3AUX_EVAL_TAC : tactic = PARSE3AUX_SPLIT_RETRY_TAC 3 PARSE3AUX_EVAL0_TAC;;

(* the evaluation, leaving the equation of the results as the goal *)
let PARSE3AUX_EVAL_EQ_LEMMA = prove
 (`!(G:(A,B,C,E)peg) x s r1 r2.
     (?eo. peg_eval G x (peg_Success s r1 eo)) /\ r1 = r2 ==>
     ?eo. peg_eval G x (peg_Success s r2 eo)`,
  MESON_TAC[]);;

let PARSE3AUX_EVAL_EQ_TAC : tactic = fun (asl,w as g) ->
  let v,ev = dest_exists w in
  let pr = rand(rator ev) in
  let inp,nte = dest_pair pr in
  let n = rand(rator nte) in
  let x = rand n in
  let rule_th = PARSE2AUX_rule x in
  let prim_th = PARSE3AUX_PRIM_CONV (rhs(concl rule_th)) in
  let inp' = PARSE3AUX_norm inp in
  let th = PARSE3AUX_eval asl inp' (rhs(concl prim_th)) in
  let th1 = CONV_RULE (RATOR_CONV(RAND_CONV(RAND_CONV
              (REWR_CONV (SYM prim_th) THENC REWR_CONV (SYM rule_th))))) th in
  let fdom = EQT_ELIM(REWRITE_CONV[FDOM_cmlPEG_nts]
               (mk_comb(mk_comb(PARSE3AUX_IN_NT_TM, n),
                        PARSE3AUX_FDOM_RULES_TM))) in
  let th2 = MP (ISPECL [PARSE3AUX_CMLPEG_TM; n; inp'; PARSE3AUX_I_TM;
                        PARSE3AUX_res th1] peg_eval_nt) (CONJ fdom th1) in
  let th3 = CONV_RULE (RAND_CONV (REWRITE_CONV PARSE3AUX_RESULT_RWTS)) th2 in
  let _,r1,eo = PARSE3AUX_succ_parts th3 in
  (MATCH_MP_TAC PARSE3AUX_EVAL_EQ_LEMMA THEN EXISTS_TAC r1 THEN CONJ_TAC THENL
    [EXISTS_TAC eo THEN CONV_TAC(LAND_CONV(LAND_CONV PARSE3AUX_NORM_CONV)) THEN
     MP_TAC th3 THEN REWRITE_TAC[] THEN DISCH_THEN ACCEPT_TAC;
     ALL_TAC]) g;;

(* split sfx into [] and CONS (stk,sl) sfx' with stk in the stoppers *)
let PARSE3AUX_SFX_SPLIT_TAC : tactic = fun (asl,w as g) ->
  let sth = snd(find (fun (_,th) -> let c = concl th in is_imp c &&
        (try fst(dest_const(fst(strip_comb(rand(rand c))))) = "stoppers"
         with Failure _ -> false)) asl) in
  let sfx = lhand(rand(lhand(concl sth))) in
  (MP_TAC (ISPEC sfx list_CASES) THEN
   DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC
     (X_CHOOSE_THEN `sfx_h:token#locs` (X_CHOOSE_THEN `sfx_t:(token#locs)list`
        SUBST_ALL_TAC))) THENL
   [ALL_TAC;
    MP_TAC(ISPEC `sfx_h:token#locs` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `stk:token` (X_CHOOSE_THEN `sl:locs` SUBST_ALL_TAC)) THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) &&
        (try fst(dest_const(fst(strip_comb(rand(rand(concl th)))))) = "stoppers"
         with Failure _ -> false))) THEN
    REWRITE_TAC[NOT_CONS_NIL; HD; FST] THEN DISCH_TAC THEN
    SUBGOAL_THEN (mk_imp(mk_neg(mk_eq(`CONS (stk:token,sl:locs) sfx_t`,PARSE3AUX_NIL_INP_TM)),
                         mk_comb(mk_comb(PARSE3AUX_IN_TOKEN_TM,
                                         mk_comb(PARSE3AUX_FST_TOKEN_TM, mk_comb(`HD:(token#locs)list->token#locs`, `CONS (stk:token,sl:locs) sfx_t`))),
                                 rand(rand(concl sth)))))
      ASSUME_TAC THENL [ASM_REWRITE_TAC[NOT_CONS_NIL; HD; FST]; ALL_TAC]]) g;;

let PARSE3AUX_SPLIT_CONJ_ASM_TAC : tactic =
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)));;

let PARSE3AUX_CCASE_TAC : tactic =
  PARSE3AUX_CSTART_TAC THEN PARSE3AUX_SPLIT_CONJ_ASM_TAC THEN
  PARSE3AUX_SKOLEM_IH_TAC THEN PARSE3AUX_DESTRUCT_TAC THEN
  TRY(PARSE3AUX_EVAL_TAC ORELSE
      (PARSE3AUX_SFX_SPLIT_TAC THEN
       (PARSE3AUX_MEM_CONTR_TAC ORELSE PARSE3AUX_EVAL_TAC)));;

(* ------------------------------------------------------------------------- *)
(* Input monotonicity of the non-terminals that look at one token only: the *)
(* evaluation on CONS (tk,lk) t is computed by the evaluator (unfolding the *)
(* rules, splitting on the undecided token tests), compared with the        *)
(* hypothesis by determinism, and instantiated at t := APPEND t sfx.        *)
(* ------------------------------------------------------------------------- *)

let PARSE3AUX_DET_RULE th1 th2 =
  let det = CONJUNCT1 (ISPEC PARSE3AUX_CMLPEG_TM peg_deterministic) in
  EQ_MP (SPEC (rand(concl th2)) (MATCH_MP det th1)) th2;;

(* peg_nt e fails on the empty input *)
let PARSE3AUX_NIL_FAIL_TH e =
  let th = MP (ISPECL [PARSE3AUX_CMLPEG_TM; e] not_peg0_peg_eval_NIL_NONE)
              (CONJ (REWRITE_RULE[cmlPEG_pnt_def]
                       (find (fun t -> rand(rand(concl t)) = e) PARSE3AUX_npeg0_ths))
                    (CONJ (PARSE3AUX_NTS_GEXPRS e) PEG_wellformed)) in
  SELECT_RULE (SELECT_RULE th);;

(* the hypothesis "H": peg_eval cmlPEG (CONS (tk,lk) t, peg_nt N I) res;   *)
(* the goal: the same on the input extended by sfx                         *)
let PARSE3AUX_MONO_EVAL_TAC (nts:term list) : tactic = fun (asl,w as g) ->
  let h = assoc "H" asl in
  let inp,e = dest_pair (rand(rator(concl h))) in
  let th = PARSE3AUX_with_unfold nts (PARSE3AUX_eval asl inp) e in
  let eq = PARSE3AUX_DET_RULE th h in
  let t0 = snd(dest_cons inp) in
  let ginp = PARSE3AUX_norm (fst(dest_pair(rand(rator w)))) in
  let th' = INST [snd(dest_cons ginp), t0] th in
  (MP_TAC eq THEN REWRITE_TAC[pegresult_inject; pegresult_distinct] THEN
   DISCH_THEN(fun e -> REWRITE_TAC(CONJUNCTS e)) THEN
   CONV_TAC(LAND_CONV(LAND_CONV PARSE3AUX_NORM_CONV)) THEN
   ACCEPT_TAC th') g;;

let PARSE3AUX_TOKMONO_TAC (nts:term list) : tactic =
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "H") THEN
  MP_TAC(ISPEC `i0:(token#locs)list` list_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC
     (X_CHOOSE_THEN `h0:token#locs` (X_CHOOSE_THEN `t0:(token#locs)list`
        SUBST_ALL_TAC))) THENL
   [(fun (asl,w as g) ->
      let h = assoc "H" asl in
      let e = rand(rand(rator(concl h))) in
      let fth = PARSE3AUX_NIL_FAIL_TH e in
      CONTR_TAC (REWRITE_RULE[pegresult_distinct] (PARSE3AUX_DET_RULE fth h)) g);
    MP_TAC(ISPEC `h0:token#locs` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `tk:token` (X_CHOOSE_THEN `lk:locs` SUBST_ALL_TAC)) THEN
    PARSE3AUX_SPLIT_RETRY_TAC 12 (PARSE3AUX_MONO_EVAL_TAC nts)];;

let PARSE3AUX_TOKMONO_NONE_TAC (nts:term list) : tactic =
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "H") THEN
  PARSE3AUX_SPLIT_RETRY_TAC 12 (PARSE3AUX_MONO_EVAL_TAC nts);;

(* ------------------------------------------------------------------------- *)
(* Input monotonicity in general: the evaluation of the hypothesis is       *)
(* inverted into facts on the sub-expressions (PARSE3AUX_INV_TAC), and the  *)
(* evaluation on the extended input is replayed by the evaluator in mono    *)
(* mode, where the non-terminals use these facts with the monotonicity     *)
(* lemmas or the induction hypothesis.                                      *)
(* ------------------------------------------------------------------------- *)

let PARSE3AUX_S_not = prove
 (`!(G:(A,B,C,E)peg) i0 e c i r eo.
     peg_eval G (i0, peg_not e c) (peg_Success i r eo) <=>
     (?fl fe. peg_eval G (i0, e) (Failure fl fe)) /\ i = i0 /\ r = c /\ eo = NONE`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [peg_eval_cases] THEN
  REWRITE_TAC[PAIR_EQ; pegsym_distinct; pegsym_inject; pegresult_distinct;
              pegresult_inject] THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM; LEFT_EXISTS_AND_THM; UNWIND_THM1;
              UNWIND_THM2; GSYM CONJ_ASSOC] THEN
  REWRITE_TAC[EXISTS_result; isFailure_def] THEN MESON_TAC[]);;

let PARSE3AUX_F_not = prove
 (`!(G:(A,B,C,E)peg) i0 e c fl fe.
     peg_eval G (i0, peg_not e c) (Failure fl fe) <=>
     (?i r eo. peg_eval G (i0, e) (peg_Success i r eo)) /\
     fl = peg_sloc i0 /\ fe = peg_notFAIL G`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [peg_eval_cases] THEN
  REWRITE_TAC[PAIR_EQ; pegsym_distinct; pegsym_inject; pegresult_distinct;
              pegresult_inject] THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM; LEFT_EXISTS_AND_THM; UNWIND_THM1;
              UNWIND_THM2; GSYM CONJ_ASSOC] THEN
  REWRITE_TAC[EXISTS_result; isSuccess_def] THEN MESON_TAC[]);;

let PARSE3AUX_F_choice = prove
 (`!(G:(A,B,C,E)peg) i0 s1 s2 f fl fe.
     peg_eval G (i0, choice s1 s2 f) (Failure fl fe) <=>
     ?fl1 fe1 fl2 fe2.
       peg_eval G (i0, s1) (Failure fl1 fe1) /\
       peg_eval G (i0, s2) (Failure fl2 fe2) /\
       fl = FST (MAXerr (fl1,fe1) (fl2,fe2)) /\
       fe = SND (MAXerr (fl1,fe1) (fl2,fe2))`,
  REWRITE_TAC[peg_eval_choice; EXISTS_result; isSuccess_def; resultmap_def;
              pegresult_distinct; PARSE3AUX_UNCURRY_Failure; pegresult_inject] THEN
  MESON_TAC[]);;

let PARSE3AUX_S_rpt = prove
 (`!(G:(A,B,C,E)peg) i0 s f i r eo.
     peg_eval G (i0, peg_rpt s f) (peg_Success i r eo) <=>
     ?l err. peg_eval_list G (i0,s) (i,l,err) /\ r = f l /\ eo = SOME err`,
  REWRITE_TAC[peg_eval_rpt; pegresult_inject] THEN MESON_TAC[]);;

let PARSE3AUX_F_rpt = prove
 (`!(G:(A,B,C,E)peg) i0 s f fl fe.
     peg_eval G (i0, peg_rpt s f) (Failure fl fe) <=> F`,
  REWRITE_TAC[peg_eval_rpt; pegresult_distinct]);;

let PARSE3AUX_F_empty = prove
 (`!(G:(A,B,C,E)peg) i0 c fl fe.
     peg_eval G (i0, empty c) (Failure fl fe) <=> F`,
  REWRITE_TAC[peg_eval_empty; pegresult_distinct]);;

let PARSE3AUX_F_tok = prove
 (`!(G:(A,B,C,E)peg) i P f fl fe.
     peg_eval G (i, peg_tok P f) (Failure fl fe) <=>
     (?tk l t. i = CONS (tk,l) t /\ fl = l /\ fe = peg_tokFALSE G /\ ~P tk) \/
     (i = [] /\ fl = Locs EOFpt EOFpt /\ fe = peg_tokEOF G)`,
  REWRITE_TAC[peg_eval_tok_NONE; EXISTS_PAIR_THM; FST; SND]);;

let PARSE3AUX_INV_RWTS =
  [peg_eval_seq_SOME; PARSE3AUX_S_choice; peg_eval_tok_SOME; PARSE3AUX_S_empty;
   PARSE3AUX_S_not; PARSE3AUX_S_rpt;
   peg_eval_seq_NONE; PARSE3AUX_F_choice; PARSE3AUX_F_tok; PARSE3AUX_F_empty;
   PARSE3AUX_F_not; PARSE3AUX_F_rpt];;

let left_insert1_mkNd = prove
 (`!(pt1:mlptree) pt2.
     left_insert1 pt1 (mkNd (INL nEapp) [pt2]) =
     mkNd (INL nEapp) [mkNd (INL nEapp) [pt1]; pt2]`,
  REWRITE_TAC[PARSE3AUX_left_insert1_mkNd1]);;

(* the evaluation of peg_nt nEapp, in terms of nEbase and its repetition *)
let PARSE3AUX_Eapp_intro = prove
 (`!i0 i1 i h eo1 l err x t.
     peg_eval cmlPEG (i0, peg_nt (INL nEbase) I) (peg_Success i1 h eo1) /\
     peg_eval_list cmlPEG (i1, peg_nt (INL nEbase) I) (i, l, err) /\
     APPEND h (FLAT l) = CONS x t ==>
     ?eo. peg_eval cmlPEG (i0, peg_nt (INL nEapp) I)
            (peg_Success i [FOLDL (\a b. mkNd (INL nEapp) [a; b])
                                  (mkNd (INL nEapp) [x]) t] eo)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[peg_eval_NT_SOME; PARSE2AUX_rule `nEapp`; FDOM_cmlPEG_nts; I_THM] THEN
  REWRITE_TAC[seql_cons_SOME; PARSE3AUX_S_seql_NIL; cmlPEG_pnt_def; peg_eval_rpt] THEN
  EXISTS_TAC `NONE:(locs#(char)list)option` THEN
  EXISTS_TAC `[FOLDL (\a b. mkNd (INL nEapp) [a; b]) (mkNd (INL nEapp) [x]) t]:(mlptree)list` THEN
  REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`i1:(token#locs)list`; `h:(mlptree)list`;
                        `FLAT (l:((mlptree)list)list)`; `eo1:(locs#(char)list)option`] THEN
  ASM_REWRITE_TAC[I_THM; APPEND_NIL] THEN
  CONJ_TAC THENL
   [MAP_EVERY EXISTS_TAC [`i:(token#locs)list`; `FLAT (l:((mlptree)list)list)`;
                          `[]:(mlptree)list`; `SOME (err:locs#(char)list)`] THEN
    REWRITE_TAC[APPEND_NIL] THEN
    MAP_EVERY EXISTS_TAC [`i:(token#locs)list`; `l:((mlptree)list)list`;
                          `err:locs#(char)list`] THEN
    ASM_REWRITE_TAC[];
    CASE_REWRITE_TAC[]]);;

let PARSE3AUX_Eapp_inv = prove
 (`!i0 i r eo.
     peg_eval cmlPEG (i0, peg_nt (INL nEapp) I) (peg_Success i r eo) ==>
     ?i1 h eo1 l err.
       peg_eval cmlPEG (i0, peg_nt (INL nEbase) I) (peg_Success i1 h eo1) /\
       peg_eval_list cmlPEG (i1, peg_nt (INL nEbase) I) (i, l, err) /\
       (APPEND h (FLAT l) = [] /\ r = [] \/
        ?x t. APPEND h (FLAT l) = CONS x t /\
              r = [FOLDL (\a b. mkNd (INL nEapp) [a; b]) (mkNd (INL nEapp) [x]) t])`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[peg_eval_NT_SOME; PARSE2AUX_rule `nEapp`;
                                   FDOM_cmlPEG_nts; I_THM]) THEN
  REWRITE_TAC[seql_cons_SOME; PARSE3AUX_S_seql_NIL; cmlPEG_pnt_def; peg_eval_rpt;
              pegresult_inject; I_THM; APPEND_NIL] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  MAP_EVERY EXISTS_TAC [`i1:(token#locs)list`; `rh:(mlptree)list`;
                        `eo1:(locs#(char)list)option`; `l:((mlptree)list)list`;
                        `err:locs#(char)list`] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `APPEND (rh:(mlptree)list) (FLAT (l:((mlptree)list)list))` list_CASES) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[NOT_CONS_NIL; APPEND_NIL] THEN
  CASE_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`h:mlptree`; `t:(mlptree)list`] THEN REWRITE_TAC[]);;

let PARSE3AUX_nt_fail = prove
 (`!N sfx. peg_nt (INL N) I IN Gexprs cmlPEG /\ ~peg0 cmlPEG (peg_nt (INL N) I) /\
           (~(sfx = []) ==> ~(FST (HD sfx) IN firstSet cmlG [NT (INL N)])) ==>
           ?fl fe. peg_eval cmlPEG (sfx, peg_nt (INL N) I) (Failure fl fe)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `sfx:(token#locs)list` list_CASES) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[NOT_CONS_NIL; HD] THENL
   [STRIP_TAC THEN MATCH_MP_TAC not_peg0_peg_eval_NIL_NONE THEN
    ASM_REWRITE_TAC[PEG_wellformed];
    MP_TAC(ISPEC `h:token#locs` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `t0:token` (X_CHOOSE_THEN `l0:locs` SUBST_ALL_TAC)) THEN
    REWRITE_TAC[FST] THEN STRIP_TAC THEN MATCH_MP_TAC peg_respects_firstSets THEN
    ASM_REWRITE_TAC[]]);;

let eapp_complete = prove
 (`!master.
     (!pt' pfx' sfx' N.
        LENGTH pfx' < LENGTH master /\ valid_lptree cmlG pt' /\
        INL N IN FDOM (peg_rules cmlPEG) /\
        ptree_head pt' = NT (INL N) /\ real_fringe pt' = MAP (TOK ## I) pfx' /\
        (~(sfx' = []) ==> FST (HD sfx') IN stoppers N) ==>
        ?eo. peg_eval cmlPEG (APPEND pfx' sfx', peg_nt (INL N) I)
                      (peg_Success sfx' [pt'] eo)) /\
     (!pt' sfx'.
        valid_lptree cmlG pt' /\ ptree_head pt' = NT (INL nEbase) /\
        real_fringe pt' = MAP (TOK ## I) master /\
        (~(sfx' = []) ==> FST (HD sfx') IN stoppers nEbase) ==>
        ?eo. peg_eval cmlPEG (APPEND master sfx', peg_nt (INL nEbase) I)
                      (peg_Success sfx' [pt'] eo))
     ==> !pfx apt sfx.
           IS_SUFFIX master pfx /\ valid_lptree cmlG apt /\
           ptree_head apt = NT (INL nEapp) /\
           real_fringe apt = MAP (TOK ## I) pfx /\
           (~(sfx = []) ==> FST (HD sfx) IN stoppers nEapp) ==>
           ?eo. peg_eval cmlPEG (APPEND pfx sfx, peg_nt (INL nEapp) I)
                         (peg_Success sfx [apt] eo)`,
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ihE")) THEN
  SUBGOAL_THEN
   `!n (pfx:(token#locs)list) apt sfx.
      LENGTH pfx = n /\ IS_SUFFIX master pfx /\ valid_lptree cmlG apt /\
      ptree_head apt = NT (INL nEapp) /\ real_fringe apt = MAP (TOK ## I) pfx /\
      (~(sfx = []) ==> FST (HD sfx) IN stoppers nEapp) ==>
      ?eo. peg_eval cmlPEG (APPEND pfx sfx, peg_nt (INL nEapp) I)
                    (peg_Success sfx [apt] eo)`
   (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_THEN(LABEL_TAC "ihn") THEN
  MAP_EVERY X_GEN_TAC [`pfx:(token#locs)list`; `apt:mlptree`; `sfx:(token#locs)list`] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`apt:mlptree`; `nEapp`; `pfx:(token#locs)list`] ptree_head_NT_mkNd) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `subs:(mlptree)list` SUBST_ALL_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[valid_lptree_mkNd; real_fringe_mkNd]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  PARSE3AUX_GRULE_CASES_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MEM; DISJ_IMP_THM; FORALL_AND_THM; FORALL_UNWIND_THM2]) THEN
  PARSE3AUX_FRINGE_SPLIT_TAC THENL
   [(* Eapp -> Eapp Ebase: reassociate as Ebase followed by an Eapp *)
    FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)) THEN
    MP_TAC(SPECL [`h0:mlptree`; `h0':mlptree`; `m1:(token#locs)list`;
                  `m2:(token#locs)list`] eapp_reassociated) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `apt':mlptree` (X_CHOOSE_THEN `bpt':mlptree`
      STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM(MP_TAC o SYM o check (fun th -> is_eq(concl th) &&
       (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "APPEND"
        with Failure _ -> false))) THEN
    REWRITE_TAC[LPARSEAUX_MAP_EQ_APPEND] THEN
    DISCH_THEN(X_CHOOSE_THEN `bf:(token#locs)list` (X_CHOOSE_THEN `af:(token#locs)list`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN (ASSUME_TAC o SYM))))) THEN
    MP_TAC(MATCH_MP PARSE3AUX_FRINGE_CONS
       (CONJ (ASSUME `real_fringe (bpt':mlptree) = MAP (TOK ## I) bf`)
       (CONJ (ASSUME `ptree_head (bpt':mlptree) = NT (INL nEbase)`)
       (CONJ (ASSUME `valid_lptree cmlG (bpt':mlptree)`) nullable_Ebase)))) THEN
    DISCH_THEN(X_CHOOSE_THEN `bt:token` (X_CHOOSE_THEN `bl:locs`
      (X_CHOOSE_THEN `bf_r:(token#locs)list`
        (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)))) THEN
    MP_TAC(MATCH_MP PARSE3AUX_FRINGE_CONS
       (CONJ (ASSUME `real_fringe (apt':mlptree) = MAP (TOK ## I) af`)
       (CONJ (ASSUME `ptree_head (apt':mlptree) = NT (INL nEapp)`)
       (CONJ (ASSUME `valid_lptree cmlG (apt':mlptree)`) nullable_Eapp)))) THEN
    DISCH_THEN(X_CHOOSE_THEN `at:token` (X_CHOOSE_THEN `al:locs`
      (X_CHOOSE_THEN `af_r:(token#locs)list`
        (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)))) THEN
    ASM_REWRITE_TAC[GSYM APPEND_ASSOC] THEN REWRITE_TAC[APPEND_ASSOC] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN
    UNDISCH_TAC `IS_SUFFIX (master:(token#locs)list) (APPEND m1 m2)` THEN
    ASM_REWRITE_TAC[LPARSEAUX_IS_SUFFIX_APPEND] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:(token#locs)list` ASSUME_TAC) THEN
    (* the Ebase *)
    SUBGOAL_THEN `?eo. peg_eval cmlPEG
        (APPEND (CONS (bt,bl) bf_r) (APPEND (CONS (at,al) af_r) sfx), peg_nt (INL nEbase) I)
        (peg_Success (APPEND (CONS (at,al) af_r) sfx) [bpt'] eo)`
      (X_CHOOSE_TAC `eob:(locs#(char)list)option`) THENL
     [USE_THEN "ih1" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[stoppers_def; IN_UNIV; FDOM_cmlPEG_nts] THEN
      REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ARITH_TAC;
      ALL_TAC] THEN
    (* the shorter Eapp *)
    SUBGOAL_THEN `?eo. peg_eval cmlPEG (APPEND (CONS (at,al) af_r) sfx, peg_nt (INL nEapp) I)
                         (peg_Success sfx [apt'] eo)`
      (X_CHOOSE_TAC `eoa:(locs#(char)list)option`) THENL
     [USE_THEN "ihn" (MP_TAC o SPEC `LENGTH (CONS (at:token,al:locs) af_r)`) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ARITH_TAC;
        ALL_TAC] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[LPARSEAUX_IS_SUFFIX_APPEND] THEN
      EXISTS_TAC `APPEND p (CONS (bt:token,bl:locs) bf_r)` THEN
      REWRITE_TAC[APPEND_ASSOC];
      ALL_TAC] THEN
    MP_TAC(MATCH_MP PARSE3AUX_Eapp_inv (ASSUME
       `peg_eval cmlPEG (APPEND (CONS (at,al) af_r) sfx, peg_nt (INL nEapp) I)
                         (peg_Success sfx [apt'] eoa)`)) THEN
    REWRITE_TAC[NOT_CONS_NIL; CONS_11] THEN
    DISCH_THEN(X_CHOOSE_THEN `i1:(token#locs)list` (X_CHOOSE_THEN `h:(mlptree)list`
      (X_CHOOSE_THEN `eo1:(locs#(char)list)option` (X_CHOOSE_THEN `l:((mlptree)list)list`
        (X_CHOOSE_THEN `err:locs#(char)list` STRIP_ASSUME_TAC))))) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
      try lhs(concl th) = `apt':mlptree` with Failure _ -> false)) THEN
    MP_TAC(ISPECL [`APPEND (CONS (bt,bl) bf_r) (APPEND (CONS (at,al) af_r) sfx):(token#locs)list`;
                   `APPEND (CONS (at,al) af_r) sfx:(token#locs)list`;
                   `sfx:(token#locs)list`; `[bpt']:(mlptree)list`;
                   `eob:(locs#(char)list)option`;
                   `CONS (h:(mlptree)list) l`; `err:locs#(char)list`; `bpt':mlptree`;
                   `CONS (x:mlptree) t`] PARSE3AUX_Eapp_intro) THEN
    ASM_REWRITE_TAC[FLAT; APPEND] THEN ANTS_TAC THENL
     [MATCH_MP_TAC peg_eval_list_cons THEN
      MAP_EVERY EXISTS_TAC [`eo1:(locs#(char)list)option`; `i1:(token#locs)list`] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[APPEND]) THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[left_insert1_FOLDL; left_insert1_mkNd; FOLDL]];
    (* Eapp -> Ebase *)
    SUBGOAL_THEN `?eo. peg_eval cmlPEG (APPEND pfx sfx, peg_nt (INL nEbase) I)
                                (peg_Success sfx [h0] eo)` STRIP_ASSUME_TAC THENL
     [MP_TAC(ISPECL [`master:(token#locs)list`; `pfx:(token#locs)list`]
                    LPARSEAUX_IS_SUFFIX_APPEND) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `p:(token#locs)list` SUBST_ALL_TAC) THEN
      ASM_CASES_TAC `p:(token#locs)list = []` THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN
        USE_THEN "ihE" (MP_TAC o SPECL [`h0:mlptree`; `sfx:(token#locs)list`]) THEN
        REWRITE_TAC[APPEND] THEN REWRITE_TAC[stoppers_def; IN_UNIV] THEN
        ASM_REWRITE_TAC[];
        USE_THEN "ih1" (MP_TAC o SPECL [`h0:mlptree`; `pfx:(token#locs)list`;
                                        `sfx:(token#locs)list`; `nEbase`]) THEN
        REWRITE_TAC[stoppers_def; IN_UNIV; FDOM_cmlPEG_nts; LENGTH_APPEND] THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
        UNDISCH_TAC `~(p:(token#locs)list = [])` THEN
        REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `?fl fe. peg_eval cmlPEG (sfx, peg_nt (INL nEbase) I) (Failure fl fe)`
      STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC PARSE3AUX_nt_fail THEN REWRITE_TAC[NTS_in_PEG_exprs; peg0_nEbase] THEN
      UNDISCH_TAC `~(sfx:(token#locs)list = []) ==> FST (HD sfx) IN stoppers nEapp` THEN
      REWRITE_TAC[stoppers_def; IN_DIFF; IN_UNIV];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`APPEND pfx sfx:(token#locs)list`; `sfx:(token#locs)list`;
                   `sfx:(token#locs)list`; `[h0]:(mlptree)list`;
                   `eo:(locs#(char)list)option`; `[]:((mlptree)list)list`;
                   `(fl:locs,fe:(char)list)`; `h0:mlptree`; `[]:(mlptree)list`]
                  PARSE3AUX_Eapp_intro) THEN
    REWRITE_TAC[FLAT; APPEND; FOLDL] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC peg_eval_list_nil THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[]]]);;

let peg_respects_firstSets' = prove
 (`!N t (l:locs) rest sfx res eo.
     peg_eval cmlPEG (CONS (t,l) rest, peg_nt N I) (peg_Success sfx res eo) /\
     peg_nt N I IN Gexprs cmlPEG /\ ~peg0 cmlPEG (peg_nt N I) ==>
     t IN firstSet cmlG [NT N]`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(SPECL [`N:MMLnonT+num`; `rest:(token#locs)list`; `t:token`; `l:locs`]
               peg_respects_firstSets) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `fl:locs` (X_CHOOSE_THEN `fe:(char)list` (fun th ->
    FIRST_X_ASSUM(fun h -> if PARSE3AUX_is_evalfact (concl h) then
      CONTR_TAC (REWRITE_RULE[pegresult_distinct] (PARSE3AUX_DET_RULE th h))
      else failwith "")))));;

let nUQConstructorName_input_monotone = prove
 (`!i0 i r eo sfx.
     peg_eval cmlPEG (i0, peg_nt (INL nUQConstructorName) I) (peg_Success i r eo) ==>
     peg_eval cmlPEG (APPEND i0 sfx, peg_nt (INL nUQConstructorName) I)
              (peg_Success (APPEND i sfx) r eo)`,
  PARSE3AUX_TOKMONO_TAC [`nUQConstructorName`]);;

let nConstructorName_input_monotone = prove
 (`!i0 i r eo sfx.
     peg_eval cmlPEG (i0, peg_nt (INL nConstructorName) I) (peg_Success i r eo) ==>
     peg_eval cmlPEG (APPEND i0 sfx, peg_nt (INL nConstructorName) I)
              (peg_Success (APPEND i sfx) r eo)`,
  PARSE3AUX_TOKMONO_TAC [`nConstructorName`; `nUQConstructorName`]);;

let peg_eval_NT_NONE = prove
 (`!i0 n fl fe.
     peg_eval cmlPEG (i0, peg_nt (INL n) I) (Failure fl fe) <=>
     INL n IN FDOM (peg_rules cmlPEG) /\
     peg_eval cmlPEG (i0, FAPPLY (peg_rules cmlPEG) (INL n)) (Failure fl fe)`,
  REWRITE_TAC[peg_eval_NT] THEN
  ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN REWRITE_TAC[resultmap_EQ_Failure] THEN
  MESON_TAC[]);;

let PARSE3AUX_LIST_LEN_LE = prove
 (`!(G:(A,B,C,E)peg) s0 e s rl err.
     peg_eval_list G (s0,e) (s,rl,err) ==> LENGTH s <= LENGTH s0`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP peg_eval_list_suffix') THEN
  ASM_SIMP_TAC[LE_REFL; LT_IMP_LE]);;

(* the length fact of an evaluation (or list evaluation) fact *)
let PARSE3AUX_len_fact th =
  let c = concl th in
  if PARSE3AUX_is_evalfact c then
    let x,e,res = PARSE3AUX_eval_parts c in
    if not (PARSE3AUX_is_succ th) then failwith "len_fact" else
    (try MATCH_MP (MATCH_MP not_peg0_LENGTH_decreases
                     (REWRITE_RULE[cmlPEG_pnt_def]
                        (find (fun t -> rand(rand(concl t)) = e) PARSE3AUX_npeg0_ths))) th
     with Failure _ -> MATCH_MP length_no_greater th)
  else if PARSE3AUX_is_listfact c then MATCH_MP PARSE3AUX_LIST_LEN_LE th
  else failwith "len_fact";;

(* unfold an evaluation fact of peg_nt (INL Y) I into the evaluation of the *)
(* primitive form of the rule of Y, and invert the compound expressions    *)
let PARSE3AUX_INV_CONV : conv =
  REWRITE_CONV (PARSE3AUX_INV_RWTS @
                [pegresult_inject; pegresult_distinct; I_THM; sumID_def; o_THM]);;

let PARSE3AUX_NT_INV_RULE th =
  let x,e,res = PARSE3AUX_eval_parts (concl th) in
  let y = rand(rand(rator e)) in
  let th1 = REWRITE_RULE[peg_eval_NT_SOME; peg_eval_NT_NONE; I_THM;
                         FDOM_cmlPEG_nts] th in
  let th2 = CONV_RULE (ONCE_DEPTH_CONV (REWR_CONV (PARSE2AUX_rule y)) THENC
                       PARSE3AUX_PRIM_CONV) th1 in
  CONV_RULE PARSE3AUX_INV_CONV th2;;

(* facts about tokens (to be normalized by PARSE3AUX_DECIDE_CONV) *)
let PARSE3AUX_is_tokfact c =
  not (is_forall c) && not (PARSE3AUX_is_evalfact c) &&
  not (PARSE3AUX_is_listfact c) &&
  not (can (find_term (fun t -> is_const t && fst(dest_const t) = "stoppers")) c) &&
  not (is_binary "<" c) && not (is_binary "<=" c) &&
  not (is_eq c && (is_var(lhs c) || is_var(rhs c))) &&
  can (find_term (fun t -> type_of t = PARSE3AUX_token_ty)) c;;

(* evaluations of the same expression on the same input have equal results *)
let PARSE3AUX_DET_UNIFY_TAC : tactic = fun (asl,w as g) ->
  let evs = filter (fun th -> PARSE3AUX_is_evalfact (concl th)) (map snd asl) in
  let rec pairs l = match l with [] -> [] | h::t -> map (fun x -> (h,x)) t @ pairs t in
  let a,b = find (fun (a,b) ->
      rand(rator(concl a)) = rand(rator(concl b)) && rand(concl a) <> rand(concl b))
      (pairs evs) in
  let eq = REWRITE_RULE[pegresult_inject; pegresult_distinct; PAIR_EQ; CONS_11;
                        NOT_CONS_NIL; GSYM NOT_CONS_NIL] (PARSE3AUX_DET_RULE a b) in
  (UNDISCH_THEN (concl b) (K ALL_TAC) THEN STRIP_ASSUME_TAC eq THEN RVEQ_TAC) g;;

(* a successful evaluation of peg_nt N on an input whose first token cannot   *)
(* start N                                                                   *)
let PARSE3AUX_FIRSTSET_CONTR_TAC : tactic = fun (asl,w as g) ->
  let try_th th =
    let c = concl th in
    if not (PARSE3AUX_is_evalfact c) || not (PARSE3AUX_is_succ th) then failwith "" else
    let x,e,_ = PARSE3AUX_eval_parts c in
    let n = rand(rator e) in
    let h,t = dest_cons x in
    let tk,l = dest_pair h in
    let mem = mk_comb(mk_comb(PARSE3AUX_IN_TOKEN_TM, tk),
                mk_comb(PARSE3AUX_FIRSTSET_TM, mk_list([mk_comb(PARSE3AUX_NT_TM, n)],
                                                 PARSE3AUX_symbol_ty))) in
    let b,mth = PARSE3AUX_decide_asm asl mem in
    if b then failwith "" else
    let i',r',eo' = PARSE3AUX_succ_parts th in
    let th1 = ISPECL [n; tk; l; t; i'; r'; eo'] peg_respects_firstSets' in
    let th2 = MP th1 (CONJ th (CONJ (PARSE3AUX_NTS_GEXPRS e)
                 (REWRITE_RULE[cmlPEG_pnt_def] (find (fun t -> rand(rand(concl t)) = e)
                                              PARSE3AUX_npeg0_ths)))) in
    CONTR_TAC (MP (NOT_ELIM mth) th2) g in
  tryfind try_th (map snd asl);;

let PARSE3AUX_CLEAN1_TAC : tactic =
  RVEQ_TAC THEN TRY PARSE3AUX_MEM_CONTR_TAC THEN TRY PARSE3AUX_FIRSTSET_CONTR_TAC THEN
  RULE_ASSUM_TAC(fun th -> if is_eq(concl th) && not (is_var(lhs(concl th))) &&
                              not (is_var(rhs(concl th)))
                           then REWRITE_RULE[CONS_11; PAIR_EQ; NOT_CONS_NIL;
                                             GSYM NOT_CONS_NIL] th else th) THEN
  RULE_ASSUM_TAC(fun th -> if PARSE3AUX_is_tokfact (concl th)
                           then CONV_RULE PARSE3AUX_DECIDE_CONV th else th) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th ->
           let c = concl th in is_conj c || is_exists c || is_disj c || c = `F`))) THEN
  RVEQ_TAC THEN
  REPEAT PARSE3AUX_DET_UNIFY_TAC;;

let PARSE3AUX_CLEAN_TAC : tactic =
  PARSE3AUX_CLEAN1_TAC THEN TRY PARSE3AUX_CLEAN1_TAC THEN TRY PARSE3AUX_CLEAN1_TAC;;

(* add the length facts of all evaluation facts *)
let PARSE3AUX_CLEN_FACTS_TAC : tactic = fun (asl,w as g) ->
  let ths = mapfilter (fun (_,th) -> PARSE3AUX_len_fact th) asl in
  let cs = map (concl o snd) asl in
  MAP_EVERY ASSUME_TAC (filter (fun th -> not (mem (concl th) cs)) ths) g;;

(* rename the bound variables of a theorem apart from each other and from  *)
(* the variables of avoid (STRIP_TAC cannot strip shadowed names)          *)
let PARSE3AUX_RENAME_BV_RULE (avoid:term list) th =
  let av = ref (avoid @ frees (concl th)) in
  let rec ren tm =
    match tm with
      Abs(v,b) ->
        let v' = variant !av v in
        av := v' :: !av;
        mk_abs(v', ren (vsubst [v',v] b))
    | Comb(f,a) -> mk_comb(ren f, ren a)
    | _ -> tm in
  let tm' = ren (concl th) in
  EQ_MP (ALPHA (concl th) tm') th;;

(* unfold a successful evaluation of peg_nt B on x when an evaluation of peg_nt A  *)
(* on x is known and the rule of B mentions A (for determinism conflicts)  *)
(* STRIP_ASSUME_TAC that closes a branch at once when a new fact x = [] or   *)
(* x = CONS .. contradicts an assumption about the shape of x: the inverted  *)
(* rule of a choice of token tests is a product of such cases, nearly all    *)
(* contradictory (they were made, then closed by PARSE3AUX_CLEAN_TAC)        *)
let PARSE3AUX_PRUNE_STRIP_ASSUME_TAC : thm_tactic =
  let is_nil t = is_const t && fst(dest_const t) = "NIL" in
  let shape t = if is_nil t then Some true else if is_cons t then Some false else None in
  let DISCARD_TAC th =
    let tm = concl th in
    fun (asl,w as g) ->
      if exists (fun a -> aconv tm (concl(snd a))) asl then ALL_TAC g
      else failwith "DISCARD_TAC: not already present" in
  let PRUNE_TAC th : tactic = fun (asl,w as g) ->
    let c = concl th in
    if not (is_eq c) || not (is_var (lhs c)) then failwith "PRUNE_TAC" else
    match shape (rhs c) with
      None -> failwith "PRUNE_TAC"
    | Some b ->
        let _,a = find (fun (_,a) -> let ca = concl a in
                          is_eq ca && lhs ca = lhs c && shape (rhs ca) = Some (not b)) asl in
        CONTR_TAC (REWRITE_RULE[NOT_CONS_NIL; NOT_NIL_CONS] (TRANS (SYM a) th)) g in
  REPEAT_TCL STRIP_THM_THEN
   (fun gth -> FIRST [CONTR_TAC gth; ACCEPT_TAC gth; DISCARD_TAC gth; PRUNE_TAC gth;
                      ASSUME_TAC gth]);;

let PARSE3AUX_PRUNE_STRIP_TAC = STRIP_GOAL_THEN PARSE3AUX_PRUNE_STRIP_ASSUME_TAC;;

let PARSE3AUX_UNFOLD_CONFLICT_TAC : tactic = fun (asl,w as g) ->
  let evs = filter (fun th -> PARSE3AUX_is_evalfact (concl th) &&
                     (let _,e,_ = PARSE3AUX_eval_parts (concl th) in
                      try fst(dest_const(fst(strip_comb e))) = "peg_nt" with Failure _ -> false))
                   (map snd asl) in
  let nt_of th = let _,e,_ = PARSE3AUX_eval_parts (concl th) in rand(rand(rator e)) in
  let inp_of th = let x,_,_ = PARSE3AUX_eval_parts (concl th) in x in
  let cands = filter (fun b ->
      PARSE3AUX_is_succ b &&
      exists (fun a -> inp_of a = inp_of b && nt_of a <> nt_of b &&
                       free_in (nt_of a) (rhs(concl(PARSE2AUX_rule (nt_of b))))) evs)
                 evs in
  if cands = [] then failwith "PARSE3AUX_UNFOLD_CONFLICT_TAC" else
  let avoid = itlist (fun (_,th) l -> union (thm_frees th) l) asl (frees w) in
  (MAP_EVERY (fun b -> MP_TAC (PARSE3AUX_RENAME_BV_RULE avoid (PARSE3AUX_NT_INV_RULE b)))
             cands THEN
   REPEAT PARSE3AUX_PRUNE_STRIP_TAC THEN PARSE3AUX_CLEAN_TAC) g;;

(* forward lemmas: !x y r eo. peg_eval cmlPEG (x, peg_nt (INL A) I)           *)
(* (peg_Success y r eo) /\ side ==> ?r1 eo1. peg_eval cmlPEG (x, peg_nt B I) ...   *)
let PARSE3AUX_fwd_lemmas = ref ([]:thm list);;

let PARSE3AUX_FWD_TAC : tactic = fun (asl,w as g) ->
  let evs = filter (fun th -> PARSE3AUX_is_evalfact (concl th) &&
                              PARSE3AUX_is_succ th) (map snd asl) in
  let one lemma f =
    let x,_,_ = PARSE3AUX_eval_parts (concl f) in
    let y,r,eo = PARSE3AUX_succ_parts f in
    let th1 = ISPECL [x; y; r; eo] lemma in
    let cnd = rand(lhand(concl th1)) in
    let cth = TAC_PROOF((asl, cnd), PARSE3AUX_STOPPERS_TAC) in
    MP th1 (CONJ f cth) in
  let ths = flat (map (fun l -> mapfilter (one l) evs) !PARSE3AUX_fwd_lemmas) in
  let new_ths = filter (fun th -> let vs,bod = strip_exists(concl th) in
                          not (exists (fun f -> can (term_match [] bod) (concl f)) evs)) ths in
  if new_ths = [] then failwith "PARSE3AUX_FWD_TAC" else
  let avoid = itlist (fun (_,th) l -> union (thm_frees th) l) asl (frees w) in
  (MAP_EVERY (fun th -> MP_TAC (PARSE3AUX_RENAME_BV_RULE avoid th)) new_ths THEN
   REPEAT PARSE3AUX_PRUNE_STRIP_TAC THEN PARSE3AUX_CLEAN_TAC) g;;

(* invert the evaluation fact labelled lab *)
let PARSE3AUX_INV_TAC (lab:string) : tactic = fun (asl,w as g) ->
  let avoid = itlist (fun (_,th) l -> union (thm_frees th) l) asl (frees w) in
  (REMOVE_THEN lab (MP_TAC o PARSE3AUX_RENAME_BV_RULE avoid o PARSE3AUX_NT_INV_RULE) THEN
   PARSE3AUX_PRUNE_STRIP_TAC THEN PARSE3AUX_CLEAN_TAC THEN TRY PARSE3AUX_UNFOLD_CONFLICT_TAC THEN
   TRY PARSE3AUX_FWD_TAC) g;;

(* induction on the input length, then on the rank of the non-terminal *)
let PARSE3AUX_LEX_IND = prove
 (`!P:MMLnonT->(token#locs)list->bool.
     (!N i0. (!N' i0'. LENGTH i0' < LENGTH i0 \/
                       i0' = i0 /\ NT_rank (INL N') < NT_rank (INL N)
                       ==> P N' i0') ==> P N i0)
     ==> !N i0. P N i0`,
  GEN_TAC THEN DISCH_THEN(LABEL_TAC "main") THEN
  SUBGOAL_THEN `!n k N (i0:(token#locs)list).
                  LENGTH i0 = n /\ NT_rank (INL N) = k ==> P N i0`
    (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_THEN(LABEL_TAC "ihn") THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `k:num` THEN DISCH_THEN(LABEL_TAC "ihk") THEN
  MAP_EVERY X_GEN_TAC [`N:MMLnonT`; `i0:(token#locs)list`] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  USE_THEN "main" MATCH_MP_TAC THEN
  MAP_EVERY X_GEN_TAC [`N':MMLnonT`; `i0':(token#locs)list`] THEN
  DISCH_THEN(DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
   [USE_THEN "ihn" (MP_TAC o SPECL [`NT_rank (INL N')`; `N':MMLnonT`;
                                     `i0':(token#locs)list`] o
                    C MP (ASSUME `LENGTH (i0':(token#locs)list) < LENGTH (i0:(token#locs)list)`) o
                    SPEC `LENGTH (i0':(token#locs)list)`) THEN
    REWRITE_TAC[];
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    USE_THEN "ihk" (MP_TAC o SPECL [`N':MMLnonT`; `i0:(token#locs)list`] o
                    C MP (ASSUME `NT_rank (INL N') < NT_rank (INL N)`) o
                    SPEC `NT_rank (INL N')`) THEN
    REWRITE_TAC[]]);;

(* split the rest i of the hypothesis and the suffix sfx of the goal, and  *)
(* simplify the stopper conditions                                          *)
let PARSE3AUX_RSPLIT_TAC : tactic = fun (asl,w as g) ->
  let _,_,res = PARSE3AUX_eval_parts w in
  let rest = rand(rator(rator res)) in
  let i,sfx = dest_binary "APPEND" rest in
  let simp = RULE_ASSUM_TAC(fun th ->
               if is_imp(concl th) &&
                  can (find_term (fun t -> is_const t &&
                                           fst(dest_const t) = "stoppers")) (concl th)
                  && not (is_forall(concl th))
               then REWRITE_RULE[NOT_CONS_NIL; HD; FST] th else th) in
  let pcases v t l r =
    MP_TAC(ISPEC v list_CASES) THEN
    DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC
      (X_CHOOSE_THEN `PARSE3AUX_h:token#locs` (X_CHOOSE_THEN r SUBST_ALL_TAC))) THENL
     [simp;
      MP_TAC(ISPEC `PARSE3AUX_h:token#locs` PAIR_SURJECTIVE) THEN
      DISCH_THEN(X_CHOOSE_THEN t (X_CHOOSE_THEN l SUBST_ALL_TAC)) THEN simp] in
  (pcases i `itk:token` `il:locs` `it:(token#locs)list` THENL
    [pcases sfx `stk:token` `sl:locs` `st:(token#locs)list`; ALL_TAC]) g;;

(* the replay of the evaluation on the extended input *)
let PARSE3AUX_MONO_REPLAY_TAC : tactic = fun (asl,w as g) ->
  let inp,e,res = PARSE3AUX_eval_parts w in
  let _,sfx = dest_binary "APPEND" inp in
  let n = rand(rator e) in
  let inp' = PARSE3AUX_norm inp in
  let th = PARSE3AUX_with_mono sfx (PARSE3AUX_eval_nt_unfold asl [] inp') n in
  (CONV_TAC(LAND_CONV(LAND_CONV PARSE3AUX_NORM_CONV)) THEN
   MP_TAC th THEN
   REWRITE_TAC (PARSE3AUX_RESULT_RWTS @ [APPEND_NIL; GSYM APPEND_ASSOC]) THEN
   DISCH_THEN ACCEPT_TAC) g;;

let PARSE3AUX_REPORT_TAC (tac:tactic) : tactic = fun (asl,w as g) ->
  try tac g with Failure s ->
    print_string ("LEAF FAIL: " ^ s ^ "\nGOAL: " ^ string_of_term w ^ "\n");
    List.iter (fun (l,th) -> if not (is_forall(concl th)) then
      print_string ("  ASM " ^ l ^ ": " ^ string_of_term (concl th) ^ "\n")) asl;
    failwith s;;

let PARSE3AUX_MONO_LEAF_TAC : tactic =
  PARSE3AUX_CLEN_FACTS_TAC THEN
  (PARSE3AUX_LEN_CONTR_TAC ORELSE
   PARSE3AUX_SPLIT_RETRY_TAC 4 PARSE3AUX_MONO_REPLAY_TAC);;

let PARSE3AUX_MONO_CASE_TAC : tactic =
  PARSE3AUX_RSPLIT_TAC THEN PARSE3AUX_INV_TAC "H" THEN
  PARSE3AUX_REPORT_TAC PARSE3AUX_MONO_LEAF_TAC;;

(* the goal ?r eo. peg_eval cmlPEG (inp, e) (peg_Success rest r eo): evaluate *)
(* e on inp, unfolding the rules of nts                                        *)
let PARSE3AUX_EVAL_EXISTS_TAC (nts:term list) : tactic = fun (asl,w as g) ->
  let vs,bod = strip_exists w in
  let inp,e,res = PARSE3AUX_eval_parts bod in
  let inp' = PARSE3AUX_norm inp in
  let th = PARSE3AUX_with_unfold nts (PARSE3AUX_eval asl inp') e in
  let _,r1,eo1 = PARSE3AUX_succ_parts th in
  (MAP_EVERY EXISTS_TAC [r1; eo1] THEN
   CONV_TAC(LAND_CONV(LAND_CONV PARSE3AUX_NORM_CONV)) THEN
   ACCEPT_TAC th) g;;

let PARSE3AUX_JSPLIT_TAC (j:term) : tactic =
  MP_TAC(ISPEC j list_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC
    (X_CHOOSE_THEN `PARSE3AUX_h:token#locs` (X_CHOOSE_THEN `jt:(token#locs)list`
      SUBST_ALL_TAC))) THENL
   [ALL_TAC;
    MP_TAC(ISPEC `PARSE3AUX_h:token#locs` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `jtk:token` (X_CHOOSE_THEN `jl:locs` SUBST_ALL_TAC))] THEN
  RULE_ASSUM_TAC(fun th ->
    if is_imp(concl th) && not (is_forall(concl th))
    then REWRITE_RULE[NOT_CONS_NIL; HD; FST] th else th);;

(* decide the goal, a test on token variables, from their membership facts *)
let PARSE3AUX_DECIDE_GOAL_TAC : tactic = fun (asl,w as g) ->
  let b,th = PARSE3AUX_decide_ctx asl w in
  if b then ACCEPT_TAC th g else failwith "PARSE3AUX_DECIDE_GOAL_TAC";;

(* ~(sfx = []) ==> ~(FST (HD sfx) IN firstSet cmlG [NT (INL nPbase)]) from *)
(* the stopper condition of sfx                                             *)
let PARSE3AUX_HD_NOTIN_TAC (sfx:term) : tactic =
  PARSE3AUX_JSPLIT_TAC sfx THEN REWRITE_TAC[NOT_CONS_NIL; HD; FST] THEN
  PARSE3AUX_DECIDE_GOAL_TAC;;

let nConstructorName_NONE_input_monotone = prove
 (`!tk l i sfx fl fe.
     peg_eval cmlPEG (CONS (tk,l) i, peg_nt (INL nConstructorName) I) (Failure fl fe) ==>
     peg_eval cmlPEG (CONS (tk,l) (APPEND i sfx), peg_nt (INL nConstructorName) I)
              (Failure fl fe)`,
  PARSE3AUX_TOKMONO_NONE_TAC [`nConstructorName`; `nUQConstructorName`]);;

let nV_input_monotone = prove
 (`!i0 i r eo sfx.
     peg_eval cmlPEG (i0, peg_nt (INL nV) I) (peg_Success i r eo) ==>
     peg_eval cmlPEG (APPEND i0 sfx, peg_nt (INL nV) I) (peg_Success (APPEND i sfx) r eo)`,
  PARSE3AUX_TOKMONO_TAC [`nV`]);;

let nV_NONE_input_monotone = prove
 (`!tk l i0 sfx fl fe.
     peg_eval cmlPEG (CONS (tk,l) i0, peg_nt (INL nV) I) (Failure fl fe) ==>
     peg_eval cmlPEG (CONS (tk,l) (APPEND i0 sfx), peg_nt (INL nV) I) (Failure fl fe)`,
  PARSE3AUX_TOKMONO_NONE_TAC [`nV`]);;

let nOpID_input_monotone = prove
 (`!i0 i r eo sfx.
     peg_eval cmlPEG (i0, peg_nt (INL nOpID) I) (peg_Success i r eo) ==>
     peg_eval cmlPEG (APPEND i0 sfx, peg_nt (INL nOpID) I)
              (peg_Success (APPEND i sfx) r eo)`,
  PARSE3AUX_TOKMONO_TAC [`nOpID`]);;

let nUQTyOp_input_monotone = prove
 (`!i0 i r eo sfx.
     peg_eval cmlPEG (i0, peg_nt (INL nUQTyOp) I) (peg_Success i r eo) ==>
     peg_eval cmlPEG (APPEND i0 sfx, peg_nt (INL nUQTyOp) I)
              (peg_Success (APPEND i sfx) r eo)`,
  PARSE3AUX_TOKMONO_TAC [`nUQTyOp`]);;

let nUQTyOp_input_monotone' =
  GEN_ALL(DISCH_ALL(MATCH_MP (CONJUNCT1 (ISPEC `cmlPEG` peg_deterministic))
                     (UNDISCH(SPEC_ALL nUQTyOp_input_monotone))));;

let nTyOp_input_monotone = prove
 (`!i0 i r eo sfx.
     peg_eval cmlPEG (i0, peg_nt (INL nTyOp) I) (peg_Success i r eo) ==>
     peg_eval cmlPEG (APPEND i0 sfx, peg_nt (INL nTyOp) I)
              (peg_Success (APPEND i sfx) r eo)`,
  PARSE3AUX_TOKMONO_TAC [`nTyOp`; `nUQTyOp`]);;

let nTyOp_input_monotone' =
  GEN_ALL(DISCH_ALL(MATCH_MP (CONJUNCT1 (ISPEC `cmlPEG` peg_deterministic))
                     (UNDISCH(SPEC_ALL nTyOp_input_monotone))));;

let PARSE3AUX_nTyOp_NONE_input_monotone = prove
 (`!tk l i sfx fl fe.
     peg_eval cmlPEG (CONS (tk,l) i, peg_nt (INL nTyOp) I) (Failure fl fe) ==>
     peg_eval cmlPEG (CONS (tk,l) (APPEND i sfx), peg_nt (INL nTyOp) I) (Failure fl fe)`,
  PARSE3AUX_TOKMONO_NONE_TAC [`nTyOp`; `nUQTyOp`]);;

let nTyOplist_input_monotone = prove
 (`!pts res i0 i sfx.
     peg_eval_list cmlPEG (i0, peg_nt (INL nTyOp) I) (i, pts, res) /\
     (i = [] /\ ~(sfx = []) ==> FST (HD sfx) IN stoppers nDType) ==>
     ?res'. peg_eval_list cmlPEG (APPEND i0 sfx, peg_nt (INL nTyOp) I)
                          (APPEND i sfx, pts, res')`,
  LIST_INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [peg_eval_list] THEN
    REWRITE_TAC[NOT_CONS_NIL] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
      concl th = `i:(token#locs)list = i0`)) THEN
    SUBGOAL_THEN `?fl' fe'. peg_eval cmlPEG (APPEND i0 sfx, peg_nt (INL nTyOp) I)
                                     (Failure fl' fe')`
      STRIP_ASSUME_TAC THENL
     [MP_TAC(ISPEC `i0:(token#locs)list` list_CASES) THEN
      DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC
        (X_CHOOSE_THEN `h:token#locs` (X_CHOOSE_THEN `t:(token#locs)list`
          SUBST_ALL_TAC))) THENL
       [REWRITE_TAC[APPEND] THEN MATCH_MP_TAC PARSE3AUX_nt_fail THEN
        REWRITE_TAC[NTS_in_PEG_exprs; peg0_nTyOp] THEN
        FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
        REWRITE_TAC[stoppers_def; IN_DIFF; IN_UNIV];
        MP_TAC(ISPEC `h:token#locs` PAIR_SURJECTIVE) THEN
        DISCH_THEN(X_CHOOSE_THEN `tk:token` (X_CHOOSE_THEN `l:locs` SUBST_ALL_TAC)) THEN
        REWRITE_TAC[APPEND] THEN
        MAP_EVERY EXISTS_TAC [`fl:locs`; `fe:(char)list`] THEN
        MATCH_MP_TAC PARSE3AUX_nTyOp_NONE_input_monotone THEN ASM_REWRITE_TAC[]];
      EXISTS_TAC `(fl',fe'):locs#(char)list` THEN
      MATCH_MP_TAC peg_eval_list_nil THEN ASM_REWRITE_TAC[]];
    REPEAT GEN_TAC THEN GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [peg_eval_list] THEN
    REWRITE_TAC[NOT_CONS_NIL; CONS_11] THEN STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
      is_eq(concl th) && is_var(lhs(concl th)) && is_var(rhs(concl th))))) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`res:locs#(char)list`; `i1:(token#locs)list`;
                                  `i:(token#locs)list`; `sfx:(token#locs)list`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_TAC `res':locs#(char)list`) THEN
    EXISTS_TAC `res':locs#(char)list` THEN
    MATCH_MP_TAC peg_eval_list_cons THEN
    MAP_EVERY EXISTS_TAC [`eo0:(locs#(char)list)option`; `APPEND i1 sfx:(token#locs)list`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC nTyOp_input_monotone THEN
    ASM_REWRITE_TAC[]]);;

(* HOL4: [local,simp] *)
let peg_eval_TyOp_LparT = prove
 (`!loc i0 i r eo.
     peg_eval cmlPEG (CONS (LparT,loc) i0, peg_nt (INL nTyOp) I)
              (peg_Success i r eo) <=> F`,
  REPEAT GEN_TAC THEN REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`INL nTyOp:MMLnonT+num`; `LparT`; `loc:locs`; `i0:(token#locs)list`;
                `i:(token#locs)list`; `r:(mlptree)list`; `eo:(locs#(char)list)option`]
               peg_respects_firstSets') THEN
  ASM_REWRITE_TAC[NTS_in_PEG_exprs; peg0_nTyOp] THEN
  CONV_TAC PARSE3AUX_DECIDE_CONV);;

let _ = cake_add_simps [peg_eval_TyOp_LparT];;

PARSE3AUX_mono_lemmas :=
  [`nUQConstructorName`, nUQConstructorName_input_monotone;
   `nConstructorName`, nConstructorName_input_monotone;
   `nV`, nV_input_monotone; `nOpID`, nOpID_input_monotone;
   `nUQTyOp`, nUQTyOp_input_monotone; `nTyOp`, nTyOp_input_monotone];;

PARSE3AUX_mono_none_lemmas :=
  [`nConstructorName`, nConstructorName_NONE_input_monotone;
   `nV`, nV_NONE_input_monotone; `nTyOp`, PARSE3AUX_nTyOp_NONE_input_monotone];;

PARSE3AUX_mono_list_lemmas := [`nTyOp`, nTyOplist_input_monotone];;

let PARSE3AUX_MONO_START_TAC : tactic =
  MATCH_MP_TAC PARSE3AUX_LEX_IND THEN
  MAP_EVERY X_GEN_TAC [`N:MMLnonT`; `i0:(token#locs)list`] THEN
  DISCH_THEN(LABEL_TAC "mih" o REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP]) THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "H")))) THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC);;

let pegComplete_Type_input_monotone = prove
 (`!N i0 i r sfx eo.
     N IN {nTypeList2, nTypeList1, nType, nPType, nDType, nTbase} /\
     (~(i = []) ==> FST (HD i) IN stoppers N) /\
     (i = [] /\ ~(sfx = []) ==> FST (HD sfx) IN stoppers N) /\
     peg_eval cmlPEG (i0, peg_nt (INL N) I) (peg_Success i r eo) ==>
     peg_eval cmlPEG (APPEND i0 sfx, peg_nt (INL N) I)
              (peg_Success (APPEND i sfx) r eo)`,
  PARSE3AUX_MONO_START_TAC THEN PARSE3AUX_MONO_CASE_TAC);;

(* HOL4: [local] *)
let Pattern_nV_nCons = prove
 (`!i j r eo.
     peg_eval cmlPEG (i, peg_nt (INL nV) I) (peg_Success j r eo) /\
     (~(j = []) ==> FST (HD j) IN stoppers nPcons) ==>
     ?r1 eo1. peg_eval cmlPEG (i, peg_nt (INL nPcons) I) (peg_Success j r1 eo1)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "H") ASSUME_TAC) THEN
  PARSE3AUX_JSPLIT_TAC `j:(token#locs)list` THEN
  PARSE3AUX_INV_TAC "H" THEN
  PARSE3AUX_SPLIT_RETRY_TAC 6
    (PARSE3AUX_EVAL_EXISTS_TAC [`nPcons`; `nPapp`; `nPbase`; `nV`;
                                `nConstructorName`; `nUQConstructorName`]));;

PARSE3AUX_mono_cond_lemmas := [`nType`, pegComplete_Type_input_monotone];;

PARSE3AUX_fwd_lemmas := [Pattern_nV_nCons];;

let PARSE3AUX_PAT_IH_TAC : tactic = DISCH_THEN(fun ih ->
  let n',i0' = `N':MMLnonT`, `i0':(token#locs)list` in
  let ih0 = SPECL [n'; i0'] ih in
  let a = lhand(concl ih0) in
  let mih = REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP]
              (GEN n' (GEN i0' (DISCH a (CONJUNCT1 (MP ih0 (ASSUME a)))))) in
  let ihb = SPECL [`nPbase`; i0'] ih in
  let a' = lhand(concl ihb) in
  let lt = lhand a' in
  let mihl = GEN i0' (DISCH lt (MP (CONJUNCT2 (MP ihb (DISJ1 (ASSUME lt) (rand a'))))
                                   (REFL `nPbase`))) in
  LABEL_TAC "mih" mih THEN LABEL_TAC "mihl" mihl);;

let PARSE3AUX_pat_mono_tm =
 `!N i0.
     (!i r sfx eo.
        N IN {nPbase, nPtuple, nPattern, nPapp, nPatternList, nPas, nPcons, nV} /\
        (~(i = []) ==> FST (HD i) IN stoppers N) /\
        (i = [] /\ ~(sfx = []) ==> FST (HD sfx) IN stoppers N) /\
        peg_eval cmlPEG (i0, peg_nt (INL N) I) (peg_Success i r eo) ==>
        peg_eval cmlPEG (APPEND i0 sfx, peg_nt (INL N) I)
                 (peg_Success (APPEND i sfx) r eo)) /\
     (N = nPbase ==>
      !rlist i err sfx.
        (~(i = []) ==> ~(FST (HD i) IN firstSet cmlG [NT (INL nPbase)])) /\
        (i = [] /\ ~(sfx = []) ==>
         ~(FST (HD sfx) IN firstSet cmlG [NT (INL nPbase)])) /\
        peg_eval_list cmlPEG (i0, peg_nt (INL nPbase) I) (i, rlist, err) ==>
        ?res'. peg_eval_list cmlPEG (APPEND i0 sfx, peg_nt (INL nPbase) I)
                             (APPEND i sfx, rlist, res'))`;;

let PARSE3AUX_PAT_START_TAC : tactic =
  MATCH_MP_TAC PARSE3AUX_LEX_IND THEN
  MAP_EVERY X_GEN_TAC [`N:MMLnonT`; `i0:(token#locs)list`] THEN
  PARSE3AUX_PAT_IH_TAC THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "H")))) THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC);
    ALL_TAC];;

(* the list part of the induction: Pbase repetitions *)
let PARSE3AUX_PAT_LIST_TAC : tactic =
  DISCH_THEN(LABEL_TAC "NL") THEN DISCH_THEN SUBST_ALL_TAC THEN
  MAP_EVERY X_GEN_TAC [`rlist:((mlptree)list)list`; `i:(token#locs)list`;
                       `err:locs#(char)list`; `sfx:(token#locs)list`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  GEN_REWRITE_TAC LAND_CONV [peg_eval_list] THEN STRIP_TAC THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `i:(token#locs)list`)) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
      lhs(concl th) = `rlist:((mlptree)list)list`)) THEN
    SUBGOAL_THEN `?fl' fe'. peg_eval cmlPEG (APPEND i0 sfx, peg_nt (INL nPbase) I)
                                     (Failure fl' fe')` STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC PARSE3AUX_nt_fail THEN REWRITE_TAC[NTS_in_PEG_exprs; peg0_nPbase] THEN
      MP_TAC(ISPEC `i0:(token#locs)list` list_CASES) THEN
      DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC
        (X_CHOOSE_THEN `h:token#locs` (X_CHOOSE_THEN `t:(token#locs)list`
          SUBST_ALL_TAC))) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[NOT_CONS_NIL; HD]) THEN
      ASM_REWRITE_TAC[APPEND; NOT_CONS_NIL; HD];
      EXISTS_TAC `(fl',fe'):locs#(char)list` THEN
      MATCH_MP_TAC peg_eval_list_nil THEN ASM_REWRITE_TAC[]];
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
      lhs(concl th) = `rlist:((mlptree)list)list`)) THEN
    SUBGOAL_THEN `peg_eval cmlPEG (APPEND i0 sfx, peg_nt (INL nPbase) I)
                    (peg_Success (APPEND i1 sfx) rh eo0)` ASSUME_TAC THENL
     [USE_THEN "NL" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[IN_INSERT; stoppers_def; IN_UNIV];
      ALL_TAC] THEN
    SUBGOAL_THEN `LENGTH (i1:(token#locs)list) < LENGTH (i0:(token#locs)list)`
      ASSUME_TAC THENL
     [MATCH_MP_TAC(MATCH_MP not_peg0_LENGTH_decreases peg0_nPbase) THEN
      MAP_EVERY EXISTS_TAC [`rh:(mlptree)list`; `eo0:(locs#(char)list)option`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    USE_THEN "mihl" (MP_TAC o SPECL [`rt:((mlptree)list)list`; `i:(token#locs)list`;
                                     `err:locs#(char)list`; `sfx:(token#locs)list`] o
                     C MP (ASSUME `LENGTH (i1:(token#locs)list) < LENGTH (i0:(token#locs)list)`) o
                     SPEC `i1:(token#locs)list`) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_TAC `res':locs#(char)list`) THEN
    EXISTS_TAC `res':locs#(char)list` THEN
    MATCH_MP_TAC peg_eval_list_cons THEN
    MAP_EVERY EXISTS_TAC [`eo0:(locs#(char)list)option`; `APPEND i1 sfx:(token#locs)list`] THEN
    ASM_REWRITE_TAC[]];;

let PARSE3AUX_pat_mono =
  (* nPbase and nPapp: the evaluation fact is inverted once, before the split *)
  (* of the rest (inverting it in each of the three branches cost 9-15 s each) *)
  let inv_first_tac =
    PARSE3AUX_INV_TAC "H" THEN PARSE3AUX_RSPLIT_TAC THEN
    PARSE3AUX_REPORT_TAC PARSE3AUX_MONO_LEAF_TAC in
  prove
 (PARSE3AUX_pat_mono_tm,
  PARSE3AUX_PAT_START_TAC THENL
   ([inv_first_tac] @ replicate PARSE3AUX_MONO_CASE_TAC 2 @ [inv_first_tac] @
    replicate PARSE3AUX_MONO_CASE_TAC 4 @ [PARSE3AUX_PAT_LIST_TAC]));;

(* HOL4: [local] *)
let pegComplete_Pattern_input_monotone0 = prove
 (`!N i0 rlist b i r l sfx eo res.
     (N IN {nPbase, nPtuple, nPattern, nPapp, nPatternList, nPas, nPcons, nV} /\
      ~b /\ (~(i = []) ==> FST (HD i) IN stoppers N) /\
      (i = [] /\ ~(sfx = []) ==> FST (HD sfx) IN stoppers N) /\
      peg_eval cmlPEG (i0, peg_nt (INL N) I) (peg_Success i r eo) ==>
      peg_eval cmlPEG (APPEND i0 sfx, peg_nt (INL N) I)
               (peg_Success (APPEND i sfx) r eo)) /\
     (N = nPbase /\ b /\
      (~(i = []) ==> ~(FST (HD i) IN firstSet cmlG [NT (INL nPbase)])) /\
      (i = [] /\ ~(sfx = []) ==>
       ~(FST (HD sfx) IN firstSet cmlG [NT (INL nPbase)])) /\
      peg_eval_list cmlPEG (i0, peg_nt (INL N) I) (i, rlist, l, res) ==>
      ?res'. peg_eval_list cmlPEG (APPEND i0 sfx, peg_nt (INL N) I)
                           (APPEND i sfx, rlist, res'))`,
  REPEAT GEN_TAC THEN CONJ_TAC THEN STRIP_TAC THENL
   [MATCH_MP_TAC(CONJUNCT1(SPECL [`N:MMLnonT`; `i0:(token#locs)list`]
                                 PARSE3AUX_pat_mono)) THEN
    ASM_REWRITE_TAC[];
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MP_TAC(MP (CONJUNCT2(SPECL [`nPbase`; `i0:(token#locs)list`] PARSE3AUX_pat_mono))
              (REFL `nPbase`)) THEN
    DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC `(l:locs,res:(char)list)` THEN
    ASM_REWRITE_TAC[]]);;

let pegComplete_Pattern_input_monotone =
  REWRITE_RULE[FORALL_AND_THM] pegComplete_Pattern_input_monotone0;;

let extend_Pbase_list = prove
 (`!results pfx sfx sfx' result e eo.
     peg_eval_list cmlPEG (pfx, peg_nt (INL nPbase) I) ([], results, e) /\
     peg_eval cmlPEG (sfx, peg_nt (INL nPbase) I) (peg_Success sfx' result eo) /\
     (~(sfx' = []) ==> ~(FST (HD sfx') IN firstSet cmlG [NT (INL nPbase)])) ==>
     ?e'. peg_eval_list cmlPEG (APPEND pfx sfx, peg_nt (INL nPbase) I)
                        (sfx', APPEND results [result], e')`,
  LIST_INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [peg_eval_list] THEN
    REWRITE_TAC[NOT_CONS_NIL] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
      concl th = `[]:(token#locs)list = pfx`)) THEN
    REWRITE_TAC[APPEND] THEN
    SUBGOAL_THEN `?fl' fe'. peg_eval cmlPEG (sfx', peg_nt (INL nPbase) I) (Failure fl' fe')`
      STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC PARSE3AUX_nt_fail THEN
      ASM_REWRITE_TAC[NTS_in_PEG_exprs; peg0_nPbase];
      ALL_TAC] THEN
    EXISTS_TAC `(fl',fe'):locs#(char)list` THEN
    MATCH_MP_TAC peg_eval_list_cons THEN
    MAP_EVERY EXISTS_TAC [`eo:(locs#(char)list)option`; `sfx':(token#locs)list`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC peg_eval_list_nil THEN ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [peg_eval_list] THEN
    REWRITE_TAC[NOT_CONS_NIL; CONS_11] THEN STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
      is_eq(concl th) && is_var(lhs(concl th)) && is_var(rhs(concl th))))) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`i1:(token#locs)list`; `sfx:(token#locs)list`;
                                  `sfx':(token#locs)list`; `result:(mlptree)list`;
                                  `e:locs#(char)list`; `eo:(locs#(char)list)option`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_TAC `e':locs#(char)list`) THEN
    EXISTS_TAC `e':locs#(char)list` THEN REWRITE_TAC[APPEND] THEN
    MATCH_MP_TAC peg_eval_list_cons THEN
    MAP_EVERY EXISTS_TAC [`eo0:(locs#(char)list)option`; `APPEND i1 sfx:(token#locs)list`] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(CONJUNCT1 pegComplete_Pattern_input_monotone) THEN
    EXISTS_TAC `F` THEN ASM_REWRITE_TAC[IN_INSERT; stoppers_def; IN_UNIV]]);;

let papp_complete = prove
 (`!master.
    (!pt' pfx' N sfx'.
       LENGTH pfx' < LENGTH master /\ valid_lptree cmlG pt' /\
       INL N IN FDOM (peg_rules cmlPEG) /\ ptree_head pt' = NT (INL N) /\
       real_fringe pt' = MAP (TOK ## I) pfx' /\
       (~(sfx' = []) ==> FST (HD sfx') IN stoppers N) ==>
       ?eo. peg_eval cmlPEG (APPEND pfx' sfx', peg_nt (INL N) I)
                     (peg_Success sfx' [pt'] eo)) /\
    (!pt' sfx'.
       valid_lptree cmlG pt' /\ ptree_head pt' = NT (INL nConstructorName) /\
       real_fringe pt' = MAP (TOK ## I) master ==>
       ?eo. peg_eval cmlPEG (APPEND master sfx', peg_nt (INL nConstructorName) I)
                     (peg_Success sfx' [pt'] eo)) ==>
    !pfx accpt sfx.
      pfx <<= master /\ valid_lptree cmlG accpt /\
      ptree_head accpt = NT (INL nPConApp) /\
      real_fringe accpt = MAP (TOK ## I) pfx /\
      (~(sfx = []) ==> FST (HD sfx) IN stoppers nPConApp) ==>
      ?cpt i bpts eo e.
        peg_eval cmlPEG (APPEND pfx sfx, peg_nt (INL nConstructorName) I)
                 (peg_Success i [cpt] eo) /\
        peg_eval_list cmlPEG (i, peg_nt (INL nPbase) I) (sfx, bpts, e) /\
        accpt = FOLDL (\pcpt bpt. bindNT0 nPConApp [pcpt; bpt])
                      (mkNd (INL nPConApp) [cpt]) (FLAT bpts)`,
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ihC")) THEN
  SUBGOAL_THEN
   `!n (pfx:(token#locs)list) accpt sfx.
      LENGTH pfx = n /\ pfx <<= master /\ valid_lptree cmlG accpt /\
      ptree_head accpt = NT (INL nPConApp) /\
      real_fringe accpt = MAP (TOK ## I) pfx /\
      (~(sfx = []) ==> FST (HD sfx) IN stoppers nPConApp) ==>
      ?cpt i bpts eo e.
        peg_eval cmlPEG (APPEND pfx sfx, peg_nt (INL nConstructorName) I)
                 (peg_Success i [cpt] eo) /\
        peg_eval_list cmlPEG (i, peg_nt (INL nPbase) I) (sfx, bpts, e) /\
        accpt = FOLDL (\pcpt bpt. bindNT0 nPConApp [pcpt; bpt])
                      (mkNd (INL nPConApp) [cpt]) (FLAT bpts)`
   (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_THEN(LABEL_TAC "ihn") THEN
  MAP_EVERY X_GEN_TAC [`pfx:(token#locs)list`; `accpt:mlptree`; `sfx:(token#locs)list`] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`accpt:mlptree`; `nPConApp`; `pfx:(token#locs)list`] ptree_head_NT_mkNd) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `subs:(mlptree)list` SUBST_ALL_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[valid_lptree_mkNd; real_fringe_mkNd]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  PARSE3AUX_GRULE_CASES_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MEM; DISJ_IMP_THM; FORALL_AND_THM; FORALL_UNWIND_THM2]) THEN
  PARSE3AUX_FRINGE_SPLIT_TAC THENL
   [SUBGOAL_THEN `?eo. peg_eval cmlPEG (APPEND pfx sfx, peg_nt (INL nConstructorName) I)
                                (peg_Success sfx [h0] eo)` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(pfx:(token#locs)list) <<= master` THEN REWRITE_TAC[IS_PREFIX_APPEND] THEN
      DISCH_THEN(X_CHOOSE_THEN `q:(token#locs)list` SUBST_ALL_TAC) THEN
      ASM_CASES_TAC `q:(token#locs)list = []` THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN
        USE_THEN "ihC" (MP_TAC o SPECL [`h0:mlptree`; `sfx:(token#locs)list`]) THEN
        REWRITE_TAC[APPEND_NIL] THEN ASM_REWRITE_TAC[];
        USE_THEN "ih1" (MP_TAC o SPECL [`h0:mlptree`; `pfx:(token#locs)list`;
                                        `nConstructorName`; `sfx:(token#locs)list`]) THEN
        REWRITE_TAC[stoppers_def; IN_UNIV; FDOM_cmlPEG_nts; LENGTH_APPEND] THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
        UNDISCH_TAC `~(q:(token#locs)list = [])` THEN
        REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `?fl fe. peg_eval cmlPEG (sfx, peg_nt (INL nPbase) I) (Failure fl fe)`
      STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC PARSE3AUX_nt_fail THEN REWRITE_TAC[NTS_in_PEG_exprs; peg0_nPbase] THEN
      PARSE3AUX_HD_NOTIN_TAC `sfx:(token#locs)list`;
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`h0:mlptree`; `sfx:(token#locs)list`; `[]:((mlptree)list)list`;
                          `eo:(locs#(char)list)option`; `(fl,fe):locs#(char)list`] THEN
    ASM_REWRITE_TAC[FLAT; FOLDL] THEN MATCH_MP_TAC peg_eval_list_nil THEN
    ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)) THEN
  MP_TAC(MATCH_MP PARSE3AUX_FRINGE_CONS
     (CONJ (ASSUME `real_fringe (h0':mlptree) = MAP (TOK ## I) m2`)
     (CONJ (ASSUME `ptree_head (h0':mlptree) = NT (INL nPbase)`)
     (CONJ (ASSUME `valid_lptree cmlG (h0':mlptree)`) nullable_Pbase)))) THEN
  DISCH_THEN(X_CHOOSE_THEN `bt:token` (X_CHOOSE_THEN `bl:locs`
    (X_CHOOSE_THEN `m2r:(token#locs)list` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)))) THEN
  MP_TAC(MATCH_MP PARSE3AUX_FRINGE_CONS
     (CONJ (ASSUME `real_fringe (h0:mlptree) = MAP (TOK ## I) m1`)
     (CONJ (ASSUME `ptree_head (h0:mlptree) = NT (INL nPConApp)`)
     (CONJ (ASSUME `valid_lptree cmlG (h0:mlptree)`) nullable_PConApp)))) THEN
  DISCH_THEN(X_CHOOSE_THEN `ct:token` (X_CHOOSE_THEN `cl:locs`
    (X_CHOOSE_THEN `m1r:(token#locs)list` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)))) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "isPREFIX" with Failure _ -> false)) THEN
  REWRITE_TAC[IS_PREFIX_APPEND] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:(token#locs)list` SUBST_ALL_TAC) THEN
    USE_THEN "ihn" (MP_TAC o SPEC `LENGTH (CONS (ct:token,cl:locs) m1r)`) THEN
  ANTS_TAC THENL [REWRITE_TAC[LENGTH; LENGTH_APPEND] THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`CONS (ct:token,cl:locs) m1r`; `h0:mlptree`;
                             `[]:(token#locs)list`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[NOT_CONS_NIL; IS_PREFIX_APPEND] THEN
    EXISTS_TAC `APPEND (CONS (bt:token,bl:locs) m2r) q` THEN
    REWRITE_TAC[APPEND_ASSOC];
    ALL_TAC] THEN
  REWRITE_TAC[APPEND_NIL] THEN
  DISCH_THEN(X_CHOOSE_THEN `cpt:mlptree` (X_CHOOSE_THEN `i:(token#locs)list`
    (X_CHOOSE_THEN `bpts:((mlptree)list)list` (X_CHOOSE_THEN `eo:(locs#(char)list)option`
      (X_CHOOSE_THEN `e:locs#(char)list` STRIP_ASSUME_TAC))))) THEN
    MP_TAC(ISPECL [`CONS (ct:token,cl:locs) m1r`; `i:(token#locs)list`; `[cpt]:(mlptree)list`;
                 `eo:(locs#(char)list)option`; `APPEND (CONS (bt:token,bl:locs) m2r) sfx`]
                nConstructorName_input_monotone) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `?eob. peg_eval cmlPEG (APPEND (CONS (bt,bl) m2r) sfx, peg_nt (INL nPbase) I)
                        (peg_Success sfx [h0'] eob)`
    (X_CHOOSE_TAC `eob:(locs#(char)list)option`) THENL
   [USE_THEN "ih1" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[stoppers_def; IN_UNIV; FDOM_cmlPEG_nts] THEN
    REWRITE_TAC[LENGTH; LENGTH_APPEND] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`bpts:((mlptree)list)list`; `i:(token#locs)list`;
                 `APPEND (CONS (bt:token,bl:locs) m2r) sfx`; `sfx:(token#locs)list`;
                 `[h0']:(mlptree)list`; `e:locs#(char)list`;
                 `eob:(locs#(char)list)option`] extend_Pbase_list) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [PARSE3AUX_HD_NOTIN_TAC `sfx:(token#locs)list`; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `e':locs#(char)list`) THEN
  MAP_EVERY EXISTS_TAC [`cpt:mlptree`; `APPEND i (APPEND (CONS (bt:token,bl:locs) m2r) sfx)`;
                        `APPEND bpts [[h0']]:((mlptree)list)list`;
                        `eo:(locs#(char)list)option`; `e':locs#(char)list`] THEN
  ASM_REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  REWRITE_TAC[FLAT_APPEND; FOLDL_APPEND; FLAT; APPEND_NIL; FOLDL; bindNT0_lemma]]);;

let leftmost_mkNd_DType = prove
 (`!(c:mlptree) cs. leftmost (mkNd (INL nDType) (CONS c cs)) = leftmost c`,
  REWRITE_TAC[PARSE3AUX_leftmost_DType]);;

let _ = cake_add_simps [leftmost_mkNd_DType];;

let leftmost_mkNd_Tbase = prove
 (`!(x:mlptree) xs. leftmost (mkNd (INL nTbase) (CONS x xs)) = x`,
  REWRITE_TAC[PARSE3AUX_leftmost_Tbase]);;

let _ = cake_add_simps [leftmost_mkNd_Tbase];;

let leftmost_FOLDL = prove
 (`!(acc:mlptree) args.
     leftmost (FOLDL (\a b. mkNd (INL nDType) [a; b]) acc args) = leftmost acc`,
  GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[FOLDL; leftmost_mkNd_DType]);;

let left_insert2_mkNd = prove
 (`!(bpt:mlptree) n sub.
     left_insert2 bpt (mkNd (INL nDType) [mkNd n [sub]]) =
     mkNd (INL nDType) [mkNd (INL nDType) [bpt]; sub]`,
  REWRITE_TAC[PARSE3AUX_left_insert2_mkNd1]);;

let _ = cake_add_simps [left_insert2_mkNd];;

(* the evaluation of peg_nt nDType, in terms of nTbase and the repetition of  *)
(* nTyOp                                                                   *)
let PARSE3AUX_DType_intro = prove
 (`!i0 i1 i h eo1 l err x t.
     peg_eval cmlPEG (i0, peg_nt (INL nTbase) I) (peg_Success i1 h eo1) /\
     peg_eval_list cmlPEG (i1, peg_nt (INL nTyOp) I) (i, l, err) /\
     APPEND h (FLAT l) = CONS x t ==>
     ?eo. peg_eval cmlPEG (i0, peg_nt (INL nDType) I)
            (peg_Success i [FOLDL (\a b. mkNd (INL nDType) [a; b])
                                  (mkNd (INL nDType) [x]) t] eo)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[peg_eval_NT_SOME; PARSE2AUX_rule `nDType`; FDOM_cmlPEG_nts; I_THM] THEN
  REWRITE_TAC[seql_cons_SOME; PARSE3AUX_S_seql_NIL; cmlPEG_pnt_def; peg_eval_rpt] THEN
  EXISTS_TAC `NONE:(locs#(char)list)option` THEN
  EXISTS_TAC `[FOLDL (\a b. mkNd (INL nDType) [a; b]) (mkNd (INL nDType) [x]) t]:(mlptree)list` THEN
  REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`i1:(token#locs)list`; `h:(mlptree)list`;
                        `FLAT (l:((mlptree)list)list)`; `eo1:(locs#(char)list)option`] THEN
  ASM_REWRITE_TAC[I_THM; APPEND_NIL] THEN
  CONJ_TAC THENL
   [MAP_EVERY EXISTS_TAC [`i:(token#locs)list`; `FLAT (l:((mlptree)list)list)`;
                          `[]:(mlptree)list`; `SOME (err:locs#(char)list)`] THEN
    REWRITE_TAC[APPEND_NIL] THEN
    MAP_EVERY EXISTS_TAC [`i:(token#locs)list`; `l:((mlptree)list)list`;
                          `err:locs#(char)list`] THEN
    ASM_REWRITE_TAC[];
    CASE_REWRITE_TAC[]]);;

let PARSE3AUX_DType_inv = prove
 (`!i0 i r eo.
     peg_eval cmlPEG (i0, peg_nt (INL nDType) I) (peg_Success i r eo) ==>
     ?i1 h eo1 l err.
       peg_eval cmlPEG (i0, peg_nt (INL nTbase) I) (peg_Success i1 h eo1) /\
       peg_eval_list cmlPEG (i1, peg_nt (INL nTyOp) I) (i, l, err) /\
       (APPEND h (FLAT l) = [] /\ r = [] \/
        ?x t. APPEND h (FLAT l) = CONS x t /\
              r = [FOLDL (\a b. mkNd (INL nDType) [a; b]) (mkNd (INL nDType) [x]) t])`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[peg_eval_NT_SOME; PARSE2AUX_rule `nDType`;
                                   FDOM_cmlPEG_nts; I_THM]) THEN
  REWRITE_TAC[seql_cons_SOME; PARSE3AUX_S_seql_NIL; cmlPEG_pnt_def; peg_eval_rpt;
              pegresult_inject; I_THM; APPEND_NIL] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  MAP_EVERY EXISTS_TAC [`i1:(token#locs)list`; `rh:(mlptree)list`;
                        `eo1:(locs#(char)list)option`; `l:((mlptree)list)list`;
                        `err:locs#(char)list`] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `APPEND (rh:(mlptree)list) (FLAT (l:((mlptree)list)list))` list_CASES) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[NOT_CONS_NIL; APPEND_NIL] THEN
  CASE_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`h:mlptree`; `t:(mlptree)list`] THEN REWRITE_TAC[]);;

(* a Tbase whose first token can start a TyOp is a TyOp *)
let PARSE3AUX_Tbase_TyOp = prove
 (`!x i r eo.
     peg_eval cmlPEG (x, peg_nt (INL nTbase) I) (peg_Success i r eo) /\
     (~(x = []) ==> FST (HD x) IN firstSet cmlG [NT (INL nTyOp)]) ==>
     ?tr eo'. peg_eval cmlPEG (x, peg_nt (INL nTyOp) I) (peg_Success i tr eo') /\
              r = bindNT nTbase tr`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "H") ASSUME_TAC) THEN
  PARSE3AUX_JSPLIT_TAC `x:(token#locs)list` THEN
  PARSE3AUX_INV_TAC "H" THEN
  FIRST_ASSUM(fun th ->
    let c = concl th in
    if PARSE3AUX_is_evalfact c &&
       (let _,e,_ = PARSE3AUX_eval_parts c in e = `peg_nt (INL nTyOp) I:(token,MMLnonT,(mlptree)list,(char)list)pegsym`)
    then let _,r1,eo1 = PARSE3AUX_succ_parts th in
         MAP_EVERY EXISTS_TAC [r1; eo1] THEN ASM_REWRITE_TAC[] THEN
         REWRITE_TAC PARSE3AUX_RESULT_RWTS
    else failwith ""));;

(* the fringe of the leftmost subtree is a prefix of the fringe *)
let PARSE3AUX_leftmost_fringe = prove
 (`!pt:mlptree. ?rest. real_fringe pt = APPEND (real_fringe (leftmost pt)) rest`,
  MATCH_MP_TAC ptree_ind THEN CONJ_TAC THENL
   [REWRITE_TAC[leftmost_def] THEN MESON_TAC[APPEND_NIL];
    X_GEN_TAC `subs:(mlptree)list` THEN DISCH_TAC THEN
    REWRITE_TAC[FORALL_PAIR_THM; leftmost_def; real_fringe_def] THEN
    MAP_EVERY X_GEN_TAC [`n:MMLnonT+num`; `l:locs`] THEN
    MP_TAC(ISPEC `subs:(mlptree)list` list_CASES) THEN
    DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC
      (X_CHOOSE_THEN `a:mlptree` (X_CHOOSE_THEN `as:(mlptree)list` SUBST_ALL_TAC))) THEN
    CASE_REWRITE_TAC[NOT_CONS_NIL; HD; real_fringe_def; MAP; FLAT] THENL
     [MESON_TAC[APPEND_NIL]; ALL_TAC] THEN
    COND_CASES_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `a:mlptree` o REWRITE_RULE[MEM]) THEN
    REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:((token,MMLnonT)symbol#locs)list` SUBST1_TAC) THEN
    MESON_TAC[APPEND_ASSOC]]);;

let dtype_complete = prove
 (`!master.
  (!pt' pfx' sfx' N.
     LENGTH pfx' < LENGTH master /\ valid_lptree cmlG pt' /\
     INL N IN FDOM (peg_rules cmlPEG) /\
     ptree_head pt' = NT (INL N) /\ real_fringe pt' = MAP (TOK ## I) pfx' /\
     (~(sfx' = []) ==> FST (HD sfx') IN stoppers N) ==>
     ?eo. peg_eval cmlPEG (APPEND pfx' sfx', peg_nt (INL N) I)
                   (peg_Success sfx' [pt'] eo)) /\
  (!pt' sfx'.
     valid_lptree cmlG pt' /\ ptree_head pt' = NT (INL nTbase) /\
     real_fringe pt' = MAP (TOK ## I) master /\
     (~(sfx' = []) ==> FST (HD sfx') IN stoppers nEbase) ==>
     ?eo. peg_eval cmlPEG (APPEND master sfx', peg_nt (INL nTbase) I)
                   (peg_Success sfx' [pt'] eo))
  ==>
  !pfx apt sfx.
    IS_SUFFIX master pfx /\ valid_lptree cmlG apt /\
    ptree_head apt = NT (INL nDType) /\ real_fringe apt = MAP (TOK ## I) pfx /\
    (~(sfx = []) ==> FST (HD sfx) IN stoppers nDType) ==>
    ?eo. peg_eval cmlPEG (APPEND pfx sfx, peg_nt (INL nDType) I)
                  (peg_Success sfx [apt] eo)`,
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ihT")) THEN
  SUBGOAL_THEN
   `!n (pfx:(token#locs)list) apt sfx.
      LENGTH pfx = n /\ IS_SUFFIX master pfx /\ valid_lptree cmlG apt /\
      ptree_head apt = NT (INL nDType) /\ real_fringe apt = MAP (TOK ## I) pfx /\
      (~(sfx = []) ==> FST (HD sfx) IN stoppers nDType) ==>
      ?eo. peg_eval cmlPEG (APPEND pfx sfx, peg_nt (INL nDType) I)
                    (peg_Success sfx [apt] eo)`
   (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_THEN(LABEL_TAC "ihn") THEN
  MAP_EVERY X_GEN_TAC [`pfx:(token#locs)list`; `apt:mlptree`; `sfx:(token#locs)list`] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`apt:mlptree`; `nDType`; `pfx:(token#locs)list`] ptree_head_NT_mkNd) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `subs:(mlptree)list` SUBST_ALL_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[valid_lptree_mkNd; real_fringe_mkNd]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  PARSE3AUX_GRULE_CASES_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MEM; DISJ_IMP_THM; FORALL_AND_THM; FORALL_UNWIND_THM2]) THEN
  PARSE3AUX_FRINGE_SPLIT_TAC THENL
   [(* DType -> DType TyOp *)
    FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)) THEN
  MP_TAC(SPECL [`h0:mlptree`; `h0':mlptree`; `m1:(token#locs)list`;
                `m2:(token#locs)list`] dtype_reassociated) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `apt':mlptree` (X_CHOOSE_THEN `bpt':mlptree`
    STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o SYM o check (fun th -> is_eq(concl th) &&
     (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "APPEND"
      with Failure _ -> false))) THEN
  REWRITE_TAC[LPARSEAUX_MAP_EQ_APPEND] THEN
  DISCH_THEN(X_CHOOSE_THEN `bf:(token#locs)list` (X_CHOOSE_THEN `af:(token#locs)list`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN (ASSUME_TAC o SYM))))) THEN
  MP_TAC(MATCH_MP PARSE3AUX_FRINGE_CONS
     (CONJ (ASSUME `real_fringe (bpt':mlptree) = MAP (TOK ## I) bf`)
     (CONJ (ASSUME `ptree_head (bpt':mlptree) = NT (INL nTbase)`)
     (CONJ (ASSUME `valid_lptree cmlG (bpt':mlptree)`) nullable_Tbase)))) THEN
  DISCH_THEN(X_CHOOSE_THEN `bt:token` (X_CHOOSE_THEN `bl:locs`
    (X_CHOOSE_THEN `bf_r:(token#locs)list`
      (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)))) THEN
  MP_TAC(MATCH_MP PARSE3AUX_FRINGE_CONS
     (CONJ (ASSUME `real_fringe (apt':mlptree) = MAP (TOK ## I) af`)
     (CONJ (ASSUME `ptree_head (apt':mlptree) = NT (INL nDType)`)
     (CONJ (ASSUME `valid_lptree cmlG (apt':mlptree)`) nullable_DType)))) THEN
  DISCH_THEN(X_CHOOSE_THEN `at:token` (X_CHOOSE_THEN `al:locs`
    (X_CHOOSE_THEN `af_r:(token#locs)list`
      (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)))) THEN
  ASM_REWRITE_TAC[GSYM APPEND_ASSOC] THEN REWRITE_TAC[APPEND_ASSOC] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  UNDISCH_TAC `IS_SUFFIX (master:(token#locs)list) (APPEND m1 m2)` THEN
  ASM_REWRITE_TAC[LPARSEAUX_IS_SUFFIX_APPEND] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:(token#locs)list` ASSUME_TAC) THEN
  SUBGOAL_THEN `?eo. peg_eval cmlPEG
      (APPEND (CONS (bt,bl) bf_r) (APPEND (CONS (at,al) af_r) sfx), peg_nt (INL nTbase) I)
      (peg_Success (APPEND (CONS (at,al) af_r) sfx) [bpt'] eo)`
    (X_CHOOSE_TAC `eob:(locs#(char)list)option`) THENL
   [USE_THEN "ih1" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[stoppers_def; IN_UNIV; FDOM_cmlPEG_nts] THEN
    REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?eo. peg_eval cmlPEG (APPEND (CONS (at,al) af_r) sfx, peg_nt (INL nDType) I)
                       (peg_Success sfx [apt'] eo)`
    (X_CHOOSE_TAC `eoa:(locs#(char)list)option`) THENL
   [USE_THEN "ihn" (MP_TAC o SPEC `LENGTH (CONS (at:token,al:locs) af_r)`) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[LPARSEAUX_IS_SUFFIX_APPEND] THEN
    EXISTS_TAC `APPEND p (CONS (bt:token,bl:locs) bf_r)` THEN
    REWRITE_TAC[APPEND_ASSOC];
    ALL_TAC] THEN
    SUBGOAL_THEN `at IN firstSet cmlG [NT (INL nTyOp)]` ASSUME_TAC THENL
   [MP_TAC(ISPEC `apt':mlptree` PARSE3AUX_leftmost_fringe) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `rest:((token,MMLnonT)symbol#locs)list` MP_TAC) THEN
    REWRITE_TAC[LPARSEAUX_MAP_EQ_APPEND] THEN
    DISCH_THEN(X_CHOOSE_THEN `f1:(token#locs)list` (X_CHOOSE_THEN `f2:(token#locs)list`
      STRIP_ASSUME_TAC)) THEN
    MP_TAC(MATCH_MP PARSE3AUX_FRINGE_CONS
       (CONJ (SYM(ASSUME `MAP ((TOK:token->(token,MMLnonT)symbol) ## (I:locs->locs)) f1 = real_fringe (leftmost (apt':mlptree))`))
       (CONJ (ASSUME `ptree_head (leftmost (apt':mlptree)) = NT (INL nTyOp)`)
       (CONJ (ASSUME `valid_lptree cmlG (leftmost (apt':mlptree))`) nullable_TyOp)))) THEN
    DISCH_THEN(X_CHOOSE_THEN `tk:token` (X_CHOOSE_THEN `lk:locs`
      (X_CHOOSE_THEN `f1r:(token#locs)list` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)))) THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) && is_cons(lhs(concl th)))) THEN
    REWRITE_TAC[APPEND; CONS_11; PAIR_EQ] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
    MP_TAC(MATCH_MP PARSE3AUX_DType_inv (ASSUME
     `peg_eval cmlPEG (APPEND (CONS (at,al) af_r) sfx, peg_nt (INL nDType) I)
                      (peg_Success sfx [apt'] eoa)`)) THEN
  REWRITE_TAC[NOT_CONS_NIL; CONS_11] THEN
  DISCH_THEN(X_CHOOSE_THEN `i1:(token#locs)list` (X_CHOOSE_THEN `h:(mlptree)list`
    (X_CHOOSE_THEN `eo1:(locs#(char)list)option` (X_CHOOSE_THEN `l:((mlptree)list)list`
      (X_CHOOSE_THEN `err:locs#(char)list` STRIP_ASSUME_TAC))))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    try lhs(concl th) = `apt':mlptree` with Failure _ -> false)) THEN
    MP_TAC(ISPECL [`APPEND (CONS (at:token,al:locs) af_r) sfx`; `i1:(token#locs)list`;
                 `h:(mlptree)list`; `eo1:(locs#(char)list)option`] PARSE3AUX_Tbase_TyOp) THEN
  ASM_REWRITE_TAC[APPEND; NOT_CONS_NIL; HD] THEN
  DISCH_THEN(X_CHOOSE_THEN `tr:(mlptree)list` (X_CHOOSE_THEN `eot:(locs#(char)list)option`
    STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP peg_sound o check (fun th ->
    try rand(rand(rator(concl th))) = `peg_nt (INL nTyOp) I:(token,MMLnonT,(mlptree)list,(char)list)pegsym`
    with Failure _ -> false)) THEN
  DISCH_THEN(X_CHOOSE_THEN `tyop2:mlptree` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `tr = [tyop2:mlptree]`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> try lhs(concl th) = `h:(mlptree)list` with Failure _ -> false)) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> try rhs(concl th) = `CONS (x:mlptree) t` with Failure _ -> false)) THEN
  REWRITE_TAC[bindNT_def; bindNT0_lemma; APPEND; CONS_11] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  MP_TAC(ISPECL [`CONS (bt:token,bl:locs) (APPEND bf_r (CONS (at,al) (APPEND af_r sfx)))`;
                 `CONS (at:token,al:locs) (APPEND af_r sfx)`; `sfx:(token#locs)list`;
                 `[bpt']:(mlptree)list`; `eob:(locs#(char)list)option`;
                 `CONS [tyop2:mlptree] l`; `err:locs#(char)list`; `bpt':mlptree`;
                 `CONS (tyop2:mlptree) (FLAT l)`] PARSE3AUX_DType_intro) THEN
  ANTS_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[APPEND]) THEN ASM_REWRITE_TAC[FLAT; APPEND] THEN
    MATCH_MP_TAC peg_eval_list_cons THEN
    MAP_EVERY EXISTS_TAC [`eot:(locs#(char)list)option`; `i1:(token#locs)list`] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[left_insert2_FOLDL; left_insert2_mkNd; FOLDL]];
    (* DType -> Tbase *)
    SUBGOAL_THEN `?eo. peg_eval cmlPEG (APPEND pfx sfx, peg_nt (INL nTbase) I)
                                (peg_Success sfx [h0] eo)` STRIP_ASSUME_TAC THENL
     [MP_TAC(ISPECL [`master:(token#locs)list`; `pfx:(token#locs)list`]
                    LPARSEAUX_IS_SUFFIX_APPEND) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `p:(token#locs)list` SUBST_ALL_TAC) THEN
      ASM_CASES_TAC `p:(token#locs)list = []` THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN
        USE_THEN "ihT" (MP_TAC o SPECL [`h0:mlptree`; `sfx:(token#locs)list`]) THEN
        REWRITE_TAC[APPEND] THEN REWRITE_TAC[stoppers_def; IN_UNIV] THEN
        ASM_REWRITE_TAC[];
        USE_THEN "ih1" (MP_TAC o SPECL [`h0:mlptree`; `pfx:(token#locs)list`;
                                        `sfx:(token#locs)list`; `nTbase`]) THEN
        REWRITE_TAC[stoppers_def; IN_UNIV; FDOM_cmlPEG_nts; LENGTH_APPEND] THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
        UNDISCH_TAC `~(p:(token#locs)list = [])` THEN
        REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `?fl fe. peg_eval cmlPEG (sfx, peg_nt (INL nTyOp) I) (Failure fl fe)`
      STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC PARSE3AUX_nt_fail THEN REWRITE_TAC[NTS_in_PEG_exprs; peg0_nTyOp] THEN
      UNDISCH_TAC `~(sfx:(token#locs)list = []) ==> FST (HD sfx) IN stoppers nDType` THEN
      REWRITE_TAC[stoppers_def; IN_DIFF; IN_UNIV];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`APPEND pfx sfx:(token#locs)list`; `sfx:(token#locs)list`;
                   `sfx:(token#locs)list`; `[h0]:(mlptree)list`;
                   `eo:(locs#(char)list)option`; `[]:((mlptree)list)list`;
                   `(fl:locs,fe:(char)list)`; `h0:mlptree`; `[]:(mlptree)list`]
                  PARSE3AUX_DType_intro) THEN
    REWRITE_TAC[FLAT; APPEND; FOLDL] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC peg_eval_list_nil THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[]]]);;

(* the evaluation of peg_linfix: e1, then the repetition of e2 e1 *)
let PARSE3AUX_linfix_intro = prove
 (`!tgt (e1:(token,MMLnonT,(mlptree)list,(char)list)pegsym) e2 i0 i1 i h eo1 l err.
     peg_eval cmlPEG (i0, e1) (peg_Success i1 [h] eo1) /\
     peg_eval_list cmlPEG (i1, peg_seq e2 e1 APPEND) (i, l, err) ==>
     ?eo. peg_eval cmlPEG (i0, peg_linfix tgt e1 e2)
            (peg_Success i [mk_linfix tgt (mkNd tgt [h]) (FLAT l)] eo)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[peg_linfix_def; peg_eval_seq_SOME; peg_eval_rpt] THEN
  EXISTS_TAC `SOME (err:locs#(char)list)` THEN
  MAP_EVERY EXISTS_TAC [`i1:(token#locs)list`; `[h]:(mlptree)list`;
                        `FLAT (l:((mlptree)list)list)`; `eo1:(locs#(char)list)option`] THEN
  ASM_REWRITE_TAC[pegresult_inject] THEN CONJ_TAC THENL
   [MAP_EVERY EXISTS_TAC [`i:(token#locs)list`; `l:((mlptree)list)list`;
                          `err:locs#(char)list`] THEN ASM_REWRITE_TAC[];
    CASE_REWRITE_TAC[]]);;

let PARSE3AUX_linfix_inv = prove
 (`!tgt (e1:(token,MMLnonT,(mlptree)list,(char)list)pegsym) e2 i0 i r eo.
     peg_eval cmlPEG (i0, peg_linfix tgt e1 e2) (peg_Success i r eo) ==>
     ?i1 a eo1 l err.
       peg_eval cmlPEG (i0, e1) (peg_Success i1 a eo1) /\
       peg_eval_list cmlPEG (i1, peg_seq e2 e1 APPEND) (i, l, err) /\
       (a = [] /\ r = [] \/
        ?h t. a = CONS h t /\ r = [mk_linfix tgt (mkNd tgt [h]) (FLAT l)])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[peg_linfix_def; peg_eval_seq_SOME; peg_eval_rpt] THEN
  REWRITE_TAC[pegresult_inject] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`i1:(token#locs)list`; `r1:(mlptree)list`;
                        `eo1:(locs#(char)list)option`; `l:((mlptree)list)list`;
                        `err:locs#(char)list`] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `r1:(mlptree)list` list_CASES) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[NOT_CONS_NIL] THEN CASE_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`h:mlptree`; `t:(mlptree)list`] THEN ASM_REWRITE_TAC[]);;

(* the separator fails on a suffix that starts with a stopper of P *)
let PARSE3AUX_SEP_fail = prove
 (`!SEP P sfx.
     (!n. SEP = NT n ==> ?nn. n = INL nn /\ peg_nt (INL nn) I IN Gexprs cmlPEG /\
                              stoppers nn = (:token)) /\
     (!t. t IN firstSet cmlG [SEP] ==> ~(t IN stoppers P)) /\
     ~peg0 cmlPEG (sym2peg SEP) /\
     (~(sfx = []) ==> FST (HD sfx) IN stoppers P) ==>
     ?fl fe. peg_eval cmlPEG (sfx, sym2peg SEP) (Failure fl fe)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `SEP:(token,MMLnonT)symbol` (cases "symbol")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `a:token` SUBST_ALL_TAC)
                              (X_CHOOSE_THEN `a:MMLnonT+num` SUBST_ALL_TAC)) THEN
  REWRITE_TAC[symbol_distinct; symbol_inject; sym2peg_def] THEN STRIP_TAC THENL
   [MP_TAC(ISPEC `sfx:(token#locs)list` list_CASES) THEN
    DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC
      (X_CHOOSE_THEN `h:token#locs` (X_CHOOSE_THEN `t:(token#locs)list`
        SUBST_ALL_TAC))) THEN
    REWRITE_TAC[tokeq_def] THENL
     [MESON_TAC[peg_eval_tok_failureEOF]; ALL_TAC] THEN
    MP_TAC(ISPEC `h:token#locs` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `tk:token` (X_CHOOSE_THEN `l:locs` SUBST_ALL_TAC)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[NOT_CONS_NIL; HD; FST]) THEN
    MAP_EVERY EXISTS_TAC [`l:locs`; `peg_tokFALSE cmlPEG`] THEN
    MP_TAC(ISPECL [`cmlPEG`; `(tk:token,l:locs)`; `t:(token#locs)list`;
                   `(=) (a:token)`; `mktokLf:token#locs->(mlptree)list`]
                  peg_eval_tok_failureF) THEN
    REWRITE_TAC[FST; SND] THEN DISCH_THEN MATCH_MP_TAC THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `a:token`) THEN
    ASM_REWRITE_TAC[firstSet_TOK; IN_SING];
    FIRST_X_ASSUM(MP_TAC o SPEC `a:MMLnonT+num`) THEN REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `nn:MMLnonT` (CONJUNCTS_THEN2 SUBST_ALL_TAC
      STRIP_ASSUME_TAC)) THEN
    MATCH_MP_TAC PARSE3AUX_nt_fail THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[]]);;

(* the results of sym2peg C are single trees *)
let PARSE3AUX_sym2peg_single = prove
 (`!C i j r eo.
     (!n. C = NT n ==> ?nn. n = INL nn) /\
     peg_eval cmlPEG (i, sym2peg C) (peg_Success j r eo) ==> ?x. r = [x]`,
  GEN_TAC THEN
  MP_TAC(ISPEC `C:(token,MMLnonT)symbol` (cases "symbol")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `a:token` SUBST_ALL_TAC)
                              (X_CHOOSE_THEN `a:MMLnonT+num` SUBST_ALL_TAC)) THEN
  REWRITE_TAC[symbol_distinct; symbol_inject; sym2peg_def] THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[tokeq_def; peg_eval_tok_SOME; mktokLf_def] THEN MESON_TAC[];
    DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `a:MMLnonT+num`) ASSUME_TAC) THEN
    REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `nn:MMLnonT` SUBST_ALL_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP peg_sound) THEN MESON_TAC[]]);;

let peg_linfix_complete = prove
 (`!master SEP C P.
  (!n. SEP = NT n ==>
       ?nn. n = INL nn /\ peg_nt (INL nn) I IN Gexprs cmlPEG /\ stoppers nn = (:token)) /\
  (!n. C = NT n ==> ?nn. n = INL nn) /\
  (!t. t IN firstSet cmlG [SEP] ==> ~(t IN stoppers P)) /\
  (!n. C = NT (INL n) ==>
       (!t. t IN firstSet cmlG [SEP] ==> t IN stoppers n) /\
       (!t. t IN stoppers P ==> t IN stoppers n)) /\
  ~peg0 cmlPEG (sym2peg C) /\ ~nullable cmlG [C] /\
  ~peg0 cmlPEG (sym2peg SEP) /\ ~nullable cmlG [SEP] /\
  FAPPLY (grammar_rules cmlG) (INL P) = {[NT (INL P); SEP; C], [C]} /\
  (!pt pfx0 sfx.
     LENGTH pfx0 < LENGTH master /\
     (!n. ptree_head pt = NT (INL n) /\ ~(sfx = []) ==>
          FST (HD sfx) IN stoppers n) /\
     valid_lptree cmlG pt /\ ptree_head pt IN {SEP, C} /\
     real_fringe pt = MAP (TOK ## I) pfx0 ==>
     ?eo. peg_eval cmlPEG (APPEND pfx0 sfx, sym2peg (ptree_head pt))
                   (peg_Success sfx [pt] eo)) /\
  (!pt sfx.
     valid_lptree cmlG pt /\ ptree_head pt = C /\
     (!n. C = NT (INL n) /\ ~(sfx = []) ==> FST (HD sfx) IN stoppers n) /\
     real_fringe pt = MAP (TOK ## I) master ==>
     ?eo. peg_eval cmlPEG (APPEND master sfx, sym2peg C) (peg_Success sfx [pt] eo))
  ==>
  !pfx pt sfx.
    IS_SUFFIX master pfx /\ valid_lptree cmlG pt /\ ptree_head pt = NT (INL P) /\
    (~(sfx = []) ==> FST (HD sfx) IN stoppers P) /\
    real_fringe pt = MAP (TOK ## I) pfx ==>
    ?eo. peg_eval cmlPEG (APPEND pfx sfx, peg_linfix (INL P) (sym2peg C) (sym2peg SEP))
                  (peg_Success sfx [pt] eo)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "c1") (CONJUNCTS_THEN2 (LABEL_TAC "c2")
    (CONJUNCTS_THEN2 (LABEL_TAC "c3") (CONJUNCTS_THEN2 (LABEL_TAC "c4")
    (CONJUNCTS_THEN2 (LABEL_TAC "c5") (CONJUNCTS_THEN2 (LABEL_TAC "c6")
    (CONJUNCTS_THEN2 (LABEL_TAC "c7") (CONJUNCTS_THEN2 (LABEL_TAC "c8")
    (CONJUNCTS_THEN2 (LABEL_TAC "rules") (CONJUNCTS_THEN2 (LABEL_TAC "ih1")
      (LABEL_TAC "ihC"))))))))))) THEN
  SUBGOAL_THEN
   `!n (pfx:(token#locs)list) pt sfx.
      LENGTH pfx = n /\ IS_SUFFIX master pfx /\ valid_lptree cmlG pt /\
      ptree_head pt = NT (INL P) /\
      (~(sfx = []) ==> FST (HD sfx) IN stoppers P) /\
      real_fringe pt = MAP (TOK ## I) pfx ==>
      ?eo. peg_eval cmlPEG (APPEND pfx sfx, peg_linfix (INL P) (sym2peg C) (sym2peg SEP))
                    (peg_Success sfx [pt] eo)`
   (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_THEN(LABEL_TAC "ihn") THEN
  MAP_EVERY X_GEN_TAC [`pfx:(token#locs)list`; `pt:mlptree`; `sfx:(token#locs)list`] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`pt:mlptree`; `P:MMLnonT`; `pfx:(token#locs)list`] ptree_head_NT_mkNd) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `subs:(mlptree)list` SUBST_ALL_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[valid_lptree_mkNd; real_fringe_mkNd]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  FIRST_X_ASSUM(MP_TAC o check (PARSE3AUX_is_grule_fact o concl)) THEN
  USE_THEN "rules" (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; pegComplete_MAP_EQ_CONS; MAP_EQ_NIL] THEN
  STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    is_var(lhs(concl th)) && type_of(lhs(concl th)) = `:(mlptree)list`))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MEM; DISJ_IMP_THM; FORALL_AND_THM; FORALL_UNWIND_THM2]) THEN
  PARSE3AUX_FRINGE_SPLIT_TAC THENL
   [(* P -> P SEP C *)
    FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)) THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)) THEN
  MP_TAC(ISPECL [`cmlG`; `INL P:MMLnonT+num`; `ptree_head (h0':mlptree)`;
                 `ptree_head (h0'':mlptree)`; `h0:mlptree`; `h0':mlptree`; `h0'':mlptree`;
                 `m1:(token#locs)list`; `m1':(token#locs)list`; `m2':(token#locs)list`]
                lassoc_reassociated) THEN
  USE_THEN "rules" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `cpt':mlptree` (X_CHOOSE_THEN `spt':mlptree`
    (X_CHOOSE_THEN `ppt':mlptree` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(MP_TAC o SYM o check (fun th -> is_eq(concl th) &&
     (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "APPEND"
      with Failure _ -> false))) THEN
  REWRITE_TAC[LPARSEAUX_MAP_EQ_APPEND] THEN
  DISCH_THEN(X_CHOOSE_THEN `csf:(token#locs)list` (X_CHOOSE_THEN `pf:(token#locs)list`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC (ASSUME_TAC o SYM))))) THEN
  REWRITE_TAC[LPARSEAUX_MAP_EQ_APPEND] THEN
  DISCH_THEN(X_CHOOSE_THEN `cf:(token#locs)list` (X_CHOOSE_THEN `sf:(token#locs)list`
    (CONJUNCTS_THEN2 SUBST_ALL_TAC (CONJUNCTS_THEN (ASSUME_TAC o SYM))))) THEN
    SUBGOAL_THEN `?st sl sf_r. sf = CONS (st:token,sl:locs) sf_r /\
                  st IN firstSet cmlG [ptree_head (h0':mlptree)]` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`cmlG`; `ptree_head (h0':mlptree)`] rfringe_length_not_nullable) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `spt':mlptree`) THEN
    ASM_REWRITE_TAC[LENGTH_MAP] THEN
    MP_TAC(ISPEC `sf:(token#locs)list` list_CASES) THEN
    DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC
      (X_CHOOSE_THEN `h:token#locs` (X_CHOOSE_THEN `t:(token#locs)list` SUBST_ALL_TAC))) THEN
    REWRITE_TAC[LENGTH; LT_REFL] THEN DISCH_TAC THEN
    MP_TAC(ISPEC `h:token#locs` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `st:token` (X_CHOOSE_THEN `sl:locs` SUBST_ALL_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`st:token`; `sl:locs`; `t:(token#locs)list`] THEN
    REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      try lhand(concl th) = `ptree_head (spt':mlptree)` with Failure _ -> false)) THEN
    MATCH_MP_TAC rfirstSet_nonempty_fringe THEN
    MAP_EVERY EXISTS_TAC [`sl:locs`; `MAP ((TOK:token->(token,MMLnonT)symbol) ## (I:locs->locs)) t`] THEN
    ASM_REWRITE_TAC[MAP; PAIR_MAP_THM; I_THM];
    ALL_TAC] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `~(cf:(token#locs)list = [])` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`cmlG`; `ptree_head (h0'':mlptree)`] rfringe_length_not_nullable) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `cpt':mlptree`) THEN
    ASM_REWRITE_TAC[LENGTH_MAP; GSYM LENGTH_EQ_NIL] THEN ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `IS_SUFFIX (master:(token#locs)list) (APPEND m1 (APPEND m1' m2'))` THEN
  REWRITE_TAC[APPEND_ASSOC] THEN ASM_REWRITE_TAC[LPARSEAUX_IS_SUFFIX_APPEND] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:(token#locs)list` ASSUME_TAC) THEN
  REWRITE_TAC[APPEND_ASSOC] THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN
    SUBGOAL_THEN `?eo. peg_eval cmlPEG
     (APPEND cf (CONS (st,sl) (APPEND sf_r (APPEND pf sfx))), sym2peg (ptree_head (cpt':mlptree)))
     (peg_Success (CONS (st,sl) (APPEND sf_r (APPEND pf sfx))) [cpt'] eo)`
    (X_CHOOSE_TAC `eoc:(locs#(char)list)option`) THENL
   [USE_THEN "ih1" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_CONS_NIL; HD; FST] THEN CONJ_TAC THENL
     [REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN
      UNDISCH_TAC `~(cf:(token#locs)list = [])` THEN
      REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN ARITH_TAC;
      X_GEN_TAC `n:MMLnonT` THEN DISCH_TAC THEN
      USE_THEN "c4" (MP_TAC o C MP (ASSUME `ptree_head (h0'':mlptree) = NT (INL n)`) o
                     SPEC `n:MMLnonT`) THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
    SUBGOAL_THEN `?eo. peg_eval cmlPEG
     (APPEND (CONS (st,sl) sf_r) (APPEND pf sfx), sym2peg (ptree_head (spt':mlptree)))
     (peg_Success (APPEND pf sfx) [spt'] eo)`
    (X_CHOOSE_TAC `eos:(locs#(char)list)option`) THENL
   [USE_THEN "ih1" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[IN_INSERT] THEN CONJ_TAC THENL
     [REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN
      UNDISCH_TAC `~(cf:(token#locs)list = [])` THEN
      REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN ARITH_TAC;
      X_GEN_TAC `n:MMLnonT` THEN STRIP_TAC THEN
      USE_THEN "c1" (MP_TAC o C MP (ASSUME `ptree_head (h0':mlptree) = NT (INL n)`) o
                     SPEC `INL n:MMLnonT+num`) THEN
      REWRITE_TAC[injectivity "sum"] THEN
      DISCH_THEN(X_CHOOSE_THEN `nn:MMLnonT` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[IN_UNIV]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?eo. peg_eval cmlPEG
     (APPEND pf sfx, peg_linfix (INL P) (sym2peg (ptree_head (h0'':mlptree)))
                       (sym2peg (ptree_head (h0':mlptree))))
     (peg_Success sfx [ppt'] eo)`
    (X_CHOOSE_TAC `eop:(locs#(char)list)option`) THENL
   [USE_THEN "ihn" (MP_TAC o SPEC `LENGTH (pf:(token#locs)list)`) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[APPEND_ASSOC] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[LPARSEAUX_IS_SUFFIX_APPEND] THEN
    EXISTS_TAC `APPEND q (APPEND cf (CONS (st:token,sl:locs) sf_r))` THEN
    REWRITE_TAC[APPEND_ASSOC];
    ALL_TAC] THEN
    MP_TAC(MATCH_MP PARSE3AUX_linfix_inv (ASSUME
     `peg_eval cmlPEG
      (APPEND pf sfx,
       peg_linfix (INL P) (sym2peg (ptree_head (h0'':mlptree)))
       (sym2peg (ptree_head (h0':mlptree))))
      (peg_Success sfx [ppt'] eop)`)) THEN
  REWRITE_TAC[NOT_CONS_NIL; CONS_11] THEN
  DISCH_THEN(X_CHOOSE_THEN `i2:(token#locs)list` (X_CHOOSE_THEN `a2:(mlptree)list`
    (X_CHOOSE_THEN `eo2:(locs#(char)list)option` (X_CHOOSE_THEN `l2:((mlptree)list)list`
      (X_CHOOSE_THEN `err2:locs#(char)list` STRIP_ASSUME_TAC))))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    try lhs(concl th) = `ppt':mlptree` with Failure _ -> false)) THEN
  MP_TAC(ISPECL [`ptree_head (h0'':mlptree)`; `APPEND pf sfx:(token#locs)list`;
                 `i2:(token#locs)list`; `a2:(mlptree)list`; `eo2:(locs#(char)list)option`]
                PARSE3AUX_sym2peg_single) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x2:mlptree` SUBST_ALL_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> try lhs(concl th) = `[x2:mlptree]` with Failure _ -> false)) THEN
  REWRITE_TAC[CONS_11] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> try rhs(concl th) = `h:mlptree` with Failure _ -> false)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> try rhs(concl th) = `t:(mlptree)list` with Failure _ -> false)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `ptree_head (spt':mlptree) = ptree_head (h0':mlptree)`;
                              ASSUME `ptree_head (cpt':mlptree) = ptree_head (h0'':mlptree)`]) THEN
  MP_TAC(ISPECL [`INL P:MMLnonT+num`; `sym2peg (ptree_head (h0'':mlptree)):(token,MMLnonT,(mlptree)list,(char)list)pegsym`;
                 `sym2peg (ptree_head (h0':mlptree)):(token,MMLnonT,(mlptree)list,(char)list)pegsym`;
                 `APPEND cf (CONS (st:token,sl:locs) (APPEND sf_r (APPEND pf sfx)))`;
                 `CONS (st:token,sl:locs) (APPEND sf_r (APPEND pf sfx))`;
                 `sfx:(token#locs)list`; `cpt':mlptree`; `eoc:(locs#(char)list)option`;
                 `CONS (APPEND [spt'] [x2:mlptree]) l2`; `err2:locs#(char)list`]
                PARSE3AUX_linfix_intro) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC peg_eval_list_cons THEN
    MAP_EVERY EXISTS_TAC [`eo2:(locs#(char)list)option`; `i2:(token#locs)list`] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC peg_eval_seq_success THEN
    MAP_EVERY EXISTS_TAC [`APPEND pf sfx:(token#locs)list`;
                          `eos:(locs#(char)list)option`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[APPEND]) THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[APPEND] THEN
    REWRITE_TAC[left_insert_mk_linfix; left_insert_mkNd; FLAT; APPEND; mk_linfix_def]];
    (* P -> C *)
    SUBGOAL_THEN `?eo. peg_eval cmlPEG (APPEND pfx sfx, sym2peg (ptree_head (h0:mlptree)))
                       (peg_Success sfx [h0] eo)` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`master:(token#locs)list`; `pfx:(token#locs)list`]
                  LPARSEAUX_IS_SUFFIX_APPEND) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:(token#locs)list` SUBST_ALL_TAC) THEN
    SUBGOAL_THEN `!n. ptree_head (h0:mlptree) = NT (INL n) /\ ~(sfx:(token#locs)list = []) ==>
                      FST (HD sfx) IN stoppers n` ASSUME_TAC THENL
     [X_GEN_TAC `n:MMLnonT` THEN STRIP_TAC THEN
      USE_THEN "c4" (MP_TAC o C MP (ASSUME `ptree_head (h0:mlptree) = NT (INL n)`) o
                     SPEC `n:MMLnonT`) THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `p:(token#locs)list = []` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[APPEND]) THEN
      USE_THEN "ihC" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      USE_THEN "ih1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INSERT] THEN
      REWRITE_TAC[LENGTH_APPEND] THEN
      UNDISCH_TAC `~(p:(token#locs)list = [])` THEN
      REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`SEP:(token,MMLnonT)symbol`; `P:MMLnonT`; `sfx:(token#locs)list`]
                PARSE3AUX_SEP_fail) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `fl:locs` (X_CHOOSE_TAC `fe:(char)list`)) THEN
  MP_TAC(ISPECL [`INL P:MMLnonT+num`;
                 `sym2peg (ptree_head (h0:mlptree)):(token,MMLnonT,(mlptree)list,(char)list)pegsym`;
                 `sym2peg (SEP:(token,MMLnonT)symbol):(token,MMLnonT,(mlptree)list,(char)list)pegsym`;
                 `APPEND pfx sfx:(token#locs)list`; `sfx:(token#locs)list`;
                 `sfx:(token#locs)list`; `h0:mlptree`; `eo:(locs#(char)list)option`;
                 `[]:((mlptree)list)list`; `(fl:locs,fe:(char)list)`]
                PARSE3AUX_linfix_intro) THEN
  REWRITE_TAC[FLAT; mk_linfix_def] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC peg_eval_list_nil THEN
  MATCH_MP_TAC peg_eval_seq_fail1 THEN ASM_REWRITE_TAC[]]);;

let pmap_EQ = prove
 (`!(x:C) (y:D) (f:A->C) (g:B->D) p.
     (x,y) = (f ## g) p <=> ?x0 y0. p = (x0,y0) /\ x = f x0 /\ y = g y0`,
  REWRITE_TAC[FORALL_PAIR_THM; PAIR_MAP_THM; PAIR_EQ] THEN MESON_TAC[]);;

let _ = cake_add_simps [pmap_EQ];;

let ptPapply0_FOLDL = prove
 (`!l (a:(A,MMLnonT,locs)parsetree) pt.
     ptPapply0 a (APPEND l [pt]) =
     [bindNT0 nPapp [FOLDL (\pcpt bpt. bindNT0 nPConApp [pcpt; bpt]) a l; pt]]`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND; ptPapply0_def; FOLDL; bindNT_def] THEN
  POP_ASSUM MP_TAC THEN
  MP_TAC(ISPEC `t:((A,MMLnonT,locs)parsetree)list` list_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC
    (X_CHOOSE_THEN `h':(A,MMLnonT,locs)parsetree`
      (X_CHOOSE_THEN `t':((A,MMLnonT,locs)parsetree)list` SUBST_ALL_TAC))) THEN
  REWRITE_TAC[APPEND; ptPapply0_def; FOLDL; bindNT_def] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[]);;

let FST_EQ = prove
 (`!(p:A#B) x. FST p = x <=> ?y. p = (x,y)`,
  REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ] THEN MESON_TAC[]);;

let _ = cake_add_simps [FST_EQ];;

let FST_NEQ = prove
 (`!(p:A#B) x. ~(FST p = x) <=> ?x0 y. p = (x0,y) /\ ~(x0 = x)`,
  REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ] THEN MESON_TAC[]);;

let _ = cake_add_simps [FST_NEQ];;

let ALL_FST_NEQ = prove
 (`!(p:A#B) x. (!y. ~(p = (x,y))) <=> ?x0 y. p = (x0,y) /\ ~(x0 = x)`,
  REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ] THEN MESON_TAC[]);;

let _ = cake_add_simps [ALL_FST_NEQ];;

let FST_IN = prove
 (`!(p:A#B) s. FST p IN s <=> ?tk l. p = (tk,l) /\ tk IN s`,
  REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ] THEN MESON_TAC[]);;

let FST_NOTIN = prove
 (`!(p:A#B) s. ~(FST p IN s) <=> ?tk l. p = (tk,l) /\ ~(tk IN s)`,
  REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ] THEN MESON_TAC[]);;

(* a token leaf is parsed by tokeq *)
let PARSE3AUX_tok_leaf = prove
 (`!(pt:mlptree) t pfx0 sfx.
     ptree_head pt = TOK t /\ real_fringe pt = MAP (TOK ## I) pfx0 ==>
     ?eo. peg_eval cmlPEG (APPEND pfx0 sfx, tokeq t) (peg_Success sfx [pt] eo)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ptree_head_eq_tok0] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `pt:mlptree`)) THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[real_fringe_def] THEN
  GEN_REWRITE_TAC LAND_CONV [EQ_SYM_EQ] THEN
  REWRITE_TAC[pegComplete_MAP_EQ_CONS; MAP_EQ_NIL; PARSE3AUX_PAIR_MAP_TKI_EQ] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[APPEND] THEN
  EXISTS_TAC `NONE:(locs#(char)list)option` THEN
  REWRITE_TAC[tokeq_def; peg_eval_tok_SOME; mktokLf_def] THEN
  MAP_EVERY EXISTS_TAC [`t:token`; `l:locs`] THEN REWRITE_TAC[FST; SND]);;

(* the side conditions of peg_linfix_complete about tokens: decided on a  *)
(* fresh token variable                                                     *)
let PARSE3AUX_TOKIMP_TAC : tactic =
  X_GEN_TAC `PARSE3AUX_x:token` THEN DISCH_TAC THEN PARSE3AUX_DECIDE_GOAL_TAC;;

(* the side conditions of peg_linfix_complete, by their shape *)
let PARSE3AUX_LINFIX_SIDE_TAC : tactic = fun (asl,w as g) ->
  let is_c c = try fst(dest_const(fst(strip_comb c))) with Failure _ -> "" in
  let body = snd(strip_forall w) in
  if is_eq w && is_c (lhs w) = "FAPPLY" then
    (REWRITE_TAC[cmlG_applied; EXTENSION; IN_INSERT; NOT_IN_EMPTY] THEN
     MESON_TAC[]) g
  else if is_neg w then
    (REWRITE_TAC(peg0_tokeq :: nullable_CONS_TOK ::
                 CONJUNCT1(CONJUNCT2(CONJUNCT2(ISPEC PARSE3AUX_CMLPEG_TM LPARSEAUX_peg0_clauses))) ::
                 PARSE3AUX_npeg0_ths @ PARSE3AUX_nonnull_ths) THEN NO_TAC) g
  else if is_imp body && is_exists (rand body) &&
          is_conj (snd(dest_exists(rand body))) then
    (* the separator is a non-terminal with all tokens as stoppers *)
    (GEN_TAC THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
     (fun (asl,w as g) ->
        let nn = rand(lhand(fst(dest_conj(snd(dest_exists w))))) in
        (EXISTS_TAC nn THEN REWRITE_TAC[NTS_in_PEG_exprs; stoppers_def]) g)) g
  else if is_imp body && is_conj (rand body) then
    (GEN_TAC THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN CONJ_TAC THEN
     PARSE3AUX_TOKIMP_TAC) g
  else if is_imp body && is_exists (rand body) then MESON_TAC[] g
  else if is_imp body && is_c (lhand body) = "IN" then PARSE3AUX_TOKIMP_TAC g
  else failwith "PARSE3AUX_LINFIX_SIDE_TAC";;

(* a completeness case of a non-terminal p whose rule is peg_linfix (INL p) *)
(* (sym2peg c) (sym2peg sep)                                                 *)
let PARSE3AUX_LINFIX_CASE_TAC (p:term) (sep:term) (c:term) : tactic =
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih") STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[peg_eval_NT_SOME; PARSE2AUX_rule p; FDOM_cmlPEG_nts; I_THM;
              cmlPEG_pnt_def] THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM; LEFT_EXISTS_AND_THM; UNWIND_THM1;
              UNWIND_THM2] THEN
  MP_TAC(ISPECL [`pfx:(token#locs)list`; sep; c; p] peg_linfix_complete) THEN
  REWRITE_TAC[sym2peg_def; symbol_distinct; symbol_inject; injectivity "sum"] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN
    FIRST
     [(* shorter fringes *)
      MAP_EVERY X_GEN_TAC [`pt:mlptree`; `pfx0:(token#locs)list`;
                           `sfx0:(token#locs)list`] THEN
      REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN STRIP_TAC THEN
      FIRST_ASSUM(SUBST1_TAC o check (fun th ->
        try lhand(concl th) = `ptree_head (pt:mlptree)` with Failure _ -> false)) THEN
      REWRITE_TAC[sym2peg_def] THEN
      (MATCH_MP_TAC PARSE3AUX_tok_leaf THEN ASM_REWRITE_TAC[] ORELSE
       (USE_THEN "ih" MATCH_MP_TAC THEN ASM_REWRITE_TAC[FDOM_cmlPEG_nts] THEN
        DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]));
      (* the same fringe, a smaller rank *)
      MAP_EVERY X_GEN_TAC [`pt:mlptree`; `sfx0:(token#locs)list`] THEN
      STRIP_TAC THEN USE_THEN "ih" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[FDOM_cmlPEG_nts] THEN CONJ_TAC THENL
       [DISJ2_TAC THEN PARSE3AUX_RANK_TAC;
        DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      PARSE3AUX_LINFIX_SIDE_TAC];
    DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[ptree_head_mkNd; IS_SUFFIX_REFL]];;

(* a completeness case by eapp_complete or dtype_complete (master := pfx) *)
let PARSE3AUX_LEMMA_CASE_TAC (lemma:thm) : tactic =
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih") STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC `pfx:(token#locs)list` lemma) THEN ANTS_TAC THENL
   [CONJ_TAC THEN REPEAT STRIP_TAC THEN USE_THEN "ih" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[FDOM_cmlPEG_nts] THEN REPEAT CONJ_TAC THEN
    TRY(DISJ2_TAC THEN PARSE3AUX_RANK_TAC) THEN
    TRY(UNDISCH_TAC `~(sfx':(token#locs)list = []) ==> FST (HD sfx') IN stoppers nEbase` THEN
        REWRITE_TAC[stoppers_def; IN_UNIV]);
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[ptree_head_mkNd; IS_SUFFIX_REFL]];;

(* replace the assumptions by clean ones (hypotheses equal to the          *)
(* conclusions), keeping the labels: STRIP_TAC chooses names that avoid the *)
(* conclusions of the assumptions only                                      *)
let PARSE3AUX_CLEAN_HYPS_TAC : tactic = fun (asl,w as g) ->
  let labs = map fst asl in
  (MAP_EVERY (fun (_,th) -> UNDISCH_TAC (concl th)) asl THEN
   MAP_EVERY (fun l -> DISCH_THEN (LABEL_TAC l)) (rev labs)) g;;

(* expand the subtree x of head NT (INL y) one level: x becomes            *)
(* mkNd (INL y) subs for the rules of y, with the facts of its subtrees     *)
let PARSE3AUX_EXPAND_TAC (y:term) : tactic = fun (asl,w as g) ->
  let hdt = mk_comb(PARSE3AUX_NT_TM, mk_comb(PARSE3AUX_INL_TM, y)) in
  let _,hd_th = find (fun (_,th) -> let c = concl th in is_eq c && rhs c = hdt &&
                        (try fst(dest_const(rator(lhs c))) = "ptree_head" with Failure _ -> false) &&
                        is_var(rand(lhs c))) asl in
  let x = rand(lhs(concl hd_th)) in
  let _,fr_th = find (fun (_,th) -> let c = concl th in is_eq c &&
                        lhs c = mk_comb(PARSE3AUX_REAL_FRINGE_TM, x)) asl in
  let _,vl_th = find (fun (_,th) -> concl th = mk_comb(PARSE3AUX_VALID_TM, x)) asl in
  let avoid = itlist (fun (_,th) l -> union (thm_frees th) l) asl (frees w) in
  let subs = variant avoid (mk_var("PARSE3AUX_subs", `:(mlptree)list`)) in
  (MP_TAC (MATCH_MP ptree_head_NT_mkNd (CONJ hd_th (CONJ vl_th fr_th))) THEN
   DISCH_THEN(X_CHOOSE_THEN subs SUBST_ALL_TAC) THEN
   (fun (asl,w as g) ->
      let nd = mk_comb(mk_comb(`mkNd:MMLnonT+num->(mlptree)list->mlptree`,
                               mk_comb(PARSE3AUX_INL_TM, y)), subs) in
      let _,fr = find (fun (_,th) -> let c = concl th in is_eq c &&
                   lhs c = mk_comb(PARSE3AUX_REAL_FRINGE_TM, nd)) asl in
      let _,vl = find (fun (_,th) -> concl th = mk_comb(PARSE3AUX_VALID_TM, nd)) asl in
      (MP_TAC (SYM (REWRITE_RULE[real_fringe_mkNd] fr)) THEN
       MP_TAC (REWRITE_RULE[valid_lptree_mkNd] vl) THEN
       DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
       PARSE3AUX_CLEAN_HYPS_TAC THEN PARSE3AUX_GRULE_CASES_TAC THEN
       RULE_ASSUM_TAC(REWRITE_RULE[ptree_head_eq_tok]) THEN
       REPEAT(FIRST_X_ASSUM(CHOOSE_THEN SUBST_ALL_TAC o check (is_exists o concl))) THEN
       RULE_ASSUM_TAC(REWRITE_RULE[MEM; DISJ_IMP_THM; FORALL_AND_THM; FORALL_UNWIND_THM2;
                                   valid_lptree_thm]) THEN
       REWRITE_TAC[MAP; FLAT; APPEND; APPEND_NIL; real_fringe_def] THEN
       REWRITE_TAC[pegComplete_MAP_EQ_CONS; MAP_EQ_NIL; LPARSEAUX_MAP_EQ_APPEND;
                   PARSE3AUX_PAIR_MAP_TKI_EQ] THEN
       DISCH_THEN(CAKE_STRIP_ASSUME_TAC) THEN RVEQ_TAC THEN
       RULE_ASSUM_TAC(fun th -> if PARSE3AUX_is_map_fact (concl th) then th
                     else if is_eq(concl th) &&
                             PARSE3AUX_is_map_fact (mk_eq(rand(concl th), lhand(concl th)))
                          then SYM th else th)) g)) g;;

(* the uniform case tactic, expanding first the subtrees of the given heads *)
let PARSE3AUX_CCASE_X_TAC (ys:term list) : tactic =
  PARSE3AUX_CSTART_TAC THEN PARSE3AUX_SPLIT_CONJ_ASM_TAC THEN
  PARSE3AUX_SKOLEM_IH_TAC THEN
  MAP_EVERY (fun y -> TRY (PARSE3AUX_EXPAND_TAC y)) ys THEN
  PARSE3AUX_SPLIT_CONJ_ASM_TAC THEN PARSE3AUX_DESTRUCT_TAC THEN
  TRY(PARSE3AUX_EVAL_TAC ORELSE
      (PARSE3AUX_SFX_SPLIT_TAC THEN
       (PARSE3AUX_MEM_CONTR_TAC ORELSE PARSE3AUX_EVAL_TAC)));;

let PARSE3AUX_case_APPEND_SING = prove
 (CASE_TERM `!(l:A list) x (d:B) p.
     (match APPEND l [x] with [] -> d | CONS a b -> p) = p`,
  GEN_TAC THEN MP_TAC(ISPEC `l:A list` list_CASES) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[APPEND] THEN CASE_REWRITE_TAC[]);;

let PARSE3AUX_ptPapply_APPEND = prove
 (`!(c:(A,MMLnonT,locs)parsetree) l x.
     ptPapply (CONS c (APPEND l [x])) =
     ptPapply0 (bindNT0 nPConApp [c]) (APPEND l [x])`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND; ptPapply_def]);;

(* the evaluation of the linfix subtree of head NT (INL p) of a completeness *)
(* case, by peg_linfix_complete with master := its fringe, as an assumption  *)
let PARSE3AUX_LINFIX_SUB_TAC (p:term) (sep:term) (c:term) : tactic = fun (asl,w as g) ->
  let hdt = mk_comb(PARSE3AUX_NT_TM, mk_comb(PARSE3AUX_INL_TM, p)) in
  let _,hd_th = find (fun (_,th) -> let c = concl th in is_eq c && rhs c = hdt &&
                        (try fst(dest_const(rator(lhs c))) = "ptree_head" with Failure _ -> false)) asl in
  let x = rand(lhs(concl hd_th)) in
  let _,fr_th = find (fun (_,th) -> let c = concl th in is_eq c &&
                        lhs c = mk_comb(PARSE3AUX_REAL_FRINGE_TM, x)) asl in
  let m = rand(rand(concl fr_th)) in
  let _,ev = dest_exists w in
  let sfx = rand(rator(rator(rand ev))) in
  let lf = list_mk_comb(`peg_linfix:MMLnonT+num->(token,MMLnonT,(mlptree)list,(char)list)pegsym->(token,MMLnonT,(mlptree)list,(char)list)pegsym->(token,MMLnonT,(mlptree)list,(char)list)pegsym`,
             [mk_comb(PARSE3AUX_INL_TM, p);
              mk_comb(`sym2peg:(token,MMLnonT)symbol->(token,MMLnonT,(mlptree)list,(char)list)pegsym`, c);
              mk_comb(`sym2peg:(token,MMLnonT)symbol->(token,MMLnonT,(mlptree)list,(char)list)pegsym`, sep)]) in
  let lf' = rhs(concl(REWRITE_CONV[sym2peg_def; tokeq_def] lf)) in
  let eov = mk_var("eo", `:(locs#(char)list)option`) in
  let fact = mk_exists(eov, list_mk_comb(`peg_eval:(token,MMLnonT,(mlptree)list,(char)list)peg->(token#locs)list#(token,MMLnonT,(mlptree)list,(char)list)pegsym->((token#locs)list,(mlptree)list,(char)list)pegresult->bool`,
               [PARSE3AUX_CMLPEG_TM;
                mk_pair(mk_comb(mk_comb(PARSE3AUX_APPEND_TM, m), sfx), lf');
                list_mk_comb(`peg_Success:(token#locs)list->(mlptree)list->(locs#(char)list)option->((token#locs)list,(mlptree)list,(char)list)pegresult`,
                             [sfx; mk_list([x], PARSE3AUX_mlptree_ty); eov])])) in
  let avoid = itlist (fun (_,th) l -> union (thm_frees th) l) asl (frees w) in
  let eo' = variant avoid (mk_var("PARSE3AUX_eo", `:(locs#(char)list)option`)) in
  (SUBGOAL_THEN fact (X_CHOOSE_TAC eo') THENL
    [MP_TAC(ISPECL [m; sep; c; p] peg_linfix_complete) THEN
     REWRITE_TAC[sym2peg_def; symbol_distinct; symbol_inject; injectivity "sum"] THEN
     REWRITE_TAC[tokeq_def] THEN
     ANTS_TAC THENL
      [REPEAT CONJ_TAC THEN
       FIRST
        [(* shorter fringes *)
         MAP_EVERY X_GEN_TAC [`pt:mlptree`; `pfx0:(token#locs)list`;
                              `sfx0:(token#locs)list`] THEN
         REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN STRIP_TAC THEN
         FIRST_ASSUM(SUBST1_TAC o check (fun th ->
           try lhand(concl th) = `ptree_head (pt:mlptree)` with Failure _ -> false)) THEN
         REWRITE_TAC[sym2peg_def] THEN
         ((MATCH_MP_TAC PARSE3AUX_tok_leaf ORELSE
           MATCH_MP_TAC (REWRITE_RULE[tokeq_def] PARSE3AUX_tok_leaf)) THEN
          ASM_REWRITE_TAC[] ORELSE
          (USE_THEN "ih" MATCH_MP_TAC THEN ASM_REWRITE_TAC[FDOM_cmlPEG_nts] THEN
           CONJ_TAC THENL
            [DISJ1_TAC THEN PARSE3AUX_CLEN_TAC;
             DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]));
         (* the whole fringe of the subtree *)
         MAP_EVERY X_GEN_TAC [`pt:mlptree`; `sfx0:(token#locs)list`] THEN
         STRIP_TAC THEN USE_THEN "ih" MATCH_MP_TAC THEN
         ASM_REWRITE_TAC[FDOM_cmlPEG_nts] THEN CONJ_TAC THENL
          [DISJ1_TAC THEN PARSE3AUX_CLEN_TAC;
           DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
         PARSE3AUX_LINFIX_SIDE_TAC];
       DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[IS_SUFFIX_REFL] THEN
       PARSE3AUX_STOPPERS_TAC];
     ALL_TAC]) g;;

(* ------------------------------------------------------------------------- *)
(* The cases of the completeness theorem, one lemma per non-terminal of the *)
(* domain of cmlPEG (HOL4: the 75 subgoals of completeness, nREPLTop        *)
(* commented out there)                                                     *)
(* ------------------------------------------------------------------------- *)

let PARSE3AUX_complete_nV = prove
 (PARSE3AUX_complete_goal "nV", PARSE3AUX_CCASE_TAC);;

let PARSE3AUX_complete_nUQTyOp = prove
 (PARSE3AUX_complete_goal "nUQTyOp", PARSE3AUX_CCASE_TAC);;

let PARSE3AUX_complete_nUQConstructorName = prove
 (PARSE3AUX_complete_goal "nUQConstructorName", PARSE3AUX_CCASE_TAC);;

let PARSE3AUX_complete_nTyvarN = prove
 (PARSE3AUX_complete_goal "nTyvarN", PARSE3AUX_CCASE_TAC);;

let PARSE3AUX_complete_nTypeName = prove
 (PARSE3AUX_complete_goal "nTypeName", PARSE3AUX_CCASE_TAC);;

let PARSE3AUX_complete_nTypeAbbrevDec = prove
 (PARSE3AUX_complete_goal "nTypeAbbrevDec", PARSE3AUX_CCASE_TAC);;

let PARSE3AUX_complete_nType = prove
 (PARSE3AUX_complete_goal "nType", PARSE3AUX_CCASE_TAC);;

let PARSE3AUX_complete_nTyOp = prove
 (PARSE3AUX_complete_goal "nTyOp", PARSE3AUX_CCASE_TAC);;

let PARSE3AUX_complete_nStructure = prove
 (PARSE3AUX_complete_goal "nStructure", PARSE3AUX_CCASE_TAC);;

let PARSE3AUX_complete_nStructName = prove
 (PARSE3AUX_complete_goal "nStructName", PARSE3AUX_CCASE_TAC);;

let PARSE3AUX_complete_nSignatureValue = prove
 (PARSE3AUX_complete_goal "nSignatureValue", PARSE3AUX_CCASE_TAC);;

let PARSE3AUX_complete_nRelOps = prove
 (PARSE3AUX_complete_goal "nRelOps", PARSE3AUX_CCASE_TAC);;

let PARSE3AUX_complete_nPtuple = prove
 (PARSE3AUX_complete_goal "nPtuple", PARSE3AUX_CCASE_TAC);;

let PARSE3AUX_complete_nPType = prove
 (PARSE3AUX_complete_goal "nPType", PARSE3AUX_CCASE_TAC);;

let PARSE3AUX_complete_nPTbase = prove
 (PARSE3AUX_complete_goal "nPTbase", PARSE3AUX_CCASE_TAC);;

let PARSE3AUX_complete_nPEsfx = prove
 (PARSE3AUX_complete_goal "nPEsfx", PARSE3AUX_CCASE_TAC);;

let PARSE3AUX_complete_nPEs = prove
 (PARSE3AUX_complete_goal "nPEs", PARSE3AUX_CCASE_TAC);;

let PARSE3AUX_complete_nOptionalSignatureAscription = prove
 (PARSE3AUX_complete_goal "nOptionalSignatureAscription", PARSE3AUX_CCASE_TAC);;

let PARSE3AUX_complete_nOptTypEqn = prove
 (PARSE3AUX_complete_goal "nOptTypEqn", PARSE3AUX_CCASE_TAC);;

let PARSE3AUX_complete_nOpID = prove
 (PARSE3AUX_complete_goal "nOpID", PARSE3AUX_CCASE_TAC);;

let PARSE3AUX_complete_nMultOps = prove
 (PARSE3AUX_complete_goal "nMultOps", PARSE3AUX_CCASE_TAC);;

let PARSE3AUX_complete_nListOps = prove
 (PARSE3AUX_complete_goal "nListOps", PARSE3AUX_CCASE_TAC);;

let PARSE3AUX_complete_nLetDec = prove
 (PARSE3AUX_complete_goal "nLetDec", PARSE3AUX_CCASE_TAC);;

let PARSE3AUX_complete_nFQV = prove
 (PARSE3AUX_complete_goal "nFQV", PARSE3AUX_CCASE_TAC);;

let PARSE3AUX_complete_nFDecl = prove
 (PARSE3AUX_complete_goal "nFDecl", PARSE3AUX_CCASE_TAC);;

let PARSE3AUX_complete_nEtyped = prove
 (PARSE3AUX_complete_goal "nEtyped", PARSE3AUX_CCASE_TAC);;

let PARSE3AUX_complete_nEseq = prove
 (PARSE3AUX_complete_goal "nEseq", PARSE3AUX_CCASE_TAC);;

let PARSE3AUX_complete_nEliteral = prove
 (PARSE3AUX_complete_goal "nEliteral", PARSE3AUX_CCASE_TAC);;

let PARSE3AUX_complete_nEhandle = prove
 (PARSE3AUX_complete_goal "nEhandle", PARSE3AUX_CCASE_TAC);;

let PARSE3AUX_complete_nE = prove
 (PARSE3AUX_complete_goal "nE", PARSE3AUX_CCASE_TAC);;

let PARSE3AUX_complete_nConstructorName = prove
 (PARSE3AUX_complete_goal "nConstructorName", PARSE3AUX_CCASE_TAC);;

let PARSE3AUX_complete_nCompOps = prove
 (PARSE3AUX_complete_goal "nCompOps", PARSE3AUX_CCASE_TAC);;

let PARSE3AUX_complete_nAddOps = prove
 (PARSE3AUX_complete_goal "nAddOps", PARSE3AUX_CCASE_TAC);;

let PARSE3AUX_complete_nTypeList2 = prove
 (PARSE3AUX_complete_goal "nTypeList2", PARSE3AUX_CCASE_TAC);;

let PARSE3AUX_complete_nTypeList1 = prove
 (PARSE3AUX_complete_goal "nTypeList1", PARSE3AUX_CCASE_TAC);;

let PARSE3AUX_complete_nPbaseList1 = prove
 (PARSE3AUX_complete_goal "nPbaseList1", PARSE3AUX_CCASE_TAC);;

let PARSE3AUX_complete_nElist1 = prove
 (PARSE3AUX_complete_goal "nElist1", PARSE3AUX_CCASE_TAC);;

let PARSE3AUX_complete_nSpecLine = prove
 (PARSE3AUX_complete_goal "nSpecLine", PARSE3AUX_CCASE_TAC);;

let PARSE3AUX_complete_nPatternList = prove
 (PARSE3AUX_complete_goal "nPatternList", PARSE3AUX_CCASE_TAC);;

let PARSE3AUX_complete_nPattern = prove
 (PARSE3AUX_complete_goal "nPattern", PARSE3AUX_CCASE_TAC);;

let PARSE3AUX_complete_nDecl = prove
 (PARSE3AUX_complete_goal "nDecl", PARSE3AUX_CCASE_TAC);;

let PARSE3AUX_complete_nTbaseList = prove
 (PARSE3AUX_complete_goal "nTbaseList", PARSE3AUX_CCASE_TAC);;

let PARSE3AUX_complete_nDconstructor = prove
 (PARSE3AUX_complete_goal "nDconstructor", PARSE3AUX_CCASE_TAC);;

let PARSE3AUX_complete_nSpecLineList = prove
 (PARSE3AUX_complete_goal "nSpecLineList", PARSE3AUX_CCASE_TAC);;

let PARSE3AUX_complete_nLetDecs = prove
 (PARSE3AUX_complete_goal "nLetDecs", PARSE3AUX_CCASE_TAC);;

let PARSE3AUX_complete_nDecls = prove
 (PARSE3AUX_complete_goal "nDecls", PARSE3AUX_CCASE_TAC);;

let PARSE3AUX_complete_nPcons = prove
 (PARSE3AUX_complete_goal "nPcons", PARSE3AUX_CCASE_TAC);;

let PARSE3AUX_complete_nElistop = prove
 (PARSE3AUX_complete_goal "nElistop", PARSE3AUX_CCASE_TAC);;

let PARSE3AUX_complete_nPbase = prove
 (PARSE3AUX_complete_goal "nPbase", PARSE3AUX_CCASE_TAC);;

let PARSE3AUX_complete_nPE = prove
 (PARSE3AUX_complete_goal "nPE", PARSE3AUX_CCASE_TAC);;

let PARSE3AUX_complete_nTopLevelDecs = prove
 (PARSE3AUX_complete_goal "nTopLevelDecs", PARSE3AUX_CCASE_TAC);;

let PARSE3AUX_complete_nNonETopLevelDecs = prove
 (PARSE3AUX_complete_goal "nNonETopLevelDecs", PARSE3AUX_CCASE_TAC);;

let PARSE3AUX_complete_nTbase = prove
 (PARSE3AUX_complete_goal "nTbase", PARSE3AUX_CCASE_X_TAC [`nTypeList2`]);;

let PARSE3AUX_complete_nEbase = prove
 (PARSE3AUX_complete_goal "nEbase",
  PARSE3AUX_CCASE_X_TAC [`nEtuple`; `nEseq`; `nElist2`]);;

let PARSE3AUX_complete_nErel = prove
 (PARSE3AUX_complete_goal "nErel",
  PARSE3AUX_LINFIX_CASE_TAC `nErel` `NT (INL nRelOps):(token,MMLnonT)symbol`
                            `NT (INL nElistop):(token,MMLnonT)symbol`);;

let PARSE3AUX_complete_nEmult = prove
 (PARSE3AUX_complete_goal "nEmult",
  PARSE3AUX_LINFIX_CASE_TAC `nEmult` `NT (INL nMultOps):(token,MMLnonT)symbol`
                            `NT (INL nEapp):(token,MMLnonT)symbol`);;

let PARSE3AUX_complete_nElogicOR = prove
 (PARSE3AUX_complete_goal "nElogicOR",
  PARSE3AUX_LINFIX_CASE_TAC `nElogicOR` `TOK OrelseT:(token,MMLnonT)symbol`
                            `NT (INL nElogicAND):(token,MMLnonT)symbol`);;

let PARSE3AUX_complete_nElogicAND = prove
 (PARSE3AUX_complete_goal "nElogicAND",
  PARSE3AUX_LINFIX_CASE_TAC `nElogicAND` `TOK AndalsoT:(token,MMLnonT)symbol`
                            `NT (INL nEtyped):(token,MMLnonT)symbol`);;

let PARSE3AUX_complete_nEcomp = prove
 (PARSE3AUX_complete_goal "nEcomp",
  PARSE3AUX_LINFIX_CASE_TAC `nEcomp` `NT (INL nCompOps):(token,MMLnonT)symbol`
                            `NT (INL nErel):(token,MMLnonT)symbol`);;

let PARSE3AUX_complete_nEbefore = prove
 (PARSE3AUX_complete_goal "nEbefore",
  PARSE3AUX_LINFIX_CASE_TAC `nEbefore` `TOK (AlphaT (implode "before")):(token,MMLnonT)symbol`
                            `NT (INL nEcomp):(token,MMLnonT)symbol`);;

let PARSE3AUX_complete_nEadd = prove
 (PARSE3AUX_complete_goal "nEadd",
  PARSE3AUX_LINFIX_CASE_TAC `nEadd` `NT (INL nAddOps):(token,MMLnonT)symbol`
                            `NT (INL nEmult):(token,MMLnonT)symbol`);;

let PARSE3AUX_complete_nTyVarList = prove
 (PARSE3AUX_complete_goal "nTyVarList",
  PARSE3AUX_LINFIX_CASE_TAC `nTyVarList` `TOK CommaT:(token,MMLnonT)symbol`
                            `NT (INL nTyvarN):(token,MMLnonT)symbol`);;

let PARSE3AUX_complete_nAndFDecls = prove
 (PARSE3AUX_complete_goal "nAndFDecls",
  PARSE3AUX_LINFIX_CASE_TAC `nAndFDecls` `TOK AndT:(token,MMLnonT)symbol`
                            `NT (INL nFDecl):(token,MMLnonT)symbol`);;

let PARSE3AUX_complete_nEapp = prove
 (PARSE3AUX_complete_goal "nEapp", PARSE3AUX_LEMMA_CASE_TAC eapp_complete);;

let PARSE3AUX_complete_nDType = prove
 (PARSE3AUX_complete_goal "nDType", PARSE3AUX_LEMMA_CASE_TAC dtype_complete);;

let PARSE3AUX_complete_nPas = prove
 (PARSE3AUX_complete_goal "nPas",
  PARSE3AUX_CSTART_TAC THEN PARSE3AUX_SPLIT_CONJ_ASM_TAC THEN
  PARSE3AUX_SKOLEM_IH_TAC THEN PARSE3AUX_DESTRUCT_TAC THEN TRY PARSE3AUX_EVAL_TAC THEN
  (* the case Pas ::= Pcons: V on the input fails, or succeeds without AsT *)
  MP_TAC(MP (ISPECL [`APPEND (CONS (pfx_t:token,pfx_l:locs) pfx_r) sfx`;
                     `peg_nt (INL nV) I:(token,MMLnonT,(mlptree)list,(char)list)pegsym`]
                    PARSE3AUX_cmlPEG_total) (PARSE3AUX_NTS_GEXPRS `peg_nt (INL nV) I:(token,MMLnonT,(mlptree)list,(char)list)pegsym`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `rv:((token#locs)list,(mlptree)list,(char)list)pegresult` MP_TAC) THEN
  STRUCT_CASES_TAC(ISPEC `rv:((token#locs)list,(mlptree)list,(char)list)pegresult` pegresult_nchotomy) THEN
  DISCH_TAC THENL
   [MP_TAC(ISPEC `a0:(token#locs)list` list_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC
    (X_CHOOSE_THEN `vh:token#locs` (X_CHOOSE_THEN `vt:(token#locs)list` SUBST_ALL_TAC))) THENL
   [PARSE3AUX_SFX_SPLIT_TAC THEN PARSE3AUX_EVAL_TAC; ALL_TAC] THEN
  MP_TAC(ISPEC `vh:token#locs` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `vtk:token` (X_CHOOSE_THEN `vl:locs` SUBST_ALL_TAC)) THEN
  ASM_CASES_TAC `AsT = vtk` THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP Pattern_nV_nCons o C CONJ
      (TAC_PROOF(([], `~(CONS (AsT,vl:locs) vt = []) ==> FST (HD (CONS (AsT,vl) vt)) IN stoppers nPcons`),
                 REWRITE_TAC[NOT_CONS_NIL; HD; FST] THEN CONV_TAC PARSE3AUX_DECIDE_CONV)) o
      check (fun th -> try rand(rand(rator(concl th))) = `peg_nt (INL nV) I:(token,MMLnonT,(mlptree)list,(char)list)pegsym` with Failure _ -> false)) THEN
    DISCH_THEN(X_CHOOSE_THEN `r1:(mlptree)list` (X_CHOOSE_TAC `eo1:(locs#(char)list)option`)) THEN
    USE_THEN "ihs" (MP_TAC o SPECL [`h0:mlptree`; `nPcons`;
                                    `CONS (pfx_t:token,pfx_l:locs) pfx_r`; `sfx:(token#locs)list`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[FDOM_cmlPEG_nts] THEN CONJ_TAC THENL
       [DISJ2_TAC THEN PARSE3AUX_RANK_TAC; PARSE3AUX_STOPPERS_TAC];
      ALL_TAC] THEN
    DISCH_THEN(fun th -> MP_TAC(PARSE3AUX_DET_RULE th (ASSUME
      `peg_eval cmlPEG (APPEND (CONS (pfx_t,pfx_l) pfx_r) sfx,peg_nt (INL nPcons) I)
                       (peg_Success (CONS (AsT,vl) vt) r1 eo1)`))) THEN
    REWRITE_TAC[pegresult_inject] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) &&
      can (find_term (fun t -> t = `stoppers nPas`)) (concl th))) THEN
    REWRITE_TAC[NOT_CONS_NIL; HD; FST] THEN CONV_TAC PARSE3AUX_DECIDE_CONV;
    PARSE3AUX_SFX_SPLIT_TAC THEN PARSE3AUX_EVAL_TAC];
    PARSE3AUX_SFX_SPLIT_TAC THEN PARSE3AUX_EVAL_TAC]);;

let PARSE3AUX_complete_nPapp = prove
 (PARSE3AUX_complete_goal "nPapp",
  PARSE3AUX_CSTART_TAC THEN PARSE3AUX_SPLIT_CONJ_ASM_TAC THEN PARSE3AUX_SKOLEM_IH_TAC THENL
   [(* Papp -> PConApp Pbase *)
    MP_TAC(SPEC `APPEND m1 m2:(token#locs)list` papp_complete) THEN ANTS_TAC THENL
   [CONJ_TAC THEN REPEAT STRIP_TAC THEN USE_THEN "ih" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[FDOM_cmlPEG_nts; stoppers_def; IN_UNIV] THEN
    DISJ2_TAC THEN PARSE3AUX_RANK_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`m1:(token#locs)list`; `h0:mlptree`; `[]:(token#locs)list`]) THEN
  ASM_REWRITE_TAC[NOT_CONS_NIL; IS_PREFIX_APPEND; APPEND_NIL] THEN
  ANTS_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `cpt:mlptree` (X_CHOOSE_THEN `i1:(token#locs)list`
    (X_CHOOSE_THEN `bpts:((mlptree)list)list` (X_CHOOSE_THEN `eoc:(locs#(char)list)option`
      (X_CHOOSE_THEN `e2:locs#(char)list` STRIP_ASSUME_TAC))))) THEN
    MP_TAC(ISPECL [`m1:(token#locs)list`; `i1:(token#locs)list`; `[cpt]:(mlptree)list`;
                 `eoc:(locs#(char)list)option`; `APPEND m2 sfx:(token#locs)list`]
                nConstructorName_input_monotone) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(MATCH_MP PARSE3AUX_FRINGE_CONS
     (CONJ (ASSUME `real_fringe (h0:mlptree) = MAP (TOK ## I) m1`)
     (CONJ (ASSUME `ptree_head (h0:mlptree) = NT (INL nPConApp)`)
     (CONJ (ASSUME `valid_lptree cmlG (h0:mlptree)`) nullable_PConApp)))) THEN
  DISCH_THEN(X_CHOOSE_THEN `ct:token` (X_CHOOSE_THEN `cl:locs`
    (X_CHOOSE_THEN `m1r:(token#locs)list` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)))) THEN
  SUBGOAL_THEN `peg_eval cmlPEG (APPEND m2 sfx, peg_nt (INL nPbase) I)
                  (peg_Success sfx [h0'] ((ihf:mlptree->MMLnonT->(token#locs)list->(token#locs)list->(locs#(char)list)option) h0' nPbase m2 sfx))` ASSUME_TAC THENL
   [USE_THEN "ihs" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[FDOM_cmlPEG_nts; stoppers_def; IN_UNIV] THEN
    REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`bpts:((mlptree)list)list`; `i1:(token#locs)list`;
                 `APPEND m2 sfx:(token#locs)list`; `sfx:(token#locs)list`;
                 `[h0']:(mlptree)list`; `e2:locs#(char)list`;
                 `(ihf:mlptree->MMLnonT->(token#locs)list->(token#locs)list->(locs#(char)list)option) h0' nPbase m2 sfx`] extend_Pbase_list) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [PARSE3AUX_HD_NOTIN_TAC `sfx:(token#locs)list`; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `e3:locs#(char)list`) THEN
    PARSE3AUX_EVAL_EQ_TAC THEN
    REWRITE_TAC[FLAT_APPEND; FLAT; APPEND_NIL; LENGTH_APPEND; LENGTH;
              ARITH_RULE `~(SUC (n + SUC 0) = 1)`] THEN
  CASE_REWRITE_TAC[PARSE3AUX_case_APPEND_SING] THEN
  REWRITE_TAC[PARSE3AUX_ptPapply_APPEND; ptPapply0_FOLDL; bindNT0_lemma];
    (* Papp -> Pbase *)
    PARSE3AUX_EXPAND_TAC `nPbase` THEN
  PARSE3AUX_SPLIT_CONJ_ASM_TAC THEN PARSE3AUX_DESTRUCT_TAC THEN
  (PARSE3AUX_EVAL_TAC ORELSE
   (PARSE3AUX_SFX_SPLIT_TAC THEN (PARSE3AUX_MEM_CONTR_TAC ORELSE PARSE3AUX_EVAL_TAC)))]);;

let PARSE3AUX_complete_nTypeDec = prove
 (PARSE3AUX_complete_goal "nTypeDec",
  PARSE3AUX_CSTART_TAC THEN PARSE3AUX_SPLIT_CONJ_ASM_TAC THEN PARSE3AUX_SKOLEM_IH_TAC THEN
  PARSE3AUX_LINFIX_SUB_TAC `nDtypeDecls` `TOK AndT:(token,MMLnonT)symbol`
                           `NT (INL nDtypeDecl):(token,MMLnonT)symbol` THEN
  PARSE3AUX_EVAL_TAC);;

let PARSE3AUX_complete_nDtypeDecl = prove
 (PARSE3AUX_complete_goal "nDtypeDecl",
  PARSE3AUX_CSTART_TAC THEN PARSE3AUX_SPLIT_CONJ_ASM_TAC THEN PARSE3AUX_SKOLEM_IH_TAC THEN
  PARSE3AUX_LINFIX_SUB_TAC `nDtypeCons` `TOK BarT:(token,MMLnonT)symbol`
                           `NT (INL nDconstructor):(token,MMLnonT)symbol` THEN
  PARSE3AUX_DESTRUCT_TAC THEN PARSE3AUX_EVAL_TAC);;

let PARSE3AUX_complete_ths =
  [`nV`, PARSE3AUX_complete_nV;
   `nUQTyOp`, PARSE3AUX_complete_nUQTyOp;
   `nUQConstructorName`, PARSE3AUX_complete_nUQConstructorName;
   `nTyvarN`, PARSE3AUX_complete_nTyvarN;
   `nTypeName`, PARSE3AUX_complete_nTypeName;
   `nTypeAbbrevDec`, PARSE3AUX_complete_nTypeAbbrevDec;
   `nType`, PARSE3AUX_complete_nType;
   `nTyOp`, PARSE3AUX_complete_nTyOp;
   `nStructure`, PARSE3AUX_complete_nStructure;
   `nStructName`, PARSE3AUX_complete_nStructName;
   `nSignatureValue`, PARSE3AUX_complete_nSignatureValue;
   `nRelOps`, PARSE3AUX_complete_nRelOps;
   `nPtuple`, PARSE3AUX_complete_nPtuple;
   `nPType`, PARSE3AUX_complete_nPType;
   `nPTbase`, PARSE3AUX_complete_nPTbase;
   `nPEsfx`, PARSE3AUX_complete_nPEsfx;
   `nPEs`, PARSE3AUX_complete_nPEs;
   `nOptionalSignatureAscription`, PARSE3AUX_complete_nOptionalSignatureAscription;
   `nOptTypEqn`, PARSE3AUX_complete_nOptTypEqn;
   `nOpID`, PARSE3AUX_complete_nOpID;
   `nMultOps`, PARSE3AUX_complete_nMultOps;
   `nListOps`, PARSE3AUX_complete_nListOps;
   `nLetDec`, PARSE3AUX_complete_nLetDec;
   `nFQV`, PARSE3AUX_complete_nFQV;
   `nFDecl`, PARSE3AUX_complete_nFDecl;
   `nEtyped`, PARSE3AUX_complete_nEtyped;
   `nEseq`, PARSE3AUX_complete_nEseq;
   `nEliteral`, PARSE3AUX_complete_nEliteral;
   `nEhandle`, PARSE3AUX_complete_nEhandle;
   `nE`, PARSE3AUX_complete_nE;
   `nConstructorName`, PARSE3AUX_complete_nConstructorName;
   `nCompOps`, PARSE3AUX_complete_nCompOps;
   `nAddOps`, PARSE3AUX_complete_nAddOps;
   `nTypeList2`, PARSE3AUX_complete_nTypeList2;
   `nTypeList1`, PARSE3AUX_complete_nTypeList1;
   `nPbaseList1`, PARSE3AUX_complete_nPbaseList1;
   `nElist1`, PARSE3AUX_complete_nElist1;
   `nSpecLine`, PARSE3AUX_complete_nSpecLine;
   `nPatternList`, PARSE3AUX_complete_nPatternList;
   `nPattern`, PARSE3AUX_complete_nPattern;
   `nDecl`, PARSE3AUX_complete_nDecl;
   `nTbaseList`, PARSE3AUX_complete_nTbaseList;
   `nDconstructor`, PARSE3AUX_complete_nDconstructor;
   `nSpecLineList`, PARSE3AUX_complete_nSpecLineList;
   `nLetDecs`, PARSE3AUX_complete_nLetDecs;
   `nDecls`, PARSE3AUX_complete_nDecls;
   `nPcons`, PARSE3AUX_complete_nPcons;
   `nElistop`, PARSE3AUX_complete_nElistop;
   `nPbase`, PARSE3AUX_complete_nPbase;
   `nPE`, PARSE3AUX_complete_nPE;
   `nTopLevelDecs`, PARSE3AUX_complete_nTopLevelDecs;
   `nNonETopLevelDecs`, PARSE3AUX_complete_nNonETopLevelDecs;
   `nTbase`, PARSE3AUX_complete_nTbase;
   `nEbase`, PARSE3AUX_complete_nEbase;
   `nErel`, PARSE3AUX_complete_nErel;
   `nEmult`, PARSE3AUX_complete_nEmult;
   `nElogicOR`, PARSE3AUX_complete_nElogicOR;
   `nElogicAND`, PARSE3AUX_complete_nElogicAND;
   `nEcomp`, PARSE3AUX_complete_nEcomp;
   `nEbefore`, PARSE3AUX_complete_nEbefore;
   `nEadd`, PARSE3AUX_complete_nEadd;
   `nTyVarList`, PARSE3AUX_complete_nTyVarList;
   `nAndFDecls`, PARSE3AUX_complete_nAndFDecls;
   `nEapp`, PARSE3AUX_complete_nEapp;
   `nDType`, PARSE3AUX_complete_nDType;
   `nTypeDec`, PARSE3AUX_complete_nTypeDec;
   `nDtypeDecl`, PARSE3AUX_complete_nDtypeDecl;
   `nPas`, PARSE3AUX_complete_nPas;
   `nPapp`, PARSE3AUX_complete_nPapp];;

(* the case of the non-terminal of the goal mkNd (INL N) subs *)
let PARSE3AUX_COMPLETE_DISPATCH_TAC : tactic = fun (asl,w as g) ->
  let _,ev = dest_exists w in
  let n = rand(rand(rator(lhand(rand(rator(rand ev)))))) in
  let th = assoc n PARSE3AUX_complete_ths in
  (MATCH_MP_TAC th THEN ASM_REWRITE_TAC[]) g;;

let completeness = prove
 (`!pt N pfx sfx.
     valid_lptree cmlG pt /\ ptree_head pt = NT (INL N) /\
     INL N IN FDOM (peg_rules cmlPEG) /\
     (~(sfx = []) ==> FST (HD sfx) IN stoppers N) /\
     real_fringe pt = MAP (TOK ## I) pfx ==>
     ?eo. peg_eval cmlPEG (APPEND pfx sfx, peg_nt (INL N) I) (peg_Success sfx [pt] eo)`,
  SUBGOAL_THEN
   `!N (pfx:(token#locs)list). !pt sfx.
      valid_lptree cmlG pt /\ ptree_head pt = NT (INL N) /\
      INL N IN FDOM (peg_rules cmlPEG) /\
      (~(sfx = []) ==> FST (HD sfx) IN stoppers N) /\
      real_fringe pt = MAP (TOK ## I) pfx ==>
      ?eo. peg_eval cmlPEG (APPEND pfx sfx, peg_nt (INL N) I) (peg_Success sfx [pt] eo)`
   (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC PARSE3AUX_LEX_IND THEN
  MAP_EVERY X_GEN_TAC [`N:MMLnonT`; `pfx:(token#locs)list`] THEN
  DISCH_THEN(LABEL_TAC "lih") THEN
  SUBGOAL_THEN
   `!pt' N' pfx' sfx'.
      (LENGTH pfx' < LENGTH (pfx:(token#locs)list) \/
       pfx' = pfx /\ NT_rank (INL N') < NT_rank (INL N)) /\
      valid_lptree cmlG pt' /\ ptree_head pt' = NT (INL N') /\
      INL N' IN FDOM (peg_rules cmlPEG) /\
      (~(sfx' = []) ==> FST (HD sfx') IN stoppers N') /\
      real_fringe pt' = MAP (TOK ## I) pfx' ==>
      ?eo. peg_eval cmlPEG (APPEND pfx' sfx', peg_nt (INL N') I)
                    (peg_Success sfx' [pt'] eo)`
    (LABEL_TAC "ih") THENL
   [MAP_EVERY X_GEN_TAC [`pt':mlptree`; `N':MMLnonT`; `pfx':(token#locs)list`;
                         `sfx':(token#locs)list`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (fun lr ->
      MP_TAC(SPECL [`pt':mlptree`; `sfx':(token#locs)list`]
               (MP (SPECL [`N':MMLnonT`; `pfx':(token#locs)list`]
                          (ASSUME `!N' pfx'. LENGTH (pfx':(token#locs)list) < LENGTH (pfx:(token#locs)list) \/
                                     pfx' = pfx /\ NT_rank (INL N') < NT_rank (INL N)
                                     ==> (!pt sfx. valid_lptree cmlG pt /\ ptree_head pt = NT (INL N') /\
                                           INL N' IN FDOM (peg_rules cmlPEG) /\
                                           (~(sfx = []) ==> FST (HD sfx) IN stoppers N') /\
                                           real_fringe pt = MAP (TOK ## I) pfx' ==>
                                           ?eo. peg_eval cmlPEG (APPEND pfx' sfx, peg_nt (INL N') I)
                                                         (peg_Success sfx [pt] eo))`)) lr)))
      STRIP_ASSUME_TAC) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`pt:mlptree`; `sfx:(token#locs)list`] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`pt:mlptree`; `N:MMLnonT`; `pfx:(token#locs)list`] ptree_head_NT_mkNd) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `subs:(mlptree)list` SUBST_ALL_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    concl th = `INL N IN FDOM (peg_rules cmlPEG)`)) THEN
  REWRITE_TAC[FDOM_cmlPEG; IN_INSERT; NOT_IN_EMPTY; injectivity "sum"] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
  PARSE3AUX_COMPLETE_DISPATCH_TAC);;

(* a fringe of tokens is the image of a token list *)
let PARSE3AUX_tok_fringe = prove
 (`!l:((token,MMLnonT)symbol#locs)list.
     (!s. MEM s (MAP FST l) ==> ?t. s = TOK t) ==> ?pfx. l = MAP (TOK ## I) pfx`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; MEM] THENL
   [MESON_TAC[MAP]; ALL_TAC] THEN
  REWRITE_TAC[DISJ_IMP_THM; FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `t0:token`) ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `pfx:(token#locs)list`) THEN
  EXISTS_TAC `CONS (t0:token, SND (h:(token,MMLnonT)symbol#locs)) pfx` THEN
  ASM_REWRITE_TAC[MAP; CONS_11; PAIR_MAP_THM; I_THM] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  MP_TAC(ISPEC `h:(token,MMLnonT)symbol#locs` PAIR_SURJECTIVE) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[FST; SND; PAIR_EQ] THEN MESON_TAC[]);;

let cmlG_unambiguous = prove
 (`!pt1 pt2 N.
     valid_lptree cmlG pt1 /\ ptree_head pt1 = NT (INL N) /\
     valid_lptree cmlG pt2 /\ ptree_head pt2 = NT (INL N) /\
     INL N IN FDOM (peg_rules cmlPEG) /\
     real_fringe pt2 = real_fringe pt1 /\
     (!s. s IN set_of_list (ptree_fringe pt1) ==> ?t. s = TOK t) ==>
     pt1 = pt2`,
  REWRITE_TAC[IN_SET_OF_LIST] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `real_fringe (pt1:mlptree)` PARSE3AUX_tok_fringe) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[GSYM ptree_fringe_real_fringe]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `pfx:(token#locs)list`) THEN
  MP_TAC(SPECL [`pt1:mlptree`; `N:MMLnonT`; `pfx:(token#locs)list`;
                `[]:(token#locs)list`] completeness) THEN
  MP_TAC(SPECL [`pt2:mlptree`; `N:MMLnonT`; `pfx:(token#locs)list`;
                `[]:(token#locs)list`] completeness) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `eo2:(locs#(char)list)option`) THEN
  DISCH_THEN(X_CHOOSE_TAC `eo1:(locs#(char)list)option`) THEN
  MP_TAC(PARSE3AUX_DET_RULE
    (ASSUME `peg_eval cmlPEG (APPEND pfx [],peg_nt (INL N) I) (peg_Success [] [pt1] eo1)`)
    (ASSUME `peg_eval cmlPEG (APPEND pfx [],peg_nt (INL N) I) (peg_Success [] [pt2] eo2)`)) THEN
  REWRITE_TAC[pegresult_inject; CONS_11] THEN MESON_TAC[]);;
