(* ========================================================================= *)
(* pegSound: port of HOL4 compiler/parsing/proofs/pegSoundScript.sml        *)
(* (CakeML v3479).                                                           *)
(* Soundness proof for the parser. If the parser returns a parse tree,      *)
(* then it is valid w.r.t. the specification grammar.                       *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - HOL4's overloads mkNT (INL), NN n (NT (INL n)) and TK (TOK on token)   *)
(*   are written out; G.rules is peg_rules G or grammar_rules G, f ' x is   *)
(*   FAPPLY f x, ++ is APPEND (HOL4's ++ associates to the left), Success   *)
(*   is peg's peg_Success.  The free variables of the HOL4 statements are   *)
(*   universally quantified.                                                 *)
(* - peg_eval_choicel_SING is the value of two SIMP_CONV calls in HOL4; it  *)
(*   is stated here as the two equations those calls give (the Failure one  *)
(*   keeps UNCURRY Failure (MAXerr ...), which srw_ss does not reduce).     *)
(* - HOL4 adds a list of rewrites to the simpset of this script with        *)
(*   augment_srw_ss (not exported); the proofs here name what they use.     *)
(*   The [simp,local] theorems FADISJ_EQ_IMP', PAIR_MAP_I, bindNT0_lemma,   *)
(*   pmap_EQ_pair and pair_EQ_components are not registered (they would be *)
(*   exported to the files that load this one); PAIR_MAP_I is              *)
(*   pegSound_PAIR_MAP_I (basic.ml binds PAIR_MAP_I to pair's theorem).     *)
(* - peg_sound: HOL4 proves it by one well-founded induction (input length, *)
(*   then NT_rank) with one hand-written case per rule of cmlPEG.  Here the *)
(*   induction is the same, and each case is a lemma PARSE3AUX_sound_nX     *)
(*   proved by one procedure (PARSE3AUX_CASE_TAC): decompose the successful *)
(*   evaluation of the rule, apply the induction hypothesis to each         *)
(*   non-terminal in it (peg_linfix_correct_lemma, peg_EbaseParen_sound to  *)
(*   those parts), and check the tree against the rule in cmlG.  The        *)
(*   inductions inside the cases nEapp and nDType are PARSE3AUX_rpt_foldl,  *)
(*   the one inside peg_linfix_correct_lemma is PARSE3AUX_linfix_rpt.       *)
(* - Helpers that are not HOL4 names have the prefix PARSE3AUX_.             *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "hol4/peg.ml";;
needs "hol4/grammar.ml";;
needs "semantics/gram.ml";;
needs "semantics/proofs/gramProps.ml";;
needs "compiler/parsing/cmlPEG.ml";;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Evaluation of the derived forms of cmlPEG.                                *)
(* ------------------------------------------------------------------------- *)

let Success_COND_Failure = prove
 (`!(i:A) (r:C) (opt:(locs#E)option) P fl1 fe1 fl2 fe2.
     ~(peg_Success i r opt = if P then Failure fl1 fe1 else Failure fl2 fe2)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[pegresult_distinct]);;
let _ = cake_add_simps [Success_COND_Failure];;

let peg_eval_choicel_NIL = prove
 (`!(G:(A,B,(C)list,E)peg) i0 x.
     peg_eval G (i0, choicel []) x <=> x = Failure (peg_sloc i0) (peg_notFAIL G)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[choicel_def] THEN
  GEN_REWRITE_TAC LAND_CONV [peg_eval_cases] THEN
  REWRITE_TAC[PAIR_EQ; pegsym_distinct; pegsym_inject; peg_eval_empty] THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM; LEFT_EXISTS_AND_THM; UNWIND_THM1;
              UNWIND_THM2; GSYM CONJ_ASSOC] THEN
  REWRITE_TAC[peg_eval_empty; UNWIND_THM1; UNWIND_THM2; isSuccess_def;
              isFailure_def] THEN
  MESON_TAC[]);;
let _ = cake_add_simps [peg_eval_choicel_NIL];;

let peg_TF = prove
 (`!(G:(A,B,C,E)peg) i e fl fe.
     (?i' r eopt. peg_eval G (i,e) (peg_Success i' r eopt)) ==>
     ~peg_eval G (i,e) (Failure fl fe)`,
  MESON_TAC[peg_deterministic; pegresult_distinct]);;

let peg_FT = prove
 (`!(G:(A,B,C,E)peg) i e i' r eopt.
     (?fl fe. peg_eval G (i,e) (Failure fl fe)) ==>
     ~peg_eval G (i,e) (peg_Success i' r eopt)`,
  MESON_TAC[peg_deterministic; pegresult_distinct]);;

let peg_eval_choicel_CONS = prove
 (`!(G:(A,B,(C)list,E)peg) i0 h t x.
     peg_eval G (i0, choicel (CONS h t)) x <=>
       (?i r eopt.
          peg_eval G (i0, h) (peg_Success i r eopt) /\ x = peg_Success i r eopt) \/
       (?res2 fl1 fe1 i r eopt fl2 fe2.
          peg_eval G (i0,h) (Failure fl1 fe1) /\
          peg_eval G (i0,choicel t) res2 /\
          (res2 = peg_Success i r eopt /\
           x = peg_Success i r (optmax MAXerr (SOME (fl1,fe1)) eopt) \/
           res2 = Failure fl2 fe2 /\
           x = UNCURRY Failure (MAXerr (fl1, fe1) (fl2,fe2))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[choicel_def] THEN
  GEN_REWRITE_TAC LAND_CONV [peg_eval_choice] THEN
  REWRITE_TAC[EXISTS_result; isSuccess_def; resultmap_def; o_THM; sumID_def] THEN
  MESON_TAC[]);;

let peg_eval_seql_NIL = prove
 (`!(G:(A,B,(C)list,E)peg) i0 f x.
     peg_eval G (i0, seql [] f) x <=> x = peg_Success i0 (f []) NONE`,
  REPEAT GEN_TAC THEN REWRITE_TAC[seql_def; pegf_def; ITLIST] THEN
  GEN_REWRITE_TAC LAND_CONV [peg_eval_cases] THEN
  REWRITE_TAC[PAIR_EQ; pegsym_distinct; pegsym_inject; peg_eval_empty;
              pegresult_distinct; pegresult_inject] THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM; LEFT_EXISTS_AND_THM; UNWIND_THM1;
              UNWIND_THM2; GSYM CONJ_ASSOC] THEN
  REWRITE_TAC[peg_eval_empty; pegresult_distinct; pegresult_inject] THEN
  MESON_TAC[]);;
let _ = cake_add_simps [peg_eval_seql_NIL];;

let peg_eval_try = prove
 (`!(G:(A,B,(C)list,E)peg) i0 s x.
     peg_eval G (i0, try s) x <=>
       (?fl fe. peg_eval G (i0, s) (Failure fl fe) /\
                x = peg_Success i0 [] (optmax MAXerr (SOME (fl,fe)) NONE)) \/
       ?i r eo. peg_eval G (i0, s) (peg_Success i r eo) /\ x = peg_Success i r eo`,
  REPEAT GEN_TAC THEN REWRITE_TAC[try_def; peg_eval_choicel_CONS;
                                  peg_eval_choicel_NIL; peg_eval_empty] THEN
  REWRITE_TAC[pegresult_distinct; pegresult_inject] THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM; LEFT_EXISTS_AND_THM; UNWIND_THM1;
              UNWIND_THM2; GSYM CONJ_ASSOC] THEN
  MESON_TAC[pegresult_distinct; pegresult_inject]);;

(* the derived form pegf *)

let PARSE3AUX_peg_eval_pegf = prove
 (`!(G:(A,B,(C)list,E)peg) i0 s f x.
     peg_eval G (i0, pegf s f) x <=>
       (?fl fe. peg_eval G (i0, s) (Failure fl fe) /\ x = Failure fl fe) \/
       (?i r eo. peg_eval G (i0, s) (peg_Success i r eo) /\
                 x = peg_Success i (f r) NONE)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pegf_def] THEN
  GEN_REWRITE_TAC LAND_CONV [peg_eval_cases] THEN
  REWRITE_TAC[PAIR_EQ; pegsym_distinct; pegsym_inject; peg_eval_empty;
              pegresult_distinct; pegresult_inject] THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM; LEFT_EXISTS_AND_THM; UNWIND_THM1;
              UNWIND_THM2; GSYM CONJ_ASSOC] THEN
  REWRITE_TAC[peg_eval_empty; pegresult_distinct; pegresult_inject] THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM; LEFT_EXISTS_AND_THM; UNWIND_THM1;
              UNWIND_THM2; GSYM CONJ_ASSOC] THEN
  MESON_TAC[]);;

let peg_eval_seql_CONS = prove
 (`!(G:(A,B,(C)list,E)peg) i0 h t f x.
     peg_eval G (i0, seql (CONS h t) f) x <=>
       (?fl fe. peg_eval G (i0, h) (Failure fl fe) /\ x = Failure fl fe) \/
       (?rh i1 fl fe eopt.
          peg_eval G (i0,h) (peg_Success i1 rh eopt) /\
          peg_eval G (i1, seql t I) (Failure fl fe) /\ x = Failure fl fe) \/
       (?rh i1 i rt eopt1 eopt2.
          peg_eval G (i0, h) (peg_Success i1 rh eopt1) /\
          peg_eval G (i1, seql t I) (peg_Success i rt eopt2) /\
          x = peg_Success i (f (APPEND rh rt)) eopt2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[seql_def; ITLIST] THEN
  REWRITE_TAC[PARSE3AUX_peg_eval_pegf; peg_eval_seq_SOME; peg_eval_seq_NONE;
              I_THM; pegresult_distinct; pegresult_inject] THEN
  MESON_TAC[]);;

let PARSE3AUX_Success_EQ_UNCURRY_Failure = prove
 (`!(fle:locs#E) (s:A) (r:C) eo. ~(peg_Success s r eo = UNCURRY Failure fle)`,
  MESON_TAC[UNCURRY_Failure_EQ_Success]);;

let peg_eval_choicel_SING = prove
 (`(!(G:(A,B,(C)list,E)peg) i0 sym i r eo.
      peg_eval G (i0, choicel [sym]) (peg_Success i r eo) <=>
      peg_eval G (i0, sym) (peg_Success i r eo)) /\
   (!(G:(A,B,(C)list,E)peg) i0 sym fl fe.
      peg_eval G (i0, choicel [sym]) (Failure fl fe) <=>
      ?fl1 fe1. peg_eval G (i0, sym) (Failure fl1 fe1) /\
                (Failure fl fe:((A#locs)list,(C)list,E)pegresult) =
                UNCURRY Failure (MAXerr (fl1,fe1) (peg_sloc i0,peg_notFAIL G)))`,
  REWRITE_TAC[peg_eval_choicel_CONS; peg_eval_choicel_NIL] THEN
  REWRITE_TAC[pegresult_distinct; pegresult_inject; UNCURRY_Failure_EQ_Success;
              PARSE3AUX_Success_EQ_UNCURRY_Failure] THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM; LEFT_EXISTS_AND_THM; UNWIND_THM1;
              UNWIND_THM2; GSYM CONJ_ASSOC] THEN
  MESON_TAC[pegresult_distinct; pegresult_inject]);;

let not_peg0_LENGTH_decreases = prove
 (`!(G:(A,B,C,E)peg) s i0 i r eo.
     ~peg0 G s ==> peg_eval G (i0, s) (peg_Success i r eo) ==> LENGTH i < LENGTH i0`,
  MESON_TAC[peg_eval_suffix'; lemma4_1a]);;

(* HOL4 adds peg_eval_seql_CONS, peg_eval_tok_SOME, tokeq_def, bindNT_def,   *)
(* mktokLf_def, peg_eval_choicel_CONS, pegf_def, peg_eval_seq_SOME, pnt_def, *)
(* peg_eval_try, try_def and resultmap_EQ_Success to the simpset of this     *)
(* script (not exported); here they are given to the proofs that use them.  *)

let peg_eval_tokSymP = prove
 (`!(G:(token,B,(mlptree)list,E)peg) i0 P i r eo.
     peg_eval G (i0, tokSymP P) (peg_Success i r eo) <=>
     ?h s. FST h = SymbolT s /\ P s /\ i0 = CONS h i /\ r = mktokLf h /\ eo = NONE`,
  REWRITE_TAC[tokSymP_def; peg_eval_tok_SOME; OPTION_BIND_EQUALS_OPTION;
              OPTION_GUARD_EQ_THM; destSymbolT_EQ_SOME; EXISTS_PAIR_THM] THEN
  MESON_TAC[]);;
let _ = cake_add_simps [peg_eval_tokSymP];;

(* HOL4: [simp,local] *)
let FADISJ_EQ_IMP' = prove
 (`!(P:A->bool) Q.
     ((!x. P x) \/ Q <=> !x. ~P x ==> Q) /\
     ((Q \/ !x. P x) <=> !x. ~P x ==> Q)`,
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Successful evaluation of the derived forms, as iff theorems for           *)
(* decomposing a hypothesis, and the token classes of the peg_tok expressions    *)
(* as constructor forms (helpers of this file).                              *)
(* ------------------------------------------------------------------------- *)

let PARSE3AUX_S_seql_NIL = prove
 (`!(G:(A,B,(C)list,E)peg) i0 f i r eo.
     peg_eval G (i0, seql [] f) (peg_Success i r eo) <=>
     i = i0 /\ r = f [] /\ eo = NONE`,
  REWRITE_TAC[peg_eval_seql_NIL; pegresult_inject] THEN MESON_TAC[]);;

let PARSE3AUX_S_seql_CONS = prove
 (`!(G:(A,B,(C)list,E)peg) i0 h t f i r eo.
     peg_eval G (i0, seql (CONS h t) f) (peg_Success i r eo) <=>
     ?i1 rh eo1 rt.
       peg_eval G (i0,h) (peg_Success i1 rh eo1) /\
       peg_eval G (i1, seql t I) (peg_Success i rt eo) /\
       r = f (APPEND rh rt)`,
  REWRITE_TAC[peg_eval_seql_CONS; pegresult_distinct; pegresult_inject] THEN
  MESON_TAC[]);;

let PARSE3AUX_S_choicel_NIL = prove
 (`!(G:(A,B,(C)list,E)peg) i0 i r eo.
     peg_eval G (i0, choicel []) (peg_Success i r eo) <=> F`,
  REWRITE_TAC[peg_eval_choicel_NIL; pegresult_distinct]);;

let PARSE3AUX_S_choicel_CONS = prove
 (`!(G:(A,B,(C)list,E)peg) i0 h t i r eo.
     peg_eval G (i0, choicel (CONS h t)) (peg_Success i r eo) <=>
     peg_eval G (i0, h) (peg_Success i r eo) \/
     ?fl fe eo'. peg_eval G (i0, h) (Failure fl fe) /\
                 peg_eval G (i0, choicel t) (peg_Success i r eo') /\
                 eo = optmax MAXerr (SOME (fl,fe)) eo'`,
  REWRITE_TAC[peg_eval_choicel_CONS; pegresult_distinct; pegresult_inject;
              UNCURRY_Failure_EQ_Success; PARSE3AUX_Success_EQ_UNCURRY_Failure] THEN
  REWRITE_TAC[EXISTS_result; pegresult_distinct; pegresult_inject] THEN
  MESON_TAC[]);;

let PARSE3AUX_S_try = prove
 (`!(G:(A,B,(C)list,E)peg) i0 s i r eo.
     peg_eval G (i0, try s) (peg_Success i r eo) <=>
     peg_eval G (i0, s) (peg_Success i r eo) \/
     ?fl fe. peg_eval G (i0, s) (Failure fl fe) /\ i = i0 /\ r = [] /\
             eo = optmax MAXerr (SOME (fl,fe)) NONE`,
  REWRITE_TAC[peg_eval_try; pegresult_inject] THEN MESON_TAC[]);;

let PARSE3AUX_S_pegf = prove
 (`!(G:(A,B,(C)list,E)peg) i0 s f i r eo.
     peg_eval G (i0, pegf s f) (peg_Success i r eo) <=>
     ?r0 eo0. peg_eval G (i0, s) (peg_Success i r0 eo0) /\ r = f r0 /\ eo = NONE`,
  REWRITE_TAC[PARSE3AUX_peg_eval_pegf; pegresult_distinct; pegresult_inject] THEN
  MESON_TAC[]);;

let PARSE3AUX_S_tokeq = prove
 (`!(G:(token,B,(mlptree)list,E)peg) i0 t i r eo.
     peg_eval G (i0, tokeq t) (peg_Success i r eo) <=>
     ?l. i0 = CONS (t,l) i /\ r = [Lf (TOK t, l)] /\ eo = NONE`,
  REWRITE_TAC[tokeq_def; peg_eval_tok_SOME; mktokLf_def] THEN MESON_TAC[]);;

let PARSE3AUX_S_empty = prove
 (`!(G:(A,B,C,E)peg) i0 c i r eo.
     peg_eval G (i0, empty c) (peg_Success i r eo) <=>
     i = i0 /\ r = c /\ eo = NONE`,
  REWRITE_TAC[peg_eval_empty; pegresult_inject] THEN MESON_TAC[]);;

let PARSE3AUX_S_choice = prove
 (`!(G:(A,B,C,E)peg) i0 s1 s2 f i r eo.
     peg_eval G (i0, choice s1 s2 f) (peg_Success i r eo) <=>
     (?r1. peg_eval G (i0, s1) (peg_Success i r1 eo) /\ r = f (INL r1)) \/
     (?r2 eo2 fl fe. peg_eval G (i0, s1) (Failure fl fe) /\
                     peg_eval G (i0, s2) (peg_Success i r2 eo2) /\
                     r = f (INR r2) /\ eo = optmax MAXerr (SOME (fl,fe)) eo2)`,
  REWRITE_TAC[peg_eval_choice; EXISTS_result; isSuccess_def; resultmap_def;
              o_THM; pegresult_distinct; pegresult_inject;
              UNCURRY_Failure_EQ_Success; PARSE3AUX_Success_EQ_UNCURRY_Failure] THEN
  MESON_TAC[]);;

let PARSE3AUX_S_tokSymP = prove
 (`!(G:(token,B,(mlptree)list,E)peg) i0 P i r eo.
     peg_eval G (i0, tokSymP P) (peg_Success i r eo) <=>
     ?l s. P s /\ i0 = CONS (SymbolT s,l) i /\ r = [Lf (TOK (SymbolT s),l)] /\
           eo = NONE`,
  REWRITE_TAC[peg_eval_tokSymP; EXISTS_PAIR_THM; mktokLf_def] THEN
  MESON_TAC[]);;

(* the token classes of the PEG's peg_tok expressions, as constructor forms *)

let PARSE3AUX_isInt_EQ = prove
 (`!t. isInt t <=> ?i. t = tokens_IntT i`,
  GEN_TAC THEN CASES_ON `t:token` THEN SIMP[] THEN MESON_TAC[]);;

let PARSE3AUX_isString_EQ = prove
 (`!t. isString t <=> ?m. t = StringT m`,
  GEN_TAC THEN CASES_ON `t:token` THEN SIMP[] THEN MESON_TAC[]);;

let PARSE3AUX_isCharT_EQ = prove
 (`!t. isCharT t <=> ?c. t = tokens_CharT c`,
  GEN_TAC THEN CASES_ON `t:token` THEN SIMP[] THEN MESON_TAC[]);;

let PARSE3AUX_isWordT_EQ = prove
 (`!t. isWordT t <=> ?n. t = tokens_WordT n`,
  GEN_TAC THEN CASES_ON `t:token` THEN SIMP[] THEN MESON_TAC[]);;

let PARSE3AUX_isTyvarT_EQ = prove
 (`!t. isTyvarT t <=> ?m. t = TyvarT m`,
  GEN_TAC THEN CASES_ON `t:token` THEN SIMP[] THEN MESON_TAC[]);;

let PARSE3AUX_isLongidT_EQ = prove
 (`!t. isLongidT t <=> ?p m. t = LongidT p m`,
  GEN_TAC THEN CASES_ON `t:token` THEN SIMP[] THEN MESON_TAC[]);;

let PARSE3AUX_isAlphaSym_EQ = prove
 (`!t. isAlphaSym t <=> (?m. t = AlphaT m) \/ (?m. t = SymbolT m)`,
  GEN_TAC THEN CASES_ON `t:token` THEN SIMP[] THEN MESON_TAC[]);;

let PARSE3AUX_destFFIT_EQ = prove
 (`!t. IS_SOME (destFFIT t) <=> ?m. t = FFIT m`,
  GEN_TAC THEN CASES_ON `t:token` THEN SIMP[] THEN MESON_TAC[]);;

let PARSE3AUX_EXISTS_REFL' = prove
 (`!a:A. (?x. a = x) <=> T`,
  MESON_TAC[]);;

let PARSE3AUX_EX_SING = prove
 (`!(a:A) P. (?pt. [a] = [pt] /\ P pt) <=> P a`,
  REWRITE_TAC[CONS_11] THEN MESON_TAC[]);;

let PARSE3AUX_DECOMP_RWTS =
  [PARSE3AUX_S_seql_NIL; PARSE3AUX_S_seql_CONS; PARSE3AUX_S_choicel_NIL;
   PARSE3AUX_S_choicel_CONS; PARSE3AUX_S_try; PARSE3AUX_S_pegf;
   PARSE3AUX_S_tokeq; PARSE3AUX_S_empty; PARSE3AUX_S_choice;
   peg_eval_tok_SOME; PARSE3AUX_S_tokSymP; peg_eval_seq_SOME; cmlPEG_pnt_def; MAP];;

let PARSE3AUX_TOKPRED_RWTS =
  [OPTION_BIND_EQUALS_OPTION; OPTION_GUARD_EQ_THM; destAlphaT_EQ_SOME;
   destSymbolT_EQ_SOME; destLongidT_EQ_SOME; o_THM;
   PARSE3AUX_isInt_EQ; PARSE3AUX_isString_EQ; PARSE3AUX_isCharT_EQ;
   PARSE3AUX_isWordT_EQ; PARSE3AUX_isTyvarT_EQ; PARSE3AUX_isLongidT_EQ;
   PARSE3AUX_isAlphaSym_EQ; PARSE3AUX_destFFIT_EQ];;

(* ------------------------------------------------------------------------- *)
(* Wrong first tokens.                                                       *)
(* ------------------------------------------------------------------------- *)

let PARSE3AUX_WRONGTOK_TAC ths =
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC([peg_eval_NT_SOME] @ ths) THEN
  REWRITE_TAC(PARSE3AUX_DECOMP_RWTS @ PARSE3AUX_TOKPRED_RWTS) THEN
  REWRITE_TAC[CONS_11; PAIR_EQ] THEN REPEAT STRIP_TAC THEN GVS[] THEN
  ASM_MESON_TAC[];;

let peg_eval_TypeDec_wrongtok = prove
 (`!(tk:token#locs) i f i' r eo.
     ~(FST tk = DatatypeT) ==>
     ~peg_eval cmlPEG (CONS tk i, peg_nt (INL nTypeDec) f) (peg_Success i' r eo)`,
  PARSE3AUX_WRONGTOK_TAC [PARSE2AUX_rule `nTypeDec`; peg_TypeDec_def]);;

let peg_eval_TypeAbbrevDec_wrongtok = prove
 (`!(tk:token#locs) i f i' r eo.
     ~(FST tk = TypeT) ==>
     ~peg_eval cmlPEG (CONS tk i, peg_nt (INL nTypeAbbrevDec) f) (peg_Success i' r eo)`,
  PARSE3AUX_WRONGTOK_TAC [PARSE2AUX_rule `nTypeAbbrevDec`]);;

let peg_eval_Structure_wrongtok = prove
 (`!(tk:token#locs) i f i' r e0.
     ~(FST tk = StructureT) ==>
     ~peg_eval cmlPEG (CONS tk i, peg_nt (INL nStructure) f) (peg_Success i' r e0)`,
  PARSE3AUX_WRONGTOK_TAC [PARSE2AUX_rule `nStructure`]);;

let peg_eval_LetDec_wrongtok = prove
 (`!(tk:token#locs) i f i' r eo.
     FST tk = SemicolonT ==>
     ~peg_eval cmlPEG (CONS tk i, peg_nt (INL nLetDec) f) (peg_Success i' r eo)`,
  PARSE3AUX_WRONGTOK_TAC [PARSE2AUX_rule `nLetDec`]);;

let peg_eval_nUQConstructor_wrongtok = prove
 (`!(t:token#locs) i f i' r eo.
     (!s. ~(FST t = AlphaT s)) ==>
     ~peg_eval cmlPEG (CONS t i, peg_nt (INL nUQConstructorName) f) (peg_Success i' r eo)`,
  PARSE3AUX_WRONGTOK_TAC [PARSE2AUX_rule `nUQConstructorName`;
                          peg_UQConstructorName_def]);;

let peg_eval_nConstructor_wrongtok = prove
 (`!(t:token#locs) i f i' r eo.
     (!s. ~(FST t = AlphaT s)) /\ (!s1 s2. ~(FST t = LongidT s1 s2)) ==>
     ~peg_eval cmlPEG (CONS t i, peg_nt (INL nConstructorName) f) (peg_Success i' r eo)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[peg_eval_NT_SOME; PARSE2AUX_rule `nConstructorName`] THEN
  REWRITE_TAC(PARSE3AUX_DECOMP_RWTS @ PARSE3AUX_TOKPRED_RWTS) THEN
  REWRITE_TAC[CONS_11; PAIR_EQ] THEN REPEAT STRIP_TAC THEN
  ASM_MESON_TAC[peg_eval_nUQConstructor_wrongtok; FST]);;

let peg_eval_nV_wrongtok = prove
 (`!(t:token#locs) i f i' r eo.
     (!s. ~(FST t = AlphaT s)) /\ (!s. ~(FST t = SymbolT s)) ==>
     ~peg_eval cmlPEG (CONS t i, peg_nt (INL nV) f) (peg_Success i' r eo)`,
  PARSE3AUX_WRONGTOK_TAC [PARSE2AUX_rule `nV`; peg_V_def]);;

let peg_eval_nFQV_wrongtok = prove
 (`!(t:token#locs) i f i' r eo.
     (!s. ~(FST t = AlphaT s)) /\ (!s. ~(FST t = SymbolT s)) /\
     (!s1 s2. ~(FST t = LongidT s1 s2)) ==>
     ~peg_eval cmlPEG (CONS t i, peg_nt (INL nFQV) f) (peg_Success i' r eo)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[peg_eval_NT_SOME; PARSE2AUX_rule `nFQV`; peg_longV_def] THEN
  REWRITE_TAC(PARSE3AUX_DECOMP_RWTS @ PARSE3AUX_TOKPRED_RWTS) THEN
  REWRITE_TAC[CONS_11; PAIR_EQ] THEN REPEAT STRIP_TAC THEN
  ASM_MESON_TAC[peg_eval_nV_wrongtok; FST]);;

(* ------------------------------------------------------------------------- *)
(* Parse trees built by the PEG.                                             *)
(* ------------------------------------------------------------------------- *)

let peg_eval_rpt_never_NONE = prove
 (`!(G:(A,B,C,E)peg) i sym f fl fe. ~peg_eval G (i, peg_rpt sym f) (Failure fl fe)`,
  REWRITE_TAC[peg_eval_rpt; pegresult_distinct]);;
let _ = cake_add_simps [peg_eval_rpt_never_NONE];;

let pegsym_to_sym_def = cake_def
  `(pegsym_to_sym (peg_tok P f:(token,MMLnonT,(mlptree)list,E)pegsym) =
      if f = mktokLf then {TOK t | t | P t} else {}) /\
   (pegsym_to_sym (peg_nt N g) = {NT N}) /\
   (pegsym_to_sym _ = {})`;;

let valid_ptree_mkNd = prove
 (`!(G:(A,B)grammar) N (subs:((A,B,locs)parsetree)list).
     valid_ptree G (mkNd N subs) <=>
       N IN FDOM (grammar_rules G) /\ MAP ptree_head subs IN FAPPLY (grammar_rules G) N /\
       !pt. MEM pt subs ==> valid_ptree G pt`,
  REWRITE_TAC[mkNd_def; valid_ptree_def; IN_SET_OF_LIST]);;
let _ = cake_add_simps [valid_ptree_mkNd];;

let ptree_head_mkNd = prove
 (`!N (subs:((A,B,locs)parsetree)list). ptree_head (mkNd N subs) = NT N`,
  REWRITE_TAC[mkNd_def; ptree_head_def]);;
let _ = cake_add_simps [ptree_head_mkNd];;

let ptree_list_loc_SING = prove
 (`!pt:(A,B,locs)parsetree. ptree_list_loc [pt] = ptree_loc pt`,
  REWRITE_TAC[ptree_list_loc_def; MAP; merge_list_locs_def]);;
let _ = cake_add_simps [ptree_list_loc_SING];;

let ptree_fringemkNd = prove
 (`!N (subs:((A,B,locs)parsetree)list).
     ptree_fringe (mkNd N subs) = FLAT (MAP ptree_fringe subs)`,
  REWRITE_TAC[mkNd_def; ptree_fringe_def]);;
let _ = cake_add_simps [ptree_fringemkNd];;

let valid_locs_mkNd = prove
 (`!N (subs:((A,B,locs)parsetree)list).
     valid_locs (mkNd N subs) <=> !pt. MEM pt subs ==> valid_locs pt`,
  REWRITE_TAC[mkNd_def; valid_locs_def; ptree_list_loc_def]);;
let _ = cake_add_simps [valid_locs_mkNd];;

let rfringe_length_not_nullable = prove
 (`!(G:(A,B)grammar) s.
     ~nullable G [s] ==>
     !pt:(A,B,locs)parsetree. ptree_head pt = s ==> valid_lptree G pt ==>
                              0 < LENGTH (real_fringe pt)`,
  MESON_TAC[fringe_length_not_nullable; LENGTH_real_fringe; valid_lptree_def]);;

let valid_lptree_mkNd = prove
 (`!(G:(A,B)grammar) n (children:((A,B,locs)parsetree)list).
     valid_lptree G (mkNd n children) <=>
       n IN FDOM (grammar_rules G) /\
       MAP ptree_head children IN FAPPLY (grammar_rules G) n /\
       !pt. MEM pt children ==> valid_lptree G pt`,
  REWRITE_TAC[mkNd_def; valid_lptree_thm; ptree_list_loc_def] THEN
  MESON_TAC[]);;
let _ = cake_add_simps [valid_lptree_mkNd];;

let real_fringe_mkNd = prove
 (`!n (subs:((A,B,locs)parsetree)list).
     real_fringe (mkNd n subs) = FLAT (MAP real_fringe subs)`,
  REWRITE_TAC[mkNd_def; real_fringe_def]);;
let _ = cake_add_simps [real_fringe_mkNd];;

let ptree_head_NT_mkNd = prove
 (`!(pt:mlptree) n (pf:(token#locs)list).
     ptree_head pt = NT (INL n) /\ valid_lptree cmlG pt /\
     real_fringe pt = MAP (TOK ## I) pf ==>
     ?subs. pt = mkNd (INL n) subs`,
  MATCH_MP_TAC ptree_ind THEN CONJ_TAC THENL
   [REWRITE_TAC[FORALL_PAIR_THM; ptree_head_def; real_fringe_def] THEN
    REPEAT GEN_TAC THEN
    STRUCT_CASES_TAC(ISPEC `pf:(token#locs)list` list_CASES) THEN
    REWRITE_TAC[MAP; NOT_CONS_NIL; CONS_11] THEN
    STRUCT_CASES_TAC(ISPEC `h:token#locs` PAIR_SURJECTIVE) THEN
    REWRITE_TAC[PAIR_MAP_THM; PAIR_EQ] THEN MESON_TAC[symbol_distinct];
    GEN_TAC THEN DISCH_THEN(K ALL_TAC) THEN
    REWRITE_TAC[FORALL_PAIR_THM; ptree_head_def; valid_lptree_thm;
                symbol_inject; mkNd_def; parsetree_inject; PAIR_EQ;
                ptree_list_loc_def] THEN
    MESON_TAC[]]);;

let mkNd_11 = prove
 (`!n1 (sub1:((A,B,locs)parsetree)list) n2 sub2.
     mkNd n1 sub1 = mkNd n2 sub2 <=> n1 = n2 /\ sub1 = sub2`,
  REWRITE_TAC[mkNd_def; parsetree_inject; PAIR_EQ] THEN MESON_TAC[]);;
let _ = cake_add_simps [mkNd_11];;

(* the repetition part of peg_linfix (the induction of HOL4's proof) *)

let PARSE3AUX_linfix_rpt = prove
 (`!UpperN (sym:(token,MMLnonT,(mlptree)list,(char)list)pegsym) sepsym
     (i0:(token#locs)list).
     (!i0' i pts s eo.
        s IN {sym, sepsym} ==>
        LENGTH i0' < LENGTH i0 ==>
        peg_eval cmlPEG (i0',s) (peg_Success i pts eo) ==>
        ?pt. pts = [pt] /\ ptree_head pt IN pegsym_to_sym s /\
             valid_lptree cmlG pt /\
             MAP (TOK ## I) i0' = APPEND (real_fringe pt) (MAP (TOK ## I) i)) /\
     ~peg0 cmlPEG sym /\
     UpperN IN FDOM (grammar_rules cmlG) /\
     {[NT UpperN; gsep; gsym] | gsep,gsym |
        gsep IN pegsym_to_sym sepsym /\ gsym IN pegsym_to_sym sym} SUBSET
       FAPPLY (grammar_rules cmlG) UpperN ==>
     !l i1 i err acc.
       peg_eval_list cmlPEG (i1, peg_seq sepsym sym APPEND) (i, l, err) /\
       LENGTH i1 < LENGTH i0 /\
       ptree_head acc = NT UpperN /\ valid_lptree cmlG acc ==>
       ptree_head (mk_linfix UpperN acc (FLAT l)) = NT UpperN /\
       valid_lptree cmlG (mk_linfix UpperN acc (FLAT l)) /\
       APPEND (real_fringe acc) (MAP (TOK ## I) i1) =
       APPEND (real_fringe (mk_linfix UpperN acc (FLAT l))) (MAP (TOK ## I) i)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih")
    (CONJUNCTS_THEN2 (LABEL_TAC "np0")
      (CONJUNCTS_THEN2 (LABEL_TAC "dom") (LABEL_TAC "sub")))) THEN
  LIST_INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [peg_eval_list] THEN
    REWRITE_TAC[NOT_CONS_NIL; GSYM NOT_CONS_NIL; FLAT; mk_linfix_def] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [peg_eval_list] THEN
  REWRITE_TAC[NOT_CONS_NIL; GSYM NOT_CONS_NIL; CONS_11; peg_eval_seq_SOME] THEN
  DISCH_THEN(CAKE_STRIP_ASSUME_TAC) THEN RVEQ_TAC THEN
  (* the separator, at a shorter input *)
  USE_THEN "ih" (MP_TAC o SPECL
    [`i1:(token#locs)list`; `i1'':(token#locs)list`; `r1:(mlptree)list`;
     `sepsym:(token,MMLnonT,(mlptree)list,(char)list)pegsym`;
     `eo1:(locs#(char)list)option`]) THEN
  REWRITE_TAC[IN_INSERT] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sep_pt:mlptree` STRIP_ASSUME_TAC) THEN
  (* the operand after it *)
  SUBGOAL_THEN `LENGTH (i1'':(token#locs)list) <= LENGTH (i1:(token#locs)list)`
    ASSUME_TAC THENL [ASM_MESON_TAC[peg_eval_suffix'; LT_IMP_LE; LE_REFL]; ALL_TAC] THEN
  USE_THEN "ih" (MP_TAC o SPECL
    [`i1'':(token#locs)list`; `i1':(token#locs)list`; `r2:(mlptree)list`;
     `sym:(token,MMLnonT,(mlptree)list,(char)list)pegsym`;
     `eo0:(locs#(char)list)option`]) THEN
  REWRITE_TAC[IN_INSERT] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sym_pt:mlptree` STRIP_ASSUME_TAC) THEN
  RVEQ_TAC THEN
  SUBGOAL_THEN `LENGTH (i1':(token#locs)list) < LENGTH (i1'':(token#locs)list)`
    ASSUME_TAC THENL
   [ASM_MESON_TAC[not_peg0_LENGTH_decreases]; ALL_TAC] THEN
  (* the rest, by the induction hypothesis *)
  FIRST_X_ASSUM(MP_TAC o SPECL
    [`i1':(token#locs)list`; `i:(token#locs)list`; `err:locs#(char)list`;
     `mkNd UpperN [acc; sep_pt; sym_pt]:mlptree`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[ptree_head_mkNd; valid_lptree_mkNd; MAP; MEM] THEN
    REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC;
      USE_THEN "sub" (MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[APPEND; FLAT; mk_linfix_def; real_fringe_mkNd; MAP;
              APPEND_NIL; GSYM APPEND_ASSOC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[APPEND_ASSOC]);;

let peg_linfix_correct_lemma = prove
 (`!UpperN (sym:(token,MMLnonT,(mlptree)list,(char)list)pegsym) sepsym
    (i0:(token#locs)list) i pts eo.
     peg_eval cmlPEG (i0, peg_linfix UpperN sym sepsym) (peg_Success i pts eo) ==>
     (!i0' i pts s eo.
        s IN {sym, sepsym} ==>
        LENGTH i0' < LENGTH i0 ==>
        peg_eval cmlPEG (i0',s) (peg_Success i pts eo) ==>
        ?pt. pts = [pt] /\ ptree_head pt IN pegsym_to_sym s /\
             valid_lptree cmlG pt /\
             MAP (TOK ## I) i0' = APPEND (real_fringe pt) (MAP (TOK ## I) i)) /\
     (!i pts s eo.
        s IN {sym, sepsym} ==>
        peg_eval cmlPEG (i0, s) (peg_Success i pts eo) ==>
        ?pt. pts = [pt] /\ ptree_head pt IN pegsym_to_sym s /\
             valid_lptree cmlG pt /\
             MAP (TOK ## I) i0 = APPEND (real_fringe pt) (MAP (TOK ## I) i)) /\
     ~peg0 cmlPEG sym /\
     UpperN IN FDOM (grammar_rules cmlG) /\
     {[gsym] | gsym | gsym IN pegsym_to_sym sym} SUBSET
       FAPPLY (grammar_rules cmlG) UpperN /\
     {[NT UpperN; gsep; gsym] | gsep,gsym |
        gsep IN pegsym_to_sym sepsym /\ gsym IN pegsym_to_sym sym} SUBSET
       FAPPLY (grammar_rules cmlG) UpperN ==>
     ?pt. pts = [pt] /\ ptree_head pt = NT UpperN /\ valid_lptree cmlG pt /\
          MAP (TOK ## I) i0 = APPEND (real_fringe pt) (MAP (TOK ## I) i)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[peg_linfix_def; peg_eval_seq_SOME; peg_eval_rpt;
              pegresult_inject] THEN
  DISCH_THEN(CAKE_STRIP_ASSUME_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1")
    (CONJUNCTS_THEN2 (LABEL_TAC "ih2")
      (CONJUNCTS_THEN2 (LABEL_TAC "np0")
        (CONJUNCTS_THEN2 (LABEL_TAC "dom")
          (CONJUNCTS_THEN2 (LABEL_TAC "sub1") (LABEL_TAC "sub2")))))) THEN
  RVEQ_TAC THEN
  (* the first operand *)
  USE_THEN "ih2" (MP_TAC o SPECL
    [`i1:(token#locs)list`; `r1:(mlptree)list`;
     `sym:(token,MMLnonT,(mlptree)list,(char)list)pegsym`;
     `eo1:(locs#(char)list)option`]) THEN
  REWRITE_TAC[IN_INSERT] THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `rpt1:mlptree` STRIP_ASSUME_TAC) THEN
  RVEQ_TAC THEN
  SUBGOAL_THEN `LENGTH (i1:(token#locs)list) < LENGTH (i0:(token#locs)list)`
    ASSUME_TAC THENL
   [ASM_MESON_TAC[not_peg0_LENGTH_decreases]; ALL_TAC] THEN
  (* the repetitions *)
  MP_TAC(SPECL [`UpperN:MMLnonT+num`;
                `sym:(token,MMLnonT,(mlptree)list,(char)list)pegsym`;
                `sepsym:(token,MMLnonT,(mlptree)list,(char)list)pegsym`;
                `i0:(token#locs)list`] PARSE3AUX_linfix_rpt) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> FIRST_ASSUM(MP_TAC o SPEC `mkNd UpperN [rpt1]:mlptree` o
                                    MATCH_MP (REWRITE_RULE[IMP_CONJ] th))) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  ANTS_TAC THENL [REWRITE_TAC[ptree_head_mkNd]; ALL_TAC] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[valid_lptree_mkNd; MAP; MEM] THEN
    CONJ_TAC THENL
     [USE_THEN "sub1" (MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[list_CASE; PARSE3AUX_EX_SING; real_fringe_mkNd; MAP; FLAT;
              APPEND_NIL] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let length_no_greater = prove
 (`!(G:(A,B,C,E)peg) i0 sym i r eo.
     peg_eval G (i0, sym) (peg_Success i r eo) ==> LENGTH i <= LENGTH i0`,
  MESON_TAC[peg_eval_suffix'; LT_IMP_LE; LE_REFL]);;

let MAP_TK_11 = prove
 (`!x y. MAP (TOK:token->(token,MMLnonT)symbol) x = MAP TOK y <=> x = y`,
  REPEAT GEN_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN
  MATCH_MP_TAC(MESON[]
    `(!l m. MAP (TOK:token->(token,MMLnonT)symbol) l = MAP TOK m ==> l = m)
     ==> MAP (TOK:token->(token,MMLnonT)symbol) x = MAP TOK y ==> x = y`) THEN
  REWRITE_TAC[INJECTIVE_MAP; symbol_inject]);;
let _ = cake_add_simps [MAP_TK_11];;

let peg_eval_nTyOp_wrongtok = prove
 (`!(tk:token#locs) i f i' r eo.
     FST tk = LparT ==>
     ~peg_eval cmlPEG (CONS tk i, peg_nt (INL nTyOp) f) (peg_Success i' r eo)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[peg_eval_NT_SOME; PARSE2AUX_rule `nTyOp`] THEN
  REWRITE_TAC(PARSE3AUX_DECOMP_RWTS @ PARSE3AUX_TOKPRED_RWTS) THEN
  REWRITE_TAC[peg_eval_NT_SOME; PARSE2AUX_rule `nUQTyOp`] THEN
  REWRITE_TAC(PARSE3AUX_DECOMP_RWTS @ PARSE3AUX_TOKPRED_RWTS) THEN
  REWRITE_TAC[CONS_11; PAIR_EQ] THEN REPEAT STRIP_TAC THEN GVS[] THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Machinery for the cases of peg_sound (helpers of this file).  The case   *)
(* of a non-terminal X: from the induction hypothesis (smaller input, or    *)
(* the same input and a non-terminal of smaller rank) and a successful      *)
(* evaluation of the rule of X, the tree is valid.  The evaluation is       *)
(* decomposed (PARSE3AUX_DECOMP_RWTS), the hypothesis is applied to every   *)
(* non-terminal in it, peg_linfix_correct_lemma and peg_EbaseParen_sound to *)
(* those parts, and the tree is checked against the rule of X in cmlG.      *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Computing NT_rank of a non-terminal (constructor equations decided by     *)
(* gramProps' table PARSE1AUX_NT_EQ_CONV).                                   *)
(* ------------------------------------------------------------------------- *)

let rec PARSE3AUX_COND_CHAIN_CONV tm =
  if is_cond tm then
    let th1 = RATOR_CONV(RATOR_CONV(RAND_CONV PARSE1AUX_NT_EQ_CONV)) tm in
    let th2 = TRANS th1 (GEN_REWRITE_CONV I [COND_CLAUSES] (rhs(concl th1))) in
    TRANS th2 (PARSE3AUX_COND_CHAIN_CONV (rhs(concl th2)))
  else REFL tm;;

let PARSE3AUX_NT_RANK_CONV =
  GEN_REWRITE_CONV I [NT_rank_def] THENC GEN_REWRITE_CONV I [sum_CASE] THENC
  BETA_CONV THENC PARSE3AUX_COND_CHAIN_CONV;;

let PARSE3AUX_RANK_TAC =
  CONV_TAC(BINOP_CONV PARSE3AUX_NT_RANK_CONV THENC NUM_LT_CONV);;

(* the statement of the case of non-terminal X: the induction hypothesis of *)
(* peg_sound (all smaller input lengths, or the same input and a smaller    *)
(* rank) and a successful evaluation of the rule of X                       *)

let PARSE3AUX_sound_goal (x:string) =
  parse_term
   ("!i0 i pts eo.
      (!N i0' i' pts' eo'.
         (LENGTH i0' < LENGTH i0 \\/
          LENGTH i0' = LENGTH i0 /\\ NT_rank N < NT_rank (INL " ^ x ^ ")) /\\
         peg_eval cmlPEG (i0', peg_nt N I) (peg_Success i' pts' eo') ==>
         ?pt. pts' = [pt] /\\ ptree_head pt = NT N /\\ valid_lptree cmlG pt /\\
              MAP (TOK ## I) i0' = APPEND (real_fringe pt) (MAP (TOK ## I) i')) /\\
      peg_eval cmlPEG (i0, FAPPLY (peg_rules cmlPEG) (INL " ^ x ^ "))
               (peg_Success i pts eo) ==>
      ?pt. pts = [pt] /\\ ptree_head pt = NT (INL " ^ x ^ ") /\\
           valid_lptree cmlG pt /\\
           MAP (TOK ## I) i0 = APPEND (real_fringe pt) (MAP (TOK ## I) i)");;

let PARSE3AUX_IH_SPLIT = prove
 (`!(i0:(token#locs)list) X.
     (!N i0' i' pts' eo'.
        (LENGTH i0' < LENGTH i0 \/
         LENGTH i0' = LENGTH i0 /\ NT_rank N < NT_rank X) /\
        peg_eval cmlPEG (i0', peg_nt N I) (peg_Success i' pts' eo') ==>
        ?pt. pts' = [pt] /\ ptree_head pt = NT N /\ valid_lptree cmlG pt /\
             MAP (TOK ## I) i0' = APPEND (real_fringe pt) (MAP (TOK ## I) i'))
     ==> (!N j j' pts eo.
            peg_eval cmlPEG (j, peg_nt N I) (peg_Success j' pts eo) ==>
            LENGTH j < LENGTH i0 ==>
            ?pt. pts = [pt] /\ ptree_head pt = NT N /\ valid_lptree cmlG pt /\
                 MAP (TOK ## I) j = APPEND (real_fringe pt) (MAP (TOK ## I) j')) /\
         (!N j' pts eo.
            peg_eval cmlPEG (i0, peg_nt N I) (peg_Success j' pts eo) ==>
            NT_rank N < NT_rank X ==>
            ?pt. pts = [pt] /\ ptree_head pt = NT N /\ valid_lptree cmlG pt /\
                 MAP (TOK ## I) i0 = APPEND (real_fringe pt) (MAP (TOK ## I) j'))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]);;

let PARSE3AUX_npeg0_ths =
  [peg0_nTypeDec; peg0_nTypeAbbrevDec; peg0_nOpID; peg0_nStructure;
   peg0_nDecl; peg0_nV; peg0_nUQTyOp; peg0_nUQConstructorName;
   peg0_nStructName; peg0_nConstructorName; peg0_nTypeName; peg0_nDtypeDecl;
   peg0_nDconstructor; peg0_nFDecl; peg0_nTyvarN; peg0_nTyOp; peg0_nTbase;
   peg0_nPTbase; peg0_nDType; peg0_nPType; peg0_nType; peg0_nTypeList1;
   peg0_nTypeList2; peg0_nRelOps; peg0_nPtuple; peg0_nPbase; peg0_nPapp;
   peg0_nPcons; peg0_nPas; peg0_nPattern; peg0_nPatternList;
   peg0_nPbaseList1; peg0_nLetDec; peg0_nMultOps; peg0_nListOps; peg0_nFQV;
   peg0_nAddOps; peg0_nCompOps; peg0_nEliteral; peg0_nEbase; peg0_nEapp;
   peg0_nEmult; peg0_nEadd; peg0_nElistop; peg0_nErel; peg0_nEcomp;
   peg0_nEbefore; peg0_nEtyped; peg0_nElogicAND; peg0_nElogicOR;
   peg0_nEhandle; peg0_nE; peg0_nPE; peg0_nPEs; peg0_nElist1;
   peg0_nSpecLine];;

let PARSE3AUX_dec_ths =
  map (MATCH_MP not_peg0_LENGTH_decreases) PARSE3AUX_npeg0_ths;;

(* peg_eval cmlPEG (a,e) (peg_Success b r eo) *)

let PARSE3AUX_is_success tm =
  try let p,args = strip_comb tm in
      fst(dest_const p) = "peg_eval" && length args = 3 &&
      fst(dest_const(fst(strip_comb(el 2 args)))) = "peg_Success"
  with Failure _ -> false;;

let PARSE3AUX_is_ntfact tm =
  PARSE3AUX_is_success tm &&
  (try fst(dest_const(fst(strip_comb(rand(el 1 (snd(strip_comb tm))))))) = "peg_nt"
   with Failure _ -> false);;

let PARSE3AUX_LEN_FACTS_TAC : tactic = fun (asl,w) ->
  let facts = filter (fun th -> PARSE3AUX_is_success (concl th)) (map snd asl) in
  let ths = flat (map (fun th ->
       MATCH_MP length_no_greater th ::
       mapfilter (fun d -> MATCH_MP d th) PARSE3AUX_dec_ths) facts) in
  MAP_EVERY ASSUME_TAC ths (asl,w);;

let PARSE3AUX_is_lenfact tm =
  (is_binary "<" tm || is_binary "<=" tm) &&
  (try fst(dest_const(rator(lhand tm))) = "LENGTH" &&
       fst(dest_const(rator(rand tm))) = "LENGTH"
   with Failure _ -> false);;

let PARSE3AUX_LEN_TAC : tactic = fun (asl,w) ->
  let facts = filter (fun th -> PARSE3AUX_is_lenfact (concl th)) (map snd asl) in
  (MAP_EVERY (MP_TAC o REWRITE_RULE[LENGTH]) facts THEN REWRITE_TAC[LENGTH] THEN
   ARITH_TAC) (asl,w);;

let PARSE3AUX_IH1_TAC (th:thm) : tactic =
  (fun (asl,_ as g) ->
     let ihb = assoc "ihb" asl in
     (MP_TAC (MATCH_MP ihb th) THEN ANTS_TAC THENL
      [PARSE3AUX_RANK_TAC; ALL_TAC]) g) ORELSE
  (fun (asl,_ as g) ->
     let iha = assoc "iha" asl in
     (MP_TAC (MATCH_MP iha th) THEN ANTS_TAC THENL
      [PARSE3AUX_LEN_TAC; ALL_TAC]) g);;

let PARSE3AUX_APPLY_IH_TAC : tactic =
  REPEAT (FIRST_X_ASSUM (fun th ->
    if PARSE3AUX_is_ntfact (concl th) then PARSE3AUX_IH1_TAC th THEN STRIP_TAC
    else failwith "PARSE3AUX_APPLY_IH_TAC"));;

(* the rule of a non-terminal in the grammar cmlG *)

let PARSE3AUX_grule (c:term) =
  find (fun r -> rand(rand(lhs(concl r))) = c) (CONJUNCTS cmlG_applied);;

let PARSE3AUX_GRULE_CONV tm =
  let c = rand(rand tm) in
  REWR_CONV (PARSE3AUX_grule c) tm;;

let PARSE3AUX_is_result tm =
  (is_eq tm &&
   (try fst(dest_const(rator(lhs tm))) = "ptree_head" with Failure _ -> false)) ||
  (try fst(dest_const(fst(strip_comb tm))) = "valid_lptree" with Failure _ -> false) ||
  (is_eq tm &&
   (try fst(dest_const(fst(strip_comb(lhs tm)))) = "MAP" with Failure _ -> false));;

let PARSE3AUX_DROP_TAC (p:term->bool) : tactic =
  REPEAT (FIRST_X_ASSUM (fun th -> if p (concl th) then ALL_TAC
                                    else failwith "PARSE3AUX_DROP_TAC"));;

let PARSE3AUX_is_evalfact tm =
  try fst(dest_const(fst(strip_comb tm))) = "peg_eval" with Failure _ -> false;;

let PARSE3AUX_CLEANUP_TAC =
  PARSE3AUX_DROP_TAC (fun t -> is_forall t || PARSE3AUX_is_evalfact t ||
                               PARSE3AUX_is_lenfact t);;

let PARSE3AUX_FINISH_GEN_TAC (extra:thm list) : tactic = fun (asl,w) ->
  let res = filter (fun th -> PARSE3AUX_is_result (concl th)) (map snd asl) in
  (REWRITE_TAC([bindNT_def; REWRITE_RULE [GSYM mkNd_def] bindNT0_def;
                mktokLf_def; APPEND; APPEND_NIL;
                I_THM; o_THM; FST; SND] @ extra) THEN
   (if extra = [] then ALL_TAC else CASE_REWRITE_TAC extra) THEN
   REWRITE_TAC[PARSE3AUX_EX_SING; UNWIND_THM1] THEN
   REWRITE_TAC([ptree_head_mkNd; valid_lptree_mkNd; real_fringe_mkNd; MAP; FLAT;
                ptree_head_def; real_fringe_def; valid_lptree_thm; MEM;
                DISJ_IMP_THM; FORALL_AND_THM; FORALL_UNWIND_THM2;
                PARSE1AUX_cmlG_FDOM_INL; PAIR_MAP_THM; I_THM; APPEND;
                APPEND_NIL; GSYM APPEND_ASSOC] @ res) THEN
   CONV_TAC(ONCE_DEPTH_CONV PARSE3AUX_GRULE_CONV) THEN
   REWRITE_TAC[IN_INSERT; IN_UNION; NOT_IN_EMPTY; IN_ELIM_THM] THEN
   CASE_REWRITE_TAC[PARSE3AUX_EXISTS_REFL'] THEN
   TRY(PARSE3AUX_CLEANUP_TAC THEN ASM_MESON_TAC[])) (asl,w);;

let PARSE3AUX_FINISH_TAC = PARSE3AUX_FINISH_GEN_TAC [];;

let PARSE3AUX_START_TAC (defs:thm list) : tactic =
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (fun ih -> let a,b = CONJ_PAIR(MATCH_MP PARSE3AUX_IH_SPLIT ih) in
               LABEL_TAC "iha" a THEN LABEL_TAC "ihb" b)
    MP_TAC) THEN
  W(fun (_,w) -> let c = rand(rand(rand(lhand(lhand w)))) in
                 REWRITE_TAC[PARSE2AUX_rule c]) THEN
  REWRITE_TAC defs THEN
  REWRITE_TAC(PARSE3AUX_DECOMP_RWTS @ PARSE3AUX_TOKPRED_RWTS) THEN
  DISCH_THEN CAKE_STRIP_ASSUME_TAC;;

let PARSE3AUX_TIDY_TAC : tactic =
  RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV GEN_BETA_CONV)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[OPTION_GUARD_EQ_THM; IN_INSERT; NOT_IN_EMPTY]);;

(* the side conditions of peg_linfix_correct_lemma *)

let PARSE3AUX_TOKLF_TAC : tactic =
  REWRITE_TAC[mktokLf_def; FST; SND; PARSE3AUX_EX_SING; ptree_head_def;
              valid_lptree_thm; real_fringe_def; MAP; PAIR_MAP_THM; I_THM;
              APPEND; IN_ELIM_THM] THEN
  MESON_TAC[];;

let PARSE3AUX_LINFIX_SUB_TAC : tactic =
  REWRITE_TAC[pegsym_to_sym_def; tokeq_def; IN_SING; peg_eval_tok_SOME] THEN
  (DISCH_THEN(fun th -> PARSE3AUX_IH1_TAC th THEN DISCH_THEN ACCEPT_TAC) ORELSE
   (STRIP_TAC THEN RVEQ_TAC THEN PARSE3AUX_TOKLF_TAC));;

let PARSE3AUX_LINFIX_CONDS_TAC : tactic =
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN REPEAT GEN_TAC THEN
    DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN DISCH_TAC THEN
    PARSE3AUX_LINFIX_SUB_TAC;
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN REPEAT GEN_TAC THEN
    DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN
    PARSE3AUX_LINFIX_SUB_TAC;
    REWRITE_TAC PARSE3AUX_npeg0_ths;
    REWRITE_TAC[PARSE1AUX_cmlG_FDOM_INL];
    REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; pegsym_to_sym_def; tokeq_def; IN_SING;
                IN_ELIM_THM] THEN
    REWRITE_TAC[FORALL_UNWIND_THM2; LEFT_IMP_EXISTS_THM] THEN
    CONV_TAC(ONCE_DEPTH_CONV PARSE3AUX_GRULE_CONV) THEN
    REWRITE_TAC[IN_INSERT; IN_UNION; NOT_IN_EMPTY; IN_ELIM_THM] THEN
    CASE_REWRITE_TAC[];
    REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; pegsym_to_sym_def; tokeq_def; IN_SING;
                IN_ELIM_THM] THEN
    REWRITE_TAC[FORALL_UNWIND_THM2; LEFT_IMP_EXISTS_THM] THEN
    CONV_TAC(ONCE_DEPTH_CONV PARSE3AUX_GRULE_CONV) THEN
    REWRITE_TAC[IN_INSERT; IN_UNION; NOT_IN_EMPTY; IN_ELIM_THM] THEN
    CASE_REWRITE_TAC[]];;

let PARSE3AUX_is_linfixfact tm =
  PARSE3AUX_is_success tm &&
  (try fst(dest_const(fst(strip_comb(rand(el 1 (snd(strip_comb tm)))))))
         = "peg_linfix"
   with Failure _ -> false);;

let PARSE3AUX_APPLY_LINFIX_TAC : tactic = fun (asl,w) ->
  let facts = filter (fun th -> PARSE3AUX_is_linfixfact (concl th))
                     (map snd asl) in
  EVERY (map (fun th -> MP_TAC (MATCH_MP peg_linfix_correct_lemma th) THEN
                        ANTS_TAC THENL [PARSE3AUX_LINFIX_CONDS_TAC; STRIP_TAC])
             facts) (asl,w);;

let peg_EbaseParen_sound = prove
 (`!(i0:(token#locs)list) i pts eo.
     peg_eval cmlPEG (i0, peg_EbaseParen) (peg_Success i pts eo) ==>
     (!i0' N i pts eo.
        LENGTH i0' < LENGTH i0 /\
        peg_eval cmlPEG (i0', peg_nt (INL N) I) (peg_Success i pts eo) ==>
        ?pt. pts = [pt] /\ ptree_head pt = NT (INL N) /\
             valid_lptree cmlG pt /\
             MAP (TOK ## I) i0' = APPEND (real_fringe pt) (MAP (TOK ## I) i)) ==>
     ?pt. pts = [pt] /\ ptree_head pt = NT (INL nEbase) /\
          valid_lptree cmlG pt /\
          MAP (TOK ## I) i0 = APPEND (real_fringe pt) (MAP (TOK ## I) i)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[peg_EbaseParen_def] THEN
  REWRITE_TAC(PARSE3AUX_DECOMP_RWTS @ PARSE3AUX_TOKPRED_RWTS) THEN
  DISCH_THEN CAKE_STRIP_ASSUME_TAC THEN
  DISCH_THEN(LABEL_TAC "iha" o REWRITE_RULE[IMP_CONJ_ALT]) THEN
  RVEQ_TAC THEN PARSE3AUX_LEN_FACTS_TAC THEN PARSE3AUX_APPLY_IH_TAC THEN
  RVEQ_TAC THEN
  PARSE3AUX_FINISH_GEN_TAC[peg_EbaseParenFn_def; list_CASE; destLf_def;
                           destTOK_def; option_CASE]);;

let PARSE3AUX_is_ebasefact tm =
  PARSE3AUX_is_success tm &&
  (try fst(dest_const(rand(el 1 (snd(strip_comb tm))))) = "peg_EbaseParen"
   with Failure _ -> false);;

let PARSE3AUX_APPLY_EBASE_TAC : tactic = fun (asl,w) ->
  let facts = filter (fun th -> PARSE3AUX_is_ebasefact (concl th))
                     (map snd asl) in
  EVERY (map (fun th ->
     MP_TAC (MATCH_MP peg_EbaseParen_sound th) THEN ANTS_TAC THENL
      [REPEAT GEN_TAC THEN
       DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (fun th ->
         USE_THEN "iha" (fun ih -> MP_TAC (MATCH_MP ih th)))) THEN
       ASM_REWRITE_TAC[];
       STRIP_TAC]) facts) (asl,w);;

let PARSE3AUX_CASE_TAC (defs:thm list) : tactic =
  PARSE3AUX_START_TAC defs THEN RVEQ_TAC THEN PARSE3AUX_TIDY_TAC THEN
  PARSE3AUX_LEN_FACTS_TAC THEN PARSE3AUX_APPLY_IH_TAC THEN
  PARSE3AUX_APPLY_LINFIX_TAC THEN PARSE3AUX_APPLY_EBASE_TAC THEN RVEQ_TAC THEN
  PARSE3AUX_FINISH_TAC;;

(* HOL4: PAIR_MAP_I [local,simp] (the name PAIR_MAP_I is pair's, basic.ml) *)
let pegSound_PAIR_MAP_I = prove
 (`!(f:A->C) (x:A#B). (f ## I) x = (f (FST x), SND x) <=> T`,
  REWRITE_TAC[FORALL_PAIR_THM; PAIR_MAP_THM; I_THM]);;

(* HOL4: [local,simp] *)
let bindNT0_lemma = REWRITE_RULE [GSYM mkNd_def] bindNT0_def;;

(* left recursive rules in the grammar turn into calls to rpt in the PEG,  *)
(* and this in turn requires inductions                                     *)

let ptPapply_lemma = prove
 (`!limit (i:(token#locs)list).
     (!i0 i pts eo.
        LENGTH i0 < limit ==>
        peg_eval cmlPEG (i0, peg_nt (INL nPbase) I) (peg_Success i pts eo) ==>
        ?pt. pts = [pt] /\ ptree_head pt = NT (INL nPbase) /\
             valid_lptree cmlG pt /\
             MAP (TOK ## I) i0 = APPEND (real_fringe pt) (MAP (TOK ## I) i)) ==>
     !ptlist pt0 acc i0 err.
       peg_eval_list cmlPEG (i0, peg_nt (INL nPbase) I) (i, ptlist, err) /\
       ptree_head pt0 = NT (INL nPbase) /\ valid_lptree cmlG pt0 /\
       ptree_head acc = NT (INL nPConApp) /\ valid_lptree cmlG acc /\
       LENGTH i0 < limit ==>
       ?pt. ptPapply0 acc (CONS pt0 (FLAT ptlist)) = [pt] /\
            ptree_head pt = NT (INL nPapp) /\ valid_lptree cmlG pt /\
            APPEND (APPEND (real_fringe acc) (real_fringe pt0)) (MAP (TOK ## I) i0) =
            APPEND (real_fringe pt) (MAP (TOK ## I) i)`,
  GEN_TAC THEN GEN_TAC THEN DISCH_THEN(LABEL_TAC "ih") THEN
  LIST_INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [peg_eval_list] THEN
    REWRITE_TAC[NOT_CONS_NIL; GSYM NOT_CONS_NIL; FLAT; ptPapply0_def;
                bindNT_def; bindNT0_lemma; PARSE3AUX_EX_SING] THEN
    STRIP_TAC THEN RVEQ_TAC THEN
    ASM_REWRITE_TAC[ptree_head_mkNd; valid_lptree_mkNd; real_fringe_mkNd; MAP;
                    MEM; FLAT; APPEND_NIL; PARSE1AUX_cmlG_FDOM_INL] THEN
    CONV_TAC(ONCE_DEPTH_CONV PARSE3AUX_GRULE_CONV) THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN CASE_REWRITE_TAC[] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [peg_eval_list] THEN
  REWRITE_TAC[NOT_CONS_NIL; GSYM NOT_CONS_NIL; CONS_11] THEN
  DISCH_THEN(CAKE_STRIP_ASSUME_TAC) THEN RVEQ_TAC THEN
  FIRST_ASSUM(fun th -> USE_THEN "ih" (fun ih ->
    if PARSE3AUX_is_ntfact (concl th) then
      MP_TAC (MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT] (REWRITE_RULE[IMP_IMP] ih)) th)
    else failwith "nt fact")) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `pt1:mlptree` STRIP_ASSUME_TAC) THEN RVEQ_TAC THEN
  FIRST_ASSUM(fun th ->
    ASSUME_TAC (MATCH_MP (MATCH_MP not_peg0_LENGTH_decreases peg0_nPbase) th)) THEN
  SUBGOAL_THEN `valid_lptree cmlG (mkNd (INL nPConApp) [acc; pt0])` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[valid_lptree_mkNd; MAP; MEM; PARSE1AUX_cmlG_FDOM_INL] THEN
    CONV_TAC(ONCE_DEPTH_CONV PARSE3AUX_GRULE_CONV) THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN CASE_REWRITE_TAC[] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (i1:(token#locs)list) < limit` ASSUME_TAC THENL
   [ASM_MESON_TAC[LT_TRANS]; ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> FIRST_ASSUM (fun pl ->
    MP_TAC (SPECL [`pt1:mlptree`; `mkNd (INL nPConApp) [acc; pt0]:mlptree`]
     (MATCH_MP (REWRITE_RULE[IMP_CONJ] th) pl)))) THEN
  ASM_REWRITE_TAC[ptree_head_mkNd] THEN
  REWRITE_TAC[FLAT; APPEND; ptPapply0_def; bindNT0_lemma; real_fringe_mkNd; MAP;
              APPEND_NIL; GSYM APPEND_ASSOC]);;

(* HOL4: [simp,local] *)
let pmap_EQ_pair = prove
 (`!(f:A->C) (g:B->D) p a b.
     (f ## g) p = (a,b) <=> ?c d. p = (c,d) /\ f c = a /\ g d = b`,
  REWRITE_TAC[FORALL_PAIR_THM; PAIR_MAP_THM; PAIR_EQ] THEN MESON_TAC[]);;

(* HOL4: [simp,local] *)
let pair_EQ_components = prove
 (`!(p:A#B) x y.
     (p = (x,SND p) <=> FST p = x) /\
     ((x,SND p) = p <=> FST p = x) /\
     (p = (FST p,y) <=> SND p = y) /\
     ((FST p,y) = p <=> SND p = y)`,
  REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The soundness theorem.  HOL4 proves it in one induction on the input     *)
(* length and the rank of the non-terminal, with one case per rule of       *)
(* cmlPEG; here each case is a lemma PARSE3AUX_sound_nX.                    *)
(* ------------------------------------------------------------------------- *)

(* left recursive rules in the grammar turn into calls to peg_rpt in the PEG;   *)
(* nEapp and nDType fold the repetitions with FOLDL (the inductions inside  *)
(* HOL4's proof of peg_sound)                                                *)

let PARSE3AUX_rpt_foldl = prove
 (`!X Y (i0:(token#locs)list).
     (!j j' pts eo.
        peg_eval cmlPEG (j, peg_nt (INL Y) I) (peg_Success j' pts eo) ==>
        LENGTH j < LENGTH i0 ==>
        ?pt. pts = [pt] /\ ptree_head pt = NT (INL Y) /\ valid_lptree cmlG pt /\
             MAP (TOK ## I) j = APPEND (real_fringe pt) (MAP (TOK ## I) j')) /\
     ~peg0 cmlPEG (peg_nt (INL Y) I) /\
     [NT (INL X); NT (INL Y)] IN FAPPLY (grammar_rules cmlG) (INL X) ==>
     !l i1 i err acc.
       peg_eval_list cmlPEG (i1, peg_nt (INL Y) I) (i, l, err) /\
       LENGTH i1 < LENGTH i0 /\
       ptree_head acc = NT (INL X) /\ valid_lptree cmlG acc ==>
       ptree_head (FOLDL (\a b. mkNd (INL X) [a; b]) acc (FLAT l)) = NT (INL X) /\
       valid_lptree cmlG (FOLDL (\a b. mkNd (INL X) [a; b]) acc (FLAT l)) /\
       APPEND (real_fringe acc) (MAP (TOK ## I) i1) =
       APPEND (real_fringe (FOLDL (\a b. mkNd (INL X) [a; b]) acc (FLAT l)))
              (MAP (TOK ## I) i)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih")
    (CONJUNCTS_THEN2 (LABEL_TAC "np0") (LABEL_TAC "rule"))) THEN
  LIST_INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [peg_eval_list] THEN
    REWRITE_TAC[NOT_CONS_NIL; GSYM NOT_CONS_NIL; FLAT; FOLDL] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [peg_eval_list] THEN
  REWRITE_TAC[NOT_CONS_NIL; GSYM NOT_CONS_NIL; CONS_11] THEN
  DISCH_THEN(CAKE_STRIP_ASSUME_TAC) THEN RVEQ_TAC THEN
  FIRST_ASSUM(fun th -> USE_THEN "ih" (fun ih ->
    MP_TAC (MATCH_MP ih th))) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `pt1:mlptree` STRIP_ASSUME_TAC) THEN RVEQ_TAC THEN
  FIRST_ASSUM(fun th -> USE_THEN "np0" (fun np0 ->
    ASSUME_TAC (MATCH_MP (MATCH_MP not_peg0_LENGTH_decreases np0) th))) THEN
  FIRST_X_ASSUM(fun th -> FIRST_ASSUM (fun pl ->
    MP_TAC (SPEC `mkNd (INL X) [acc; pt1]:mlptree`
     (MATCH_MP (REWRITE_RULE[IMP_CONJ] th) pl)))) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[ptree_head_mkNd; valid_lptree_mkNd; MAP; MEM;
                  PARSE1AUX_cmlG_FDOM_INL; FLAT; APPEND; FOLDL] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[real_fringe_mkNd; MAP; FLAT; APPEND_NIL; APPEND_ASSOC]);;

let PARSE3AUX_is_rptfact tm =
  PARSE3AUX_is_success tm &&
  (try fst(dest_const(fst(strip_comb(rand(el 1 (snd(strip_comb tm)))))))
         = "peg_rpt"
   with Failure _ -> false);;

(* replace each successful peg_rpt by its peg_eval_list *)

let PARSE3AUX_RPT_TAC : tactic =
  REPEAT(FIRST_X_ASSUM(fun th ->
    if PARSE3AUX_is_rptfact (concl th)
    then MP_TAC (REWRITE_RULE[peg_eval_rpt; pegresult_inject] th) THEN
         DISCH_THEN CAKE_STRIP_ASSUME_TAC
    else failwith "PARSE3AUX_RPT_TAC")) THEN RVEQ_TAC;;

let PARSE3AUX_is_listfact tm =
  try fst(dest_const(fst(strip_comb tm))) = "peg_eval_list"
  with Failure _ -> false;;

(* the cases nEapp and nDType: the first operand X, then FOLDL over the     *)
(* repetitions of Y                                                          *)

let PARSE3AUX_FOLDL_CASE_TAC (x:term) (y:term) : tactic =
  PARSE3AUX_START_TAC [] THEN RVEQ_TAC THEN PARSE3AUX_TIDY_TAC THEN
  PARSE3AUX_LEN_FACTS_TAC THEN PARSE3AUX_APPLY_IH_TAC THEN PARSE3AUX_RPT_TAC THEN
  RVEQ_TAC THEN
  REWRITE_TAC[APPEND; I_THM; APPEND_NIL; list_CASE; PARSE3AUX_EX_SING] THEN
  W(fun (asl,w) ->
    let fl = find_term (fun t -> try fst(dest_const(fst(strip_comb t))) = "FOLDL"
                                 with Failure _ -> false) w in
    let acc = el 1 (snd(strip_comb fl)) in
    let i0 = rand(lhand(rand(rand w))) in
    MP_TAC (SPECL [x; y; i0] PARSE3AUX_rpt_foldl) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [USE_THEN "iha" (ACCEPT_TAC o SPEC (mk_comb(`INL:MMLnonT->MMLnonT+num`,y)));
        REWRITE_TAC PARSE3AUX_npeg0_ths;
        CONV_TAC(ONCE_DEPTH_CONV PARSE3AUX_GRULE_CONV) THEN
        REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN CASE_REWRITE_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(fun th -> FIRST_ASSUM(fun pl ->
      if PARSE3AUX_is_listfact (concl pl)
      then MP_TAC (SPEC acc (MATCH_MP (REWRITE_RULE[IMP_CONJ] th) pl))
      else failwith "list fact")) THEN
    ANTS_TAC THENL [PARSE3AUX_LEN_TAC; ALL_TAC] THEN
    ANTS_TAC THENL [REWRITE_TAC[ptree_head_mkNd]; ALL_TAC] THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[valid_lptree_mkNd; MAP; MEM; PARSE1AUX_cmlG_FDOM_INL] THEN
      CONV_TAC(ONCE_DEPTH_CONV PARSE3AUX_GRULE_CONV) THEN
      REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN CASE_REWRITE_TAC[] THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[real_fringe_mkNd; MAP; FLAT; APPEND_NIL] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let PARSE3AUX_SUC_1 = ARITH_RULE `!n. SUC 0 = 1 /\ (SUC (SUC n) = 1 <=> F)`;;

let PARSE3AUX_peg_eval_list_NIL = prove
 (`!(G:(A,B,C,E)peg) i0 e i err.
     peg_eval_list G (i0, e) (i, [], err) <=>
     ?fl fe. peg_eval G (i0, e) (Failure fl fe) /\ i = i0 /\ err = (fl,fe)`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [peg_eval_list] THEN
  REWRITE_TAC[NOT_CONS_NIL; GSYM NOT_CONS_NIL] THEN MESON_TAC[]);;

let PARSE3AUX_peg_eval_list_CONS = prove
 (`!(G:(A,B,C,E)peg) i0 e i h t err.
     peg_eval_list G (i0, e) (i, CONS h t, err) <=>
     ?i1 eo0. peg_eval G (i0, e) (peg_Success i1 h eo0) /\
              peg_eval_list G (i1, e) (i, t, err)`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [peg_eval_list] THEN
  REWRITE_TAC[NOT_CONS_NIL; GSYM NOT_CONS_NIL; CONS_11] THEN MESON_TAC[]);;

let PARSE3AUX_LIST_DEST_TAC : tactic =
  FIRST_X_ASSUM(fun th ->
    if PARSE3AUX_is_listfact (concl th) then
      MP_TAC (REWRITE_RULE[PARSE3AUX_peg_eval_list_NIL;
                           PARSE3AUX_peg_eval_list_CONS] th)
    else failwith "PARSE3AUX_LIST_DEST_TAC") THEN
  DISCH_THEN STRIP_ASSUME_TAC THEN RVEQ_TAC;;

(* the case nPapp: a constructor name, then ptPapply over the repetitions  *)
(* of nPbase (ptPapply_lemma), or one nPbase                               *)

let PARSE3AUX_PAPPLY_TAC : tactic = fun (asl,w) ->
  let pp = find_term (fun t -> try fst(dest_const(fst(strip_comb t))) = "ptPapply0"
                               with Failure _ -> false) w in
  let acc,rest = match snd(strip_comb pp) with [a;b] -> a,b | _ -> failwith "ptPapply0" in
  let pt0 = lhand rest in
  let i0 = rand(lhand(rand(rand(rand(snd(dest_exists w)))))) in
  let i = rand(rand(rand(rand(rand(rand(snd(dest_exists w))))))) in
  (MP_TAC (SPECL [mk_comb(`LENGTH:(token#locs)list->num`,i0); i] ptPapply_lemma) THEN
   ANTS_TAC THENL
    [REPEAT STRIP_TAC THEN
     USE_THEN "iha" (fun ih -> FIRST_X_ASSUM (fun th -> MP_TAC (MATCH_MP ih th))) THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   DISCH_THEN(fun th -> FIRST_ASSUM(fun pl ->
     if PARSE3AUX_is_listfact (concl pl)
     then MP_TAC (SPECL [pt0; acc] (MATCH_MP (REWRITE_RULE[IMP_CONJ] th) pl))
     else failwith "list fact")) THEN
   SUBGOAL_THEN (mk_comb(`valid_lptree cmlG`,acc)) ASSUME_TAC THENL
    [ASM_REWRITE_TAC[valid_lptree_mkNd; MAP; MEM; PARSE1AUX_cmlG_FDOM_INL] THEN
     CONV_TAC(ONCE_DEPTH_CONV PARSE3AUX_GRULE_CONV) THEN
     REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN CASE_REWRITE_TAC[] THEN
     ASM_MESON_TAC[];
     ALL_TAC] THEN
   ASM_REWRITE_TAC[ptree_head_mkNd] THEN
   ANTS_TAC THENL [PARSE3AUX_LEN_TAC; ALL_TAC] THEN
   MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN STRIP_TAC THEN
   ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
   REWRITE_TAC[real_fringe_mkNd; MAP; FLAT; APPEND_NIL; GSYM APPEND_ASSOC]) (asl,w);;

let PARSE3AUX_sound_nPapp_TAC : tactic =
  PARSE3AUX_START_TAC [] THEN RVEQ_TAC THEN PARSE3AUX_TIDY_TAC THEN
  PARSE3AUX_LEN_FACTS_TAC THEN PARSE3AUX_APPLY_IH_TAC THEN PARSE3AUX_RPT_TAC THEN
  RVEQ_TAC THENL
   [W(fun (asl,w) ->
      let pl = concl(find (fun th -> PARSE3AUX_is_listfact (concl th)) (map snd asl)) in
      let l = lhand(rand(rand pl)) in
      MP_TAC (ISPEC l list_CASES)) THEN
    DISCH_THEN(CAKE_STRIP_ASSUME_TAC) THEN RVEQ_TAC THEN PARSE3AUX_LIST_DEST_TAC THEN
    REWRITE_TAC[APPEND; I_THM; FLAT; APPEND_NIL; LENGTH; PARSE3AUX_SUC_1;
                COND_CLAUSES] THENL
     [PARSE3AUX_FINISH_TAC;
      PARSE3AUX_LEN_FACTS_TAC THEN PARSE3AUX_APPLY_IH_TAC THEN RVEQ_TAC THEN
      REWRITE_TAC[APPEND; I_THM; FLAT; APPEND_NIL; LENGTH; PARSE3AUX_SUC_1;
                  COND_CLAUSES; list_CASE; ptPapply_def; bindNT0_lemma] THEN
      PARSE3AUX_PAPPLY_TAC];
    PARSE3AUX_FINISH_TAC];;

(* the cases, in the order of HOL4's proof (the order of FDOM_cmlPEG) *)

let PARSE3AUX_sound_ths = ref ([]:(term * thm) list);;

let PARSE3AUX_SOUND (x:string) (tac:tactic) =
  let th = prove(PARSE3AUX_sound_goal x, tac) in
  PARSE3AUX_sound_ths := (parse_term x, th) :: !PARSE3AUX_sound_ths; th;;

let PARSE3AUX_sound_nNonETopLevelDecs = PARSE3AUX_SOUND "nNonETopLevelDecs"
  (PARSE3AUX_CASE_TAC []);;
let PARSE3AUX_sound_nTopLevelDecs = PARSE3AUX_SOUND "nTopLevelDecs"
  (PARSE3AUX_CASE_TAC []);;
let PARSE3AUX_sound_nStructure = PARSE3AUX_SOUND "nStructure"
  (PARSE3AUX_CASE_TAC []);;
let PARSE3AUX_sound_nStructName = PARSE3AUX_SOUND "nStructName"
  (PARSE3AUX_CASE_TAC [peg_StructName_def]);;
let PARSE3AUX_sound_nOptionalSignatureAscription = PARSE3AUX_SOUND "nOptionalSignatureAscription"
  (PARSE3AUX_CASE_TAC []);;
let PARSE3AUX_sound_nSignatureValue = PARSE3AUX_SOUND "nSignatureValue"
  (PARSE3AUX_CASE_TAC []);;
let PARSE3AUX_sound_nSpecLineList = PARSE3AUX_SOUND "nSpecLineList"
  (PARSE3AUX_CASE_TAC []);;
let PARSE3AUX_sound_nSpecLine = PARSE3AUX_SOUND "nSpecLine"
  (PARSE3AUX_CASE_TAC []);;
let PARSE3AUX_sound_nOptTypEqn = PARSE3AUX_SOUND "nOptTypEqn"
  (PARSE3AUX_CASE_TAC []);;
let PARSE3AUX_sound_nDecls = PARSE3AUX_SOUND "nDecls"
  (PARSE3AUX_CASE_TAC []);;
let PARSE3AUX_sound_nTypeAbbrevDec = PARSE3AUX_SOUND "nTypeAbbrevDec"
  (PARSE3AUX_CASE_TAC []);;
let PARSE3AUX_sound_nDecl = PARSE3AUX_SOUND "nDecl"
  (PARSE3AUX_CASE_TAC []);;
let PARSE3AUX_sound_nLetDecs = PARSE3AUX_SOUND "nLetDecs"
  (PARSE3AUX_CASE_TAC []);;
let PARSE3AUX_sound_nLetDec = PARSE3AUX_SOUND "nLetDec"
  (PARSE3AUX_CASE_TAC []);;
let PARSE3AUX_sound_nPtuple = PARSE3AUX_SOUND "nPtuple"
  (PARSE3AUX_CASE_TAC []);;
let PARSE3AUX_sound_nPatternList = PARSE3AUX_SOUND "nPatternList"
  (PARSE3AUX_CASE_TAC []);;
let PARSE3AUX_sound_nPattern = PARSE3AUX_SOUND "nPattern"
  (PARSE3AUX_CASE_TAC []);;
let PARSE3AUX_sound_nPas = PARSE3AUX_SOUND "nPas"
  (PARSE3AUX_CASE_TAC []);;
let PARSE3AUX_sound_nPcons = PARSE3AUX_SOUND "nPcons"
  (PARSE3AUX_CASE_TAC []);;
let PARSE3AUX_sound_nPapp = PARSE3AUX_SOUND "nPapp"
  (PARSE3AUX_sound_nPapp_TAC);;
let PARSE3AUX_sound_nPbase = PARSE3AUX_SOUND "nPbase"
  (PARSE3AUX_CASE_TAC []);;
let PARSE3AUX_sound_nConstructorName = PARSE3AUX_SOUND "nConstructorName"
  (PARSE3AUX_CASE_TAC []);;
let PARSE3AUX_sound_nUQConstructorName = PARSE3AUX_SOUND "nUQConstructorName"
  (PARSE3AUX_CASE_TAC [peg_UQConstructorName_def]);;
let PARSE3AUX_sound_nDconstructor = PARSE3AUX_SOUND "nDconstructor"
  (PARSE3AUX_CASE_TAC []);;
let PARSE3AUX_sound_nDtypeDecl = PARSE3AUX_SOUND "nDtypeDecl"
  (PARSE3AUX_CASE_TAC []);;
let PARSE3AUX_sound_nTypeDec = PARSE3AUX_SOUND "nTypeDec"
  (PARSE3AUX_CASE_TAC [peg_TypeDec_def]);;
let PARSE3AUX_sound_nTyVarList = PARSE3AUX_SOUND "nTyVarList"
  (PARSE3AUX_CASE_TAC []);;
let PARSE3AUX_sound_nTypeName = PARSE3AUX_SOUND "nTypeName"
  (PARSE3AUX_CASE_TAC []);;
let PARSE3AUX_sound_nPType = PARSE3AUX_SOUND "nPType"
  (PARSE3AUX_CASE_TAC []);;
let PARSE3AUX_sound_nUQTyOp = PARSE3AUX_SOUND "nUQTyOp"
  (PARSE3AUX_CASE_TAC []);;
let PARSE3AUX_sound_nTyOp = PARSE3AUX_SOUND "nTyOp"
  (PARSE3AUX_CASE_TAC []);;
let PARSE3AUX_sound_nTbaseList = PARSE3AUX_SOUND "nTbaseList"
  (PARSE3AUX_CASE_TAC []);;
let PARSE3AUX_sound_nTypeList1 = PARSE3AUX_SOUND "nTypeList1"
  (PARSE3AUX_CASE_TAC []);;
let PARSE3AUX_sound_nTypeList2 = PARSE3AUX_SOUND "nTypeList2"
  (PARSE3AUX_CASE_TAC []);;
let PARSE3AUX_sound_nPTbase = PARSE3AUX_SOUND "nPTbase"
  (PARSE3AUX_CASE_TAC []);;
let PARSE3AUX_sound_nTbase = PARSE3AUX_SOUND "nTbase"
  (PARSE3AUX_CASE_TAC []);;
let PARSE3AUX_sound_nDType = PARSE3AUX_SOUND "nDType"
  (PARSE3AUX_FOLDL_CASE_TAC `nDType` `nTyOp`);;
let PARSE3AUX_sound_nType = PARSE3AUX_SOUND "nType"
  (PARSE3AUX_CASE_TAC []);;
let PARSE3AUX_sound_nPbaseList1 = PARSE3AUX_SOUND "nPbaseList1"
  (PARSE3AUX_CASE_TAC []);;
let PARSE3AUX_sound_nFDecl = PARSE3AUX_SOUND "nFDecl"
  (PARSE3AUX_CASE_TAC []);;
let PARSE3AUX_sound_nAndFDecls = PARSE3AUX_SOUND "nAndFDecls"
  (PARSE3AUX_CASE_TAC []);;
let PARSE3AUX_sound_nPEsfx = PARSE3AUX_SOUND "nPEsfx"
  (PARSE3AUX_CASE_TAC []);;
let PARSE3AUX_sound_nPE = PARSE3AUX_SOUND "nPE"
  (PARSE3AUX_CASE_TAC []);;
let PARSE3AUX_sound_nPEs = PARSE3AUX_SOUND "nPEs"
  (PARSE3AUX_CASE_TAC []);;
let PARSE3AUX_sound_nE = PARSE3AUX_SOUND "nE"
  (PARSE3AUX_CASE_TAC []);;
let PARSE3AUX_sound_nEhandle = PARSE3AUX_SOUND "nEhandle"
  (PARSE3AUX_CASE_TAC []);;
let PARSE3AUX_sound_nElogicOR = PARSE3AUX_SOUND "nElogicOR"
  (PARSE3AUX_CASE_TAC []);;
let PARSE3AUX_sound_nElogicAND = PARSE3AUX_SOUND "nElogicAND"
  (PARSE3AUX_CASE_TAC []);;
let PARSE3AUX_sound_nEtyped = PARSE3AUX_SOUND "nEtyped"
  (PARSE3AUX_CASE_TAC []);;
let PARSE3AUX_sound_nEbefore = PARSE3AUX_SOUND "nEbefore"
  (PARSE3AUX_CASE_TAC []);;
let PARSE3AUX_sound_nEcomp = PARSE3AUX_SOUND "nEcomp"
  (PARSE3AUX_CASE_TAC []);;
let PARSE3AUX_sound_nErel = PARSE3AUX_SOUND "nErel"
  (PARSE3AUX_CASE_TAC []);;
let PARSE3AUX_sound_nElistop = PARSE3AUX_SOUND "nElistop"
  (PARSE3AUX_CASE_TAC []);;
let PARSE3AUX_sound_nEadd = PARSE3AUX_SOUND "nEadd"
  (PARSE3AUX_CASE_TAC []);;
let PARSE3AUX_sound_nEmult = PARSE3AUX_SOUND "nEmult"
  (PARSE3AUX_CASE_TAC []);;
let PARSE3AUX_sound_nEseq = PARSE3AUX_SOUND "nEseq"
  (PARSE3AUX_CASE_TAC []);;
let PARSE3AUX_sound_nEbase = PARSE3AUX_SOUND "nEbase"
  (PARSE3AUX_CASE_TAC []);;
let PARSE3AUX_sound_nEliteral = PARSE3AUX_SOUND "nEliteral"
  (PARSE3AUX_CASE_TAC []);;
let PARSE3AUX_sound_nOpID = PARSE3AUX_SOUND "nOpID"
  (PARSE3AUX_CASE_TAC []);;
let PARSE3AUX_sound_nCompOps = PARSE3AUX_SOUND "nCompOps"
  (PARSE3AUX_CASE_TAC []);;
let PARSE3AUX_sound_nListOps = PARSE3AUX_SOUND "nListOps"
  (PARSE3AUX_CASE_TAC []);;
let PARSE3AUX_sound_nRelOps = PARSE3AUX_SOUND "nRelOps"
  (PARSE3AUX_CASE_TAC []);;
let PARSE3AUX_sound_nAddOps = PARSE3AUX_SOUND "nAddOps"
  (PARSE3AUX_CASE_TAC []);;
let PARSE3AUX_sound_nMultOps = PARSE3AUX_SOUND "nMultOps"
  (PARSE3AUX_CASE_TAC []);;
let PARSE3AUX_sound_nElist1 = PARSE3AUX_SOUND "nElist1"
  (PARSE3AUX_CASE_TAC []);;
let PARSE3AUX_sound_nEapp = PARSE3AUX_SOUND "nEapp"
  (PARSE3AUX_FOLDL_CASE_TAC `nEapp` `nEbase`);;
let PARSE3AUX_sound_nFQV = PARSE3AUX_SOUND "nFQV"
  (PARSE3AUX_CASE_TAC [peg_longV_def]);;
let PARSE3AUX_sound_nTyvarN = PARSE3AUX_SOUND "nTyvarN"
  (PARSE3AUX_CASE_TAC []);;
let PARSE3AUX_sound_nV = PARSE3AUX_SOUND "nV"
  (PARSE3AUX_CASE_TAC [peg_V_def]);;

let peg_sound = prove
 (`!N i0 i pts eo.
     peg_eval cmlPEG (i0,peg_nt N I) (peg_Success i pts eo) ==>
     ?pt. pts = [pt] /\ ptree_head pt = NT N /\ valid_lptree cmlG pt /\
          MAP (TOK ## I) i0 = APPEND (real_fringe pt) (MAP (TOK ## I) i)`,
  (* well-founded induction on the length of the input, then the rank of *)
  (* the non-terminal (HOL4: measure LENGTH LEX measure NT_rank) *)
  SUBGOAL_THEN
   `!n r (i0:(token#locs)list) N.
      LENGTH i0 = n /\ NT_rank N = r ==>
      !i pts eo.
        peg_eval cmlPEG (i0,peg_nt N I) (peg_Success i pts eo) ==>
        ?pt. pts = [pt] /\ ptree_head pt = NT N /\ valid_lptree cmlG pt /\
             MAP (TOK ## I) i0 = APPEND (real_fringe pt) (MAP (TOK ## I) i)`
   (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_THEN(LABEL_TAC "ihn") THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `r:num` THEN DISCH_THEN(LABEL_TAC "ihr") THEN
  MAP_EVERY X_GEN_TAC [`i0:(token#locs)list`; `N:MMLnonT+num`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) (ASSUME_TAC o SYM)) THEN
  SUBGOAL_THEN
   `!N' i0' i' pts' eo'.
      (LENGTH i0' < LENGTH (i0:(token#locs)list) \/
       LENGTH i0' = LENGTH i0 /\ NT_rank N' < NT_rank (N:MMLnonT+num)) /\
      peg_eval cmlPEG (i0', peg_nt N' I) (peg_Success i' pts' eo') ==>
      ?pt. pts' = [pt] /\ ptree_head pt = NT N' /\ valid_lptree cmlG pt /\
           MAP (TOK ## I) i0' = APPEND (real_fringe pt) (MAP (TOK ## I) i')`
   (LABEL_TAC "ih") THENL
   [REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 DISJ_CASES_TAC ASSUME_TAC) THENL
     [USE_THEN "ihn" (MP_TAC o SPEC `LENGTH (i0':(token#locs)list)`);
      USE_THEN "ihr" (MP_TAC o SPEC `NT_rank (N':MMLnonT+num)`)] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[peg_eval_NT_SOME; I_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `r0:(mlptree)list`
    (CONJUNCTS_THEN2 SUBST1_TAC (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC))) THEN
  REWRITE_TAC[FDOM_cmlPEG; IN_INSERT; NOT_IN_EMPTY] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
  W(fun (asl,w) ->
    let c = rand(rand(rand(lhand(rand(snd(dest_exists w)))))) in
    let th = assoc c !PARSE3AUX_sound_ths in
    USE_THEN "ih" (fun ih -> FIRST_ASSUM(fun fact ->
      ACCEPT_TAC (MATCH_MP th (CONJ ih fact))))));;
