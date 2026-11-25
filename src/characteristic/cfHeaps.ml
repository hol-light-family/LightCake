(* ========================================================================= *)
(* cfHeaps: port of HOL4 characteristic/cfHeapsScript.sml (CakeML v3479).    *)
(* Defines what is means for a CF separation logic assertion to be "local".  *)
(*                                                                           *)
(* Notation as in characteristic/cfHeapsBase.ml.  Names: local and is_local *)
(* are cf_local and cf_is_local (doc/names.tsv).  HOL4's variable F *)
(* (a characteristic formula) is HF here: F is HOL Light's falsity.  HOL4's  *)
(* hsimpl and rew_heap steps are written as plain separation-logic steps.    *)
(* Helper lemmas that are not HOL4 theorems are CF1AUX_.                     *)
(* ========================================================================= *)

needs "characteristic/cfHeapsBase.ml";;
needs "hol4/set_sep.ml";;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* hchange: using a H1 ==>> H2 theorem modulo frame rule                     *)
(* ------------------------------------------------------------------------- *)

let hchange_lemma' = prove
 (`!(H1:(A->bool)->bool) H1' H H' H2.
     H1 ==>> H1' ==>
     H ==>> H1 STAR H2 /\
     H1' STAR H2 ==>> H' ==>
     H ==>> H'`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SEP_IMP_TRANS THEN
  QEXISTS_TAC "H1 STAR H2" THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SEP_IMP_TRANS THEN QEXISTS_TAC "H1' STAR H2" THEN
  ASM_SIMP_TAC[SEP_IMP_FRAME]);;

let hchange_lemma = prove
 (`!(H1:(A->bool)->bool) H1' H H' H2.
     H1 ==>> H1' /\
     H ==>> H1 STAR H2 /\
     H1' STAR H2 ==>> H' ==>
     H ==>> H'`,
  MESON_TAC[hchange_lemma']);;

(* ------------------------------------------------------------------------- *)
(* Locality                                                                  *)
(* ------------------------------------------------------------------------- *)

(* local = frame rule + consequence rule + garbage collection *)

let cf_local_def = cake_def
  `cf_local (cf:hprop->(res->hprop)->bool) (H:hprop) (Q:res->hprop) <=>
     !h:heap. H h ==> ?H1 H2 Q1.
       (H1 STAR H2) h /\
       cf H1 Q1 /\
       (Q1 *+ H2 ==+> Q *+ cf_GC)`;;

let cf_is_local_def = cake_def
  `cf_is_local (cf:hprop->(res->hprop)->bool) <=> (cf = cf_local cf)`;;

(* helpers: garbage on the right *)

let CF1AUX_SEP_IMP_GC_R = prove
 (`!H:hprop. H ==>> H STAR cf_GC`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`H:hprop`; `H:hprop`; `set_sep_emp:hprop`; `cf_GC`] SEP_IMP_STAR) THEN
  REWRITE_TAC[SEP_IMP_REFL; hsimpl_gc; SEP_CLAUSES]);;

let CF1AUX_STAR_GC_GC = prove
 (`!q:hprop. (q STAR cf_GC) STAR cf_GC = q STAR cf_GC`,
  REWRITE_TAC[GSYM STAR_ASSOC; GC_STAR_GC]);;

let CF1AUX_STARPOST_GC_R = prove
 (`!Q:res->hprop. Q ==+> Q *+ cf_GC`,
  REWRITE_TAC[SEP_IMPPOST_def; STARPOST_def; CF1AUX_SEP_IMP_GC_R]);;

(* a frame around an entailment with garbage on the right *)
let CF1AUX_STAR_GC_FRAME = prove
 (`!p q r:hprop. p ==>> q STAR cf_GC ==> p STAR r ==>> (q STAR r) STAR cf_GC`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(q STAR r) STAR cf_GC = (q STAR cf_GC) STAR (r:hprop)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM STAR_ASSOC] THEN AP_TERM_TAC THEN MATCH_ACCEPT_TAC STAR_COMM;
    ASM_SIMP_TAC[SEP_IMP_FRAME]]);;

(* Properties of [local] *)

let local_elim = prove
 (`!cf H Q. cf H Q ==> cf_local cf H Q`,
  REWRITE_TAC[cf_local_def] THEN REPEAT STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`H:hprop`; `set_sep_emp:hprop`; `Q:res->hprop`] THEN
  ASM_REWRITE_TAC[SEP_CLAUSES; STARPOST_emp; CF1AUX_STARPOST_GC_R]);;

let local_local = prove
 (`!cf. cf_local (cf_local cf) = cf_local cf`,
  GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  MAP_EVERY X_GEN_TAC [`H:hprop`; `Q:res->hprop`] THEN EQ_TAC THENL
   [ALL_TAC; REWRITE_TAC[local_elim]] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [cf_local_def] THEN
  DISCH_TAC THEN REWRITE_TAC[cf_local_def] THEN
  X_GEN_TAC `h:heap` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `h:heap`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `H1:hprop` (X_CHOOSE_THEN `H2:hprop`
    (X_CHOOSE_THEN `Q1:res->hprop` STRIP_ASSUME_TAC))) THEN
  QPAT_X_ASSUM "(H1 STAR H2) h" (MP_TAC o REWRITE_RULE[STAR_def]) THEN
  DISCH_THEN(X_CHOOSE_THEN `h1:heap` (X_CHOOSE_THEN `h2:heap` STRIP_ASSUME_TAC)) THEN
  QPAT_X_ASSUM "cf_local cf H1 Q1" (MP_TAC o SPEC `h1:heap` o REWRITE_RULE[cf_local_def]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `H1':hprop` (X_CHOOSE_THEN `H2':hprop`
    (X_CHOOSE_THEN `Q1':res->hprop` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`H1':hprop`; `H2' STAR H2:hprop`; `Q1':res->hprop`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[STAR_ASSOC] THEN ONCE_REWRITE_TAC[STAR_def] THEN BETA_TAC THEN
    MAP_EVERY EXISTS_TAC [`h1:heap`; `h2:heap`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SEP_IMPPOST_def; STARPOST_def]) THEN
  REWRITE_TAC[SEP_IMPPOST_def; STARPOST_def] THEN X_GEN_TAC `r:res` THEN
  MATCH_MP_TAC SEP_IMP_TRANS THEN
  EXISTS_TAC `((Q1:res->hprop) r STAR H2) STAR cf_GC` THEN CONJ_TAC THENL
   [REWRITE_TAC[STAR_ASSOC] THEN MATCH_MP_TAC CF1AUX_STAR_GC_FRAME THEN
    ASM_REWRITE_TAC[];
    GEN_REWRITE_TAC RAND_CONV [GSYM CF1AUX_STAR_GC_GC] THEN
    ASM_SIMP_TAC[SEP_IMP_FRAME]]);;

let local_is_local = prove
 (`!HF. cf_is_local (cf_local HF) <=> T`,
  REWRITE_TAC[cf_is_local_def; local_local]);;

let is_local_prove = prove
 (`!HF. (!H Q. HF H Q <=> cf_local HF H Q) ==> cf_is_local HF`,
  REWRITE_TAC[cf_is_local_def; FUN_EQ_THM]);;

(* unfold the locality of a characteristic formula in the goal HF H Q *)
let CF1AUX_UNFOLD_LOCAL_TAC =
  REWRITE_TAC[cf_is_local_def] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> if is_eq(concl th) && is_var(lhs(concl th))
                          then ONCE_REWRITE_TAC[th] else failwith "") THEN
  REWRITE_TAC[cf_local_def] THEN X_GEN_TAC `h:heap` THEN DISCH_TAC;;

let local_frame_gc = prove
 (`!HF H H1 H2 Q1 Q.
     cf_is_local HF ==>
     HF H1 Q1 ==>
     H ==>> H1 STAR H2 ==>
     Q1 *+ H2 ==+> Q *+ cf_GC ==>
     HF H Q`,
  CF1AUX_UNFOLD_LOCAL_TAC THEN
  MAP_EVERY EXISTS_TAC [`H1:hprop`; `H2:hprop`; `Q1:res->hprop`] THEN
  ASM_MESON_TAC[SEP_IMP_def]);;

let local_frame = prove
 (`!H1 H2 Q1 HF H Q.
     cf_is_local HF ==>
     HF H1 Q1 ==>
     H ==>> H1 STAR H2 ==>
     Q1 *+ H2 ==+> Q ==>
     HF H Q`,
  CF1AUX_UNFOLD_LOCAL_TAC THEN
  MAP_EVERY EXISTS_TAC [`H1:hprop`; `H2:hprop`; `Q1:res->hprop`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_MESON_TAC[SEP_IMP_def]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SEP_IMPPOST_def; STARPOST_def]) THEN
  REWRITE_TAC[SEP_IMPPOST_def; STARPOST_def] THEN
  ASM_MESON_TAC[SEP_IMP_TRANS; CF1AUX_SEP_IMP_GC_R]);;

let local_gc_pre_on = prove
 (`!HG H' HF H Q.
     cf_is_local HF ==>
     H ==>> HG STAR H' ==>
     HF H' Q ==>
     HF H Q`,
  CF1AUX_UNFOLD_LOCAL_TAC THEN
  MAP_EVERY EXISTS_TAC [`H':hprop`; `HG:hprop`; `Q:res->hprop`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[STAR_COMM] THEN ASM_MESON_TAC[SEP_IMP_def];
    REWRITE_TAC[SEP_IMPPOST_def; STARPOST_def] THEN GEN_TAC THEN
    MATCH_MP_TAC SEP_IMP_STAR THEN REWRITE_TAC[SEP_IMP_REFL; hsimpl_gc]]);;

let local_gc_post = prove
 (`!Q' HF H Q.
     cf_is_local HF ==>
     HF H Q' ==>
     Q' ==+> Q *+ cf_GC ==>
     HF H Q`,
  CF1AUX_UNFOLD_LOCAL_TAC THEN
  MAP_EVERY EXISTS_TAC [`H:hprop`; `set_sep_cond T:hprop`; `Q':res->hprop`] THEN
  ASM_REWRITE_TAC[SEP_CLAUSES; STARPOST_emp]);;

(* Extraction of premisses from [local] *)

let local_intro_prop = prove
 (`!HF H P Q.
     cf_is_local HF ==>
     (P ==> HF H Q) ==>
     HF (H STAR set_sep_cond P) Q`,
  CF1AUX_UNFOLD_LOCAL_TAC THEN
  MAP_EVERY EXISTS_TAC [`H:hprop`; `set_sep_emp:hprop`; `Q:res->hprop`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[cond_STAR]) THEN
  ASM_SIMP_TAC[SEP_CLAUSES; STARPOST_emp; CF1AUX_STARPOST_GC_R]);;

(* Extraction of existentials from [local] *)

(* HOL4: A is a vacuous variable *)
let local_extract_exists = prove
 (`!HF (A:C) (J:B->hprop) Q.
     cf_is_local HF ==>
     (!x. HF (J x) Q) ==>
     HF ((SEP_EXISTS) J) Q`,
  CF1AUX_UNFOLD_LOCAL_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `x:B` o REWRITE_RULE[SEP_EXISTS]) THEN
  MAP_EVERY EXISTS_TAC [`(J:B->hprop) x`; `set_sep_emp:hprop`; `Q:res->hprop`] THEN
  ASM_REWRITE_TAC[SEP_CLAUSES; STARPOST_emp; CF1AUX_STARPOST_GC_R]);;

(* Auxiliary lemmas for [hclean]. Mostly repackaging of previous lemmas *)

let hclean_prop = prove
 (`!HF H P Q.
     cf_is_local HF /\
     (P ==> HF H Q) ==>
     HF (H STAR set_sep_cond P) Q`,
  MESON_TAC[local_intro_prop]);;

let hclean_prop_single = prove
 (`!HF P Q.
     cf_is_local HF /\
     (P ==> HF set_sep_emp Q) ==>
     HF (set_sep_cond P) Q`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`HF:hprop->(res->hprop)->bool`; `set_sep_emp:hprop`] local_intro_prop) THEN
  REWRITE_TAC[SEP_CLAUSES] THEN MESON_TAC[]);;

let hclean_exists_single = prove
 (`!HF (A:C) (J:B->hprop) Q.
     cf_is_local HF /\
     (!x. HF (J x) Q) ==>
     HF ((SEP_EXISTS) J) Q`,
  MESON_TAC[local_extract_exists]);;
