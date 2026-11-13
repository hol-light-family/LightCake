(* ========================================================================= *)
(* fmsp: port of HOL4 src/transfer/examples/fmspScript.sml (HOL4 library    *)
(* used by CakeML v3479): the bridge between finite maps num |-> 'a and     *)
(* sptrees: the transfer relation FMSP and the conversions sp2fm, fm2sp.    *)
(*                                                                           *)
(* Notes: HOL4 defines fm2sp fm = ITFMAP insert fm LN; finite_map.ml has no *)
(* ITFMAP, so here fm2sp fm = fromAList (fmap_to_alist fm), the same        *)
(* function (both are well-formed sptrees with lookup k = FLOOKUP fm k;     *)
(* see fm2sp_thm, wf_fm2sp, lookup_fm2sp), and fm2sp_def states this        *)
(* definition.  HOL4 fm \\ k is fdomsub fm k (infix \\), ### is RPROD.      *)
(* HOL4 transfer$total is transfer_total (transfer.ml).  RRANGE_FMSP (only  *)
(* used by the transfer automation) is not ported.  Helper lemmas are      *)
(* LUNIFAUX_.                                                                *)
(* ========================================================================= *)

needs "hol4/vocab.ml";;
needs "hol4/finite_map.ml";;
needs "hol4/alist.ml";;
needs "hol4/sptree.ml";;
needs "hol4/transfer.ml";;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The transfer relation FMSP and its rules.                                 *)
(* ------------------------------------------------------------------------- *)

let FMSP_def = new_definition
  `FMSP (AN:A->num->bool) (BC:B->C->bool) fm sp <=>
     wf sp /\ !a n. AN a n ==> OPTREL BC (FLOOKUP fm a) (lookup n sp)`;;

let FMSP_FDOM = prove
 (`!(AN:A->num->bool) (BC:B->C->bool).
     (FMSP AN BC |==> (AN |==> (<=>))) FDOM domain`,
  REWRITE_TAC[FMSP_def; FUN_REL_def] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a':A`; `b':num`]) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `FDOM (a:(A,B)fmap) a' <=> a' IN FDOM a` SUBST1_TAC THENL
   [REWRITE_TAC[IN]; ALL_TAC] THEN
  SUBGOAL_THEN `domain (b:C spt) b' <=> b' IN domain b` SUBST1_TAC THENL
   [REWRITE_TAC[IN]; ALL_TAC] THEN
  REWRITE_TAC[FDOM_FLOOKUP; domain_lookup] THEN
  CASES_ON `FLOOKUP (a:(A,B)fmap) a'` THEN
  CASES_ON `lookup b' (b:C spt)` THEN
  REWRITE_TAC[OPTREL_THM; option_DISTINCT; option_INJ] THEN MESON_TAC[]);;

let FMSP_FEMPTY = prove
 (`!(AN:A->num->bool) (BC:B->C->bool). FMSP AN BC FEMPTY LN`,
  REWRITE_TAC[FMSP_def; wf_LN; FLOOKUP_EMPTY; lookup_rwts; OPTREL_THM]);;

let FMSP_FUPDATE = prove
 (`!(AN:A->num->bool) (BC:B->C->bool).
     bi_unique AN ==>
     (FMSP AN BC |==> (AN ### BC) |==> FMSP AN BC)
       FUPDATE (\sp (n,v). insert n v sp)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[bi_unique_def; left_unique_def; right_unique_def] THEN
  STRIP_TAC THEN REWRITE_TAC[FUN_REL_def; FORALL_PAIR_THM; PAIR_REL_THM] THEN
  REWRITE_TAC[FMSP_def] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[wf_insert] THEN
  REWRITE_TAC[FLOOKUP_UPDATE; lookup_insert] THEN
  ASM_CASES_TAC `(p1:A) = a'` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `(n:num) = p1'` SUBST1_TAC THENL
     [ASM_MESON_TAC[]; ASM_REWRITE_TAC[OPTREL_THM]];
    SUBGOAL_THEN `~((n:num) = p1')` (fun th -> ASM_REWRITE_TAC[th]) THENL
     [ASM_MESON_TAC[]; ASM_MESON_TAC[]]]);;

let FMSP_total = prove
 (`!(AN:A->num->bool) (BC:B->C->bool).
     transfer_total AN /\ transfer_total BC /\ bi_unique AN
     ==> transfer_total (FMSP AN BC)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[transfer_total_def] THEN
  MATCH_MP_TAC fmap_INDUCT THEN CONJ_TAC THENL
   [MESON_TAC[FMSP_FEMPTY]; ALL_TAC] THEN
  X_GEN_TAC `fm:(A,B)fmap` THEN
  DISCH_THEN(X_CHOOSE_TAC `sp:C spt`) THEN
  MAP_EVERY X_GEN_TAC [`k:A`; `v:B`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `?n:num. AN (k:A) n` (X_CHOOSE_TAC `n:num`) THENL
   [ASM_MESON_TAC[transfer_total_def]; ALL_TAC] THEN
  SUBGOAL_THEN `?c:C. BC (v:B) c` (X_CHOOSE_TAC `c:C`) THENL
   [ASM_MESON_TAC[transfer_total_def]; ALL_TAC] THEN
  EXISTS_TAC `insert n (c:C) sp` THEN
  MP_TAC(SPECL [`AN:A->num->bool`; `BC:B->C->bool`] FMSP_FUPDATE) THEN
  ASM_REWRITE_TAC[FUN_REL_def; FORALL_PAIR_THM; PAIR_REL_THM] THEN
  DISCH_THEN(MP_TAC o SPECL [`fm:(A,B)fmap`; `sp:C spt`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`k:A`; `v:B`; `n:num`; `c:C`]) THEN
  ASM_REWRITE_TAC[]);;

let FMSP_FUNION = prove
 (`!(AN:A->num->bool) (BC:B->C->bool).
     (FMSP AN BC |==> FMSP AN BC |==> FMSP AN BC) FUNION union`,
  REWRITE_TAC[FUN_REL_def; FMSP_def] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[wf_union] THEN REWRITE_TAC[FLOOKUP_FUNION; lookup_union] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a'':A`; `n:num`]) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a'':A`; `n:num`]) THEN
  ASM_REWRITE_TAC[] THEN
  CASES_ON `FLOOKUP (a:(A,B)fmap) a''` THEN
  CASES_ON `lookup n (b:C spt)` THEN
  REWRITE_TAC[OPTREL_THM; option_CASE] THEN MESON_TAC[]);;

let FMSP_FDOMSUB = prove
 (`!(AN:A->num->bool) (BC:B->C->bool).
     bi_unique AN ==>
     (FMSP AN BC |==> AN |==> FMSP AN BC) fdomsub (flip delete)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[bi_unique_def; left_unique_def; right_unique_def] THEN
  STRIP_TAC THEN REWRITE_TAC[FUN_REL_def; FMSP_def; flip_DEF] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[wf_delete] THEN
  REWRITE_TAC[DOMSUB_FLOOKUP_THM; lookup_delete] THEN
  ASM_CASES_TAC `(a':A) = a''` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `(n:num) = b'` SUBST1_TAC THENL
     [ASM_MESON_TAC[]; REWRITE_TAC[OPTREL_THM]];
    SUBGOAL_THEN `~((n:num) = b')` (fun th -> ASM_REWRITE_TAC[th]) THENL
     [ASM_MESON_TAC[]; ASM_MESON_TAC[]]]);;

let FMSP_LOOKUP = prove
 (`!(AN:A->num->bool) (BC:B->C->bool).
     (FMSP AN BC |==> AN |==> OPTREL BC) FLOOKUP (flip lookup)`,
  REWRITE_TAC[FUN_REL_def; FMSP_def; flip_DEF] THEN MESON_TAC[]);;

let FMSP_EQ = prove
 (`!(AN:A->num->bool) (BC:B->C->bool).
     bi_unique AN /\ bitotal AN /\ bi_unique BC ==>
     (FMSP AN BC |==> FMSP AN BC |==> (<=>)) (=) (=)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bi_unique_def; bitotal_def] THEN STRIP_TAC THEN
  REWRITE_TAC[FUN_REL_def; FMSP_def] THEN
  MAP_EVERY X_GEN_TAC [`fm1:(A,B)fmap`; `sp1:C spt`] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`fm2:(A,B)fmap`; `sp2:C spt`] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[spt_eq_thm; FLOOKUP_EXT; FUN_EQ_THM] THEN EQ_TAC THENL
   [DISCH_TAC THEN X_GEN_TAC `n:num` THEN
    SUBGOAL_THEN `?k:A. AN k (n:num)` (X_CHOOSE_TAC `k:A`) THENL
     [ASM_MESON_TAC[surj_def]; ALL_TAC] THEN
    MP_TAC(ISPEC `BC:B->C->bool` OPTREL_right_unique) THEN
    ASM_REWRITE_TAC[right_unique_def] THEN DISCH_THEN MATCH_MP_TAC THEN
    EXISTS_TAC `FLOOKUP (fm1:(A,B)fmap) k` THEN ASM_MESON_TAC[];
    DISCH_TAC THEN X_GEN_TAC `k:A` THEN
    SUBGOAL_THEN `?n:num. AN (k:A) n` (X_CHOOSE_TAC `n:num`) THENL
     [ASM_MESON_TAC[transfer_total_def]; ALL_TAC] THEN
    MP_TAC(ISPEC `BC:B->C->bool` OPTREL_left_unique) THEN
    ASM_REWRITE_TAC[left_unique_def] THEN DISCH_THEN MATCH_MP_TAC THEN
    EXISTS_TAC `lookup n (sp1:C spt)` THEN ASM_MESON_TAC[]]);;

let total_eq = total_EQ;;
let bi_unique_eq = bi_unique_EQ;;
let surj_eq = surj_EQ;;

let left_unique_FMSP = prove
 (`!(AN:A->num->bool) (CD:B->C->bool).
     transfer_total AN /\ left_unique CD ==> left_unique (FMSP AN CD)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[left_unique_def; FMSP_def; FLOOKUP_EXT; FUN_EQ_THM] THEN
  MAP_EVERY X_GEN_TAC [`fm1:(A,B)fmap`; `fm2:(A,B)fmap`; `sp:C spt`] THEN
  STRIP_TAC THEN X_GEN_TAC `a:A` THEN
  SUBGOAL_THEN `?n:num. AN (a:A) n` (X_CHOOSE_TAC `n:num`) THENL
   [ASM_MESON_TAC[transfer_total_def]; ALL_TAC] THEN
  MP_TAC(ISPEC `CD:B->C->bool` OPTREL_left_unique) THEN
  ASM_REWRITE_TAC[left_unique_def] THEN DISCH_THEN MATCH_MP_TAC THEN
  EXISTS_TAC `lookup n (sp:C spt)` THEN ASM_MESON_TAC[]);;

let right_unique_FMSP = prove
 (`!(AN:A->num->bool) (CD:B->C->bool).
     surj AN /\ right_unique CD ==> right_unique (FMSP AN CD)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[right_unique_def; FMSP_def] THEN
  MAP_EVERY X_GEN_TAC [`fm:(A,B)fmap`; `sp1:C spt`; `sp2:C spt`] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[spt_eq_thm] THEN X_GEN_TAC `n:num` THEN
  SUBGOAL_THEN `?a:A. AN a (n:num)` (X_CHOOSE_TAC `a:A`) THENL
   [ASM_MESON_TAC[surj_def]; ALL_TAC] THEN
  MP_TAC(ISPEC `CD:B->C->bool` OPTREL_right_unique) THEN
  ASM_REWRITE_TAC[right_unique_def] THEN DISCH_THEN MATCH_MP_TAC THEN
  EXISTS_TAC `FLOOKUP (fm:(A,B)fmap) a` THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The conversions sp2fm and fm2sp.                                          *)
(* ------------------------------------------------------------------------- *)

let sp2fm_def = new_definition
  `sp2fm (sp:A spt) = FUN_FMAP (\k. THE (lookup k sp)) (domain sp)`;;

let FDOM_sp2fm = prove
 (`!sp:A spt. FDOM (sp2fm sp) = domain sp`,
  SIMP_TAC[sp2fm_def; FDOM_FMAP; FINITE_domain]);;

let FLOOKUP_sp2fm = prove
 (`!(sp:A spt) k. FLOOKUP (sp2fm sp) k = lookup k sp`,
  SIMP_TAC[sp2fm_def; FLOOKUP_FUN_FMAP; FINITE_domain] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[domain_lookup] THEN
  CASES_ON `lookup k (sp:A spt)` THEN
  REWRITE_TAC[option_DISTINCT; option_INJ; THE_DEF] THEN MESON_TAC[]);;

let sp2fm_thm = prove
 (`sp2fm (LN:A spt) = FEMPTY /\
   !k (v:A) sp. sp2fm (insert k v sp) = sp2fm sp |+ (k,v)`,
  REWRITE_TAC[FLOOKUP_EXT; FUN_EQ_THM; FLOOKUP_sp2fm; FLOOKUP_EMPTY;
              FLOOKUP_UPDATE; lookup_insert; lookup_rwts] THEN
  MESON_TAC[]);;

let sp2fm_correct = prove
 (`!(fm:(num,A)fmap) sp. FMSP (=) (=) fm sp <=> wf sp /\ fm = sp2fm sp`,
  REWRITE_TAC[FMSP_def; OPTREL_eq; FLOOKUP_EXT; FUN_EQ_THM; FLOOKUP_sp2fm] THEN
  MESON_TAC[]);;

let fm2sp_def = new_definition
  `fm2sp (fm:(num,A)fmap) = fromAList (fmap_to_alist fm)`;;

let wf_fm2sp = prove
 (`!fm:(num,A)fmap. wf (fm2sp fm)`,
  REWRITE_TAC[fm2sp_def; wf_fromAList]);;

let lookup_fm2sp = prove
 (`!(fm:(num,A)fmap) k. lookup k (fm2sp fm) = FLOOKUP fm k`,
  REWRITE_TAC[fm2sp_def; lookup_fromAList; ALOOKUP_EQ_FLOOKUP]);;

let fm2sp_thm = prove
 (`fm2sp (FEMPTY:(num,A)fmap) = LN /\
   !(fm:(num,A)fmap) k v. fm2sp (fm |+ (k,v)) = insert k v (fm2sp (fm \\ k))`,
  SIMP_TAC[spt_eq_thm; wf_fm2sp; wf_LN; wf_insert; lookup_fm2sp; lookup_rwts;
           FLOOKUP_EMPTY; lookup_insert; FLOOKUP_UPDATE; DOMSUB_FLOOKUP_THM] THEN
  MESON_TAC[]);;

let fm2sp_sp2fm = prove
 (`!sp:A spt. wf sp ==> fm2sp (sp2fm sp) = sp`,
  SIMP_TAC[spt_eq_thm; wf_fm2sp; lookup_fm2sp; FLOOKUP_sp2fm]);;

let sp2fm_fm2sp = prove
 (`!fm:(num,A)fmap. sp2fm (fm2sp fm) = fm`,
  REWRITE_TAC[FLOOKUP_EXT; FUN_EQ_THM; FLOOKUP_sp2fm; lookup_fm2sp]);;

let fm2sp_DOMSUB = prove
 (`!(fm:(num,A)fmap) k. fm2sp (fm \\ k) = delete k (fm2sp fm)`,
  SIMP_TAC[spt_eq_thm; wf_fm2sp; wf_delete; lookup_fm2sp; lookup_delete;
           DOMSUB_FLOOKUP_THM] THEN
  MESON_TAC[]);;

let _ = cake_add_simps
  [FDOM_sp2fm; FLOOKUP_sp2fm; sp2fm_thm; fm2sp_thm; wf_fm2sp; lookup_fm2sp;
   fm2sp_sp2fm; sp2fm_fm2sp];;
