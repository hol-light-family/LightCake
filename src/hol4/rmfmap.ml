(* ========================================================================= *)
(* rmfmap: port of HOL4 examples/algorithms/unification/triangular/         *)
(* first-order/compilation/rmfmapScript.sml (HOL4 library used by CakeML    *)
(* v3479): unification over sptrees instead of finite maps (sunify, swalk,  *)
(* svwalk, soc, swfs), with the characterising theorems in sptree form.     *)
(*                                                                           *)
(* How the theorems were obtained: HOL4 derives svR_thm, svwalk_thm,        *)
(* swalk_thm, soc_thm, soc_walking and sunify_thm with transferLib (xfer)   *)
(* from vR_def, vwalk_def, walk_def, oc_thm, oc_walking and unify_def.  The *)
(* transfer automation is not ported: the same statements (the sptree      *)
(* variable carries the hypothesis sptree_wf sp that the transfer adds) are proved *)
(* directly from the definitions and fmsp.ml.                               *)
(*                                                                           *)
(* Notes: HOL4 term_CASE is term_term_CASE (term.ml); term_CASE_CONG and    *)
(* term_CASE_EQCONG keep their HOL4 names.  The sptree type 'a term num_map *)
(* is (A term_term)spt.                                                      *)
(* ========================================================================= *)

needs "hol4/vocab.ml";;
needs "hol4/transfer.ml";;
needs "hol4/fmsp.ml";;
needs "hol4/unifDef.ml";;

type_invention_error := true;;

let FUNREL_flipR = prove
 (`!(AB:A->B->bool) (CD:C->D->bool) (EF:E->F->bool) f g.
     (AB |==> CD |==> EF) f (flip g) <=> (CD |==> AB |==> EF) (flip f) g`,
  REWRITE_TAC[FUN_REL_def; flip_DEF] THEN MESON_TAC[]);;

let TERMREL_def = cake_def
  `(TERMREL (AB:A->B->bool) (term_Var n) t <=> t = term_Var n) /\
   (TERMREL AB (Pair t11 t12) t <=>
      ?t21 t22. t = Pair t21 t22 /\ TERMREL AB t11 t21 /\ TERMREL AB t12 t22) /\
   (TERMREL AB (Const c1) t <=> ?c2. AB c1 c2 /\ t = Const c2)`;;

let TERMREL_EQ = prove
 (`TERMREL ((=):A->A->bool) = (=)`,
  REWRITE_TAC[FUN_EQ_THM] THEN MATCH_MP_TAC term_term_INDUCT THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[TERMREL_def] THEN MESON_TAC[]);;

let term_CASE_CONG = prove
 (`!(AB:A->B->bool) (CD:C->D->bool).
     (TERMREL AB |==> ((=) |==> CD) |==>
      (TERMREL AB |==> TERMREL AB |==> CD) |==> (AB |==> CD) |==> CD)
     term_term_CASE term_term_CASE`,
  REWRITE_TAC[FUN_REL_def] THEN GEN_TAC THEN GEN_TAC THEN
  MATCH_MP_TAC term_term_INDUCT THEN
  REWRITE_TAC[TERMREL_def] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[term_term_CASE] THEN ASM_MESON_TAC[]);;

let term_CASE_EQCONG = prove
 (`!CD:C->D->bool.
     (((=):A term_term->A term_term->bool) |==>
      ((=) |==> CD) |==> ((=) |==> (=) |==> CD) |==> ((=) |==> CD) |==> CD)
     term_term_CASE term_term_CASE`,
  REWRITE_TAC[FUN_REL_def] THEN GEN_TAC THEN MATCH_MP_TAC term_term_INDUCT THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  REWRITE_TAC[term_term_CASE] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The sptree versions of vR, wfs, vwalk, walk, walkstar_oc and unify.       *)
(* ------------------------------------------------------------------------- *)

let svR_def = new_definition
  `svR (sp:(A term_term)spt) u v <=> subst_vR (sp2fm sp) u v`;;

let FMSP_rvR = prove
 (`(FMSP (=) (=) |==> (=) |==> (=) |==> (=))
     (subst_vR:(num,A term_term)fmap->num->num->bool) svR`,
  REWRITE_TAC[FUN_REL_def; sp2fm_correct; svR_def] THEN MESON_TAC[]);;

let svR_thm = prove
 (CASE_TERM `!(sp:(A term_term)spt) y x. sptree_wf sp ==>
     (svR sp y x <=> (match lookup x sp with SOME t -> y IN term_vars t | _ -> F))`,
  REWRITE_TAC[svR_def; subst_vR_def; FLOOKUP_sp2fm]);;

let swfs_def = new_definition
  `swfs (sp:(A term_term)spt) <=> wfs (sp2fm sp)`;;

let FMSP_wfs = prove
 (`(FMSP (=) (=) |==> (=)) (wfs:(num,A term_term)fmap->bool) swfs`,
  REWRITE_TAC[FUN_REL_def; sp2fm_correct; swfs_def] THEN MESON_TAC[]);;

let svwalk_def = new_definition
  `svwalk (sp:(A term_term)spt) t = vwalk (sp2fm sp) t`;;

let FMSP_vwalk = prove
 (`(FMSP (=) (=) |==> (=) |==> (=)) (vwalk:(num,A term_term)fmap->num->A term_term)
     svwalk`,
  REWRITE_TAC[FUN_REL_def; sp2fm_correct; svwalk_def] THEN MESON_TAC[]);;

let svwalk_thm = prove
 (CASE_TERM `!(sp:(A term_term)spt) v. sptree_wf sp /\ swfs sp ==>
     svwalk sp v =
     (match lookup v sp with SOME (term_Var u) -> svwalk sp u | SOME t -> t
                           | NONE -> term_Var v)`,
  REWRITE_TAC[swfs_def; svwalk_def] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [MATCH_MP vwalk_def th]) THEN
  REWRITE_TAC[FLOOKUP_sp2fm]);;

let swalk_def = new_definition
  `swalk (sp:(A term_term)spt) t = walk (sp2fm sp) t`;;

let FMSP_walk = prove
 (`(FMSP (=) (=) |==> (=) |==> (=))
     (walk:(num,A term_term)fmap->A term_term->A term_term) swalk`,
  REWRITE_TAC[FUN_REL_def; sp2fm_correct; swalk_def] THEN MESON_TAC[]);;

let swalk_thm = prove
 (CASE_TERM `!(sp:(A term_term)spt) t. sptree_wf sp ==>
     swalk sp t = (match t with term_Var v -> svwalk sp v | t -> t)`,
  REWRITE_TAC[swalk_def; svwalk_def; walk_def]);;

let soc_def = new_definition
  `soc (sp:(A term_term)spt) t v <=> walkstar_oc (sp2fm sp) t v`;;

let FMSP_oc = prove
 (`(FMSP (=) (=) |==> (=) |==> (=) |==> (=))
     (walkstar_oc:(num,A term_term)fmap->A term_term->num->bool) soc`,
  REWRITE_TAC[FUN_REL_def; sp2fm_correct; soc_def] THEN MESON_TAC[]);;

let soc_thm = prove
 (CASE_TERM `!(sp:(A term_term)spt) v x t1 t2 c. sptree_wf sp ==>
     (swfs sp ==>
      (soc sp (term_Var v) x <=>
       match svwalk sp v with
         term_Var u -> x = u
       | Pair t1 t2 -> soc sp t1 x \/ soc sp t2 x
       | _ -> F)) /\
     (soc sp (Pair t1 t2) v <=> soc sp t1 v \/ soc sp t2 v) /\
     ~soc sp (Const c) v`,
  REWRITE_TAC[swfs_def; soc_def; svwalk_def] THEN SIMP_TAC[oc_thm]);;

let soc_walking = prove
 (CASE_TERM `!(sp:(A term_term)spt) t v. sptree_wf sp /\ swfs sp ==>
     (soc sp t v <=>
      match swalk sp t with
        term_Var u -> v = u
      | Pair t1 t2 -> soc sp t1 v \/ soc sp t2 v
      | _ -> F)`,
  REWRITE_TAC[swfs_def; soc_def; swalk_def] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [MATCH_MP oc_walking th]) THEN
  REFL_TAC);;

let sunify_def = new_definition
  `sunify (sp:(A term_term)spt) t1 t2 = OPTION_MAP fm2sp (unifDef_unify (sp2fm sp) t1 t2)`;;

let FMSP_unify = prove
 (`(FMSP (=) (=) |==> (=) |==> (=) |==> OPTREL (FMSP (=) (=)))
     (unifDef_unify:(num,A term_term)fmap->A term_term->A term_term->
            ((num,A term_term)fmap)option) sunify`,
  REWRITE_TAC[FUN_REL_def; sp2fm_correct; sunify_def] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  CASES_ON `unifDef_unify (sp2fm (b:(A term_term)spt)) b' b''` THEN
  REWRITE_TAC[OPTION_MAP_DEF; OPTREL_THM; sp2fm_correct; wf_fm2sp;
              sp2fm_fm2sp]);;

let sunify_thm = prove
 (CASE_TERM `!(sp:(A term_term)spt) t1 t2. sptree_wf sp /\ swfs sp ==>
      sunify sp t1 t2 =
      (match (swalk sp t1, swalk sp t2) with
         (term_Var v1, term_Var v2) ->
           SOME (if v1 = v2 then sp else insert v1 (term_Var v2) sp)
       | (term_Var v1, t2) ->
           if soc sp t2 v1 then NONE else SOME (insert v1 t2 sp)
       | (t1, term_Var v2) ->
           if soc sp t1 v2 then NONE else SOME (insert v2 t1 sp)
       | (Pair t1a t1d, Pair t2a t2d) ->
           OPTION_BIND (sunify sp t1a t2a) (\sx. sunify sx t1d t2d)
       | (Const c1, Const c2) -> if c1 = c2 then SOME sp else NONE
       | _ -> NONE)`,
  REWRITE_TAC[swfs_def] THEN REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [sunify_def] THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
    [MATCH_MP unifDef_unify_def th]) THEN
  REWRITE_TAC[swalk_def; soc_def] THEN
  CASES_ON `walk (sp2fm (sp:(A term_term)spt)) t1` THEN
  CASES_ON `walk (sp2fm (sp:(A term_term)spt)) t2` THEN
  REWRITE_TAC[term_term_CASE; ext_s_check_def] THEN
  TRY COND_CASES_TAC THEN
  ASM_SIMP_TAC[OPTION_MAP_DEF; fm2sp_sp2fm; GSYM(CONJUNCT2 sp2fm_thm);
               wf_insert] THEN
  REWRITE_TAC[sunify_def] THEN
  CASES_ON `unifDef_unify (sp2fm (sp:(A term_term)spt)) a0 a0'` THEN
  REWRITE_TAC[OPTION_BIND_DEF; OPTION_MAP_DEF; sp2fm_fm2sp]);;
