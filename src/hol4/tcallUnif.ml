(* ========================================================================= *)
(* tcallUnif: port of HOL4 examples/algorithms/unification/triangular/      *)
(* first-order/compilation/tcallUnifScript.sml (HOL4 library used by CakeML *)
(* v3479): the case-distribution lemmas, the tail-recursive walk (tvwalk,   *)
(* twalk) and the worklist occurs check (tocwl) with their correctness, and *)
(* the bag and rangevars lemmas that CakeML's unify uses for its own        *)
(* tail-recursive unifier.                                                   *)
(*                                                                           *)
(* Notes:                                                                    *)
(* - HOL4 BAG_OF_LIST is an overload of FOLDR BAG_INSERT EMPTY_BAG; here it *)
(*   is a constant, BAG_OF_LIST l = ITLIST BAG_INSERT l EMPTY_BAG            *)
(*   (BAG_OF_LIST_def), with the list equations BAG_OF_LIST_THM.             *)
(* - HOL4 TAILCALL/TAILREC are basic.ml's; the code of tvwalk is written in *)
(*   tvwalk_def (HOL4 keeps it in the ML value svwalk_code).  tvwalk_thm and *)
(*   tvwalk_correct are proved directly (HOL4 uses                           *)
(*   TAILREC_GUARD_ELIMINATION).                                             *)
(* - sum_CASE_list_CASE and option_CASE_MAP are tcallUnif_sum_CASE_list_CASE *)
(*   and tcallUnif_option_CASE_MAP (CakeML's unify has theorems of these     *)
(*   names).                                                                 *)
(* - The occurs check worklist tocwl is defined with HOL4's code and        *)
(*   tocwl_correct, disj_oc are proved by well-founded induction on the bag *)
(*   order (HOL4 goes through the continuation forms koc, apply_ockont and   *)
(*   kocwl, derived with cpsLib automation; those are not ported).           *)
(* - Not ported (not used by the CakeML closure; HOL4 derives most of them   *)
(*   with cpsLib automation): koc, apply_ockont, dfkoc, kocwl, kunify,       *)
(*   apply_unifkont, dfkunify, kunifywl, ucode, kuR, the worklist unifier    *)
(*   tunifywl and their theorems.  Helper lemmas are LUNIFAUX_.             *)
(* ========================================================================= *)

needs "hol4/vocab.ml";;
needs "hol4/bag.ml";;
needs "hol4/cps.ml";;
needs "hol4/rmfmap.ml";;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Term predicates and destructors; contify and sum_CASE distribution.       *)
(* ------------------------------------------------------------------------- *)

let ispair_def = cake_def
  `(ispair (Pair (t1:A term_term) t2) <=> T) /\
   (ispair (term_Var v:A term_term) <=> F) /\
   (ispair (Const (c:A)) <=> F)`;;

let isconst_def = cake_def
  `(isconst (Const (c:A)) <=> T) /\
   (isconst (term_Var v:A term_term) <=> F) /\
   (isconst (Pair (c1:A term_term) c2) <=> F)`;;

let destpair_def = cake_def
  `destpair (Pair (c1:A term_term) c2) = (c1,c2)`;;

let destvar_def = cake_def
  `destvar (term_Var v:A term_term) = v`;;

let contify_optbind = prove
 (CASE_TERM `!(k:B option->C) (opt:A option) f.
     contify k (OPTION_BIND opt f) =
     contify (\ov. match ov with NONE -> k NONE | SOME x -> contify k (f x)) opt`,
  REPEAT GEN_TAC THEN REWRITE_TAC[contify_def] THEN
  STRUCT_CASES_TAC(ISPEC `opt:A option` (cases "option")) THEN
  REWRITE_TAC[option_CASE; OPTION_BIND_DEF]);;

let contify_term_case = prove
 (CASE_TERM `!(k:B->C) (t:A term_term) v p c.
     contify k (term_term_CASE t v p c) =
     contify (\t. match t with term_Var n -> contify k (v n)
                             | Pair t1 t2 -> contify k (p t1 t2)
                             | Const cn -> contify k (c cn)) t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[contify_def] THEN
  STRUCT_CASES_TAC(ISPEC `t:A term_term` term_term_nchotomy) THEN
  REWRITE_TAC[term_term_CASE]);;

let sum_CASE_pair_CASE = prove
 (`!(p:A#B) (f:A->B->C+D) (lf:C->E) rf.
     sum_CASE (pair_CASE p f) lf rf = pair_CASE p (\a b. sum_CASE (f a b) lf rf)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `p:A#B` PAIR_SURJECTIVE) THEN REWRITE_TAC[pair_CASE]);;

let sum_CASE_term_CASE = prove
 (`!(t:A term_term) (vf:num->B+C) pf cf (lf:B->D) rf.
     sum_CASE (term_term_CASE t vf pf cf) lf rf =
     term_term_CASE t (\v. sum_CASE (vf v) lf rf)
                      (\t1 t2. sum_CASE (pf t1 t2) lf rf)
                      (\cn. sum_CASE (cf cn) lf rf)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `t:A term_term` term_term_nchotomy) THEN
  REWRITE_TAC[term_term_CASE]);;

let sum_CASE_COND = prove
 (`!p (t:A+B) e (lf:A->C) rf.
     sum_CASE (if p then t else e) lf rf =
     if p then sum_CASE t lf rf else sum_CASE e lf rf`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[]);;

let sum_CASE_option_CASE = prove
 (`!(ov:A option) (n:B+C) sf (lf:B->D) rf.
     sum_CASE (option_CASE ov n sf) lf rf =
     option_CASE ov (sum_CASE n lf rf) (\v. sum_CASE (sf v) lf rf)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `ov:A option` (cases "option")) THEN
  REWRITE_TAC[option_CASE]);;

let tcallUnif_sum_CASE_list_CASE = prove
 (`!(k:A list) (i:B+C) tkf (lf:B->D) rf.
     sum_CASE (list_CASE k i tkf) lf rf =
     list_CASE k (sum_CASE i lf rf) (\t k. sum_CASE (tkf t k) lf rf)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `k:A list` list_CASES) THEN REWRITE_TAC[list_CASE]);;

(* ------------------------------------------------------------------------- *)
(* The tail-recursive walk.                                                  *)
(* ------------------------------------------------------------------------- *)

let tvwalk_def = new_definition (CASE_TERM
  `tvwalk (s:(A term_term)spt) nm =
   TAILREC (\(s:(A term_term)spt,nm:num). match lookup nm s with
              NONE -> (INR (term_Var nm):((A term_term)spt#num)+A term_term)
            | SOME (term_Var nm') -> INL (s,nm')
            | SOME (Pair t1 t2) -> INR (Pair t1 t2)
            | SOME (Const c) -> INR (Const c)) (s,nm)`);;

let tvwalk_thm = prove
 (CASE_TERM `!(s:(A term_term)spt) nm.
     tvwalk s nm =
     (match lookup nm s with
        NONE -> term_Var nm
      | SOME (term_Var nm') -> tvwalk s nm'
      | SOME (Pair t1 t2) -> Pair t1 t2
      | SOME (Const c) -> Const c)`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [tvwalk_def] THEN
  GEN_REWRITE_TAC LAND_CONV [TAILREC] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[sum_CASE_option_CASE; sum_CASE_term_CASE; sum_CASE] THEN
  REWRITE_TAC[GSYM tvwalk_def]);;

let tvwalk_correct = prove
 (`!(s:(A term_term)spt) nm. swfs s /\ sptree_wf s ==> svwalk s nm = tvwalk s nm`,
  GEN_TAC THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `wfs (sp2fm (s:(A term_term)spt))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM swfs_def]; ALL_TAC] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP vwalk_ind) THEN
  X_GEN_TAC `nm:num` THEN REWRITE_TAC[FLOOKUP_sp2fm] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`s:(A term_term)spt`; `nm:num`] svwalk_thm) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [tvwalk_thm] THEN
  CASES_ON `lookup nm (s:(A term_term)spt)` THEN REWRITE_TAC[option_CASE] THEN
  CASES_ON `a:A term_term` THEN REWRITE_TAC[term_term_CASE] THEN
  ASM_MESON_TAC[]);;

let twalk_def = cake_def
  `twalk (s:(A term_term)spt) t =
     match t with term_Var v -> tvwalk s v | Pair t1 t2 -> Pair t1 t2
                | Const c -> Const c`;;

let twalk_correct = prove
 (`!(s:(A term_term)spt) t. swfs s /\ sptree_wf s ==> swalk s t = twalk s t`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[swalk_thm; twalk_def] THEN
  CASES_ON `t:A term_term` THEN REWRITE_TAC[term_term_CASE] THEN
  ASM_SIMP_TAC[tvwalk_correct]);;

(* ------------------------------------------------------------------------- *)
(* Bags of lists, rangevars and option_CASE distribution.                    *)
(* ------------------------------------------------------------------------- *)

let BAG_OF_LIST_def = new_definition
  `BAG_OF_LIST (l:A list) = ITLIST BAG_INSERT l EMPTY_BAG`;;

let BAG_OF_LIST_THM = prove
 (`BAG_OF_LIST ([]:A list) = EMPTY_BAG /\
   !(h:A) t. BAG_OF_LIST (CONS h t) = BAG_INSERT h (BAG_OF_LIST t)`,
  REWRITE_TAC[BAG_OF_LIST_def; ITLIST]);;

let LUNIFAUX_BAG_OF_LIST_LIST_TO_BAG = prove
 (`!l:A list. BAG_OF_LIST l = LIST_TO_BAG l`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[BAG_OF_LIST_THM; LIST_TO_BAG_def]);;

let FINITE_BAG_OF_LIST = prove
 (`!l:A list. FINITE_BAG (BAG_OF_LIST l)`,
  REWRITE_TAC[LUNIFAUX_BAG_OF_LIST_LIST_TO_BAG; FINITE_LIST_TO_BAG]);;

let BAG_OF_SUM = cake_def
  `(BAG_OF_SUM (INL (t,k):(A#A list)+(A list#B)) = BAG_OF_LIST (CONS t k)) /\
   (BAG_OF_SUM (INR (k,b)) = BAG_OF_LIST k)`;;

let mlt1_BAG_INSERT = prove
 (`!(R:A->A->bool) b e. FINITE_BAG b ==> mlt1 R b (BAG_INSERT e b)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[mlt1_def; FINITE_BAG_THM] THEN
  MAP_EVERY EXISTS_TAC [`e:A`; `EMPTY_BAG:A->num`; `b:A->num`] THEN
  REWRITE_TAC[BAG_UNION_EMPTY; NOT_IN_EMPTY_BAG; BAG_UNION_INSERT]);;

let vwalk_rangevars = prove
 (`!(s:(num,A term_term)fmap) v t.
     wfs s /\ vwalk s v = t
     ==> t = term_Var v /\ ~(v IN FDOM s) \/ term_vars t SUBSET rangevars s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `(v:num) IN FDOM (s:(num,A term_term)fmap)` THENL
   [DISJ2_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
    MATCH_MP_TAC IN_FRANGE_rangevars THEN ASM_MESON_TAC[vwalk_IN_FRANGE];
    DISJ1_TAC THEN ASM_MESON_TAC[NOT_FDOM_vwalk]]);;

let walk_rangevars = prove
 (`!(s:(num,A term_term)fmap) t u.
     wfs s /\ walk s t = u ==> term_vars u SUBSET rangevars s UNION term_vars t`,
  MESON_TAC[LUNIFAUX_walk_rangevars]);;

let substvars_FUPDATE = prove
 (`!(fm:(num,A term_term)fmap) v t.
     substvars (fm |+ (v,t)) = (substvars (fm \\ v) UNION {v}) UNION term_vars t`,
  REWRITE_TAC[substvars_def; EXTENSION; IN_UNION; LUNIFAUX_IN_rangevars;
              FDOM_FUPDATE; FDOM_DOMSUB; IN_INSERT; IN_DELETE; IN_SING;
              FAPPLY_FUPDATE_THM; DOMSUB_FAPPLY_THM] THEN
  MESON_TAC[]);;

let tcallUnif_option_CASE_MAP = prove
 (`!(f:A->B) x (n:C) sf.
     option_CASE (OPTION_MAP f x) n sf = option_CASE x n (sf o f)`,
  GEN_TAC THEN MATCH_MP_TAC option_INDUCT THEN
  REWRITE_TAC[OPTION_MAP_DEF; option_CASE; o_THM]);;

let option_CASE_term_CASE = prove
 (`!(t:A term_term) (vf:num->B option) pf cf (n:C) sf.
     option_CASE (term_term_CASE t vf pf cf) n sf =
     term_term_CASE t (\v. option_CASE (vf v) n sf)
                      (\t1 t2. option_CASE (pf t1 t2) n sf)
                      (\c. option_CASE (cf c) n sf)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `t:A term_term` term_term_nchotomy) THEN
  REWRITE_TAC[term_term_CASE]);;

let option_CASE_COND = prove
 (`!g (t:A option) e (n:B) sf.
     option_CASE (if g then t else e) n sf =
     if g then option_CASE t n sf else option_CASE e n sf`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[]);;

let twalk_to_var = prove
 (`!(s:(A term_term)spt) t v.
     swfs s /\ sptree_wf s /\ twalk s t = term_Var v ==>
     ~(v IN domain s) /\ ?u. t = term_Var u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`sp2fm (s:(A term_term)spt)`; `t:A term_term`; `v:num`]
               walk_to_var) THEN
  ASM_REWRITE_TAC[GSYM swfs_def; GSYM swalk_def; FDOM_sp2fm] THEN
  ASM_SIMP_TAC[twalk_correct]);;

(* ------------------------------------------------------------------------- *)
(* The occurs check as a worklist loop.                                      *)
(* ------------------------------------------------------------------------- *)

let tocwl_def = new_definition (CASE_TERM
  `tocwl (s:(A term_term)spt) v k =
   TAILREC (\(s:(A term_term)spt,k:(A term_term)list). match k with
              [] -> (INR F:((A term_term)spt#(A term_term)list)+bool)
            | CONS t k ->
                (match twalk s t with
                   term_Var n -> if v = n then INR T else INL (s,k)
                 | Pair t1 t2 -> INL (s,CONS t1 (CONS t2 k))
                 | Const _ -> INL (s,k))) (s,k)`);;

let tocwl_thm = prove
 (CASE_TERM `!(s:(A term_term)spt) v k.
     tocwl s v k <=>
     (match k with
        [] -> F
      | CONS t k ->
          (match twalk s t with
             term_Var n -> if v = n then T else tocwl s v k
           | Pair t1 t2 -> tocwl s v (CONS t1 (CONS t2 k))
           | Const _ -> tocwl s v k))`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [tocwl_def] THEN
  GEN_REWRITE_TAC LAND_CONV [TAILREC] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[tcallUnif_sum_CASE_list_CASE; sum_CASE_term_CASE; sum_CASE_COND;
              sum_CASE] THEN
  REWRITE_TAC[GSYM tocwl_def]);;

let ocR_def = new_definition
  `ocR (s:(A term_term)spt) =
     inv_image (RPROD (=) (mlt1 (walkstarR (sp2fm s))))
               (\(s:(A term_term)spt,k:(A term_term)list). (s,BAG_OF_LIST k))`;;

let WF_ocR = prove
 (`!s:(A term_term)spt. swfs s ==> WF (ocR s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ocR_def] THEN MATCH_MP_TAC WF_inv_image THEN
  MATCH_MP_TAC WF_SUBSET THEN
  EXISTS_TAC `inv_image (mlt1 (walkstarR (sp2fm (s:(A term_term)spt))))
                        (SND:(A term_term)spt#(A term_term->num)->(A term_term->num))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[FORALL_PAIR_THM; PAIR_REL_THM; inv_image_THM] THEN MESON_TAC[];
    MATCH_MP_TAC WF_inv_image THEN MATCH_MP_TAC WF_mlt1 THEN
    MATCH_MP_TAC walkstar_thWF THEN ASM_REWRITE_TAC[GSYM swfs_def]]);;

let RTC_ocR_preserves_subst = prove
 (`!(s0:(A term_term)spt) s1 s2 x y. RTC (ocR s0) (s1,x) (s2,y) ==> s1 = s2`,
  GEN_TAC THEN
  SUBGOAL_THEN `!p q. RTC (ocR (s0:(A term_term)spt)) p q ==> FST p = FST q`
    (fun th -> MESON_TAC[th; FST]) THEN
  MATCH_MP_TAC RTC_INDUCT THEN
  REWRITE_TAC[FORALL_PAIR_THM; ocR_def; inv_image_THM; PAIR_REL_THM] THEN
  MESON_TAC[]);;

let LUNIFAUX_mlt1_tail = prove
 (`!(R:A->A->bool) h t. mlt1 R (BAG_OF_LIST t) (BAG_OF_LIST (CONS h t))`,
  REWRITE_TAC[BAG_OF_LIST_THM] THEN MESON_TAC[mlt1_BAG_INSERT; FINITE_BAG_OF_LIST]);;

let LUNIFAUX_tocwl_EX = prove
 (`!(s:(A term_term)spt) v. swfs s /\ sptree_wf s ==>
      !k. tocwl s v k <=> EX (\t. soc s t v) k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
    `WF (inv_image (mlt1 (walkstarR (sp2fm (s:(A term_term)spt))))
                   (BAG_OF_LIST:(A term_term)list->(A term_term->num)))`
    MP_TAC THENL
   [MATCH_MP_TAC WF_inv_image THEN MATCH_MP_TAC WF_mlt1 THEN
    MATCH_MP_TAC walkstar_thWF THEN ASM_REWRITE_TAC[GSYM swfs_def];
    ALL_TAC] THEN
  REWRITE_TAC[WF_IND; inv_image_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
  X_GEN_TAC `k:(A term_term)list` THEN DISCH_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [tocwl_thm] THEN
  CASES_ON `k:(A term_term)list` THEN REWRITE_TAC[list_CASE; EX] THEN
  SUBGOAL_THEN `twalk s (a0:A term_term) = swalk s a0` SUBST1_TAC THENL
   [ASM_MESON_TAC[twalk_correct]; ALL_TAC] THEN
  MP_TAC(SPECL [`s:(A term_term)spt`; `a0:A term_term`; `v:num`] soc_walking) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  CASES_ON `swalk s (a0:A term_term)` THEN REWRITE_TAC[term_term_CASE] THENL
   [SUBGOAL_THEN `tocwl s v (a1:(A term_term)list) <=> EX (\t. soc s t v) a1`
      SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[LUNIFAUX_mlt1_tail];
      COND_CASES_TAC THEN ASM_REWRITE_TAC[]];
    SUBGOAL_THEN `walk (sp2fm (s:(A term_term)spt)) a0 = Pair a0' a1'`
      ASSUME_TAC THENL [ASM_REWRITE_TAC[GSYM swalk_def]; ALL_TAC] THEN
    SUBGOAL_THEN `wfs (sp2fm (s:(A term_term)spt))` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[GSYM swfs_def]; ALL_TAC] THEN
    FIRST_X_ASSUM(fun th -> W(fun (_,w) -> MP_TAC(SPEC (rand(lhand w)) th))) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[BAG_OF_LIST_THM; mlt1_def; FINITE_BAG_THM; FINITE_BAG_OF_LIST] THEN
      MAP_EVERY EXISTS_TAC
       [`a0:A term_term`;
        `BAG_INSERT (a0':A term_term) (BAG_INSERT a1' EMPTY_BAG)`;
        `BAG_OF_LIST (a1:(A term_term)list)`] THEN
      REWRITE_TAC[BAG_UNION_INSERT; BAG_UNION_EMPTY; BAG_IN_BAG_INSERT;
                  NOT_IN_EMPTY_BAG] THEN
      ASM_MESON_TAC[walkstar_th1; walkstar_th2];
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[EX; DISJ_ASSOC]];
    FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[LUNIFAUX_mlt1_tail]]);;

let tocwl_correct = prove
 (`!(s:(A term_term)spt) t v. swfs s /\ sptree_wf s ==> (soc s t v <=> tocwl s v [t])`,
  SIMP_TAC[LUNIFAUX_tocwl_EX; EX]);;

let disj_oc = prove
 (`!(s:(A term_term)spt) t1 t2 v.
     swfs s /\ sptree_wf s ==> (soc s t1 v \/ soc s t2 v <=> tocwl s v [t1; t2])`,
  SIMP_TAC[LUNIFAUX_tocwl_EX; EX]);;

let _ = cake_add_simps
  [ispair_def; isconst_def; destpair_def; destvar_def; BAG_OF_LIST_THM;
   FINITE_BAG_OF_LIST; BAG_OF_SUM];;
