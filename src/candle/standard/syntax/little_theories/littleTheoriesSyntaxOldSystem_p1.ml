(* ========================================================================= *)
(* littleTheoriesSyntaxOldSystem: port of HOL4 candle/standard/syntax/       *)
(* little_theories/littleTheoriesSyntaxOldSystemScript.sml (CakeML v3479).   *)
(* Some lemmas about the extended Little Theories syntactic functions.       *)
(* The theory is in seven consecutive parts, each loading the one before;    *)
(* littleTheoriesSyntaxOldSystem.ml loads them all.  Part 1 (HOL4 lines      *)
(* 1-1000): esubst_ty on variables and constants, REV_ASSOCD,                *)
(* VSUBST, NVARIANT, free variables, VSUBSTfm, esubst_ty0.                   *)
(*                                                                           *)
(* Notes on the rendering (all parts):                                       *)
(* - Names as doc/names.tsv says: proves_theory_ok is                        *)
(*   little_proves_theory_ok, FAPPLY_FLOOKUP is little_FAPPLY_FLOOKUP.  The  *)
(*   conventions of littleTheoriesSyntax.ml (see its header) hold here:      *)
(*   HOL4 Overloads written out, sigma and theta for the Greek letters,      *)
(*   record notation, proves' and nproves written prefix.                    *)
(* - The variable val of HOL4 (a constant of the words library here) is u.   *)
(* - The free variables of a HOL4 statement are quantified, after the        *)
(*   variables that HOL4 quantifies (in HOL4's order).                       *)
(* - HOL4 Theorem name = expr (a derived theorem) is let name = expr.        *)
(* - The HOL4 ML tactics strip_d1, strip_d2, contrapos_tac, drw, spec_impl   *)
(*   and rC are CLITAUX_strip_d1, ... (below); the others are defined where  *)
(*   HOL4 defines them, with the prefix CLITAUX_.                            *)
(* - Local helpers that are not HOL4 theorems are CLITAUX_.                  *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "basis/pure/mlstring.ml";;
needs "hol4/toto.ml";;
needs "hol4/comparison.ml";;
needs "hol4/ternaryComparisons.ml";;
needs "hol4/errorMonad.ml";;
needs "candle/syntax-lib/holSyntaxLib.ml";;
needs "candle/standard/syntax/holSyntax.ml";;
needs "candle/standard/syntax/holSyntaxExtra.ml";;
needs "candle/standard/syntax/holConservative.ml";;
needs "candle/standard/syntax/little_theories/littleTheoriesSyntax.ml";;

prioritize_num();;
type_invention_error := true;;

(* HOL4 val cpn_distinct and cpn_nchotomy are toto.ml's. *)

(* HOL4 strip_d1, strip_d2: a disjunctive goal as an implication *)
let CLITAUX_strip_d1 = CONV_TAC(REWR_CONV(TAUT `p \/ q <=> ~p ==> q`)) THEN STRIP_TAC;;
let CLITAUX_strip_d2 = CONV_TAC(REWR_CONV(TAUT `p \/ q <=> ~q ==> p`)) THEN STRIP_TAC;;

(* HOL4 contrapos_tac *)
let CLITAUX_contrapos_tac =
  CONV_TAC(REWR_CONV(TAUT `(p ==> q) <=> (~q ==> ~p)`)) THEN STRIP_TAC;;

(* HOL4 drw thms = DEP_REWRITE_TAC thms >> simp[] *)
let CLITAUX_drw thl = DEP_REWRITE_TAC thl THEN SIMP[];;

(* HOL4 spec_impl v = first_x_assum (qspec_then v mp_tac) >> impl_tac *)
let CLITAUX_spec_impl v = FIRST_X_ASSUM(QSPEC_THEN v MP_TAC) THEN ANTS_TAC;;

(* HOL4 rC q = rename [q] >> Cases_on q >> simp[] *)
let CLITAUX_rC q = RENAME1 q THEN QCASES_ON q THEN SIMP[];;

(* ASM_CASES_TAC, UNDISCH_TAC and SUBGOAL_THEN with the term given as a string
   parsed in the goal's context (as the kit's QBY), so that its variables need
   no type annotations *)
let CLITAUX_QASM_CASES_TAC (s:string) : tactic = fun g ->
  ASM_CASES_TAC (kit_parse_typed (kit_goal_frees g) bool_ty s) g;;
let CLITAUX_QUNDISCH_TAC (s:string) : tactic = fun g ->
  UNDISCH_TAC (kit_parse_typed (kit_goal_frees g) bool_ty s) g;;
let CLITAUX_QSUBGOAL_THEN (s:string) (ttac:thm_tactic) : tactic = fun g ->
  SUBGOAL_THEN (kit_parse_typed (kit_goal_frees g) bool_ty s) ttac g;;

let esubst_ty_var = prove
 (`!sigma avds n ty.
     esubst_ty sigma avds (hol_Var n ty) = hol_Var n (ty_esubst sigma ty)`,
  RW[esubst_ty_def; esubst_ty0_def; REV_ASSOCD_def]);;
let _ = cake_add_simps [esubst_ty_var];;

let esubst_ty_const = prove
 (`!sigma avds n ty.
     esubst_ty sigma avds (hol_Const n ty) = hol_Const n (ty_esubst sigma ty)`,
  RW[esubst_ty_def; esubst_ty0_def; REV_ASSOCD_def]);;
let _ = cake_add_simps [esubst_ty_const];;

let REV_ASSOCD_NEQ_DEFAULT = prove
 (`!t2 (sigma:(A#B)list) d.
     ~(REV_ASSOCD t2 sigma d = d) ==> ?t1. MEM (t1,t2) sigma /\ ~(t1 = d)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[REV_ASSOCD_def; MEM] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_MESON_TAC[PAIR]);;

let try_eq_error = prove
 (`!(m:(A,E1)error) (f:E1->(A,E2)error) e.
     little_try m f = errorMonad_error e <=>
     ?e1. m = errorMonad_error e1 /\ f e1 = errorMonad_error e`,
  REPEAT GEN_TAC THEN QCASES_ON "m" THEN
  REWRITE_TAC[little_try_def; distinctness "error"; injectivity "error"] THEN MESON_TAC[]);;

let try_eq_return = prove
 (`!(m:(A,E1)error) (f:E1->(A,E2)error) v.
     little_try m f = errorMonad_return v <=>
     m = errorMonad_return v \/ ?e. m = errorMonad_error e /\ f e = errorMonad_return v`,
  REPEAT GEN_TAC THEN QCASES_ON "m" THEN
  REWRITE_TAC[little_try_def; distinctness "error"; injectivity "error"] THEN MESON_TAC[]);;

let CLITAUX_CONS_EQ_APPEND3 = prove
 (`!(h:A) t p x s.
     CONS h t = APPEND (APPEND p [x]) s <=>
     (p = [] /\ h = x /\ t = s) \/ (?p'. p = CONS h p' /\ t = APPEND (APPEND p' [x]) s)`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `p:A list` list_CASES) THEN
  REWRITE_TAC[APPEND; CONS_11; NOT_CONS_NIL] THEN MESON_TAC[]);;

let CLITAUX_NIL_NEQ_APPEND3 = prove
 (`!(p:A list) x s. ~([] = APPEND (APPEND p [x]) s)`,
  MESON_TAC[APPEND_EQ_NIL; NOT_CONS_NIL]);;

let term_ok_rev_assocd = prove
 (`!sig (t1:A) env t2.
     hol_term_ok sig (REV_ASSOCD t1 env t2) <=>
     (?p t s. env = APPEND (APPEND p [(t,t1)]) s /\ (!e d. MEM (e,d) p ==> ~(d = t1)) /\
              hol_term_ok sig t) \/
     (!e d. MEM (e,d) env ==> ~(d = t1)) /\ hol_term_ok sig t2`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
   [REWRITE_TAC[REV_ASSOCD_def; MEM; CLITAUX_NIL_NEQ_APPEND3]; ALL_TAC] THEN
  X_GEN_TAC `h:hol_term#A` THEN X_GEN_TAC `rest:(hol_term#A)list` THEN DISCH_TAC THEN
  PAIR_CASES_ON `h:hol_term#A` THEN GEN_TAC THEN
  REWRITE_TAC[REV_ASSOCD_def; CLITAUX_CONS_EQ_APPEND3; MEM; PAIR_EQ] THEN
  COND_CASES_TAC THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN EQ_TAC THENL
     [DISCH_TAC THEN DISJ1_TAC THEN
      MAP_EVERY EXISTS_TAC [`[]:(hol_term#A)list`; `h0:hol_term`; `rest:(hol_term#A)list`] THEN
      ASM_REWRITE_TAC[MEM];
      REPEAT STRIP_TAC THEN FS[MEM] THEN ASM_MESON_TAC[]];
    ASM_REWRITE_TAC[] THEN EQ_TAC THEN STRIP_TAC THENL
     [DISJ1_TAC THEN
      MAP_EVERY EXISTS_TAC [`CONS (h0:hol_term,h1:A) p`; `t:hol_term`; `s:(hol_term#A)list`] THEN
      ASM_REWRITE_TAC[MEM; PAIR_EQ] THEN CONJ_TAC THENL
       [EXISTS_TAC `p:(hol_term#A)list` THEN REWRITE_TAC[]; ASM_MESON_TAC[]];
      DISJ2_TAC THEN ASM_MESON_TAC[];
      DISJ1_TAC THEN
      MAP_EVERY EXISTS_TAC [`p':(hol_term#A)list`; `t:hol_term`; `s:(hol_term#A)list`] THEN
      ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_MESON_TAC[MEM];
      DISJ2_TAC THEN ASM_MESON_TAC[]]]);;

let has_type_var = hd (CONJUNCTS has_type_rules);;
let _ = cake_add_simps [has_type_var];;
let has_type_const = hd (tl (CONJUNCTS has_type_rules));;
let _ = cake_add_simps [has_type_const];;

let rev_assocd_neq_mem = prove
 (`!(x:B) (l:(A#B)list) d.
     ~(REV_ASSOCD x l d = d) ==> MEM (REV_ASSOCD x l d,x) l`,
  MESON_TAC[REV_ASSOCD_MEM]);;

let neq_error = prove
 (`!x:(A,E)error. (!e. ~(x = errorMonad_error e)) <=> ?v. x = errorMonad_return v`,
  GEN_TAC THEN QCASES_ON "x" THEN
  REWRITE_TAC[distinctness "error"; injectivity "error"] THEN MESON_TAC[]);;

let vsubst_has_type = prove
 (`!ilist t tau. t has_type tau /\ vsubst_tys_ok ilist ==> (VSUBST ilist t) has_type tau`,
  REWRITE_TAC[vsubst_tys_ok_def] THEN MESON_TAC[VSUBST_HAS_TYPE]);;

let welltyped_comb_vsubst = prove
 (`!x y lst.
     welltyped (hol_Comb x y) /\ vsubst_tys_ok lst
     ==> welltyped (hol_Comb (VSUBST lst x) (VSUBST lst y))`,
  REWRITE_TAC[vsubst_tys_ok_def] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `welltyped (VSUBST lst (hol_Comb x y))` MP_TAC THENL
   [MATCH_MP_TAC VSUBST_WELLTYPED THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[VSUBST_def]]);;

let vsubst_tys_ok_cons = prove
 (`!x xs. vsubst_tys_ok (CONS x xs) <=>
          vsubst_tys_ok xs /\ ?n ty s'. x = (s',hol_Var n ty) /\ s' has_type ty`,
  REPEAT GEN_TAC THEN PAIR_CASES_ON `x:hol_term#hol_term` THEN
  REWRITE_TAC[vsubst_tys_ok_def; MEM; PAIR_EQ] THEN MESON_TAC[]);;
let _ = cake_add_simps [vsubst_tys_ok_cons];;

let vsubst_tys_ok_filter = prove
 (`!P lst. vsubst_tys_ok lst ==> vsubst_tys_ok (FILTER P lst)`,
  REWRITE_TAC[vsubst_tys_ok_def; MEM_FILTER] THEN MESON_TAC[]);;
let _ = cake_add_simps [vsubst_tys_ok_filter];;

let term_ok_vsubst_alt = prove
 (`!x lst sig.
     ALL (\p. hol_term_ok sig (FST p)) lst /\ hol_term_ok sig x /\ vsubst_tys_ok lst
     ==> hol_term_ok sig (VSUBST lst x)`,
  REWRITE_TAC[vsubst_tys_ok_def; GSYM ALL_MEM] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC term_ok_VSUBST THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN RES_TAC THEN RULE_ASSUM_TAC BETA_RULE THEN
  ASM_MESON_TAC[FST]);;

let vsubst_tys_ok_nil = prove
 (`vsubst_tys_ok []`,
  REWRITE_TAC[vsubst_tys_ok_def; MEM]);;
let _ = cake_add_simps [vsubst_tys_ok_nil];;

let VSUBST_nil = prove
 (`!tm. VSUBST [] tm = tm`,
  MATCH_MP_TAC hol_term_INDUCT THEN RW[VSUBST_def; REV_ASSOCD_def; FILTER; EX]);;
let _ = cake_add_simps [VSUBST_nil];;

let VSUBST_nil_eta = prove
 (`VSUBST [] = \p. p`,
  REWRITE_TAC[FUN_EQ_THM; VSUBST_nil]);;
let _ = cake_add_simps [VSUBST_nil_eta];;

let term_ok_vsubst_variant = prove
 (`!tm x1 x2 ty sig.
     hol_term_ok sig tm /\ type_ok (FST sig) ty
     ==> hol_term_ok sig (VSUBST [(hol_Var x1 ty,hol_Var x2 ty)] tm)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC term_ok_VSUBST THEN
  ASM_REWRITE_TAC[MEM; PAIR_EQ] THEN REPEAT STRIP_TAC THEN
  ASM_MESON_TAC[has_type_rules; hol_term_ok_def]);;

let term_var_ok = prove
 (`!n sig ty. type_ok (FST sig) ty ==> hol_term_ok sig (hol_Var n ty)`,
  REWRITE_TAC[hol_term_ok_def]);;

(* VSUBST_def on an abstraction over a variable, with the lets reduced *)
let CLITAUX_VSUBST_Abs_Var = prove
 (`!ilist x ty t.
     VSUBST ilist (hol_Abs (hol_Var x ty) t) =
     if EX (\(s',s). VFREE_IN (hol_Var x ty) s' /\ VFREE_IN s t)
           (FILTER (\(s',s). ~(s = hol_Var x ty)) ilist)
     then hol_Abs (hol_Var (VARIANT (VSUBST (FILTER (\(s',s). ~(s = hol_Var x ty)) ilist) t)
                                    (explode x) ty) ty)
            (VSUBST (CONS (hol_Var (VARIANT (VSUBST (FILTER (\(s',s). ~(s = hol_Var x ty))
                                                            ilist) t)
                                            (explode x) ty) ty,hol_Var x ty)
                          (FILTER (\(s',s). ~(s = hol_Var x ty)) ilist)) t)
     else hol_Abs (hol_Var x ty) (VSUBST (FILTER (\(s',s). ~(s = hol_Var x ty)) ilist) t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[VSUBST_def; dest_var_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[pair_CASE]);;

let VFREE_IN_VSUBST_OTHER_VAR = prove
 (`!tm ilist sig v.
     hol_term_ok sig tm /\
     (!v1 v2. MEM (v1,v2) ilist
              ==> ?n1 t1 n2 t2. v1 = hol_Var n1 t1 /\ v2 = hol_Var n2 t2 /\ ~(v1 = v)) /\
     VFREE_IN v (VSUBST ilist tm)
     ==> VFREE_IN v tm`,
  MATCH_MP_TAC hol_term_INDUCT THEN REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[VSUBST_def] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`ilist:(hol_term#hol_term)list`; `hol_Var a0 a1`; `hol_Var a0 a1`]
             REV_ASSOCD_MEM) THEN STRIP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME
        `MEM (REV_ASSOCD (hol_Var a0 a1) ilist (hol_Var a0 a1),hol_Var a0 a1) ilist`)) THEN
      STRIP_TAC THEN GVS[VFREE_IN_def];
      RFS[]];
    SIMP[VSUBST_def];
    REWRITE_TAC[VSUBST_def; VFREE_IN_def; hol_term_ok_def] THEN REPEAT STRIP_TAC THENL
     [DISJ1_TAC; DISJ2_TAC] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`ilist:(hol_term#hol_term)list`; `sig:sig`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`bv:hol_term`; `t:hol_term`] THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[hol_term_ok_def] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[CLITAUX_VSUBST_Abs_Var] THEN
  ABBREV_TAC `ilist' = FILTER (\(s',s). ~(s = hol_Var x ty)) (ilist:(hol_term#hol_term)list)` THEN
  ABBREV_TAC `z = hol_Var (VARIANT (VSUBST ilist' t) (explode x) ty) ty` THEN
  SUBGOAL_THEN `!v1 v2. MEM (v1,v2) (ilist':(hol_term#hol_term)list)
                  ==> ?n1 t1 n2 t2. v1 = hol_Var n1 t1 /\ v2 = hol_Var n2 t2 /\ ~(v1 = v)`
    ASSUME_TAC THENL
   [EXPAND_TAC "ilist'" THEN REWRITE_TAC[MEM_FILTER] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[VFREE_IN_def] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `EX (\(s',s). VFREE_IN (hol_Var x ty) s' /\ VFREE_IN s t)
                     (ilist':(hol_term#hol_term)list)` THEN
      REWRITE_TAC[GSYM EX_MEM; EXISTS_PAIR_THM] THEN
      CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
      STRIP_TAC THEN RES_TAC THEN GVS[VFREE_IN_def];
      FIRST_X_ASSUM(MATCH_MP_TAC o SPECL [`CONS (z:hol_term,hol_Var x ty) ilist'`; `sig:sig`;
                                          `v:hol_term`]) THEN
      ASM_REWRITE_TAC[MEM; PAIR_EQ] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
       [MAP_EVERY EXISTS_TAC
          [`VARIANT (VSUBST (ilist':(hol_term#hol_term)list) t) (explode x) ty`;
           `ty:hol_type`; `x:mlstring`; `ty:hol_type`] THEN ASM_REWRITE_TAC[];
        FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]];
    FIRST_X_ASSUM(MATCH_MP_TAC o SPECL [`ilist':(hol_term#hol_term)list`; `sig:sig`;
                                        `v:hol_term`]) THEN
    ASM_REWRITE_TAC[]]);;

let VFREE_IN_tm_names = prove
 (`!tm n ty. VFREE_IN (hol_Var n ty) tm ==> MEM n (tm_names tm)`,
  MATCH_MP_TAC hol_term_INDUCT THEN
  REWRITE_TAC[VFREE_IN_def; tm_names_def; MEM; MEM_APPEND; injectivity "hol_term";
              distinctness "hol_term"] THEN
  MESON_TAC[]);;

let nvar_aux_never_mem = prove
 (`!nms n. ~MEM (nvar_aux nms n) nms`,
  MATCH_MP_TAC nvar_aux_ind THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[nvar_aux] THEN COND_CASES_TAC THEN ASM_MESON_TAC[]);;

let NVARIANT_THM = prove
 (`!ty t n avds. ~VFREE_IN (hol_Var (NVARIANT n avds t) ty) t`,
  REWRITE_TAC[NVARIANT] THEN MESON_TAC[VFREE_IN_tm_names; nvar_aux_never_mem; MEM_APPEND]);;

let NVARIANT_MEM = prove
 (`!tm n avds. ~MEM (NVARIANT n avds tm) (APPEND (tm_names tm) avds)`,
  REWRITE_TAC[NVARIANT; nvar_aux_never_mem]);;

let NVARIANT_NAMES_THM = prove
 (`!tm n avds. ~MEM (NVARIANT n avds tm) (tm_names tm)`,
  MESON_TAC[NVARIANT_MEM; MEM_APPEND]);;

let NVARIANT_AVDS_THM = prove
 (`!tm n avds. ~MEM (NVARIANT n avds tm) avds`,
  MESON_TAC[NVARIANT_MEM; MEM_APPEND]);;

let FVs_VFREE_in = prove
 (`!tm n ty sig.
     hol_term_ok sig tm ==> (VFREE_IN (hol_Var n ty) tm <=> (n,ty) IN FVs tm)`,
  MATCH_MP_TAC hol_term_INDUCT THEN
  REWRITE_TAC[VFREE_IN_def; FVs_def; hol_term_ok_def; IN_UNION; IN_DIFF; IN_SING;
              NOT_IN_EMPTY; PAIR_EQ; injectivity "hol_term"; distinctness "hol_term"] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[FVs_def; IN_SING; PAIR_EQ; injectivity "hol_term"] THEN
  ASM_MESON_TAC[]);;

let FVs_VFREER_in = prove
 (`!tm n ty. (n,ty) IN FVs tm ==> VFREE_IN (hol_Var n ty) tm`,
  MATCH_MP_TAC hol_term_INDUCT THEN
  REWRITE_TAC[VFREE_IN_def; FVs_def; IN_UNION; IN_DIFF; IN_SING; NOT_IN_EMPTY; PAIR_EQ;
              injectivity "hol_term"; distinctness "hol_term"] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN ASM_MESON_TAC[FVs_def; IN_SING]);;

let sublist_map = prove
 (`!(xs:A list) ys (f:A->B).
     (!x. MEM x xs ==> MEM x ys) ==> (!x. MEM x (MAP f xs) ==> MEM x (MAP f ys))`,
  REWRITE_TAC[MEM_MAP] THEN MESON_TAC[]);;

let exists_free_in_ilist = prove
 (`!ilist x ty tm'.
     EX (\(s',s). VFREE_IN (hol_Var x ty) s' /\ VFREE_IN s tm') ilist /\
     (!p. MEM p ilist ==> ?n1 t1 n2 t2. p = (hol_Var n1 t1,hol_Var n2 t2))
     ==> (x,ty) IN UNIONS (set_of_list (MAP (\p. FVs (FST p)) ilist))`,
  REWRITE_TAC[GSYM EX_MEM; IN_UNIONS; IN_SET_OF_LIST; MEM_MAP; EXISTS_PAIR_THM] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REPEAT STRIP_TAC THEN RES_TAC THEN
  GVS[VFREE_IN_def] THEN EXISTS_TAC `FVs (hol_Var x ty)` THEN
  REWRITE_TAC[FVs_def; IN_SING] THEN
  MAP_EVERY EXISTS_TAC [`hol_Var x ty`; `hol_Var n2 t2`] THEN ASM_REWRITE_TAC[FVs_def]);;

let variant_name_self = prove
 (`!tm x ty. ~VFREE_IN (hol_Var x ty) tm <=> VARIANT tm (explode x) ty = x`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN REWRITE_TAC[VARIANT_def] THEN
    MP_TAC(ISPECL [`tm:hol_term`; `explode x`; `ty:hol_type`] VARIANT_PRIMES_def) THEN
    DISCH_THEN(MP_TAC o SPEC `0` o CONJUNCT2) THEN
    REWRITE_TAC[list_of_seq; APPEND_NIL; implode_explode] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `~(0 < n) <=> n = 0`] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[list_of_seq; APPEND_NIL; implode_explode];
    MESON_TAC[VARIANT_THM]]);;

let rev_assocd_default_cases = prove
 (`!(x:B) (l:(A#B)list) d.
     REV_ASSOCD x l d = d ==> MEM (d,x) l \/ ~(?y. MEM (y,x) l)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[REV_ASSOCD_def; MEM] THEN
  PAIR_CASES_ON `h:A#B` THEN REWRITE_TAC[REV_ASSOCD; PAIR_EQ] THEN
  GEN_TAC THEN COND_CASES_TAC THEN ASM_MESON_TAC[]);;

let NVARIANT_esubst_ty0 = prove
 (`!tm subst_tm n ty avds sig.
     (!n. MEM n (tm_names tm) ==> MEM n (tm_names subst_tm)) /\
     hol_term_ok sig tm
     ==> ~VFREE_IN (hol_Var (NVARIANT n avds subst_tm) ty) tm`,
  MESON_TAC[NVARIANT_NAMES_THM; VFREE_IN_tm_names]);;

let NVARIANT_esubst_ty0_alt = prove
 (`!tm subst_tm n ty avds sig.
     (!n. MEM n (tm_names tm) ==> MEM n (tm_names subst_tm)) /\
     hol_term_ok sig tm
     ==> ~((NVARIANT n avds subst_tm,ty) IN FVs tm)`,
  MESON_TAC[NVARIANT_esubst_ty0; FVs_VFREE_in]);;

let rev_assocd_different_default = prove
 (`!(l:(A#B)list) k d1 d2.
     REV_ASSOCD k l d1 = d1 /\ REV_ASSOCD k l d2 = d2 /\ ~(d1 = d2)
     ==> !v. ~MEM (v,k) l`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[REV_ASSOCD_def; MEM] THEN
  PAIR_CASES_ON `h:A#B` THEN REWRITE_TAC[REV_ASSOCD; PAIR_EQ] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_MESON_TAC[]);;

(* HOL4: REV_ASSOCD_NEQ_DEFAULT |> CONV_RULE CONTRAPOS_CONV |> SRULE[] *)
let REV_ASSOCD_EQ_DEFAULT_i = prove
 (`!t2 (sigma:(A#B)list) d.
     (!t1. MEM (t1,t2) sigma ==> t1 = d) ==> REV_ASSOCD t2 sigma d = d`,
  MESON_TAC[REV_ASSOCD_NEQ_DEFAULT]);;

let VSUBST_NOT_FREE = prove
 (`!tm ilist sig.
     hol_term_ok sig tm /\
     (!v k. MEM (v,k) ilist ==> ?n ty. k = hol_Var n ty /\ ~((n,ty) IN FVs tm))
     ==> VSUBST ilist tm = tm`,
  MATCH_MP_TAC hol_term_INDUCT THEN REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[VSUBST_def] THEN STRIP_TAC THEN
    MATCH_MP_TAC REV_ASSOCD_EQ_DEFAULT_i THEN REPEAT STRIP_TAC THEN
    RES_TAC THEN GVS[FVs_def; IN_SING];
    SIMP[VSUBST_def];
    REWRITE_TAC[VSUBST_def; hol_term_ok_def; FVs_def; IN_UNION; DE_MORGAN_THM;
                injectivity "hol_term"] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `sig:sig` THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`bv:hol_term`; `t:hol_term`] THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[hol_term_ok_def] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[CLITAUX_VSUBST_Abs_Var] THEN
  ABBREV_TAC `ilist' = FILTER (\(s',s). ~(s = hol_Var x ty)) (ilist:(hol_term#hol_term)list)` THEN
  SUBGOAL_THEN `!v k. MEM (v,k) (ilist':(hol_term#hol_term)list)
                  ==> ?n ty'. k = hol_Var n ty' /\ ~((n,ty') IN FVs t)`
    ASSUME_TAC THENL
   [EXPAND_TAC "ilist'" THEN REWRITE_TAC[MEM_FILTER] THEN
    CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REPEAT STRIP_TAC THEN RES_TAC THEN
    GVS[FVs_def; IN_DIFF; IN_SING; PAIR_EQ; injectivity "hol_term"] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~EX (\(s',s). VFREE_IN (hol_Var x ty) s' /\ VFREE_IN s t)
                    (ilist':(hol_term#hol_term)list)`
    (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[GSYM EX_MEM; EXISTS_PAIR_THM] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
    REPEAT STRIP_TAC THEN RES_TAC THEN GVS[] THEN ASM_MESON_TAC[FVs_VFREE_in];
    ALL_TAC] THEN
  AP_TERM_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o SPECL [`ilist':(hol_term#hol_term)list`; `sig:sig`]) THEN
  ASM_REWRITE_TAC[]);;

let free_names_comb = prove
 (`!t1 t2. free_names (hol_Comb t1 t2) = free_names t1 UNION free_names t2`,
  REWRITE_TAC[free_names; FVs_def; EXTENSION; IN_ELIM_THM; IN_UNION] THEN MESON_TAC[]);;
let _ = cake_add_simps [free_names_comb];;

let alist_to_fm_FILTER = prove
 (`!(ilist:(B#A)list) k.
     alist_to_fm (FILTER (\(s',s). ~(s = k)) ilist) = alist_to_fm ilist \\ k`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[FILTER; alist_to_fm_def; DOMSUB_FEMPTY] THEN
  PAIR_CASES_ON `h:B#A` THEN GEN_TAC THEN REWRITE_TAC[FILTER] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[alist_to_fm_def; DOMSUB_FUPDATE_THM] THEN
  ASM_MESON_TAC[]);;

let FLOOKUP_alist_to_fm_NONE = prove
 (`!(ilist:(B#A)list) k d.
     FLOOKUP (alist_to_fm ilist) k = NONE ==> REV_ASSOCD k ilist d = d`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[alist_to_fm_def; REV_ASSOCD_def] THEN
  PAIR_CASES_ON `h:B#A` THEN
  REWRITE_TAC[alist_to_fm_def; REV_ASSOCD; FLOOKUP_UPDATE] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[distinctness "option"]);;

let ALL_DISTINCT_MAP_SND = prove
 (`!(ilist:(B#A)list) v k.
     ALL_DISTINCT (MAP SND ilist) /\ MEM (v,k) ilist
     ==> FLOOKUP (alist_to_fm ilist) k = SOME v`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MEM] THEN PAIR_CASES_ON `h:B#A` THEN
  REWRITE_TAC[alist_to_fm_def; FLOOKUP_UPDATE; PAIR_EQ; MAP; ALL_DISTINCT; MEM] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN
  ASM_MESON_TAC[MEM_MAP; SND]);;

let FLOOKUP_alist_to_fm_MEM = prove
 (`!(ilist:(B#A)list) v k.
     FLOOKUP (alist_to_fm ilist) k = SOME v ==> MEM (v,k) ilist`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[alist_to_fm_def; FLOOKUP_EMPTY; distinctness "option"] THEN
  PAIR_CASES_ON `h:B#A` THEN
  REWRITE_TAC[alist_to_fm_def; FLOOKUP_UPDATE; MEM; PAIR_EQ] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[injectivity "option"] THEN
  ASM_MESON_TAC[]);;

(* REV_ASSOCD of an association list is the lookup in alist_to_fm *)
let CLITAUX_REV_ASSOCD_alist_to_fm = prove
 (CASE_TERM `!(ilist:(B#A)list) k d.
     REV_ASSOCD k ilist d =
     (match FLOOKUP (alist_to_fm ilist) k with NONE -> d | SOME v -> v)`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[alist_to_fm_def; REV_ASSOCD_def; FLOOKUP_EMPTY; option_CASE];
    PAIR_CASES_ON `h:B#A` THEN
    ASM_REWRITE_TAC[alist_to_fm_def; REV_ASSOCD; FLOOKUP_UPDATE] THEN
    REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[option_CASE]]);;

(* VSUBSTfm on an abstraction over a variable, with the lets reduced *)
let CLITAUX_VSUBSTfm_Abs_Var = prove
 (`!fm x ty t.
     VSUBSTfm fm (hol_Abs (hol_Var x ty) t) =
     if ?k w. FLOOKUP (fm \\ hol_Var x ty) k = SOME w /\ VFREE_IN (hol_Var x ty) w /\
              VFREE_IN k t
     then hol_Abs (hol_Var (VARIANT (VSUBSTfm (fm \\ hol_Var x ty) t) (explode x) ty) ty)
            (VSUBSTfm (fm \\ hol_Var x ty |+
                       (hol_Var x ty,
                        hol_Var (VARIANT (VSUBSTfm (fm \\ hol_Var x ty) t) (explode x) ty) ty))
                      t)
     else hol_Abs (hol_Var x ty) (VSUBSTfm (fm \\ hol_Var x ty) t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[VSUBSTfm; dest_var_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[pair_CASE]);;

let VSUBST_VSUBSTfm = prove
 (`!tm ilist sig.
     ALL_DISTINCT (MAP SND ilist) /\ hol_term_ok sig tm
     ==> VSUBST ilist tm = VSUBSTfm (alist_to_fm ilist) tm`,
  MATCH_MP_TAC hol_term_INDUCT THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[VSUBST_def; VSUBSTfm; CLITAUX_REV_ASSOCD_alist_to_fm];
    REWRITE_TAC[VSUBST_def; VSUBSTfm];
    REWRITE_TAC[VSUBST_def; VSUBSTfm; hol_term_ok_def; injectivity "hol_term"] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `sig:sig` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`bv:hol_term`; `t:hol_term`] THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[hol_term_ok_def] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  REWRITE_TAC[CLITAUX_VSUBST_Abs_Var; CLITAUX_VSUBSTfm_Abs_Var; GSYM alist_to_fm_FILTER] THEN
  ABBREV_TAC `ilist' = FILTER (\(s',s). ~(s = hol_Var x ty)) (ilist:(hol_term#hol_term)list)` THEN
  SUBGOAL_THEN `ALL_DISTINCT (MAP SND (ilist':(hol_term#hol_term)list)) /\
                ~MEM (hol_Var x ty) (MAP SND ilist')`
    STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "ilist'" THEN REWRITE_TAC[MAP_SND_FILTER_NEQ; MEM_FILTER] THEN
    ASM_SIMP_TAC[FILTER_ALL_DISTINCT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(EX (\(s',s). VFREE_IN (hol_Var x ty) s' /\ VFREE_IN s t) ilist' <=>
     ?k w. FLOOKUP (alist_to_fm ilist') k = SOME w /\ VFREE_IN (hol_Var x ty) w /\
           VFREE_IN k t)`
    SUBST1_TAC THENL
   [REWRITE_TAC[GSYM EX_MEM; EXISTS_PAIR_THM] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
    ASM_MESON_TAC[ALL_DISTINCT_MAP_SND; FLOOKUP_alist_to_fm_MEM];
    ALL_TAC] THEN
  SUBGOAL_THEN `VSUBST ilist' t = VSUBSTfm (alist_to_fm ilist') t` SUBST1_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `sig:sig` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[injectivity "hol_term"] THEN
  REWRITE_TAC[GSYM alist_to_fm_def] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  EXISTS_TAC `sig:sig` THEN ASM_REWRITE_TAC[MAP; ALL_DISTINCT]);;

let exists_free_in_fm_map = prove
 (`!tm fm x ty sig.
     hol_term_ok sig tm /\
     (?k v. FLOOKUP fm k = SOME v /\ VFREE_IN (hol_Var x ty) v /\ VFREE_IN k tm) /\
     (!v. v IN FRANGE fm ==> ?n ty. v = hol_Var n ty) /\
     (!v. v IN FDOM fm ==> ?n ty. v = hol_Var n ty)
     ==> (x,ty) IN
         UNIONS {FVs t | ?n ty'. (n,ty') IN FVs tm /\ FLOOKUP fm (hol_Var n ty') = SOME t}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
  SUBGOAL_THEN `(k:hol_term) IN FDOM fm /\ (v:hol_term) IN FRANGE fm` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[FDOM_FLOOKUP; IN_FRANGE_FLOOKUP; distinctness "option"] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  RES_TAC THEN GVS[VFREE_IN_def] THEN EXISTS_TAC `FVs (hol_Var x ty)` THEN
  REWRITE_TAC[FVs_def; IN_SING] THEN EXISTS_TAC `hol_Var x ty` THEN
  REWRITE_TAC[FVs_def] THEN MAP_EVERY EXISTS_TAC [`n:mlstring`; `ty':hol_type`] THEN
  ASM_MESON_TAC[FVs_VFREE_in]);;

let FLOOKUP_FUPDATE = prove
 (`!(fm:(A,B)fmap) k v k1.
     FLOOKUP (fm |+ (k,v)) k1 = if k1 = k then SOME v else FLOOKUP fm k1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FLOOKUP_UPDATE] THEN
  ASM_CASES_TAC `k1:A = k` THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let MEM_ZIP_FST = prove
 (`!(l1:A list) (l2:B list) x. MEM x (ZIP l1 l2) ==> MEM (FST x) l1`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ZIP_DEF; MEM] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* HOL4's ZIP truncates the longer list; with HOL Light's, the second
   components come from l2 only when l1 is not longer. *)
let MEM_ZIP_SND = prove
 (`!(l1:A list) (l2:B list) x.
     LENGTH l1 <= LENGTH l2 /\ MEM x (ZIP l1 l2) ==> MEM (SND x) l2`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ZIP_DEF; MEM] THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `l2:B list` list_CASES) THEN
  REWRITE_TAC[LENGTH; HD; TL; MEM; ARITH_RULE `~(SUC n <= 0)`; LE_SUC] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* VSUBSTfm_FVs pointwise, for a map to variables *)
let CLITAUX_VSUBSTfm_FVs_pt = prove
 (`!tm sig fm m ty'.
     hol_term_ok sig tm /\
     (!k v. FLOOKUP fm k = SOME v ==> ?n ty. v = hol_Var n ty)
     ==> ((m,ty') IN FVs (VSUBSTfm fm tm) <=>
          ((m,ty') IN FVs tm /\ FLOOKUP fm (hol_Var m ty') = NONE) \/
          (?n ty. (n,ty) IN FVs tm /\ FLOOKUP fm (hol_Var n ty) = SOME (hol_Var m ty')))`,
  MATCH_MP_TAC hol_term_INDUCT THEN REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[VSUBSTfm; FVs_def; IN_SING; PAIR_EQ] THEN
    TOP_CASE_TAC THEN REWRITE_TAC[FVs_def; IN_SING; PAIR_EQ] THENL
     [ASM_MESON_TAC[distinctness "option"];
      FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME
        `FLOOKUP (fm:(hol_term,hol_term)fmap) (hol_Var a0 a1) = SOME a`)) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[FVs_def; IN_SING; PAIR_EQ] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `a = hol_Var n ty`]) THEN
      ASM_MESON_TAC[distinctness "option"; injectivity "option"; injectivity "hol_term"]];
    REWRITE_TAC[VSUBSTfm; FVs_def; NOT_IN_EMPTY];
    REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[hol_term_ok_def] THEN
    STRIP_TAC THEN RULE_ASSUM_TAC(fun th -> try SPEC `sig:sig` th with Failure _ -> th) THEN
    ASM_SIMP_TAC[VSUBSTfm; FVs_def; IN_UNION] THEN MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`bv:hol_term`; `t:hol_term`] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`sig:sig`; `fm:(hol_term,hol_term)fmap`; `m:mlstring`; `mty:hol_type`] THEN
  REWRITE_TAC[hol_term_ok_def; LEFT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:mlstring`; `xty:hol_type`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(fun th -> try SPEC `sig:sig` th with Failure _ -> th) THEN
  REWRITE_TAC[CLITAUX_VSUBSTfm_Abs_Var] THEN
  ABBREV_TAC `fm' = (fm:(hol_term,hol_term)fmap) \\ hol_Var x xty` THEN
  SUBGOAL_THEN `!k. FLOOKUP (fm':(hol_term,hol_term)fmap) k =
                    if k = hol_Var x xty then NONE else FLOOKUP fm k` ASSUME_TAC THENL
   [EXPAND_TAC "fm'" THEN REWRITE_TAC[DOMSUB_FLOOKUP_THM] THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!k v. FLOOKUP (fm':(hol_term,hol_term)fmap) k = SOME v
                      ==> ?n ty. v = hol_Var n ty` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[distinctness "option"]; ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[FVs_def; IN_DIFF; IN_SING; PAIR_EQ] THENL
   [ABBREV_TAC `xv = VARIANT (VSUBSTfm fm' t) (explode x) xty` THEN
    SUBGOAL_THEN `~((xv,xty) IN FVs (VSUBSTfm fm' t))` MP_TAC THENL
     [EXPAND_TAC "xv" THEN MESON_TAC[VARIANT_THM; FVs_VFREER_in]; ALL_TAC] THEN
    SUBGOAL_THEN `!k v. FLOOKUP (fm' |+ (hol_Var x xty,hol_Var xv xty)) k = SOME v
                        ==> ?n ty. v = hol_Var n ty` ASSUME_TAC THENL
     [REWRITE_TAC[FLOOKUP_UPDATE] THEN ASM_MESON_TAC[injectivity "option"]; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN REWRITE_TAC[FLOOKUP_UPDATE] THEN
    ASM_REWRITE_TAC[injectivity "hol_term"] THEN
    REWRITE_TAC[COND_CASE_EQ; distinctness "option"; injectivity "option";
                injectivity "hol_term"] THEN
    MESON_TAC[];
    SUBGOAL_THEN `!n ty m mty. (n,ty) IN FVs t /\ ~(n = x /\ ty = xty) /\
                     FLOOKUP fm (hol_Var n ty) = SOME (hol_Var m mty) ==> ~(m = x /\ mty = xty)`
      ASSUME_TAC THENL
     [REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
      QPAT_X_ASSUM "~(?k w. _)" MP_TAC THEN REWRITE_TAC[] THEN
      MAP_EVERY EXISTS_TAC [`hol_Var n ty`; `hol_Var m mty`] THEN
      ASM_REWRITE_TAC[injectivity "hol_term"; VFREE_IN_def] THEN
      ASM_MESON_TAC[FVs_VFREER_in];
      ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN
    ASM_REWRITE_TAC[COND_CASE_EQ; distinctness "option"; injectivity "option";
                    injectivity "hol_term"] THEN
    POP_ASSUM MP_TAC THEN MESON_TAC[]]);;

let VSUBSTfm_FVs = prove
 (`!tm fm sig.
     hol_term_ok sig tm /\
     (!v. v IN FRANGE fm ==> ?n ty. v = hol_Var n ty) /\
     (!v. v IN FDOM fm ==> ?n ty. v = hol_Var n ty)
     ==> FVs (VSUBSTfm fm tm) =
         (FVs tm DIFF {(n,ty) | hol_Var n ty IN FDOM fm}) UNION
         UNIONS {FVs t | ?n ty. (n,ty) IN FVs tm /\ FLOOKUP fm (hol_Var n ty) = SOME t}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!k v. FLOOKUP (fm:(hol_term,hol_term)fmap) k = SOME v
                      ==> ?n ty. v = hol_Var n ty` ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_FRANGE_FLOOKUP]; ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`m:mlstring`; `mty:hol_type`] THEN
  MP_TAC(SPECL [`tm:hol_term`; `sig:sig`; `fm:(hol_term,hol_term)fmap`; `m:mlstring`;
                `mty:hol_type`] CLITAUX_VSUBSTfm_FVs_pt) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[IN_UNION; IN_DIFF; IN_ELIM_THM; IN_UNIONS; FDOM_FLOOKUP; PAIR_EQ] THEN
  MATCH_MP_TAC(TAUT `(b <=> b') /\ (c <=> c') ==> (a /\ b \/ c <=> a /\ b' \/ c')`) THEN
  CONJ_TAC THENL [MESON_TAC[]; EQ_TAC THEN STRIP_TAC] THENL
   [EXISTS_TAC `FVs (hol_Var m mty)` THEN REWRITE_TAC[FVs_def; IN_SING] THEN
    EXISTS_TAC `hol_Var m mty` THEN REWRITE_TAC[FVs_def] THEN
    MAP_EVERY EXISTS_TAC [`n:mlstring`; `ty:hol_type`] THEN ASM_REWRITE_TAC[];
    FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME
      `FLOOKUP (fm:(hol_term,hol_term)fmap) (hol_Var n ty) = SOME t'`)) THEN
    STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`n:mlstring`; `ty:hol_type`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `t':hol_term = hol_Var n' ty'`; FVs_def; IN_SING;
                                PAIR_EQ]) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(m:mlstring,mty:hol_type) IN t` THEN ASM_REWRITE_TAC[IN_SING; PAIR_EQ] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[]]);;

let FVs_VSUBST_CASES = prove
 (`!tm x ty1 a b ty sig.
     hol_term_ok sig tm
     ==> ((x,ty1) IN FVs (VSUBST [(hol_Var a ty,hol_Var b ty)] tm) <=>
          (x = a /\ ty1 = ty /\ (b,ty) IN FVs tm) \/
          ((x,ty1) IN FVs tm /\ (~(x = b) \/ ~(ty1 = ty))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`tm:hol_term`; `[(hol_Var a ty,hol_Var b ty)]`; `sig:sig`] VSUBST_VSUBSTfm) THEN
  ASM_REWRITE_TAC[MAP; ALL_DISTINCT; MEM] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(SPECL [`tm:hol_term`; `sig:sig`; `alist_to_fm [(hol_Var a ty,hol_Var b ty)]`;
                `x:mlstring`; `ty1:hol_type`] CLITAUX_VSUBSTfm_FVs_pt) THEN
  REWRITE_TAC[alist_to_fm_def; FLOOKUP_UPDATE; FLOOKUP_EMPTY] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[COND_CASE_EQ; distinctness "option"; injectivity "option"] THEN
    MESON_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[COND_CASE_EQ; distinctness "option"; injectivity "option";
              injectivity "hol_term"] THEN
  MESON_TAC[]);;

let FVs_VSUBST_PRESERVED_VAR = prove
 (`!tm n n1 n2 ty ty1 sig.
     hol_term_ok sig tm /\ (n,ty) IN FVs tm /\ ~(ty = ty1)
     ==> (n,ty) IN FVs (VSUBST [(hol_Var n2 ty1,hol_Var n1 ty1)] tm)`,
  MESON_TAC[FVs_VSUBST_CASES]);;

let FVs_VSUBST_SUBSTITUTED_VAR = prove
 (`!tm n oldN ty sig.
     hol_term_ok sig tm /\ (n,ty) IN FVs tm
     ==> (n,ty) IN FVs (VSUBST [(hol_Var n ty,hol_Var oldN ty)] tm)`,
  MESON_TAC[FVs_VSUBST_CASES]);;

let FVs_in_tm_names = prove
 (`!tm n ty. (n,ty) IN FVs tm ==> MEM n (tm_names tm)`,
  MATCH_MP_TAC hol_term_INDUCT THEN
  REWRITE_TAC[FVs_def; tm_names_def; MEM; MEM_APPEND; IN_SING; IN_UNION; IN_DIFF;
              NOT_IN_EMPTY; PAIR_EQ] THEN
  MESON_TAC[]);;

let tm_names_vsubst = prove
 (`!tm n m ty1 ty2 sig.
     hol_term_ok sig tm /\ (n,ty1) IN FVs tm /\ ~(ty1 = ty2) /\ MEM n (tm_names tm)
     ==> MEM n (tm_names (VSUBST [(hol_Var m ty2,hol_Var n ty2)] tm))`,
  MESON_TAC[FVs_VSUBST_PRESERVED_VAR; FVs_in_tm_names]);;

let alist_to_fm_FDOM_MEM = prove
 (`!(k:A) (ilist:(B#A)list).
     k IN FDOM (alist_to_fm ilist) ==> ?v. MEM (v,k) ilist`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[alist_to_fm_def; FDOM_FEMPTY; NOT_IN_EMPTY; MEM] THEN
  PAIR_CASES_ON `h:B#A` THEN REWRITE_TAC[alist_to_fm_def; FDOM_FUPDATE; IN_INSERT; PAIR_EQ] THEN
  ASM_MESON_TAC[]);;

let alist_to_fm_FRANGE_MEM = prove
 (`!(v:B) (ilist:(B#A)list).
     v IN FRANGE (alist_to_fm ilist) ==> ?k. MEM (v,k) ilist`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[alist_to_fm_def; IN_FRANGE_FLOOKUP; FLOOKUP_EMPTY; distinctness "option"; MEM] THEN
  PAIR_CASES_ON `h:B#A` THEN REWRITE_TAC[alist_to_fm_def; FLOOKUP_UPDATE; PAIR_EQ] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_FRANGE_FLOOKUP]) THEN
  ASM_MESON_TAC[injectivity "option"]);;

let FLOOKUP_fm_DOMSUB_FUPDATE = prove
 (`!(fm:(A,B)fmap) k v k1 v1.
     FLOOKUP (fm \\ k1) k = SOME v ==> FLOOKUP (fm |+ (k1,v1)) k = SOME v`,
  REWRITE_TAC[DOMSUB_FLOOKUP_THM; FLOOKUP_UPDATE] THEN REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[distinctness "option"] THEN ASM_REWRITE_TAC[]);;

let tm_names_VSUBSTfm_fupdate = prove
 (`!fm tm' n nv ty k w sig.
     ~(n = nv) /\
     type_ok (FST sig) ty /\
     hol_term_ok sig tm' /\
     (!v. v IN FDOM fm ==> ?x ty. v = hol_Var x ty /\ ~(x = n)) /\
     (!v. v IN FRANGE fm ==> ?n ty. v = hol_Var n ty) /\
     (!v. v IN FRANGE fm ==> hol_term_ok sig v) /\
     FLOOKUP (fm \\ hol_Var n ty) k = SOME w /\
     VFREE_IN (hol_Var n ty) w /\
     VFREE_IN k tm'
     ==> MEM n (tm_names (VSUBSTfm (fm |+ (hol_Var n ty,hol_Var nv ty)) tm'))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FVs_in_tm_names THEN EXISTS_TAC `ty:hol_type` THEN
  MP_TAC(SPECL [`tm':hol_term`; `sig:sig`; `fm |+ (hol_Var n ty,hol_Var nv ty)`; `n:mlstring`;
                `ty:hol_type`] CLITAUX_VSUBSTfm_FVs_pt) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[FLOOKUP_UPDATE; COND_CASE_EQ; injectivity "option"] THEN
    REPEAT STRIP_TAC THENL
     [MAP_EVERY EXISTS_TAC [`nv:mlstring`; `ty:hol_type`] THEN ASM_REWRITE_TAC[];
      QPAT_X_ASSUM "!v. v IN FRANGE fm ==> ?n ty. _" MATCH_MP_TAC THEN
      REWRITE_TAC[IN_FRANGE_FLOOKUP] THEN ASM_MESON_TAC[]];
    DISCH_THEN SUBST1_TAC] THEN
  DISJ2_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[DOMSUB_FLOOKUP_THM; COND_CASE_EQ;
                                              distinctness "option"]) THEN
  SUBGOAL_THEN `(k:hol_term) IN FDOM fm /\ (w:hol_term) IN FRANGE fm` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[FDOM_FLOOKUP; IN_FRANGE_FLOOKUP] THEN ASM_MESON_TAC[distinctness "option"];
    ALL_TAC] THEN
  RES_TAC THEN GVS[VFREE_IN_def] THEN
  REWRITE_TAC[FLOOKUP_UPDATE; COND_CASE_EQ; injectivity "hol_term"; injectivity "option"] THEN
  ASM_MESON_TAC[FVs_VFREE_in]);;

let tm_names_vsubstfm_different_name = prove
 (`!tm fm n sig.
     hol_term_ok sig tm /\
     (!v. v IN FDOM fm ==> ?x ty. v = hol_Var x ty /\ ~(x = n)) /\
     (!v. v IN FRANGE fm ==> ?n ty. v = hol_Var n ty) /\
     (!v. v IN FRANGE fm ==> hol_term_ok sig v) /\
     MEM n (tm_names tm)
     ==> MEM n (tm_names (VSUBSTfm fm tm))`,
  MATCH_MP_TAC hol_term_INDUCT THEN REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[tm_names_def; MEM; VSUBSTfm] THEN STRIP_TAC THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN TOP_CASE_TAC THEN REWRITE_TAC[tm_names_def; MEM] THEN
    SUBGOAL_THEN `hol_Var a0 a1 IN FDOM (fm:(hol_term,hol_term)fmap)` MP_TAC THENL
     [ASM_REWRITE_TAC[FDOM_FLOOKUP; distinctness "option"]; ALL_TAC] THEN
    DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th)) THEN
    REWRITE_TAC[injectivity "hol_term"] THEN MESON_TAC[];
    REWRITE_TAC[tm_names_def; MEM];
    REWRITE_TAC[tm_names_def; MEM_APPEND; VSUBSTfm; hol_term_ok_def] THEN
    REPEAT STRIP_TAC THENL [DISJ1_TAC; DISJ2_TAC] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `sig:sig` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`bv:hol_term`; `t:hol_term`] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`fm:(hol_term,hol_term)fmap`; `n:mlstring`; `sig:sig`] THEN
  REWRITE_TAC[hol_term_ok_def; LEFT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:mlstring`; `xty:hol_type`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[tm_names_def; APPEND; MEM]) THEN
  REWRITE_TAC[CLITAUX_VSUBSTfm_Abs_Var] THEN
  SUBGOAL_THEN `(!v. v IN FRANGE (fm \\ hol_Var x xty) ==> ?n ty. v = hol_Var n ty) /\
                (!v. v IN FRANGE (fm \\ hol_Var x xty) ==> hol_term_ok sig v) /\
                (!v. v IN FDOM (fm \\ hol_Var x xty) ==> ?x ty. v = hol_Var x ty /\ ~(x = n))`
    STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC IN_FRANGE_DOMSUB_suff THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC IN_FRANGE_DOMSUB_suff THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[FDOM_DOMSUB; IN_DELETE] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[tm_names_def; APPEND; MEM] THEN
  ASM_CASES_TAC `n:mlstring = x` THEN ASM_REWRITE_TAC[] THENL
   [ASM_CASES_TAC `x = VARIANT (VSUBSTfm (fm \\ hol_Var x xty) t) (explode x) xty` THENL
     [DISJ1_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[FUPDATE_PURGE'] THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `k:hol_term` (X_CHOOSE_THEN `w:hol_term` STRIP_ASSUME_TAC) o
                  check (is_exists o concl)) THEN
    MATCH_MP_TAC tm_names_VSUBSTfm_fupdate THEN
    MAP_EVERY EXISTS_TAC [`k:hol_term`; `w:hol_term`; `sig:sig`] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    DISJ2_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `sig:sig` THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[FDOM_FUPDATE; IN_INSERT] THEN ASM_MESON_TAC[];
      MATCH_MP_TAC IN_FRANGE_FUPDATE_suff THEN ASM_REWRITE_TAC[] THEN MESON_TAC[];
      MATCH_MP_TAC IN_FRANGE_FUPDATE_suff THEN ASM_REWRITE_TAC[hol_term_ok_def];
      ASM_MESON_TAC[]];
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `sig:sig` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[]]);;

let tm_names_vsubst_different_name = prove
 (`!tm ilist n sig.
     hol_term_ok sig tm /\
     (!v. MEM v ilist ==> ?x1 x2 ty. v = (hol_Var x1 ty,hol_Var x2 ty) /\
                                     ~(n = x2) /\ hol_term_ok sig (hol_Var x1 ty)) /\
     ALL_DISTINCT (MAP SND ilist) /\
     MEM n (tm_names tm)
     ==> MEM n (tm_names (VSUBST ilist tm))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`tm:hol_term`; `ilist:(hol_term#hol_term)list`; `sig:sig`] VSUBST_VSUBSTfm) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC tm_names_vsubstfm_different_name THEN EXISTS_TAC `sig:sig` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN X_GEN_TAC `v:hol_term` THEN DISCH_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP alist_to_fm_FDOM_MEM);
    FIRST_X_ASSUM(MP_TAC o MATCH_MP alist_to_fm_FRANGE_MEM);
    FIRST_X_ASSUM(MP_TAC o MATCH_MP alist_to_fm_FRANGE_MEM)] THEN
  STRIP_TAC THEN RES_TAC THEN GVS[PAIR_EQ] THEN ASM_MESON_TAC[]);;

let has_type_comb = prove
 (`!t1 t2 ty.
     hol_Comb t1 t2 has_type ty <=>
     ?dty. t1 has_type Tyapp (implode "fun") [dty; ty] /\ t2 has_type dty`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [has_type_cases] THEN
  REWRITE_TAC[distinctness "hol_term"; injectivity "hol_term"] THEN MESON_TAC[]);;

let has_type_typeof = prove
 (`!a b. a has_type b ==> typeof a = b`,
  MATCH_MP_TAC has_type_ind THEN SIMP[typeof_def; codomain_def]);;

let ty_esubst_fun = prove
 (`!sig sigma ty1 ty2.
     esubsts_ok sig sigma
     ==> ty_esubst sigma (Tyapp (implode "fun") [ty1; ty2]) = Tyapp
       (implode "fun") [ty_esubst sigma ty1; ty_esubst sigma ty2]`,
  REWRITE_TAC[FORALL_PAIR_THM; esubsts_ok_def] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[ty_esubst_def] THEN
  SUBGOAL_THEN `FLOOKUP p1' (implode "fun") = (NONE:(mlstring list#hol_type)option)`
    SUBST1_TAC THENL [ASM_REWRITE_TAC[FLOOKUP_DEF]; ALL_TAC] THEN
  REWRITE_TAC[option_CASE; MAP]);;
let _ = cake_add_simps [ty_esubst_fun];;

let codomain_ty_esubst = prove
 (`!tm sig sigma dty ty.
     esubsts_ok sig sigma /\ tm has_type Tyapp (implode "fun") [dty; ty]
     ==> codomain (ty_esubst sigma (typeof tm)) = ty_esubst sigma (codomain (typeof tm))`,
  REPEAT STRIP_TAC THEN IMP_RES_TAC has_type_typeof THEN ASM_REWRITE_TAC[codomain_def] THEN
  ASM_MESON_TAC[ty_esubst_fun; codomain_def]);;

let typeof_vsubst = prove
 (`!tm ilist sig.
     hol_term_ok sig tm /\
     (!v1 v2. MEM (v1,v2) ilist ==> ?n1 n2 ty. v1 = hol_Var n1 ty /\ v2 = hol_Var n2 ty)
     ==> typeof (VSUBST ilist tm) = typeof tm`,
  MATCH_MP_TAC hol_term_INDUCT THEN REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[VSUBST_def] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`ilist:(hol_term#hol_term)list`; `hol_Var a0 a1`; `hol_Var a0 a1`]
             REV_ASSOCD_MEM) THEN STRIP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME
        `MEM (REV_ASSOCD (hol_Var a0 a1) ilist (hol_Var a0 a1),hol_Var a0 a1) ilist`)) THEN
      STRIP_TAC THEN GVS[typeof_def];
      ASM_REWRITE_TAC[]];
    SIMP[VSUBST_def];
    REWRITE_TAC[VSUBST_def; hol_term_ok_def; typeof_def] THEN REPEAT STRIP_TAC THEN
    AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `sig:sig` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`bv:hol_term`; `t:hol_term`] THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[hol_term_ok_def] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[CLITAUX_VSUBST_Abs_Var] THEN
  ABBREV_TAC `ilist' = FILTER (\(s',s). ~(s = hol_Var x ty)) (ilist:(hol_term#hol_term)list)` THEN
  SUBGOAL_THEN `!v1 v2. MEM (v1,v2) (ilist':(hol_term#hol_term)list)
                  ==> ?n1 n2 ty. v1 = hol_Var n1 ty /\ v2 = hol_Var n2 ty`
    ASSUME_TAC THENL
   [EXPAND_TAC "ilist'" THEN REWRITE_TAC[MEM_FILTER] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[typeof_def; CONS_11; injectivity "hol_type"] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `sig:sig` THEN ASM_REWRITE_TAC[MEM; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* HOL4's unused n1 has a type variable as its type; here mlstring *)
let typeof_vsubst1 = prove
 (`!tm ilist sig.
     hol_term_ok sig tm /\
     (!v1 v2. MEM (v1,v2) ilist
              ==> ?(n1:mlstring) n2 ty. v1 has_type ty /\ v2 = hol_Var n2 ty)
     ==> typeof (VSUBST ilist tm) = typeof tm`,
  MATCH_MP_TAC hol_term_INDUCT THEN REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[VSUBST_def] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`ilist:(hol_term#hol_term)list`; `hol_Var a0 a1`; `hol_Var a0 a1`]
             REV_ASSOCD_MEM) THEN STRIP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME
        `MEM (REV_ASSOCD (hol_Var a0 a1) ilist (hol_Var a0 a1),hol_Var a0 a1) ilist`)) THEN
      STRIP_TAC THEN IMP_RES_TAC has_type_typeof THEN GVS[typeof_def];
      ASM_REWRITE_TAC[]];
    SIMP[VSUBST_def];
    REWRITE_TAC[VSUBST_def; hol_term_ok_def; typeof_def] THEN REPEAT STRIP_TAC THEN
    AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `sig:sig` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`bv:hol_term`; `t:hol_term`] THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[hol_term_ok_def] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[CLITAUX_VSUBST_Abs_Var] THEN
  ABBREV_TAC `ilist' = FILTER (\(s',s). ~(s = hol_Var x ty)) (ilist:(hol_term#hol_term)list)` THEN
  SUBGOAL_THEN `!v1 v2. MEM (v1,v2) (ilist':(hol_term#hol_term)list)
                  ==> ?(n1:mlstring) n2 ty. v1 has_type ty /\ v2 = hol_Var n2 ty`
    ASSUME_TAC THENL
   [EXPAND_TAC "ilist'" THEN REWRITE_TAC[MEM_FILTER] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[typeof_def; CONS_11; injectivity "hol_type"] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `sig:sig` THEN ASM_REWRITE_TAC[MEM; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[has_type_rules]);;

let VFREE_IN_VSUBST_OUT = prove
 (`!tm ilist sig n ty.
     hol_term_ok sig tm /\
     (!v1 v2. MEM (v1,v2) ilist ==> ?n1 n2 ty. v1 = hol_Var n1 ty /\ v2 = hol_Var n2 ty) /\
     (?vin. MEM (vin,hol_Var n ty) ilist) /\
     (!vout vin. MEM (vin,vout) ilist ==> ~(vin = hol_Var n ty))
     ==> ~VFREE_IN (hol_Var n ty) (VSUBST ilist tm)`,
  MATCH_MP_TAC hol_term_INDUCT THEN REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[VSUBST_def] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`ilist:(hol_term#hol_term)list`; `hol_Var a0 a1`; `hol_Var a0 a1`]
             REV_ASSOCD_MEM) THEN STRIP_TAC THENL
     [RES_TAC THEN GVS[VFREE_IN_def];
      ASM_REWRITE_TAC[VFREE_IN_def; injectivity "hol_term"] THEN STRIP_TAC THEN
      FIRST_X_ASSUM SUBST_ALL_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP rev_assocd_default_cases) THEN ASM_MESON_TAC[]];
    SIMP[VSUBST_def; VFREE_IN_def; distinctness "hol_term"];
    REWRITE_TAC[VSUBST_def; VFREE_IN_def; hol_term_ok_def; DE_MORGAN_THM] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `sig:sig` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`bv:hol_term`; `t:hol_term`] THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[hol_term_ok_def; LEFT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:mlstring`; `xty:hol_type`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[CLITAUX_VSUBST_Abs_Var] THEN
  ABBREV_TAC `ilist' = FILTER (\(s',s). ~(s = hol_Var x xty)) (ilist:(hol_term#hol_term)list)` THEN
  ABBREV_TAC `z = hol_Var (VARIANT (VSUBST ilist' t) (explode x) xty) xty` THEN
  SUBGOAL_THEN `!v1 v2. MEM (v1,v2) (ilist':(hol_term#hol_term)list) <=>
                        MEM (v1,v2) ilist /\ ~(v2 = hol_Var x xty)`
    ASSUME_TAC THENL
   [EXPAND_TAC "ilist'" THEN REWRITE_TAC[MEM_FILTER] THEN
    CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN MESON_TAC[];
    ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[VFREE_IN_def; DE_MORGAN_THM] THENL
   [ASM_CASES_TAC `z = hol_Var n ty` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o SPECL [`CONS (z:hol_term,hol_Var x xty) ilist'`; `sig:sig`;
                                        `n:mlstring`; `ty:hol_type`]) THEN
    ASM_REWRITE_TAC[MEM; PAIR_EQ] THEN REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
       [MAP_EVERY EXISTS_TAC
          [`VARIANT (VSUBST (ilist':(hol_term#hol_term)list) t) (explode x) xty`;
           `x:mlstring`; `xty:hol_type`] THEN ASM_REWRITE_TAC[];
        ASM_MESON_TAC[]];
      ASM_MESON_TAC[];
      ASM_MESON_TAC[]];
    ASM_CASES_TAC `hol_Var x xty = hol_Var n ty` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o SPECL [`ilist':(hol_term#hol_term)list`; `sig:sig`;
                                        `n:mlstring`; `ty:hol_type`]) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

let VSUBST_ID = prove
 (`!tm ilist sig.
     hol_term_ok sig tm /\
     (!v1 v2. MEM (v1,v2) ilist ==> v1 = v2 /\ (?n ty. v1 = hol_Var n ty))
     ==> VSUBST ilist tm = tm`,
  MATCH_MP_TAC hol_term_INDUCT THEN REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[VSUBST_def] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`ilist:(hol_term#hol_term)list`; `hol_Var a0 a1`; `hol_Var a0 a1`]
             REV_ASSOCD_MEM) THEN STRIP_TAC THEN ASM_MESON_TAC[];
    SIMP[VSUBST_def];
    REWRITE_TAC[VSUBST_def; hol_term_ok_def; injectivity "hol_term"] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `sig:sig` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`bv:hol_term`; `t:hol_term`] THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[hol_term_ok_def] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[CLITAUX_VSUBST_Abs_Var] THEN
  ABBREV_TAC `ilist' = FILTER (\(s',s). ~(s = hol_Var x ty)) (ilist:(hol_term#hol_term)list)` THEN
  SUBGOAL_THEN `!v1 v2. MEM (v1,v2) (ilist':(hol_term#hol_term)list)
                  ==> v1 = v2 /\ (?n ty. v1 = hol_Var n ty) /\ ~(v2 = hol_Var x ty)`
    ASSUME_TAC THENL
   [EXPAND_TAC "ilist'" THEN REWRITE_TAC[MEM_FILTER] THEN
    CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~EX (\(s',s). VFREE_IN (hol_Var x ty) s' /\ VFREE_IN s t)
                    (ilist':(hol_term#hol_term)list)`
    (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[GSYM EX_MEM; EXISTS_PAIR_THM] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
    REPEAT STRIP_TAC THEN RES_TAC THEN GVS[VFREE_IN_def];
    ALL_TAC] THEN
  AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `sig:sig` THEN
  ASM_MESON_TAC[]);;

let esubst_ty0_impossible1 = prove
 (`!env sigma avds tm sig.
     esubsts_ok sig sigma /\
     (!k v. MEM (v,k) env ==> ?n ty. k = hol_Var n (ty_esubst sigma ty) /\ v = hol_Var n ty) /\
     hol_term_ok sig tm
     ==> (!e. esubst_ty0 env sigma avds tm = errorMonad_error e
              ==> ?n typ1 typ2.
                    (n,typ1) IN FVs tm /\
                    ty_esubst sigma typ1 = ty_esubst sigma typ2 /\
                    ~(typ1 = typ2) /\
                    REV_ASSOCD (hol_Var n (ty_esubst sigma typ1)) env (hol_Var n typ1) =
                      hol_Var n typ2 /\
                    e = hol_Var n (ty_esubst sigma typ1)) /\
         (!n typ1 typ2.
            (n,typ1) IN FVs tm /\
            ty_esubst sigma typ1 = ty_esubst sigma typ2 /\
            ~(typ1 = typ2) /\
            REV_ASSOCD (hol_Var n (ty_esubst sigma typ1)) env (hol_Var n typ1) =
              hol_Var n typ2
            ==> ?e. esubst_ty0 env sigma avds tm = errorMonad_error e) /\
         (!subst_tm. esubst_ty0 env sigma avds tm = errorMonad_return subst_tm
                     ==> typeof subst_tm = ty_esubst sigma (typeof tm) /\
                         (!n. MEM n (tm_names tm) ==> MEM n (tm_names subst_tm)))`,
  MATCH_MP_TAC esubst_ty0_ind THEN REPEAT CONJ_TAC THENL
   [(* Var *)
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    REWRITE_TAC[esubst_ty0_def; FVs_def; IN_SING; PAIR_EQ; tm_names_def; MEM] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    COND_CASES_TAC THEN REWRITE_TAC[distinctness "error"; injectivity "error"] THENL
     [CONJ_TAC THENL
       [REPEAT STRIP_TAC THEN GVS[injectivity "hol_term"];
        REPEAT STRIP_TAC THEN GVS[typeof_def; tm_names_def; MEM]];
      CONJ_TAC THENL
       [REPEAT STRIP_TAC THEN
        FIRST_ASSUM(MP_TAC o MATCH_MP rev_assocd_neq_mem) THEN
        DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th)) THEN
        DISCH_THEN(X_CHOOSE_THEN `n2:mlstring`
          (X_CHOOSE_THEN `ty2:hol_type` STRIP_ASSUME_TAC)) THEN
        RULE_ASSUM_TAC(REWRITE_RULE[injectivity "hol_term"]) THEN
        MAP_EVERY EXISTS_TAC [`n:mlstring`; `ty:hol_type`; `ty2:hol_type`] THEN
        ASM_MESON_TAC[];
        MESON_TAC[]]];
    (* Const *)
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    REWRITE_TAC[esubst_ty0_def; FVs_def; NOT_IN_EMPTY; distinctness "error";
                injectivity "error"] THEN
    REPEAT STRIP_TAC THEN GVS[typeof_def; tm_names_def; MEM];
    (* Comb *)
    REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `sig:sig` THEN STRIP_TAC THEN
    SUBGOAL_THEN `hol_term_ok sig t1 /\ hol_term_ok sig t2 /\ welltyped (hol_Comb t1 t2)`
      STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[hol_term_ok_def]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `sig:sig`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `sig:sig`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    REWRITE_TAC[esubst_ty0_def; bind_EQ_error; bind_EQ_return; FVs_def; IN_UNION;
                tm_names_def; MEM_APPEND; distinctness "error"; injectivity "error"] THEN
    REPEAT CONJ_TAC THENL
     [GEN_TAC THEN STRIP_TAC THEN RES_TAC THEN ASM_MESON_TAC[];
      REPEAT STRIP_TAC THEN RES_TAC THEN ASM_MESON_TAC[cases "error"];
      GEN_TAC THEN DISCH_THEN(X_CHOOSE_THEN `u:hol_term` (CONJUNCTS_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN `u':hol_term` (CONJUNCTS_THEN2 ASSUME_TAC (SUBST_ALL_TAC o SYM))))) THEN
      RES_TAC THEN ASM_REWRITE_TAC[typeof_def; tm_names_def; MEM_APPEND] THEN CONJ_TAC THENL
       [UNDISCH_TAC `welltyped (hol_Comb t1 t2)` THEN
        REWRITE_TAC[welltyped_def; has_type_comb] THEN
        STRIP_TAC THEN IMP_RES_TAC has_type_typeof THEN ASM_REWRITE_TAC[] THEN
        ASM_SIMP_TAC[MATCH_MP ty_esubst_fun (ASSUME `esubsts_ok sig sigma`); codomain_def];
        ASM_MESON_TAC[]]];
    ALL_TAC] THEN
  (* Abs *)
  MAP_EVERY X_GEN_TAC [`env:(hol_term#hol_term)list`;
     `sigma:(mlstring,mlstring list#hol_type)fmap#(mlstring,hol_term#hol_type)fmap`;
     `avds:mlstring list`; `v:hol_term`; `body:hol_term`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ihc") (CONJUNCTS_THEN2 (LABEL_TAC "ihb")
    (LABEL_TAC "iha"))) THEN
  X_GEN_TAC `sig:sig` THEN
  REWRITE_TAC[hol_term_ok_def; LEFT_AND_EXISTS_THM; RIGHT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:mlstring`; `ty:hol_type`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  REMOVE_THEN "iha" (MP_TAC o SPECL [`x:mlstring`; `ty:hol_type`]) THEN
  REWRITE_TAC[dest_var_def] THEN DISCH_THEN(MP_TAC o SPEC `sig:sig`) THEN
  ASM_REWRITE_TAC[MEM; PAIR_EQ] THEN ANTS_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC] THEN
  REMOVE_THEN "ihb" (MP_TAC o SPECL
    [`hol_Var x (ty_esubst (sigma:(mlstring,mlstring list#hol_type)fmap#
                                  (mlstring,hol_term#hol_type)fmap) ty)`;
     `x:mlstring`; `ty:hol_type`]) THEN
  REWRITE_TAC[dest_var_def] THEN DISCH_THEN(MP_TAC o SPEC `sig:sig`) THEN
  ASM_REWRITE_TAC[MEM; REV_ASSOCD_def; injectivity "hol_term"] THEN STRIP_TAC THEN
  REMOVE_THEN "ihc" (MP_TAC o SPECL
    [`hol_Var x (ty_esubst (sigma:(mlstring,mlstring list#hol_type)fmap#
                                  (mlstring,hol_term#hol_type)fmap) ty)`]) THEN
  REWRITE_TAC[dest_var_def; PAIR_EQ] THEN
  DISCH_THEN(MP_TAC o GEN `body1:hol_term` o SPECL [`body1:hol_term`; `x:mlstring`; `ty:hol_type`]) THEN
  REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "ihc") THEN
  SUBGOAL_THEN `?b1. esubst_ty0 [] sigma avds body = errorMonad_return b1`
    (X_CHOOSE_THEN `b1:hol_term` ASSUME_TAC) THENL
   [REWRITE_TAC[GSYM neq_error] THEN GEN_TAC THEN DISCH_TAC THEN RES_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!m. MEM m (tm_names body) ==> MEM m (tm_names b1)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!typ. ~((NVARIANT x avds b1,typ) IN FVs body)` ASSUME_TAC THENL
   [ASM_MESON_TAC[NVARIANT_NAMES_THM; FVs_in_tm_names]; ALL_TAC] THEN
  REMOVE_THEN "ihc" (MP_TAC o SPECL [`b1:hol_term`; `sig:sig`]) THEN
  ASM_SIMP_TAC[term_ok_vsubst_variant; MEM; PAIR_EQ] THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; STRIP_TAC] THEN
  REWRITE_TAC[esubst_ty0_def; dest_var_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[pair_CASE] THEN ASM_REWRITE_TAC[errorMonad_bind_def] THEN
  MP_TAC(ISPEC `esubst_ty0 (CONS (hol_Var x ty,hol_Var x (ty_esubst sigma ty)) env) sigma avds
                  body` (cases "error")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `b0:hol_term` ASSUME_TAC)
                              (X_CHOOSE_THEN `e0:hol_term` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[little_try_def; errorMonad_bind_def; distinctness "error";
                  injectivity "error"] THENL
   [(* the first call returns *)
    CONJ_TAC THENL
     [REPEAT GEN_TAC THEN REWRITE_TAC[FVs_def; IN_DIFF; IN_SING; PAIR_EQ] THEN STRIP_TAC THEN
      SUBGOAL_THEN `?e. esubst_ty0 (CONS (hol_Var x ty,hol_Var x (ty_esubst sigma ty)) env)
                          (sigma:(mlstring,mlstring list#hol_type)fmap#
                                 (mlstring,hol_term#hol_type)fmap)
                          avds body = errorMonad_error e` MP_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN
        CLITAUX_QASM_CASES_TAC "n:mlstring = x /\\ ty_esubst sigma typ1 = ty_esubst sigma ty"
        THENL
         [MAP_EVERY EXISTS_TAC [`x:mlstring`; `typ1:hol_type`; `ty:hol_type`] THEN
          FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC) THEN
          ASM_REWRITE_TAC[REV_ASSOCD] THEN ASM_MESON_TAC[];
          MAP_EVERY EXISTS_TAC [`n:mlstring`; `typ1:hol_type`; `typ2:hol_type`] THEN
          ASM_REWRITE_TAC[REV_ASSOCD; injectivity "hol_term"] THEN
          ASM_MESON_TAC[]];
        ASM_REWRITE_TAC[distinctness "error"]];
      GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      FIRST_X_ASSUM(fun th -> MP_TAC(MATCH_MP th (ASSUME
        `esubst_ty0 (CONS (hol_Var x ty,hol_Var x (ty_esubst sigma ty)) env)
           (sigma:(mlstring,mlstring list#hol_type)fmap#(mlstring,hol_term#hol_type)fmap)
           avds body = errorMonad_return b0`))) THEN
      REWRITE_TAC[typeof_def; tm_names_def; MEM; APPEND] THEN STRIP_TAC THEN
      ASM_SIMP_TAC[MATCH_MP ty_esubst_fun (ASSUME `esubsts_ok sig sigma`)] THEN
      ASM_MESON_TAC[]];
    (* the first call fails *)
    ALL_TAC] THEN
  CLITAUX_QASM_CASES_TAC "e0 = hol_Var x (ty_esubst sigma ty)" THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(MATCH_MP th (ASSUME
    `esubst_ty0 (CONS (hol_Var x ty,hol_Var x (ty_esubst sigma ty)) env)
       (sigma:(mlstring,mlstring list#hol_type)fmap#(mlstring,hol_term#hol_type)fmap)
       avds body = errorMonad_error e0`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `n0:mlstring` (X_CHOOSE_THEN `typ0:hol_type`
    (X_CHOOSE_THEN `typ0':hol_type` STRIP_ASSUME_TAC))) THENL
   [ALL_TAC;
    (* not the bound variable: the same error *)
    REWRITE_TAC[distinctness "error"; injectivity "error"] THEN
    CONJ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
    GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MAP_EVERY EXISTS_TAC [`n0:mlstring`; `typ0:hol_type`; `typ0':hol_type`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REV_ASSOCD]) THEN
    ASM_REWRITE_TAC[FVs_def; IN_DIFF; IN_SING; PAIR_EQ] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[injectivity "hol_term"]) THEN
    ASM_MESON_TAC[]] THEN
  (* the bound variable clashes: renaming *)
  CLITAUX_QSUBGOAL_THEN "n0 = x /\\ ty_esubst sigma typ0 = ty_esubst sigma ty /\\ typ0' = ty"
    STRIP_ASSUME_TAC THENL
   [CLITAUX_QUNDISCH_TAC "REV_ASSOCD (hol_Var n0 (ty_esubst sigma typ0))
      (CONS (hol_Var x ty,hol_Var x (ty_esubst sigma ty)) env)
      (hol_Var n0 typ0) = hol_Var n0 typ0'" THEN
    CLITAUX_QSUBGOAL_THEN "hol_Var x (ty_esubst sigma ty) = hol_Var n0 (ty_esubst sigma typ0)"
      MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[injectivity "hol_term"] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[REV_ASSOCD; injectivity "hol_term"] THEN MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `nn = NVARIANT x avds b1` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `NVARIANT x avds b1 = nn`]) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MP_TAC(ISPEC `esubst_ty0 (CONS (hol_Var nn ty,hol_Var nn (ty_esubst sigma ty)) env)
                  (sigma:(mlstring,mlstring list#hol_type)fmap#(mlstring,hol_term#hol_type)fmap)
                  avds (VSUBST [hol_Var nn ty,hol_Var x ty] body)` (cases "error")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `b3:hol_term` ASSUME_TAC)
                              (X_CHOOSE_THEN `e3:hol_term` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[errorMonad_bind_def; distinctness "error"; injectivity "error"] THENL
   [(* the renamed call returns *)
    CONJ_TAC THENL
     [REPEAT GEN_TAC THEN REWRITE_TAC[FVs_def; IN_DIFF; IN_SING; PAIR_EQ] THEN STRIP_TAC THEN
      CLITAUX_QSUBGOAL_THEN
        "?e. esubst_ty0 (CONS (hol_Var nn ty,hol_Var nn (ty_esubst sigma ty)) env)
               sigma avds (VSUBST [hol_Var nn ty,hol_Var x ty] body) = errorMonad_error e"
        MP_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN
        MAP_EVERY EXISTS_TAC [`n:mlstring`; `typ1:hol_type`; `typ2:hol_type`] THEN
        ASM_REWRITE_TAC[MATCH_MP FVs_VSUBST_CASES (ASSUME `hol_term_ok sig body`)] THEN
        ASM_REWRITE_TAC[REV_ASSOCD; injectivity "hol_term"] THEN
        SUBGOAL_THEN `~(nn:mlstring = n)` (fun th -> REWRITE_TAC[th]) THEN ASM_MESON_TAC[];
        ASM_REWRITE_TAC[distinctness "error"]];
      GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      FIRST_X_ASSUM(fun th -> MP_TAC(MATCH_MP th (ASSUME
        `esubst_ty0 (CONS (hol_Var nn ty,hol_Var nn (ty_esubst sigma ty)) env)
           (sigma:(mlstring,mlstring list#hol_type)fmap#(mlstring,hol_term#hol_type)fmap)
           avds (VSUBST [hol_Var nn ty,hol_Var x ty] body) = errorMonad_return b3`))) THEN
      SUBGOAL_THEN `typeof (VSUBST [hol_Var nn ty,hol_Var x ty] body) = typeof body`
        (fun th -> REWRITE_TAC[th]) THENL
       [MATCH_MP_TAC typeof_vsubst THEN EXISTS_TAC `sig:sig` THEN
        ASM_REWRITE_TAC[MEM; PAIR_EQ] THEN MESON_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[typeof_def; tm_names_def; MEM; APPEND] THEN STRIP_TAC THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[MATCH_MP ty_esubst_fun (ASSUME `esubsts_ok sig sigma`)]; ALL_TAC] THEN
      X_GEN_TAC `m:mlstring` THEN DISCH_TAC THEN
      ASM_CASES_TAC `m:mlstring = x` THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN DISJ2_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        MATCH_MP_TAC tm_names_vsubst THEN
        MAP_EVERY EXISTS_TAC [`typ0:hol_type`; `sig:sig`] THEN
        ASM_MESON_TAC[FVs_in_tm_names];
        DISJ2_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        MATCH_MP_TAC tm_names_vsubst_different_name THEN EXISTS_TAC `sig:sig` THEN
        ASM_REWRITE_TAC[MEM; MAP; ALL_DISTINCT; hol_term_ok_def] THEN
        CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
        GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
        MAP_EVERY EXISTS_TAC [`nn:mlstring`; `x:mlstring`; `ty:hol_type`] THEN
        ASM_REWRITE_TAC[]]];
    (* the renamed call fails *)
    CONJ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
    GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    FIRST_X_ASSUM(fun th -> MP_TAC(MATCH_MP th (ASSUME
      `esubst_ty0 (CONS (hol_Var nn ty,hol_Var nn (ty_esubst sigma ty)) env)
         (sigma:(mlstring,mlstring list#hol_type)fmap#(mlstring,hol_term#hol_type)fmap)
         avds (VSUBST [hol_Var nn ty,hol_Var x ty] body) = errorMonad_error e3`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `n3:mlstring` (X_CHOOSE_THEN `typ3:hol_type`
      (X_CHOOSE_THEN `typ3':hol_type` STRIP_ASSUME_TAC))) THEN
    MAP_EVERY EXISTS_TAC [`n3:mlstring`; `typ3:hol_type`; `typ3':hol_type`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP FVs_VSUBST_CASES (ASSUME `hol_term_ok sig body`);
                                REV_ASSOCD; injectivity "hol_term"; COND_CASE_EQ]) THEN
    ASM_REWRITE_TAC[FVs_def; IN_DIFF; IN_SING; PAIR_EQ] THEN
    ASM_MESON_TAC[]]);;

let esubst_ty0_always_returns = prove
 (`!sigma tm sig avds.
     esubsts_ok sig sigma /\ hol_term_ok sig tm
     ==> ?v. esubst_ty0 [] sigma avds tm = errorMonad_return v`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`[]:(hol_term#hol_term)list`; `sigma:(mlstring,mlstring list#hol_type)fmap#
                                                  (mlstring,hol_term#hol_type)fmap`;
                 `avds:mlstring list`; `tm:hol_term`; `sig:sig`] esubst_ty0_impossible1) THEN
  ASM_REWRITE_TAC[MEM; REV_ASSOCD_def; injectivity "hol_term"] THEN
  REWRITE_TAC[GSYM neq_error] THEN MESON_TAC[]);;

let esubst_comb = prove
 (`!t1 t2 sig sigma avds.
     esubsts_ok sig sigma /\ hol_term_ok sig t1 /\ hol_term_ok sig t2
     ==> esubst sigma avds (hol_Comb t1 t2) =
         hol_Comb (esubst sigma avds t1) (esubst sigma avds t2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?v1. esubst_ty0 [] sigma avds t1 = errorMonad_return v1` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[esubst_ty0_always_returns]; ALL_TAC] THEN
  SUBGOAL_THEN `?v2. esubst_ty0 [] sigma avds t2 = errorMonad_return v2` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[esubst_ty0_always_returns]; ALL_TAC] THEN
  ASM_REWRITE_TAC[esubst_def; esubst_ty_def; esubst_ty0_def; errorMonad_bind_def;
                  esubst_tm_def; case_def "error"]);;
let _ = cake_add_simps [esubst_comb];;

let esubst_ty_comb = prove
 (`!t1 t2 sig sigma avds.
     esubsts_ok sig sigma /\ hol_term_ok sig t1 /\ hol_term_ok sig t2
     ==> esubst_ty sigma avds (hol_Comb t1 t2) =
         hol_Comb (esubst_ty sigma avds t1) (esubst_ty sigma avds t2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?v1. esubst_ty0 [] sigma avds t1 = errorMonad_return v1` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[esubst_ty0_always_returns]; ALL_TAC] THEN
  SUBGOAL_THEN `?v2. esubst_ty0 [] sigma avds t2 = errorMonad_return v2` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[esubst_ty0_always_returns]; ALL_TAC] THEN
  ASM_REWRITE_TAC[esubst_ty_def; esubst_ty0_def; errorMonad_bind_def; case_def "error"]);;
let _ = cake_add_simps [esubst_ty_comb];;

let typeof_esubst_ty = prove
 (`!tm tm1 sig sigma theta env avds.
     esubsts_ok sig (sigma,theta) /\
     hol_term_ok sig tm /\
     (!k v. MEM (v,k) env
            ==> ?n ty. k = hol_Var n (ty_esubst (sigma,theta) ty) /\ v = hol_Var n ty) /\
     esubst_ty0 env (sigma,theta) avds tm = errorMonad_return tm1
     ==> typeof tm1 = ty_esubst (sigma,theta) (typeof tm)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`env:(hol_term#hol_term)list`; `(sigma,theta):(mlstring,mlstring list#hol_type)fmap#
                                                  (mlstring,hol_term#hol_type)fmap`;
                 `avds:mlstring list`; `tm:hol_term`; `sig:sig`] esubst_ty0_impossible1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `tm1:hol_term` o CONJUNCT2 o CONJUNCT2) THEN
  ASM_SIMP_TAC[]);;
