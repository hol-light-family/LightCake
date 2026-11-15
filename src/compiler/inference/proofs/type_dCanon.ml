(* ========================================================================= *)
(* type_dCanon: port of HOL4 compiler/inference/proofs/type_dCanonScript.sml *)
(* (CakeML v3479).  For any type_d, prove that the canonical type            *)
(* identifier strategy succeeds.                                             *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/namespace.ml";;
needs "semantics/typeSystem.ml";;
needs "semantics/proofs/namespaceProps.ml";;
needs "semantics/proofs/typeSysProps.ml";;
needs "semantics/proofs/typeSoundInvariants.ml";;
needs "compiler/inference/inferProps.ml";;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Notes on the rendering:                                                   *)
(* - Records: tenv.v is type_env_v tenv, record literals are type_env_REC.   *)
(* - HOL4 EVERY is ALL, LIST_REL is ALL2, set is set_of_list, BIGUNION is    *)
(*   UNIONS, FOLDR f e l is ITLIST f l e, GENLIST f n is list_of_seq f n.    *)
(* - The free variables of a HOL4 statement are universally quantified.      *)
(* - HOL4 [local] theorems are kept (they are ordinary theorems here).       *)
(* - Helper lemmas that are not HOL4 theorems are INFER1AUX_.                *)
(* ------------------------------------------------------------------------- *)

(* HOL4 comment: TODO: move *)

let tenv_equiv_def = cake_def
  `tenv_equiv (tenv1:type_env) (tenv2:type_env) <=>
     nsAll2 (\i v1 v2. v1 = v2) (type_env_t tenv1) (type_env_t tenv2) /\
     nsAll2 (\i v1 v2. v1 = v2) (type_env_c tenv1) (type_env_c tenv2) /\
     nsAll2 (\i v1 v2. v1 = v2) (type_env_v tenv1) (type_env_v tenv2)`;;

let INFER1AUX_nsAll2_eq_refl = prove
 (`!e:(M,N,V)namespace. nsAll2 (\i v1 v2. v1 = v2) e e`,
  REWRITE_TAC[nsAll2_def; nsSub_def] THEN MESON_TAC[]);;

let INFER1AUX_nsAll2_eq_sym = prove
 (`!e1 e2:(M,N,V)namespace.
     nsAll2 (\i v1 v2. v1 = v2) e1 e2 ==> nsAll2 (\i v1 v2. v1 = v2) e2 e1`,
  REWRITE_TAC[nsAll2_def; nsSub_def] THEN MESON_TAC[]);;

let INFER1AUX_NOT_NONE = prove
 (`!x:A option. ~(x = NONE) <=> ?v. x = SOME v`,
  MESON_TAC[cases "option"; option_DISTINCT]);;

let INFER1AUX_nsAll2_eq_lookup = prove
 (`!e1 e2:(M,N,V)namespace n.
     nsAll2 (\i v1 v2. v1 = v2) e1 e2 ==> nsLookup e1 n = nsLookup e2 n`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `nsLookup (e1:(M,N,V)namespace) n = NONE` THENL
   [ASM_MESON_TAC[nsAll2_nsLookup_none]; ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `v:V` o REWRITE_RULE[INFER1AUX_NOT_NONE]) THEN
  MP_TAC(ISPECL [`\(i:(M,N)id) (v1:V) (v2:V). v1 = v2`; `e1:(M,N,V)namespace`;
                 `e2:(M,N,V)namespace`; `n:(M,N)id`; `v:V`] nsAll2_nsLookup1) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let tenv_equiv_refl = prove
 (`!tenv. tenv_equiv tenv tenv`,
  REWRITE_TAC[tenv_equiv_def; INFER1AUX_nsAll2_eq_refl]);;
let _ = cake_add_simps [tenv_equiv_refl];;

let tenv_equiv_sym = prove
 (`!t1 t2. tenv_equiv t1 t2 ==> tenv_equiv t2 t1`,
  REWRITE_TAC[tenv_equiv_def] THEN MESON_TAC[INFER1AUX_nsAll2_eq_sym]);;

let tenv_equiv_tenvLift = prove
 (`!t1 t2 m. tenv_equiv t1 t2 ==> tenv_equiv (tenvLift m t1) (tenvLift m t2)`,
  REWRITE_TAC[tenv_equiv_def; tenvLift_def; type_env_INFO.ri_accessors; nsAll2_nsLift]);;

let check_type_names_tenv_equiv = prove
 (`!t1 t t2.
     nsAll2 (\i v1 v2. v1 = v2) t1 t2 /\ check_type_names t1 t ==> check_type_names t2 t`,
  MATCH_MP_TAC check_type_names_ind THEN REWRITE_TAC[check_type_names_def] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN REPEAT GEN_TAC THEN
  STRIP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[EVERY_MEM]) THEN
  REWRITE_TAC[EVERY_MEM] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP INFER1AUX_nsAll2_eq_lookup th)]) THEN
  ASM_MESON_TAC[]);;

let lookup_var_tenv_equiv = prove
 (`!tenv1 tenv2 n bvs.
     tenv_equiv tenv1 tenv2 ==> lookup_var n bvs tenv1 = lookup_var n bvs tenv2`,
  REWRITE_TAC[tenv_equiv_def; lookup_var_def] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP INFER1AUX_nsAll2_eq_lookup th]));;

(* HOL4 ast_t_ind (a local ML value of the script): ast_t_induction        *)
(* specialised to P and EVERY P                                              *)
let INFER1AUX_ast_t_ind = prove
 (`!P. (!a. P (Atvar a)) /\
       (!t1 t2. P t1 /\ P t2 ==> P (Atfun t1 t2)) /\
       (!l. ALL P l ==> P (Attup l)) /\
       (!l n. ALL P l ==> P (Atapp l n))
       ==> !t. P t`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`P:ast_t->bool`; `ALL (P:ast_t->bool)`] ast_t_INDUCT) THEN
  ASM_SIMP_TAC[ALL]);;

let type_name_subst_tenv_equiv = prove
 (`!t1 t t2.
     nsAll2 (\i v1 v2. v1 = v2) t1 t2 ==> type_name_subst t1 t = type_name_subst t2 t`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN SPEC_TAC(`t:ast_t`,`t:ast_t`) THEN
  MATCH_MP_TAC INFER1AUX_ast_t_ind THEN
  REWRITE_TAC[type_name_subst_def; LET_DEF; LET_END_DEF; EVERY_MEM] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP INFER1AUX_nsAll2_eq_lookup th]) THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `MAP (type_name_subst t1) l = MAP (type_name_subst t2) l` SUBST1_TAC THEN
  REWRITE_TAC[MAP_EQ_f] THEN ASM_MESON_TAC[]);;

(* apply one of the rules of an inductive definition (backward) *)
let INFER1AUX_RULE_TAC rules : tactic =
  FIRST (map (fun th g -> try MATCH_MP_TAC th g with Failure _ -> MATCH_ACCEPT_TAC th g)
             (CONJUNCTS rules));;

let INFER1AUX_EQUIV_LOOKUP_TAC =
  ASSUM_LIST(fun ths ->
    REWRITE_TAC(mapfilter (GSYM o MATCH_MP INFER1AUX_nsAll2_eq_lookup) ths));;

let type_p_tenv_equiv = prove
 (`(!tvs tenv1 p t bindings.
      type_p tvs tenv1 p t bindings
      ==> !tenv2. tenv_equiv tenv1 tenv2 ==> type_p tvs tenv2 p t bindings) /\
   (!tvs tenv1 ps ts bindings.
      type_ps tvs tenv1 ps ts bindings
      ==> !tenv2. tenv_equiv tenv1 tenv2 ==> type_ps tvs tenv2 ps ts bindings)`,
  MATCH_MP_TAC type_p_ind THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[tenv_equiv_def]) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP type_name_subst_tenv_equiv th]) THEN
  INFER1AUX_RULE_TAC type_p_rules THEN
  ASM_SIMP_TAC[] THEN INFER1AUX_EQUIV_LOOKUP_TAC THEN
  ASM_MESON_TAC[check_type_names_tenv_equiv; type_name_subst_tenv_equiv]);;

let type_e_tenv_equiv = prove
 (`(!tenv1 bvs e t.
      type_e tenv1 bvs e t
      ==> !tenv2. tenv_equiv tenv1 tenv2 ==> type_e tenv2 bvs e t) /\
   (!tenv1 bvs es ts.
      type_es tenv1 bvs es ts
      ==> !tenv2. tenv_equiv tenv1 tenv2 ==> type_es tenv2 bvs es ts) /\
   (!tenv1 bvs funs ts.
      type_funs tenv1 bvs funs ts
      ==> !tenv2. tenv_equiv tenv1 tenv2 ==> type_funs tenv2 bvs funs ts)`,
  MATCH_MP_TAC type_e_ind THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[tenv_equiv_def]) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP type_name_subst_tenv_equiv th]) THEN
  INFER1AUX_RULE_TAC type_e_rules THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP lookup_var_tenv_equiv th)]) THEN
  ASM_SIMP_TAC[] THEN INFER1AUX_EQUIV_LOOKUP_TAC THEN
  TRY(ASM_MESON_TAC[check_type_names_tenv_equiv; type_name_subst_tenv_equiv]) THEN
  TRY(EXISTS_TAC `t1:t`) THEN ASM_SIMP_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`p':pat`; `e':exp`] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`p':pat`; `e':exp`]) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN EXISTS_TAC `bindings:(mlstring#t)list` THEN ASM_SIMP_TAC[] THEN
  ASM_MESON_TAC[type_p_tenv_equiv]);;

let type_pe_determ_tenv_equiv = prove
 (`!t1 x y z t2.
     type_pe_determ t1 x y z /\ tenv_equiv t1 t2 ==> type_pe_determ t2 x y z`,
  REWRITE_TAC[type_pe_determ_def] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP tenv_equiv_sym) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`t1':t`; `t2':t`] THEN
  ASM_MESON_TAC[type_p_tenv_equiv; type_e_tenv_equiv]);;

(* -- *)

(* all the tids used in a tenv *)
let set_tids_tenv_def = cake_def
  `set_tids_tenv (tids:num->bool) (tenv:type_env) <=>
     nsAll (\i p. match p with (ls,t) -> set_tids_subset tids t) (type_env_t tenv) /\
     nsAll (\i p. match p with
                    (ls,ts,tid) -> ALL (\t. set_tids_subset tids t) ts /\ tid IN tids)
           (type_env_c tenv) /\
     nsAll (\i p. match p with (n,t) -> set_tids_subset tids t) (type_env_v tenv)`;;

let type_pe_determ_canon_def = cake_def
  `type_pe_determ_canon (n:num) (tenv:type_env) (tenvE:tenv_val_exp) (p:pat) (e:exp) <=>
     !t1 tenv1 t2 tenv2.
       type_p 0 tenv p t1 tenv1 /\ type_e tenv tenvE e t1 /\
       ALL (\(k:mlstring,t). set_tids_subset (count n) t) tenv1 /\
       type_p 0 tenv p t2 tenv2 /\ type_e tenv tenvE e t2 /\
       ALL (\(k:mlstring,t). set_tids_subset (count n) t) tenv2
       ==> tenv1 = tenv2`;;

let type_pe_determ_canon_tenv_equiv = prove
 (`!n t1 x y z t2.
     type_pe_determ_canon n t1 x y z /\ tenv_equiv t1 t2
     ==> type_pe_determ_canon n t2 x y z`,
  REWRITE_TAC[type_pe_determ_canon_def] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP tenv_equiv_sym) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`t1':t`; `t2':t`] THEN
  ASM_MESON_TAC[type_p_tenv_equiv; type_e_tenv_equiv]);;

(* A "canonical" version of type_d that produces the type identifiers in   *)
(* ascending order.  It also drops the extra_checks argument so it          *)
(* corresponds to type_d T, but adds a starting index, and an argument for  *)
(* the number of type ids that got produced.                                *)

let type_d_canon_rules,type_d_canon_ind,type_d_canon_cases,type_d_canon_strongind =
  cake_inductive
  `(!n tvs tenv p e t bindings locs.
      is_value e /\
      ALL_DISTINCT (pat_bindings p) /\
      type_p tvs tenv p t bindings /\
      type_e tenv (bind_tvar tvs Empty) e t /\
      (!tvs' bindings' t'.
         type_p tvs' tenv p t' bindings' /\
         type_e tenv (bind_tvar tvs' Empty) e t' /\
         ALL (\(k:mlstring,t). set_tids_subset (count n) t) bindings'
         ==> ALL2 tscheme_inst (MAP SND (tenv_add_tvs tvs' bindings'))
                               (MAP SND (tenv_add_tvs tvs bindings)))
      ==> type_d_canon n tenv (Dlet locs p e) 0
            (type_env_REC (alist_to_ns (tenv_add_tvs tvs bindings)) nsEmpty nsEmpty)) /\
   (!n tenv p e t bindings locs.
      (~is_value e /\ type_pe_determ_canon n tenv Empty p e) /\
      ALL_DISTINCT (pat_bindings p) /\
      type_p 0 tenv p t bindings /\
      type_e tenv Empty e t
      ==> type_d_canon n tenv (Dlet locs p e) 0
            (type_env_REC (alist_to_ns (tenv_add_tvs 0 bindings)) nsEmpty nsEmpty)) /\
   (!n tenv funs bindings tvs locs.
      type_funs tenv (bind_var_list 0 bindings (bind_tvar tvs Empty)) funs bindings /\
      (!tvs' bindings'.
         type_funs tenv (bind_var_list 0 bindings' (bind_tvar tvs' Empty)) funs bindings' /\
         ALL (\(k:mlstring,t). set_tids_subset (count n) t) bindings'
         ==> ALL2 tscheme_inst (MAP SND (tenv_add_tvs tvs' bindings'))
                               (MAP SND (tenv_add_tvs tvs bindings)))
      ==> type_d_canon n tenv (Dletrec locs funs) 0
            (type_env_REC (alist_to_ns (tenv_add_tvs tvs bindings)) nsEmpty nsEmpty)) /\
   (!n type_identities tenv tdefs tenvT locs.
      ITLIST MAX (CONS Tlist_num (CONS Tbool_num prim_type_nums)) 0 < n /\
      type_identities = list_of_seq (\i. i + n) (LENGTH tdefs) /\
      check_ctor_tenv (nsAppend tenvT (type_env_t tenv)) tdefs /\
      tenvT = alist_to_ns
                (MAP2 (\tdef i. match tdef with
                                  (tvs,tn,ctors) -> (tn,(tvs,Tapp (MAP Tvar tvs) i)))
                      tdefs type_identities)
      ==> type_d_canon n tenv (Dtype locs tdefs) (LENGTH tdefs)
            (type_env_REC nsEmpty
               (build_ctor_tenv (nsAppend tenvT (type_env_t tenv)) tdefs type_identities)
               tenvT)) /\
   (!n tenv tvs tn t locs.
      check_freevars_ast tvs t /\
      check_type_names (type_env_t tenv) t /\
      ALL_DISTINCT tvs
      ==> type_d_canon n tenv (Dtabbrev locs tvs tn t) 0
            (type_env_REC nsEmpty nsEmpty
               (nsSing tn (tvs,type_name_subst (type_env_t tenv) t)))) /\
   (!n tenv cn ts locs.
      ALL (check_freevars_ast []) ts /\
      ALL (check_type_names (type_env_t tenv)) ts
      ==> type_d_canon n tenv (Dexn locs cn ts) 0
            (type_env_REC nsEmpty
               (nsSing cn ([],MAP (type_name_subst (type_env_t tenv)) ts,Texn_num))
               nsEmpty)) /\
   (!n tenv mn ds decls tenv'.
      type_ds_canon n tenv ds decls tenv'
      ==> type_d_canon n tenv (Dmod mn ds) decls (tenvLift mn tenv')) /\
   (!n tenv lds ds decls1 decls2 tenv1 tenv2.
      type_ds_canon n tenv lds decls1 tenv1 /\
      type_ds_canon (n + decls1) (extend_dec_tenv tenv1 tenv) ds decls2 tenv2
      ==> type_d_canon n tenv (Dlocal lds ds) (decls1 + decls2) tenv2) /\
   (!n tenv.
      T ==> type_ds_canon n tenv [] 0 (type_env_REC nsEmpty nsEmpty nsEmpty)) /\
   (!n tenv d ds tenv1 tenv2 decls1 decls2.
      type_d_canon n tenv d decls1 tenv1 /\
      type_ds_canon (n + decls1) (extend_dec_tenv tenv1 tenv) ds decls2 tenv2
      ==> type_ds_canon n tenv (CONS d ds) (decls1 + decls2)
            (extend_dec_tenv tenv2 tenv1))`;;

(* The remapping must be identity on these numbers *)
let good_remap_def = cake_def
  `good_remap (f:num->num) <=>
     MAP f (CONS Tlist_num (CONS Tbool_num prim_type_nums)) =
     CONS Tlist_num (CONS Tbool_num prim_type_nums)`;;

let ts_tid_rename_type_subst = prove
 (`!s t f.
     ts_tid_rename f (type_subst s t) =
     type_subst (ts_tid_rename f o_f s) (ts_tid_rename f t)`,
  MATCH_MP_TAC type_subst_ind THEN
  REWRITE_TAC[type_subst_def; ts_tid_rename_def] THEN REPEAT CONJ_TAC THEN
  REPEAT GEN_TAC THENL
   [REWRITE_TAC[FLOOKUP_o_f] THEN
    CASES_ON `FLOOKUP (s:(mlstring,t)fmap) tv` THEN CASE_REWRITE_TAC[ts_tid_rename_def];
    DISCH_TAC THEN GEN_TAC THEN REWRITE_TAC[injectivity "t"; MAP_MAP_o; MAP_EQ_f; o_THM] THEN
    ASM_SIMP_TAC[]]);;

let INFER1AUX_good_remap_thm = prove
 (`!f. good_remap f <=>
       f Tlist_num = Tlist_num /\ f Tbool_num = Tbool_num /\
       f Tarray_num = Tarray_num /\ f Tchar_num = Tchar_num /\
       f Texn_num = Texn_num /\ f Tfn_num = Tfn_num /\ f Tint_num = Tint_num /\
       f Tref_num = Tref_num /\ f Tstring_num = Tstring_num /\
       f Ttup_num = Ttup_num /\ f Tvector_num = Tvector_num /\
       f Tword64_num = Tword64_num /\ f Tword8_num = Tword8_num /\
       f Tword8array_num = Tword8array_num /\ f Tdouble_num = Tdouble_num`,
  REWRITE_TAC[good_remap_def; prim_type_nums_def; MAP; CONS_11]);;

let INFER1AUX_o_f_alist_to_fmap_ZIP = prove
 (`!(g:B->C) (l1:A list) l2.
     LENGTH l1 = LENGTH l2
     ==> g o_f alist_to_fmap (ZIP l1 l2) = alist_to_fmap (ZIP l1 (MAP g l2))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[ZIP_MAP; GSYM alist_to_fmap_MAP_values] THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM]);;

let ts_tid_rename_type_name_subst = prove
 (CASE_TERM `!tenvt t f (tenv:A).
     good_remap f /\ check_type_names tenvt t
     ==> ts_tid_rename f (type_name_subst tenvt t) =
         type_name_subst (nsMap (\p. match p with (ls,t) -> (ls,ts_tid_rename f t)) tenvt) t`,
  GEN_TAC THEN MATCH_MP_TAC INFER1AUX_ast_t_ind THEN
  REWRITE_TAC[type_name_subst_def; check_type_names_def; ts_tid_rename_def; LET_DEF;
              LET_END_DEF; EVERY_MEM; typeSystem_Tfn_def; typeSystem_Ttup_def;
              INFER1AUX_good_remap_thm; MAP] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN REPEAT GEN_TAC THEN
  STRIP_TAC THEN ASM_SIMP_TAC[injectivity "t"; MAP_MAP_o; MAP_EQ_f; o_THM] THEN
  REWRITE_TAC[nsLookup_nsMap] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> free_in
    `nsLookup (tenvt:(mlstring,mlstring,mlstring list#t)namespace) n` (concl th))) THEN
  CASES_ON `nsLookup (tenvt:(mlstring,mlstring,mlstring list#t)namespace) n` THEN
  CASE_REWRITE_TAC[OPTION_MAP_DEF] THEN
  MP_TAC(ISPEC `a:mlstring list#t` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `tvs:mlstring list` (X_CHOOSE_THEN `t0:t` SUBST1_TAC)) THEN
  CASE_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[ts_tid_rename_type_subst] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[INFER1AUX_o_f_alist_to_fmap_ZIP; LENGTH_MAP] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[MAP_MAP_o; MAP_EQ_f; o_THM] THEN
  ASM_SIMP_TAC[]);;

let check_type_names_ts_tid_rename = prove
 (CASE_TERM `!f tenvt t.
     check_type_names tenvt t <=>
     check_type_names (nsMap (\p. match p with (ls,t) -> (ls,ts_tid_rename f t)) tenvt) t`,
  GEN_TAC THEN MATCH_MP_TAC check_type_names_ind THEN
  REWRITE_TAC[check_type_names_def; EVERY_MEM; nsLookup_nsMap] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[] THEN
  CASES_ON `nsLookup (tenvT:(mlstring,mlstring,mlstring list#t)namespace) tn` THEN
  CASE_REWRITE_TAC[OPTION_MAP_DEF] THEN
  MP_TAC(ISPEC `a:mlstring list#t` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `tvs:mlstring list` (X_CHOOSE_THEN `t0:t` SUBST1_TAC)) THEN
  CASE_REWRITE_TAC[]);;

let extend_bij_def = cake_def
  `extend_bij (f:num->num) (g:num->num) (ids:num->bool) (n:num) (v:num) =
     if v IN ids then n + g v else f v`;;

let extend_bij_id = prove
 (`!f g s n. extend_bij f f s 0 = f /\ extend_bij f g {} n = f`,
  REWRITE_TAC[extend_bij_def; FUN_EQ_THM; NOT_IN_EMPTY; ADD_CLAUSES] THEN
  MESON_TAC[]);;
let _ = cake_add_simps [extend_bij_id];;

let extend_bij_compose = prove
 (`!f g h ids jds n m.
     extend_bij (extend_bij f g ids n) h jds (n + m) =
     extend_bij f (extend_bij g h jds m) (ids UNION jds) n`,
  REWRITE_TAC[extend_bij_def; FUN_EQ_THM; IN_UNION] THEN REPEAT GEN_TAC THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[ADD_ASSOC] THEN ASM_MESON_TAC[]);;

(* needs monotonicity of set_tids_tenv *)
let set_tids_tenv_extend_dec_tenv = prove
 (`!s t s' t'.
     set_tids_tenv (s' UNION s) t' /\ set_tids_tenv (s' UNION s) t
     ==> set_tids_tenv (s' UNION s) (extend_dec_tenv t' t)`,
  REWRITE_TAC[extend_dec_tenv_def; set_tids_tenv_def; type_env_INFO.ri_accessors] THEN
  MESON_TAC[nsAll_nsAppend]);;

let INFER1AUX_nsAll_mono_tc = prove
 (`!P Q (e:(M,N,V)namespace). nsAll P e ==> (!id x. P id x ==> Q id x) ==> nsAll Q e`,
  MESON_TAC[nsAll_mono]);;

let set_tids_tenv_remap = prove
 (`!tids tenv f.
     set_tids_tenv tids tenv ==> set_tids_tenv (IMAGE f tids) (remap_tenv f tenv)`,
  REWRITE_TAC[set_tids_tenv_def; remap_tenv_def; type_env_INFO.ri_accessors;
              nsAll_nsMap] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP INFER1AUX_nsAll_mono_tc) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[set_tids_subset_def; set_tids_ts_tid_rename; EVERY_MAP; o_THM] THEN
  REWRITE_TAC[EVERY_MEM; set_tids_ts_tid_rename] THEN
  MESON_TAC[IMAGE_SUBSET; FUN_IN_IMAGE]);;

let good_remap_extend_bij = prove
 (`!f g ids n. good_remap f /\ prim_tids F ids ==> good_remap (extend_bij f g ids n)`,
  REWRITE_TAC[good_remap_def; extend_bij_def; prim_tids_def; prim_type_nums_def;
              ALL; MAP; CONS_11] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let remap_tenv_extend_dec_tenv = prove
 (`!f t t'.
     remap_tenv f (extend_dec_tenv t t') =
     extend_dec_tenv (remap_tenv f t) (remap_tenv f t')`,
  REWRITE_TAC[remap_tenv_def; extend_dec_tenv_def; nsMap_nsAppend;
              type_env_INFO.ri_accessors]);;

let BIJ_extend_bij = prove
 (`!tids ids f g n.
     DISJOINT tids ids /\ BIJ f tids (count n) /\ BIJ g ids (count (CARD ids))
     ==> BIJ (extend_bij f g ids n) (tids UNION ids) (count (n + CARD ids))`,
  REWRITE_TAC[BIJ; INJ; SURJ; extend_bij_def; IN_DISJOINT; IN_UNION; IN_COUNT] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `a /\ b /\ c ==> (a /\ b) /\ (a /\ c)`) THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `x:num` THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC[LT_ADD_LCANCEL] THEN DISCH_TAC THEN
    MATCH_MP_TAC(ARITH_RULE `a < n ==> a < n + b`) THEN ASM_MESON_TAC[];
    MAP_EVERY X_GEN_TAC [`x:num`; `y:num`] THEN
    REPEAT COND_CASES_TAC THEN REWRITE_TAC[EQ_ADD_LCANCEL] THENL
     [ASM_MESON_TAC[];
      ASM_MESON_TAC[ARITH_RULE `f < n ==> ~(n + g = f)`];
      ASM_MESON_TAC[ARITH_RULE `f < n ==> ~(f = n + g)`];
      ASM_MESON_TAC[]];
    X_GEN_TAC `z:num` THEN DISCH_TAC THEN ASM_CASES_TAC `z < n` THENL
     [ASM_MESON_TAC[];
      SUBGOAL_THEN `?y. y IN ids /\ (g:num->num) y = z - n` STRIP_ASSUME_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
      EXISTS_TAC `y:num` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]]);;

let set_tids_subset_mono = prove
 (`!tids t tids'.
     set_tids_subset tids t /\ tids SUBSET tids' ==> set_tids_subset tids' t`,
  REWRITE_TAC[set_tids_subset_def] THEN MESON_TAC[SUBSET_TRANS]);;

let set_tids_tenv_mono = prove
 (`!tids tenv tids'.
     set_tids_tenv tids tenv /\ tids SUBSET tids' ==> set_tids_tenv tids' tenv`,
  REWRITE_TAC[set_tids_tenv_def] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP INFER1AUX_nsAll_mono_tc) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[EVERY_MEM] THEN ASM_MESON_TAC[set_tids_subset_mono; SUBSET]);;

let check_freevars_ts_tid_rename = prove
 (`!f ts ls t. check_freevars ts ls (ts_tid_rename f t) <=> check_freevars ts ls t`,
  GEN_TAC THEN MATCH_MP_TAC check_freevars_ind THEN
  REWRITE_TAC[ts_tid_rename_def; check_freevars_def; EVERY_MAP; EVERY_MEM] THEN
  MESON_TAC[]);;

let sing_renum_def = cake_def
  `sing_renum (m:num) (n:num) = \x. if x = m then n else x`;;

let sing_renum_NOT_tscheme_inst = prove
 (`!m n t.
     m IN set_tids t /\ ~(m = n)
     ==> ~(ts_tid_rename (sing_renum m n) t = t) /\
         !tvs tvs'.
           ~tscheme_inst (tvs,ts_tid_rename (sing_renum m n) t) (tvs',t) /\
           ~tscheme_inst (tvs',t) (tvs,ts_tid_rename (sing_renum m n) t)`,
  REPEAT GEN_TAC THEN SPEC_TAC(`t:t`,`t:t`) THEN MATCH_MP_TAC t_ind THEN
  REWRITE_TAC[set_tids_def; NOT_IN_EMPTY] THEN
  X_GEN_TAC `l:t list` THEN DISCH_TAC THEN X_GEN_TAC `tn:num` THEN
  REWRITE_TAC[IN_INSERT; IN_UNIONS; IN_SET_OF_LIST; MEM_MAP] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  REWRITE_TAC[ts_tid_rename_def; tscheme_inst_def; deBruijn_subst_def; injectivity "t";
              check_freevars_def] THEN
  ASM_CASES_TAC `tn:num = m` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[sing_renum_def] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?y. MEM y l /\ m IN set_tids y` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `sing_renum m n tn = tn` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[sing_renum_def]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:t` o REWRITE_RULE[EVERY_MEM]) THEN
  ASM_REWRITE_TAC[tscheme_inst_def] THEN STRIP_TAC THEN
  REWRITE_TAC[MAP_EQ_ID; MAP_MAP_o; MAP_EQ_f; o_THM; EVERY_MEM; MEM_MAP] THEN
  REPEAT STRIP_TAC THEN ASM_MESON_TAC[EVERY_MEM]);;

let sing_renum_NOTIN_ID = prove
 (`!m n t. ~(m IN set_tids t) ==> ts_tid_rename (sing_renum m n) t = t`,
  REPEAT GEN_TAC THEN SPEC_TAC(`t:t`,`t:t`) THEN MATCH_MP_TAC t_ind THEN
  REWRITE_TAC[set_tids_def; ts_tid_rename_def; IN_INSERT; IN_UNIONS; IN_SET_OF_LIST;
              MEM_MAP; injectivity "t"; MAP_EQ_ID; EVERY_MEM; sing_renum_def] THEN
  MESON_TAC[]);;

let sing_renum_IN_NOT_ID = prove
 (`!m n t. m IN set_tids t /\ ~(m = n) ==> ~(ts_tid_rename (sing_renum m n) t = t)`,
  MESON_TAC[sing_renum_NOT_tscheme_inst]);;

let INFER1AUX_nsAll2_nsMap_id = prove
 (`!P (g:V->V) (e:(M,N,V)namespace).
     nsAll P e /\ (!id v. P id v ==> g v = v)
     ==> nsAll2 (\i v1 v2. v1 = v2) (nsMap g e) e`,
  REWRITE_TAC[nsAll2_def; nsSub_def; nsLookup_nsMap; nsLookupMod_nsMap;
              OPTION_MAP_EQ_NONE; OPTION_MAP_EQ_SOME; nsAll_def] THEN
  MESON_TAC[]);;

(* HOL4 comment: TODO: this is only true up to equivalence on tenvs *)
let sing_renum_NOTIN_tenv_ID = prove
 (`!tids tenv m n.
     set_tids_tenv tids tenv /\ ~(m IN tids)
     ==> tenv_equiv (remap_tenv (sing_renum m n) tenv) tenv`,
  REWRITE_TAC[set_tids_tenv_def; remap_tenv_def; tenv_equiv_def;
              type_env_INFO.ri_accessors] THEN
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] INFER1AUX_nsAll2_nsMap_id)) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN CASE_REWRITE_TAC[PAIR_EQ] THEN
  REWRITE_TAC[set_tids_subset_def; SUBSET; EVERY_MEM; MAP_EQ_ID] THEN
  ASM_MESON_TAC[sing_renum_NOTIN_ID; sing_renum_def]);;

let INFER1AUX_tydefs =
  [typeSystem_Tarray_def; typeSystem_Tbool_def; typeSystem_Tchar_def; typeSystem_Texn_def;
   typeSystem_Tfn_def; typeSystem_Tint_def; typeSystem_Tlist_def; typeSystem_Tref_def;
   typeSystem_Tstring_def; typeSystem_Ttup_def; typeSystem_Tvector_def;
   typeSystem_Tword64_def; typeSystem_Tword8_def; typeSystem_Tword8array_def;
   typeSystem_Tdouble_def];;

let type_p_ts_tid_rename = prove
 (`!f. good_remap f
     ==> (!tvs tenv p t bindings.
            type_p tvs tenv p t bindings
            ==> type_p tvs (remap_tenv f tenv) p (ts_tid_rename f t)
                  (MAP (\(n:mlstring,t). (n,ts_tid_rename f t)) bindings)) /\
         (!tvs tenv ps ts bindings.
            type_ps tvs tenv ps ts bindings
            ==> type_ps tvs (remap_tenv f tenv) ps (MAP (ts_tid_rename f) ts)
                  (MAP (\(n:mlstring,t). (n,ts_tid_rename f t)) bindings))`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[INFER1AUX_good_remap_thm]) THEN
  MATCH_MP_TAC type_p_ind THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC (INFER1AUX_tydefs @ [ts_tid_rename_def; MAP; MAP_APPEND]) THEN
  ASM_REWRITE_TAC[] THENL
   [ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC;
    INFER1AUX_RULE_TAC (REWRITE_RULE INFER1AUX_tydefs type_p_rules) THEN
    MAP_EVERY EXISTS_TAC [`MAP (ts_tid_rename f) ts`; `tvs':mlstring list`] THEN
    ASM_REWRITE_TAC[LENGTH_MAP; EVERY_MAP; check_freevars_ts_tid_rename; ETA_AX;
                    remap_tenv_def; type_env_INFO.ri_accessors; nsLookup_nsMap;
                    OPTION_MAP_DEF] THEN
    CASE_REWRITE_TAC[] THEN
    SUBGOAL_THEN `MAP (type_subst (alist_to_fmap (ZIP tvs' (MAP (ts_tid_rename f) ts'))))
                      (MAP (ts_tid_rename f) ts) =
                  MAP (ts_tid_rename f) (MAP (type_subst (alist_to_fmap (ZIP tvs' ts'))) ts)`
      SUBST1_TAC THENL
     [REWRITE_TAC[MAP_MAP_o; MAP_EQ_f; o_THM; ts_tid_rename_type_subst] THEN
      ASM_SIMP_TAC[INFER1AUX_o_f_alist_to_fmap_ZIP];
      RULE_ASSUM_TAC(REWRITE_RULE[remap_tenv_def]) THEN ASM_REWRITE_TAC[]];
    ALL_TAC; ALL_TAC; ALL_TAC;
    SUBGOAL_THEN `ts_tid_rename f (type_name_subst (type_env_t tenv) t) =
                  type_name_subst (type_env_t (remap_tenv f tenv)) t` SUBST1_TAC THENL
     [REWRITE_TAC[remap_tenv_def; type_env_INFO.ri_accessors] THEN
      MATCH_MP_TAC ts_tid_rename_type_name_subst THEN ASM_REWRITE_TAC[];
      ALL_TAC];
    ALL_TAC; ALL_TAC] THEN
  INFER1AUX_RULE_TAC (REWRITE_RULE INFER1AUX_tydefs type_p_rules) THEN
  ASM_REWRITE_TAC[check_freevars_ts_tid_rename] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[remap_tenv_def; type_env_INFO.ri_accessors]) THEN
  ASM_REWRITE_TAC[remap_tenv_def; type_env_INFO.ri_accessors] THEN
  ASM_MESON_TAC[check_type_names_ts_tid_rename; ts_tid_rename_type_name_subst]);;

let INFER1AUX_t_of_rename = prove
 (`!f ty. good_remap f ==> ts_tid_rename f (t_of ty) = t_of ty`,
  REWRITE_TAC[INFER1AUX_good_remap_thm] THEN REPEAT STRIP_TAC THEN
  STRUCT_CASES_TAC(ISPEC `ty:prim_type` (cases "prim_type")) THEN
  TRY(STRUCT_CASES_TAC(ISPEC `a:word_size` (cases "word_size"))) THEN
  ASM_REWRITE_TAC(t_of_def :: ts_tid_rename_def :: MAP :: INFER1AUX_tydefs));;

let type_op_ts_tid_rename = prove
 (`!f. good_remap f
     ==> !op ts t. type_op op ts t
                   ==> type_op op (MAP (ts_tid_rename f) ts) (ts_tid_rename f t)`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[INFER1AUX_good_remap_thm]) THEN
  ASSUME_TAC(MATCH_MP INFER1AUX_t_of_rename (ASSUME `good_remap f`)) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[type_op_cases] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN
    (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC))) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl))) THEN
  REWRITE_TAC[type_op_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC(MAP :: ts_tid_rename_def :: INFER1AUX_tydefs) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[EVERY_MEM; LENGTH_MAP; MEM_MAP] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[EVERY_MEM]) THEN ASM_MESON_TAC[]);;

let remap_tenvE_def = cake_def
  `(remap_tenvE (f:num->num) Empty = Empty) /\
   (remap_tenvE f (Bind_tvar n e) = Bind_tvar n (remap_tenvE f e)) /\
   (remap_tenvE f (Bind_name s n t e) =
      Bind_name s n (ts_tid_rename f t) (remap_tenvE f e))`;;

let num_tvs_remap_tenvE = prove
 (`!f tenvE. num_tvs (remap_tenvE f tenvE) = num_tvs tenvE`,
  GEN_TAC THEN MATCH_MP_TAC tenv_val_exp_INDUCT THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[remap_tenvE_def; num_tvs_def]);;

let remap_tenvE_bind_var_list = prove
 (`!f n env tenvE.
     remap_tenvE f (bind_var_list n env tenvE) =
     bind_var_list n (MAP (\(x:mlstring,t). (x,ts_tid_rename f t)) env) (remap_tenvE f tenvE)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[bind_var_list_def; MAP] THEN
  SPEC_TAC(`h:mlstring#t`,`h:mlstring#t`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  ASM_REWRITE_TAC[bind_var_list_def; remap_tenvE_def]);;

let remap_tenvE_bind_tvar = prove
 (`!f tvs e. remap_tenvE f (bind_tvar tvs e) = bind_tvar tvs (remap_tenvE f e)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bind_tvar_def] THEN COND_CASES_TAC THEN
  REWRITE_TAC[remap_tenvE_def]);;

let deBruijn_inc_ts_tid_rename = prove
 (`!f skip n t.
     ts_tid_rename f (deBruijn_inc skip n t) = deBruijn_inc skip n (ts_tid_rename f t)`,
  GEN_TAC THEN MATCH_MP_TAC deBruijn_inc_ind THEN
  REWRITE_TAC[deBruijn_inc_def; ts_tid_rename_def] THEN REPEAT STRIP_TAC THENL
   [COND_CASES_TAC THEN REWRITE_TAC[ts_tid_rename_def];
    REWRITE_TAC[injectivity "t"; MAP_MAP_o; MAP_EQ_f; o_THM] THEN ASM_SIMP_TAC[]]);;

let INFER1AUX_tveLookup_remap_tenvE = prove
 (`!f x tenvE k.
     tveLookup x k (remap_tenvE f tenvE) =
     OPTION_MAP (\(id,t). (id,ts_tid_rename f t)) (tveLookup x k tenvE)`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC tenv_val_exp_INDUCT THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[remap_tenvE_def; tveLookup_def; OPTION_MAP_DEF] THEN
  TRY COND_CASES_TAC THEN
  ASM_REWRITE_TAC[OPTION_MAP_DEF; deBruijn_inc_ts_tid_rename]);;

let lookup_varE_remap_tenvE = prove
 (`!f n tenvE.
     lookup_varE n (remap_tenvE f tenvE) =
     OPTION_MAP (\(id,t). (id,ts_tid_rename f t)) (lookup_varE n tenvE)`,
  GEN_TAC THEN MATCH_MP_TAC id_INDUCT THEN
  REWRITE_TAC[lookup_varE_def] THEN CASE_REWRITE_TAC[OPTION_MAP_DEF] THEN
  REWRITE_TAC[INFER1AUX_tveLookup_remap_tenvE]);;

let ts_tid_rename_deBruijn_subst = prove
 (`!f n targs t.
     ts_tid_rename f (deBruijn_subst n targs t) =
     deBruijn_subst n (MAP (ts_tid_rename f) targs) (ts_tid_rename f t)`,
  GEN_TAC THEN MATCH_MP_TAC deBruijn_subst_ind THEN
  REWRITE_TAC[deBruijn_subst_def; ts_tid_rename_def; LENGTH_MAP] THEN
  REPEAT STRIP_TAC THENL
   [REWRITE_TAC[prove(`!b x y. ts_tid_rename f (if b then x else y) =
                               if b then ts_tid_rename f x else ts_tid_rename f y`,
                       REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[])] THEN
    REWRITE_TAC[ts_tid_rename_def] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC EL_MAP THEN ASM_ARITH_TAC;
    REWRITE_TAC[injectivity "t"; MAP_MAP_o; MAP_EQ_f; o_THM] THEN ASM_SIMP_TAC[]]);;

let INFER1AUX_lookup_var_remap = prove
 (`!f n tenvE tenv.
     lookup_var n (remap_tenvE f tenvE) (remap_tenv f tenv) =
     OPTION_MAP (\(id,t). (id,ts_tid_rename f t)) (lookup_var n tenvE tenv)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[lookup_var_def; lookup_varE_remap_tenvE; remap_tenv_def;
              type_env_INFO.ri_accessors; nsLookup_nsMap] THEN
  CASES_ON `lookup_varE n tenvE` THEN CASE_REWRITE_TAC[OPTION_MAP_DEF] THEN
  CASES_ON `nsLookup (type_env_v tenv) n` THEN CASE_REWRITE_TAC[OPTION_MAP_DEF] THEN
  MP_TAC(ISPEC `a:num#t` PAIR_SURJECTIVE) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]);;

let INFER1AUX_remap_opt_bind_name = prove
 (`!f n tvs t tenvE.
     remap_tenvE f (opt_bind_name n tvs t tenvE) =
     opt_bind_name n tvs (ts_tid_rename f t) (remap_tenvE f tenvE)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[opt_bind_name_def] THEN
  CASES_ON `n:mlstring option` THEN CASE_REWRITE_TAC[remap_tenvE_def]);;

let INFER1AUX_tns_remap = prove
 (`!f tenv t.
     good_remap f /\ check_type_names (type_env_t tenv) t
     ==> ts_tid_rename f (type_name_subst (type_env_t tenv) t) =
         type_name_subst (type_env_t (remap_tenv f tenv)) t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[remap_tenv_def; type_env_INFO.ri_accessors] THEN
  MATCH_MP_TAC ts_tid_rename_type_name_subst THEN ASM_REWRITE_TAC[]);;

(* the facts of good_remap f, under the assumption good_remap f (for rewriting in goals *)
(* that have good_remap f among their assumptions)                                   *)
let INFER1AUX_GR = REWRITE_RULE[INFER1AUX_good_remap_thm] (ASSUME `good_remap (f:num->num)`);;

let INFER1AUX_ALOOKUP_MAP_GABS = prove
 (`!(g:B->C) (l:(A#B)list) k.
     ALOOKUP (MAP (\(x,t). (x,g t)) l) k = OPTION_MAP g (ALOOKUP l k)`,
  REWRITE_TAC[ALOOKUP_MAP; o_THM]);;

let type_e_ts_tid_rename = prove
 (`!f. good_remap f
     ==> (!tenv tenvE e t.
            type_e tenv tenvE e t
            ==> type_e (remap_tenv f tenv) (remap_tenvE f tenvE) e (ts_tid_rename f t)) /\
         (!tenv tenvE es ts.
            type_es tenv tenvE es ts
            ==> type_es (remap_tenv f tenv) (remap_tenvE f tenvE) es
                  (MAP (ts_tid_rename f) ts)) /\
         (!tenv tenvE funs env.
            type_funs tenv tenvE funs env
            ==> type_funs (remap_tenv f tenv) (remap_tenvE f tenvE) funs
                  (MAP (\(n:mlstring,t). (n,ts_tid_rename f t)) env))`,
  GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC type_e_ind THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC (INFER1AUX_tydefs @ [ts_tid_rename_def; MAP; MAP_APPEND;
     remap_tenvE_def; remap_tenvE_bind_var_list; INFER1AUX_remap_opt_bind_name;
     ts_tid_rename_deBruijn_subst; INFER1AUX_GR]) THEN
  ASM_SIMP_TAC[INFER1AUX_tns_remap] THEN
  INFER1AUX_RULE_TAC (REWRITE_RULE INFER1AUX_tydefs type_e_rules) THEN
  RULE_ASSUM_TAC(REWRITE_RULE (INFER1AUX_tydefs @ [ts_tid_rename_def; MAP; MAP_APPEND;
     remap_tenvE_def; remap_tenvE_bind_var_list; INFER1AUX_remap_opt_bind_name;
     INFER1AUX_GR])) THEN
  ASM_REWRITE_TAC[check_freevars_ts_tid_rename; num_tvs_remap_tenvE; LENGTH_MAP;
                  EVERY_MAP; ETA_AX; INFER1AUX_ALOOKUP_MAP_GABS; OPTION_MAP_DEF] THEN
  FIRST
   [(* App *)
    EXISTS_TAC `MAP (ts_tid_rename f) ts` THEN
    ASM_SIMP_TAC[MATCH_MP type_op_ts_tid_rename (ASSUME `good_remap (f:num->num)`)] THEN
    NO_TAC;
    (* Var *)
    EXISTS_TAC `tvs:num` THEN
    ASM_REWRITE_TAC[INFER1AUX_lookup_var_remap; OPTION_MAP_DEF] THEN
    CASE_REWRITE_TAC[] THEN NO_TAC;
    (* Con *)
    MAP_EVERY EXISTS_TAC [`tvs:mlstring list`; `MAP (ts_tid_rename f) ts`] THEN
    ASM_REWRITE_TAC[remap_tenv_def; type_env_INFO.ri_accessors; nsLookup_nsMap;
                    OPTION_MAP_DEF] THEN
    CASE_REWRITE_TAC[] THEN
    SUBGOAL_THEN `MAP (type_subst (alist_to_fmap (ZIP tvs (MAP (ts_tid_rename f) ts'))))
                      (MAP (ts_tid_rename f) ts) =
                  MAP (ts_tid_rename f) (MAP (type_subst (alist_to_fmap (ZIP tvs ts'))) ts)`
      SUBST1_TAC THENL
     [REWRITE_TAC[MAP_MAP_o; MAP_EQ_f; o_THM; ts_tid_rename_type_subst] THEN
      ASM_SIMP_TAC[INFER1AUX_o_f_alist_to_fmap_ZIP];
      RULE_ASSUM_TAC(REWRITE_RULE[remap_tenv_def]) THEN ASM_REWRITE_TAC[]] THEN NO_TAC;
    (* Letrec *)
    EXISTS_TAC `MAP (\(n:mlstring,t). (n,ts_tid_rename f t)) bindings` THEN
    ASM_REWRITE_TAC[] THEN NO_TAC;
    (* Tannot *)
    MP_TAC(SPECL [`f:num->num`; `tenv:type_env`; `t:ast_t`] INFER1AUX_tns_remap) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[remap_tenv_def; type_env_INFO.ri_accessors] THEN
    ASM_MESON_TAC[check_type_names_ts_tid_rename];
    (* funs *)
    RULE_ASSUM_TAC(REWRITE_RULE[check_freevars_def; ALL]) THEN
    ASM_REWRITE_TAC[check_freevars_def; ALL; check_freevars_ts_tid_rename] THEN NO_TAC;
    (* Handle, Mat *)
    TRY(EXISTS_TAC `ts_tid_rename f t1`) THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`p':pat`; `e':exp`] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`p':pat`; `e':exp`]) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN
    EXISTS_TAC `MAP (\(n:mlstring,t). (n,ts_tid_rename f t)) bindings` THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP (CONJUNCT1 (MATCH_MP type_p_ts_tid_rename
      (ASSUME `good_remap (f:num->num)`)))) THEN
    REWRITE_TAC (INFER1AUX_tydefs @ [ts_tid_rename_def; MAP; INFER1AUX_GR])]);;

let good_remap_LINV = prove
 (`!f s t. good_remap f /\ prim_tids T s /\ INJ f s t ==> good_remap (LINV f s o f)`,
  REWRITE_TAC[good_remap_def; prim_tids_def; MAP_EQ_ID; EVERY_MEM; o_THM] THEN
  MESON_TAC[LINV_DEF]);;

let ts_tid_rename_LINV = prove
 (`!s t f x.
     INJ f s t /\ set_tids_subset s x ==> ts_tid_rename (LINV f s) (ts_tid_rename f x) = x`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC ts_tid_rename_ind THEN
  REWRITE_TAC[ts_tid_rename_def; MAP_MAP_o; set_tids_subset_def; SUBSET; MAP_EQ_ID;
              set_tids_def; IN_INSERT; IN_UNIONS; IN_SET_OF_LIST; MEM_MAP; o_THM;
              injectivity "t"] THEN
  REPEAT STRIP_TAC THENL [ASM_MESON_TAC[]; ASM_MESON_TAC[LINV_DEF]]);;

let LINVI_def = cake_def
  `LINVI (f:A->A) (s:A->bool) (y:A) =
     match LINV_OPT f s y with SOME x -> x | NONE -> f y`;;

let INFER1AUX_nsAll2_nsMap_lookup_id = prove
 (`!(g:V->V) (e:(M,N,V)namespace).
     (!id v. nsLookup e id = SOME v ==> g v = v)
     ==> nsAll2 (\i v1 v2. v1 = v2) (nsMap g e) e`,
  REWRITE_TAC[nsAll2_def; nsSub_def; nsLookup_nsMap; nsLookupMod_nsMap;
              OPTION_MAP_EQ_NONE; OPTION_MAP_EQ_SOME] THEN
  MESON_TAC[]);;

let INFER1AUX_tenv_equiv_nsMap = prove
 (`!tenv gv gc gt.
     (!id v. nsLookup (type_env_v tenv) id = SOME v ==> gv v = v) /\
     (!id v. nsLookup (type_env_c tenv) id = SOME v ==> gc v = v) /\
     (!id v. nsLookup (type_env_t tenv) id = SOME v ==> gt v = v)
     ==> tenv_equiv (type_env_REC (nsMap gv (type_env_v tenv)) (nsMap gc (type_env_c tenv))
                                  (nsMap gt (type_env_t tenv))) tenv`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[tenv_equiv_def; type_env_INFO.ri_accessors] THEN
  REPEAT CONJ_TAC THEN MATCH_MP_TAC INFER1AUX_nsAll2_nsMap_lookup_id THEN
  ASM_REWRITE_TAC[]);;

let INFER1AUX_set_tids_tenv_lookup = prove
 (`!tids tenv.
     set_tids_tenv tids tenv
     ==> (!id ls t. nsLookup (type_env_t tenv) id = SOME (ls,t) ==> set_tids_subset tids t) /\
         (!id ls ts tid. nsLookup (type_env_c tenv) id = SOME (ls,ts,tid)
                         ==> ALL (set_tids_subset tids) ts /\ tid IN tids) /\
         (!id n t. nsLookup (type_env_v tenv) id = SOME (n,t) ==> set_tids_subset tids t)`,
  REWRITE_TAC[set_tids_tenv_def; nsAll_def] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`id:(mlstring,mlstring)id`; `(ls:mlstring list,t:t)`]);
    FIRST_X_ASSUM(MP_TAC o SPECL [`id:(mlstring,mlstring)id`;
                                  `(ls:mlstring list,ts:t list,tid:num)`]);
    FIRST_X_ASSUM(MP_TAC o SPECL [`id:(mlstring,mlstring)id`; `(n:num,t:t)`])] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[ETA_AX]);;

let remap_tenv_LINV = prove
 (`!f s t tenv.
     BIJ f s t /\ set_tids_tenv s tenv
     ==> tenv_equiv (remap_tenv (LINV f s) (remap_tenv f tenv)) tenv`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP INFER1AUX_set_tids_tenv_lookup) THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o REWRITE_RULE[BIJ]) THEN
  REWRITE_TAC[remap_tenv_def; type_env_INFO.ri_accessors; nsMap_compose] THEN
  MATCH_MP_TAC INFER1AUX_tenv_equiv_nsMap THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  CASE_REWRITE_TAC[o_THM; PAIR_EQ; MAP_MAP_o] THEN REPEAT STRIP_TAC THEN
  RES_TAC THEN REWRITE_TAC[MAP_EQ_ID; o_THM] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[EVERY_MEM]) THEN
  ASM_MESON_TAC[ts_tid_rename_LINV; LINV_DEF]);;

let good_remap_BIJ = prove
 (`!f s t. good_remap f /\ prim_tids T s /\ BIJ f s t ==> good_remap (LINV f s)`,
  REWRITE_TAC[good_remap_def; prim_tids_def; MAP_EQ_ID; EVERY_MEM; BIJ] THEN
  MESON_TAC[LINV_DEF]);;

let good_remap_LINVI = prove
 (`!f s t. good_remap f /\ prim_tids T s /\ INJ f s t ==> good_remap (LINVI f s)`,
  REWRITE_TAC[good_remap_def; prim_tids_def; MAP_EQ_ID; EVERY_MEM; LINVI_def] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `LINV_OPT f s (x:num) = SOME x` (fun th -> REWRITE_TAC[th] THEN
    CASE_REWRITE_TAC[]) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP INJ_LINV_OPT th]) THEN
  ASM_MESON_TAC[INJ]);;

let INJ_LINVI = prove
 (`!(f:A->A) s t x. INJ f s t /\ x IN s ==> LINVI f s (f x) = x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LINVI_def] THEN
  SUBGOAL_THEN `LINV_OPT f s ((f:A->A) x) = SOME x` (fun th -> REWRITE_TAC[th] THEN
    CASE_REWRITE_TAC[]) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP INJ_LINV_OPT th]) THEN
  ASM_MESON_TAC[INJ]);;

let LINVI_RINV = prove
 (`!(f:A->A) s t y. INJ f s t /\ (?x. x IN s /\ f x = y) ==> f (LINVI f s y) = y`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  ASM_MESON_TAC[INJ_LINVI]);;

let ts_tid_rename_LINVI = prove
 (`!s t f x.
     INJ f s t /\ set_tids_subset s x ==> ts_tid_rename (LINVI f s) (ts_tid_rename f x) = x`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC ts_tid_rename_ind THEN
  REWRITE_TAC[ts_tid_rename_def; MAP_MAP_o; set_tids_subset_def; SUBSET; MAP_EQ_ID;
              set_tids_def; IN_INSERT; IN_UNIONS; IN_SET_OF_LIST; MEM_MAP; o_THM;
              injectivity "t"] THEN
  REPEAT STRIP_TAC THENL [ASM_MESON_TAC[]; ASM_MESON_TAC[INJ_LINVI]]);;

let remap_tenv_LINVI = prove
 (`!f s t tenv.
     INJ f s t /\ set_tids_tenv s tenv
     ==> tenv_equiv (remap_tenv (LINVI f s) (remap_tenv f tenv)) tenv`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP INFER1AUX_set_tids_tenv_lookup) THEN
  REWRITE_TAC[remap_tenv_def; type_env_INFO.ri_accessors; nsMap_compose] THEN
  MATCH_MP_TAC INFER1AUX_tenv_equiv_nsMap THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  CASE_REWRITE_TAC[o_THM; PAIR_EQ; MAP_MAP_o] THEN REPEAT STRIP_TAC THEN
  RES_TAC THEN REWRITE_TAC[MAP_EQ_ID; o_THM] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[EVERY_MEM]) THEN
  ASM_MESON_TAC[ts_tid_rename_LINVI; INJ_LINVI]);;

let ts_tid_rename_compose = prove
 (`!g t f. ts_tid_rename f (ts_tid_rename g t) = ts_tid_rename (f o g) t`,
  MATCH_MP_TAC ts_tid_rename_ind THEN
  REWRITE_TAC[ts_tid_rename_def; MAP_MAP_o; o_THM; injectivity "t"; MAP_EQ_f] THEN
  MESON_TAC[]);;

let remap_tenv_compose = prove
 (`!f g tenv. remap_tenv f (remap_tenv g tenv) = remap_tenv (f o g) tenv`,
  REWRITE_TAC[remap_tenv_def; type_env_INFO.ri_accessors; nsMap_compose] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[injectivity "type_env"] THEN
  REPEAT CONJ_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; o_THM] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[ts_tid_rename_compose; MAP_MAP_o; MAP_EQ_f; o_THM]);;

let ts_tid_rename_eq_id = prove
 (`!f t. ts_tid_rename f t = t <=> !x. x IN set_tids t ==> f x = x`,
  MATCH_MP_TAC ts_tid_rename_ind THEN
  REWRITE_TAC[ts_tid_rename_def; set_tids_def; MAP_EQ_ID; injectivity "t"; NOT_IN_EMPTY;
              IN_INSERT; IN_UNIONS; IN_SET_OF_LIST; MEM_MAP] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN MESON_TAC[]);;

let ts_tid_rename_eq_f = prove
 (`!f t g. ts_tid_rename f t = ts_tid_rename g t <=> !x. x IN set_tids t ==> f x = g x`,
  MATCH_MP_TAC ts_tid_rename_ind THEN
  REWRITE_TAC[ts_tid_rename_def; set_tids_def; MAP_EQ_f; injectivity "t"; NOT_IN_EMPTY;
              IN_INSERT; IN_UNIONS; IN_SET_OF_LIST; MEM_MAP] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN MESON_TAC[]);;

let inj_ts_tid_rename_eq = prove
 (`!f t1 t2.
     (!x y. x IN set_tids t1 /\ y IN set_tids t2 /\ f x = f y ==> x = y) /\
     ts_tid_rename f t1 = ts_tid_rename f t2
     ==> t1 = t2`,
  GEN_TAC THEN MATCH_MP_TAC t_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
   [ALL_TAC; ALL_TAC; DISCH_TAC THEN GEN_TAC THEN GEN_TAC] THEN
  STRUCT_CASES_TAC(ISPEC `t2:t` (CONJUNCT1 (cases "t"))) THEN
  REWRITE_TAC[ts_tid_rename_def; distinctness "t"; injectivity "t"; set_tids_def;
              NOT_IN_EMPTY; IN_INSERT; IN_UNIONS; IN_SET_OF_LIST; MEM_MAP] THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC(ISPEC `ts_tid_rename f` INJ_MAP_EQ_2) THEN
    ASM_REWRITE_TAC[IN_SET_OF_LIST] THEN REPEAT STRIP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[EVERY_MEM]) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:t` o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[];
    ASM_MESON_TAC[]]);;

let INFER1AUX_good_remap_sing_renum = prove
 (`!m n tids. ~(m IN tids) /\ prim_tids T tids ==> good_remap (sing_renum m n)`,
  REWRITE_TAC[good_remap_def; prim_tids_def; sing_renum_def; MAP_EQ_ID; EVERY_MEM] THEN
  MESON_TAC[]);;

let type_p_ts_tid_rename_sing_renum = prove
 (`!m tids tvs tenv p t bindings n.
     ~(m IN tids) /\ prim_tids T tids /\
     type_p tvs tenv p t bindings /\
     set_tids_tenv tids tenv
     ==> type_p tvs tenv p (ts_tid_rename (sing_renum m n) t)
           (MAP (\(nn:mlstring,t). (nn,ts_tid_rename (sing_renum m n) t)) bindings)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `good_remap (sing_renum m n)` ASSUME_TAC THENL
   [ASM_MESON_TAC[INFER1AUX_good_remap_sing_renum]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (CONJUNCT1 (MATCH_MP type_p_ts_tid_rename
    (ASSUME `good_remap (sing_renum m n)`)))) THEN
  DISCH_TAC THEN FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (CONJUNCT1 type_p_tenv_equiv)) THEN
  ASM_MESON_TAC[sing_renum_NOTIN_tenv_ID]);;

let type_e_ts_tid_rename_sing_renum = prove
 (`!m tids tenv tenvE e t n.
     ~(m IN tids) /\ prim_tids T tids /\
     type_e tenv tenvE e t /\
     set_tids_tenv tids tenv
     ==> type_e tenv (remap_tenvE (sing_renum m n) tenvE) e
           (ts_tid_rename (sing_renum m n) t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `good_remap (sing_renum m n)` ASSUME_TAC THENL
   [ASM_MESON_TAC[INFER1AUX_good_remap_sing_renum]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (CONJUNCT1 (MATCH_MP type_e_ts_tid_rename
    (ASSUME `good_remap (sing_renum m n)`)))) THEN
  DISCH_TAC THEN FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (CONJUNCT1 type_e_tenv_equiv)) THEN
  ASM_MESON_TAC[sing_renum_NOTIN_tenv_ID]);;

let type_funs_ts_tid_rename_sing_renum = prove
 (`!m tids tenv tenvE funs res n.
     ~(m IN tids) /\ prim_tids T tids /\
     type_funs tenv tenvE funs res /\
     set_tids_tenv tids tenv
     ==> type_funs tenv (remap_tenvE (sing_renum m n) tenvE) funs
           (MAP (\(z:mlstring,t). (z,ts_tid_rename (sing_renum m n) t)) res)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `good_remap (sing_renum m n)` ASSUME_TAC THENL
   [ASM_MESON_TAC[INFER1AUX_good_remap_sing_renum]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (CONJUNCT2 (CONJUNCT2 (MATCH_MP type_e_ts_tid_rename
    (ASSUME `good_remap (sing_renum m n)`))))) THEN
  DISCH_TAC THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (CONJUNCT2 (CONJUNCT2 type_e_tenv_equiv))) THEN
  ASM_MESON_TAC[sing_renum_NOTIN_tenv_ID]);;

let INFER1AUX_ALL2_same_MEM = prove
 (`!(R:A->A->bool) l x. ALL2 R l l /\ MEM x l ==> R x x`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[ALL2; MEM; NOT_CONS_NIL; HD; TL] THEN
  REPEAT STRIP_TAC THEN ASM_MESON_TAC[]);;

let type_pe_bindings_tids = prove
 (`!tids tenv tvs p t bindings e.
     prim_tids T tids /\ set_tids_tenv tids tenv /\
     type_p tvs tenv p t bindings /\ type_e tenv (bind_tvar tvs Empty) e t /\
     (!tvs' bindings' t'.
        type_p tvs' tenv p t' bindings' /\ type_e tenv (bind_tvar tvs' Empty) e t'
        ==> ALL2 tscheme_inst (MAP SND (MAP (\(n:mlstring,t). (n,tvs',t)) bindings'))
                              (MAP SND (MAP (\(n:mlstring,t). (n,tvs,t)) bindings)))
     ==> !p_1 p_2. MEM (p_1,p_2) bindings ==> set_tids_subset tids p_2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[set_tids_subset_def; SUBSET] THEN X_GEN_TAC `x:num` THEN DISCH_TAC THEN
  CCONTR_TAC THEN
  MP_TAC(SPECL [`x:num`; `tids:num->bool`; `tvs:num`; `tenv:type_env`; `p:pat`; `t:t`;
                `bindings:(mlstring#t)list`; `x + 1`] type_p_ts_tid_rename_sing_renum) THEN
  MP_TAC(SPECL [`x:num`; `tids:num->bool`; `tenv:type_env`; `bind_tvar tvs Empty`;
                `e:exp`; `t:t`; `x + 1`] type_e_ts_tid_rename_sing_renum) THEN
  ASM_REWRITE_TAC[remap_tenvE_bind_tvar; remap_tenvE_def] THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`tvs:num`;
    `MAP (\(nn:mlstring,t). (nn,ts_tid_rename (sing_renum x (x + 1)) t)) bindings`;
    `ts_tid_rename (sing_renum x (x + 1)) t`]) THEN
  ASM_REWRITE_TAC[MAP_MAP_o; EVERY2_MAP] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP INFER1AUX_ALL2_same_MEM o
    C CONJ (ASSUME `MEM (p_1:mlstring,p_2:t) bindings`)) THEN
  REWRITE_TAC[o_THM] THEN
  MP_TAC(SPECL [`x:num`; `x + 1`; `p_2:t`] sing_renum_NOT_tscheme_inst) THEN
  ASM_REWRITE_TAC[ARITH_RULE `~(x = x + 1)`] THEN MESON_TAC[]);;

let type_funs_bindings_tids = prove
 (`!tenv bindings tvs funs tids.
     type_funs tenv (bind_var_list 0 bindings (bind_tvar tvs Empty)) funs bindings /\
     set_tids_tenv tids tenv /\ prim_tids T tids /\
     (!tvs' bindings'.
        type_funs tenv (bind_var_list 0 bindings' (bind_tvar tvs' Empty)) funs bindings'
        ==> ALL2 tscheme_inst (MAP (\x. (tvs',SND x)) bindings')
                              (MAP (\x. (tvs,SND x)) bindings))
     ==> ALL (set_tids_subset tids o SND) bindings`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[EVERY_MEM; FORALL_PAIR_THM; o_THM; set_tids_subset_def; SUBSET] THEN
  MAP_EVERY X_GEN_TAC [`p_1:mlstring`; `p_2:t`] THEN DISCH_TAC THEN
  X_GEN_TAC `x:num` THEN DISCH_TAC THEN CCONTR_TAC THEN
  MP_TAC(SPECL [`x:num`; `tids:num->bool`; `tenv:type_env`;
                `bind_var_list 0 bindings (bind_tvar tvs Empty)`;
                `funs:(mlstring#mlstring#exp)list`; `bindings:(mlstring#t)list`; `x + 1`]
               type_funs_ts_tid_rename_sing_renum) THEN
  ASM_REWRITE_TAC[remap_tenvE_bind_var_list; remap_tenvE_bind_tvar; remap_tenvE_def] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP (ASSUME
   `!tvs' bindings'.
        type_funs tenv (bind_var_list 0 bindings' (bind_tvar tvs' Empty)) funs bindings'
        ==> ALL2 tscheme_inst (MAP (\x. (tvs',SND x)) bindings')
                              (MAP (\x. (tvs,SND (x:mlstring#t))) bindings)`)) THEN
  REWRITE_TAC[MAP_MAP_o; EVERY2_MAP] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP INFER1AUX_ALL2_same_MEM o
    C CONJ (ASSUME `MEM (p_1:mlstring,p_2:t) bindings`)) THEN
  REWRITE_TAC[o_THM] THEN
  MP_TAC(SPECL [`x:num`; `x + 1`; `p_2:t`] sing_renum_NOT_tscheme_inst) THEN
  ASM_REWRITE_TAC[ARITH_RULE `~(x = x + 1)`] THEN MESON_TAC[]);;

let type_pe_bindings_tids_0 = prove
 (`!tids tenv p t bindings e.
     prim_tids T tids /\ set_tids_tenv tids tenv /\
     type_p 0 tenv p t bindings /\ type_e tenv Empty e t /\
     type_pe_determ tenv Empty p e
     ==> !p_1 p_2. MEM (p_1,p_2) bindings ==> set_tids_subset tids p_2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[set_tids_subset_def; SUBSET] THEN X_GEN_TAC `x:num` THEN DISCH_TAC THEN
  CCONTR_TAC THEN
  MP_TAC(SPECL [`x:num`; `tids:num->bool`; `0`; `tenv:type_env`; `p:pat`; `t:t`;
                `bindings:(mlstring#t)list`; `x + 1`] type_p_ts_tid_rename_sing_renum) THEN
  MP_TAC(SPECL [`x:num`; `tids:num->bool`; `tenv:type_env`; `Empty`;
                `e:exp`; `t:t`; `x + 1`] type_e_ts_tid_rename_sing_renum) THEN
  ASM_REWRITE_TAC[remap_tenvE_def] THEN REPEAT DISCH_TAC THEN
  UNDISCH_TAC `type_pe_determ tenv Empty p e` THEN REWRITE_TAC[type_pe_determ_def] THEN
  DISCH_THEN(MP_TAC o SPECL [`t:t`; `bindings:(mlstring#t)list`;
    `ts_tid_rename (sing_renum x (x + 1)) t`;
    `MAP (\(nn:mlstring,t). (nn,ts_tid_rename (sing_renum x (x + 1)) t)) bindings`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SYM) THEN
  REWRITE_TAC[MAP_EQ_ID] THEN DISCH_THEN(MP_TAC o SPEC `(p_1:mlstring,p_2:t)`) THEN
  ASM_REWRITE_TAC[PAIR_EQ] THEN
  MATCH_MP_TAC sing_renum_IN_NOT_ID THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let type_pe_determ_remap = prove
 (`!tenv p e f tids n.
     type_pe_determ tenv Empty p e /\ good_remap f /\ prim_tids T tids /\
     BIJ f tids (count n) /\ set_tids_tenv tids tenv
     ==> type_pe_determ_canon n (remap_tenv f tenv) Empty p e`,
  REWRITE_TAC[type_pe_determ_canon_def; type_pe_determ_def] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "det") STRIP_ASSUME_TAC) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `good_remap (LINV f tids)` ASSUME_TAC THENL
   [ASM_MESON_TAC[good_remap_BIJ]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP type_p_ts_tid_rename) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP type_e_ts_tid_rename) THEN
  SUBGOAL_THEN `tenv_equiv (remap_tenv (LINV f tids) (remap_tenv f tenv)) tenv` ASSUME_TAC
  THENL [ASM_MESON_TAC[remap_tenv_LINV]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!t tb. type_p 0 (remap_tenv f tenv) p t tb /\ type_e (remap_tenv f tenv) Empty e t
           ==> type_p 0 tenv p (ts_tid_rename (LINV f tids) t)
                 (MAP (\(n:mlstring,t). (n,ts_tid_rename (LINV f tids) t)) tb) /\
               type_e tenv Empty e (ts_tid_rename (LINV f tids) t)`
    ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP (CONJUNCT1 (MATCH_MP type_p_ts_tid_rename
        (ASSUME `good_remap (LINV (f:num->num) tids)`)))) THEN DISCH_TAC THEN
      FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (CONJUNCT1 type_p_tenv_equiv)) THEN
      ASM_REWRITE_TAC[];
      FIRST_ASSUM(MP_TAC o MATCH_MP (CONJUNCT1 (MATCH_MP type_e_ts_tid_rename
        (ASSUME `good_remap (LINV (f:num->num) tids)`)))) THEN
      REWRITE_TAC[remap_tenvE_def] THEN DISCH_TAC THEN
      FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (CONJUNCT1 type_e_tenv_equiv)) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `MAP (\(n:mlstring,t). (n,ts_tid_rename (LINV f tids) t)) tenv1 =
    MAP (\(n:mlstring,t). (n,ts_tid_rename (LINV f tids) t)) tenv2`
    ASSUME_TAC THENL
   [USE_THEN "det" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`ts_tid_rename (LINV f tids) t1`;
                          `ts_tid_rename (LINV f tids) t2`] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `INJ (LINV f tids) (count n) (tids:num->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[BIJ_LINV_BIJ; BIJ]; ALL_TAC] THEN
  MATCH_MP_TAC(ISPEC `\(n:mlstring,t). (n,ts_tid_rename (LINV f tids) t)` INJ_MAP_EQ_2) THEN
  ASM_REWRITE_TAC[FORALL_PAIR_THM; IN_SET_OF_LIST; PAIR_EQ] THEN
  MAP_EVERY X_GEN_TAC [`k1:mlstring`; `u1:t`; `k2:mlstring`; `u2:t`] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC inj_ts_tid_rename_eq THEN
  EXISTS_TAC `LINV (f:num->num) (tids:num->bool)` THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[EVERY_MEM; FORALL_PAIR_THM; set_tids_subset_def; SUBSET]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INJ]) THEN ASM_MESON_TAC[]);;

(* DEVIATION: the hypothesis check_ctor_tenv tenvt xs is added (HOL Light's  *)
(* ZIP in type_name_subst; see notes/DEVIATIONS.md)                          *)
let build_ctor_tenv_type_identities = prove
 (CASE_TERM `!tenvt xs type_identities tids.
     prim_tids T tids /\
     nsAll (\i p. match p with
                    (ls,t) -> set_tids_subset (tids UNION set_of_list type_identities) t)
           tenvt /\
     LENGTH xs = LENGTH type_identities /\
     check_ctor_tenv tenvt xs
     ==> nsAll (\i p. match p with
                        (ls,ts,tid) ->
                          ALL (\t. set_tids_subset (tids UNION set_of_list type_identities) t)
                              ts /\
                          (tid IN tids \/ MEM tid type_identities))
               (build_ctor_tenv tenvt xs type_identities
                  :(mlstring,mlstring,mlstring list # t list # num)namespace)`,
  MATCH_MP_TAC build_ctor_tenv_ind THEN
  REWRITE_TAC[build_ctor_tenv_def; LENGTH; NOT_SUC; GSYM NOT_SUC; alist_to_ns_nil;
              nsAll_nsEmpty; SUC_INJ] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC nsAll_nsAppend THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `(id:num) INSERT tids`) THEN
    SUBGOAL_THEN `((id:num) INSERT tids) UNION set_of_list ids =
                  tids UNION set_of_list (CONS id ids)`
      SUBST1_TAC THENL [REWRITE_TAC[set_of_list] THEN SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC `prim_tids T tids` THEN REWRITE_TAC[prim_tids_def] THEN
        MATCH_MP_TAC MONO_ALL THEN SIMP_TAC[IN_INSERT];
        UNDISCH_TAC `check_ctor_tenv tenvT (CONS (tvs,tn,ctors) tds)` THEN
        SIMP_TAC[check_ctor_tenv_def]];
      ALL_TAC] THEN
    DISCH_THEN(MATCH_MP_TAC o MATCH_MP INFER1AUX_nsAll_mono_tc) THEN
    REWRITE_TAC[FORALL_PAIR_THM] THEN CASE_REWRITE_TAC[IN_INSERT; MEM] THEN MESON_TAC[];
    MATCH_MP_TAC nsAll_alist_to_ns THEN
    REWRITE_TAC[EVERY_REVERSE; ALL_MAP] THEN
    UNDISCH_TAC `check_ctor_tenv tenvT (CONS (tvs,tn,ctors) tds)` THEN
    REWRITE_TAC[check_ctor_tenv_def] THEN STRIP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[EVERY_MEM; FORALL_PAIR_THM]) THEN
    RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
    REWRITE_TAC[EVERY_MEM; FORALL_PAIR_THM; o_THM] THEN CASE_REWRITE_TAC[MEM] THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[MEM_MAP]) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC set_tids_subset_type_name_subst THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `prim_tids T tids` THEN REWRITE_TAC[prim_tids_def] THEN
      MATCH_MP_TAC MONO_ALL THEN SIMP_TAC[IN_UNION];
      ASM_MESON_TAC[]]]);;

let DISJOINT_CARD_UNION = prove
 (`!s t:A->bool. FINITE s /\ FINITE t /\ DISJOINT s t ==> CARD (s UNION t) = CARD s + CARD t`,
  MESON_TAC[CARD_UNION; DISJOINT]);;

(* Helpers for type_d_type_d_canon *)

let INFER1AUX_nsMap_nsSing = prove
 (`!(f:V->W) (n:N) (v:V). nsMap f (nsSing n v:(M,N,V)namespace) = nsSing n (f v)`,
  REWRITE_TAC[nsSing_def; nsMap_def; MAP] THEN CASE_REWRITE_TAC[]);;

let INFER1AUX_tenv_equiv_trans = prove
 (`!a b c. tenv_equiv a b /\ tenv_equiv b c ==> tenv_equiv a c`,
  REWRITE_TAC[tenv_equiv_def; nsAll2_def; nsSub_def] THEN MESON_TAC[]);;

let INFER1AUX_tenv_equiv_extend = prove
 (`!a1 b1 a2 b2.
     tenv_equiv a1 b1 /\ tenv_equiv a2 b2
     ==> tenv_equiv (extend_dec_tenv a1 a2) (extend_dec_tenv b1 b2)`,
  REWRITE_TAC[tenv_equiv_def; extend_dec_tenv_def; type_env_INFO.ri_accessors] THEN
  MESON_TAC[nsAll2_nsAppend]);;

let INFER1AUX_set_tids_tenv_empty = prove
 (`!tids. set_tids_tenv tids (type_env_REC nsEmpty nsEmpty nsEmpty)`,
  REWRITE_TAC[set_tids_tenv_def; type_env_INFO.ri_accessors; nsAll_nsEmpty]);;

let INFER1AUX_remap_tenv_empty = prove
 (`!f. remap_tenv f (type_env_REC nsEmpty nsEmpty nsEmpty) =
       type_env_REC nsEmpty nsEmpty nsEmpty`,
  REWRITE_TAC[remap_tenv_def; type_env_INFO.ri_accessors; nsMap_nsEmpty]);;

let INFER1AUX_nsAll2_nsMap_agree = prove
 (`!(g1:V->W) g2 (e:(M,N,V)namespace).
     (!id v. nsLookup e id = SOME v ==> g1 v = g2 v)
     ==> nsAll2 (\i v1 v2. v1 = v2) (nsMap g1 e) (nsMap g2 e)`,
  REWRITE_TAC[nsAll2_def; nsSub_def; nsLookup_nsMap; nsLookupMod_nsMap;
              OPTION_MAP_EQ_NONE; OPTION_MAP_EQ_SOME] THEN
  MESON_TAC[]);;

let INFER1AUX_remap_tenv_agree = prove
 (`!tids tenv f g.
     set_tids_tenv tids tenv /\ (!x. x IN tids ==> f x = g x)
     ==> tenv_equiv (remap_tenv f tenv) (remap_tenv g tenv)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP INFER1AUX_set_tids_tenv_lookup) THEN
  REWRITE_TAC[tenv_equiv_def; remap_tenv_def; type_env_INFO.ri_accessors] THEN
  REPEAT CONJ_TAC THEN MATCH_MP_TAC INFER1AUX_nsAll2_nsMap_agree THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN CASE_REWRITE_TAC[PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN RES_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[EVERY_MEM; set_tids_subset_def; SUBSET]) THEN
  ASM_SIMP_TAC[ts_tid_rename_eq_f; MAP_EQ_f] THEN ASM_MESON_TAC[]);;

let INFER1AUX_prim_tids_F_EMPTY = prove
 (`prim_tids F {}`,
  REWRITE_TAC[prim_tids_def; prim_type_nums_def; ALL; NOT_IN_EMPTY]);;

let INFER1AUX_BIJ_EMPTY = prove
 (`!g:A->B. BIJ g {} {}`,
  REWRITE_TAC[BIJ; INJ; SURJ; NOT_IN_EMPTY]);;

let INFER1AUX_nsAll_nsSing = prove
 (`!R (n:N) (x:V). R (Short n) x ==> nsAll R (nsSing n x:(M,N,V)namespace)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `nsSing n x:(M,N,V)namespace = alist_to_ns [n,x]` SUBST1_TAC THENL
   [REWRITE_TAC[nsSing_def; alist_to_ns_def]; ALL_TAC] THEN
  MATCH_MP_TAC nsAll_alist_to_ns THEN REWRITE_TAC[ALL] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[]);;

(* split the tenv_equiv assumptions into their nsAll2 components *)
let INFER1AUX_SPLIT_EQUIV_TAC =
  let is_te tm = try fst(dest_const(fst(strip_comb tm))) = "tenv_equiv"
                 with Failure _ -> false in
  ASSUM_LIST(fun ths ->
    MAP_EVERY (STRIP_ASSUME_TAC o REWRITE_RULE[tenv_equiv_def])
              (filter (is_te o concl) ths));;

let INFER1AUX_mapped_tns = prove
 (`!f tenv mt t.
     good_remap f /\ tenv_equiv (remap_tenv f tenv) mt /\ check_type_names (type_env_t tenv) t
     ==> check_type_names (type_env_t mt) t /\
         ts_tid_rename f (type_name_subst (type_env_t tenv) t) =
         type_name_subst (type_env_t mt) t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN INFER1AUX_SPLIT_EQUIV_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC check_type_names_tenv_equiv THEN
    EXISTS_TAC `type_env_t (remap_tenv f tenv)` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[remap_tenv_def; type_env_INFO.ri_accessors;
                GSYM check_type_names_ts_tid_rename] THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[INFER1AUX_tns_remap] THEN MATCH_MP_TAC type_name_subst_tenv_equiv THEN
    ASM_REWRITE_TAC[]]);;

let INFER1AUX_remap_alist_tenv_add_tvs = prove
 (`!f tvs bindings.
     remap_tenv f (type_env_REC (alist_to_ns (tenv_add_tvs tvs bindings)) nsEmpty nsEmpty) =
     type_env_REC (alist_to_ns (tenv_add_tvs tvs
                     (MAP (\(n:mlstring,t). (n,ts_tid_rename f t)) bindings)))
                  nsEmpty nsEmpty`,
  REWRITE_TAC[remap_tenv_def; type_env_INFO.ri_accessors; nsMap_nsEmpty;
              nsMap_alist_to_ns; tenv_add_tvs_def; MAP_MAP_o] THEN
  REPEAT GEN_TAC THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[MAP_EQ_f; FORALL_PAIR_THM; o_THM] THEN CASE_REWRITE_TAC[]);;

let INFER1AUX_set_tids_tenv_alist = prove
 (`!tids tvs bindings.
     (!p_1 p_2. MEM (p_1,p_2) bindings ==> set_tids_subset tids p_2)
     ==> set_tids_tenv tids
           (type_env_REC (alist_to_ns (tenv_add_tvs tvs bindings)) nsEmpty nsEmpty)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[set_tids_tenv_def; type_env_INFO.ri_accessors; nsAll_nsEmpty] THEN
  MATCH_MP_TAC nsAll_alist_to_ns THEN
  REWRITE_TAC[tenv_add_tvs_def; ALL_MAP] THEN
  REWRITE_TAC[EVERY_MEM; FORALL_PAIR_THM; o_THM] THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[]);;

let INFER1AUX_tenv_add_tvs_GABS = prove
 (`!tvs (l:(mlstring#t)list). tenv_add_tvs tvs l = MAP (\(n:mlstring,t). (n,tvs,t)) l`,
  REWRITE_TAC[tenv_add_tvs_def] THEN REPEAT GEN_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM] THEN CASE_REWRITE_TAC[]);;

let INFER1AUX_MAP_SND_tenv_add_tvs = prove
 (`!tvs (l:(mlstring#t)list). MAP SND (tenv_add_tvs tvs l) = MAP (\x. (tvs,SND x)) l`,
  REWRITE_TAC[tenv_add_tvs_def; MAP_MAP_o] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[MAP_EQ_f; FORALL_PAIR_THM; o_THM] THEN CASE_REWRITE_TAC[]);;

let INFER1AUX_tscheme_inst_transfer = prove
 (`!f tids n tvs tvs' b' b.
     BIJ f tids (count n) /\ set_tids_subset (count n) b' /\
     tscheme_inst (tvs',ts_tid_rename (LINV f tids) b') (tvs,b)
     ==> tscheme_inst (tvs',b') (tvs,ts_tid_rename f b)`,
  REWRITE_TAC[tscheme_inst_def] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `MAP (ts_tid_rename f) subst` THEN
  ASM_REWRITE_TAC[LENGTH_MAP; check_freevars_ts_tid_rename; EVERY_MAP; ETA_AX] THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `ts_tid_rename (f:num->num)`) THEN
  REWRITE_TAC[ts_tid_rename_deBruijn_subst; ts_tid_rename_compose] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[ts_tid_rename_eq_id; o_THM] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[set_tids_subset_def; SUBSET]) THEN
  ASM_MESON_TAC[BIJ_LINV_INV]);;

let INFER1AUX_ALL2_transfer = prove
 (`!f tids n tvs tvs' (b':(mlstring#t)list) (b:(mlstring#t)list).
     BIJ f tids (count n) /\ ALL (\(k:mlstring,t). set_tids_subset (count n) t) b' /\
     ALL2 tscheme_inst
       (MAP (\x. (tvs',SND x)) (MAP (\(n:mlstring,t). (n,ts_tid_rename (LINV f tids) t)) b'))
       (MAP (\x. (tvs,SND x)) b)
     ==> ALL2 tscheme_inst (MAP (\x. (tvs',SND x)) b')
           (MAP (\x. (tvs,SND x)) (MAP (\(n:mlstring,t). (n,ts_tid_rename f t)) b))`,
  REPEAT GEN_TAC THEN
  SPEC_TAC(`b:(mlstring#t)list`,`b:(mlstring#t)list`) THEN
  SPEC_TAC(`b':(mlstring#t)list`,`b':(mlstring#t)list`) THEN
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; ALL2; ALL] THEN
  SPEC_TAC(`h:mlstring#t`,`h:mlstring#t`) THEN
  SPEC_TAC(`h':mlstring#t`,`h':mlstring#t`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC INFER1AUX_tscheme_inst_transfer THEN ASM_MESON_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let INFER1AUX_pull_back = prove
 (`!f tids n tenv mt.
     BIJ f tids (count n) /\ good_remap f /\ prim_tids T tids /\
     set_tids_tenv tids tenv /\ tenv_equiv (remap_tenv f tenv) mt
     ==> (!tvs p t b.
            type_p tvs mt p t b
            ==> type_p tvs tenv p (ts_tid_rename (LINV f tids) t)
                  (MAP (\(n:mlstring,t). (n,ts_tid_rename (LINV f tids) t)) b)) /\
         (!tvs e t.
            type_e mt (bind_tvar tvs Empty) e t
            ==> type_e tenv (bind_tvar tvs Empty) e (ts_tid_rename (LINV f tids) t)) /\
         (!tvs b funs b'.
            type_funs mt (bind_var_list 0 b (bind_tvar tvs Empty)) funs b'
            ==> type_funs tenv
                  (bind_var_list 0
                     (MAP (\(n:mlstring,t). (n,ts_tid_rename (LINV f tids) t)) b)
                     (bind_tvar tvs Empty))
                  funs (MAP (\(n:mlstring,t). (n,ts_tid_rename (LINV f tids) t)) b'))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `good_remap (LINV f tids)` ASSUME_TAC THENL
   [ASM_MESON_TAC[good_remap_BIJ]; ALL_TAC] THEN
  SUBGOAL_THEN `tenv_equiv (remap_tenv (LINV f tids) (remap_tenv f tenv)) tenv` ASSUME_TAC
  THENL [ASM_MESON_TAC[remap_tenv_LINV]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP tenv_equiv_sym o
    check (fun th -> concl th = `tenv_equiv (remap_tenv f tenv) mt`)) THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `remap_tenv f tenv` o
      MATCH_MP (CONJUNCT1 type_p_tenv_equiv)) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (CONJUNCT1 (MATCH_MP type_p_ts_tid_rename
      (ASSUME `good_remap (LINV (f:num->num) tids)`)))) THEN
    DISCH_THEN(MATCH_MP_TAC o MATCH_MP (CONJUNCT1 type_p_tenv_equiv)) THEN
    ASM_REWRITE_TAC[];
    FIRST_ASSUM(MP_TAC o SPEC `remap_tenv f tenv` o
      MATCH_MP (CONJUNCT1 type_e_tenv_equiv)) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (CONJUNCT1 (MATCH_MP type_e_ts_tid_rename
      (ASSUME `good_remap (LINV (f:num->num) tids)`)))) THEN
    REWRITE_TAC[remap_tenvE_bind_tvar; remap_tenvE_def] THEN
    DISCH_THEN(MATCH_MP_TAC o MATCH_MP (CONJUNCT1 type_e_tenv_equiv)) THEN
    ASM_REWRITE_TAC[];
    FIRST_ASSUM(MP_TAC o SPEC `remap_tenv f tenv` o
      MATCH_MP (CONJUNCT2 (CONJUNCT2 type_e_tenv_equiv))) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (CONJUNCT2 (CONJUNCT2 (MATCH_MP type_e_ts_tid_rename
      (ASSUME `good_remap (LINV (f:num->num) tids)`))))) THEN
    REWRITE_TAC[remap_tenvE_bind_var_list; remap_tenvE_bind_tvar; remap_tenvE_def] THEN
    DISCH_THEN(MATCH_MP_TAC o MATCH_MP (CONJUNCT2 (CONJUNCT2 type_e_tenv_equiv))) THEN
    ASM_REWRITE_TAC[]]);;

let INFER1AUX_push_forward = prove
 (`!f tenv mt.
     good_remap f /\ tenv_equiv (remap_tenv f tenv) mt
     ==> (!tvs p t b.
            type_p tvs tenv p t b
            ==> type_p tvs mt p (ts_tid_rename f t)
                  (MAP (\(n:mlstring,t). (n,ts_tid_rename f t)) b)) /\
         (!tvs e t.
            type_e tenv (bind_tvar tvs Empty) e t
            ==> type_e mt (bind_tvar tvs Empty) e (ts_tid_rename f t)) /\
         (!tvs b funs b'.
            type_funs tenv (bind_var_list 0 b (bind_tvar tvs Empty)) funs b'
            ==> type_funs mt
                  (bind_var_list 0 (MAP (\(n:mlstring,t). (n,ts_tid_rename f t)) b)
                     (bind_tvar tvs Empty))
                  funs (MAP (\(n:mlstring,t). (n,ts_tid_rename f t)) b'))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP (CONJUNCT1 (MATCH_MP type_p_ts_tid_rename
      (ASSUME `good_remap (f:num->num)`)))) THEN
    DISCH_THEN(MATCH_MP_TAC o MATCH_MP (CONJUNCT1 type_p_tenv_equiv)) THEN
    ASM_REWRITE_TAC[];
    FIRST_ASSUM(MP_TAC o MATCH_MP (CONJUNCT1 (MATCH_MP type_e_ts_tid_rename
      (ASSUME `good_remap (f:num->num)`)))) THEN
    REWRITE_TAC[remap_tenvE_bind_tvar; remap_tenvE_def] THEN
    DISCH_THEN(MATCH_MP_TAC o MATCH_MP (CONJUNCT1 type_e_tenv_equiv)) THEN
    ASM_REWRITE_TAC[];
    FIRST_ASSUM(MP_TAC o MATCH_MP (CONJUNCT2 (CONJUNCT2 (MATCH_MP type_e_ts_tid_rename
      (ASSUME `good_remap (f:num->num)`))))) THEN
    REWRITE_TAC[remap_tenvE_bind_var_list; remap_tenvE_bind_tvar; remap_tenvE_def] THEN
    DISCH_THEN(MATCH_MP_TAC o MATCH_MP (CONJUNCT2 (CONJUNCT2 type_e_tenv_equiv))) THEN
    ASM_REWRITE_TAC[]]);;

(* ---------- the cases of type_d_type_d_canon ---------- *)

let INFER1AUX_TDC_NIL_TAC =
  REPEAT STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`\x:num. x`; `type_env_REC nsEmpty nsEmpty nsEmpty`] THEN
  REWRITE_TAC[UNION_EMPTY; INFER1AUX_set_tids_tenv_empty; INFER1AUX_prim_tids_F_EMPTY;
              FINITE_EMPTY; CARD_CLAUSES; COUNT_ZERO; INFER1AUX_BIJ_EMPTY;
              INFER1AUX_remap_tenv_empty; tenv_equiv_refl] THEN
  MATCH_MP_TAC(el 8 (CONJUNCTS type_d_canon_rules)) THEN REWRITE_TAC[];;

let INFER1AUX_TDC_DTABBREV_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`f:num->num`; `tenv:type_env`; `mapped_tenv:type_env`; `t:ast_t`]
               INFER1AUX_mapped_tns) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `\x:num. x` THEN
  EXISTS_TAC `type_env_REC nsEmpty nsEmpty
                (nsSing tn (tvs,type_name_subst (type_env_t mapped_tenv) t))` THEN
  REWRITE_TAC[UNION_EMPTY; INFER1AUX_prim_tids_F_EMPTY; FINITE_EMPTY; CARD_CLAUSES;
              COUNT_ZERO; INFER1AUX_BIJ_EMPTY; extend_bij_id] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[set_tids_tenv_def; type_env_INFO.ri_accessors; nsAll_nsEmpty] THEN
    MATCH_MP_TAC INFER1AUX_nsAll_nsSing THEN CASE_REWRITE_TAC[] THEN
    MATCH_MP_TAC set_tids_subset_type_name_subst THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT1 o REWRITE_RULE[set_tids_tenv_def]) THEN
    REWRITE_TAC[];
    MATCH_MP_TAC(el 4 (CONJUNCTS type_d_canon_rules)) THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[remap_tenv_def; type_env_INFO.ri_accessors; nsMap_nsEmpty;
                INFER1AUX_nsMap_nsSing] THEN
    CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[tenv_equiv_refl]];;

let INFER1AUX_TDC_DEXN_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!t. MEM t ts ==> check_type_names (type_env_t mapped_tenv) t /\
                   ts_tid_rename f (type_name_subst (type_env_t tenv) t) =
                   type_name_subst (type_env_t mapped_tenv) t` ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC INFER1AUX_mapped_tns THEN
    RULE_ASSUM_TAC(REWRITE_RULE[EVERY_MEM]) THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `\x:num. x` THEN
  EXISTS_TAC `type_env_REC nsEmpty
                (nsSing cn ([],MAP (type_name_subst (type_env_t mapped_tenv)) ts,Texn_num))
                nsEmpty` THEN
  REWRITE_TAC[UNION_EMPTY; INFER1AUX_prim_tids_F_EMPTY; FINITE_EMPTY; CARD_CLAUSES;
              COUNT_ZERO; INFER1AUX_BIJ_EMPTY; extend_bij_id] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[set_tids_tenv_def; type_env_INFO.ri_accessors; nsAll_nsEmpty] THEN
    MATCH_MP_TAC INFER1AUX_nsAll_nsSing THEN CASE_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[EVERY_MAP; EVERY_MEM] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC set_tids_subset_type_name_subst THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [FIRST_ASSUM(MP_TAC o CONJUNCT1 o REWRITE_RULE[set_tids_tenv_def]) THEN
        REWRITE_TAC[];
        RULE_ASSUM_TAC(REWRITE_RULE[EVERY_MEM]) THEN ASM_MESON_TAC[]];
      UNDISCH_TAC `prim_tids T tids` THEN
      REWRITE_TAC[prim_tids_def; prim_type_nums_def; ALL] THEN SIMP_TAC[]];
    MATCH_MP_TAC(el 5 (CONJUNCTS type_d_canon_rules)) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[EVERY_MEM] THEN ASM_MESON_TAC[];
    REWRITE_TAC[remap_tenv_def; type_env_INFO.ri_accessors; nsMap_nsEmpty;
                INFER1AUX_nsMap_nsSing] THEN
    CASE_REWRITE_TAC[MAP_MAP_o] THEN
    REWRITE_TAC[INFER1AUX_GR] THEN
    SUBGOAL_THEN `MAP (ts_tid_rename f o type_name_subst (type_env_t tenv)) ts =
                  MAP (type_name_subst (type_env_t mapped_tenv)) ts`
      (fun th -> REWRITE_TAC[th; tenv_equiv_refl]) THEN
    REWRITE_TAC[MAP_EQ_f; o_THM] THEN ASM_MESON_TAC[]];;

let INFER1AUX_remap_tenvLift = prove
 (`!h mn x. remap_tenv h (tenvLift mn x) = tenvLift mn (remap_tenv h x)`,
  REWRITE_TAC[remap_tenv_def; tenvLift_def; type_env_INFO.ri_accessors; nsLift_nsMap]);;

let INFER1AUX_TDC_DMOD_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`tids:num->bool`; `f:num->num`; `n:num`;
                                `mapped_tenv:type_env`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:num->num` (X_CHOOSE_THEN `mt:type_env` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`g:num->num`; `tenvLift mn mt`] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `set_tids_tenv (tids UNION decls) tenv'` THEN
    REWRITE_TAC[set_tids_tenv_def; tenvLift_def; type_env_INFO.ri_accessors; nsAll_nsLift];
    MATCH_MP_TAC(el 6 (CONJUNCTS type_d_canon_rules)) THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[INFER1AUX_remap_tenvLift] THEN MATCH_MP_TAC tenv_equiv_tenvLift THEN
    ASM_REWRITE_TAC[]];;

(* the common part of the Dlocal and the cons cases: instantiate the two     *)
(* induction hypotheses; leaves the final existential with g1 g2 mt1 mt2   *)
let INFER1AUX_TDC_TWO_IH_TAC =
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ih1"))
    (CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ih2")) ASSUME_TAC)) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REMOVE_THEN "ih1" (MP_TAC o SPECL [`tids:num->bool`; `f:num->num`; `n:num`;
                                     `mapped_tenv:type_env`]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g1:num->num` (X_CHOOSE_THEN `mt1:type_env` STRIP_ASSUME_TAC)) THEN
  REMOVE_THEN "ih2" (MP_TAC o SPECL [`tids UNION decls1:num->bool`;
     `extend_bij f g1 decls1 n`; `n + CARD (decls1:num->bool)`;
     `extend_dec_tenv mt1 mapped_tenv`]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM SET_TAC[];
      MATCH_MP_TAC set_tids_tenv_extend_dec_tenv THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC set_tids_tenv_mono THEN EXISTS_TAC `tids:num->bool` THEN
      ASM_REWRITE_TAC[SUBSET_UNION];
      MATCH_MP_TAC BIJ_extend_bij THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      UNDISCH_TAC `prim_tids T tids` THEN REWRITE_TAC[prim_tids_def] THEN
      MATCH_MP_TAC MONO_ALL THEN SIMP_TAC[IN_UNION];
      MATCH_MP_TAC good_remap_extend_bij THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[remap_tenv_extend_dec_tenv] THEN MATCH_MP_TAC INFER1AUX_tenv_equiv_extend THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INFER1AUX_tenv_equiv_trans THEN
      EXISTS_TAC `remap_tenv f tenv` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC INFER1AUX_remap_tenv_agree THEN EXISTS_TAC `tids:num->bool` THEN
      ASM_REWRITE_TAC[extend_bij_def] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g2:num->num` (X_CHOOSE_THEN `mt2:type_env` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `CARD (decls1 UNION decls2:num->bool) = CARD decls1 + CARD decls2`
    SUBST1_TAC THENL [MATCH_MP_TAC DISJOINT_CARD_UNION THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `extend_bij g1 g2 decls2 (CARD (decls1:num->bool))` THEN
  REWRITE_TAC[GSYM extend_bij_compose; FINITE_UNION] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[UNION_ASSOC]) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `prim_tids F (decls1 UNION decls2) /\
                BIJ (extend_bij g1 g2 decls2 (CARD decls1)) (decls1 UNION decls2)
                    (count (CARD decls1 + CARD decls2))` (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `prim_tids F decls1` THEN UNDISCH_TAC `prim_tids F decls2` THEN
      REWRITE_TAC[prim_tids_def; prim_type_nums_def; ALL; IN_UNION] THEN SIMP_TAC[];
      MATCH_MP_TAC BIJ_extend_bij THEN ASM_REWRITE_TAC[]];
    ALL_TAC];;

let INFER1AUX_TDC_DLOCAL_TAC =
  INFER1AUX_TDC_TWO_IH_TAC THEN EXISTS_TAC `mt2:type_env` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(el 7 (CONJUNCTS type_d_canon_rules)) THEN
  EXISTS_TAC `mt1:type_env` THEN ASM_REWRITE_TAC[];;

let INFER1AUX_TDC_CONS_TAC =
  INFER1AUX_TDC_TWO_IH_TAC THEN EXISTS_TAC `extend_dec_tenv mt2 mt1` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC set_tids_tenv_extend_dec_tenv THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC set_tids_tenv_mono THEN EXISTS_TAC `tids UNION decls1:num->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    MATCH_MP_TAC(el 9 (CONJUNCTS type_d_canon_rules)) THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[remap_tenv_extend_dec_tenv] THEN MATCH_MP_TAC INFER1AUX_tenv_equiv_extend THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INFER1AUX_tenv_equiv_trans THEN
    EXISTS_TAC `remap_tenv (extend_bij f g1 decls1 n) tenv1` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC INFER1AUX_remap_tenv_agree THEN EXISTS_TAC `tids UNION decls1:num->bool` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:num` THEN DISCH_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV) [extend_bij_def] THEN
    SUBGOAL_THEN `~(x IN (decls2:num->bool))` (fun th -> REWRITE_TAC[th]) THEN
    MAP_EVERY UNDISCH_TAC [`x IN tids UNION (decls1:num->bool)`;
      `DISJOINT (decls1 UNION decls2) (tids:num->bool)`;
      `DISJOINT decls1 (decls2:num->bool)`] THEN
    SET_TAC[]];;

let INFER1AUX_TDC_DLET_MONO_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `extra_checks ==> ~is_value e /\ type_pe_determ tenv Empty p e` THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[UNION_EMPTY; INFER1AUX_prim_tids_F_EMPTY; FINITE_EMPTY; CARD_CLAUSES;
                  COUNT_ZERO; INFER1AUX_BIJ_EMPTY; extend_bij_id;
                  INFER1AUX_remap_alist_tenv_add_tvs] THEN
  EXISTS_TAC `type_env_REC (alist_to_ns (tenv_add_tvs 0
                (MAP (\(n:mlstring,t). (n,ts_tid_rename f t)) bindings))) nsEmpty nsEmpty` THEN
  REWRITE_TAC[tenv_equiv_refl] THEN CONJ_TAC THENL
   [MATCH_MP_TAC INFER1AUX_set_tids_tenv_alist THEN
    MATCH_MP_TAC type_pe_bindings_tids_0 THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(el 1 (CONJUNCTS type_d_canon_rules)) THEN
  EXISTS_TAC `ts_tid_rename f t` THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC type_pe_determ_canon_tenv_equiv THEN
    EXISTS_TAC `remap_tenv f tenv` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC type_pe_determ_remap THEN EXISTS_TAC `tids:num->bool` THEN
    ASM_REWRITE_TAC[];
    FIRST_ASSUM(MP_TAC o MATCH_MP (CONJUNCT1 (MATCH_MP type_p_ts_tid_rename
      (ASSUME `good_remap (f:num->num)`)))) THEN
    DISCH_THEN(MATCH_MP_TAC o MATCH_MP (CONJUNCT1 type_p_tenv_equiv)) THEN
    ASM_REWRITE_TAC[];
    FIRST_ASSUM(MP_TAC o MATCH_MP (CONJUNCT1 (MATCH_MP type_e_ts_tid_rename
      (ASSUME `good_remap (f:num->num)`)))) THEN
    REWRITE_TAC[remap_tenvE_def] THEN
    DISCH_THEN(MATCH_MP_TAC o MATCH_MP (CONJUNCT1 type_e_tenv_equiv)) THEN
    ASM_REWRITE_TAC[]];;

let INFER1AUX_EXTRA_CHECKS_TAC =
  FIRST_X_ASSUM(fun th ->
    if is_imp (concl th) && fst(dest_imp(concl th)) = `extra_checks:bool`
    then MP_TAC th THEN ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "gen")
    else failwith "no");;

let INFER1AUX_TDC_DLET_POLY_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  INFER1AUX_EXTRA_CHECKS_TAC THEN
  ASM_REWRITE_TAC[UNION_EMPTY; INFER1AUX_prim_tids_F_EMPTY; FINITE_EMPTY; CARD_CLAUSES;
                  COUNT_ZERO; INFER1AUX_BIJ_EMPTY; extend_bij_id;
                  INFER1AUX_remap_alist_tenv_add_tvs] THEN
  EXISTS_TAC `type_env_REC (alist_to_ns (tenv_add_tvs tvs
                (MAP (\(n:mlstring,t). (n,ts_tid_rename f t)) bindings))) nsEmpty nsEmpty` THEN
  REWRITE_TAC[tenv_equiv_refl] THEN CONJ_TAC THENL
   [MATCH_MP_TAC INFER1AUX_set_tids_tenv_alist THEN
    MP_TAC(SPECL [`tids:num->bool`; `tenv:type_env`; `tvs:num`; `p:pat`; `t:t`;
                  `bindings:(mlstring#t)list`; `e:exp`] type_pe_bindings_tids) THEN
    ASM_REWRITE_TAC[GSYM INFER1AUX_tenv_add_tvs_GABS];
    ALL_TAC] THEN
  MP_TAC(SPECL [`f:num->num`; `tenv:type_env`; `mapped_tenv:type_env`]
               INFER1AUX_push_forward) THEN
  MP_TAC(SPECL [`f:num->num`; `tids:num->bool`; `n:num`; `tenv:type_env`;
                `mapped_tenv:type_env`] INFER1AUX_pull_back) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "pbp") (CONJUNCTS_THEN2 (LABEL_TAC "pbe") ASSUME_TAC)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "pfp") (CONJUNCTS_THEN2 (LABEL_TAC "pfe") ASSUME_TAC)) THEN
  MATCH_MP_TAC(el 0 (CONJUNCTS type_d_canon_rules)) THEN
  EXISTS_TAC `ts_tid_rename f t` THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [USE_THEN "pfp" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    USE_THEN "pfe" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN
    REMOVE_THEN "gen" (MP_TAC o SPECL [`tvs':num`;
       `MAP (\(n:mlstring,t). (n,ts_tid_rename (LINV f tids) t)) bindings'`;
       `ts_tid_rename (LINV f tids) t'`]) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [USE_THEN "pbp" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        USE_THEN "pbe" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[INFER1AUX_MAP_SND_tenv_add_tvs] THEN DISCH_TAC THEN
    MATCH_MP_TAC INFER1AUX_ALL2_transfer THEN
    MAP_EVERY EXISTS_TAC [`tids:num->bool`; `n:num`] THEN ASM_REWRITE_TAC[]];;

let INFER1AUX_TDC_DLETREC_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  INFER1AUX_EXTRA_CHECKS_TAC THEN
  ASM_REWRITE_TAC[UNION_EMPTY; INFER1AUX_prim_tids_F_EMPTY; FINITE_EMPTY; CARD_CLAUSES;
                  COUNT_ZERO; INFER1AUX_BIJ_EMPTY; extend_bij_id;
                  INFER1AUX_remap_alist_tenv_add_tvs] THEN
  EXISTS_TAC `type_env_REC (alist_to_ns (tenv_add_tvs tvs
                (MAP (\(n:mlstring,t). (n,ts_tid_rename f t)) bindings))) nsEmpty nsEmpty` THEN
  REWRITE_TAC[tenv_equiv_refl] THEN CONJ_TAC THENL
   [MATCH_MP_TAC INFER1AUX_set_tids_tenv_alist THEN
    MP_TAC(SPECL [`tenv:type_env`; `bindings:(mlstring#t)list`; `tvs:num`;
                  `funs:(mlstring#mlstring#exp)list`; `tids:num->bool`]
                 type_funs_bindings_tids) THEN
    USE_THEN "gen" (MP_TAC o REWRITE_RULE[INFER1AUX_MAP_SND_tenv_add_tvs]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[EVERY_MEM; FORALL_PAIR_THM; o_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`f:num->num`; `tenv:type_env`; `mapped_tenv:type_env`]
               INFER1AUX_push_forward) THEN
  MP_TAC(SPECL [`f:num->num`; `tids:num->bool`; `n:num`; `tenv:type_env`;
                `mapped_tenv:type_env`] INFER1AUX_pull_back) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "pbf"))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "pff"))) THEN
  MATCH_MP_TAC(el 2 (CONJUNCTS type_d_canon_rules)) THEN CONJ_TAC THENL
   [USE_THEN "pff" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN
    REMOVE_THEN "gen" (MP_TAC o SPECL [`tvs':num`;
       `MAP (\(n:mlstring,t). (n,ts_tid_rename (LINV f tids) t)) bindings'`]) THEN
    ANTS_TAC THENL [USE_THEN "pbf" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[INFER1AUX_MAP_SND_tenv_add_tvs] THEN DISCH_TAC THEN
    MATCH_MP_TAC INFER1AUX_ALL2_transfer THEN
    MAP_EVERY EXISTS_TAC [`tids:num->bool`; `n:num`] THEN ASM_REWRITE_TAC[]];;

(* ---------- helpers for the Dtype case ---------- *)

let INFER1AUX_nsLookup_nsAppend_alist = prove
 (CASE_TERM `!l (e:(M,N,V)namespace) id.
     nsLookup (nsAppend (alist_to_ns l) e) id =
     match nsLookup (alist_to_ns l) id with SOME v -> SOME v | NONE -> nsLookup e id`,
  GEN_TAC THEN GEN_TAC THEN CASES_ON `e:(M,N,V)namespace` THEN
  MATCH_MP_TAC id_INDUCT THEN
  REWRITE_TAC[alist_to_ns_def; nsAppend_def; nsLookup_def; APPEND; ALOOKUP_APPEND;
              ALOOKUP_THM] THEN
  CASE_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
  CASES_ON `ALOOKUP (l:(N#V)list) a` THEN CASE_REWRITE_TAC[]);;
let INFER1AUX_check_type_names_FST = prove
 (`!(E:(mlstring,mlstring,mlstring list#t)namespace) E'.
     (!id. OPTION_MAP FST (nsLookup E id) = OPTION_MAP FST (nsLookup E' id))
     ==> !t. check_type_names E t <=> check_type_names E' t`,
  GEN_TAC THEN GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC INFER1AUX_ast_t_ind THEN
  REWRITE_TAC[check_type_names_def; EVERY_MEM] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:(mlstring,mlstring)id`) THEN
  CASES_ON `nsLookup (E:(mlstring,mlstring,mlstring list#t)namespace) n` THEN
  CASES_ON `nsLookup (E':(mlstring,mlstring,mlstring list#t)namespace) n` THEN
  CASE_REWRITE_TAC[OPTION_MAP_DEF] THEN
  REWRITE_TAC[pair_CASE_def] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]);;

let INFER1AUX_ALOOKUP_tenvT_FST = prove
 (CASE_TERM `!(tdefs:(mlstring list#mlstring#(mlstring#ast_t list)list)list) ids ids' x.
     LENGTH ids = LENGTH tdefs /\ LENGTH ids' = LENGTH tdefs
     ==> OPTION_MAP FST (ALOOKUP (MAP2 (\tdef i. match tdef with
                          (tvs,tn,ctors) -> (tn,(tvs,Tapp (MAP Tvar tvs) i))) tdefs ids) x) =
         OPTION_MAP FST (ALOOKUP (MAP2 (\tdef i. match tdef with
                          (tvs,tn,ctors) -> (tn,(tvs,Tapp (MAP Tvar tvs) i))) tdefs ids') x)`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `ids:num list` list_CASES) THEN
  STRUCT_CASES_TAC(ISPEC `ids':num list` list_CASES) THEN
  REWRITE_TAC[LENGTH; NOT_SUC; GSYM NOT_SUC; SUC_INJ; MAP2; ALOOKUP_THM] THEN
  STRIP_TAC THEN
  MP_TAC(ISPEC `h:mlstring list#mlstring#(mlstring#ast_t list)list` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `tvs:mlstring list` (X_CHOOSE_THEN `r:mlstring#(mlstring#ast_t list)list`
    SUBST1_TAC)) THEN
  MP_TAC(ISPEC `r:mlstring#(mlstring#ast_t list)list` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `tn:mlstring` (X_CHOOSE_THEN `ctors:(mlstring#ast_t list)list`
    SUBST1_TAC)) THEN
  CASE_REWRITE_TAC[ALOOKUP_THM] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[OPTION_MAP_DEF] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let INFER1AUX_tenvT_lookup_FST = prove
 (CASE_TERM `!(tdefs:(mlstring list#mlstring#(mlstring#ast_t list)list)list) ids ids'
     (e:(mlstring,mlstring,mlstring list#t)namespace) e'.
     LENGTH ids = LENGTH tdefs /\ LENGTH ids' = LENGTH tdefs /\
     (!id. OPTION_MAP FST (nsLookup e id) = OPTION_MAP FST (nsLookup e' id))
     ==> !id. OPTION_MAP FST (nsLookup (nsAppend (alist_to_ns (MAP2 (\tdef i. match tdef with
                          (tvs,tn,ctors) -> (tn,(tvs,Tapp (MAP Tvar tvs) i))) tdefs ids)) e) id) =
              OPTION_MAP FST (nsLookup (nsAppend (alist_to_ns (MAP2 (\tdef i. match tdef with
                          (tvs,tn,ctors) -> (tn,(tvs,Tapp (MAP Tvar tvs) i))) tdefs ids')) e') id)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[INFER1AUX_nsLookup_nsAppend_alist] THEN
  MATCH_MP_TAC id_INDUCT THEN REWRITE_TAC[alist_to_ns_def; nsLookup_def; ALOOKUP_THM] THEN
  CASE_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `x:mlstring` THEN
    MP_TAC(SPECL [`tdefs:(mlstring list#mlstring#(mlstring#ast_t list)list)list`;
                  `ids:num list`; `ids':num list`; `x:mlstring`] INFER1AUX_ALOOKUP_tenvT_FST) THEN
    ASM_REWRITE_TAC[] THEN
    CASE_TAC THEN CASE_TAC THEN REWRITE_TAC[OPTION_MAP_DEF; option_DISTINCT] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[injectivity "option"];
    ASM_REWRITE_TAC[]]);;

let INFER1AUX_mapped_t_FST = prove
 (`!f tenv mt.
     tenv_equiv (remap_tenv f tenv) mt
     ==> !id. OPTION_MAP FST (nsLookup (type_env_t tenv) id) =
              OPTION_MAP FST (nsLookup (type_env_t mt) id)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tenv_equiv_def] THEN STRIP_TAC THEN GEN_TAC THEN
  UNDISCH_TAC `nsAll2 (\i v1 v2. v1 = v2) (type_env_t (remap_tenv f tenv)) (type_env_t mt)` THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM(MATCH_MP INFER1AUX_nsAll2_eq_lookup th)]) THEN
  REWRITE_TAC[remap_tenv_def; type_env_INFO.ri_accessors; nsLookup_nsMap] THEN
  CASES_ON `nsLookup (type_env_t tenv) id` THEN CASE_REWRITE_TAC[OPTION_MAP_DEF] THEN
  MP_TAC(ISPEC `a:mlstring list#t` PAIR_SURJECTIVE) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]);;

let INFER1AUX_MAP_rename_Tvar = prove
 (`!ff (tvs:mlstring list). MAP (ts_tid_rename ff) (MAP Tvar tvs) = MAP Tvar tvs`,
  REWRITE_TAC[MAP_MAP_o; MAP_EQ_f; o_THM; ts_tid_rename_def]);;

let INFER1AUX_nsMap_tenvT = prove
 (CASE_TERM `!ff (tdefs:(mlstring list#mlstring#(mlstring#ast_t list)list)list) ids ids'.
     LENGTH ids = LENGTH tdefs /\ LENGTH ids' = LENGTH tdefs /\
     (!k. k < LENGTH ids ==> ff (EL k ids) = EL k ids')
     ==> nsMap (\p. match p with (ls,t) -> (ls,ts_tid_rename ff t))
               (alist_to_ns (MAP2 (\tdef i. match tdef with
                  (tvs,tn,ctors) -> (tn,(tvs,Tapp (MAP Tvar tvs) i))) tdefs ids)
                :(mlstring,mlstring,mlstring list#t)namespace) =
         alist_to_ns (MAP2 (\tdef i. match tdef with
                  (tvs,tn,ctors) -> (tn,(tvs,Tapp (MAP Tvar tvs) i))) tdefs ids')`,
  GEN_TAC THEN REWRITE_TAC[nsMap_alist_to_ns; alist_to_ns_11] THEN
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `ids:num list` list_CASES) THEN
  STRUCT_CASES_TAC(ISPEC `ids':num list` list_CASES) THEN
  REWRITE_TAC[LENGTH; NOT_SUC; GSYM NOT_SUC; SUC_INJ; MAP2; MAP] THEN
  STRIP_TAC THEN
  MP_TAC(ISPEC `h:mlstring list#mlstring#(mlstring#ast_t list)list` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `tvs:mlstring list` (X_CHOOSE_THEN `r:mlstring#(mlstring#ast_t list)list`
    SUBST1_TAC)) THEN
  MP_TAC(ISPEC `r:mlstring#(mlstring#ast_t list)list` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `tn:mlstring` (X_CHOOSE_THEN `ctors:(mlstring#ast_t list)list`
    SUBST1_TAC)) THEN
  CASE_REWRITE_TAC[ts_tid_rename_def; INFER1AUX_MAP_rename_Tvar; CONS_11; PAIR_EQ] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN REWRITE_TAC[LENGTH; LT_0; EL; HD];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `SUC k`) THEN ASM_REWRITE_TAC[LENGTH; LT_SUC; EL; TL]]);;

let INFER1AUX_nsMap_build_ctor_tenv = prove
 (CASE_TERM `!ff E E' (tdefs:(mlstring list#mlstring#(mlstring#ast_t list)list)list) ids ids'.
     LENGTH ids = LENGTH tdefs /\ LENGTH ids' = LENGTH tdefs /\
     (!k. k < LENGTH ids ==> ff (EL k ids) = EL k ids') /\
     (!tvs tn ctors cn ts t. MEM (tvs,tn,ctors) tdefs /\ MEM (cn,ts) ctors /\ MEM t ts
         ==> ts_tid_rename ff (type_name_subst E t) = type_name_subst E' t)
     ==> nsMap (\p. match p with (ls,ts,tid) -> (ls,MAP (ts_tid_rename ff) ts,ff tid))
               (build_ctor_tenv E tdefs ids
                :(mlstring,mlstring,mlstring list#t list#num)namespace) =
         build_ctor_tenv E' tdefs ids'`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `ids:num list` list_CASES) THEN
  STRUCT_CASES_TAC(ISPEC `ids':num list` list_CASES) THEN
  REWRITE_TAC[LENGTH; NOT_SUC; GSYM NOT_SUC; SUC_INJ; build_ctor_tenv_def; MEM] THEN
  REWRITE_TAC[nsMap_alist_to_ns; MAP] THEN
  MP_TAC(ISPEC `h:mlstring list#mlstring#(mlstring#ast_t list)list` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `tvs:mlstring list` (X_CHOOSE_THEN `r:mlstring#(mlstring#ast_t list)list`
    SUBST1_TAC)) THEN
  MP_TAC(ISPEC `r:mlstring#(mlstring#ast_t list)list` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `tn:mlstring` (X_CHOOSE_THEN `ctors:(mlstring#ast_t list)list`
    SUBST1_TAC)) THEN
  REWRITE_TAC[build_ctor_tenv_def; nsMap_nsAppend; nsMap_alist_to_ns] THEN STRIP_TAC THEN
  BINOP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `SUC k`) THEN
      ASM_REWRITE_TAC[LENGTH; LT_SUC; EL; TL];
      ASM_MESON_TAC[]];
    AP_TERM_TAC THEN REWRITE_TAC[GSYM MAP_REVERSE] THEN AP_TERM_TAC THEN
    REWRITE_TAC[MAP_MAP_o; MAP_EQ_f; FORALL_PAIR_THM; o_THM] THEN CASE_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[PAIR_EQ; MAP_MAP_o; MAP_EQ_f; o_THM] THENL
     [ASM_MESON_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN REWRITE_TAC[LENGTH; LT_0; EL; HD]]]);;

let INFER1AUX_index_EL = prove
 (`!(ids:num list) k.
     ALL_DISTINCT ids /\ k < LENGTH ids
     ==> (THE o ALOOKUP (ZIP ids (COUNT_LIST (LENGTH ids)))) (EL k ids) = k`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[o_THM] THEN
  MP_TAC(ISPECL [`ZIP (ids:num list) (COUNT_LIST (LENGTH ids))`; `k:num`]
                ALOOKUP_ALL_DISTINCT_EL) THEN
  ASM_SIMP_TAC[LENGTH_ZIP; LENGTH_COUNT_LIST; MAP_ZIP; EL_ZIP; EL_COUNT_LIST; THE_DEF]);;

let INFER1AUX_index_BIJ = prove
 (`!(ids:num list).
     ALL_DISTINCT ids
     ==> BIJ (THE o ALOOKUP (ZIP ids (COUNT_LIST (LENGTH ids)))) (set_of_list ids)
             (count (LENGTH ids))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[BIJ; INJ; SURJ; IN_SET_OF_LIST; IN_COUNT; MEM_EXISTS_EL] THEN
  REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[INFER1AUX_index_EL] THEN ASM_MESON_TAC[INFER1AUX_index_EL]);;

let INFER1AUX_check_ctor_tenv_names = prove
 (`!E tdefs tvs tn ctors cn ts t.
     check_ctor_tenv E tdefs /\ MEM (tvs,tn,ctors) tdefs /\ MEM (cn,ts) ctors /\ MEM t ts
     ==> check_type_names E t`,
  REWRITE_TAC[check_ctor_tenv_EVERY; EVERY_MEM; FORALL_PAIR_THM] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[EVERY_MEM; FORALL_PAIR_THM] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[EVERY_MEM] THEN MESON_TAC[]);;

let INFER1AUX_nsAll2_eq_trans = prove
 (`!a b c:(M,N,V)namespace.
     nsAll2 (\i v1 v2. v1 = v2) a b /\ nsAll2 (\i v1 v2. v1 = v2) b c
     ==> nsAll2 (\i v1 v2. v1 = v2) a c`,
  REWRITE_TAC[nsAll2_def; nsSub_def] THEN MESON_TAC[]);;

let INFER1AUX_prims_lt = prove
 (`!f tids n.
     BIJ f tids (count n) /\ prim_tids T tids /\ good_remap f
     ==> ITLIST MAX (CONS Tlist_num (CONS Tbool_num prim_type_nums)) 0 < n`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `Tdouble_num IN tids` ASSUME_TAC THENL
   [UNDISCH_TAC `prim_tids T tids` THEN
    REWRITE_TAC[prim_tids_def; prim_type_nums_def; ALL] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `f Tdouble_num < n` MP_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[BIJ; INJ; IN_COUNT]) THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[INFER1AUX_GR] THEN
  REWRITE_TAC[prim_type_nums_def; ITLIST; typeSystem_Tarray_num_def; typeSystem_Tbool_num_def;
              typeSystem_Tchar_num_def; typeSystem_Texn_num_def; typeSystem_Tfn_num_def;
              typeSystem_Tint_num_def; typeSystem_Tlist_num_def; typeSystem_Tref_num_def;
              typeSystem_Tstring_num_def; typeSystem_Ttup_num_def; typeSystem_Tvector_num_def;
              typeSystem_Tword64_num_def; typeSystem_Tword8_num_def;
              typeSystem_Tword8array_num_def; typeSystem_Tdouble_num_def; MAX] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

let INFER1AUX_MEM_MAP2_tenvT = prove
 (CASE_TERM `!(tdefs:(mlstring list#mlstring#(mlstring#ast_t list)list)list) ids x.
     LENGTH ids = LENGTH tdefs /\
     MEM x (MAP2 (\tdef i. match tdef with
                   (tvs,tn,ctors) -> (tn,(tvs,Tapp (MAP Tvar tvs) i))) tdefs ids)
     ==> ?tvs i. SND x = (tvs,Tapp (MAP Tvar tvs) i) /\ MEM i ids`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `ids:num list` list_CASES) THEN
  REWRITE_TAC[LENGTH; NOT_SUC; GSYM NOT_SUC; SUC_INJ; MAP2; MEM] THEN
  MP_TAC(ISPEC `h:mlstring list#mlstring#(mlstring#ast_t list)list` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `tvs:mlstring list` (X_CHOOSE_THEN `r:mlstring#(mlstring#ast_t list)list`
    SUBST1_TAC)) THEN
  MP_TAC(ISPEC `r:mlstring#(mlstring#ast_t list)list` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `tn:mlstring` (X_CHOOSE_THEN `ctors:(mlstring#ast_t list)list`
    SUBST1_TAC)) THEN
  CASE_REWRITE_TAC[] THEN STRIP_TAC THENL
   [ASM_REWRITE_TAC[SND] THEN MESON_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPECL [`t':num list`; `x:mlstring#mlstring list#t`]) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[]]);;

let INFER1AUX_tenvT_set_tids = prove
 (CASE_TERM `!tids (tdefs:(mlstring list#mlstring#(mlstring#ast_t list)list)list) ids.
     LENGTH ids = LENGTH tdefs
     ==> nsAll (\i p. match p with (ls,t) -> set_tids_subset (tids UNION set_of_list ids) t)
               (alist_to_ns (MAP2 (\tdef i. match tdef with
                   (tvs,tn,ctors) -> (tn,(tvs,Tapp (MAP Tvar tvs) i))) tdefs ids)
                :(mlstring,mlstring,mlstring list#t)namespace)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC nsAll_alist_to_ns THEN
  REWRITE_TAC[EVERY_MEM] THEN X_GEN_TAC `x:mlstring#mlstring list#t` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`tdefs:(mlstring list#mlstring#(mlstring#ast_t list)list)list`;
                `ids:num list`; `x:mlstring#mlstring list#t`] INFER1AUX_MEM_MAP2_tenvT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `x:mlstring#mlstring list#t` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:mlstring` (X_CHOOSE_THEN `v:mlstring list#t` SUBST_ALL_TAC)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SND]) THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[set_tids_subset_def; set_tids_def; SUBSET; IN_INSERT; IN_UNIONS;
              IN_SET_OF_LIST; MEM_MAP; IN_UNION] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MEM_MAP]) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
  ASM_MESON_TAC[set_tids_def; NOT_IN_EMPTY]);;

let INFER1AUX_Dtype_set_tids = prove
 (CASE_TERM `!tids tenv (tdefs:(mlstring list#mlstring#(mlstring#ast_t list)list)list) ids.
     prim_tids T tids /\ set_tids_tenv tids tenv /\ LENGTH ids = LENGTH tdefs /\
     check_ctor_tenv (nsAppend (alist_to_ns (MAP2 (\tdef i. match tdef with
                   (tvs,tn,ctors) -> (tn,(tvs,Tapp (MAP Tvar tvs) i))) tdefs ids))
                               (type_env_t tenv)) tdefs
     ==> set_tids_tenv (tids UNION set_of_list ids)
           (type_env_REC nsEmpty
              (build_ctor_tenv (nsAppend (alist_to_ns (MAP2 (\tdef i. match tdef with
                   (tvs,tn,ctors) -> (tn,(tvs,Tapp (MAP Tvar tvs) i))) tdefs ids))
                                         (type_env_t tenv)) tdefs ids)
              (alist_to_ns (MAP2 (\tdef i. match tdef with
                   (tvs,tn,ctors) -> (tn,(tvs,Tapp (MAP Tvar tvs) i))) tdefs ids)))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[set_tids_tenv_def; type_env_INFO.ri_accessors; nsAll_nsEmpty] THEN
  MP_TAC(SPECL [`tids:num->bool`; `tdefs:(mlstring list#mlstring#(mlstring#ast_t list)list)list`;
                `ids:num list`] INFER1AUX_tenvT_set_tids) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] nsAll_mono) THEN
  EXISTS_TAC (CASE_TERM `\(i:(mlstring,mlstring)id) (p:mlstring list#t list#num).
                        match p with
                        (ls,ts,tid) ->
                          ALL (\t. set_tids_subset (tids UNION set_of_list (ids:num list)) t)
                              ts /\
                          (tid IN tids \/ MEM tid ids)`) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[FORALL_PAIR_THM] THEN CASE_REWRITE_TAC[IN_UNION; IN_SET_OF_LIST];
    MATCH_MP_TAC build_ctor_tenv_type_identities THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC nsAll_nsAppend THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT1 o REWRITE_RULE[set_tids_tenv_def]) THEN
    MATCH_MP_TAC nsAll_mono THEN
    REWRITE_TAC[FORALL_PAIR_THM] THEN CASE_REWRITE_TAC[] THEN
    MESON_TAC[set_tids_subset_mono; SUBSET_UNION]]);;

let INFER1AUX_Dtype_tns = prove
 (CASE_TERM `!ff f tids tenv mt tenvT tenvT' t.
     good_remap ff /\ set_tids_tenv tids tenv /\ (!x. x IN tids ==> ff x = f x) /\
     tenv_equiv (remap_tenv f tenv) mt /\
     check_type_names (nsAppend tenvT (type_env_t tenv)) t /\
     nsMap (\p. match p with (ls,t) -> (ls,ts_tid_rename ff t)) tenvT = tenvT'
     ==> ts_tid_rename ff (type_name_subst (nsAppend tenvT (type_env_t tenv)) t) =
         type_name_subst (nsAppend tenvT' (type_env_t mt)) t`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[ts_tid_rename_type_name_subst; nsMap_nsAppend] THEN
  MATCH_MP_TAC type_name_subst_tenv_equiv THEN MATCH_MP_TAC nsAll2_nsAppend THEN
  REWRITE_TAC[INFER1AUX_nsAll2_eq_refl] THEN
  MATCH_MP_TAC INFER1AUX_nsAll2_eq_trans THEN
  EXISTS_TAC `type_env_t (remap_tenv f tenv)` THEN CONJ_TAC THENL
   [REWRITE_TAC[remap_tenv_def; type_env_INFO.ri_accessors] THEN
    MATCH_MP_TAC INFER1AUX_nsAll2_nsMap_agree THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP INFER1AUX_set_tids_tenv_lookup) THEN
    REWRITE_TAC[FORALL_PAIR_THM] THEN CASE_REWRITE_TAC[PAIR_EQ] THEN
    REPEAT STRIP_TAC THEN RES_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[set_tids_subset_def; SUBSET]) THEN
    REWRITE_TAC[ts_tid_rename_eq_f] THEN ASM_MESON_TAC[];
    UNDISCH_TAC `tenv_equiv (remap_tenv f tenv) mt` THEN SIMP_TAC[tenv_equiv_def]]);;

let INFER1AUX_Dtype_remap = prove
 (CASE_TERM `!f g tids n tenv mt (tdefs:(mlstring list#mlstring#(mlstring#ast_t list)list)list)
     ids.
     good_remap f /\ set_tids_tenv tids tenv /\ tenv_equiv (remap_tenv f tenv) mt /\
     LENGTH ids = LENGTH tdefs /\ prim_tids F (set_of_list ids) /\
     DISJOINT (set_of_list ids) tids /\
     (!k. k < LENGTH ids ==> g (EL k ids) = k) /\
     check_ctor_tenv (nsAppend (alist_to_ns (MAP2 (\tdef i. match tdef with
                   (tvs,tn,ctors) -> (tn,(tvs,Tapp (MAP Tvar tvs) i))) tdefs ids))
                               (type_env_t tenv)) tdefs
     ==> remap_tenv (extend_bij f g (set_of_list ids) n)
           (type_env_REC nsEmpty
              (build_ctor_tenv (nsAppend (alist_to_ns (MAP2 (\tdef i. match tdef with
                   (tvs,tn,ctors) -> (tn,(tvs,Tapp (MAP Tvar tvs) i))) tdefs ids))
                                         (type_env_t tenv)) tdefs ids)
              (alist_to_ns (MAP2 (\tdef i. match tdef with
                   (tvs,tn,ctors) -> (tn,(tvs,Tapp (MAP Tvar tvs) i))) tdefs ids))) =
         type_env_REC nsEmpty
           (build_ctor_tenv (nsAppend (alist_to_ns (MAP2 (\tdef i. match tdef with
                   (tvs,tn,ctors) -> (tn,(tvs,Tapp (MAP Tvar tvs) i))) tdefs
                   (list_of_seq (\i. i + n) (LENGTH tdefs))))
                                      (type_env_t mt)) tdefs
              (list_of_seq (\i. i + n) (LENGTH tdefs)))
           (alist_to_ns (MAP2 (\tdef i. match tdef with
                   (tvs,tn,ctors) -> (tn,(tvs,Tapp (MAP Tvar tvs) i))) tdefs
                   (list_of_seq (\i. i + n) (LENGTH tdefs))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!k. k < LENGTH ids
                    ==> extend_bij f g (set_of_list ids) n (EL k ids) =
                        EL k (list_of_seq (\i. i + n) (LENGTH (tdefs:(mlstring list#mlstring#
                               (mlstring#ast_t list)list)list)))` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[extend_bij_def; IN_SET_OF_LIST] THEN
    SUBGOAL_THEN `MEM (EL k ids) (ids:num list)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_MESON_TAC[MEM_EL]; ALL_TAC] THEN
    SUBGOAL_THEN `k < LENGTH (tdefs:(mlstring list#mlstring#(mlstring#ast_t list)list)list)`
      ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[EL_LIST_OF_SEQ] THEN REWRITE_TAC[ADD_SYM];
    ALL_TAC] THEN
  SUBGOAL_THEN `good_remap (extend_bij f g (set_of_list (ids:num list)) n)` ASSUME_TAC THENL
   [MATCH_MP_TAC good_remap_extend_bij THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN (CASE_TERM
   `nsMap (\p. match p with (ls,t) -> (ls,ts_tid_rename (extend_bij f g (set_of_list ids) n) t))
          (alist_to_ns (MAP2 (\tdef i. match tdef with
                   (tvs,tn,ctors) -> (tn,(tvs,Tapp (MAP Tvar tvs) i)))
                   (tdefs:(mlstring list#mlstring#(mlstring#ast_t list)list)list) ids)
           :(mlstring,mlstring,mlstring list#t)namespace) =
    alist_to_ns (MAP2 (\tdef i. match tdef with
                   (tvs,tn,ctors) -> (tn,(tvs,Tapp (MAP Tvar tvs) i))) tdefs
                   (list_of_seq (\i. i + n) (LENGTH tdefs)))`)
    ASSUME_TAC THENL
   [MATCH_MP_TAC INFER1AUX_nsMap_tenvT THEN ASM_REWRITE_TAC[LENGTH_LIST_OF_SEQ]; ALL_TAC] THEN
  REWRITE_TAC[remap_tenv_def; type_env_INFO.ri_accessors; nsMap_nsEmpty;
              injectivity "type_env"] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC INFER1AUX_nsMap_build_ctor_tenv THEN
  ASM_REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC INFER1AUX_Dtype_tns THEN
  MAP_EVERY EXISTS_TAC [`f:num->num`; `tids:num->bool`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[extend_bij_def] THEN
    UNDISCH_TAC `DISJOINT (set_of_list ids) (tids:num->bool)` THEN
    REWRITE_TAC[IN_DISJOINT] THEN MESON_TAC[];
    MATCH_MP_TAC INFER1AUX_check_ctor_tenv_names THEN ASM_MESON_TAC[]]);;

let INFER1AUX_TDC_DTYPE_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> try fst(dest_var(lhs(concl th))) = "tenvT"
                                                 with Failure _ -> false)) THEN
  SUBGOAL_THEN `CARD (set_of_list (type_identities:num list)) = LENGTH (tdefs:(mlstring list#
                  mlstring#(mlstring#ast_t list)list)list)` SUBST1_TAC THENL
   [ASM_MESON_TAC[ALL_DISTINCT_CARD_LIST_TO_SET]; ALL_TAC] THEN
  SUBGOAL_THEN `prim_tids F (set_of_list (type_identities:num list))` ASSUME_TAC THENL
   [UNDISCH_TAC `DISJOINT (set_of_list type_identities)
                   (set_of_list (CONS Tlist_num (CONS Tbool_num prim_type_nums)))` THEN
    REWRITE_TAC[prim_tids_def; IN_DISJOINT; EVERY_MEM; IN_SET_OF_LIST] THEN MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `THE o ALOOKUP (ZIP (type_identities:num list) (COUNT_LIST (LENGTH type_identities)))` THEN
  EXISTS_TAC (CASE_TERM `type_env_REC nsEmpty
     (build_ctor_tenv (nsAppend (alist_to_ns (MAP2 (\tdef i. match tdef with
                   (tvs,tn,ctors) -> (tn,(tvs,Tapp (MAP Tvar tvs) i)))
                   (tdefs:(mlstring list#mlstring#(mlstring#ast_t list)list)list)
                   (list_of_seq (\i. i + n) (LENGTH tdefs))))
                                (type_env_t mapped_tenv)) tdefs
              (list_of_seq (\i. i + n) (LENGTH tdefs)))
     (alist_to_ns (MAP2 (\tdef i. match tdef with
                   (tvs,tn,ctors) -> (tn,(tvs,Tapp (MAP Tvar tvs) i))) tdefs
                   (list_of_seq (\i. i + n) (LENGTH tdefs))))`) THEN
  ASM_REWRITE_TAC[FINITE_SET_OF_LIST] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC INFER1AUX_Dtype_set_tids THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `LENGTH (type_identities:num list) = LENGTH (tdefs:(mlstring
             list#mlstring#(mlstring#ast_t list)list)list)` THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
    MATCH_MP_TAC INFER1AUX_index_BIJ THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC(el 3 (CONJUNCTS type_d_canon_rules)) THEN REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC INFER1AUX_prims_lt THEN
      MAP_EVERY EXISTS_TAC [`f:num->num`; `tids:num->bool`] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC check_ctor_tenv_change_tenvT THEN
    EXISTS_TAC (CASE_TERM `nsAppend (alist_to_ns (MAP2 (\tdef i. match tdef with
                   (tvs,tn,ctors) -> (tn,(tvs,Tapp (MAP Tvar tvs) i)))
                   (tdefs:(mlstring list#mlstring#(mlstring#ast_t list)list)list)
                   type_identities)) (type_env_t tenv)`) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`tdefs:(mlstring list#mlstring#(mlstring#ast_t list)list)list`;
                   `type_identities:num list`;
                   `list_of_seq (\i. i + n) (LENGTH (tdefs:(mlstring list#mlstring#
                      (mlstring#ast_t list)list)list))`;
                   `type_env_t tenv`; `type_env_t mapped_tenv`] INFER1AUX_tenvT_lookup_FST) THEN
    ASM_REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN ANTS_TAC THENL
     [MATCH_MP_TAC INFER1AUX_mapped_t_FST THEN EXISTS_TAC `f:num->num` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(ASSUME_TAC o MATCH_MP INFER1AUX_check_type_names_FST) THEN
    REWRITE_TAC[EVERY_MEM; FORALL_PAIR_THM] THEN CASE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[EVERY_MEM];
    MP_TAC(ISPECL [`f:num->num`;
                   `THE o ALOOKUP (ZIP (type_identities:num list)
                                       (COUNT_LIST (LENGTH type_identities)))`;
                   `tids:num->bool`; `n:num`; `tenv:type_env`; `mapped_tenv:type_env`;
                   `tdefs:(mlstring list#mlstring#(mlstring#ast_t list)list)list`;
                   `type_identities:num list`] INFER1AUX_Dtype_remap) THEN
    ASM_SIMP_TAC[INFER1AUX_index_EL] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[tenv_equiv_refl]];;

(* For any type_d, prove that the canonical type identifier strategy        *)
(* succeeds.  f,g are maps from the identifiers used in type_d into the     *)
(* ones used by type_d_canon (HOL4 comment: TODO: do we actually need the   *)
(* bijection??)                                                             *)
let type_d_type_d_canon = prove
 (`(!extra_checks tenv d ids tenv'.
      type_d extra_checks tenv d ids tenv'
      ==> !tids f n mapped_tenv.
            extra_checks = T /\ DISJOINT ids tids /\ set_tids_tenv tids tenv /\
            BIJ f tids (count n) /\ prim_tids T tids /\ good_remap f /\
            tenv_equiv (remap_tenv f tenv) mapped_tenv
            ==> ?g mapped_tenv'.
                  set_tids_tenv (tids UNION ids) tenv' /\ prim_tids F ids /\ FINITE ids /\
                  BIJ g ids (count (CARD ids)) /\
                  type_d_canon n mapped_tenv d (CARD ids) mapped_tenv' /\
                  tenv_equiv (remap_tenv (extend_bij f g ids n) tenv') mapped_tenv') /\
   (!extra_checks tenv ds ids tenv'.
      type_ds extra_checks tenv ds ids tenv'
      ==> !tids f n mapped_tenv.
            extra_checks = T /\ DISJOINT ids tids /\ set_tids_tenv tids tenv /\
            BIJ f tids (count n) /\ prim_tids T tids /\ good_remap f /\
            tenv_equiv (remap_tenv f tenv) mapped_tenv
            ==> ?g mapped_tenv'.
                  set_tids_tenv (tids UNION ids) tenv' /\ prim_tids F ids /\ FINITE ids /\
                  BIJ g ids (count (CARD ids)) /\
                  type_ds_canon n mapped_tenv ds (CARD ids) mapped_tenv' /\
                  tenv_equiv (remap_tenv (extend_bij f g ids n) tenv') mapped_tenv')`,
  MATCH_MP_TAC type_d_strongind THEN REPEAT CONJ_TAC THENL
   [INFER1AUX_TDC_DLET_POLY_TAC; INFER1AUX_TDC_DLET_MONO_TAC; INFER1AUX_TDC_DLETREC_TAC;
    INFER1AUX_TDC_DTYPE_TAC; INFER1AUX_TDC_DTABBREV_TAC; INFER1AUX_TDC_DEXN_TAC;
    INFER1AUX_TDC_DMOD_TAC; INFER1AUX_TDC_DLOCAL_TAC; INFER1AUX_TDC_NIL_TAC;
    INFER1AUX_TDC_CONS_TAC]);;

(* n.b. proof almost entirely copied from type_d_tenv_ok_helper *)
let type_d_canon_tenv_ok = prove
 (`(!check tenv d tdecs tenv'.
      type_d_canon check tenv d tdecs tenv' ==> tenv_ok tenv ==> tenv_ok tenv') /\
   (!check tenv d tdecs tenv'.
      type_ds_canon check tenv d tdecs tenv' ==> tenv_ok tenv ==> tenv_ok tenv')`,
  MATCH_MP_TAC type_d_canon_ind THEN RW[tenv_ctor_ok_def; tenvLift_def] THENL
   [(* Dlet (value) *)
    MATCH_MP_TAC TPROPSAUX_tenv_ok_tenv_add_tvs THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP (CONJUNCT1 type_p_freevars) o
      check (fun th -> can (term_match [] `type_p a b c d e`) (concl th))) THEN SIMP_TAC[];
    (* Dlet *)
    MATCH_MP_TAC TPROPSAUX_tenv_ok_tenv_add_tvs THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP (CONJUNCT1 type_p_freevars) o
      check (fun th -> can (term_match [] `type_p a b c d e`) (concl th))) THEN SIMP_TAC[];
    (* Dletrec *)
    MATCH_MP_TAC TPROPSAUX_tenv_ok_tenv_add_tvs THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP (CONJUNCT2 (CONJUNCT2 type_e_freevars)) o
      check (fun th -> can (term_match [] `type_funs a b c d`) (concl th))) THEN
    REWRITE_TAC[num_tvs_bind_var_list; bind_tvar_rewrites; num_tvs_def; ADD_CLAUSES] THEN
    DISCH_THEN MATCH_MP_TAC THEN FS[tenv_ok_def] THEN
    MATCH_MP_TAC tenv_val_exp_ok_bvl_funs THEN
    REWRITE_TAC[bind_tvar_rewrites; tenv_val_exp_ok_def] THEN ASM_MESON_TAC[];
    (* Dtype *)
    REWRITE_TAC[tenv_ok_def; type_env_INFO.ri_accessors; tenv_val_ok_nsEmpty;
                TPROPSAUX_tenv_abbrev_ok_tdefs] THEN
    MATCH_MP_TAC check_ctor_tenv_ok THEN ASM_REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN
    MATCH_MP_TAC tenv_abbrev_ok_merge THEN REWRITE_TAC[TPROPSAUX_tenv_abbrev_ok_tdefs] THEN
    FS[tenv_ok_def];
    (* Dtabbrev *)
    FS[tenv_ok_def; tenv_abbrev_ok_def; nsAll_nsSing] THEN CASE_REWRITE_TAC[] THEN
    MATCH_MP_TAC check_freevars_type_name_subst THEN ASM_REWRITE_TAC[tenv_abbrev_ok_def];
    (* Dexn *)
    FS[tenv_ok_def; tenv_ctor_ok_def; nsAll_nsSing] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[EVERY_MAP] THEN FS[EVERY_MEM] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC check_freevars_type_name_subst THEN ASM_SIMP_TAC[tenv_abbrev_ok_def];
    (* Dmod *)
    FS[tenv_ok_def; tenv_val_ok_def; tenv_ctor_ok_def; tenv_abbrev_ok_def; nsAll_nsLift] THEN
    ASM_REWRITE_TAC[ETA_AX];
    (* Dlocal *)
    ASM_MESON_TAC[extend_dec_tenv_ok];
    (* type_ds *)
    ASM_MESON_TAC[extend_dec_tenv_ok]]);;
