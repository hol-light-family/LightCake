(* ========================================================================= *)
(* weakening: port of HOL4 semantics/proofs/weakeningScript.sml              *)
(* (CakeML v3479).  Weakening lemmas used in type soundness.                 *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/typeSystem.ml";;
needs "semantics/proofs/typeSysProps.ml";;
needs "semantics/proofs/namespaceProps.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/proofs/typeSoundInvariants.ml";;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Notes on the rendering:                                                   *)
(* - As in typeSysProps: tenv.v is type_env_v tenv, EVERY is ALL, LIST_REL  *)
(*   is ALL2, paired lambdas (\(a,b). t) are (\p. match p with (a,b) -> t);  *)
(*   variables that a HOL4 statement quantifies without using them get the  *)
(*   type their name suggests; variables it leaves free stay free.          *)
(* - weakCT is polymorphic (as in HOL4: its definition has no type).        *)
(* - HOL4's local remove_lambda_prod is weakening_remove_lambda_prod, the   *)
(*   same theorem as typeSysProps' remove_lambda_prod.                       *)
(* - TPROPSAUX_ names are local helpers.                                     *)
(* ------------------------------------------------------------------------- *)

let weak_tenvE_def = cake_def
  `weak_tenvE (tenv:tenv_val_exp) (tenv':tenv_val_exp) <=>
     num_tvs tenv >= num_tvs tenv' /\
     (!n inc tvs t.
        tveLookup n inc tenv' = SOME (tvs,t) <=> tveLookup n inc tenv = SOME (tvs,t))`;;

let weakS_def = cake_def
  `weakS (tenvS:tenv_store) (tenvS':tenv_store) <=> tenvS' SUBMAP tenvS`;;

let weak_tenvE_refl = prove
 (`!tenvE. weak_tenvE tenvE tenvE`,
  RW[weak_tenvE_def] THEN ARITH_TAC);;

let weak_tenv_refl = prove
 (`!tenv. tenv_val_ok (type_env_v tenv) ==> weak_tenv tenv tenv`,
  RW[weak_tenv_def] THENL
   [RW[nsSub_def; tscheme_inst2_def] THEN
    FS[tenv_val_ok_def] THEN DRULE nsLookup_nsAll THEN DISCH_THEN DRULE THEN
    SPEC_TAC(`v1:num#t`,`v1:num#t`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
    CASE_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[tscheme_inst_def] THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `MAP Tvar_db (COUNT_LIST p1)` THEN
    ASM_SIMP_TAC[LENGTH_MAP; LENGTH_COUNT_LIST; deBruijn_subst_id] THEN
    REWRITE_TAC[EVERY_MAP; GSYM ALL_MEM; MEM_COUNT_LIST; check_freevars_def];
    RW[nsSub_def]]);;

let weakS_refl = prove
 (`!tenvS. weakS tenvS tenvS`,
  RW[weakS_def; SUBMAP_REFL]);;

let weakS_bind = prove
 (`!l t tenvS. FLOOKUP tenvS l = NONE ==> weakS (tenvS |+ (l,t)) tenvS`,
  RW[weakS_def; SUBMAP_DEF; FDOM_FUPDATE; IN_INSERT; FAPPLY_FUPDATE_THM; flookup_thm] THEN
  ASM_MESON_TAC[]);;

let weak_tenvE_freevars = prove
 (`!tenv tenv' tvs t.
     weak_tenvE tenv' tenv /\ check_freevars (num_tvs tenv) tvs t
     ==> check_freevars (num_tvs tenv') tvs t`,
  RW[weak_tenvE_def] THEN ASM_MESON_TAC[check_freevars_add]);;

let weak_tenvE_bind = prove
 (`!tenv tenv' n tvs t.
     weak_tenvE tenv' tenv
     ==> weak_tenvE (Bind_name n tvs t tenv') (Bind_name n tvs t tenv)`,
  RW[weak_tenvE_def; tveLookup_def; num_tvs_def] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

let weak_tenvE_opt_bind = prove
 (`!tenv tenv' n tvs t.
     weak_tenvE tenv' tenv
     ==> weak_tenvE (opt_bind_name n tvs t tenv') (opt_bind_name n tvs t tenv)`,
  REPEAT GEN_TAC THEN CASES_ON `n:mlstring option` THEN
  REWRITE_TAC[opt_bind_name_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[weak_tenvE_bind]);;

let weak_tenvE_bind_tvar = prove
 (`!tenv tenv' tvs.
     weak_tenvE tenv' tenv ==> weak_tenvE (bind_tvar tvs tenv') (bind_tvar tvs tenv)`,
  RW[weak_tenvE_def; bind_tvar_rewrites] THEN ASM_ARITH_TAC);;

let weak_tenvE_bind_tvar2 = prove
 (`!tenv tenv' (n:mlstring) tvs (t:t).
     tenv_val_exp_ok tenv /\ num_tvs tenv = 0 /\ weak_tenvE tenv' tenv
     ==> weak_tenvE (bind_tvar tvs tenv') (bind_tvar 0 tenv)`,
  RW[weak_tenvE_def; bind_tvar_rewrites] THEN TRY ARITH_TAC THEN
  ASM_MESON_TAC[tveLookup_no_tvs]);;

let weak_tenvE_bind_var_list = prove
 (`!bindings tenvE tenvE' (n:mlstring) tvs (t:t).
     weak_tenvE tenvE' tenvE
     ==> weak_tenvE (bind_var_list tvs bindings tenvE') (bind_var_list tvs bindings tenvE)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[bind_var_list_def] THEN
  SPEC_TAC(`h:mlstring#t`,`h:mlstring#t`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  REWRITE_TAC[bind_var_list_def] THEN ASM_MESON_TAC[weak_tenvE_bind]);;

let eLookupC_weak = prove
 (`!cn tenv tenv' tvs ts tn.
     weak_tenv tenv' tenv /\ nsLookup (type_env_c tenv) cn = SOME (tvs,ts,tn)
     ==> nsLookup (type_env_c tenv') cn = SOME (tvs,ts,tn)`,
  RW[weak_tenv_def; nsSub_def] THEN RES_TAC THEN FS[] THEN ASM_MESON_TAC[]);;

let eLookupV_weak = prove
 (`!n tenv tenv' tvs t.
     weak_tenv tenv' tenv /\ nsLookup (type_env_v tenv) n = SOME (tvs,t)
     ==> ?tvs' t'. nsLookup (type_env_v tenv') n = SOME (tvs',t') /\
                   tscheme_inst (tvs,t) (tvs',t')`,
  RW[weak_tenv_def; nsSub_def; tscheme_inst2_def] THEN
  ASM_MESON_TAC[PAIR]);;

let weak_def = cake_def
  `weak (tenv':type_env) (tenv:type_env) <=>
     type_env_t tenv' = type_env_t tenv /\ weak_tenv tenv' tenv`;;

let type_p_weakening = prove
 (`(!tvs tenv p t bindings. type_p tvs tenv p t bindings
      ==> !tenv' tvs'. tvs' >= tvs /\ weak tenv' tenv
                       ==> type_p tvs' tenv' p t bindings) /\
   (!tvs tenv ps ts bindings. type_ps tvs tenv ps ts bindings
      ==> !tenv' tvs'. tvs' >= tvs /\ weak tenv' tenv
                       ==> type_ps tvs' tenv' ps ts bindings)`,
  MATCH_MP_TAC type_p_ind THEN RW[] THEN ONCE_REWRITE_TAC[type_p_cases] THEN
  RW[] THEN FS[EVERY_MEM; weak_def] THEN
  ASM_MESON_TAC[check_freevars_add; eLookupC_weak]);;

let TPROPSAUX_option_ext = prove
 (`!x y:A option. x = y <=> (!v. x = SOME v <=> y = SOME v)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `x:A option` (cases "option")) THEN
  STRUCT_CASES_TAC (ISPEC `y:A option` (cases "option")) THEN
  REWRITE_TAC[option_DISTINCT; option_INJ] THEN MESON_TAC[]);;

let TPROPSAUX_weak_lookup_varE = prove
 (`!n tenvE tenvE'. weak_tenvE tenvE' tenvE ==> lookup_varE n tenvE' = lookup_varE n tenvE`,
  REPEAT GEN_TAC THEN CASES_ON `n:(mlstring,mlstring)id` THEN
  REWRITE_TAC[lookup_varE_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[weak_tenvE_def] THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[TPROPSAUX_option_ext] THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  ASM_REWRITE_TAC[]);;

let TPROPSAUX_weakening_var = prove
 (`!n tenv tenv' tenvE tenvE' targs t.
     weak_tenv tenv' tenv /\ weak_tenvE tenvE' tenvE /\
     ALL (check_freevars (num_tvs tenvE) []) targs /\
     lookup_var n tenvE tenv = SOME (LENGTH targs,t)
     ==> ?t' targs'. deBruijn_subst 0 targs t = deBruijn_subst 0 targs' t' /\
                     ALL (check_freevars (num_tvs tenvE') []) targs' /\
                     lookup_var n tenvE' tenv' = SOME (LENGTH targs',t')`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ALL (check_freevars (num_tvs tenvE') []) (targs:t list)` ASSUME_TAC THENL
   [FS[EVERY_MEM] THEN ASM_MESON_TAC[weak_tenvE_freevars]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o SPEC `n:(mlstring,mlstring)id` o
              MATCH_MP TPROPSAUX_weak_lookup_varE) THEN
  UNDISCH_TAC `lookup_var n tenvE tenv = SOME (LENGTH (targs:t list),t)` THEN
  ASM_REWRITE_TAC[lookup_var_def] THEN
  CASES_ON `lookup_varE n tenvE` THEN CASE_REWRITE_TAC[] THENL
   [DISCH_TAC THEN
    MP_TAC(SPECL [`n:(mlstring,mlstring)id`; `tenv:type_env`; `tenv':type_env`;
                  `LENGTH (targs:t list)`; `t:t`] eLookupV_weak) THEN
    ASM_REWRITE_TAC[tscheme_inst_def] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`t':t`; `MAP (deBruijn_subst 0 targs) (subst:t list)`] THEN
    ASM_REWRITE_TAC[LENGTH_MAP] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        can (term_match [] `deBruijn_subst 0 s x = y`) (concl th))) THEN
      MP_TAC(SPECL [`t':t`; `0`; `subst:t list`; `targs:t list`; `0`]
        (CONJUNCT1 deBruijn_subst2)) THEN
      ASM_REWRITE_TAC[deBruijn_inc0];
      REWRITE_TAC[EVERY_MAP] THEN
      UNDISCH_TAC `ALL (check_freevars (LENGTH (targs:t list)) []) (subst:t list)` THEN
      MATCH_MP_TAC MONO_ALL THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
      MATCH_MP_TAC deBruijn_subst_check_freevars2 THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[option_INJ] THEN DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC [`t:t`; `targs:t list`] THEN ASM_REWRITE_TAC[]]);;

let type_e_weakening_lem = prove
 (`(!tenv tenvE e t. type_e tenv tenvE e t
      ==> !tenv' tenvE'. weak tenv' tenv /\ weak_tenvE tenvE' tenvE
                         ==> type_e tenv' tenvE' e t) /\
   (!tenv tenvE es ts. type_es tenv tenvE es ts
      ==> !tenv' tenvE'. weak tenv' tenv /\ weak_tenvE tenvE' tenvE
                         ==> type_es tenv' tenvE' es ts) /\
   (!tenv tenvE funs bindings. type_funs tenv tenvE funs bindings
      ==> !tenv' tenvE'. weak tenv' tenv /\ weak_tenvE tenvE' tenvE
                         ==> type_funs tenv' tenvE' funs bindings)`,
  let PES_TAC p e =
    FIRST_X_ASSUM(MP_TAC o SPECL [p; e]) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    EXISTS_TAC `bindings:(mlstring#t)list` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [FIRST_ASSUM(MP_TAC o SPECL [`tenv':type_env`; `num_tvs tenvE'`] o
        MATCH_MP (CONJUNCT1 type_p_weakening) o
        check (fun th -> can (term_match [] `type_p a b c d e`) (concl th))) THEN
      ASM_REWRITE_TAC[weak_def] THEN DISCH_THEN MATCH_MP_TAC THEN FS[weak_tenvE_def];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC weak_tenvE_bind_var_list THEN ASM_REWRITE_TAC[]] in
  MATCH_MP_TAC type_e_ind THEN RW[weak_def] THEN ONCE_REWRITE_TAC[type_e_cases] THEN
  RW[] THENL
   [(* Raise *)
    ASM_MESON_TAC[weak_tenvE_freevars];
    (* Handle *)
    PES_TAC `p:pat` `e':exp`;
    (* Con (SOME cn) *)
    MAP_EVERY EXISTS_TAC [`tvs:mlstring list`; `ts:t list`] THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [FS[EVERY_MEM] THEN ASM_MESON_TAC[weak_tenvE_freevars];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[eLookupC_weak]];
    (* Var *)
    MATCH_MP_TAC TPROPSAUX_weakening_var THEN ASM_MESON_TAC[];
    (* Fun: the argument type *)
    ASM_MESON_TAC[weak_tenvE_freevars];
    (* Fun: the body *)
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC weak_tenvE_bind THEN ASM_REWRITE_TAC[];
    (* App *)
    EXISTS_TAC `ts:t list` THEN ASM_MESON_TAC[weak_tenvE_freevars];
    (* Mat *)
    EXISTS_TAC `t1:t` THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`p0:pat`; `e0:exp`] THEN DISCH_TAC THEN
      PES_TAC `p0:pat` `e0:exp`];
    (* Let *)
    EXISTS_TAC `t1:t` THEN CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC weak_tenvE_opt_bind THEN ASM_REWRITE_TAC[];
    (* Letrec *)
    EXISTS_TAC `bindings:(mlstring#t)list` THEN CONJ_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC weak_tenvE_bind_var_list THEN ASM_REWRITE_TAC[];
    (* type_funs: the function type *)
    ASM_MESON_TAC[weak_tenvE_freevars];
    (* type_funs: the body *)
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC weak_tenvE_bind THEN ASM_REWRITE_TAC[]]);;

let type_e_weakening = prove
 (`(!tenv tenvE e t tenv' tenvE'.
      type_e tenv tenvE e t /\ weak tenv' tenv /\ weak_tenvE tenvE' tenvE
      ==> type_e tenv' tenvE' e t) /\
   (!tenv tenvE es ts tenv' tenvE'.
      type_es tenv tenvE es ts /\ weak tenv' tenv /\ weak_tenvE tenvE' tenvE
      ==> type_es tenv' tenvE' es ts) /\
   (!tenv tenvE funs bindings tenv' tenvE'.
      type_funs tenv tenvE funs bindings /\ weak tenv' tenv /\ weak_tenvE tenvE' tenvE
      ==> type_funs tenv' tenvE' funs bindings)`,
  MESON_TAC[type_e_weakening_lem]);;

let gt_0 = prove
 (`!x:num. x >= 0`,
  ARITH_TAC);;

let weakCT_def = cake_def
  `weakCT (cenv_impl:(A,B)fmap) (cenv_spec:(A,B)fmap) <=> cenv_spec SUBMAP cenv_impl`;;

let weak_ctMap_lookup = prove
 (`!(ctMap:(A,B#C)fmap) ctMap' tvs ts stamp.
     weakCT ctMap' ctMap /\ FLOOKUP ctMap stamp = SOME (tvs,ts)
     ==> FLOOKUP ctMap' stamp = SOME (tvs,ts)`,
  RW[weakCT_def] THEN ASM_MESON_TAC[FLOOKUP_SUBMAP]);;

let weakCT_refl = prove
 (`!ctMap:(A,B)fmap. weakCT ctMap ctMap`,
  RW[weakCT_def; SUBMAP_REFL]);;

let weakCT_trans = prove
 (`weakCT (C1:(A,B)fmap) C2 /\ weakCT C2 C3 ==> weakCT C1 C3`,
  RW[weakCT_def] THEN ASM_MESON_TAC[SUBMAP_TRANS]);;

let disjoint_env_weakCT = prove
 (`!ctMap ctMap':(A,B)fmap.
     DISJOINT (FDOM ctMap') (FDOM ctMap) ==> weakCT (FUNION ctMap' ctMap) ctMap`,
  RW[weakCT_def] THEN ASM_MESON_TAC[SUBMAP_FUNION_ID]);;

let weakCT2 = prove
 (`!ctMap ctMap':(A,B)fmap. weakCT (FUNION ctMap' ctMap) ctMap'`,
  RW[weakCT_def; SUBMAP_FUNION_ID]);;

let type_tenv_ctor_weakening = prove
 (`!ctMap (tenvC:(M,N,mlstring list#t list#num)namespace)
          (envC:(M,N,num#stamp)namespace) ctMap'.
     weakCT ctMap' ctMap /\ nsAll2 (type_ctor ctMap) envC tenvC
     ==> nsAll2 (type_ctor ctMap') envC tenvC`,
  RW[weakCT_def; weakS_def] THEN TPROPSAUX_NSALL2_MONO_TAC THEN
  REWRITE_TAC[FORALL_PAIR_THM; type_ctor_def] THEN ASM_MESON_TAC[FLOOKUP_SUBMAP]);;

let type_tenv_val_weakening_lemma = prove
 (CASE_TERM `!ctMap tenvS (tenvV:(M,N,num#t)namespace) (envV:(M,N,v)namespace) ctMap' tenvS'.
     weakCT ctMap' ctMap /\ weakS tenvS' tenvS /\
     nsAll2 (\i v p. match p with
                       (tvs,t) -> !tvs' ctMap' tenvS'.
                                    (tvs = 0 \/ tvs = tvs') /\
                                    weakCT ctMap' ctMap /\ weakS tenvS' tenvS
                                    ==> type_v tvs' ctMap' tenvS' v t)
            envV tenvV
     ==> nsAll2 (\i v p. match p with (tvs,t) -> type_v tvs ctMap' tenvS' v t) envV tenvV`,
  REPEAT STRIP_TAC THEN TPROPSAUX_NSALL2_MONO_TAC THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN CASE_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* HOL4: remove_lambda_prod (local; the same as typeSysProps' one) *)
let weakening_remove_lambda_prod = remove_lambda_prod;;

let type_v_weakening = prove
 (`!tvs ctMap tenvS v t. type_v tvs ctMap tenvS v t
     ==> !tvs' ctMap' tenvS'.
           (tvs = 0 \/ tvs = tvs') /\ weakCT ctMap' ctMap /\ weakS tenvS' tenvS
           ==> type_v tvs' ctMap' tenvS' v t`,
  let ALL2_MONO_TAC =
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      is_comb (concl th) &&
      fst(strip_comb(concl th)) = `ALL2:(v->t->bool)->v list->t list->bool`)) THEN
    MATCH_MP_TAC MONO_ALL2 THEN BETA_TAC THEN ASM_MESON_TAC[] in
  let ALL_FV_TAC =
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      is_comb (concl th) &&
      fst(strip_comb(concl th)) = `ALL:(t->bool)->t list->bool`)) THEN
    MATCH_MP_TAC MONO_ALL THEN ASM_MESON_TAC[check_freevars_add; gt_0] in
  let CONV_CASE_TAC =
    MAP_EVERY EXISTS_TAC [`tvs':mlstring list`; `ts:t list`] THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN
    FIRST [ASM_MESON_TAC[weak_ctMap_lookup]; ALL2_MONO_TAC; ALL_FV_TAC] in
  let CLOS_COMMON_TAC =
    REPEAT CONJ_TAC THEN
    TRY (FIRST [MATCH_MP_TAC type_tenv_ctor_weakening THEN ASM_MESON_TAC[];
                MATCH_MP_TAC type_tenv_val_weakening_lemma THEN ASM_MESON_TAC[]]) in
  let WEAK_REFL_TAC =
    REWRITE_TAC[weak_def] THEN MATCH_MP_TAC weak_tenv_refl THEN FS[tenv_ok_def] in
  let LOC_TAC = FS[weakS_def] THEN ASM_MESON_TAC[FLOOKUP_SUBMAP] in
  let VEC_TAC =
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      is_comb (concl th) && fst(strip_comb(concl th)) = `ALL:(v->bool)->v list->bool`)) THEN
    MATCH_MP_TAC MONO_ALL THEN BETA_TAC THEN ASM_MESON_TAC[] in
  MATCH_MP_TAC type_v_ind THEN RW[] THEN ONCE_REWRITE_TAC[type_v_cases] THEN RW[] THENL
   [(* Conv (SOME stamp), from tvs = 0 *)
    CONV_CASE_TAC;
    (* Conv (SOME stamp) *)
    CONV_CASE_TAC;
    (* Conv NONE, from tvs = 0 *)
    ALL2_MONO_TAC;
    (* Conv NONE *)
    ALL2_MONO_TAC;
    (* Closure, from tvs = 0 *)
    MAP_EVERY EXISTS_TAC [`tenv:type_env`; `tenvE:tenv_val_exp`] THEN ASM_REWRITE_TAC[] THEN
    CLOS_COMMON_TAC THENL
     [ASM_MESON_TAC[check_freevars_add; gt_0];
      MATCH_MP_TAC (CONJUNCT1 type_e_weakening) THEN
      MAP_EVERY EXISTS_TAC [`tenv:type_env`; `Bind_name n 0 t1 (bind_tvar 0 tenvE)`] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [WEAK_REFL_TAC;
        MATCH_MP_TAC weak_tenvE_bind THEN MATCH_MP_TAC weak_tenvE_bind_tvar2 THEN
        ASM_REWRITE_TAC[weak_tenvE_refl]]];
    (* Closure *)
    MAP_EVERY EXISTS_TAC [`tenv:type_env`; `tenvE:tenv_val_exp`] THEN ASM_REWRITE_TAC[] THEN
    CLOS_COMMON_TAC;
    (* Recclosure, from tvs = 0 *)
    MAP_EVERY EXISTS_TAC [`tenv:type_env`; `tenvE:tenv_val_exp`;
                          `bindings:(mlstring#t)list`] THEN
    ASM_REWRITE_TAC[] THEN CLOS_COMMON_TAC THEN
    MATCH_MP_TAC (CONJUNCT2 (CONJUNCT2 type_e_weakening)) THEN
    MAP_EVERY EXISTS_TAC [`tenv:type_env`; `bind_var_list 0 bindings (bind_tvar 0 tenvE)`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [WEAK_REFL_TAC;
      MATCH_MP_TAC weak_tenvE_bind_var_list THEN MATCH_MP_TAC weak_tenvE_bind_tvar2 THEN
      ASM_REWRITE_TAC[weak_tenvE_refl]];
    (* Recclosure *)
    MAP_EVERY EXISTS_TAC [`tenv:type_env`; `tenvE:tenv_val_exp`;
                          `bindings:(mlstring#t)list`] THEN
    ASM_REWRITE_TAC[] THEN CLOS_COMMON_TAC;
    (* Loc *)
    LOC_TAC; LOC_TAC; LOC_TAC; LOC_TAC; LOC_TAC; LOC_TAC;
    (* Vectorv *)
    VEC_TAC; VEC_TAC]);;

let type_all_env_weakening = prove
 (`!ctMap tenvS tenv env ctMap' tenvS'.
     weakCT ctMap' ctMap /\ weakS tenvS' tenvS /\ type_all_env ctMap tenvS env tenv
     ==> type_all_env ctMap' tenvS' env tenv`,
  RW[type_all_env_def] THENL
   [ASM_MESON_TAC[type_tenv_ctor_weakening];
    TPROPSAUX_NSALL2_MONO_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN CASE_REWRITE_TAC[] THEN
    ASM_MESON_TAC[type_v_weakening]]);;

let type_sv_weakening = prove
 (`!ctMap tenvS st sv ctMap' tenvS'.
     type_sv ctMap tenvS sv st /\ weakCT ctMap' ctMap /\ weakS tenvS' tenvS
     ==> type_sv ctMap' tenvS' sv st`,
  REPEAT GEN_TAC THEN CASES_ON `sv:v store_v` THEN CASES_ON `st:store_t` THEN
  RW[type_sv_def] THENL
   [ASM_MESON_TAC[type_v_weakening];
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_comb (concl th) &&
      fst(strip_comb(concl th)) = `ALL:(v->bool)->v list->bool`)) THEN
    MATCH_MP_TAC MONO_ALL THEN BETA_TAC THEN ASM_MESON_TAC[type_v_weakening]]);;

(* HOL4 names the store argument of type_s tenvS and the store typing st *)
let type_s_weakening = prove
 (`!ctMap tenvS st ctMap'.
     type_s ctMap tenvS st /\ weakCT ctMap' ctMap ==> type_s ctMap' tenvS st`,
  RW[type_s_def] THEN ASM_MESON_TAC[type_sv_weakening; weakS_refl]);;

let weak_tenv_extend_dec_tenv = prove
 (`!tenv1 tenv2 tenv3.
     tenv_val_ok (type_env_v tenv1) /\ weak_tenv tenv2 tenv3
     ==> weak_tenv (extend_dec_tenv tenv1 tenv2) (extend_dec_tenv tenv1 tenv3)`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP weak_tenv_refl) THEN
  UNDISCH_TAC `weak_tenv tenv2 tenv3` THEN
  REWRITE_TAC[weak_tenv_def; extend_dec_tenv_def; type_env_INFO.ri_accessors] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC nsSub_nsAppend2 THEN ASM_REWRITE_TAC[]);;

let weak_extend_dec_tenv = prove
 (`tenv_ok tenv1 /\ weak tenv2 tenv3
   ==> weak (extend_dec_tenv tenv1 tenv2) (extend_dec_tenv tenv1 tenv3)`,
  REWRITE_TAC[weak_def; tenv_ok_def] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[weak_tenv_extend_dec_tenv] THEN
  ASM_REWRITE_TAC[extend_dec_tenv_def; type_env_INFO.ri_accessors]);;

let type_d_weakening = prove
 (`(!check tenv d decls tenv'. type_d check tenv d decls tenv'
      ==> !tenv''. check = F /\ tenv_ok tenv'' /\ weak tenv'' tenv
                   ==> type_d check tenv'' d decls tenv') /\
   (!check tenv d decls tenv'. type_ds check tenv d decls tenv'
      ==> !tenv''. check = F /\ tenv_ok tenv'' /\ weak tenv'' tenv
                   ==> type_ds check tenv'' d decls tenv')`,
  let WEAKT_TAC =
    FIRST_ASSUM(fun th -> if fst(strip_comb(concl th)) = `weak` then
      STRIP_ASSUME_TAC(REWRITE_RULE[weak_def] th) else NO_TAC) THEN
    ASM_REWRITE_TAC[] in
  MATCH_MP_TAC type_d_ind THEN RW[] THEN ONCE_REWRITE_TAC[type_d_cases] THEN RW[] THENL
   [(* Dlet (value) *)
    DISJ1_TAC THEN MAP_EVERY EXISTS_TAC [`tvs:num`; `t:t`; `bindings:(mlstring#t)list`] THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL
     [FIRST_ASSUM(MP_TAC o SPECL [`tenv'':type_env`; `tvs:num`] o
        MATCH_MP (CONJUNCT1 type_p_weakening)) THEN ASM_REWRITE_TAC[GE; LE_REFL];
      MATCH_MP_TAC (CONJUNCT1 type_e_weakening) THEN
      MAP_EVERY EXISTS_TAC [`tenv:type_env`; `bind_tvar tvs Empty`] THEN
      ASM_REWRITE_TAC[weak_tenvE_refl]];
    (* Dlet *)
    DISJ2_TAC THEN MAP_EVERY EXISTS_TAC [`t:t`; `bindings:(mlstring#t)list`] THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL
     [FIRST_ASSUM(MP_TAC o SPECL [`tenv'':type_env`; `0`] o
        MATCH_MP (CONJUNCT1 type_p_weakening)) THEN ASM_REWRITE_TAC[GE; LE_REFL];
      MATCH_MP_TAC (CONJUNCT1 type_e_weakening) THEN
      MAP_EVERY EXISTS_TAC [`tenv:type_env`; `Empty`] THEN
      ASM_REWRITE_TAC[weak_tenvE_refl]];
    (* Dletrec *)
    MAP_EVERY EXISTS_TAC [`bindings:(mlstring#t)list`; `tvs:num`] THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC (CONJUNCT2 (CONJUNCT2 type_e_weakening)) THEN
    MAP_EVERY EXISTS_TAC [`tenv:type_env`; `bind_var_list 0 bindings (bind_tvar tvs Empty)`] THEN
    ASM_REWRITE_TAC[weak_tenvE_refl];
    (* Dtype *)
    EXISTS_TAC `type_identities:num list` THEN WEAKT_TAC;
    (* Dtabbrev *)
    WEAKT_TAC;
    (* Dtabbrev *)
    WEAKT_TAC;
    (* Dexn *)
    WEAKT_TAC;
    (* Dexn *)
    WEAKT_TAC;
    (* Dmod *)
    EXISTS_TAC `tenv':type_env` THEN REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    (* Dlocal *)
    MAP_EVERY EXISTS_TAC [`tenv1:type_env`; `decls1:num->bool`; `decls2:num->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `type_ds F tenv'' lds decls1 tenv1` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> free_in `lds:dec list` (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `tenv_ok tenv1` ASSUME_TAC THENL
     [ASM_MESON_TAC[type_d_tenv_ok_helper]; ALL_TAC] THEN
    ASM_SIMP_TAC[extend_dec_tenv_ok; weak_extend_dec_tenv];
    (* type_ds *)
    MAP_EVERY EXISTS_TAC [`tenv1:type_env`; `tenv2:type_env`; `decls1:num->bool`;
                          `decls2:num->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `type_d F tenv'' d decls1 tenv1` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> free_in `d:dec` (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `tenv_ok tenv1` ASSUME_TAC THENL
     [ASM_MESON_TAC[type_d_tenv_ok_helper]; ALL_TAC] THEN
    ASM_SIMP_TAC[extend_dec_tenv_ok; weak_extend_dec_tenv]]);;
