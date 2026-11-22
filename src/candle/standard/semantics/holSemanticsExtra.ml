(* ========================================================================= *)
(* holSemanticsExtra: port of HOL4 candle/standard/semantics/                *)
(* holSemanticsExtraScript.sml (CakeML v3479).  Some lemmas about the        *)
(* semantics.  Notes on the rendering: the header of holSemantics.ml.        *)
(* ========================================================================= *)

needs "candle/syntax-lib/holSyntaxLib.ml";;
needs "candle/standard/syntax/holSyntax.ml";;
needs "candle/standard/syntax/holSyntaxExtra.ml";;
needs "candle/standard/semantics/holSemantics.ml";;
needs "candle/set-theory/setSpec.ml";;

prioritize_num();;
type_invention_error := true;;
let is_std_interpretation_is_type = prove
 (`is_std_interpretation0 (mem:U->U->bool) i ==> is_std_type_assignment0 mem (FST i)`,
  SIMP[is_std_interpretation0_def]);;

(* typesem *)

let typesem_inhabited = prove
 (`is_set_theory (mem:U->U->bool) ==>
   !tyenv dl tau ty.
     is_type_valuation0 mem tau /\
     is_type_assignment0 mem tyenv dl /\
     type_ok tyenv ty
     ==> ?x. mem x (typesem dl tau ty)`,
  STRIP_TAC THEN GEN_TAC THEN MATCH_MP_TAC typesem_ind THEN
  SIMP[typesem_def; is_type_valuation0_def; type_ok_def] THEN
  RW[is_type_assignment0_def; FEVERY_ALL_FLOOKUP] THEN
  SUBGOAL_THEN
   `!ls. LENGTH ls = LENGTH (args:hol_type list) /\ ALL (\s. ?x. mem x s) ls
         ==> ?x. (mem:U->U->bool) x ((dl:mlstring->U list->U) name ls)`
   MATCH_MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[LENGTH_MAP; EVERY_MAP] THEN FS[EVERY_MEM] THEN ASM_MESON_TAC[]);;

let typesem_Fun = prove
 (`!dl tau dom rng.
     is_std_type_assignment0 (mem:U->U->bool) dl
     ==> typesem dl tau (Tyapp (implode "fun") [dom; rng]) =
         funspace mem (typesem dl tau dom) (typesem dl tau rng)`,
  RW[is_std_type_assignment0_def; typesem_def; MAP]);;

let typesem_Bool = prove
 (`!dl tau.
     is_std_type_assignment0 (mem:U->U->bool) dl
     ==> typesem dl tau (Tyapp (implode "bool") []) = two mem`,
  RW[is_std_type_assignment0_def; typesem_def; MAP]);;

let typesem_TYPE_SUBST = prove
 (`!tyin ty (dl:mlstring->U list->U) tau.
     typesem dl tau (TYPE_SUBST tyin ty) =
     typesem dl (\x. typesem dl tau (TYPE_SUBST tyin (Tyvar x))) ty`,
  MATCH_MP_TAC TYPE_SUBST_ind THEN SIMP[typesem_def; TYPE_SUBST_def] THEN
  RW[] THEN AP_TERM_TAC THEN SIMP[MAP_MAP_o; MAP_EQ_f; o_THM]);;

let typesem_tyvars = prove
 (`!(dl:mlstring->U list->U) tau ty tau'.
     (!x. MEM x (tyvars ty) ==> tau' x = tau x)
     ==> typesem dl tau' ty = typesem dl tau ty`,
  MATCH_MP_TAC typesem_ind THEN
  REWRITE_TAC[tyvars_def; MEM_FOLDR_LIST_UNION; typesem_def; MEM] THEN
  CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[MAP_EQ_f] THEN
  X_GEN_TAC `y:hol_type` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:hol_type`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[]);;

let typesem_consts = prove
 (`!(dl:mlstring->U list->U) tau ty dl'.
     (!name args. RTC subtype1 (Tyapp name args) ty
        ==> dl' name = dl name \/
            ?vars. args = MAP Tyvar vars /\
                   dl' name (MAP tau vars) = dl name (MAP tau vars))
     ==> typesem dl' tau ty = typesem dl tau ty`,
  MATCH_MP_TAC typesem_ind THEN CONJ_TAC THENL [SIMP[typesem_def]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[typesem_def] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`name:mlstring`; `args:hol_type list`]) THEN
  REWRITE_TAC[RTC_REFL] THEN STRIP_TAC THENL
   [ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN REWRITE_TAC[MAP_EQ_f] THEN
    X_GEN_TAC `y:hol_type` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:hol_type`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN MATCH_MP_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[subtype_Tyapp] THEN ASM_MESON_TAC[];
    ASM_REWRITE_TAC[MAP_MAP_o; o_DEF; typesem_def; ETA_AX]]);;

(* termsem *)

let termsem_typesem = prove
 (`is_set_theory (mem:U->U->bool) ==>
   !sig i tm v dl tau tmenv.
     dl = FST i /\ tau = FST v /\
     is_valuation0 mem (FST sig) dl v /\
     is_interpretation0 mem sig i /\
     is_std_type_assignment0 mem dl /\
     hol_term_ok sig tm /\ tmenv = SND sig
     ==> mem (termsem0 mem tmenv i v tm) (typesem dl tau (typeof tm))`,
  STRIP_TAC THEN GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC hol_term_INDUCT THEN
  REPEAT CONJ_TAC THENL
   [(* Var *)
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[termsem0_def; typeof_def] THEN
    FS[is_valuation0_def; is_term_valuation0_def; hol_term_ok_def];
    (* Const *)
    MAP_EVERY X_GEN_TAC [`name:mlstring`; `ty:hol_type`] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN RVEQ_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[hol_term_ok_def]) THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `ty0:hol_type` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl)) THEN
    RENAME_TAC ["TYPE_SUBST tyin ty0"] THEN
    REWRITE_TAC[termsem0_def; typeof_def] THEN
    MP_TAC(ISPECL [`SND (sig:sig)`; `i:(mlstring->U list->U)#(mlstring->U list->U)`;
                   `name:mlstring`; `TYPE_SUBST tyin ty0`; `ty0:hol_type`;
                   `tyin:(hol_type#hol_type)list`] instance_def) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN BETA_TAC THEN
    ONCE_REWRITE_TAC[typesem_TYPE_SUBST] THEN
    SUBGOAL_THEN `is_term_assignment0 mem (SND (sig:sig))
                    (FST (i:(mlstring->U list->U)#(mlstring->U list->U))) (SND i)`
      MP_TAC THENL [ASM_MESON_TAC[is_interpretation0_def]; ALL_TAC] THEN
    REWRITE_TAC[is_term_assignment0_def; FEVERY_ALL_FLOOKUP] THEN
    DISCH_THEN(MP_TAC o SPECL [`name:mlstring`; `ty0:hol_type`]) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
    DISCH_THEN(MP_TAC o SPEC
      `\x. if MEM x (tyvars ty0)
           then typesem (FST (i:(mlstring->U list->U)#(mlstring->U list->U)))
                  (FST (v:(mlstring->U)#(mlstring#hol_type->U))) (TYPE_SUBST tyin (Tyvar x))
           else two (mem:U->U->bool)`) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[is_type_valuation0_def] THEN X_GEN_TAC `x:mlstring` THEN
      COND_CASES_TAC THENL
       [MATCH_MP_TAC(UNDISCH typesem_inhabited) THEN EXISTS_TAC `FST (sig:sig)` THEN
        RULE_ASSUM_TAC(REWRITE_RULE[is_valuation0_def; is_interpretation0_def]) THEN
        ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[type_ok_TYPE_SUBST_imp];
        ASM_MESON_TAC[mem_boolset]];
      ALL_TAC] THEN
    MATCH_MP_TAC EQ_IMP THEN BINOP_TAC THENL
     [AP_TERM_TAC THEN REWRITE_TAC[MAP_EQ_f; o_THM] THEN
      REWRITE_TAC[GSYM IN_SET_OF_LIST; set_MAP_implode_STRING_SORT_MAP_explode] THEN
      SIMP_TAC[IN_SET_OF_LIST];
      MATCH_MP_TAC typesem_tyvars THEN SIMP_TAC[]];
    (* Comb *)
    MAP_EVERY X_GEN_TAC [`t1:hol_term`; `t2:hol_term`] THEN STRIP_TAC THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN RVEQ_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[hol_term_ok_def; WELLTYPED_CLAUSES]) THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
    REWRITE_TAC[termsem0_def; typeof_def] THEN
    MATCH_MP_TAC(UNDISCH apply_in_rng) THEN
    EXISTS_TAC `typesem (FST (i:(mlstring->U list->U)#(mlstring->U list->U)))
                  (FST (v:(mlstring->U)#(mlstring#hol_type->U))) (typeof t2)` THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[codomain_def; GSYM typesem_Fun] THEN
    SUBGOAL_THEN `Tyapp (implode "fun") [typeof t2; rty] = typeof t1` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[]; ASM_MESON_TAC[]];
    (* Abs *)
    MAP_EVERY X_GEN_TAC [`t1:hol_term`; `b:hol_term`] THEN STRIP_TAC THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN RVEQ_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[hol_term_ok_def]) THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `x:mlstring` (X_CHOOSE_THEN `ty:hol_type`
      (CONJUNCTS_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC))) THEN
    ASM_SIMP_TAC[termsem0_def; typeof_def; typesem_Fun] THEN
    MATCH_MP_TAC(UNDISCH abstract_in_funspace) THEN
    X_GEN_TAC `m:U` THEN DISCH_TAC THEN BETA_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC
      `(FST (v:(mlstring->U)#(mlstring#hol_type->U)), ((x,ty) =+ (m:U)) (SND v))`) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[is_valuation0_def; is_term_valuation0_def]) THEN
    ASM_REWRITE_TAC[is_valuation0_def; is_term_valuation0_def; APPLY_UPDATE_THM] THEN
    REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN ASM_MESON_TAC[]]);;

let termsem_typesem_matchable = prove
 (`is_set_theory (mem:U->U->bool) ==>
   !sig i tm v dl tau tmenv ty.
     dl = FST i /\ tau = FST v /\ is_valuation0 mem (FST sig) dl v /\
     is_interpretation0 mem sig i /\ is_std_type_assignment0 mem dl /\
     hol_term_ok sig tm /\ tmenv = SND sig /\
     ty = typesem dl tau (typeof tm)
     ==> mem (termsem0 mem tmenv i v tm) ty`,
  MESON_TAC[termsem_typesem]);;

let termsem_consts = prove
 (`!tmsig i v tm i'.
     welltyped tm /\
     (!name ty. VFREE_IN (hol_Const name ty) tm
                ==> instance tmsig i' name ty (FST v) =
                    instance tmsig i name ty (FST v)) /\
     (!t. RTC subterm1 t tm
          ==> typesem (FST i') (FST v) (typeof t) =
              typesem (FST i) (FST v) (typeof t))
     ==> termsem0 (mem:U->U->bool) tmsig i' v tm = termsem0 mem tmsig i v tm`,
  QINDUCT_ON "tm" THENL
   [SIMP_TAC[termsem0_def];
    REPEAT STRIP_TAC THEN REWRITE_TAC[termsem0_def] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[VFREE_IN_def];
    MAP_EVERY X_GEN_TAC [`t1:hol_term`; `t2:hol_term`] THEN STRIP_TAC THEN
    REPEAT GEN_TAC THEN REWRITE_TAC[WELLTYPED_CLAUSES; VFREE_IN_def; subterm_Comb] THEN
    STRIP_TAC THEN REWRITE_TAC[termsem0_def] THEN BINOP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[];
    MAP_EVERY X_GEN_TAC [`t1:hol_term`; `b:hol_term`] THEN STRIP_TAC THEN
    REPEAT GEN_TAC THEN REWRITE_TAC[WELLTYPED_CLAUSES] THEN STRIP_TAC THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REWRITE_TAC[termsem0_def] THEN
    FIRST_ASSUM(MP_TAC o SPEC `hol_Var n ty`) THEN
    FIRST_ASSUM(MP_TAC o SPEC `b:hol_term`) THEN
    REWRITE_TAC[subterm_Abs; RTC_REFL; typeof_def] THEN
    REPEAT(DISCH_THEN SUBST1_TAC) THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `m:U` THEN BETA_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[VFREE_IN_def; subterm_Abs; injectivity "hol_term";
                    distinctness "hol_term"]]);;

(* HOL4: the right side is ^Equalsem [..], the lambda term of               *)
(* is_std_interpretation_def applied to the list (a beta-redex).            *)
let CSEMAUX_tyvars_Equal = prove
 (`MAP implode (STRING_SORT (MAP explode (tyvars
     (Tyapp (implode "fun") [Tyvar (implode "A");
        Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "bool") []]])))) =
   [implode "A"]`,
  REWRITE_TAC[tyvars_def; ITLIST; LIST_UNION_def; LIST_INSERT_def; MEM; MAP] THEN
  REWRITE_TAC[STRING_SORT_def; ITLIST; INORDER_INSERT_def; MAP; explode_implode;
              implode_explode; FILTER; APPEND]);;

let termsem_Equal = prove
 (`is_set_theory (mem:U->U->bool) ==>
   !G i v ty.
     is_structure0 mem G i v /\ type_ok (FST G) ty
     ==> termsem0 mem (SND G) i v
           (hol_Const (implode "=")
              (Tyapp (implode "fun") [ty; Tyapp (implode "fun") [ty; Tyapp (implode "bool") []]])) =
         (\l. abstract mem (HD l) (funspace mem (HD l) (two mem))
                (\x. abstract mem (HD l) (two mem) (\y. boolean mem (x = y))))
         [typesem (FST i) (FST v) ty]`,
  STRIP_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[is_structure0_def; is_std_sig_def] THEN
  STRIP_TAC THEN REWRITE_TAC[termsem0_def] THEN
  MP_TAC(ISPECL [`SND (G:sig)`; `i:(mlstring->U list->U)#(mlstring->U list->U)`;
    `implode "="`;
    `Tyapp (implode "fun") [ty; Tyapp (implode "fun") [ty; Tyapp (implode "bool") []]]`;
    `Tyapp (implode "fun") [Tyvar (implode "A");
       Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "bool") []]]`;
    `[(ty:hol_type, Tyvar (implode "A"))]`] instance_def) THEN
  ASM_REWRITE_TAC[TYPE_SUBST_def; REV_ASSOCD; MAP] THEN
  DISCH_THEN SUBST1_TAC THEN BETA_TAC THEN
  REWRITE_TAC[CSEMAUX_tyvars_Equal; MAP; o_THM; TYPE_SUBST_def; REV_ASSOCD; HD] THEN
  UNDISCH_TAC `is_std_interpretation0 (mem:U->U->bool) i` THEN
  REWRITE_TAC[is_std_interpretation0_def; interprets0_def] THEN
  DISCH_THEN(MP_TAC o SPEC
    `\x:mlstring. typesem (FST (i:(mlstring->U list->U)#(mlstring->U list->U)))
                    (FST (v:(mlstring->U)#(mlstring#hol_type->U))) ty` o CONJUNCT2) THEN
  REWRITE_TAC[MAP; HD] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[is_type_valuation0_def] THEN
  MATCH_MP_TAC(UNDISCH typesem_inhabited) THEN EXISTS_TAC `FST (G:sig)` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[is_valuation0_def; is_interpretation0_def]) THEN
  ASM_REWRITE_TAC[]);;
let termsem_equation = prove
 (`is_set_theory (mem:U->U->bool) ==>
   !sig i v s t tmenv.
     is_structure0 mem sig i v /\
     hol_term_ok sig (s === t) /\
     tmenv = SND sig
     ==> termsem0 mem tmenv i v (s === t) =
         boolean mem (termsem0 mem tmenv i v s = termsem0 mem tmenv i v t)`,
  STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `is_std_sig sig /\ is_std_interpretation0 (mem:U->U->bool) i /\
                is_interpretation0 mem sig i /\ is_valuation0 mem (FST sig) (FST i) v`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[is_structure0_def]; ALL_TAC] THEN
  SUBGOAL_THEN `hol_term_ok sig s /\ hol_term_ok sig t /\ typeof t = typeof s`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[term_ok_equation]; ALL_TAC] THEN
  SUBGOAL_THEN `type_ok (FST (sig:sig)) (typeof s)` ASSUME_TAC THENL
   [ASM_MESON_TAC[term_ok_type_ok]; ALL_TAC] THEN
  SUBGOAL_THEN `is_std_type_assignment0 (mem:U->U->bool)
                  (FST (i:(mlstring->U list->U)#(mlstring->U list->U)))` ASSUME_TAC THENL
   [ASM_MESON_TAC[is_std_interpretation_is_type]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!u. hol_term_ok sig u /\ typeof u = typeof s
        ==> (mem:U->U->bool) (termsem0 mem (SND sig) i v u)
              (typesem (FST i) (FST v) (typeof s))`
   ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC(UNDISCH termsem_typesem) THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[equation_def; CONJUNCT1(CONJUNCT2(CONJUNCT2 termsem0_def))] THEN
  ASM_SIMP_TAC[termsem_Equal] THEN BETA_TAC THEN REWRITE_TAC[HD] THEN
  ABBREV_TAC `a = typesem (FST (i:(mlstring->U list->U)#(mlstring->U list->U)))
                    (FST (v:(mlstring->U)#(mlstring#hol_type->U))) (typeof s)` THEN
  SUBGOAL_THEN
   `apply mem (abstract mem a (funspace mem a (two mem))
       (\x. abstract mem a (two mem) (\y. boolean mem (x = y))))
       (termsem0 mem (SND (sig:sig)) i v s) =
    abstract mem a (two (mem:U->U->bool))
       (\y. boolean mem (termsem0 mem (SND sig) i v s = y))`
   SUBST1_TAC THENL
   [QSPECL_THEN ["\\x. abstract mem a (two mem) (\\y. boolean mem (x = y))";
                  "termsem0 mem (SND sig) i v s"; "a"; "funspace mem a (two mem)"]
      MP_TAC (UNDISCH apply_abstract) THEN
    BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [ASM_MESON_TAC[];
      MATCH_MP_TAC(UNDISCH abstract_in_funspace) THEN
      ASM_SIMP_TAC[boolean_in_boolset]];
    ALL_TAC] THEN
  QSPECL_THEN ["\\y. boolean mem (termsem0 mem (SND sig) i v s = y)";
               "termsem0 mem (SND sig) i v t"; "a"; "two mem"]
    MP_TAC (UNDISCH apply_abstract) THEN
  BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[boolean_in_boolset]);;

let termsem_raconv = prove
 (`!env tp. RACONV env tp
     ==> !G i v1 v2.
           FST v1 = FST v2 /\
           (!x1 ty1 x2 ty2.
              ALPHAVARS env (hol_Var x1 ty1,hol_Var x2 ty2)
              ==> termsem0 (mem:U->U->bool) G i v1 (hol_Var x1 ty1) =
                  termsem0 mem G i v2 (hol_Var x2 ty2)) /\
           ALL (\(x,y). welltyped x /\ welltyped y /\ typeof x = typeof y) env /\
           welltyped (FST tp) /\ welltyped (SND tp)
           ==> termsem0 mem G i v1 (FST tp) = termsem0 mem G i v2 (SND tp)`,
  MATCH_MP_TAC RACONV_strongind THEN REWRITE_TAC[FST; SND] THEN REPEAT CONJ_TAC THENL
   [MESON_TAC[];
    SIMP_TAC[termsem0_def];
    REPEAT STRIP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[WELLTYPED_CLAUSES]) THEN
    REWRITE_TAC[termsem0_def] THEN BINOP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`env:(hol_term#hol_term)list`; `t1:hol_term`; `t2:hol_term`;
                       `u1:hol_term`; `u2:hol_term`] THEN
  STRIP_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[WELLTYPED_CLAUSES] THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[typeof_def]) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) && is_var(lhs(concl th)) &&
                                                  type_of(lhs(concl th)) = `:hol_type`)) THEN
  SUBGOAL_THEN `typeof t1 = typeof t2` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`CONS (hol_Var n ty',hol_Var n' ty') env`; `(t1:hol_term,t2:hol_term)`]
      RACONV_TYPE) THEN
    ASM_REWRITE_TAC[ALL; FST; SND; WELLTYPED_CLAUSES; typeof_def];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[termsem0_def] THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `m:U` THEN BETA_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[ALL; WELLTYPED_CLAUSES; typeof_def] THEN
  REWRITE_TAC[ALPHAVARS_def; PAIR_EQ; injectivity "hol_term"; FST; SND] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[termsem0_def; APPLY_UPDATE_THM] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM]) THEN
  ASM_REWRITE_TAC[PAIR_EQ] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x1:mlstring`; `ty1:hol_type`; `x2:mlstring`; `ty2:hol_type`]) THEN
  ASM_REWRITE_TAC[termsem0_def] THEN ASM_MESON_TAC[]);;

let termsem_aconv = prove
 (`!G i v t1 t2.
     ACONV t1 t2 /\ welltyped t1 /\ welltyped t2
     ==> termsem0 (mem:U->U->bool) G i v t1 = termsem0 mem G i v t2`,
  REWRITE_TAC[ACONV_def] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP termsem_raconv) THEN
  REWRITE_TAC[FST; SND] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[ALPHAVARS_def; ALL; FST; SND] THEN MESON_TAC[]);;

(* HOL4's MEM_LIST_UNION is a set equation; its MEM form: *)
let CSEMAUX_MEM_LIST_UNION = prove
 (`!l1 l2 (x:A). MEM x (LIST_UNION l1 l2) <=> MEM x l1 \/ MEM x l2`,
  REWRITE_TAC[REWRITE_RULE[EXTENSION; IN_UNION; IN_SET_OF_LIST] MEM_LIST_UNION]);;

let termsem_frees = prove
 (`!G i t v1 v2.
     welltyped t /\ FST v1 = FST v2 /\
     (!x ty. VFREE_IN (hol_Var x ty) t ==> SND v1 (x,ty) = SND v2 (x,ty))
     ==> termsem0 (mem:U->U->bool) G i v1 t = termsem0 mem G i v2 t`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC hol_term_INDUCT THEN
  REWRITE_TAC[termsem0_def; VFREE_IN_def; WELLTYPED_CLAUSES] THEN
  REPEAT CONJ_TAC THENL
   [MESON_TAC[];
    SIMP_TAC[];
    REPEAT STRIP_TAC THEN BINOP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[];
    MAP_EVERY X_GEN_TAC [`t1:hol_term`; `b:hol_term`] THEN STRIP_TAC THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl)) THEN
    ASM_REWRITE_TAC[termsem0_def] THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `m:U` THEN BETA_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[APPLY_UPDATE_THM] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[injectivity "hol_term"] THEN
    ASM_MESON_TAC[PAIR_EQ]]);;

let typesem_frees = prove
 (`!ty tau1 tau2 (dl:mlstring->U list->U).
     (!a. MEM a (tyvars ty) ==> tau1 a = tau2 a)
     ==> typesem dl tau1 ty = typesem dl tau2 ty`,
  MESON_TAC[typesem_tyvars]);;

let termsem_tyfrees = prove
 (`!G i t v1 v2 tmenv.
     hol_term_ok G t /\
     SND v1 = SND v2 /\
     (!a. MEM a (tvars t) ==> FST v1 a = FST v2 a) /\
     tmenv = SND G
     ==> termsem0 (mem:U->U->bool) tmenv i v1 t = termsem0 mem tmenv i v2 t`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC hol_term_INDUCT THEN
  REWRITE_TAC[termsem0_def; tvars_def; hol_term_ok_def] THEN
  REPEAT CONJ_TAC THENL
   [MESON_TAC[];
    MAP_EVERY X_GEN_TAC [`name:mlstring`; `ty:hol_type`] THEN REPEAT GEN_TAC THEN
    STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl)) THEN
    RENAME_TAC ["TYPE_SUBST tyin ty0"] THEN
    MP_TAC(ISPECL [`SND (G:sig)`; `i:(mlstring->U list->U)#(mlstring->U list->U)`;
                   `name:mlstring`; `TYPE_SUBST tyin ty0`; `ty0:hol_type`;
                   `tyin:(hol_type#hol_type)list`] instance_def) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN BETA_TAC THEN
    AP_TERM_TAC THEN REWRITE_TAC[MAP_EQ_f; o_THM] THEN
    REWRITE_TAC[GSYM IN_SET_OF_LIST; set_MAP_implode_STRING_SORT_MAP_explode] THEN
    REWRITE_TAC[IN_SET_OF_LIST] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC typesem_frees THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[GSYM IN_SET_OF_LIST; tyvars_TYPE_SUBST; IN_ELIM_THM] THEN
    REWRITE_TAC[IN_SET_OF_LIST] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[TYPE_SUBST_def]) THEN ASM_MESON_TAC[];
    REWRITE_TAC[CSEMAUX_MEM_LIST_UNION] THEN REPEAT STRIP_TAC THEN BINOP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t1:hol_term`; `b:hol_term`] THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[tvars_def; CSEMAUX_MEM_LIST_UNION]) THEN
  REWRITE_TAC[termsem0_def] THEN
  SUBGOAL_THEN `!ty'. set_of_list (tyvars ty') SUBSET set_of_list (tvars b) \/
                      set_of_list (tyvars ty') SUBSET set_of_list (tyvars ty)
                ==> typesem (FST (i:(mlstring->U list->U)#(mlstring->U list->U)))
                      (FST (v1:(mlstring->U)#(mlstring#hol_type->U))) ty' =
                    typesem (FST i) (FST (v2:(mlstring->U)#(mlstring#hol_type->U))) ty'`
    ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC typesem_frees THEN
    RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; IN_SET_OF_LIST]) THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `set_of_list (tyvars (typeof b)) SUBSET set_of_list (tvars b)` ASSUME_TAC THENL
   [MATCH_MP_TAC tyvars_typeof_subset_tvars THEN ASM_MESON_TAC[WELLTYPED; term_ok_welltyped];
    ALL_TAC] THEN
  MK_COMB_TAC THENL
   [MK_COMB_TAC THENL [AP_TERM_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[SUBSET_REFL];
    ALL_TAC] THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `m:U` THEN BETA_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let CSEMAUX_UPDATE_LIST_dest_var = prove
 (CASE_TERM
  `!ilist (f:mlstring#hol_type->U) (g:hol_term->U) x ty.
     (!s s'. MEM (s',s) ilist ==> ?x ty. s = hol_Var x ty)
     ==> (f =++ MAP ((dest_var ## g) o (\(s',s). (s,s'))) (REVERSE ilist)) (x,ty) =
         match ALOOKUP (MAP (\(s',s). (s,s')) ilist) (hol_Var x ty) with
           NONE -> f (x,ty) | SOME t -> g t`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[APPLY_UPDATE_LIST_ALOOKUP; MAP_REVERSE; REVERSE_REVERSE] THEN
  REWRITE_TAC[GSYM MAP_MAP_o] THEN
  MP_TAC(ISPECL [`MAP (\(s':hol_term,s:hol_term). (s,s')) ilist`; `g:hol_term->U`;
                 `x:mlstring`; `ty:hol_type`] ALOOKUP_MAP_dest_var) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[GSYM ALL_MEM; MEM_MAP; EXISTS_PAIR_THM] THEN
    REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ] THEN ASM_MESON_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  CASES_ON `ALOOKUP (MAP (\(s':hol_term,s:hol_term). (s,s')) ilist) (hol_Var x ty)` THEN
  REWRITE_TAC[OPTION_MAP_DEF; option_CASE]);;

let CSEMAUX_ALOOKUP_FILTER_swap = prove
 (`!(l:(hol_term#hol_term)list) w k.
     ALOOKUP (MAP (\(s',s). (s,s')) (FILTER (\(s',s). ~(s = w)) l)) k =
     if k = w then NONE else ALOOKUP (MAP (\(s',s). (s,s')) l) k`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[FILTER; MAP; ALOOKUP_def; COND_ID] THEN
  REPEAT GEN_TAC THEN PAIR_CASES_ON `h:hol_term#hol_term` THEN
  REWRITE_TAC[FILTER; MAP; ALOOKUP_def] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  ASM_CASES_TAC `h1:hol_term = w` THEN ASM_REWRITE_TAC[MAP; ALOOKUP_def] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let termsem_simple_subst = prove
 (`!tm ilist.
     welltyped tm /\
     DISJOINT (set_of_list (bv_names tm))
       {y | ?ty u. VFREE_IN (hol_Var y ty) u /\ MEM u (MAP FST ilist)} /\
     (!s s'. MEM (s',s) ilist ==> ?x ty. s = hol_Var x ty /\ s' has_type ty)
     ==> !G i v.
           termsem0 (mem:U->U->bool) G i v (simple_subst ilist tm) =
           termsem0 mem G i
             (FST v, SND v =++ MAP ((dest_var ## termsem0 mem G i v) o (\(s',s). (s,s')))
                                   (REVERSE ilist))
             tm`,
  MATCH_MP_TAC hol_term_INDUCT THEN REPEAT CONJ_TAC THENL
   [(* Var *)
   REPEAT STRIP_TAC THEN REWRITE_TAC[simple_subst_def; termsem0_def] THEN
   QSPECL_THEN ["ilist"; "SND v"; "termsem0 mem G i v"; "a0"; "a1"] MP_TAC
     CSEMAUX_UPDATE_LIST_dest_var THEN
   ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
   REWRITE_TAC[REV_ASSOCD_ALOOKUP] THEN
   CASES_ON `ALOOKUP (MAP (\(s':hol_term,s:hol_term). (s,s')) ilist) (hol_Var a0 a1)` THEN
   REWRITE_TAC[option_CASE; termsem0_def];
    (* Const *)
    SIMP_TAC[simple_subst_def; termsem0_def];
    (* Comb *)
   MAP_EVERY X_GEN_TAC [`t1:hol_term`; `t2:hol_term`] THEN STRIP_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM]) THEN REPEAT GEN_TAC THEN
   REWRITE_TAC[WELLTYPED_CLAUSES; bv_names_def; SET_OF_LIST_APPEND; DISJOINT_UNION] THEN
   STRIP_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[simple_subst_def; termsem0_def] THEN
   BINOP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    (* Abs *)
   MAP_EVERY X_GEN_TAC [`t1:hol_term`; `b:hol_term`] THEN STRIP_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM]) THEN
   X_GEN_TAC `ilist:(hol_term#hol_term)list` THEN
   REWRITE_TAC[WELLTYPED_CLAUSES] THEN STRIP_TAC THEN
   FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl)) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[bv_names_def; dest_var_def; set_of_list; DISJOINT_INSERT;
                               IN_ELIM_THM]) THEN
   FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)) THEN
   REPEAT GEN_TAC THEN REWRITE_TAC[simple_subst_def; termsem0_def] THEN
   ABBREV_TAC `il = FILTER (\(s':hol_term,s:hol_term). ~(s = hol_Var n ty)) ilist` THEN
   SUBGOAL_THEN `!s s'. MEM (s',s) il ==> ?x ty. s = hol_Var x ty /\ s' has_type ty`
     ASSUME_TAC THENL
    [EXPAND_TAC "il" THEN REWRITE_TAC[MEM_FILTER] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `typeof (simple_subst il b) = typeof b` SUBST1_TAC THENL
    [MATCH_MP_TAC WELLTYPED_LEMMA THEN MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP] simple_subst_has_type) THEN
     ASM_REWRITE_TAC[GSYM WELLTYPED; GSYM ALL_MEM; FORALL_PAIR_THM] THEN
     REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`p2:hol_term`; `p1:hol_term`]) THEN
     ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[typeof_def];
     ALL_TAC] THEN
   AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `m:U` THEN BETA_TAC THEN
   FIRST_X_ASSUM(QSPECL_THEN ["il"; "G"; "i"; "(FST v, ((n,ty) =+ m) (SND v))"] MP_TAC) THEN
   ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN
     SUBGOAL_THEN `!u. MEM u (MAP FST (il:(hol_term#hol_term)list)) ==> MEM u (MAP FST (ilist:(hol_term#hol_term)list))`
       MP_TAC THENL
      [EXPAND_TAC "il" THEN REWRITE_TAC[MEM_MAP; MEM_FILTER] THEN MESON_TAC[]; ALL_TAC] THEN
     UNDISCH_TAC `DISJOINT (set_of_list (bv_names b))
       {y | ?ty u. VFREE_IN (hol_Var y ty) u /\ MEM u (MAP FST (ilist:(hol_term#hol_term)list))}` THEN
     REWRITE_TAC[IN_DISJOINT; IN_ELIM_THM] THEN MESON_TAC[];
     DISCH_THEN SUBST1_TAC] THEN
   AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[PAIR_EQ; FUN_EQ_THM; FORALL_PAIR_THM] THEN
   MAP_EVERY X_GEN_TAC [`z:mlstring`; `tyr:hol_type`] THEN
   QSPECL_THEN ["il"; "((n,ty) =+ m) (SND v)"; "termsem0 mem G i (FST v, ((n,ty) =+ m) (SND v))";
                "z"; "tyr"] MP_TAC CSEMAUX_UPDATE_LIST_dest_var THEN
   ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
   REWRITE_TAC[APPLY_UPDATE_THM] THEN
   QSPECL_THEN ["ilist"; "SND v"; "termsem0 mem G i v"; "z"; "tyr"] MP_TAC
     CSEMAUX_UPDATE_LIST_dest_var THEN
   ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
   EXPAND_TAC "il" THEN REWRITE_TAC[CSEMAUX_ALOOKUP_FILTER_swap; injectivity "hol_term"; PAIR_EQ] THEN
   ASM_CASES_TAC `n:mlstring = z /\ ty:hol_type = tyr` THENL
   [FIRST_X_ASSUM(CONJUNCTS_THEN SUBST_ALL_TAC) THEN REWRITE_TAC[option_CASE]; ALL_TAC] THEN
   SUBGOAL_THEN `~(z:mlstring = n /\ tyr:hol_type = ty)` (fun th -> REWRITE_TAC[th]) THENL
    [ASM_MESON_TAC[]; ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN
   CASES_ON `ALOOKUP (MAP (\(s':hol_term,s:hol_term). (s,s')) ilist) (hol_Var z tyr)` THEN
   REWRITE_TAC[option_CASE] THEN
   FIRST_X_ASSUM(MP_TAC o MATCH_MP ALOOKUP_MEM) THEN
   REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM; PAIR_EQ] THEN
   CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[PAIR_EQ] THEN
   DISCH_THEN(X_CHOOSE_THEN `p1:hol_term` (X_CHOOSE_THEN `p2:hol_term` STRIP_ASSUME_TAC)) THEN
   REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o rhs o concl))) THEN
   MATCH_MP_TAC termsem_frees THEN REWRITE_TAC[APPLY_UPDATE_THM; PAIR_EQ] THEN CONJ_TAC THENL
    [ASM_MESON_TAC[welltyped_def]; ALL_TAC] THEN
   REPEAT STRIP_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
   FIRST_X_ASSUM(CONJUNCTS_THEN SUBST_ALL_TAC) THEN
   SUBGOAL_THEN `MEM (p1:hol_term) (MAP FST (ilist:(hol_term#hol_term)list))` ASSUME_TAC THENL
    [REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM] THEN ASM_MESON_TAC[FST]; ASM_MESON_TAC[]]]);;
let termsem_VSUBST = prove
 (`!tm ilist.
     welltyped tm /\
     (!s s'. MEM (s',s) ilist ==> ?x ty. s = hol_Var x ty /\ s' has_type ty)
     ==> !G i v.
           termsem0 (mem:U->U->bool) G i v (VSUBST ilist tm) =
           termsem0 mem G i
             (FST v, SND v =++ MAP ((dest_var ## termsem0 mem G i v) o (\(s',s). (s,s')))
                                   (REVERSE ilist))
             tm`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`{y | ?ty u. VFREE_IN (hol_Var y ty) u /\
                              MEM u (MAP FST (ilist:(hol_term#hol_term)list))}`;
                 `tm:hol_term`] fresh_term_def) THEN
  ASM_REWRITE_TAC[FINITE_VFREE_IN_list] THEN
  ABBREV_TAC `fm = fresh_term {y | ?ty u. VFREE_IN (hol_Var y ty) u /\
                               MEM u (MAP FST (ilist:(hol_term#hol_term)list))} tm` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `ACONV (VSUBST ilist tm) (VSUBST ilist fm)` ASSUME_TAC THENL
   [MATCH_MP_TAC ACONV_VSUBST THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `welltyped (VSUBST ilist tm) /\ welltyped (VSUBST ilist fm)`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[VSUBST_WELLTYPED]; ALL_TAC] THEN
  SUBGOAL_THEN `VSUBST ilist fm = simple_subst ilist fm` ASSUME_TAC THENL
   [MATCH_MP_TAC VSUBST_simple_subst THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  TRANS_TAC EQ_TRANS `termsem0 (mem:U->U->bool) G i v (VSUBST ilist fm)` THEN
  CONJ_TAC THENL [MATCH_MP_TAC termsem_aconv THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`fm:hol_term`; `ilist:(hol_term#hol_term)list`] termsem_simple_subst) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC termsem_aconv THEN ASM_REWRITE_TAC[]);;
let termsem_simple_inst = prove
 (`!G tm tyin tmenv.
     welltyped tm /\ hol_term_ok G tm /\
     ALL_DISTINCT (bv_names tm) /\
     DISJOINT (set_of_list (bv_names tm)) {x | ?ty. VFREE_IN (hol_Var x ty) tm} /\
     tmenv = SND G
     ==> !i v.
           termsem0 (mem:U->U->bool) tmenv i v (simple_inst tyin tm) =
           termsem0 mem tmenv i
             ((\x. typesem (FST i) (FST v) (TYPE_SUBST tyin (Tyvar x))),
              (\(x,ty). SND v (x, TYPE_SUBST tyin ty)))
             tm`,
  GEN_TAC THEN MATCH_MP_TAC hol_term_INDUCT THEN REPEAT CONJ_TAC THENL
   [(* Var *)
   SIMP_TAC[simple_inst_def; termsem0_def] THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
   REWRITE_TAC[];
    (* Const *)
   MAP_EVERY X_GEN_TAC [`name:mlstring`; `ty:hol_type`] THEN
   REWRITE_TAC[RIGHT_IMP_FORALL_THM] THEN REPEAT GEN_TAC THEN
   REWRITE_TAC[hol_term_ok_def] THEN STRIP_TAC THEN
   FIRST_X_ASSUM SUBST_ALL_TAC THEN
   FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl)) THEN
   RENAME_TAC ["TYPE_SUBST i1 ty0"] THEN
   REWRITE_TAC[simple_inst_def; termsem0_def; TYPE_SUBST_compose] THEN
   MP_TAC(ISPECL [`SND (G:sig)`; `i:(mlstring->U list->U)#(mlstring->U list->U)`;
                  `name:mlstring`; `TYPE_SUBST i1 ty0`; `ty0:hol_type`;
                  `i1:(hol_type#hol_type)list`] instance_def) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
   MP_TAC(ISPECL [`SND (G:sig)`; `i:(mlstring->U list->U)#(mlstring->U list->U)`;
                  `name:mlstring`;
                  `TYPE_SUBST (APPEND (MAP (TYPE_SUBST tyin ## I) i1) tyin) ty0`; `ty0:hol_type`;
                  `APPEND (MAP (TYPE_SUBST tyin ## I) i1) tyin`] instance_def) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN BETA_TAC THEN
   AP_TERM_TAC THEN REWRITE_TAC[MAP_EQ_f; o_THM] THEN REPEAT STRIP_TAC THEN
   REWRITE_TAC[GSYM TYPE_SUBST_compose] THEN
   GEN_REWRITE_TAC LAND_CONV [typesem_TYPE_SUBST] THEN REFL_TAC;
    (* Comb *)
   MAP_EVERY X_GEN_TAC [`t1:hol_term`; `t2:hol_term`] THEN STRIP_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM]) THEN
   REWRITE_TAC[RIGHT_IMP_FORALL_THM] THEN REPEAT GEN_TAC THEN
   REWRITE_TAC[WELLTYPED_CLAUSES; hol_term_ok_def; bv_names_def; ALL_DISTINCT_APPEND;
               SET_OF_LIST_APPEND; DISJOINT_UNION; VFREE_IN_def] THEN
   STRIP_TAC THEN REWRITE_TAC[simple_inst_def; termsem0_def] THEN BINOP_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
   RULE_ASSUM_TAC(REWRITE_RULE[IN_DISJOINT; IN_ELIM_THM]) THEN
   REWRITE_TAC[IN_DISJOINT; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    (* Abs *)
   MAP_EVERY X_GEN_TAC [`t1:hol_term`; `b:hol_term`] THEN STRIP_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM]) THEN
   REWRITE_TAC[RIGHT_IMP_FORALL_THM] THEN REPEAT GEN_TAC THEN
   REWRITE_TAC[WELLTYPED_CLAUSES] THEN STRIP_TAC THEN
   REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl))) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[hol_term_ok_def; injectivity "hol_term"; bv_names_def;
     dest_var_def; set_of_list; ALL_DISTINCT; DISJOINT_INSERT; IN_ELIM_THM; VFREE_IN_def;
     IN_SET_OF_LIST]) THEN
   REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
   REWRITE_TAC[simple_inst_def; termsem0_def] THEN
   SUBGOAL_THEN `typeof (simple_inst tyin b) = TYPE_SUBST tyin (typeof b)` SUBST1_TAC THENL
    [MATCH_MP_TAC WELLTYPED_LEMMA THEN ASM_SIMP_TAC[simple_inst_has_type]; ALL_TAC] THEN
   MK_COMB_TAC THENL
    [MK_COMB_TAC THENL [AP_TERM_TAC; ALL_TAC] THEN MATCH_ACCEPT_TAC typesem_TYPE_SUBST;
     ALL_TAC] THEN
   REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `m:U` THEN BETA_TAC THEN
   SUBGOAL_THEN `hol_term_ok G b` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
   FIRST_X_ASSUM(QSPECL_THEN ["tyin"; "SND G"; "i"; "(FST v, ((n, TYPE_SUBST tyin ty) =+ m) (SND v))"]
     MP_TAC) THEN
   ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN
     UNDISCH_TAC `DISJOINT (set_of_list (bv_names b))
       {x | ?ty'. ~(n = x /\ ty = ty') /\ VFREE_IN (hol_Var x ty') b}` THEN
     UNDISCH_TAC `~MEM n (bv_names b)` THEN
     REWRITE_TAC[IN_DISJOINT; IN_ELIM_THM; IN_SET_OF_LIST] THEN MESON_TAC[];
     DISCH_THEN SUBST1_TAC] THEN
   REWRITE_TAC[] THEN MATCH_MP_TAC termsem_frees THEN ASM_REWRITE_TAC[] THEN
   REPEAT GEN_TAC THEN DISCH_TAC THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
   REWRITE_TAC[APPLY_UPDATE_THM; PAIR_EQ] THEN
   ASM_CASES_TAC `n:mlstring = x` THEN ASM_REWRITE_TAC[] THEN
   FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
   ASM_CASES_TAC `ty:hol_type = ty'` THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;
let termsem_INST = prove
 (`!G tm tyin tmenv.
     hol_term_ok G tm /\ tmenv = SND G
     ==> !i v.
           termsem0 (mem:U->U->bool) tmenv i v (INST tyin tm) =
           termsem0 mem tmenv i
             ((\x. typesem (FST i) (FST v) (TYPE_SUBST tyin (Tyvar x))),
              (\(x,ty). SND v (x, TYPE_SUBST tyin ty)))
             tm`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `welltyped tm` ASSUME_TAC THENL [ASM_MESON_TAC[term_ok_welltyped]; ALL_TAC] THEN
  MP_TAC(ISPECL [`{x | ?ty. VFREE_IN (hol_Var x ty) tm}`; `tm:hol_term`] fresh_term_def) THEN
  ASM_REWRITE_TAC[FINITE_VFREE_IN] THEN
  ABBREV_TAC `fm = fresh_term {x | ?ty. VFREE_IN (hol_Var x ty) tm} tm` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `ACONV (INST tyin tm) (INST tyin fm)` ASSUME_TAC THENL
   [MATCH_MP_TAC ACONV_INST THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `welltyped (INST tyin tm) /\ welltyped (INST tyin fm)`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[INST_WELLTYPED]; ALL_TAC] THEN
  SUBGOAL_THEN `{x | ?ty. VFREE_IN (hol_Var x ty) tm} = {x | ?ty. VFREE_IN (hol_Var x ty) fm}`
    ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN ASM_MESON_TAC[VFREE_IN_ACONV]; ALL_TAC] THEN
  SUBGOAL_THEN `INST tyin fm = simple_inst tyin fm` ASSUME_TAC THENL
   [MATCH_MP_TAC INST_simple_inst THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `hol_term_ok G fm` ASSUME_TAC THENL
   [ASM_MESON_TAC[term_ok_aconv]; ALL_TAC] THEN
  TRANS_TAC EQ_TRANS `termsem0 (mem:U->U->bool) (SND (G:sig)) i v (INST tyin fm)` THEN
  CONJ_TAC THENL [MATCH_MP_TAC termsem_aconv THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`G:sig`; `fm:hol_term`; `tyin:(hol_type#hol_type)list`; `SND (G:sig)`]
    termsem_simple_inst) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC termsem_aconv THEN ASM_REWRITE_TAC[]);;
(* HOL4: the bound variable tyenv' is vacuous (a type variable in HOL4);   *)
(* here it has the type tysig.                                              *)
let termsem_extend = prove
 (`!tyenv tmenv (tyenv':tysig) tmenv' tm.
     tmenv SUBMAP tmenv' /\
     hol_term_ok (tyenv,tmenv) tm
     ==> !i v. termsem0 (mem:U->U->bool) tmenv' i v tm = termsem0 mem tmenv i v tm`,
  REPEAT GEN_TAC THEN REWRITE_TAC[RIGHT_IMP_FORALL_THM] THEN
  SPEC_TAC(`tm:hol_term`,`tm:hol_term`) THEN MATCH_MP_TAC hol_term_INDUCT THEN
  REWRITE_TAC[termsem0_def; hol_term_ok_def] THEN REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`name:mlstring`; `ty:hol_type`] THEN REPEAT GEN_TAC THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl)) THEN
    RENAME_TAC ["TYPE_SUBST tyin ty0"] THEN
    SUBGOAL_THEN `FLOOKUP (tmenv':tmsig) name = SOME ty0` ASSUME_TAC THENL
     [ASM_MESON_TAC[FLOOKUP_SUBMAP]; ALL_TAC] THEN
    MP_TAC(ISPECL [`tmenv':tmsig`; `i:(mlstring->U list->U)#(mlstring->U list->U)`;
                   `name:mlstring`; `TYPE_SUBST tyin ty0`; `ty0:hol_type`;
                   `tyin:(hol_type#hol_type)list`] instance_def) THEN
    MP_TAC(ISPECL [`tmenv:tmsig`; `i:(mlstring->U list->U)#(mlstring->U list->U)`;
                   `name:mlstring`; `TYPE_SUBST tyin ty0`; `ty0:hol_type`;
                   `tyin:(hol_type#hol_type)list`] instance_def) THEN
    ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN REFL_TAC;
    SIMP_TAC[];
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o check (is_var o lhs o concl)) THEN
    REWRITE_TAC[termsem0_def] THEN ASM_SIMP_TAC[]]);;

let is_valuation_reduce = prove
 (`!tyenv tyenv' dl v.
     tyenv SUBMAP tyenv' /\ is_valuation0 (mem:U->U->bool) tyenv' dl v
     ==> is_valuation0 mem tyenv dl v`,
  REWRITE_TAC[is_valuation0_def; is_term_valuation0_def] THEN
  MESON_TAC[type_ok_extend]);;

(* HOL4: the bound variable tm is vacuous (a type variable in HOL4); here   *)
(* it has the type hol_term.                                                *)
let satisfies_extend = prove
 (`!tyenv tmenv tyenv' tmenv' (tm:hol_term) i h c.
     tmenv SUBMAP tmenv' /\ tyenv SUBMAP tyenv' /\
     ALL (hol_term_ok (tyenv,tmenv)) (CONS c h) /\
     satisfies0 (mem:U->U->bool) i ((tyenv,tmenv),h,c)
     ==> satisfies0 mem i ((tyenv',tmenv'),h,c)`,
  REWRITE_TAC[satisfies0_def; ALL; GSYM ALL_MEM] THEN
  MESON_TAC[hol_term_ok_extend; termsem_extend; is_valuation_reduce]);;
(* one interpretation being compatible with another in a signature *)

let equal_on_def = cake_def
  `equal_on (sig:sig) (i:(mlstring->U list->U)#(mlstring->U list->U)) i' <=>
     (!name. name IN FDOM (FST sig) ==> FST i' name = FST i name) /\
     (!name. name IN FDOM (SND sig) ==> SND i' name = SND i name)`;;

let equal_on_refl = prove
 (`!sig (i:(mlstring->U list->U)#(mlstring->U list->U)). equal_on sig i i`,
  REWRITE_TAC[equal_on_def]);;

let equal_on_sym = prove
 (`!sig (i:(mlstring->U list->U)#(mlstring->U list->U)) i'.
     equal_on sig i i' ==> equal_on sig i' i`,
  SIMP_TAC[equal_on_def]);;

let equal_on_trans = prove
 (`!sig (i1:(mlstring->U list->U)#(mlstring->U list->U)) i2 i3.
     equal_on sig i1 i2 /\ equal_on sig i2 i3 ==> equal_on sig i1 i3`,
  SIMP_TAC[equal_on_def]);;

let equal_on_interprets = prove
 (`!sig (i1:(mlstring->U list->U)#(mlstring->U list->U)) i2 name args ty m.
     equal_on sig i1 i2 /\
     interprets0 (mem:U->U->bool) (SND i1) name args m /\
     FLOOKUP (SND sig) name = SOME ty /\
     type_ok (FST sig) ty /\
     set_of_list (tyvars ty) = set_of_list args
     ==> interprets0 mem (SND i2) name args m`,
  REWRITE_TAC[equal_on_def; interprets0_def] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `SND (i2:(mlstring->U list->U)#(mlstring->U list->U)) name =
                SND (i1:(mlstring->U list->U)#(mlstring->U list->U)) name`
    SUBST1_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[FLOOKUP_DEF; option_DISTINCT];
    ASM_MESON_TAC[]]);;

let equal_on_reduce = prove
 (`!ls ctxt (i:(mlstring->U list->U)#(mlstring->U list->U)) i'.
     equal_on (alist_to_fmap (FLAT (MAP types_of_upd (APPEND ls ctxt))),
               alist_to_fmap (FLAT (MAP consts_of_upd (APPEND ls ctxt)))) i i' /\
     DISJOINT (FDOM (alist_to_fmap (FLAT (MAP types_of_upd ls))))
              (FDOM (alist_to_fmap (FLAT (MAP types_of_upd ctxt)))) /\
     DISJOINT (FDOM (alist_to_fmap (FLAT (MAP consts_of_upd ls))))
              (FDOM (alist_to_fmap (FLAT (MAP consts_of_upd ctxt))))
     ==> equal_on (alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
                   alist_to_fmap (FLAT (MAP consts_of_upd ctxt))) i i'`,
  REWRITE_TAC[equal_on_def; FDOM_alist_to_fmap; MAP_APPEND; FLAT_APPEND;
              SET_OF_LIST_APPEND; IN_UNION] THEN
  MESON_TAC[]);;

(* semantics only depends on interpretation of things in the term's signature *)

let typesem_sig = prove
 (`!ty tau (dl:mlstring->U list->U) dl' tyenv.
     type_ok tyenv ty /\ (!name. name IN FDOM tyenv ==> dl' name = dl name)
     ==> typesem dl' tau ty = typesem dl tau ty`,
  MATCH_MP_TAC type_ind THEN REWRITE_TAC[typesem_def; type_ok_def; GSYM ALL_MEM] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `MAP (typesem dl' tau) l = MAP (typesem (dl:mlstring->U list->U) tau) l`
    SUBST1_TAC THENL
   [REWRITE_TAC[MAP_EQ_f] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  AP_THM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_MESON_TAC[FLOOKUP_DEF; option_DISTINCT]);;
let termsem_sig = prove
 (`!tm G i v i' tmenv.
     is_std_sig G /\ hol_term_ok G tm /\ tmenv = SND G /\ equal_on G i i'
     ==> termsem0 (mem:U->U->bool) tmenv i' v tm = termsem0 mem tmenv i v tm`,
  REWRITE_TAC[equal_on_def] THEN MATCH_MP_TAC hol_term_INDUCT THEN
  REWRITE_TAC[termsem0_def; hol_term_ok_def] THEN REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`name:mlstring`; `ty:hol_type`] THEN REPEAT GEN_TAC THEN
    STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl))) THEN
    RENAME_TAC ["TYPE_SUBST tyin ty0"] THEN
    MP_TAC(ISPECL [`SND (G:sig)`; `i':(mlstring->U list->U)#(mlstring->U list->U)`;
                   `name:mlstring`; `TYPE_SUBST tyin ty0`; `ty0:hol_type`;
                   `tyin:(hol_type#hol_type)list`] instance_def) THEN
    MP_TAC(ISPECL [`SND (G:sig)`; `i:(mlstring->U list->U)#(mlstring->U list->U)`;
                   `name:mlstring`; `TYPE_SUBST tyin ty0`; `ty0:hol_type`;
                   `tyin:(hol_type#hol_type)list`] instance_def) THEN
    ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN BETA_TAC THEN
    MK_COMB_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_MESON_TAC[FLOOKUP_DEF; option_DISTINCT];
      REWRITE_TAC[MAP_EQ_f; o_THM] THEN
      REWRITE_TAC[GSYM IN_SET_OF_LIST; set_MAP_implode_STRING_SORT_MAP_explode] THEN
      REWRITE_TAC[IN_SET_OF_LIST] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC typesem_sig THEN EXISTS_TAC `FST (G:sig)` THEN
      ASM_MESON_TAC[type_ok_TYPE_SUBST_imp]];
    REPEAT STRIP_TAC THEN BINOP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t1:hol_term`; `b:hol_term`] THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl))) THEN
  REWRITE_TAC[termsem0_def] THEN
  SUBGOAL_THEN `!ty'. type_ok (FST (G:sig)) ty'
                      ==> typesem (FST (i':(mlstring->U list->U)#(mlstring->U list->U)))
                            (FST (v:(mlstring->U)#(mlstring#hol_type->U))) ty' =
                          typesem (FST (i:(mlstring->U list->U)#(mlstring->U list->U))) (FST v) ty'`
    ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC typesem_sig THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `type_ok (FST (G:sig)) (typeof b)` ASSUME_TAC THENL
   [ASM_MESON_TAC[term_ok_type_ok]; ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  X_GEN_TAC `m:U` THEN BETA_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  EXISTS_TAC `G:sig` THEN ASM_REWRITE_TAC[]);;

let satisfies_sig = prove
 (`!(i:(mlstring->U list->U)#(mlstring->U list->U)) i' sig h c.
     is_std_sig sig /\
     ALL (hol_term_ok sig) (CONS c h) /\
     equal_on sig i i' /\
     satisfies0 (mem:U->U->bool) i (sig,h,c)
     ==> satisfies0 mem i' (sig,h,c)`,
  REWRITE_TAC[satisfies0_def; ALL; GSYM ALL_MEM] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `termsem0 (mem:U->U->bool) (SND (sig:sig)) i v c = setSpec_true mem` MP_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[termsem_sig]] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[termsem_sig]] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[is_valuation0_def; is_term_valuation0_def]) THEN
  ASM_REWRITE_TAC[is_valuation0_def; is_term_valuation0_def] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `typesem (FST (i:(mlstring->U list->U)#(mlstring->U list->U)))
                  (FST (v:(mlstring->U)#(mlstring#hol_type->U))) ty =
                typesem (FST (i':(mlstring->U list->U)#(mlstring->U list->U))) (FST v) ty` SUBST1_TAC THENL
   [MATCH_MP_TAC typesem_sig THEN EXISTS_TAC `FST (sig:sig)` THEN
    ASM_MESON_TAC[equal_on_def];
    ASM_MESON_TAC[]]);;
(* valuations exist *)

let term_valuation_exists = prove
 (`is_set_theory (mem:U->U->bool) ==>
   !tyenv dl tau.
     is_type_valuation0 mem tau /\ is_type_assignment0 mem tyenv dl
     ==> ?sigma. is_valuation0 mem tyenv dl (tau,sigma)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[is_valuation0_def; is_term_valuation0_def] THEN
  EXISTS_TAC `\(x:mlstring,ty). @v. (mem:U->U->bool) v (typesem dl tau ty)` THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REPEAT STRIP_TAC THEN
  CONV_TAC SELECT_CONV THEN ASM_MESON_TAC[typesem_inhabited]);;

(* HOL4: the local value is_type_valuation_exists (an UNDISCHed theorem) *)
let CSEMAUX_is_type_valuation_exists = UNDISCH (prove
 (`is_set_theory (mem:U->U->bool) ==> is_type_valuation0 mem (K (two mem))`,
  SIMP_TAC[is_type_valuation0_def; K_THM] THEN MESON_TAC[boolean_in_boolset]));;

let valuation_exists = prove
 (`is_set_theory (mem:U->U->bool) ==>
   !tyenv dl. is_type_assignment0 mem tyenv dl ==> ?v. is_valuation0 mem tyenv dl v`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[is_valuation0_def] THEN
  EXISTS_TAC `(K (two (mem:U->U->bool)):mlstring->U,
               \(x:mlstring,ty). @v. (mem:U->U->bool) v (typesem dl (K (two mem)) ty))` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [ACCEPT_TAC(DISCH_ALL CSEMAUX_is_type_valuation_exists |> C MP (ASSUME `is_set_theory (mem:U->U->bool)`));
    ALL_TAC] THEN
  REWRITE_TAC[is_term_valuation0_def] THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  REPEAT STRIP_TAC THEN CONV_TAC SELECT_CONV THEN
  MATCH_MP_TAC(UNDISCH typesem_inhabited) THEN EXISTS_TAC `tyenv:tysig` THEN
  ASM_REWRITE_TAC[CSEMAUX_is_type_valuation_exists]);;

let extend_valuation_exists = prove
 (`is_set_theory (mem:U->U->bool) ==>
   !tysig dl v tysig'.
     is_valuation0 mem tysig dl v /\ tysig SUBMAP tysig' /\
     is_type_assignment0 mem tysig' dl
     ==> ?v'. is_valuation0 mem tysig' dl v' /\
              FST v' = FST v /\
              (!x ty. type_ok tysig ty ==> SND v (x,ty) = SND v' (x,ty))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXISTS_PAIR_THM] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[is_valuation0_def; is_term_valuation0_def]) THEN
  REWRITE_TAC[is_valuation0_def; is_term_valuation0_def] THEN
  EXISTS_TAC `FST (v:(mlstring->U)#(mlstring#hol_type->U))` THEN
  EXISTS_TAC `\(x:mlstring,ty). if type_ok tysig ty
                                then SND (v:(mlstring->U)#(mlstring#hol_type->U)) (x,ty)
                                else @m. (mem:U->U->bool) m (typesem dl (FST v) ty)` THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  SIMP_TAC[] THEN REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN
  CONV_TAC SELECT_CONV THEN ASM_MESON_TAC[typesem_inhabited]);;

let is_type_valuation_UPDATE_LIST = prove
 (`!t ls. is_type_valuation0 (mem:U->U->bool) t /\ ALL ((\s. ?x. mem x s) o SND) ls
          ==> is_type_valuation0 mem (t =++ ls)`,
  REWRITE_TAC[is_type_valuation0_def; APPLY_UPDATE_LIST_ALOOKUP] THEN
  REPEAT STRIP_TAC THEN
  CASES_ON `ALOOKUP (REVERSE (ls:(mlstring#U)list)) x` THEN
  ASM_REWRITE_TAC[option_CASE] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP ALOOKUP_MEM) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_MEM; o_THM]) THEN
  REWRITE_TAC[MEM_REVERSE] THEN ASM_MESON_TAC[SND]);;
(* identity instance *)

(* HOL4: the outer bound variable tau is vacuous (a type variable in HOL4,  *)
(* the right side binds its own tau); here it has the type mlstring -> U.  *)
let identity_instance = prove
 (`!tmenv (i:(mlstring->U list->U)#(mlstring->U list->U)) name ty (tau:mlstring->U).
     FLOOKUP tmenv name = SOME ty
     ==> instance tmenv i name ty =
         \tau. SND i name (MAP tau (MAP implode (STRING_SORT (MAP explode (tyvars ty)))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`tmenv:tmsig`; `i:(mlstring->U list->U)#(mlstring->U list->U)`;
                 `name:mlstring`; `ty:hol_type`; `ty:hol_type`;
                 `[]:(hol_type#hol_type)list`] instance_def) THEN
  ASM_REWRITE_TAC[TYPE_SUBST_NIL] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN BETA_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[MAP_EQ_f; o_THM; TYPE_SUBST_def; REV_ASSOCD; typesem_def]);;

(* special cases of interprets *)

(* HOL4: interprets_def specialised to vs = [] and simplified with the      *)
(* local rwt; like HOL4's theorem it has the hypothesis is_set_theory mem.  *)
let interprets_nil = UNDISCH (prove
 (`is_set_theory (mem:U->U->bool) ==>
   !gamma name f. interprets0 mem gamma name [] f <=> gamma name [] = f []`,
  DISCH_TAC THEN REWRITE_TAC[interprets0_def; MAP] THEN
  MESON_TAC[CSEMAUX_is_type_valuation_exists]));;

let interprets_one = prove
 (`interprets0 (mem:U->U->bool) i name [v] f <=>
   (!x. (?y. mem y x) ==> i name [x] = f [x])`,
  REWRITE_TAC[interprets0_def; MAP; is_type_valuation0_def] THEN EQ_TAC THEN
  REPEAT STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `K (x:U):mlstring->U`) THEN REWRITE_TAC[K_THM] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* for models, reducing the context *)

let is_type_assignment_reduce = prove
 (`!tyenv tyenv' dl.
     tyenv SUBMAP tyenv' /\ is_type_assignment0 (mem:U->U->bool) tyenv' dl
     ==> is_type_assignment0 mem tyenv dl`,
  REWRITE_TAC[is_type_assignment0_def] THEN MESON_TAC[FEVERY_SUBMAP]);;

let is_term_assignment_reduce = prove
 (`!tmenv tmenv' dl gamma.
     tmenv SUBMAP tmenv' /\ is_term_assignment0 (mem:U->U->bool) tmenv' dl gamma
     ==> is_term_assignment0 mem tmenv dl gamma`,
  REWRITE_TAC[is_term_assignment0_def] THEN MESON_TAC[FEVERY_SUBMAP]);;

let is_interpretation_reduce = prove
 (`!(i:(mlstring->U list->U)#(mlstring->U list->U)) tyenv tmenv tyenv' tmenv'.
     tyenv SUBMAP tyenv' /\ tmenv SUBMAP tmenv' /\
     is_interpretation0 (mem:U->U->bool) (tyenv',tmenv') i
     ==> is_interpretation0 mem (tyenv,tmenv) i`,
  REWRITE_TAC[is_interpretation0_def] THEN
  MESON_TAC[is_type_assignment_reduce; is_term_assignment_reduce]);;

let is_valuation_extend_sig = prove
 (`is_set_theory (mem:U->U->bool) ==>
   !tyenv tyenv' tyass v.
     is_valuation0 mem tyenv tyass v /\
     is_type_assignment0 mem tyenv' tyass /\
     tyenv SUBMAP tyenv'
     ==> ?v'. FST v' = FST v /\
              (!ty. type_ok tyenv ty ==> !x. SND v' (x,ty) = SND v (x,ty)) /\
              is_valuation0 mem tyenv' tyass v'`,
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[is_valuation0_def; is_term_valuation0_def]) THEN
  REWRITE_TAC[is_valuation0_def; is_term_valuation0_def; EXISTS_PAIR_THM] THEN
  EXISTS_TAC `FST (v:(mlstring->U)#(mlstring#hol_type->U))` THEN
  EXISTS_TAC `\p:mlstring#hol_type. if type_ok tyenv (SND p)
                                    then SND (v:(mlstring->U)#(mlstring#hol_type->U)) p
                                    else @m. (mem:U->U->bool) m (typesem tyass (FST v) (SND p))` THEN
  ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN
  CONV_TAC SELECT_CONV THEN ASM_MESON_TAC[typesem_inhabited]);;
let satisfies_reduce = prove
 (`is_set_theory (mem:U->U->bool) ==>
   !i tyenv tmenv tyenv' tmenv' h c.
     is_std_sig (tyenv,tmenv) /\
     tyenv SUBMAP tyenv' /\
     tmenv SUBMAP tmenv' /\
     ALL (hol_term_ok (tyenv,tmenv)) (CONS c h) /\
     is_type_assignment0 mem tyenv' (FST i) /\
     satisfies0 mem i ((tyenv',tmenv'),h,c)
     ==> satisfies0 mem i ((tyenv,tmenv),h,c)`,
  REPEAT STRIP_TAC THEN UNDISCH_TAC `satisfies0 (mem:U->U->bool) i ((tyenv',tmenv'),h,c)` THEN
  REWRITE_TAC[satisfies0_def] THEN DISCH_TAC THEN
  X_GEN_TAC `v:(mlstring->U)#(mlstring#hol_type->U)` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tyenv:tysig`; `tyenv':tysig`;
                 `FST (i:(mlstring->U list->U)#(mlstring->U list->U))`;
                 `v:(mlstring->U)#(mlstring#hol_type->U)`]
    (UNDISCH is_valuation_extend_sig)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `v':(mlstring->U)#(mlstring#hol_type->U)` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!tm. hol_term_ok (tyenv,tmenv) tm
         ==> termsem0 (mem:U->U->bool) tmenv' i v' tm = termsem0 mem tmenv i v tm`
   ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    TRANS_TAC EQ_TRANS `termsem0 (mem:U->U->bool) tmenv' i v tm` THEN CONJ_TAC THENL
     [MATCH_MP_TAC termsem_frees THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[term_ok_welltyped]; ALL_TAC] THEN
      REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `type_ok (tyenv:tysig) ty` (fun th -> ASM_MESON_TAC[th]) THEN
      MP_TAC(SPECL [`tm:hol_term`; `ty:hol_type`] (MATCH_MP type_ok_types_in
        (ASSUME `is_std_sig (tyenv:tysig,tmenv:tmsig)`))) THEN
      REWRITE_TAC[FST] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP VFREE_IN_types_in) THEN REWRITE_TAC[typeof_def];
      MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM] termsem_extend) THEN
      EXISTS_TAC `tyenv:tysig` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ALL; GSYM ALL_MEM]) THEN
  SUBGOAL_THEN `termsem0 (mem:U->U->bool) tmenv' i v' c = setSpec_true mem` MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ASM_MESON_TAC[]]);;

let models_reduce = prove
 (`is_set_theory (mem:U->U->bool) ==>
   !i tyenv tmenv axs tyenv' tmenv' axs'.
     is_std_sig (tyenv,tmenv) /\
     tyenv SUBMAP tyenv' /\ tmenv SUBMAP tmenv' /\ axs SUBSET axs' /\
     models0 mem i ((tyenv',tmenv'),axs') /\
     (!p. p IN axs ==> hol_term_ok (tyenv,tmenv) p)
     ==> models0 mem i ((tyenv,tmenv),axs)`,
  REPEAT STRIP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[models0_def]) THEN
  REWRITE_TAC[models0_def] THEN FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[is_interpretation_reduce]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(UNDISCH satisfies_reduce) THEN
  MAP_EVERY EXISTS_TAC [`tyenv':tysig`; `tmenv':tmsig`] THEN
  ASM_REWRITE_TAC[ALL] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[is_interpretation0_def; SUBSET]) THEN ASM_MESON_TAC[]);;
