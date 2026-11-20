(* ========================================================================= *)
(* typeSound: port of HOL4 semantics/proofs/typeSoundScript.sml              *)
(* (CakeML v3479).  Proof of type soundness: a type-correct program does not *)
(* crash.                                                                    *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/typeSystem.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/fpSem.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/proofs/namespaceProps.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/proofs/evaluateProps.ml";;
needs "semantics/proofs/weakening.ml";;
needs "semantics/proofs/typeSysProps.ml";;
needs "semantics/proofs/typeSoundInvariants.ml";;
needs "semantics/semantics.ml";;
needs "semantics/proofs/primSemEnv.ml";;

type_invention_error := true;;

(* HOL4's ML value type_num_defs: the definitions of the type numbers *)
let TPROPSAUX_type_num_defs =
  [typeSystem_Tarray_num_def; typeSystem_Tbool_num_def; typeSystem_Tchar_num_def;
   typeSystem_Texn_num_def; typeSystem_Tfn_num_def; typeSystem_Tint_num_def;
   typeSystem_Tlist_num_def; typeSystem_Tref_num_def; typeSystem_Tstring_num_def;
   typeSystem_Ttup_num_def; typeSystem_Tvector_num_def; typeSystem_Tword64_num_def;
   typeSystem_Tword8_num_def; typeSystem_Tword8array_num_def;
   typeSystem_Tdouble_num_def];;

let list_rel_flat = prove
 (`!R:A->B->bool l1 l2. ALL2 (ALL2 R) l1 l2 ==> ALL2 R (FLAT l1) (FLAT l2)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `l2:(B list)list` list_CASES) THEN
  REWRITE_TAC[ALL2; FLAT] THEN STRIP_TAC THEN
  MATCH_MP_TAC EVERY2_APPEND_suff THEN ASM_SIMP_TAC[]);;

let fst_triple = prove
 (CASE_TERM `(\p. match p with (x,y,z) -> x) = (FST:A#B#C->A)`,
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM] THEN CASE_REWRITE_TAC[]);;

let disjoint_image = prove
 (`!s1 s2 (f:A->B). DISJOINT (IMAGE f s1) (IMAGE f s2) ==> DISJOINT s1 s2`,
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_IMAGE; NOT_IN_EMPTY] THEN MESON_TAC[]);;

let sing_list = prove
 (`!l:A list. LENGTH l = 1 <=> ?x. l = [x]`,
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `l:A list` list_CASES) THEN
  REWRITE_TAC[LENGTH; NOT_CONS_NIL; CONS_11; ARITH_RULE `~(0 = 1)`;
              ARITH_RULE `SUC n = 1 <=> n = 0`; LENGTH_EQ_NIL] THEN
  MESON_TAC[]);;

(* HOL4: EVERY_LIST_REL (local; HOL4 rebinds the name below) *)
let TPROPSAUX_EVERY_LIST_REL = prove
 (`ALL (\x. (f:A->B->bool) x y) l = ALL2 (\x y. f x y) l (REPLICATE (LENGTH l) y)`,
  SPEC_TAC(`l:A list`,`l:A list`) THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[ALL; ALL2; LENGTH; REPLICATE]);;

let v_unchanged = prove
 (`!tenv (x:A). type_env_v_fupd (K (type_env_v tenv)) tenv = tenv`,
  REWRITE_TAC[type_env_component_equality; type_env_INFO.ri_accfupds; K_THM]);;
let _ = cake_add_simps [v_unchanged];;

let check_dup_ctors_thm = prove
 (`check_dup_ctors (tvs,tn,condefs) <=> ALL_DISTINCT (MAP FST condefs)`,
  REWRITE_TAC[check_dup_ctors_def; LET_DEF; LET_END_DEF] THEN AP_TERM_TAC THEN
  SPEC_TAC(`condefs:(mlstring#ast_t list)list`,`l:(mlstring#ast_t list)list`) THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ITLIST; MAP] THEN
  SPEC_TAC(`h:mlstring#ast_t list`,`h:mlstring#ast_t list`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[]);;
(* the type abbreviations and type numbers, with the constructor theorems  *)
(* of t: decides equations between primitive types                        *)
let TPROPSAUX_TYEQS =
  [typeSystem_Tarray_def; typeSystem_Tbool_def; typeSystem_Tchar_def;
   typeSystem_Texn_def; typeSystem_Tfn_def; typeSystem_Tint_def; typeSystem_Tlist_def;
   typeSystem_Tref_def; typeSystem_Tstring_def; typeSystem_Ttup_def;
   typeSystem_Tvector_def; typeSystem_Tword64_def; typeSystem_Tword8_def;
   typeSystem_Tword8array_def; typeSystem_Tdouble_def; injectivity "t";
   distinctness "t"; CONS_11; NOT_CONS_NIL; distinctness "list"; ARITH_EQ] @
  TPROPSAUX_type_num_defs;;

(* what ctMap_ok says about one entry *)
let TPROPSAUX_ctMap_ok_FLOOKUP = prove
 (`!ctMap stamp tvs ts ti.
     ctMap_ok ctMap /\ FLOOKUP ctMap stamp = SOME (tvs,ts,ti)
     ==> (?ex. stamp = ExnStamp ex /\ tvs = [] /\ ti = Texn_num) \/
         (?cn x. stamp = TypeStamp cn x /\ ~MEM ti prim_type_nums)`,
  REWRITE_TAC[ctMap_ok_def] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  CASES_ON `stamp:stamp` THEN ASM_MESON_TAC[]);;

(* adds the facts TPROPSAUX_ctMap_ok_FLOOKUP for every FLOOKUP assumption *)
let TPROPSAUX_CTMAP_TAC : tactic = fun (asl,w as gl) ->
  let isc s th =
    try fst(dest_const(fst(strip_comb(concl th)))) = s with Failure _ -> false in
  let oks = filter (isc "ctMap_ok") (map snd asl) in
  let ths = List.concat (map (fun ok -> mapfilter (fun (_,fl) ->
              MATCH_MP TPROPSAUX_ctMap_ok_FLOOKUP (CONJ ok fl)) asl) oks) in
  MAP_EVERY STRIP_ASSUME_TAC ths gl;;

(* closes a goal by rewriting the assumptions with thl to F *)
let TPROPSAUX_CONTR_TAC thl =
  RULE_ASSUM_TAC(REWRITE_RULE thl) THEN FIRST_ASSUM CONTR_TAC;;
(* closes goals with an impossible type_v case: a constructor of a        *)
(* primitive type, or a recursive closure of a non-function type           *)
let TPROPSAUX_NEG_TAC : tactic =
  (TPROPSAUX_CTMAP_TAC THEN
   TPROPSAUX_CONTR_TAC (TPROPSAUX_TYEQS @
     [prim_type_nums_def; MEM; distinctness "stamp"; injectivity "stamp"])) ORELSE
  (IMP_RES_TAC type_funs_Tfn THEN TPROPSAUX_CONTR_TAC TPROPSAUX_TYEQS);;

let TPROPSAUX_type_s_FLOOKUP = prove
 (`!ctMap envS tenvS n st.
     type_s ctMap envS tenvS /\ FLOOKUP tenvS n = SOME st
     ==> ?sv. store_lookup n envS = SOME sv /\ type_sv ctMap tenvS sv st`,
  REWRITE_TAC[type_s_def] THEN MESON_TAC[]);;
(* the store cases of prim_canonical_values_thm *)
let TPROPSAUX_PCV_STORE_TAC : tactic =
  FIRST_ASSUM(fun fl ->
    FIRST_ASSUM(fun ts ->
      let th = MATCH_MP TPROPSAUX_type_s_FLOOKUP (CONJ ts fl) in
      X_CHOOSE_THEN `sv:v store_v` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) th)) THEN
  CASES_ON `sv:v store_v` THEN REWRITE_TAC[type_sv_def] THEN
  ASM_MESON_TAC[];;

(* the case analysis of prim_canonical_values_thm *)
let TPROPSAUX_PCV_TAC : tactic =
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o ONCE_REWRITE_RULE[type_v_cases])
    STRIP_ASSUME_TAC) THEN
  REWRITE_TAC TPROPSAUX_TYEQS THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  TRY TPROPSAUX_NEG_TAC;;

(* HOL4's statement has tvs ctMap tenvS v ts t1 t2 t envS free *)
let prim_canonical_values_thm = prove
 (`(type_v tvs ctMap tenvS v Tint /\ ctMap_ok ctMap ==> ?n. v = Litv (IntLit n)) /\
   (type_v tvs ctMap tenvS v Tchar /\ ctMap_ok ctMap ==> ?c. v = Litv (Char c)) /\
   (type_v tvs ctMap tenvS v Tstring /\ ctMap_ok ctMap ==> ?s. v = Litv (StrLit s)) /\
   (type_v tvs ctMap tenvS v Tword8 /\ ctMap_ok ctMap ==> ?n. v = Litv (Word8 n)) /\
   (type_v tvs ctMap tenvS v Tword64 /\ ctMap_ok ctMap ==> ?n. v = Litv (Word64 n)) /\
   (type_v tvs ctMap tenvS v Tdouble /\ ctMap_ok ctMap ==> ?n. v = Litv (Float64 n)) /\
   (type_v tvs ctMap tenvS v (Ttup ts) /\ ctMap_ok ctMap
    ==> ?vs. v = Conv NONE vs /\ LENGTH ts = LENGTH vs) /\
   (type_v tvs ctMap tenvS v (Tfn t1 t2) /\ ctMap_ok ctMap
    ==> (?env n e. v = Closure env n e) \/ (?env funs n. v = Recclosure env funs n)) /\
   (type_v tvs ctMap tenvS v (Tref t1) /\ ctMap_ok ctMap /\ type_s ctMap envS tenvS
    ==> ?n v2. v = Loc T n /\ store_lookup n envS = SOME (Refv v2) /\
               type_v 0 ctMap tenvS v2 t1) /\
   (type_v tvs ctMap tenvS v Tword8array /\ ctMap_ok ctMap /\ type_s ctMap envS tenvS
    ==> ?n ws. v = Loc T n /\ store_lookup n envS = SOME (W8array ws) /\
               FLOOKUP tenvS n = SOME W8array_t) /\
   (type_v tvs ctMap tenvS v (Tarray t) /\ ctMap_ok ctMap /\ type_s ctMap envS tenvS
    ==> ?n vs. v = Loc T n /\ store_lookup n envS = SOME (Varray vs) /\
               ALL (\v. type_v 0 ctMap tenvS v t) vs /\
               FLOOKUP tenvS n = SOME (Varray_t t)) /\
   (type_v tvs ctMap tenvS v (Tvector t) /\ ctMap_ok ctMap
    ==> ?vs. v = Vectorv vs /\ ALL (\v. type_v tvs ctMap tenvS v t) vs)`,
  REPEAT CONJ_TAC THEN TPROPSAUX_PCV_TAC THEN
  (TPROPSAUX_PCV_STORE_TAC ORELSE ASM_MESON_TAC[LIST_REL_LENGTH]));;

let TPROPSAUX_head_is s tm =
  try fst(dest_const(fst(strip_comb tm))) = s with Failure _ -> false;;

(* HOL4 qpat_x_assum `c _ ..` mp_tac for a constant c *)
let TPROPSAUX_POP s = FIRST_X_ASSUM(MP_TAC o check (TPROPSAUX_head_is s o concl));;

(* HOL4 has v free; HOL4 measureInduct_on is WF_INDUCT_TAC *)
let has_lists_v_to_list = prove
 (`!ctMap tvs tenvS t3.
     ctMap_ok ctMap /\ ctMap_has_lists ctMap /\ type_v tvs ctMap tenvS v (Tlist t3)
     ==> ?vs. v_to_list v = SOME vs /\
              ALL (\v. type_v tvs ctMap tenvS v t3) vs /\
              (t3 = Tchar ==> ?vs. v_to_char_list v = SOME vs) /\
              (t3 = Tstring ==> ?str. vs_to_string vs = SOME str)`,
  WF_INDUCT_TAC `v_size v` THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (MP_TAC o REWRITE_RULE TPROPSAUX_TYEQS o ONCE_REWRITE_RULE[type_v_cases]))) THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN TRY TPROPSAUX_NEG_TAC THEN
  SUBGOAL_THEN `?cn. stamp = TypeStamp cn list_type_num` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `same_type stamp (TypeStamp (implode "[]") list_type_num)` MP_TAC THENL
     [UNDISCH_TAC `ctMap_ok ctMap` THEN REWRITE_TAC[ctMap_ok_def] THEN
      DISCH_THEN(MATCH_MP_TAC o last o CONJUNCTS) THEN
      MAP_EVERY EXISTS_TAC [`tvs':mlstring list`; `ts:t list`; `6`;
                            `[implode "'a"]`; `[]:t list`] THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `ctMap_has_lists ctMap` THEN
      SIMP_TAC (ctMap_has_lists_def :: TPROPSAUX_type_num_defs);
      CASES_ON `stamp:stamp` THEN REWRITE_TAC[same_type_def] THEN MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `cn = implode "::" \/ cn = implode "[]"` MP_TAC THENL
   [UNDISCH_TAC `ctMap_has_lists ctMap` THEN REWRITE_TAC[ctMap_has_lists_def] THEN
    ASM_MESON_TAC[option_DISTINCT];
    ALL_TAC] THEN
  STRIP_TAC THEN RVEQ_TAC THENL
   [SUBGOAL_THEN `tvs' = [implode "'a"] /\
                  ts = [Tvar (implode "'a"); Tlist (Tvar (implode "'a"))]`
      STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `ctMap_has_lists ctMap` THEN REWRITE_TAC[ctMap_has_lists_def] THEN
      ASM_REWRITE_TAC[injectivity "option"; PAIR_EQ] THEN MESON_TAC[]; ALL_TAC] THEN
    RVEQ_TAC THEN TPROPSAUX_POP "ALL2" THEN
    REWRITE_TAC[ZIP; REVERSE; APPEND; FUPDATE_LIST_THM; MAP; type_subst_def;
                FLOOKUP_UPDATE; typeSystem_Tlist_def] THEN
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[LIST_REL_CONS2; LIST_REL_NIL] THEN
    STRIP_TAC THEN RVEQ_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `h'':v`) THEN
    ANTS_TAC THENL [REWRITE_TAC[type_size_def "v"] THEN ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL [`ctMap:ctMap`; `tvs:num`; `tenvS:tenv_store`; `t3:t`]) THEN
    ASM_REWRITE_TAC[typeSystem_Tlist_def] THEN STRIP_TAC THEN
    EXISTS_TAC `CONS (h':v) vs` THEN
    ASM_REWRITE_TAC[v_to_list_def; ALL] THEN CASE_REWRITE_TAC[] THEN
    CONJ_TAC THEN DISCH_TAC THEN RVEQ_TAC THEN
    MAP_EVERY IMP_RES_TAC (CONJUNCTS prim_canonical_values_thm) THEN RVEQ_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_exists o concl)) THEN
    ASM_REWRITE_TAC[v_to_char_list_def; vs_to_string_def] THEN CASE_REWRITE_TAC[] THEN
    MESON_TAC[];
    SUBGOAL_THEN `tvs' = [implode "'a"] /\ ts = []:t list` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `ctMap_has_lists ctMap` THEN REWRITE_TAC[ctMap_has_lists_def] THEN
      ASM_REWRITE_TAC[injectivity "option"; PAIR_EQ] THEN MESON_TAC[]; ALL_TAC] THEN
    RVEQ_TAC THEN TPROPSAUX_POP "ALL2" THEN REWRITE_TAC[MAP; LIST_REL_NIL] THEN
    DISCH_THEN SUBST1_TAC THEN EXISTS_TAC `[]:v list` THEN
    REWRITE_TAC[v_to_list_def; v_to_char_list_def; vs_to_string_def; ALL] THEN
    MESON_TAC[]]);;

(* HOL4 qpat_x_assum `pat` mp_tac *)
let TPROPSAUX_POP_MATCH pat =
  FIRST_X_ASSUM(MP_TAC o check (can (term_match [] pat) o concl));;

(* the last conjunct of ctMap_ok_def *)
let TPROPSAUX_ctMap_ok_same_type = prove
 (`!ctMap s1 s2 tvs1 ts1 ti tvs2 ts2.
     ctMap_ok ctMap /\ FLOOKUP ctMap s1 = SOME (tvs1,ts1,ti) /\
     FLOOKUP ctMap s2 = SOME (tvs2,ts2,ti)
     ==> same_type s1 s2`,
  REWRITE_TAC[ctMap_ok_def] THEN MESON_TAC[]);;

let TPROPSAUX_same_type_TypeStamp = prove
 (`!s cn n. same_type s (TypeStamp cn n) <=> ?cn'. s = TypeStamp cn' n`,
  GEN_TAC THEN CASES_ON `s:stamp` THEN
  REWRITE_TAC[same_type_def; injectivity "stamp"; distinctness "stamp"] THEN MESON_TAC[]);;

let TPROPSAUX_same_type_ExnStamp = prove
 (`!s n. same_type s (ExnStamp n) <=> ?n'. s = ExnStamp n'`,
  GEN_TAC THEN CASES_ON `s:stamp` THEN
  REWRITE_TAC[same_type_def; injectivity "stamp"; distinctness "stamp"] THEN MESON_TAC[]);;

(* a goal type_v .. v t /\ .. ==> ..: the cases of type_v for v, with the  *)
(* primitive types decided and the impossible cases closed                  *)
let TPROPSAUX_TYPE_V_CASES_TAC : tactic =
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o REWRITE_RULE TPROPSAUX_TYEQS o
                              ONCE_REWRITE_RULE[type_v_cases]) STRIP_ASSUME_TAC) THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN TRY TPROPSAUX_NEG_TAC;;

(* a recursive closure has a function type *)
let TPROPSAUX_TFN_TAC : tactic =
  IMP_RES_TAC type_funs_Tfn THEN RULE_ASSUM_TAC(REWRITE_RULE TPROPSAUX_TYEQS) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_exists o concl))) THEN RVEQ_TAC;;

(* HOL4's statement has tvs ctMap tenvS v t ts ti stamp tvs' ts' free *)
let ctor_canonical_values_thm = prove
 (`(type_v tvs ctMap tenvS v Tbool /\ ctMap_ok ctMap /\ ctMap_has_bools ctMap
    ==> ?b. v = Boolv b) /\
   (type_v tvs ctMap tenvS v (Tlist t) /\ ctMap_ok ctMap /\ ctMap_has_lists ctMap
    ==> ?vs. v_to_list v = SOME vs /\ ALL (\v. type_v tvs ctMap tenvS v t) vs /\
             (t = Tchar ==> ?vs. v_to_char_list v = SOME vs) /\
             (t = Tstring ==> ?str. vs_to_string vs = SOME str)) /\
   (type_v tvs ctMap tenvS v (Tapp ts ti) /\ ctMap_ok ctMap /\
    FLOOKUP ctMap stamp = SOME (tvs',ts',ti)
    ==> (?cn n vs. same_type stamp (TypeStamp cn n) /\
                   v = Conv (SOME (TypeStamp cn n)) vs) \/
        (?n vs. same_type stamp (ExnStamp n) /\ v = Conv (SOME (ExnStamp n)) vs))`,
  REPEAT CONJ_TAC THENL
   [TPROPSAUX_TYPE_V_CASES_TAC THEN
    UNDISCH_TAC `ctMap_has_bools ctMap` THEN
    REWRITE_TAC[ctMap_has_bools_def; typeSystem_Tbool_num_def] THEN STRIP_TAC THEN
    SUBGOAL_THEN `same_type stamp (TypeStamp (implode "True") bool_type_num)` MP_TAC THENL
     [ASM_MESON_TAC[TPROPSAUX_ctMap_ok_same_type]; ALL_TAC] THEN
    REWRITE_TAC[TPROPSAUX_same_type_TypeStamp] THEN STRIP_TAC THEN RVEQ_TAC THEN
    SUBGOAL_THEN `cn' = implode "True" \/ cn' = implode "False"` MP_TAC THENL
     [ASM_MESON_TAC[option_DISTINCT]; ALL_TAC] THEN
    STRIP_TAC THEN RVEQ_TAC THEN
    (SUBGOAL_THEN `tvs' = []:mlstring list /\ ts = []:t list` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[injectivity "option"; PAIR_EQ]; ALL_TAC]) THEN RVEQ_TAC THEN
    TPROPSAUX_POP "ALL2" THEN REWRITE_TAC[MAP; LIST_REL_NIL] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[semanticPrimitives_Boolv_def] THEN
    ((EXISTS_TAC `T` THEN REWRITE_TAC[] THEN NO_TAC) ORELSE
     (EXISTS_TAC `F` THEN REWRITE_TAC[]));
    STRIP_TAC THEN MATCH_MP_TAC (GEN_ALL has_lists_v_to_list) THEN ASM_REWRITE_TAC[];
    TPROPSAUX_TYPE_V_CASES_TAC THENL
     [SUBGOAL_THEN `same_type stamp stamp'` MP_TAC THENL
       [ASM_MESON_TAC[TPROPSAUX_ctMap_ok_same_type]; ALL_TAC] THEN
      CASES_ON `stamp':stamp` THEN REWRITE_TAC[injectivity "v"; injectivity "option"] THEN
      MESON_TAC[];
      TPROPSAUX_TFN_TAC THEN TPROPSAUX_NEG_TAC]]);;

let same_type_refl = prove
 (`!t. same_type t t`,
  GEN_TAC THEN CASES_ON `t:stamp` THEN REWRITE_TAC[same_type_def]);;

(* split conjunctive assumptions, eliminate variable equations, decide     *)
(* equations between types; close the goal on an F assumption              *)
let TPROPSAUX_NORM_TAC : tactic =
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE TPROPSAUX_TYEQS) THEN
  TRY (FIRST_ASSUM CONTR_TAC);;

(* the cases of type_v for every assumption type_v .. (C ..) t *)
let TPROPSAUX_TV_ASM_CASES_TAC : tactic =
  REPEAT (FIRST_X_ASSUM (fun th ->
    let c = concl th in
    if TPROPSAUX_head_is "type_v" c && not (is_var (rand (rator c))) then
      MP_TAC (REWRITE_RULE (TPROPSAUX_TYEQS @
                [distinctness "v"; injectivity "v"; distinctness "lit"; injectivity "lit"])
                (ONCE_REWRITE_RULE[type_v_cases] th))
    else NO_TAC)) THEN
  REPEAT STRIP_TAC THEN TPROPSAUX_NORM_TAC THEN TPROPSAUX_NORM_TAC;;

(* rewrite every assumption with the boolean variables among them *)
let TPROPSAUX_BOOL_VARS_TAC : tactic = fun (asl,w as gl) ->
  let bs = filter (fun (_,th) -> is_var (concl th)) asl in
  (RULE_ASSUM_TAC (REWRITE_RULE (map snd bs))) gl;;

(* HOL4 EVERY_LIST_REL for any relation *)
let TPROPSAUX_ALL_REPLICATE = prove
 (`!(R:A->B->bool) y l. ALL (\x. R x y) l <=> ALL2 R l (REPLICATE (LENGTH l) y)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[ALL; ALL2; LENGTH; REPLICATE]);;

(* the cases of eq_same_type that need no induction hypothesis *)
let TPROPSAUX_EQ1_TAC : tactic =
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[do_eq_def; distinctness "eq_result"]) THEN
  TRY (FIRST_ASSUM CONTR_TAC) THEN
  TPROPSAUX_TV_ASM_CASES_TAC THEN
  TRY TPROPSAUX_NEG_TAC THEN
  TRY (TPROPSAUX_TFN_TAC THEN TPROPSAUX_NEG_TAC) THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[do_eq_def; lit_same_type_def; ctor_same_type_def;
                                   distinctness "eq_result"]) THEN
  TRY (FIRST_ASSUM CONTR_TAC);;

(* HOL4 has the unused variables cns (of a type variable) *)
let eq_same_type = prove
 (`(!v1 v2 tvs ctMap (cns:A) tenvS t.
      ctMap_ok ctMap /\ type_v tvs ctMap tenvS v1 t /\ type_v tvs ctMap tenvS v2 t
      ==> ~(do_eq v1 v2 = Eq_type_error)) /\
   (!vs1 vs2 tvs ctMap (cns:A) tenvS ts.
      ctMap_ok ctMap /\ ALL2 (type_v tvs ctMap tenvS) vs1 ts /\
      ALL2 (type_v tvs ctMap tenvS) vs2 ts
      ==> ~(do_eq_list vs1 vs2 = Eq_type_error))`,
  let loc_tac =
    TPROPSAUX_BOOL_VARS_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[distinctness "eq_result"]) THEN
    FIRST_ASSUM CONTR_TAC in
  (MATCH_MP_TAC do_eq_ind THEN REPEAT CONJ_TAC THEN TPROPSAUX_EQ1_TAC) THENL
   [loc_tac; loc_tac; loc_tac;
    (* two constructors *)
    SUBGOAL_THEN `same_type stamp stamp'` ASSUME_TAC THENL
     [ASM_MESON_TAC[TPROPSAUX_ctMap_ok_same_type]; ALL_TAC] THEN
    TPROPSAUX_POP_MATCH `(if a then b else c) = Eq_type_error` THEN
    ASM_CASES_TAC `stamp:stamp = stamp' /\ LENGTH (vs:v list) = LENGTH (vs':v list)` THEN
    ASM_REWRITE_TAC[distinctness "eq_result"] THEN
    FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC) THEN RVEQ_TAC THEN
    SUBGOAL_THEN `tvs'':mlstring list = tvs' /\ ts''':t list = ts` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[injectivity "option"; PAIR_EQ]; ALL_TAC] THEN RVEQ_TAC THEN
    ASM_MESON_TAC[];
    (* two tuples *)
    TPROPSAUX_POP_MATCH `(if a then b else c) = Eq_type_error` THEN
    ASM_CASES_TAC `LENGTH (vs:v list) = LENGTH (vs':v list)` THEN
    ASM_REWRITE_TAC[distinctness "eq_result"] THEN ASM_MESON_TAC[];
    (* two vectors *)
    TPROPSAUX_POP_MATCH `(if a then b else c) = Eq_type_error` THEN
    ASM_CASES_TAC `LENGTH (vs:v list) = LENGTH (vs':v list)` THEN
    ASM_REWRITE_TAC[distinctness "eq_result"] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[TPROPSAUX_ALL_REPLICATE; ETA_AX]) THEN
    FIRST_X_ASSUM(fun th ->
      MP_TAC (MP th (ASSUME `LENGTH (vs:v list) = LENGTH (vs':v list)`))) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
      concl th = `LENGTH (vs:v list) = LENGTH (vs':v list)`)) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`tvs:num`; `ctMap:ctMap`; `tenvS:tenv_store`;
                          `REPLICATE (LENGTH (vs':v list)) (t':t)`] THEN
    ASM_REWRITE_TAC[];
    (* do_eq_list on two non-empty lists *)
    RULE_ASSUM_TAC(REWRITE_RULE[LIST_REL_CONS1]) THEN
    REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_exists o concl))) THEN RVEQ_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ALL2; CONS_11]) THEN TPROPSAUX_NORM_TAC THEN
    SUBGOAL_THEN `~(do_eq v1 v2 = Eq_type_error)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC (ISPEC `do_eq v1 v2` (cases "eq_result")) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_TAC `r:bool`) THEN
    TPROPSAUX_POP_MATCH `(x:eq_result) = Eq_type_error` THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    ASM_CASES_TAC `r:bool` THEN ASM_REWRITE_TAC[distinctness "eq_result"] THEN
    ASM_MESON_TAC[]]);;

(* HOL4 has the unused variables tn and cn' (of type variables) *)
let type_env_conv_thm = prove
 (`!ctMap (envC:(M,N,num#stamp)namespace)
          (tenvC:(M,N,mlstring list#t list#num)namespace).
     nsAll2 (type_ctor ctMap) envC tenvC
     ==> !cn tvs ts (tn:A) ti.
           (nsLookup tenvC cn = SOME (tvs,ts,ti)
            ==> ?(cn':B) stamp. nsLookup envC cn = SOME (LENGTH ts,stamp) /\
                                FLOOKUP ctMap stamp = SOME (tvs,ts,ti)) /\
           (nsLookup tenvC cn = NONE ==> nsLookup envC cn = NONE)`,
  REPEAT STRIP_TAC THENL
   [MP_TAC(ISPECL [`type_ctor ctMap:(M,N)id->num#stamp->mlstring list#t list#num->bool`;
                   `envC:(M,N,num#stamp)namespace`;
                   `tenvC:(M,N,mlstring list#t list#num)namespace`;
                   `cn:(M,N)id`; `(tvs,ts,ti):mlstring list#t list#num`]
                  nsAll2_nsLookup2) THEN
    ASM_REWRITE_TAC[EXISTS_PAIR_THM; type_ctor_def] THEN MESON_TAC[];
    ASM_MESON_TAC[nsAll2_nsLookup_none]]);;

let type_funs_fst = prove
 (`!tenv tenvE funs tenv'.
     type_funs tenv tenvE funs tenv' ==> MAP FST funs = MAP FST tenv'`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN GEN_TAC THENL
   [REWRITE_TAC[TPROPSAUX_type_funs_cases] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[MAP];
    SPEC_TAC(`h:mlstring#mlstring#exp`,`h:mlstring#mlstring#exp`) THEN
    REWRITE_TAC[FORALL_PAIR_THM; TPROPSAUX_type_funs_cases] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[MAP; CONS_11; FST] THEN ASM_MESON_TAC[]]);;

(* the type_v rule of recursive closures *)
let TPROPSAUX_type_v_Recclosure = el 9 (CONJUNCTS type_v_rules);;

(* HOL4 has the unused variable fn (of a type variable) *)
let type_recfun_env_help = prove
 (CASE_TERM `!(fn:A) funs funs' ctMap tenv bindings tenvE env tenvS tvs bindings'.
     ALL_DISTINCT (MAP FST funs') /\
     tenv_ok tenv /\
     type_all_env ctMap tenvS env
       (type_env_v_fupd (K (add_tenvE tenvE (type_env_v tenv))) tenv) /\
     tenv_val_exp_ok tenvE /\
     num_tvs tenvE = 0 /\
     (!fn t. ALOOKUP bindings fn = SOME t ==> ALOOKUP bindings' fn = SOME t) /\
     type_funs tenv (bind_var_list 0 bindings' (bind_tvar tvs tenvE)) funs' bindings' /\
     type_funs tenv (bind_var_list 0 bindings' (bind_tvar tvs tenvE)) funs bindings
     ==> ALL2 (\xy xy'. match xy with (x,y) -> match xy' with (x',y') ->
                 x = x' /\ (\p. match p with (tvs,t) -> type_v tvs ctMap tenvS y t) y')
              (MAP (\p. match p with (fn,n,e) -> (fn,Recclosure env funs' fn)) funs)
              (MAP (\p. match p with (x,t) -> (x,tvs,t)) bindings)`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[TPROPSAUX_type_funs_cases] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[MAP; ALL2];
    SPEC_TAC(`h:mlstring#mlstring#exp`,`h:mlstring#mlstring#exp`) THEN
    REWRITE_TAC[FORALL_PAIR_THM; TPROPSAUX_type_funs_cases] THEN
    REPEAT STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[MAP; ALL2] THEN CASE_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC TPROPSAUX_type_v_Recclosure THEN
      MAP_EVERY EXISTS_TAC [`tenv:type_env`; `tenvE:tenv_val_exp`;
                            `bindings':(mlstring#t)list`] THEN
      TPROPSAUX_POP "type_all_env" THEN
      REWRITE_TAC[type_all_env_def; type_env_INFO.ri_accfupds; K_THM] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `ALOOKUP (bindings':(mlstring#t)list) p1 = SOME (Tfn t1 t2)`
        ASSUME_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[ALOOKUP_THM]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      IMP_RES_TAC type_funs_fst THEN ASM_REWRITE_TAC[] THEN
      IMP_RES_TAC ALOOKUP_MEM THEN REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM] THEN
      ASM_MESON_TAC[FST];
      FIRST_X_ASSUM(MATCH_MP_TAC o BETA_RULE) THEN
      MAP_EVERY EXISTS_TAC [`tenv:type_env`; `tenvE:tenv_val_exp`;
                            `bindings':(mlstring#t)list`] THEN
      ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[ALOOKUP_THM] THEN
      COND_CASES_TAC THEN ASM_MESON_TAC[option_DISTINCT]]]);;

let type_recfun_env = prove
 (CASE_TERM `!funs ctMap tenvS tvs tenv tenvE env bindings.
     tenv_ok tenv /\
     type_all_env ctMap tenvS env
       (type_env_v_fupd (K (add_tenvE tenvE (type_env_v tenv))) tenv) /\
     tenv_val_exp_ok tenvE /\
     num_tvs tenvE = 0 /\
     type_funs tenv (bind_var_list 0 bindings (bind_tvar tvs tenvE)) funs bindings /\
     ALL_DISTINCT (MAP FST funs)
     ==> ALL2 (\xy xy'. match xy with (x,y) -> match xy' with (x',y') ->
                 x = x' /\ (\p. match p with (tvs,t) -> type_v tvs ctMap tenvS y t) y')
              (MAP (\p. match p with (fn,n,e) -> (fn,Recclosure env funs fn)) funs)
              (MAP (\p. match p with (x,t) -> (x,tvs,t)) bindings)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`ARB:num`; `funs:(mlstring#mlstring#exp)list`;
                 `funs:(mlstring#mlstring#exp)list`; `ctMap:ctMap`; `tenv:type_env`;
                 `bindings:(mlstring#t)list`; `tenvE:tenv_val_exp`; `env:v sem_env`;
                 `tenvS:tenv_store`; `tvs:num`; `bindings:(mlstring#t)list`]
                type_recfun_env_help) THEN
  ASM_REWRITE_TAC[]);;

(* the type_v rule of constructor values *)
let TPROPSAUX_type_v_Conv = el 6 (CONJUNCTS type_v_rules);;

(* HOL4: the ML value type_v_exn (SIMP_RULE of a Q.prove) *)
let TPROPSAUX_type_v_exn = prove
 (`!tvs cenv senv.
     ctMap_has_exns cenv
     ==> type_v tvs cenv senv (Conv (SOME chr_stamp) []) Texn /\
         type_v tvs cenv senv (Conv (SOME subscript_stamp) []) Texn /\
         type_v tvs cenv senv (Conv (SOME bind_stamp) []) Texn /\
         type_v tvs cenv senv (Conv (SOME div_stamp) []) Texn`,
  REWRITE_TAC[ctMap_has_exns_def; typeSystem_Texn_def] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC TPROPSAUX_type_v_Conv THEN
  MAP_EVERY EXISTS_TAC [`[]:mlstring list`; `[]:t list`] THEN
  ASM_REWRITE_TAC[ALL; LENGTH; ALL2; MAP]);;

let type_v_Boolv = prove
 (`ctMap_has_bools ctMap ==> type_v tvs ctMap tenvS (Boolv b) Tbool`,
  REWRITE_TAC[ctMap_has_bools_def; semanticPrimitives_Boolv_def; typeSystem_Tbool_def] THEN
  STRIP_TAC THEN COND_CASES_TAC THEN
  MATCH_MP_TAC TPROPSAUX_type_v_Conv THEN
  MAP_EVERY EXISTS_TAC [`[]:mlstring list`; `[]:t list`] THEN
  ASM_REWRITE_TAC[ALL; LENGTH; ALL2; MAP]);;

(* HOL4: remove_lambda_prod (local; the same as typeSysProps' one) *)
let typeSound_remove_lambda_prod = remove_lambda_prod;;

(* the cases of type_v for the assumption type_v .. v t of the given v *)
let TPROPSAUX_TV_CASES_ON (v:term) : tactic =
  FIRST_X_ASSUM (fun th ->
    let c = concl th in
    if TPROPSAUX_head_is "type_v" c && rand (rator c) = v then
      MP_TAC (REWRITE_RULE (TPROPSAUX_TYEQS @
                [distinctness "v"; injectivity "v"; distinctness "lit"; injectivity "lit"])
                (ONCE_REWRITE_RULE[type_v_cases] th))
    else NO_TAC) THEN
  REPEAT STRIP_TAC THEN TPROPSAUX_NORM_TAC THEN TPROPSAUX_NORM_TAC;;

let opapp_type_sound = prove
 (`!ctMap tenvS vs ts t.
     ctMap_ok ctMap /\ type_op Opapp ts t /\ ALL2 (type_v 0 ctMap tenvS) vs ts
     ==> ?env e tenv tenvE.
           tenv_ok tenv /\ tenv_val_exp_ok tenvE /\ num_tvs tenvE = 0 /\
           type_all_env ctMap tenvS env
             (type_env_v_fupd (K (add_tenvE tenvE (type_env_v tenv))) tenv) /\
           type_e tenv tenvE e t /\ do_opapp vs = SOME (env,e)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[type_op_cases; distinctness "op"; injectivity "op"] THEN STRIP_TAC THEN
  RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[LIST_REL_CONS2; LIST_REL_NIL]) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
  TPROPSAUX_NORM_TAC THEN REWRITE_TAC[do_opapp_def] THEN CASE_REWRITE_TAC[] THEN
  TPROPSAUX_TV_CASES_ON `h':v` THEN TRY TPROPSAUX_NEG_TAC THEN CASE_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[bind_tvar_def]) THENL
   [(* a closure *)
    MAP_EVERY EXISTS_TAC [`sem_env_v_fupd (K (nsBind n h'' (sem_env_v env))) (env:v sem_env)`;
                          `e:exp`; `tenv:type_env`; `Bind_name n 0 t1 tenvE`] THEN
    ASM_REWRITE_TAC[tenv_val_exp_ok_def; num_tvs_def; ADD_CLAUSES] THEN
    REWRITE_TAC[type_all_env_def; type_env_INFO.ri_accfupds; sem_env_INFO.ri_accfupds;
                K_THM; add_tenvE_def] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC nsAll2_nsBind THEN ASM_REWRITE_TAC[] THEN
    CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[];
    (* a recursive closure *)
    MP_TAC(ISPECL [`n:mlstring`; `ARB:num`; `funs:(mlstring#mlstring#exp)list`;
                   `bindings:(mlstring#t)list`; `ARB:exp`; `tenv:type_env`;
                   `bind_var_list 0 bindings tenvE`; `Tapp [a0'; t] 4`]
                  type_funs_find_recfun) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `n':mlstring` (X_CHOOSE_TAC `e':exp`)) THEN
    MP_TAC(ISPECL [`n:mlstring`; `funs:(mlstring#mlstring#exp)list`; `n':mlstring`;
                   `e':exp`; `tenv:type_env`; `bind_var_list 0 bindings tenvE`;
                   `bindings:(mlstring#t)list`; `0`; `a0':t`; `t:t`]
                  type_recfun_lookup) THEN
    ASM_REWRITE_TAC[typeSystem_Tfn_def; typeSystem_Tfn_num_def] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC
      [`sem_env_v_fupd (K (nsBind n' h'' (build_rec_env funs env (sem_env_v env))))
         (env:v sem_env)`;
       `e':exp`; `tenv:type_env`; `Bind_name n' 0 a0' (bind_var_list 0 bindings tenvE)`] THEN
    ASM_REWRITE_TAC[tenv_val_exp_ok_def; num_tvs_def; ADD_CLAUSES; num_tvs_bind_var_list] THEN
    REWRITE_TAC[fst_triple] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[type_v_freevars];
      ASM_MESON_TAC[tenv_val_exp_ok_bvl_funs];
      REWRITE_TAC[type_all_env_def; type_env_INFO.ri_accfupds; sem_env_INFO.ri_accfupds;
                  K_THM; add_tenvE_def] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC nsAll2_nsBind THEN CASE_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[build_rec_env_merge; nsAppend_to_nsBindList; add_tenvE_bvl] THEN
      MATCH_MP_TAC nsAll2_nsBindList THEN ASM_REWRITE_TAC[] THEN BETA_TAC THEN
      MATCH_MP_TAC (BETA_RULE type_recfun_env) THEN
      EXISTS_TAC `tenv:type_env` THEN EXISTS_TAC `tenvE:tenv_val_exp` THEN
      ASM_REWRITE_TAC[type_all_env_def; type_env_INFO.ri_accfupds; K_THM; bind_tvar_def]]]);;

let store_type_extension_def = cake_def
  `store_type_extension (tenvS1:(A,B)fmap) (tenvS2:(A,B)fmap) <=>
     ?tenvS'. tenvS2 = FUNION tenvS' tenvS1 /\
              (!l. FLOOKUP tenvS' l = NONE \/ FLOOKUP tenvS1 l = NONE)`;;

let store_type_extension_weakS = prove
 (`!tenvS1 tenvS2. store_type_extension tenvS1 tenvS2 ==> weakS tenvS2 tenvS1`,
  RW[store_type_extension_def; weakS_def; SUBMAP_DEF; FUNION_DEF; IN_UNION] THEN
  FS[FLOOKUP_DEF] THEN ASM_MESON_TAC[]);;

let store_type_extension_refl = prove
 (`!tenvS:(A,B)fmap. store_type_extension tenvS tenvS`,
  RW[store_type_extension_def] THEN EXISTS_TAC `FEMPTY:(A,B)fmap` THEN
  REWRITE_TAC[FUNION_FEMPTY_1; FLOOKUP_EMPTY]);;

let store_type_extension_trans = prove
 (`!s1 s2 s3:(A,B)fmap.
     store_type_extension s1 s2 /\ store_type_extension s2 s3
     ==> store_type_extension s1 s3`,
  RW[store_type_extension_def] THEN
  EXISTS_TAC `FUNION (tenvS'':(A,B)fmap) tenvS'` THEN
  REWRITE_TAC[FUNION_ASSOC; FLOOKUP_FUNION] THEN X_GEN_TAC `l:A` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `l:A`) THEN FIRST_X_ASSUM(MP_TAC o SPEC `l:A`) THEN
  REWRITE_TAC[FLOOKUP_FUNION] THEN
  CASES_ON `FLOOKUP (tenvS'':(A,B)fmap) l` THEN CASES_ON `FLOOKUP (tenvS':(A,B)fmap) l` THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[option_DISTINCT]);;

let store_assign_type_sound = prove
 (`!ctMap tenvS store sv st l.
     type_s ctMap store tenvS /\ FLOOKUP tenvS l = SOME st /\ type_sv ctMap tenvS sv st
     ==> ?store'. store_assign l sv store = SOME store' /\ type_s ctMap store' tenvS`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`ctMap:ctMap`; `store:(v store_v)list`; `tenvS:tenv_store`; `l:num`;
                 `st:store_t`] TPROPSAUX_type_s_FLOOKUP) THEN
  ASM_REWRITE_TAC[store_lookup_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; injectivity "option"] THEN
  DISCH_THEN(X_CHOOSE_THEN `sv0:v store_v` STRIP_ASSUME_TAC) THEN RVEQ_TAC THEN
  SUBGOAL_THEN `store_v_same_type (EL l store) (sv:v store_v)` ASSUME_TAC THENL
   [REPEAT(TPROPSAUX_POP "type_sv") THEN
    SPEC_TAC(`EL l store:v store_v`,`a:v store_v`) THEN GEN_TAC THEN
    CASES_ON `st:store_t` THEN CASES_ON `a:v store_v` THEN CASES_ON `sv:v store_v` THEN
    REWRITE_TAC[type_sv_def; store_v_same_type_def] THEN CASE_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[store_assign_def; injectivity "option"; UNWIND_THM1] THEN
  UNDISCH_TAC `type_s ctMap store tenvS` THEN
  REWRITE_TAC[type_s_def; store_lookup_def; LENGTH_LUPDATE; EL_LUPDATE] THEN
  DISCH_TAC THEN X_GEN_TAC `l':num` THEN FIRST_X_ASSUM(MP_TAC o SPEC `l':num`) THEN
  ASM_CASES_TAC `l':num = l` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[injectivity "option"]);;

let store_alloc_type_sound = prove
 (`!ctMap tenvS store sv st.
     ctMap_ok ctMap /\ type_s ctMap store tenvS /\ type_sv ctMap tenvS sv st
     ==> ?store' tenvS' n.
           store_type_extension tenvS tenvS' /\
           store_alloc sv store = (store',n) /\
           type_s ctMap store' tenvS' /\
           FLOOKUP tenvS' n = SOME st`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `FLOOKUP (tenvS:tenv_store) (LENGTH (store:(v store_v)list)) = NONE`
    ASSUME_TAC THENL
   [UNDISCH_TAC `type_s ctMap store tenvS` THEN
    REWRITE_TAC[type_s_def; store_lookup_def] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o SPEC `LENGTH (store:(v store_v)list)`) THEN
    REWRITE_TAC[LT_REFL; option_DISTINCT] THEN MESON_TAC[cases "option"];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`APPEND store [sv:v store_v]`;
                        `(tenvS:tenv_store) |+ (LENGTH (store:(v store_v)list),st)`;
                        `LENGTH (store:(v store_v)list)`] THEN
  REWRITE_TAC[store_alloc_def; FLOOKUP_UPDATE] THEN CONJ_TAC THENL
   [REWRITE_TAC[store_type_extension_def] THEN
    EXISTS_TAC `FEMPTY |+ (LENGTH (store:(v store_v)list),st:store_t)` THEN
    REWRITE_TAC[fmap_eq_flookup; FLOOKUP_FUNION; FLOOKUP_UPDATE; FLOOKUP_EMPTY] THEN
    CONJ_TAC THEN X_GEN_TAC `l:num` THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[option_CASE] THEN TRY (RVEQ_TAC THEN ASM_REWRITE_TAC[]);
    ALL_TAC] THEN
  UNDISCH_TAC `type_s ctMap store tenvS` THEN REWRITE_TAC[type_s_def] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!sv' st'. type_sv ctMap tenvS sv' st'
                 ==> type_sv ctMap (tenvS |+ (LENGTH (store:(v store_v)list),st)) sv' st'`
    ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC type_sv_weakening THEN
    MAP_EVERY EXISTS_TAC [`ctMap:ctMap`; `tenvS:tenv_store`] THEN
    ASM_SIMP_TAC[weakCT_refl; weakS_bind]; ALL_TAC] THEN
  X_GEN_TAC `l:num` THEN
  REWRITE_TAC[store_lookup_def; LENGTH_APPEND; LENGTH; FLOOKUP_UPDATE] THEN
  ASM_CASES_TAC `l = LENGTH (store:(v store_v)list)` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REWRITE_TAC[EL_APPEND; LT_REFL; SUB_REFL; EL; HD; ARITH_RULE `n < n + SUC 0`] THEN
    REWRITE_TAC[injectivity "option"] THEN CONJ_TAC THENL
     [MESON_TAC[]; REPEAT STRIP_TAC THEN RVEQ_TAC THEN ASM_SIMP_TAC[]];
    SUBGOAL_THEN `l < LENGTH (store:(v store_v)list) + SUC 0 <=> l < LENGTH store`
      SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_SIMP_TAC[EL_APPEND1] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `l:num`) THEN ASM_REWRITE_TAC[store_lookup_def] THEN
    REWRITE_TAC[injectivity "option"; option_DISTINCT] THEN REPEAT STRIP_TAC THEN
    RVEQ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]]);;

let TPROPSAUX_ALL2_2 = prove
 (`!R (a:A) (b:A) (l:B list). ALL2 R [a; b] l <=> ?x y. l = [x; y] /\ R a x /\ R b y`,
  REWRITE_TAC[LIST_REL_CONS1; LIST_REL_NIL] THEN MESON_TAC[]);;

(* the cases of type_v for the given theorem type_v .. v t *)
let TPROPSAUX_TV_CASES_THM (th:thm) : tactic =
  MP_TAC (REWRITE_RULE (TPROPSAUX_TYEQS @
            [distinctness "v"; injectivity "v"; distinctness "lit"; injectivity "lit";
             distinctness "option"; injectivity "option"])
            (ONCE_REWRITE_RULE[type_v_cases] th)) THEN
  REPEAT STRIP_TAC THEN TPROPSAUX_NORM_TAC THEN TPROPSAUX_NORM_TAC;;

(* HOL4 has n ctMap tenvS free *)
let type_v_list_to_v = prove
 (`!x xs t. type_v n ctMap tenvS x t /\ v_to_list x = SOME xs
            ==> type_v n ctMap tenvS (list_to_v xs) t`,
  MATCH_MP_TAC v_to_list_ind THEN REWRITE_TAC[v_to_list_def; option_DISTINCT] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC[option_DISTINCT; injectivity "option"] THEN STRIP_TAC THEN RVEQ_TAC THEN
    ASM_REWRITE_TAC[list_to_v_def];
    REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT] THEN
    DISCH_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[option_case_eq; option_DISTINCT] THEN
    STRIP_TAC THEN RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[injectivity "option"]) THEN
    RVEQ_TAC THEN TPROPSAUX_TV_ASM_CASES_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[injectivity "option"; distinctness "option"]) THEN
    TRY (FIRST_ASSUM CONTR_TAC) THEN RVEQ_TAC THEN
    REWRITE_TAC[list_to_v_def] THEN MATCH_MP_TAC TPROPSAUX_type_v_Conv THEN
    MAP_EVERY EXISTS_TAC [`tvs':mlstring list`; `ts:t list`] THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[TPROPSAUX_ALL2_2]) THEN
    REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
    ASM_REWRITE_TAC[ALL2] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let type_v_list_to_v_APPEND = prove
 (`!xs ys t.
     ctMap_has_lists ctMap /\
     type_v 0 ctMap tenvS (list_to_v xs) (Tapp [t] Tlist_num) /\
     type_v 0 ctMap tenvS (list_to_v ys) (Tapp [t] Tlist_num)
     ==> type_v 0 ctMap tenvS (list_to_v (APPEND xs ys)) (Tapp [t] Tlist_num)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  TPROPSAUX_POP_MATCH `type_v 0 ctMap tenvS (list_to_v (CONS a b)) x` THEN
  DISCH_THEN(TPROPSAUX_TV_CASES_THM o REWRITE_RULE[list_to_v_def]) THEN
  TRY TPROPSAUX_NEG_TAC THEN TRY (TPROPSAUX_TFN_TAC THEN TPROPSAUX_NEG_TAC) THEN
  SUBGOAL_THEN `tvs' = [implode "'a"] /\
                ts = [Tvar (implode "'a"); Tlist (Tvar (implode "'a"))]`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `ctMap_has_lists ctMap` THEN REWRITE_TAC[ctMap_has_lists_def] THEN
    ASM_REWRITE_TAC[injectivity "option"; PAIR_EQ] THEN MESON_TAC[]; ALL_TAC] THEN
  RVEQ_TAC THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[ZIP; REVERSE; APPEND; FUPDATE_LIST_THM; MAP;
                 type_subst_def; FLOOKUP_UPDATE; typeSystem_Tlist_def;
                 typeSystem_Tlist_num_def; ALL2]) THEN
  REWRITE_TAC[list_to_v_def] THEN MATCH_MP_TAC TPROPSAUX_type_v_Conv THEN
  MAP_EVERY EXISTS_TAC [`[implode "'a"]`;
                        `[Tvar (implode "'a"); Tlist (Tvar (implode "'a"))]`] THEN
  CASE_REWRITE_TAC[ZIP; REVERSE; APPEND; FUPDATE_LIST_THM; MAP; type_subst_def;
                   FLOOKUP_UPDATE; typeSystem_Tlist_def; typeSystem_Tlist_num_def;
                   ALL2; LENGTH] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[typeSystem_Tlist_num_def]) THEN
  ASM_REWRITE_TAC[]);;

(* HOL4 has b b' free *)
let do_eq_Boolv = prove
 (`do_eq (Boolv b) (Boolv b') = Eq_val (b = b')`,
  BOOL_CASES_TAC `b:bool` THEN BOOL_CASES_TAC `b':bool` THEN
  REWRITE_TAC[semanticPrimitives_Boolv_def; do_eq_def] THEN
  REWRITE_TAC[injectivity "option"; injectivity "stamp"; injectivity "mlstring"; CONS_11;
              injectivity "char"; ctor_same_type_def] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[same_type_def]);;

let prim_canonical_Boolv_thm = prove
 (`type_v tvs ctMap tenvS v Tbool /\ ctMap_ok ctMap /\ ctMap_has_bools ctMap
   ==> ?b. v = Boolv b`,
  MESON_TAC[ctor_canonical_values_thm]);;

let prim_canonical_Boolv_cases = prove
 (`type_v tvs ctMap tenvS v (Tapp [] Tbool_num) /\ ctMap_ok ctMap /\
   ctMap_has_bools ctMap
   ==> v = Boolv T \/ v = Boolv F`,
  REWRITE_TAC[GSYM typeSystem_Tbool_def] THEN
  DISCH_THEN(MP_TAC o MATCH_MP prim_canonical_Boolv_thm) THEN
  DISCH_THEN(X_CHOOSE_THEN `b:bool` SUBST1_TAC) THEN
  BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* op_type_sound: one lemma TPROPSAUX_ots_OP per operator OP, the statement *)
(* of op_type_sound with op := OP (HOL4 proves all operators in one proof)   *)
(* ------------------------------------------------------------------------- *)

let TPROPSAUX_OTS_TEMPLATE = CASE_TERM
  `!ctMap tenvS vs ts t store (ffi:(FFI)ffi_state).
     good_ctMap ctMap /\ type_s ctMap store tenvS /\ type_op TPROPSAUX_OP ts t /\
     check_freevars 0 [] t /\ ALL2 (type_v 0 ctMap tenvS) vs (REVERSE ts)
     ==> ?tenvS' store' ffi' r.
           store_type_extension tenvS tenvS' /\ type_s ctMap store' tenvS' /\
           do_app (store,ffi) TPROPSAUX_OP (REVERSE vs) = SOME ((store',ffi'),r) /\
           (match r with
              Rval v -> type_v 0 ctMap tenvS' v t
            | Rerr (Rraise v) -> type_v 0 ctMap tenvS' v Texn
            | Rerr (Rabort (Rffi_error _)) -> T
            | Rerr (Rabort _) -> F)`;;

let TPROPSAUX_OTS (op:term) = vsubst [op, `TPROPSAUX_OP:op`] TPROPSAUX_OTS_TEMPLATE;;

(* canonical values and the type_v rules, with the types decided *)
let TPROPSAUX_PCV_IMPS =
  CONJUNCTS (REWRITE_RULE TPROPSAUX_TYEQS prim_canonical_values_thm);;

let TPROPSAUX_CCV_IMPS =
  let ths = CONJUNCTS (REWRITE_RULE TPROPSAUX_TYEQS ctor_canonical_values_thm) in
  [hd ths; hd (tl ths)];;

let TPROPSAUX_TV_RULES = CONJUNCTS (REWRITE_RULE TPROPSAUX_TYEQS type_v_rules);;

let TPROPSAUX_TV_LIT_RULES =
  filter (fun th -> not (is_imp (snd (strip_forall (concl th))))) TPROPSAUX_TV_RULES;;

let TPROPSAUX_type_v_Boolv' = REWRITE_RULE TPROPSAUX_TYEQS type_v_Boolv;;

let TPROPSAUX_type_v_exn' = REWRITE_RULE TPROPSAUX_TYEQS TPROPSAUX_type_v_exn;;

(* the value of Explode has type Tlist Tchar (HOL4 proves it inside         *)
(* op_type_sound)                                                            *)
let TPROPSAUX_type_v_chars = prove
 (`!cs. ctMap_has_lists ctMap
        ==> type_v tvs ctMap tenvS (list_to_v (MAP (\c. Litv (Char c)) cs))
                   (Tapp [Tapp [] 2] 6)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; list_to_v_def] THEN DISCH_TAC THEN
  MATCH_MP_TAC TPROPSAUX_type_v_Conv THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[ctMap_has_lists_def; typeSystem_Tlist_num_def])
  THENL
   [MAP_EVERY EXISTS_TAC [`[implode "'a"]`; `[]:t list`] THEN
    ASM_REWRITE_TAC[check_freevars_def; ALL; LENGTH; MAP; ALL2];
    MAP_EVERY EXISTS_TAC [`[implode "'a"]`;
                          `[Tvar (implode "'a"); Tlist (Tvar (implode "'a"))]`] THEN
    ASM_REWRITE_TAC[] THEN
    CASE_REWRITE_TAC[ZIP; REVERSE; APPEND; FUPDATE_LIST_THM; MAP; type_subst_def;
                     FLOOKUP_UPDATE; typeSystem_Tlist_def; typeSystem_Tlist_num_def;
                     ALL2; LENGTH; check_freevars_def; ALL] THEN
    ASM_SIMP_TAC TPROPSAUX_TV_LIT_RULES]);;

(* the type_op case, the values (with their canonical forms) and do_app *)
let TPROPSAUX_OTS_START : tactic =
  REPEAT GEN_TAC THEN
  REWRITE_TAC[good_ctMap_def; type_op_cases; distinctness "op"; injectivity "op";
              distinctness "word_size"] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REVERSE; APPEND; LIST_REL_CONS2; LIST_REL_NIL]) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
  RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE TPROPSAUX_TYEQS) THEN
  MAP_EVERY IMP_RES_TAC TPROPSAUX_PCV_IMPS THEN
  MAP_EVERY IMP_RES_TAC TPROPSAUX_CCV_IMPS THEN
  RULE_ASSUM_TAC(REWRITE_RULE TPROPSAUX_TYEQS) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
  RVEQ_TAC THEN
  REWRITE_TAC[REVERSE; APPEND] THEN REWRITE_TAC[do_app_def] THEN CASE_REWRITE_TAC[];;

(* the witnesses of the goal of TPROPSAUX_OTS: the given store type, and   *)
(* store', ffi' and r from their equations in the goal (s0 = store' or     *)
(* SOME ((s0,f0),r0) = SOME ((store',ffi'),r))                              *)
let TPROPSAUX_DO_APP_EXISTS_TAC (tenv':term) : tactic = fun (asl,w as gl) ->
  let vs,body = strip_exists w in
  let rec flat c = if is_conj c then flat (lhand c) @ flat (rand c) else [c] in
  let eqs = filter is_eq (flat body) in
  let some_eq =
    try Some (find (fun e -> try fst(dest_const(rator(lhs e))) = "SOME" &&
                                  fst(dest_const(rator(rhs e))) = "SOME"
                             with Failure _ -> false) eqs)
    with Failure _ -> None in
  let from_some v = match some_eq with
      Some e -> let (a,b),c = (let p,q = dest_pair (rand (lhs e)) in dest_pair p,q) in
                let (a',b'),c' = (let p,q = dest_pair (rand (rhs e)) in dest_pair p,q) in
                assoc v [a',a; b',b; c',c]
    | None -> failwith "from_some" in
  let wit v =
    try lhs (find (fun e -> rhs e = v) eqs) with Failure _ ->
    try rhs (find (fun e -> lhs e = v) eqs) with Failure _ -> from_some v in
  let ws = tenv' :: map wit (tl vs) in
  MAP_EVERY EXISTS_TAC ws gl;;

let TPROPSAUX_head_args s n tm =
  try let f,args = strip_comb tm in fst(dest_const f) = s && length args = n
  with Failure _ -> false;;

(* the goal after the witnesses: store extension, store typing, the result *)
let TPROPSAUX_OTS_FINISH_TAC : tactic =
  REWRITE_TAC (TPROPSAUX_TYEQS @ [sub_exn_v_def; chr_exn_v_def; div_exn_v_def]) THEN
  CASE_REWRITE_TAC[store_type_extension_refl] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[check_freevars_def; ALL]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GE; NOT_LE]) THEN
  (fun (asl,w as gl) ->
     let alls = filter (fun (_,th) -> TPROPSAUX_head_args "ALL" 2 (concl th)) asl in
     MAP_EVERY (fun (_,th) -> ASSUME_TAC (REWRITE_RULE[EVERY_EL; BETA_THM] th)) alls gl) THEN
  ASM_SIMP_TAC (TPROPSAUX_type_v_Boolv' :: TPROPSAUX_type_v_exn' :: TPROPSAUX_type_v_chars ::
                ALL2 :: TPROPSAUX_TV_RULES);;

(* the result type t of the goal of TPROPSAUX_OTS (in its Rval branch) *)
let TPROPSAUX_result_type (w:term) : term =
  rand (find_term (fun t -> TPROPSAUX_head_args "type_v" 5 t && not (rand t = `Texn`)) w);;

(* do_app (store,ffi) op vs with a store_alloc: store_alloc_type_sound      *)
(* for its value, with the store type of the result type of the goal       *)
let TPROPSAUX_STORE_ALLOC_TAC : tactic = fun (asl,w as gl) ->
  let t = find_term (TPROPSAUX_head_args "store_alloc" 2) w in
  let sv,st = (fun l -> hd l, hd (tl l)) (snd (strip_comb t)) in
  let rt = rhs (concl (REWRITE_CONV TPROPSAUX_TYEQS (TPROPSAUX_result_type w))) in
  let ts,n = (fun l -> hd l, hd (tl l)) (snd (strip_comb rt)) in
  let stt = if n = `7` then mk_comb(`Ref_t`, hd (dest_list ts))
            else if n = `13` then `W8array_t`
            else mk_comb(`Varray_t`, hd (dest_list ts)) in
  (MP_TAC(ISPECL [`ctMap:ctMap`; `tenvS:tenv_store`; st; sv; stt] store_alloc_type_sound) THEN
   ASM_REWRITE_TAC[type_sv_def; ALL; EVERY_REPLICATE] THEN
   DISCH_THEN(X_CHOOSE_THEN `store1:(v store_v)list` (X_CHOOSE_THEN `tenvS1:tenv_store`
     (X_CHOOSE_THEN `n1:num` STRIP_ASSUME_TAC))) THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
   TPROPSAUX_DO_APP_EXISTS_TAC `tenvS1:tenv_store`) gl;;

(* do_app (store,ffi) op vs with a store_assign l sv store:                 *)
(* store_assign_type_sound                                                   *)
let TPROPSAUX_STORE_ASSIGN_TAC : tactic = fun (asl,w as gl) ->
  let t = find_term (TPROPSAUX_head_args "store_assign" 3) w in
  let l,sv,st = (fun x -> hd x, hd (tl x), hd (tl (tl x))) (snd (strip_comb t)) in
  let fl = find (fun (_,th) -> let c = concl th in
                   is_eq c && TPROPSAUX_head_args "FLOOKUP" 2 (lhs c) && rand (lhs c) = l)
                asl in
  let stt = rand (rhs (concl (snd fl))) in
  (MP_TAC(ISPECL [`ctMap:ctMap`; `tenvS:tenv_store`; st; sv; stt; l]
                 store_assign_type_sound) THEN
   ASM_SIMP_TAC[type_sv_def; IMP_EVERY_LUPDATE] THEN
   DISCH_THEN(X_CHOOSE_THEN `store1:(v store_v)list` STRIP_ASSUME_TAC) THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
   TPROPSAUX_DO_APP_EXISTS_TAC `tenvS:tenv_store`) gl;;

(* split on a case expression or conditional of the goal (not on store     *)
(* updates, which TPROPSAUX_STORE_ALLOC_TAC and TPROPSAUX_STORE_ASSIGN_TAC  *)
(* handle)                                                                   *)
let TPROPSAUX_SPLIT_TAC : tactic = fun (asl,w as gl) ->
  let ok t =
    (is_cond t || is_case_app t) &&
    (let x = scrutinee_of t in
     free_in x w && not (x = `T`) && not (x = `F`) && not (is_constructor_app x) &&
     not (TPROPSAUX_head_args "store_assign" 3 x) &&
     not (TPROPSAUX_head_args "store_alloc" 2 x)) in
  let x = scrutinee_of (case_find_subterm ok w) in
  (CASES_ON x THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[LET_DEF; LET_END_DEF]) gl;;

(* the cases of do_app after TPROPSAUX_OTS_START, then the witnesses *)
let TPROPSAUX_OTS_GEN_TAC : tactic =
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH; LENGTH_NIL_SYM]) THEN RVEQ_TAC THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REPEAT TPROPSAUX_SPLIT_TAC THEN
  IMP_RES_TAC type_v_freevars THEN
  (TPROPSAUX_STORE_ALLOC_TAC ORELSE TPROPSAUX_STORE_ASSIGN_TAC ORELSE
   TPROPSAUX_DO_APP_EXISTS_TAC `tenvS:tenv_store`) THEN
  TPROPSAUX_OTS_FINISH_TAC;;

let TPROPSAUX_LENGTH_EQ = prove
 (`!l:A list. (1 = LENGTH l <=> ?x. l = [x]) /\ (2 = LENGTH l <=> ?x y. l = [x; y]) /\
              (3 = LENGTH l <=> ?x y z. l = [x; y; z])`,
  GEN_TAC THEN REPEAT CONJ_TAC THEN GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [EQ_SYM_EQ] THEN
  REPEAT (CHANGED_TAC (REWRITE_TAC[LENGTH_EQ_NUM_compute] THEN CONV_TAC NUM_REDUCE_CONV)) THEN
  MESON_TAC[]);;

let TPROPSAUX_EXISTS_REFL' = prove
 (`!a:A. ?x. a = x`,
  MESON_TAC[]);;

(* the type_op case of a primitive operator, split on the primitive types   *)
(* and operations                                                            *)
let TPROPSAUX_CASES_WORDT : tactic = fun (asl,w as gl) ->
  let t = find_term (fun t -> is_comb t && rator t = `WordT` && is_var (rand t)) w in
  CASES_ON (rand t) gl;;

let TPROPSAUX_OTS_START1 : tactic =
  REPEAT GEN_TAC THEN
  REWRITE_TAC[good_ctMap_def; type_op_cases; distinctness "op"; injectivity "op";
              distinctness "word_size"] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[supported_arith_def; supported_conversion_def;
                              supported_test_def; MEM; distinctness "arith";
                              distinctness "prim_type"; distinctness "word_size";
                              distinctness "test"; injectivity "prim_type";
                              option_DISTINCT; injectivity "option"]) THEN
  TRY (FIRST_ASSUM CONTR_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[TPROPSAUX_LENGTH_EQ]) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_exists o concl))) THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ALL; t_of_def]) THEN TPROPSAUX_NORM_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[t_of_def]);;

(* the values (with their canonical forms) and do_app *)
let TPROPSAUX_OTS_START2 : tactic =
  RULE_ASSUM_TAC(REWRITE_RULE[REVERSE; APPEND; LIST_REL_CONS2; LIST_REL_NIL]) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
  RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE TPROPSAUX_TYEQS) THEN
  MAP_EVERY IMP_RES_TAC TPROPSAUX_PCV_IMPS THEN
  MAP_EVERY IMP_RES_TAC TPROPSAUX_CCV_IMPS THEN
  RULE_ASSUM_TAC(REWRITE_RULE TPROPSAUX_TYEQS) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
  RVEQ_TAC THEN
  REWRITE_TAC[REVERSE; APPEND] THEN REWRITE_TAC[do_app_def] THEN CASE_REWRITE_TAC[];;

(* the computation of the primitive operations *)
let TPROPSAUX_OTS_PRIM_TAC : tactic =
  REWRITE_TAC[check_type_def; do_arith_def; do_conversion_def; do_test_def;
              the_Litv_IntLit_def; the_Litv_Word8_def; the_Litv_Word64_def;
              the_Litv_Float64_def; the_Litv_Char_def; the_Boolv_def; dest_Litv_def;
              MAP; ALL; TPROPSAUX_EXISTS_REFL'; semanticPrimitivesProps_Boolv_11;
              EXCLUDED_MIDDLE; do_eq_Boolv; do_eq_def; lit_same_type_def;
              injectivity "v"; injectivity "lit"; distinctness "prim_type"; t_of_def] THEN
  CASE_REWRITE_TAC[] THEN TPROPSAUX_OTS_GEN_TAC;;


let TPROPSAUX_ots_Arith = prove
 (TPROPSAUX_OTS `Arith a ty`,
  CASES_ON `ty:prim_type` THEN TRY TPROPSAUX_CASES_WORDT THEN CASES_ON `a:arith` THEN
  TPROPSAUX_OTS_START1 THEN TPROPSAUX_OTS_START2 THEN TPROPSAUX_OTS_PRIM_TAC);;

let TPROPSAUX_ots_FromTo = prove
 (TPROPSAUX_OTS `FromTo ty1 ty2`,
  CASES_ON `ty1:prim_type` THEN TRY TPROPSAUX_CASES_WORDT THEN
  CASES_ON `ty2:prim_type` THEN TRY TPROPSAUX_CASES_WORDT THEN
  TPROPSAUX_OTS_START1 THEN TPROPSAUX_OTS_START2 THEN TPROPSAUX_OTS_PRIM_TAC);;

let TPROPSAUX_ots_Shift = prove
 (TPROPSAUX_OTS `Shift w a1 a2`,
  CASES_ON `w:word_size` THEN TPROPSAUX_OTS_START THEN TPROPSAUX_OTS_GEN_TAC);;

let TPROPSAUX_ots_Equality = prove
 (TPROPSAUX_OTS `Equality`,
  TPROPSAUX_OTS_START THEN
  MP_TAC (ISPECL [`h'':v`; `h':v`; `0`; `ctMap:ctMap`; `ARB:num`; `tenvS:tenv_store`;
                  `a0:t`] (CONJUNCT1 eq_same_type)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC (ISPEC `do_eq h'' h'` (cases "eq_result")) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:bool` ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN TPROPSAUX_DO_APP_EXISTS_TAC `tenvS:tenv_store` THEN
  TPROPSAUX_OTS_FINISH_TAC);;

let TPROPSAUX_ots_Test = prove
 (TPROPSAUX_OTS `Test test ty`,
  CASES_ON `ty:prim_type` THEN TRY TPROPSAUX_CASES_WORDT THEN CASES_ON `test:test` THEN
  TPROPSAUX_OTS_START1 THEN TPROPSAUX_OTS_START2 THEN TPROPSAUX_OTS_PRIM_TAC);;

let TPROPSAUX_ots_Opassign = prove
 (TPROPSAUX_OTS `Opassign`,
  TPROPSAUX_OTS_START THEN TPROPSAUX_TV_ASM_CASES_TAC THEN
  TPROPSAUX_STORE_ASSIGN_TAC THEN TPROPSAUX_OTS_FINISH_TAC);;

let TPROPSAUX_ots_Opref = prove
 (TPROPSAUX_OTS `Opref`, TPROPSAUX_OTS_START THEN TPROPSAUX_OTS_GEN_TAC);;

let TPROPSAUX_ots_Opderef = prove
 (TPROPSAUX_OTS `Opderef`, TPROPSAUX_OTS_START THEN TPROPSAUX_OTS_GEN_TAC);;

let TPROPSAUX_ots_Aw8alloc = prove
 (TPROPSAUX_OTS `Aw8alloc`, TPROPSAUX_OTS_START THEN TPROPSAUX_OTS_GEN_TAC);;

let TPROPSAUX_ots_Aw8sub = prove
 (TPROPSAUX_OTS `Aw8sub`, TPROPSAUX_OTS_START THEN TPROPSAUX_OTS_GEN_TAC);;

let TPROPSAUX_ots_Aw8length = prove
 (TPROPSAUX_OTS `Aw8length`, TPROPSAUX_OTS_START THEN TPROPSAUX_OTS_GEN_TAC);;

let TPROPSAUX_ots_Aw8update = prove
 (TPROPSAUX_OTS `Aw8update`, TPROPSAUX_OTS_START THEN TPROPSAUX_OTS_GEN_TAC);;

let TPROPSAUX_ots_CopyStrStr = prove
 (TPROPSAUX_OTS `CopyStrStr`, TPROPSAUX_OTS_START THEN TPROPSAUX_OTS_GEN_TAC);;

let TPROPSAUX_ots_CopyStrAw8 = prove
 (TPROPSAUX_OTS `CopyStrAw8`, TPROPSAUX_OTS_START THEN TPROPSAUX_OTS_GEN_TAC);;

let TPROPSAUX_ots_CopyAw8Str = prove
 (TPROPSAUX_OTS `CopyAw8Str`, TPROPSAUX_OTS_START THEN TPROPSAUX_OTS_GEN_TAC);;

let TPROPSAUX_ots_CopyAw8Aw8 = prove
 (TPROPSAUX_OTS `CopyAw8Aw8`, TPROPSAUX_OTS_START THEN TPROPSAUX_OTS_GEN_TAC);;

let TPROPSAUX_ots_Implode = prove
 (TPROPSAUX_OTS `Implode`, TPROPSAUX_OTS_START THEN TPROPSAUX_OTS_GEN_TAC);;

let TPROPSAUX_ots_Explode = prove
 (TPROPSAUX_OTS `Explode`, TPROPSAUX_OTS_START THEN TPROPSAUX_OTS_GEN_TAC);;

let TPROPSAUX_ots_Strsub = prove
 (TPROPSAUX_OTS `Strsub`, TPROPSAUX_OTS_START THEN TPROPSAUX_OTS_GEN_TAC);;

let TPROPSAUX_ots_Strlen = prove
 (TPROPSAUX_OTS `Strlen`, TPROPSAUX_OTS_START THEN TPROPSAUX_OTS_GEN_TAC);;

let TPROPSAUX_ots_Strcat = prove
 (TPROPSAUX_OTS `Strcat`, TPROPSAUX_OTS_START THEN TPROPSAUX_OTS_GEN_TAC);;

let TPROPSAUX_ots_VfromList = prove
 (TPROPSAUX_OTS `VfromList`, TPROPSAUX_OTS_START THEN TPROPSAUX_OTS_GEN_TAC);;

let TPROPSAUX_ots_Vsub = prove
 (TPROPSAUX_OTS `Vsub`, TPROPSAUX_OTS_START THEN TPROPSAUX_OTS_GEN_TAC);;

let TPROPSAUX_ots_Vlength = prove
 (TPROPSAUX_OTS `Vlength`, TPROPSAUX_OTS_START THEN TPROPSAUX_OTS_GEN_TAC);;

let TPROPSAUX_ots_Aalloc = prove
 (TPROPSAUX_OTS `Aalloc`, TPROPSAUX_OTS_START THEN TPROPSAUX_OTS_GEN_TAC);;

let TPROPSAUX_ots_AallocEmpty = prove
 (TPROPSAUX_OTS `AallocEmpty`, TPROPSAUX_OTS_START THEN TPROPSAUX_OTS_GEN_TAC);;

let TPROPSAUX_ots_Asub = prove
 (TPROPSAUX_OTS `Asub`, TPROPSAUX_OTS_START THEN TPROPSAUX_OTS_GEN_TAC);;

let TPROPSAUX_ots_Alength = prove
 (TPROPSAUX_OTS `Alength`, TPROPSAUX_OTS_START THEN TPROPSAUX_OTS_GEN_TAC);;

let TPROPSAUX_ots_Aupdate = prove
 (TPROPSAUX_OTS `Aupdate`, TPROPSAUX_OTS_START THEN TPROPSAUX_OTS_GEN_TAC);;

let TPROPSAUX_ots_ListAppend = prove
 (TPROPSAUX_OTS `ListAppend`,
  TPROPSAUX_OTS_START THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  TPROPSAUX_DO_APP_EXISTS_TAC `tenvS:tenv_store` THEN
  REWRITE_TAC TPROPSAUX_TYEQS THEN CASE_REWRITE_TAC[store_type_extension_refl] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC (REWRITE_RULE[typeSystem_Tlist_num_def] type_v_list_to_v_APPEND) THEN
  ASM_MESON_TAC[GEN_ALL type_v_list_to_v]);;

let TPROPSAUX_ots_ConfigGC = prove
 (TPROPSAUX_OTS `ConfigGC`, TPROPSAUX_OTS_START THEN TPROPSAUX_OTS_GEN_TAC);;

let TPROPSAUX_ots_FFI = prove
 (TPROPSAUX_OTS `FFI s`, TPROPSAUX_OTS_START THEN TPROPSAUX_OTS_GEN_TAC);;

let TPROPSAUX_OTS_LEMMAS =
  [TPROPSAUX_ots_Arith; TPROPSAUX_ots_FromTo; TPROPSAUX_ots_Shift; TPROPSAUX_ots_Equality;
   TPROPSAUX_ots_Test; TPROPSAUX_ots_Opassign; TPROPSAUX_ots_Opref; TPROPSAUX_ots_Opderef;
   TPROPSAUX_ots_Aw8alloc; TPROPSAUX_ots_Aw8sub; TPROPSAUX_ots_Aw8length;
   TPROPSAUX_ots_Aw8update; TPROPSAUX_ots_CopyStrStr; TPROPSAUX_ots_CopyStrAw8;
   TPROPSAUX_ots_CopyAw8Str; TPROPSAUX_ots_CopyAw8Aw8; TPROPSAUX_ots_Implode;
   TPROPSAUX_ots_Explode; TPROPSAUX_ots_Strsub; TPROPSAUX_ots_Strlen; TPROPSAUX_ots_Strcat;
   TPROPSAUX_ots_VfromList; TPROPSAUX_ots_Vsub; TPROPSAUX_ots_Vlength; TPROPSAUX_ots_Aalloc;
   TPROPSAUX_ots_AallocEmpty; TPROPSAUX_ots_Asub; TPROPSAUX_ots_Alength;
   TPROPSAUX_ots_Aupdate; TPROPSAUX_ots_ListAppend; TPROPSAUX_ots_ConfigGC;
   TPROPSAUX_ots_FFI];;

(* HOL4's ffi : 'ffi ffi_state is (FFI)ffi_state *)
let op_type_sound = prove
 (CASE_TERM `!ctMap tenvS vs op ts t store (ffi:(FFI)ffi_state).
     good_ctMap ctMap /\ ~(op = Opapp) /\ type_s ctMap store tenvS /\ type_op op ts t /\
     check_freevars 0 [] t /\ ALL2 (type_v 0 ctMap tenvS) vs (REVERSE ts)
     ==> ?tenvS' store' ffi' r.
           store_type_extension tenvS tenvS' /\ type_s ctMap store' tenvS' /\
           do_app (store,ffi) op (REVERSE vs) = SOME ((store',ffi'),r) /\
           (match r with
              Rval v -> type_v 0 ctMap tenvS' v t
            | Rerr (Rraise v) -> type_v 0 ctMap tenvS' v Texn
            | Rerr (Rabort (Rffi_error _)) -> T
            | Rerr (Rabort _) -> F)`,
  REPEAT GEN_TAC THEN CASES_ON `op:op` THEN REWRITE_TAC[distinctness "op"] THEN
  (FIRST (map (fun th -> MATCH_ACCEPT_TAC (GEN_ALL th)) TPROPSAUX_OTS_LEMMAS) ORELSE
   REWRITE_TAC[type_op_cases; distinctness "op"]));;

let build_conv_type_sound = prove
 (`!envC cn vs tvs ts ctMap tenvS ts' tn tenvC tvs' tenvE l.
     nsAll2 (type_ctor ctMap) envC tenvC /\
     do_con_check envC (SOME cn) l /\
     num_tvs tenvE = 0 /\
     ALL (check_freevars (num_tvs (bind_tvar tvs tenvE)) []) ts' /\
     LENGTH tvs' = LENGTH ts' /\
     ALL2 (type_v tvs ctMap tenvS) vs
       (REVERSE (MAP (type_subst (alist_to_fmap (ZIP tvs' ts'))) ts)) /\
     nsLookup tenvC cn = SOME (tvs',ts,tn)
     ==> ?v. build_conv envC (SOME cn) (REVERSE vs) = SOME v /\
             type_v tvs ctMap tenvS v (Tapp ts' tn)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`ctMap:ctMap`; `envC:(mlstring,mlstring,num#stamp)namespace`;
                 `tenvC:(mlstring,mlstring,mlstring list#t list#num)namespace`]
                type_env_conv_thm) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`cn:(mlstring,mlstring)id`; `tvs':mlstring list`; `ts:t list`;
                             `tn:num`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[build_conv_def] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[injectivity "option"; UNWIND_THM1] THEN
  MATCH_MP_TAC TPROPSAUX_type_v_Conv THEN
  MAP_EVERY EXISTS_TAC [`tvs':mlstring list`; `ts:t list`] THEN
  TPROPSAUX_POP "ALL" THEN ASM_REWRITE_TAC[bind_tvar_rewrites; ADD_CLAUSES] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC[TPROPSAUX_FEMPTY_FUPDATE_LIST_REVERSE; GSYM EVERY2_REVERSE1]);;

let same_ctor_and_same_tid = prove
 (`!stamp1 stamp2.
     same_ctor stamp1 stamp2 /\ same_type stamp1 stamp2 ==> stamp1 = stamp2`,
  REWRITE_TAC[same_ctor_def] THEN MESON_TAC[]);;

(* the variant of type_env_conv_thm used for patterns *)
let TPROPSAUX_tenvC_lookup = prove
 (`!ctMap (envC:(M,N,num#stamp)namespace) (tenvC:(M,N,mlstring list#t list#num)namespace)
     cn tvs ts ti.
     nsAll2 (type_ctor ctMap) envC tenvC /\ nsLookup tenvC cn = SOME (tvs,ts,ti)
     ==> ?stamp. nsLookup envC cn = SOME (LENGTH ts,stamp) /\
                 FLOOKUP ctMap stamp = SOME (tvs,ts,ti)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o ISPECL [`cn:(M,N)id`; `tvs:mlstring list`; `ts:t list`; `ARB:num`;
                                 `ti:num`] o MATCH_MP type_env_conv_thm) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

(* the cases of type_p for every assumption type_p .. (C ..) t bs *)
let TPROPSAUX_TP_ASM_CASES_TAC : tactic =
  REPEAT (FIRST_X_ASSUM (fun th ->
    let c = concl th in
    if (TPROPSAUX_head_is "type_p" c || TPROPSAUX_head_is "type_ps" c) &&
       not (is_var (rand (rator (rator c)))) then
      MP_TAC (REWRITE_RULE (TPROPSAUX_TYEQS @
                [distinctness "pat"; injectivity "pat"; distinctness "lit"; injectivity "lit";
                 distinctness "option"; injectivity "option"; NOT_CONS_NIL; CONS_11])
                (ONCE_REWRITE_RULE[type_p_cases] th))
    else NO_TAC)) THEN
  REPEAT STRIP_TAC THEN TPROPSAUX_NORM_TAC THEN TPROPSAUX_NORM_TAC;;

let TPROPSAUX_mentions s tm =
  can (find_term (fun t -> is_const t && fst(dest_const t) = s)) tm;;

(* the cases of pat_type_sound: unfold pmatch, split the types of the      *)
(* value and the pattern, close the impossible cases                         *)
let TPROPSAUX_PAT_PRE_TAC : tactic =
  REPEAT STRIP_TAC THEN REWRITE_TAC[pmatch_def; distinctness "match_result"] THEN
  CASE_REWRITE_TAC[] THEN
  TPROPSAUX_TV_ASM_CASES_TAC THEN TPROPSAUX_TP_ASM_CASES_TAC THEN
  IMP_RES_TAC TPROPSAUX_tenvC_lookup THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[injectivity "option"; distinctness "option"]) THEN
  TPROPSAUX_NORM_TAC THEN
  TRY TPROPSAUX_NEG_TAC THEN TRY (TPROPSAUX_TFN_TAC THEN TPROPSAUX_NEG_TAC) THEN
  TRY (TPROPSAUX_CONTR_TAC [distinctness "option"; ALL2; NOT_CONS_NIL]);;

let TPROPSAUX_PAT_SIMPLE_TAC : tactic =
  TPROPSAUX_PAT_PRE_TAC THEN
  REWRITE_TAC[lit_same_type_def] THEN CASE_REWRITE_TAC[] THEN
  REPEAT COND_CASES_TAC THEN
  ASM_REWRITE_TAC[distinctness "match_result"; injectivity "match_result"; APPEND;
                  UNWIND_THM1; ALL2] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[];;

let TPROPSAUX_PAT_IH_TAC : tactic =
  TPROPSAUX_PAT_PRE_TAC THEN REWRITE_TAC[GSYM APPEND_ASSOC; APPEND] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[ALL2] THEN CASE_REWRITE_TAC[] THEN
  ASM_MESON_TAC[];;

let TPROPSAUX_PAT_PCON_SOME_TAC : tactic =
  TPROPSAUX_PAT_PRE_TAC THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  SUBGOAL_THEN `same_type stamp'' stamp` ASSUME_TAC THENL
   [ASM_MESON_TAC[TPROPSAUX_ctMap_ok_same_type]; ALL_TAC] THEN
  IMP_RES_TAC type_ps_length THEN IMP_RES_TAC LIST_REL_LENGTH THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_MAP]) THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[same_ctor_def]) THEN RVEQ_TAC THEN
  SUBGOAL_THEN `tvs'':mlstring list = tvs' /\ ts'':t list = ts` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[injectivity "option"; PAIR_EQ]; ALL_TAC] THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[TPROPSAUX_FEMPTY_FUPDATE_LIST_REVERSE]) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];;

let TPROPSAUX_PAT_PCON_NONE_TAC : tactic =
  TPROPSAUX_PAT_PRE_TAC THEN
  IMP_RES_TAC type_ps_length THEN IMP_RES_TAC LIST_REL_LENGTH THEN
  ASM_REWRITE_TAC[] THEN RES_TAC THEN ASM_MESON_TAC[];;

let TPROPSAUX_PAT_PREF_TAC : tactic =
  TPROPSAUX_PAT_PRE_TAC THEN
  IMP_RES_TAC TPROPSAUX_type_s_FLOOKUP THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
  FIRST_X_ASSUM(fun th ->
    if TPROPSAUX_head_is "type_sv" (concl th) then MP_TAC th else NO_TAC) THEN
  CASES_ON `sv:v store_v` THEN REWRITE_TAC[type_sv_def] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN RES_TAC THEN
  IMP_RES_TAC type_v_weakening THEN ASM_MESON_TAC[weakCT_refl; weakS_refl];;

let TPROPSAUX_PAT_CONS_TAC : tactic =
  TPROPSAUX_PAT_PRE_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[ALL2]) THEN TPROPSAUX_NORM_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`tenv:type_env`; `ctMap:ctMap`; `tbindings:(mlstring#t)list`;
                                `t:t`; `bindings:(mlstring#t)list`; `tenvS:tenv_store`;
                                `tvs:num`] o
                check (fun th -> length (fst (strip_forall (concl th))) = 7 &&
                                 not (TPROPSAUX_mentions "pmatch_list" (concl th)))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  RES_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[distinctness "match_result"; injectivity "match_result"; UNWIND_THM1;
              GSYM APPEND_ASSOC] THEN
  ASM_REWRITE_TAC[];;

(* HOL4's paired lambdas \(x,v) (x',t). .. are written with pair_CASE *)
let pat_type_sound = prove
 (CASE_TERM `(!(cenv:(mlstring,mlstring,num#stamp)namespace) (st:(v store_v)list) p v
               bindings tenv ctMap tbindings t new_tbindings tenvS tvs.
     ctMap_ok ctMap /\ nsAll2 (type_ctor ctMap) cenv (type_env_c tenv) /\
     type_v tvs ctMap tenvS v t /\ type_p tvs tenv p t new_tbindings /\
     type_s ctMap st tenvS /\
     ALL2 (\xv xt. match xv with (x,v) -> match xt with (x',t) ->
                     x = x' /\ type_v tvs ctMap tenvS v t) bindings tbindings
     ==> pmatch cenv st p v bindings = No_match \/
         (?bindings'.
            pmatch cenv st p v bindings = Match bindings' /\
            ALL2 (\xv xt. match xv with (x,v) -> match xt with (x',t) ->
                            x = x' /\ type_v tvs ctMap tenvS v t)
                 bindings' (APPEND new_tbindings tbindings))) /\
   (!(cenv:(mlstring,mlstring,num#stamp)namespace) (st:(v store_v)list) ps vs
               bindings tenv ctMap tbindings new_tbindings ts tenvS tvs.
     ctMap_ok ctMap /\ nsAll2 (type_ctor ctMap) cenv (type_env_c tenv) /\
     ALL2 (type_v tvs ctMap tenvS) vs ts /\ type_ps tvs tenv ps ts new_tbindings /\
     type_s ctMap st tenvS /\
     ALL2 (\xv xt. match xv with (x,v) -> match xt with (x',t) ->
                     x = x' /\ type_v tvs ctMap tenvS v t) bindings tbindings
     ==> pmatch_list cenv st ps vs bindings = No_match \/
         (?bindings'.
            pmatch_list cenv st ps vs bindings = Match bindings' /\
            ALL2 (\xv xt. match xv with (x,v) -> match xt with (x',t) ->
                            x = x' /\ type_v tvs ctMap tenvS v t)
                 bindings' (APPEND new_tbindings tbindings)))`,
  let s = TPROPSAUX_PAT_SIMPLE_TAC and ih = TPROPSAUX_PAT_IH_TAC in
  MATCH_MP_TAC pmatch_ind THEN REPEAT CONJ_TAC THENL
   ([s; s; s; TPROPSAUX_PAT_PCON_SOME_TAC; TPROPSAUX_PAT_PCON_NONE_TAC;
     TPROPSAUX_PAT_PREF_TAC; ih; ih] @ replicate s 27 @
    [TPROPSAUX_PAT_CONS_TAC; s; s]));;

let lookup_var_sound = prove
 (`!n tvs tenvE targs t ctMap tenvS env tenv.
     lookup_var n (bind_tvar tvs tenvE) tenv = SOME (LENGTH targs,t) /\
     ctMap_ok ctMap /\ tenv_val_exp_ok tenvE /\ num_tvs tenvE = 0 /\
     ALL (check_freevars tvs []) targs /\
     type_all_env ctMap tenvS env
       (type_env_v_fupd (K (add_tenvE tenvE (type_env_v tenv))) tenv)
     ==> ?v. nsLookup (sem_env_v env) n = SOME v /\
             type_v tvs ctMap tenvS v (deBruijn_subst 0 targs t)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[type_all_env_def; type_env_INFO.ri_accfupds; K_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `nsLookup (add_tenvE tenvE (type_env_v tenv)) (n:(mlstring,mlstring)id) =
                SOME (LENGTH (targs:t list),(t:t))` ASSUME_TAC THENL
   [UNDISCH_TAC `lookup_var n (bind_tvar tvs tenvE) tenv =
                 SOME (LENGTH (targs:t list),(t:t))` THEN
    REWRITE_TAC[lookup_var_def; lookup_varE_def; bind_tvar_rewrites] THEN
    CASES_ON `n:(mlstring,mlstring)id` THEN
    CASE_REWRITE_TAC[bind_tvar_rewrites; ADD_CLAUSES] THENL
     [CASES_ON `tveLookup a tvs tenvE` THEN CASE_REWRITE_TAC[] THEN DISCH_TAC THENL
       [MATCH_MP_TAC nsLookup_add_tenvE2 THEN EXISTS_TAC `tvs:num` THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC nsLookup_add_tenvE1 THEN EXISTS_TAC `tvs:num` THEN
        RULE_ASSUM_TAC(REWRITE_RULE[injectivity "option"]) THEN RVEQ_TAC THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC tveLookup_freevars THEN
        MAP_EVERY EXISTS_TAC [`a:mlstring`; `tvs:num`; `tenvE:tenv_val_exp`] THEN
        ASM_REWRITE_TAC[]];
      MESON_TAC[nsLookup_add_tenvE3]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [CASE_TERM `\(i:(mlstring,mlstring)id) (v:v) (p:num#t).
                    match p with (tvs,t) -> type_v tvs ctMap tenvS v t`;
                 `sem_env_v (env:v sem_env)`; `add_tenvE tenvE (type_env_v tenv)`;
                 `n:(mlstring,mlstring)id`; `(LENGTH (targs:t list),(t:t))`]
                nsAll2_nsLookup2) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:v` STRIP_ASSUME_TAC) THEN EXISTS_TAC `v:v` THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (INST [`tvs:num`,`tvs':num`] type_subst)) THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC type_v_freevars THEN
  MAP_EVERY EXISTS_TAC [`ctMap:ctMap`; `tenvS:tenv_store`; `v:v`] THEN ASM_REWRITE_TAC[]);;

(* HOL4: EVERY_REPLICATE (the name is rich_list's EVERY_REPLICATE here);    *)
(* HOL4 has tvs ctMap tenv t' vs free                                         *)
let typeSound_EVERY_REPLICATE = prove
 (`ALL (\x. type_v tvs ctMap tenv x t') vs =
   ALL (\x. type_v tvs ctMap tenv (FST x) (SND x)) (ZIP vs (REPLICATE (LENGTH vs) t'))`,
  SPEC_TAC(`vs:v list`,`vs:v list`) THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[ALL; ZIP; LENGTH; REPLICATE]);;

(* HOL4 has n ctMap tenvS t vs free *)
let EVERY_LIST_REL = prove
 (`ALL (\v. type_v n ctMap tenvS v t) vs =
   ALL2 (type_v n ctMap tenvS) vs (REPLICATE (LENGTH vs) t)`,
  REWRITE_TAC[TPROPSAUX_ALL_REPLICATE; ETA_AX]);;

(* ------------------------------------------------------------------------- *)
(* exp_type_sound: one lemma TPROPSAUX_ets_k per case of evaluate_ind (the   *)
(* properties P1 and P2 below are the two conjuncts of exp_type_sound)       *)
(* ------------------------------------------------------------------------- *)

let TPROPSAUX_ETS_P1 = CASE_TERM
 `\(s:(FFI)state) (env:v sem_env) (es:exp list).
    !r s' tenv tenvE ts tvs tenvS.
      evaluate s env es = (s',r) /\
      tenv_ok tenv /\ tenv_val_exp_ok tenvE /\ good_ctMap ctMap /\ num_tvs tenvE = 0 /\
      type_all_env ctMap tenvS env
        (type_env_v_fupd (K (add_tenvE tenvE (type_env_v tenv))) tenv) /\
      type_s ctMap (state_refs s) tenvS /\
      (~(tvs = 0) ==> ALL is_value es) /\
      type_es tenv (bind_tvar tvs tenvE) es ts
      ==> ?tenvS'. type_s ctMap (state_refs s') tenvS' /\
                   store_type_extension tenvS tenvS' /\
                   state_next_type_stamp s' = state_next_type_stamp s /\
                   state_next_exn_stamp s' = state_next_exn_stamp s /\
                   (match r with
                      Rval vs -> ALL2 (type_v tvs ctMap tenvS') vs ts
                    | Rerr (Rraise v) -> type_v 0 ctMap tenvS' v Texn
                    | Rerr (Rabort Rtimeout_error) -> T
                    | Rerr (Rabort (Rffi_error _)) -> T
                    | Rerr (Rabort Rtype_error) -> F)`;;

let TPROPSAUX_ETS_P2 = CASE_TERM
 `\(s:(FFI)state) (env:v sem_env) (v:v) (pes:(pat#exp)list) (err_v:v).
    !r s' tenv tenvE t1 t2 tvs tenvS.
      evaluate_match s env v pes err_v = (s',r) /\
      tenv_ok tenv /\ tenv_val_exp_ok tenvE /\ good_ctMap ctMap /\ num_tvs tenvE = 0 /\
      type_all_env ctMap tenvS env
        (type_env_v_fupd (K (add_tenvE tenvE (type_env_v tenv))) tenv) /\
      type_s ctMap (state_refs s) tenvS /\
      type_v tvs ctMap tenvS v t1 /\ type_v 0 ctMap tenvS err_v Texn /\
      type_pes tvs tvs tenv tenvE pes t1 t2
      ==> ?tenvS'. type_s ctMap (state_refs s') tenvS' /\
                   store_type_extension tenvS tenvS' /\
                   state_next_type_stamp s' = state_next_type_stamp s /\
                   state_next_exn_stamp s' = state_next_exn_stamp s /\
                   (match r with
                      Rval vs -> type_v tvs ctMap tenvS' (HD vs) t2
                    | Rerr (Rraise v) -> type_v 0 ctMap tenvS' v Texn
                    | Rerr (Rabort Rtimeout_error) -> T
                    | Rerr (Rabort (Rffi_error _)) -> T
                    | Rerr (Rabort Rtype_error) -> F)`;;

let TPROPSAUX_ETS_IND =
  CONV_RULE (DEPTH_CONV BETA_CONV)
    (ISPECL [TPROPSAUX_ETS_P1; TPROPSAUX_ETS_P2] evaluate_ind);;

let TPROPSAUX_ETS_CASES = conjuncts (lhand (concl TPROPSAUX_ETS_IND));;

let TPROPSAUX_ETS k = el k TPROPSAUX_ETS_CASES;;

(* the cases of type_e for every assumption type_e .. (C ..) t *)
let TPROPSAUX_TE_ASM_CASES_TAC : tactic =
  REPEAT (FIRST_X_ASSUM (fun th ->
    let c = concl th in
    if TPROPSAUX_head_is "type_e" c && not (is_var (rand (rator c))) then
      MP_TAC (REWRITE_RULE (TPROPSAUX_TYEQS @
                [distinctness "exp"; injectivity "exp"; distinctness "lit"; injectivity "lit";
                 distinctness "option"; injectivity "option"])
                (ONCE_REWRITE_RULE[type_e_cases] th))
    else NO_TAC)) THEN
  REPEAT STRIP_TAC THEN TPROPSAUX_NORM_TAC THEN TPROPSAUX_NORM_TAC;;

(* the case of evaluate_ind: assumptions split, the evaluate equation and *)
(* the typing of the expressions unfolded                                  *)
let TPROPSAUX_ETS_START : tactic =
  REPEAT GEN_TAC THEN REWRITE_TAC[evaluate_def; good_ctMap_def; type_es_list_rel] THEN
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LIST_REL_CONS1; LIST_REL_NIL; PAIR_EQ]) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
  TPROPSAUX_NORM_TAC THEN REWRITE_TAC TPROPSAUX_TYEQS;;

(* the result with the unchanged store type *)
let TPROPSAUX_ETS_REFL_TAC : tactic =
  EXISTS_TAC `tenvS:tenv_store` THEN ASM_REWRITE_TAC[store_type_extension_refl] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC (ALL2 :: TPROPSAUX_TYEQS) THEN
  ASM_SIMP_TAC TPROPSAUX_TV_RULES;;

(* the type_v rule of closures *)
let TPROPSAUX_type_v_Closure = el 8 (CONJUNCTS type_v_rules);;

(* rewrite every assumption with the assumptions num_tvs .. = 0 *)
let TPROPSAUX_NUM_TVS_TAC : tactic = fun (asl,w as gl) ->
  let ths = filter (fun th -> let c = concl th in is_eq c && rhs c = `0` &&
                     TPROPSAUX_head_is "num_tvs" (lhs c)) (map snd asl) in
  RULE_ASSUM_TAC(fun th -> if mem th ths then th
                           else REWRITE_RULE (ADD_CLAUSES :: ths) th) gl;;

(* unfold type_all_env in the assumptions *)
let TPROPSAUX_TAE_TAC : tactic =   (* unfold type_all_env in the assumptions *)
  RULE_ASSUM_TAC(REWRITE_RULE[type_all_env_def; type_env_INFO.ri_accfupds; K_THM;
                              bind_tvar_rewrites; ADD_CLAUSES]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  TPROPSAUX_NUM_TVS_TAC;;

(* the induction hypothesis for the same state and environment *)
let TPROPSAUX_ETS_IH_TAC : tactic =
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`tenv:type_env`; `tenvE:tenv_val_exp`] THEN
  ASM_REWRITE_TAC[ALL2; is_value_def; ALL; type_es_list_rel] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[is_value_def; ALL]) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[CONS_11] THEN ASM_MESON_TAC[];;

(* the result value with the unchanged store type *)
let TPROPSAUX_ETS_FINISH_TAC : tactic =
  RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN TPROPSAUX_NORM_TAC THEN
  EXISTS_TAC `tenvS:tenv_store` THEN ASM_REWRITE_TAC[store_type_extension_refl] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC (ALL2 :: TPROPSAUX_TYEQS) THEN
  ASM_SIMP_TAC TPROPSAUX_TV_RULES;;

(* rewrite the assumptions satisfying p with the other assumptions *)
let TPROPSAUX_RW_ASM_TAC (p:term->bool) : tactic = fun (asl,w as gl) ->
  let ths = map snd asl in
  RULE_ASSUM_TAC(fun th -> if p (concl th) then
                    CASE_REWRITE_RULE (filter (fun th' -> not (th' == th)) ths) th
                  else th) gl;;

(* the unfolded evaluate assumption: case .. = (s',r) *)
let TPROPSAUX_is_eval_eq tm =
  is_eq tm && is_pair (rhs tm) &&
  (let a,b = dest_pair (rhs tm) in is_var a && is_var b) &&
  (is_case_app (lhs tm) || is_cond (lhs tm));;

(* split the unfolded evaluate assumption on its innermost case          *)
(* expression                                                              *)
let TPROPSAUX_EVAL_SPLIT_TAC : tactic = fun (asl,w as gl) ->
  let (_,eq) = find (fun (_,th) -> TPROPSAUX_is_eval_eq (concl th)) asl in
  let l = lhs (concl eq) in
  let ok t = (is_cond t || is_case_app t) &&
             (let x = scrutinee_of t in
              free_in x l && not (is_constructor_app x) && not (x = `T`) && not (x = `F`)) in
  let x = scrutinee_of (case_find_subterm ok l) in
  if type_of x = bool_ty then
    (ASM_CASES_TAC x THEN TPROPSAUX_RW_ASM_TAC TPROPSAUX_is_eval_eq) gl
  else
    (MP_TAC (ISPEC x (nchotomy_of_type (type_of x))) THEN
     DISCH_THEN(REPEAT_TCL STRIP_THM_THEN ASSUME_TAC) THEN
     TPROPSAUX_RW_ASM_TAC TPROPSAUX_is_eval_eq) gl;;

(* the goal ?tenvS'. .. with the given store type *)
let TPROPSAUX_ETS_EXISTS_TAC (tenv':term) : tactic =
  EXISTS_TAC tenv' THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LIST_REL_CONS2; LIST_REL_NIL; ALL2]) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
  TPROPSAUX_NORM_TAC THEN ASM_REWRITE_TAC[HD; ALL2];;

let TPROPSAUX_types_of (asl:(string*thm) list) (es:term) : term =
  let cs = map (concl o snd) asl in
  let rec go es =
    if is_comb es && is_comb (rator es) &&
       (try fst(dest_const(rator(rator es))) = "CONS" with Failure _ -> false) then
      let e = rand (rator es) and rest = rand es in
      let c = find (fun c -> TPROPSAUX_head_is "type_e" c && rand (rator c) = e) cs in
      let t = rand c in
      let r = go rest in
      mk_cons t r
    else if (try fst(dest_const es) = "NIL" with Failure _ -> false) then
      mk_const("NIL",[`:t`,`:A`])
    else if TPROPSAUX_head_is "REVERSE" es then
      mk_comb(mk_const("REVERSE",[`:t`,`:A`]), go (rand es))
    else
      let c = find (fun c -> TPROPSAUX_head_is "ALL2" c && rand (rator c) = es) cs in
      rand c in
  go es;;

(* apply the induction hypothesis of exp_type_sound (P1) for the evaluate   *)
(* call of an assumption evaluate st env es = (a,b): the types of es and     *)
(* their environment from the assumptions type_e tenv E e t (E =             *)
(* bind_tvar tvs tenvE or tenvE), with the given tvs and store type; the     *)
(* antecedent is discharged with the assumptions; the conclusion is          *)
(* stripped, its store type named nm                                          *)
let TPROPSAUX_APPLY_IH_T_TAC (tenv:term) (tvs:term) (tenvS:term) (nm:term) : tactic =
  fun (asl,w as gl) ->
  let is_call t = TPROPSAUX_head_is "evaluate" t in
  let eqs = filter (fun (_,th) -> let c = concl th in
                      is_eq c && is_pair (rhs c) && is_call (lhs c)) asl in
  let ihs = filter (fun (_,th) -> let vs,b = strip_forall (concl th) in
                      length vs = 7 && is_imp b &&
                      (let a1 = hd (conjuncts (lhand b)) in is_eq a1 && is_call (lhs a1))) asl in
  let cs = map (concl o snd) asl in
  let env_of es =
    try let e1 = hd (dest_list es) in
        let c = find (fun c -> TPROPSAUX_head_is "type_e" c && rand (rator c) = e1) cs in
        let ee = rand (rator (rator c)) in
        if TPROPSAUX_head_is "bind_tvar" ee then rand ee else ee
    with Failure _ ->
    try
      let e1 = rand (rator es) in
      let c = find (fun c -> TPROPSAUX_head_is "type_e" c && rand (rator c) = e1) cs in
      let ee = rand (rator (rator c)) in
      if TPROPSAUX_head_is "bind_tvar" ee then rand ee else ee
    with Failure _ ->
      let l = if TPROPSAUX_head_is "REVERSE" es then rand es else es in
      let c = find (fun c -> TPROPSAUX_head_is "ALL2" c && rand (rator c) = l &&
                             TPROPSAUX_head_is "type_e" (rand (rator (rator c)))) cs in
      let ee = rand (rand (rator (rator c))) in
      if TPROPSAUX_head_is "bind_tvar" ee then rand ee else ee in
  let pick (_,ih) =
    let vs,b = strip_forall (concl ih) in
    let a1 = hd (conjuncts (lhand b)) in
    let (_,eq) = find (fun (_,eq) -> lhs (concl eq) = lhs a1) eqs in
    let a,bb = dest_pair (rhs (concl eq)) in
    let es = rand (lhs a1) in
    ih, [bb; a; tenv; env_of es; TPROPSAUX_types_of asl es; tvs; tenvS] in
  let ih,tms = tryfind pick ihs in
  (MP_TAC (SPECL tms ih) THEN
   ANTS_TAC THENL
    [RULE_ASSUM_TAC(REWRITE_RULE[bind_tvar0; ALL; is_value_def]) THEN
     ASM_REWRITE_TAC[ALL2; ALL; is_value_def; bind_tvar0; bind_tvar_rewrites; ADD_CLAUSES;
                     good_ctMap_def; type_es_list_rel; CONS_11; tenv_val_exp_ok_def;
                     num_tvs_def; num_tvs_bind_var_list; LIST_REL_REVERSE_EQ;
                     EVERY_REVERSE; dec_clock_def; state_INFO.ri_accfupds; K_THM] THEN
     TRY (FIRST_ASSUM CONTR_TAC) THEN TRY (ASM_MESON_TAC[]);
     DISCH_THEN(X_CHOOSE_THEN nm STRIP_ASSUME_TAC)]) gl;;

let TPROPSAUX_APPLY_IH_TAC (tvs:term) (tenvS:term) (nm:term) : tactic =
  TPROPSAUX_APPLY_IH_T_TAC `tenv:type_env` tvs tenvS nm;;

(* the environment typing for a store type that extends tenvS *)

(* the environment typing for a store type that extends tenvS *)
let TPROPSAUX_WEAKEN_ENV_TAC (st1:term) : tactic =
  SUBGOAL_THEN (vsubst [st1, `tenvS1:tenv_store`]
    `type_all_env ctMap tenvS1 env
       (type_env_v_fupd (K (add_tenvE tenvE (type_env_v tenv))) tenv)`) ASSUME_TAC THENL
   [MATCH_MP_TAC type_all_env_weakening THEN
    MAP_EVERY EXISTS_TAC [`ctMap:ctMap`; `tenvS:tenv_store`] THEN
    ASM_SIMP_TAC[weakCT_refl; store_type_extension_weakS]; ALL_TAC];;

(* the induction hypotheses under a condition evaluate .. = (st',C v):   *)
(* resolved with the assumptions                                          *)
let TPROPSAUX_RESOLVE_IH_TAC : tactic = fun (asl,w as gl) ->
  let ths = map snd asl in
  let cond_ihs = filter (fun th -> let vs,b = strip_forall (concl th) in
                           vs <> [] && is_imp b &&
                           (let a = hd (conjuncts (lhand b)) in
                            is_eq a && (TPROPSAUX_head_is "evaluate" (lhs a) ||
                                        TPROPSAUX_head_is "evaluate_match" (lhs a))) &&
                           length vs < 7) ths in
  let rec under_foralls c tm =
    if is_forall tm then BINDER_CONV (under_foralls c) tm else c tm in
  let curry1 th = CONV_RULE (under_foralls (TRY_CONV (REWR_CONV (GSYM IMP_IMP)))) th in
  let rec discharge th =
    let vs,b = strip_forall (concl th) in
    if is_imp b && length vs < 7 then
      (try discharge (tryfind (fun a -> MATCH_MP (curry1 th) a) ths)
       with Failure _ -> th)
    else th in
  let new_ths = List.concat (map (fun ih -> mapfilter (fun eq ->
                   discharge (MATCH_MP (curry1 ih) eq)) ths) cond_ihs) in
  MAP_EVERY ASSUME_TAC new_ths gl;;

let TPROPSAUX_type_v_ext = prove
 (`!tvs ctMap tenvS1 tenvS2 v t.
     type_v tvs ctMap tenvS1 v t /\ store_type_extension tenvS1 tenvS2
     ==> type_v tvs ctMap tenvS2 v t`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP type_v_weakening) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[weakCT_refl; store_type_extension_weakS]);;

let TPROPSAUX_type_vs_ext = prove
 (`!tvs ctMap tenvS1 tenvS2 vs ts.
     ALL2 (type_v tvs ctMap tenvS1) vs ts /\ store_type_extension tenvS1 tenvS2
     ==> ALL2 (type_v tvs ctMap tenvS2) vs ts`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`type_v tvs ctMap tenvS1`; `type_v tvs ctMap tenvS2`;
                 `vs:v list`; `ts:t list`] (GEN_ALL MONO_ALL2)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_MESON_TAC[TPROPSAUX_type_v_ext]);;

(* the goal ?tenvS'. .. with the given store type, the facts of the     *)
(* induction hypotheses chained                                           *)
let TPROPSAUX_ETS_FIN_TAC (st':term) : tactic =
  EXISTS_TAC st' THEN CASE_REWRITE_TAC[] THEN RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
  RULE_ASSUM_TAC(fun th -> if TPROPSAUX_head_is "ALL2" (concl th)
                           then REWRITE_RULE[LIST_REL_CONS2; LIST_REL_NIL; ALL2] th
                           else th) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
  TPROPSAUX_NORM_TAC THEN ASM_REWRITE_TAC[HD; ALL2] THEN
  ASM_MESON_TAC[store_type_extension_trans; TPROPSAUX_type_v_ext; TPROPSAUX_type_vs_ext];;

(* the value of a boolean type: Boolv b, b split *)
let TPROPSAUX_CANON_BOOL_TAC : tactic =
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LIST_REL_CONS2; LIST_REL_NIL; ALL2]) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
  TPROPSAUX_NORM_TAC THEN MAP_EVERY IMP_RES_TAC TPROPSAUX_CCV_IMPS THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
  TPROPSAUX_NORM_TAC;;

(* split the boolean variables b of the values Boolv b, everywhere *)
let TPROPSAUX_BOOLV_CASES_TAC : tactic = fun (asl,w as gl) ->
  let tms = List.concat (map (fun (_,th) ->
              find_terms (fun t -> is_comb t && rator t = `Boolv` && is_var (rand t))
                         (concl th)) asl) in
  match setify (map rand tms) with
    [] -> ALL_TAC gl
  | b::_ ->
      (MP_TAC (SPEC b BOOL_CASES_AX) THEN DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THEN
       RULE_ASSUM_TAC(REWRITE_RULE[HD; do_if_def; do_log_def;
                                   semanticPrimitivesProps_Boolv_11;
                                   injectivity "option"; distinctness "option";
                                   distinctness "exp_or_val"; injectivity "exp_or_val"]) THEN
       TRY (FIRST_ASSUM CONTR_TAC) THEN TPROPSAUX_NORM_TAC) gl;;

(* the environment typing with a new variable *)
let TPROPSAUX_type_all_env_bind = prove
 (`!ctMap tenvS env tenv tenvE v t x.
     type_all_env ctMap tenvS env
       (type_env_v_fupd (K (add_tenvE tenvE (type_env_v tenv))) tenv) /\
     type_v 0 ctMap tenvS v t
     ==> type_all_env ctMap tenvS (sem_env_v_fupd (K (nsBind x v (sem_env_v env))) env)
           (type_env_v_fupd (K (add_tenvE (Bind_name x 0 t tenvE) (type_env_v tenv))) tenv)`,
  REWRITE_TAC[type_all_env_def; type_env_INFO.ri_accfupds; sem_env_INFO.ri_accfupds; K_THM;
              add_tenvE_def] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC nsAll2_nsBind THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[]);;

(* split a free variable of the given type *)
let TPROPSAUX_CASES_VAR_TAC (ty:hol_type) : tactic = fun (asl,w as gl) ->
  let fvs = freesl (w :: map (concl o snd) asl) in
  let v = find (fun v -> type_of v = ty) fvs in
  CASES_ON v gl;;

let TPROPSAUX_ets_nil = prove
 (TPROPSAUX_ETS 0, TPROPSAUX_ETS_START THEN TPROPSAUX_ETS_REFL_TAC);;

let TPROPSAUX_ets_cons = prove
 (TPROPSAUX_ETS 1,
  TPROPSAUX_ETS_START THEN REPEAT TPROPSAUX_EVAL_SPLIT_TAC THEN TPROPSAUX_NORM_TAC THEN
  TPROPSAUX_APPLY_IH_TAC `tvs:num` `tenvS:tenv_store` `tenvS1:tenv_store` THEN
  ((TPROPSAUX_RESOLVE_IH_TAC THEN TPROPSAUX_WEAKEN_ENV_TAC `tenvS1:tenv_store` THEN
    TPROPSAUX_APPLY_IH_TAC `tvs:num` `tenvS1:tenv_store` `tenvS2:tenv_store` THEN
    TPROPSAUX_ETS_FIN_TAC `tenvS2:tenv_store`) ORELSE
   TPROPSAUX_ETS_FIN_TAC `tenvS1:tenv_store`));;

let TPROPSAUX_ets_Lit = prove
 (TPROPSAUX_ETS 2,
  TPROPSAUX_ETS_START THEN TPROPSAUX_TE_ASM_CASES_TAC THEN TPROPSAUX_ETS_REFL_TAC);;

let TPROPSAUX_ets_Raise = prove
 (TPROPSAUX_ETS 3,
  TPROPSAUX_ETS_START THEN TPROPSAUX_TE_ASM_CASES_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[is_value_def; ALL]) THEN TPROPSAUX_NORM_TAC THEN
  REPEAT TPROPSAUX_EVAL_SPLIT_TAC THEN TPROPSAUX_NORM_TAC THEN
  TPROPSAUX_APPLY_IH_TAC `0` `tenvS:tenv_store` `tenvS1:tenv_store` THEN
  TPROPSAUX_ETS_EXISTS_TAC `tenvS1:tenv_store`);;

let TPROPSAUX_ets_Var = prove
 (TPROPSAUX_ETS 6,
  TPROPSAUX_ETS_START THEN TPROPSAUX_TE_ASM_CASES_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[bind_tvar_rewrites]) THEN TPROPSAUX_NUM_TVS_TAC THEN
  IMP_RES_TAC lookup_var_sound THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
  TPROPSAUX_RW_ASM_TAC TPROPSAUX_is_eval_eq THEN TPROPSAUX_ETS_FINISH_TAC);;

let TPROPSAUX_ets_Fun = prove
 (TPROPSAUX_ETS 7,
  TPROPSAUX_ETS_START THEN TPROPSAUX_TE_ASM_CASES_TAC THEN
  EXISTS_TAC `tenvS:tenv_store` THEN ASM_REWRITE_TAC[store_type_extension_refl] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC (ALL2 :: TPROPSAUX_TYEQS) THEN
  MATCH_MP_TAC (REWRITE_RULE TPROPSAUX_TYEQS TPROPSAUX_type_v_Closure) THEN
  MAP_EVERY EXISTS_TAC [`tenv:type_env`; `tenvE:tenv_val_exp`] THEN
  TPROPSAUX_TAE_TAC THEN ASM_REWRITE_TAC[]);;

let TPROPSAUX_ets_Tannot = prove
 (TPROPSAUX_ETS 14,
  TPROPSAUX_ETS_START THEN TPROPSAUX_TE_ASM_CASES_TAC THEN TPROPSAUX_ETS_IH_TAC);;

let TPROPSAUX_ets_Lannot = prove
 (TPROPSAUX_ETS 15,
  TPROPSAUX_ETS_START THEN TPROPSAUX_TE_ASM_CASES_TAC THEN TPROPSAUX_ETS_IH_TAC);;

let TPROPSAUX_ets_match_nil = prove
 (TPROPSAUX_ETS 16, TPROPSAUX_ETS_START THEN TPROPSAUX_ETS_REFL_TAC);;

let TPROPSAUX_ets_Log_TAC : tactic =
  TPROPSAUX_ETS_START THEN TPROPSAUX_TE_ASM_CASES_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[is_value_def; ALL]) THEN TPROPSAUX_NORM_TAC THEN
  REPEAT TPROPSAUX_EVAL_SPLIT_TAC THEN TPROPSAUX_NORM_TAC THEN
  TPROPSAUX_APPLY_IH_TAC `0` `tenvS:tenv_store` `tenvS1:tenv_store` THEN
  ((TPROPSAUX_RESOLVE_IH_TAC THEN TPROPSAUX_CANON_BOOL_TAC THEN
    TPROPSAUX_CASES_VAR_TAC `:lop` THEN TPROPSAUX_BOOLV_CASES_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[distinctness "lop"]) THEN TRY (FIRST_ASSUM CONTR_TAC) THEN
    ((TPROPSAUX_WEAKEN_ENV_TAC `tenvS1:tenv_store` THEN
      TPROPSAUX_APPLY_IH_TAC `0` `tenvS1:tenv_store` `tenvS2:tenv_store` THEN
      TPROPSAUX_ETS_FIN_TAC `tenvS2:tenv_store`) ORELSE
     (TPROPSAUX_ETS_FIN_TAC `tenvS1:tenv_store`))) ORELSE
   TPROPSAUX_ETS_FIN_TAC `tenvS1:tenv_store`);;

let TPROPSAUX_ets_Log = prove (TPROPSAUX_ETS 9, TPROPSAUX_ets_Log_TAC);;

let TPROPSAUX_ets_If_TAC : tactic =
  TPROPSAUX_ETS_START THEN TPROPSAUX_TE_ASM_CASES_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[is_value_def; ALL]) THEN TPROPSAUX_NORM_TAC THEN
  REPEAT TPROPSAUX_EVAL_SPLIT_TAC THEN TPROPSAUX_NORM_TAC THEN
  TPROPSAUX_APPLY_IH_TAC `0` `tenvS:tenv_store` `tenvS1:tenv_store` THEN
  ((TPROPSAUX_RESOLVE_IH_TAC THEN TPROPSAUX_CANON_BOOL_TAC THEN TPROPSAUX_BOOLV_CASES_TAC THEN
    TPROPSAUX_WEAKEN_ENV_TAC `tenvS1:tenv_store` THEN
    TPROPSAUX_APPLY_IH_TAC `0` `tenvS1:tenv_store` `tenvS2:tenv_store` THEN
    TPROPSAUX_ETS_FIN_TAC `tenvS2:tenv_store`) ORELSE
   TPROPSAUX_ETS_FIN_TAC `tenvS1:tenv_store`);;

let TPROPSAUX_ets_If = prove (TPROPSAUX_ETS 10, TPROPSAUX_ets_If_TAC);;

let TPROPSAUX_ets_Let_TAC : tactic =
  TPROPSAUX_ETS_START THEN TPROPSAUX_TE_ASM_CASES_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[is_value_def; ALL]) THEN TPROPSAUX_NORM_TAC THEN
  REPEAT TPROPSAUX_EVAL_SPLIT_TAC THEN TPROPSAUX_NORM_TAC THEN
  TPROPSAUX_APPLY_IH_TAC `0` `tenvS:tenv_store` `tenvS1:tenv_store` THEN
  ((TPROPSAUX_RESOLVE_IH_TAC THEN TPROPSAUX_CANON_BOOL_TAC THEN
    TPROPSAUX_CASES_VAR_TAC `:mlstring option` THEN
    RULE_ASSUM_TAC(CASE_REWRITE_RULE[opt_bind_name_def; nsOptBind_def; bind_tvar0; HD;
                                     with_same_v]) THEN
    IMP_RES_TAC type_v_freevars THEN TPROPSAUX_WEAKEN_ENV_TAC `tenvS1:tenv_store` THEN
    IMP_RES_TAC TPROPSAUX_type_all_env_bind THEN
    TPROPSAUX_APPLY_IH_TAC `0` `tenvS1:tenv_store` `tenvS2:tenv_store` THEN
    TPROPSAUX_ETS_FIN_TAC `tenvS2:tenv_store`) ORELSE
   TPROPSAUX_ETS_FIN_TAC `tenvS1:tenv_store`);;

let TPROPSAUX_ets_Let = prove (TPROPSAUX_ETS 12, TPROPSAUX_ets_Let_TAC);;

(* replace the implicational assumptions A ==> B whose A is an assumption *)
(* by B                                                                     *)
let TPROPSAUX_MP_ASSUM_TAC : tactic = fun (asl,w as gl) ->
  let ths = map snd asl in
  let find_a t = find (fun a -> concl a = t) ths in
  let ok th = is_imp (concl th) && can (map find_a) (conjuncts (lhand (concl th))) in
  let imps = filter ok ths in
  MAP_EVERY (fun th ->
    ASSUME_TAC (MP th (end_itlist CONJ (map find_a (conjuncts (lhand (concl th))))))) imps gl;;

(* Letrec: the typing facts of the body's environment *)
let TPROPSAUX_LETREC_ENV_TAC : tactic = fun (asl,w as gl) ->
  let cs = map (concl o snd) asl in
  let tf = find (fun c -> TPROPSAUX_head_is "type_funs" c) cs in
  let _,args = strip_comb tf in
  let ee = el 1 args and funs = el 2 args and bs = el 3 args in
  let base = rand ee in
  let g1 = list_mk_comb(`tenv_val_exp_ok`, [ee]) in
  let g2 = vsubst [funs, `funs:(mlstring#mlstring#exp)list`; ee, `ee:tenv_val_exp`]
     `type_all_env ctMap tenvS
        (sem_env_v_fupd (K (build_rec_env funs env (sem_env_v env))) env)
        (type_env_v_fupd (K (add_tenvE ee (type_env_v tenv))) tenv)` in
  (SUBGOAL_THEN g1 ASSUME_TAC THENL
    [MATCH_MP_TAC tenv_val_exp_ok_bvl_funs THEN ASM_MESON_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN g2 ASSUME_TAC THENL
    [TPROPSAUX_TAE_TAC THEN
     REWRITE_TAC[type_all_env_def; type_env_INFO.ri_accfupds; sem_env_INFO.ri_accfupds; K_THM;
                 build_rec_env_merge; nsAppend_to_nsBindList; add_tenvE_bvl] THEN
     ASM_REWRITE_TAC[] THEN MATCH_MP_TAC nsAll2_nsBindList THEN ASM_REWRITE_TAC[] THEN
     BETA_TAC THEN MATCH_MP_TAC (BETA_RULE type_recfun_env) THEN
     EXISTS_TAC `tenv:type_env` THEN EXISTS_TAC base THEN
     ASM_REWRITE_TAC[type_all_env_def; type_env_INFO.ri_accfupds; K_THM; bind_tvar0] THEN
     ASM_MESON_TAC[type_funs_distinct; fst_triple];
     ALL_TAC]) gl;;

let TPROPSAUX_ets_Letrec_TAC : tactic =
  TPROPSAUX_ETS_START THEN TPROPSAUX_TE_ASM_CASES_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[is_value_def; ALL]) THEN TPROPSAUX_NORM_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[bind_tvar0]) THEN
  TPROPSAUX_EVAL_SPLIT_TAC THENL
   [TPROPSAUX_MP_ASSUM_TAC THEN TPROPSAUX_LETREC_ENV_TAC THEN
    TPROPSAUX_APPLY_IH_TAC `0` `tenvS:tenv_store` `tenvS1:tenv_store` THEN
    TPROPSAUX_ETS_FIN_TAC `tenvS1:tenv_store`;
    ASM_MESON_TAC[type_funs_distinct]];;

let TPROPSAUX_ets_Letrec = prove (TPROPSAUX_ETS 13, TPROPSAUX_ets_Letrec_TAC);;

(* split the unfolded evaluate assumption on its outermost case expression *)
let TPROPSAUX_EVAL_SPLIT_OUTER_TAC : tactic = fun (asl,w as gl) ->
  let (_,eq) = find (fun (_,th) -> TPROPSAUX_is_eval_eq (concl th)) asl in
  let l = lhs (concl eq) in
  let ok t = (is_cond t || is_case_app t) &&
             (let x = scrutinee_of t in
              free_in x l && not (is_constructor_app x) && not (x = `T`) && not (x = `F`)) in
  let x = scrutinee_of (find_term ok l) in
  if type_of x = bool_ty then
    (ASM_CASES_TAC x THEN TPROPSAUX_RW_ASM_TAC TPROPSAUX_is_eval_eq) gl
  else
    (MP_TAC (ISPEC x (nchotomy_of_type (type_of x))) THEN
     DISCH_THEN(REPEAT_TCL STRIP_THM_THEN ASSUME_TAC) THEN
     TPROPSAUX_RW_ASM_TAC TPROPSAUX_is_eval_eq) gl;;

(* a copy of type_all_env, unfolded *)
let TPROPSAUX_TAE_COPY_TAC : tactic =
  FIRST_ASSUM(STRIP_ASSUME_TAC o
    REWRITE_RULE[type_all_env_def; type_env_INFO.ri_accfupds; K_THM] o
    check (TPROPSAUX_head_is "type_all_env" o concl));;

(* Con: the impossible case do_con_check false *)
let TPROPSAUX_CON_CONTR_TAC : tactic =
  TPROPSAUX_TAE_COPY_TAC THEN IMP_RES_TAC TPROPSAUX_tenvC_lookup THEN
  IMP_RES_TAC LIST_REL_LENGTH THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_MAP]) THEN
  TPROPSAUX_POP_MATCH `~do_con_check a b c` THEN
  REWRITE_TAC[do_con_check_def] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[];;

(* the type_v rule of tuples *)
let TPROPSAUX_type_v_ConvNONE = el 7 (CONJUNCTS type_v_rules);;

(* Con: build_conv of a constructor *)
let TPROPSAUX_CON_BC_TAC : tactic =   (* build_conv of a constructor *)
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN TPROPSAUX_TAE_COPY_TAC THEN
  IMP_RES_TAC build_conv_type_sound THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
  TPROPSAUX_RW_ASM_TAC (fun t -> is_eq t && TPROPSAUX_head_is "build_conv" (lhs t)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[injectivity "option"; distinctness "option"]) THEN
  TRY (FIRST_ASSUM CONTR_TAC) THEN TPROPSAUX_NORM_TAC;;

(* Con: build_conv of a tuple *)
let TPROPSAUX_CON_BCN_TAC : tactic =   (* build_conv of a tuple *)
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[build_conv_def]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[injectivity "option"; distinctness "option"]) THEN
  TRY (FIRST_ASSUM CONTR_TAC) THEN TPROPSAUX_NORM_TAC THEN
  FIRST_ASSUM(fun th -> if TPROPSAUX_head_is "ALL2" (concl th) &&
                           TPROPSAUX_head_is "REVERSE" (rand (concl th))
                        then ASSUME_TAC (REWRITE_RULE[EVERY2_REVERSE1] th) else NO_TAC) THEN
  IMP_RES_TAC (REWRITE_RULE TPROPSAUX_TYEQS TPROPSAUX_type_v_ConvNONE);;

let TPROPSAUX_ets_Con_TAC : tactic =
  let fin = TPROPSAUX_ETS_FIN_TAC `tenvS1:tenv_store` in
  TPROPSAUX_ETS_START THEN TPROPSAUX_TE_ASM_CASES_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[is_value_def; ALL; type_es_list_rel]) THEN TPROPSAUX_NORM_TAC THEN
  TPROPSAUX_EVAL_SPLIT_OUTER_TAC THENL
   [TPROPSAUX_MP_ASSUM_TAC THEN REPEAT TPROPSAUX_EVAL_SPLIT_TAC THEN TPROPSAUX_NORM_TAC THEN
    TPROPSAUX_APPLY_IH_TAC `tvs:num` `tenvS:tenv_store` `tenvS1:tenv_store` THENL
     [TPROPSAUX_CON_BC_TAC; TPROPSAUX_CON_BC_TAC THEN fin; fin];
    TPROPSAUX_CON_CONTR_TAC;
    TPROPSAUX_MP_ASSUM_TAC THEN REPEAT TPROPSAUX_EVAL_SPLIT_TAC THEN TPROPSAUX_NORM_TAC THEN
    TPROPSAUX_APPLY_IH_TAC `tvs:num` `tenvS:tenv_store` `tenvS1:tenv_store` THENL
     [TPROPSAUX_CON_BCN_TAC; TPROPSAUX_CON_BCN_TAC THEN fin; fin];
    TPROPSAUX_CON_CONTR_TAC];;
let TPROPSAUX_ets_Con = prove (TPROPSAUX_ETS 5, TPROPSAUX_ets_Con_TAC);;

(* the patterns of well-typed matches cannot give a type error *)
let TPROPSAUX_can_pmatch_all = prove
 (`!ctMap (envc:(mlstring,mlstring,num#stamp)namespace) tenv refs tenvS ps v t tvs.
     ctMap_ok ctMap /\ nsAll2 (type_ctor ctMap) envc (type_env_c tenv) /\
     type_s ctMap refs tenvS /\ type_v tvs ctMap tenvS v t /\
     (!p. MEM p ps ==> ?bs. type_p tvs tenv p t bs)
     ==> can_pmatch_all envc refs ps v`,
  REWRITE_TAC[can_pmatch_all_EVERY; GSYM ALL_MEM] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:pat`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `bs:(mlstring#t)list`) THEN
  MP_TAC (ISPECL [`envc:(mlstring,mlstring,num#stamp)namespace`; `refs:(v store_v)list`;
                  `x:pat`; `v:v`; `[]:(mlstring#v)list`; `tenv:type_env`; `ctMap:ctMap`;
                  `[]:(mlstring#t)list`; `t:t`; `bs:(mlstring#t)list`; `tenvS:tenv_store`;
                  `tvs:num`] (CONJUNCT1 pat_type_sound)) THEN
  ASM_REWRITE_TAC[ALL2; distinctness "match_result"]);;

(* apply the induction hypothesis of exp_type_sound for evaluate_match (P2) *)
(* for an assumption evaluate_match .. = (a,b), with the given t1 t2 tvs   *)
(* and store type                                                            *)
let TPROPSAUX_APPLY_IH2_TAC (extra:term list) (nm:term) : tactic = fun (asl,w as gl) ->
  let is_call t = TPROPSAUX_head_is "evaluate_match" t in
  let eqs = filter (fun (_,th) -> let c = concl th in
                      is_eq c && is_pair (rhs c) && is_call (lhs c)) asl in
  let ihs = filter (fun (_,th) -> let vs,b = strip_forall (concl th) in
                      length vs = 8 && is_imp b &&
                      (let a1 = hd (conjuncts (lhand b)) in is_eq a1 && is_call (lhs a1))) asl in
  let pick (_,ih) =
    let vs,b = strip_forall (concl ih) in
    let a1 = hd (conjuncts (lhand b)) in
    let (_,eq) = find (fun (_,eq) -> lhs (concl eq) = lhs a1) eqs in
    let a,bb = dest_pair (rhs (concl eq)) in
    ih, [bb; a; `tenv:type_env`; `tenvE:tenv_val_exp`] @ extra in
  let ih,tms = tryfind pick ihs in
  (MP_TAC (SPECL tms ih) THEN
   ANTS_TAC THENL
    [RULE_ASSUM_TAC(REWRITE_RULE[bind_tvar0; HD]) THEN TPROPSAUX_NUM_TVS_TAC THEN
     ASM_REWRITE_TAC[good_ctMap_def; type_pes_def; bind_tvar0; HD] THEN
     ASM_SIMP_TAC[TPROPSAUX_type_v_exn'; bind_exn_v_def] THEN
     TRY (FIRST_ASSUM CONTR_TAC) THEN TRY (ASM_MESON_TAC[]);
     DISCH_THEN(X_CHOOSE_THEN nm STRIP_ASSUME_TAC)]) gl;;

(* the result type of the goal of a P1 case: the head of its type list *)
let TPROPSAUX_goal_type (w:term) : term =
  let t = find_term (fun t -> TPROPSAUX_head_is "ALL2" t &&
                              TPROPSAUX_head_is "type_v" (rand (rator (rator t)))) w in
  hd (dest_list (rand t));;

(* evaluate_match returns one value *)
let TPROPSAUX_MATCH_SING_TAC : tactic =
  CASES_ON `r:(v list,v)result` THEN CASE_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
  TRY (IMP_RES_TAC (CONJUNCT1 (CONJUNCT2 evaluate_length)) THEN
       RULE_ASSUM_TAC(REWRITE_RULE[sing_list]) THEN
       REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
       TPROPSAUX_NORM_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[HD]));;

(* Handle: the raised exception is handled *)
let TPROPSAUX_HANDLE_RAISE_TAC : tactic = fun (asl,w as gl) ->
  let t2 = TPROPSAUX_goal_type w in
  (RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN TPROPSAUX_RESOLVE_IH_TAC THEN
   TPROPSAUX_WEAKEN_ENV_TAC `tenvS1:tenv_store` THEN
   TPROPSAUX_APPLY_IH2_TAC [`Tapp [] 3`; t2; `0`; `tenvS1:tenv_store`] `tenvS2:tenv_store` THEN
   TPROPSAUX_MATCH_SING_TAC THEN TPROPSAUX_ETS_FIN_TAC `tenvS2:tenv_store`) gl;;

(* Handle: the impossible case can_pmatch_all false *)
let TPROPSAUX_HANDLE_CONTR_TAC : tactic =
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN TPROPSAUX_TAE_COPY_TAC THEN
  TPROPSAUX_POP_MATCH `~can_pmatch_all a b c d` THEN
  MATCH_MP_TAC (TAUT `p ==> ~p ==> q`) THEN
  MATCH_MP_TAC TPROPSAUX_can_pmatch_all THEN
  MAP_EVERY EXISTS_TAC [`ctMap:ctMap`; `tenv:type_env`] THEN
  ASM_REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM] THEN ASM_MESON_TAC[];;

let TPROPSAUX_ets_Handle_TAC : tactic =
  let fin = TPROPSAUX_ETS_FIN_TAC `tenvS1:tenv_store` in
  TPROPSAUX_ETS_START THEN TPROPSAUX_TE_ASM_CASES_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[is_value_def; ALL]) THEN TPROPSAUX_NORM_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[bind_tvar0]) THEN TPROPSAUX_NUM_TVS_TAC THEN
  REPEAT TPROPSAUX_EVAL_SPLIT_TAC THEN TPROPSAUX_NORM_TAC THEN
  TPROPSAUX_APPLY_IH_TAC `0` `tenvS:tenv_store` `tenvS1:tenv_store` THENL
   [fin; TPROPSAUX_HANDLE_RAISE_TAC; TPROPSAUX_HANDLE_CONTR_TAC; fin];;
let TPROPSAUX_ets_Handle = prove (TPROPSAUX_ETS 4, TPROPSAUX_ets_Handle_TAC);;

(* the type of the expression of an assumption evaluate st env [e] = .. *)
let TPROPSAUX_eval_type (asl:(string*thm) list) : term =
  let cs = map (concl o snd) asl in
  let eq = find (fun c -> is_eq c && TPROPSAUX_head_is "evaluate" (lhs c) &&
                          length (dest_list (rand (lhs c))) = 1) cs in
  let e = hd (dest_list (rand (lhs eq))) in
  rand (find (fun c -> TPROPSAUX_head_is "type_e" c && rand (rator c) = e) cs);;

(* Mat: the value is matched *)
let TPROPSAUX_MAT_RVAL_TAC : tactic = fun (asl,w as gl) ->
  let t2 = TPROPSAUX_goal_type w and t1 = TPROPSAUX_eval_type asl in
  (RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN TPROPSAUX_RESOLVE_IH_TAC THEN
   RULE_ASSUM_TAC(fun th -> if TPROPSAUX_head_is "ALL2" (concl th)
                            then REWRITE_RULE[LIST_REL_CONS2; LIST_REL_NIL; ALL2] th
                            else th) THEN
   REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
   TPROPSAUX_NORM_TAC THEN
   TPROPSAUX_WEAKEN_ENV_TAC `tenvS1:tenv_store` THEN
   TPROPSAUX_APPLY_IH2_TAC [t1; t2; `0`; `tenvS1:tenv_store`] `tenvS2:tenv_store` THEN
   TPROPSAUX_MATCH_SING_TAC THEN TPROPSAUX_ETS_FIN_TAC `tenvS2:tenv_store`) gl;;

(* Mat: the impossible case can_pmatch_all false *)
let TPROPSAUX_MAT_CONTR_TAC : tactic =
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
  RULE_ASSUM_TAC(fun th -> if TPROPSAUX_head_is "ALL2" (concl th)
                           then REWRITE_RULE[LIST_REL_CONS2; LIST_REL_NIL; ALL2] th
                           else th) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
  TPROPSAUX_NORM_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[HD]) THEN TPROPSAUX_TAE_COPY_TAC THEN
  TPROPSAUX_POP_MATCH `~can_pmatch_all a b c d` THEN
  MATCH_MP_TAC (TAUT `p ==> ~p ==> q`) THEN
  MATCH_MP_TAC TPROPSAUX_can_pmatch_all THEN
  MAP_EVERY EXISTS_TAC [`ctMap:ctMap`; `tenv:type_env`] THEN
  ASM_REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM] THEN ASM_MESON_TAC[];;

let TPROPSAUX_ets_Mat_TAC : tactic =
  TPROPSAUX_ETS_START THEN TPROPSAUX_TE_ASM_CASES_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[is_value_def; ALL]) THEN TPROPSAUX_NORM_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[bind_tvar0]) THEN TPROPSAUX_NUM_TVS_TAC THEN
  REPEAT TPROPSAUX_EVAL_SPLIT_TAC THEN TPROPSAUX_NORM_TAC THEN
  TPROPSAUX_APPLY_IH_TAC `0` `tenvS:tenv_store` `tenvS1:tenv_store` THENL
   [TPROPSAUX_MAT_RVAL_TAC; TPROPSAUX_MAT_CONTR_TAC;
    TPROPSAUX_ETS_FIN_TAC `tenvS1:tenv_store`];;
let TPROPSAUX_ets_Mat = prove (TPROPSAUX_ETS 11, TPROPSAUX_ets_Mat_TAC);;

let TPROPSAUX_type_v_0 = prove
 (`!ctMap tenvS v t tvs. type_v 0 ctMap tenvS v t ==> type_v tvs ctMap tenvS v t`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP type_v_weakening) THEN
  DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[weakCT_refl; weakS_refl]);;

(* the bindings of a match as namespace bindings *)
let TPROPSAUX_bindings_ALL2 = prove
 (CASE_TERM `!tvs ctMap tenvS (bs':(mlstring#v)list) (bs:(mlstring#t)list).
     ALL2 (\xv xt. match xv with (x,v) -> match xt with (x',t) ->
                     x = x' /\ type_v tvs ctMap tenvS v t) bs' bs
     ==> ALL2 (\xy xy'. match xy with (x,y) -> match xy' with (x',y') ->
                x = x' /\ (match y' with (tvs',t) -> type_v tvs' ctMap tenvS y t))
              bs' (MAP (\p. match p with (x,t) -> (x,(tvs,t))) bs)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[ALL2; MAP] THEN
  SPEC_TAC(`h:mlstring#v`,`h:mlstring#v`) THEN SPEC_TAC(`h':mlstring#t`,`h':mlstring#t`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN CASE_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* the evaluate_match case Match: the environment of the clause *)
let TPROPSAUX_MATCH_ENV_TAC : tactic =
  SUBGOAL_THEN `tenv_val_exp_ok (bind_var_list tvs bindings tenvE)` ASSUME_TAC THENL
   [MATCH_MP_TAC (MATCH_MP (CONJUNCT1 type_p_bvl)
      (ASSUME `type_p tvs tenv p t1 (bindings:(mlstring#t)list)`)) THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `type_all_env ctMap tenvS
      (sem_env_v_fupd (K (nsAppend (alist_to_ns bindings') (sem_env_v env))) env)
      (type_env_v_fupd (K (add_tenvE (bind_var_list tvs bindings tenvE) (type_env_v tenv)))
         tenv)` ASSUME_TAC THENL
   [TPROPSAUX_TAE_COPY_TAC THEN
    REWRITE_TAC[type_all_env_def; type_env_INFO.ri_accfupds; sem_env_INFO.ri_accfupds;
                K_THM; add_tenvE_bvl; nsAppend_to_nsBindList] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC nsAll2_nsBindList THEN ASM_REWRITE_TAC[] THEN
    BETA_TAC THEN MATCH_MP_TAC TPROPSAUX_bindings_ALL2 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[APPEND_NIL]) THEN ASM_REWRITE_TAC[];
    ALL_TAC];;

let TPROPSAUX_ets_match_cons_TAC : tactic =
  TPROPSAUX_ETS_START THEN
  SUBGOAL_THEN `type_pes tvs tvs tenv tenvE pes t1 t2 /\
                (?bindings. ALL_DISTINCT (pat_bindings p) /\ type_p tvs tenv p t1 bindings /\
                            type_e tenv (bind_var_list tvs bindings tenvE) e t2)`
    STRIP_ASSUME_TAC THENL
   [TPROPSAUX_POP "type_pes" THEN REWRITE_TAC[type_pes_def; MEM; PAIR_EQ] THEN MESON_TAC[];
    ALL_TAC] THEN
  TPROPSAUX_TAE_COPY_TAC THEN
  MP_TAC (ISPECL [`sem_env_c (env:v sem_env)`; `state_refs (st:(FFI)state)`; `p:pat`; `v:v`;
                  `[]:(mlstring#v)list`; `tenv:type_env`; `ctMap:ctMap`; `[]:(mlstring#t)list`;
                  `t1:t`; `bindings:(mlstring#t)list`; `tenvS:tenv_store`; `tvs:num`]
                 (CONJUNCT1 pat_type_sound)) THEN
  ASM_REWRITE_TAC[ALL2] THEN STRIP_TAC THEN
  TPROPSAUX_RW_ASM_TAC TPROPSAUX_is_eval_eq THEN TPROPSAUX_NORM_TAC THEN
  TPROPSAUX_MP_ASSUM_TAC THENL
   [TPROPSAUX_APPLY_IH2_TAC [`t1:t`; `t2:t`; `tvs:num`; `tenvS:tenv_store`] `tenvS1:tenv_store`
    THEN TPROPSAUX_ETS_FIN_TAC `tenvS1:tenv_store`;
    FIRST_X_ASSUM(fun th -> let vs,b = strip_forall (concl th) in
                    if length vs = 1 && is_imp b then
                      ASSUME_TAC (SPEC `bindings':(mlstring#v)list` th) else NO_TAC) THEN
    TPROPSAUX_MP_ASSUM_TAC THEN TPROPSAUX_MATCH_ENV_TAC THEN
    TPROPSAUX_APPLY_IH_TAC `0` `tenvS:tenv_store` `tenvS1:tenv_store` THEN
    RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
    CASES_ON `r:(v list,v)result` THEN CASE_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[LIST_REL_CONS2; LIST_REL_NIL]) THEN
    REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
    TPROPSAUX_NORM_TAC THEN IMP_RES_TAC TPROPSAUX_type_v_0 THEN
    TPROPSAUX_ETS_FIN_TAC `tenvS1:tenv_store`];;

let TPROPSAUX_ets_match_cons = prove (TPROPSAUX_ETS 17, TPROPSAUX_ets_match_cons_TAC);;

(* the operator classes *)
let TPROPSAUX_getOpClass = prove
 (`!op. (getOpClass op = FunApp ==> op = Opapp) /\
        (getOpClass op = EvalOp ==> op = Eval) /\
        (getOpClass op = Force ==> op = ThunkOp ForceThunk) /\
        (getOpClass op = Simple ==> ~(op = Opapp))`,
  GEN_TAC THEN CASES_ON `op:op` THEN REWRITE_TAC[getOpClass_def] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[distinctness "op_class"; distinctness "op";
                                      injectivity "op"] THEN
  TRY (CASES_ON `a:thunk_op` THEN CASE_REWRITE_TAC[] THEN
       REWRITE_TAC[distinctness "op_class"; distinctness "thunk_op"]));;

(* App: operators that have no type *)
let TPROPSAUX_APP_CONTR_TAC : tactic =
  RULE_ASSUM_TAC(REWRITE_RULE[type_op_cases; distinctness "op"]) THEN FIRST_ASSUM CONTR_TAC;;

(* App: function application *)
let TPROPSAUX_APP_FUN_TAC : tactic =
  RULE_ASSUM_TAC(REWRITE_RULE[EVERY2_REVERSE1]) THEN
  MP_TAC (ISPECL [`ctMap:ctMap`; `tenvS1:tenv_store`; `REVERSE (a:v list)`; `ts:t list`;
                  `h':t`] opapp_type_sound) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `env1:v sem_env` (X_CHOOSE_THEN `e1:exp`
    (X_CHOOSE_THEN `tenv1:type_env` (X_CHOOSE_THEN `tenvE1:tenv_val_exp`
       STRIP_ASSUME_TAC)))) THEN
  TPROPSAUX_RW_ASM_TAC TPROPSAUX_is_eval_eq THEN TPROPSAUX_EVAL_SPLIT_TAC THEN
  TPROPSAUX_NORM_TAC THENL
   [TPROPSAUX_ETS_FIN_TAC `tenvS1:tenv_store`;
    TPROPSAUX_RESOLVE_IH_TAC THEN
    TPROPSAUX_APPLY_IH_T_TAC `tenv1:type_env` `0` `tenvS1:tenv_store` `tenvS2:tenv_store` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[dec_clock_def; state_INFO.ri_accfupds; K_THM]) THEN
    TPROPSAUX_ETS_FIN_TAC `tenvS2:tenv_store`];;

let TPROPSAUX_list_result_case = prove
 (CASE_TERM `!ctMap tenvS (r:(v,v)result) t.
     (match r with
        Rval v -> type_v 0 ctMap tenvS v t
      | Rerr (Rraise v) -> type_v 0 ctMap tenvS v (Tapp [] 3)
      | Rerr (Rabort (Rffi_error _)) -> T
      | Rerr (Rabort _) -> F)
     ==> (match list_result r with
            Rval vs -> ALL2 (type_v 0 ctMap tenvS) vs [t]
          | Rerr (Rraise v) -> type_v 0 ctMap tenvS v (Tapp [] 3)
          | Rerr (Rabort Rtimeout_error) -> T
          | Rerr (Rabort (Rffi_error _)) -> T
          | Rerr (Rabort Rtype_error) -> F)`,
  REPEAT GEN_TAC THEN CASES_ON `r:(v,v)result` THEN
  REWRITE_TAC[list_result_def] THEN CASE_REWRITE_TAC[ALL2] THEN
  TRY (CASES_ON `a:(v)error_result` THEN CASE_REWRITE_TAC[] THEN
       TRY (CASES_ON `a':abort` THEN CASE_REWRITE_TAC[])));;

(* App: primitive operators *)
let TPROPSAUX_APP_SIMPLE_TAC : tactic =
  MP_TAC (ISPECL [`ctMap:ctMap`; `tenvS1:tenv_store`; `a:v list`; `op':op`; `ts:t list`;
                  `h':t`; `state_refs (x:(FFI)state)`; `state_ffi (x:(FFI)state)`]
                 op_type_sound) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[good_ctMap_def]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `tenvS2:tenv_store` (X_CHOOSE_THEN `store1:(v store_v)list`
    (X_CHOOSE_THEN `ffi1:(FFI)ffi_state` (X_CHOOSE_THEN `r1:(v,v)result`
       STRIP_ASSUME_TAC)))) THEN
  TPROPSAUX_RW_ASM_TAC TPROPSAUX_is_eval_eq THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN TPROPSAUX_NORM_TAC THEN
  EXISTS_TAC `tenvS2:tenv_store` THEN
  REWRITE_TAC[state_INFO.ri_accfupds; K_THM] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[store_type_extension_trans]; ALL_TAC] THEN
  MATCH_MP_TAC TPROPSAUX_list_result_case THEN ASM_REWRITE_TAC[];;

let TPROPSAUX_ets_App_TAC : tactic =
  TPROPSAUX_ETS_START THEN TPROPSAUX_TE_ASM_CASES_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[is_value_def; ALL; type_es_list_rel]) THEN TPROPSAUX_NORM_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[bind_tvar0]) THEN TPROPSAUX_NUM_TVS_TAC THEN
  TPROPSAUX_EVAL_SPLIT_OUTER_TAC THEN TPROPSAUX_EVAL_SPLIT_OUTER_TAC THEN TPROPSAUX_NORM_TAC THEN
  TPROPSAUX_APPLY_IH_TAC `0` `tenvS:tenv_store` `tenvS1:tenv_store` THENL
   [RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN TPROPSAUX_EVAL_SPLIT_OUTER_TAC THEN
    MAP_EVERY IMP_RES_TAC (CONJUNCTS (SPEC_ALL TPROPSAUX_getOpClass)) THEN
    TPROPSAUX_NORM_TAC THENL
     [TPROPSAUX_APP_CONTR_TAC; TPROPSAUX_APP_FUN_TAC; TPROPSAUX_APP_CONTR_TAC;
      TPROPSAUX_APP_SIMPLE_TAC];
    TPROPSAUX_ETS_FIN_TAC `tenvS1:tenv_store`];;
let TPROPSAUX_ets_App = prove (TPROPSAUX_ETS 8, TPROPSAUX_ets_App_TAC);;

(* HOL4 has ctMap free; the conjuncts are the properties TPROPSAUX_ETS_P1   *)
(* and TPROPSAUX_ETS_P2                                                      *)
let exp_type_sound = prove
 (CASE_TERM
  `(!(s:(FFI)state) env es r s' tenv tenvE ts tvs tenvS.
      evaluate s env es = (s',r) /\
      tenv_ok tenv /\ tenv_val_exp_ok tenvE /\ good_ctMap ctMap /\ num_tvs tenvE = 0 /\
      type_all_env ctMap tenvS env
        (type_env_v_fupd (K (add_tenvE tenvE (type_env_v tenv))) tenv) /\
      type_s ctMap (state_refs s) tenvS /\
      (~(tvs = 0) ==> ALL is_value es) /\
      type_es tenv (bind_tvar tvs tenvE) es ts
      ==> ?tenvS'. type_s ctMap (state_refs s') tenvS' /\
                   store_type_extension tenvS tenvS' /\
                   state_next_type_stamp s' = state_next_type_stamp s /\
                   state_next_exn_stamp s' = state_next_exn_stamp s /\
                   (match r with
                      Rval vs -> ALL2 (type_v tvs ctMap tenvS') vs ts
                    | Rerr (Rraise v) -> type_v 0 ctMap tenvS' v Texn
                    | Rerr (Rabort Rtimeout_error) -> T
                    | Rerr (Rabort (Rffi_error _)) -> T
                    | Rerr (Rabort Rtype_error) -> F)) /\
   (!(s:(FFI)state) env v pes err_v r s' tenv tenvE t1 t2 tvs tenvS.
      evaluate_match s env v pes err_v = (s',r) /\
      tenv_ok tenv /\ tenv_val_exp_ok tenvE /\ good_ctMap ctMap /\ num_tvs tenvE = 0 /\
      type_all_env ctMap tenvS env
        (type_env_v_fupd (K (add_tenvE tenvE (type_env_v tenv))) tenv) /\
      type_s ctMap (state_refs s) tenvS /\
      type_v tvs ctMap tenvS v t1 /\ type_v 0 ctMap tenvS err_v Texn /\
      type_pes tvs tvs tenv tenvE pes t1 t2
      ==> ?tenvS'. type_s ctMap (state_refs s') tenvS' /\
                   store_type_extension tenvS tenvS' /\
                   state_next_type_stamp s' = state_next_type_stamp s /\
                   state_next_exn_stamp s' = state_next_exn_stamp s /\
                   (match r with
                      Rval vs -> type_v tvs ctMap tenvS' (HD vs) t2
                    | Rerr (Rraise v) -> type_v 0 ctMap tenvS' v Texn
                    | Rerr (Rabort Rtimeout_error) -> T
                    | Rerr (Rabort (Rffi_error _)) -> T
                    | Rerr (Rabort Rtype_error) -> F))`,
  ACCEPT_TAC (MATCH_MP TPROPSAUX_ETS_IND
    (end_itlist CONJ
      [TPROPSAUX_ets_nil; TPROPSAUX_ets_cons; TPROPSAUX_ets_Lit; TPROPSAUX_ets_Raise;
       TPROPSAUX_ets_Handle; TPROPSAUX_ets_Con; TPROPSAUX_ets_Var; TPROPSAUX_ets_Fun;
       TPROPSAUX_ets_App; TPROPSAUX_ets_Log; TPROPSAUX_ets_If; TPROPSAUX_ets_Mat;
       TPROPSAUX_ets_Let; TPROPSAUX_ets_Letrec; TPROPSAUX_ets_Tannot;
       TPROPSAUX_ets_Lannot; TPROPSAUX_ets_match_nil; TPROPSAUX_ets_match_cons])));;

(* ------------------------------------------------------------------------- *)
(* Declarations                                                              *)
(* ------------------------------------------------------------------------- *)

(* the constructors of one type definition, looked up in the reversed ctMap entries *)
let TPROPSAUX_alookup_ctors = prove
 (CASE_TERM `!(ctors:(conN # ast_t list) list) (next:num) (tvs:tvarN list)
               (tenvT:tenv_abbrev) (id:num) cn ts.
     ALL_DISTINCT (MAP FST ctors) /\ MEM (cn,ts) ctors
     ==> ALOOKUP (REVERSE (MAP (\p. match p with (cn,ts) ->
                     (TypeStamp cn next,tvs,MAP (type_name_subst tenvT) ts,id)) ctors))
                 (TypeStamp cn next) =
         SOME (tvs,MAP (type_name_subst tenvT) ts,id)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   (CASE_TERM `MAP FST (MAP (\p. match p with (cn,ts) ->
                  (TypeStamp cn (next:num),(tvs:tvarN list),
                   MAP (type_name_subst (tenvT:tenv_abbrev)) ts,(id:num))) ctors) =
               MAP (\x. TypeStamp x next) (MAP FST (ctors:(conN # ast_t list) list))`)
   ASSUME_TAC THENL
  [REWRITE_TAC[MAP_MAP_o; o_DEF] THEN MATCH_MP_TAC MAP_EQ THEN
   REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM] THEN CASE_REWRITE_TAC[] THEN
   REWRITE_TAC[FST];
   ALL_TAC] THEN
  MATCH_MP_TAC ALOOKUP_ALL_DISTINCT_MEM THEN
  REWRITE_TAC[GSYM MAP_REVERSE; ALL_DISTINCT_REVERSE; MEM_REVERSE] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
  [MATCH_MP_TAC ALL_DISTINCT_MAP_INJ THEN ASM_REWRITE_TAC[injectivity "stamp"] THEN
   MESON_TAC[];
   REWRITE_TAC[MEM_MAP] THEN EXISTS_TAC `(cn,ts):conN # ast_t list` THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]]);;

let build_tdefs_build_tenv = prove
 (CASE_TERM `!tenvT (tds:type_def) (tids:num list) next (ctMap:ctMap).
     ALL (\d. match d with (tvs,tn,ctors) -> ALL_DISTINCT (MAP FST ctors)) tds /\
     LENGTH tds = LENGTH tids
     ==> nsAll2 (type_ctor (ctMap |++ REVERSE (type_def_to_ctMap tenvT next tds tids)))
           (build_tdefs next tds:(mlstring,mlstring,num#stamp)namespace)
           (build_ctor_tenv tenvT tds tids)`,
  MATCH_MP_TAC build_ctor_tenv_ind THEN
  RW[build_tdefs_def; build_ctor_tenv_def; type_def_to_ctMap_def] THEN FS[] THEN
  MATCH_MP_TAC nsAll2_nsAppend THEN CONJ_TAC THENL
  [REWRITE_TAC[REVERSE_APPEND; REVERSE_REVERSE; FUPDATE_LIST_APPEND] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  MATCH_MP_TAC nsAll2_alist_to_ns THEN MATCH_MP_TAC EVERY2_REVERSE THEN
  REWRITE_TAC[build_constrs_def; EVERY2_MAP] THEN MATCH_MP_TAC EVERY2_refl THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN CASE_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[type_ctor_def; LENGTH_MAP; flookup_fupdate_list; REVERSE_REVERSE;
              ALOOKUP_APPEND] THEN
  CASES_ON `ALOOKUP (type_def_to_ctMap (tenvT:tenv_abbrev) (next + 1) (tds:type_def)
                       (ids:num list)) (TypeStamp p1 next)` THEN
  CASE_REWRITE_TAC[] THENL
  [FIRST_ASSUM(fun mem -> FIRST_ASSUM(fun ad ->
     REWRITE_TAC[MATCH_MP TPROPSAUX_alookup_ctors (CONJ ad mem)])) THEN
   CASE_REWRITE_TAC[];
   FIRST_X_ASSUM(MP_TAC o MATCH_MP ALOOKUP_MEM) THEN DISCH_TAC THEN
   FIRST_ASSUM(fun mem -> FIRST_ASSUM(fun len ->
     MP_TAC(MATCH_MP mem_type_def_to_ctMap (CONJ mem len)))) THEN
   REWRITE_TAC[injectivity "stamp"] THEN STRIP_TAC THEN ASM_ARITH_TAC]);;

let type_sound_invariant_union = prove
 (`type_sound_invariant (st:(FFI)state) env ctMap tenvS (tids1 UNION tids2) tenv
   ==> type_sound_invariant st env ctMap tenvS tids1 tenv`,
  REWRITE_TAC[type_sound_invariant_def; consistent_ctMap_def] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let check_ctor_tenv_dups = prove
 (`!tenvT tds. check_ctor_tenv tenvT tds ==> ALL check_dup_ctors tds`,
  MATCH_MP_TAC check_ctor_tenv_ind THEN REWRITE_TAC[check_ctor_tenv_def; ALL] THEN
  MESON_TAC[]);;

let type_all_env_extend = prove
 (`type_all_env ctMap tenvS env1 tenv1 /\ type_all_env ctMap tenvS env2 tenv2
   ==> type_all_env ctMap tenvS (extend_dec_env env1 env2) (extend_dec_tenv tenv1 tenv2)`,
  REWRITE_TAC[type_all_env_def; extend_dec_env_def; extend_dec_tenv_def;
              sem_env_INFO.ri_accessors; type_env_INFO.ri_accessors] THEN
  MESON_TAC[nsAll2_nsAppend]);;

let type_e_con_check = prove
 (CASE_TERM
  `(!tenv tenvE e t.
      type_e tenv tenvE e t ==>
      nsAll2 (type_ctor (ctMap:ctMap)) (envc:(mlstring,mlstring,num#stamp)namespace)
        (type_env_c tenv) ==>
      every_exp (one_con_check envc) e) /\
   (!tenv tenvE es ts.
      type_es tenv tenvE es ts ==>
      nsAll2 (type_ctor ctMap) envc (type_env_c tenv) ==>
      ALL (every_exp (one_con_check envc)) es) /\
   (!tenv tenvE funs env.
      type_funs tenv tenvE funs env ==>
      nsAll2 (type_ctor ctMap) envc (type_env_c tenv) ==>
      ALL (\fne. match fne with (f,n,e) -> every_exp (one_con_check envc) e) funs)`,
  MATCH_MP_TAC type_e_strongind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[every_exp_def; one_con_check_def; ALL] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THENL
  [(* Handle *)
   REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM] THEN CASE_REWRITE_TAC[] THEN
   ASM_MESON_TAC[];
   (* Con SOME *)
   FIRST_ASSUM(fun lk -> FIRST_ASSUM(fun al ->
     MP_TAC(MATCH_MP nsAll2_nsLookup2 (CONJ lk al)))) THEN
   REWRITE_TAC[EXISTS_PAIR_THM; type_ctor_def] THEN STRIP_TAC THEN
   ASM_REWRITE_TAC[do_con_check_def] THEN CASE_REWRITE_TAC[] THEN
   IMP_RES_TAC type_es_length THEN ASM_REWRITE_TAC[LENGTH_MAP] THEN
   CASE_REWRITE_TAC[] THEN REWRITE_TAC[];
   (* Con NONE *)
   REWRITE_TAC[do_con_check_def] THEN CASE_REWRITE_TAC[];
   (* Mat *)
   REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM] THEN CASE_REWRITE_TAC[] THEN
   ASM_MESON_TAC[];
   (* type_funs cons *)
   CASE_REWRITE_TAC[] THEN ASM_SIMP_TAC[]]);;

(* decs_type_sound_no_check is proved by evaluate_decs_ind, one lemma per *)
(* clause of evaluate_decs: TPROPSAUX_DTS k is the k-th case              *)
let TPROPSAUX_DTS_P = CASE_TERM
 `\(st:(FFI)state) (env:v sem_env) (ds:dec list).
    !st' r ctMap tenvS tenv tids tenv'.
      evaluate_decs st env ds = (st',r) /\ type_ds F tenv ds tids tenv' /\
      type_sound_invariant st env ctMap tenvS tids tenv
      ==> ?ctMap' tenvS'. weakCT ctMap' ctMap /\
            FRANGE ((SND o SND) o_f ctMap') DIFF FRANGE ((SND o SND) o_f ctMap) SUBSET tids /\
            store_type_extension tenvS tenvS' /\
            (match r with
               Rval env' -> type_all_env ctMap' tenvS' env' tenv' /\
                 type_sound_invariant st' (extend_dec_env env' env) ctMap' tenvS' {}
                   (extend_dec_tenv tenv' tenv)
             | Rerr (Rraise err_v) -> type_v 0 ctMap' tenvS' err_v Texn /\
                 type_sound_invariant st' env ctMap' tenvS' {} tenv
             | Rerr (Rabort Rtype_error) -> F
             | Rerr (Rabort Rtimeout_error) -> T
             | Rerr (Rabort (Rffi_error _)) -> T)`;;

let TPROPSAUX_DTS_IND = CONV_RULE (DEPTH_CONV BETA_CONV)
    (ISPEC TPROPSAUX_DTS_P evaluate_decs_ind);;

let TPROPSAUX_DTS_CASES = conjuncts (lhand (concl TPROPSAUX_DTS_IND));;

let TPROPSAUX_DTS k = el k TPROPSAUX_DTS_CASES;;

let TPROPSAUX_extend_empty = prove
 (`(!env:v sem_env. extend_dec_env (sem_env_REC nsEmpty nsEmpty) env = env) /\
   (!tenv. extend_dec_tenv (type_env_REC nsEmpty nsEmpty nsEmpty) tenv = tenv)`,
  REWRITE_TAC[extend_dec_env_def; extend_dec_tenv_def; sem_env_INFO.ri_accessors;
              type_env_INFO.ri_accessors; nsAppend_nsEmpty; unchanged_env;
              unchanged_tenv]);;

let TPROPSAUX_dts_nil = prove
 (TPROPSAUX_DTS 0,
  REPEAT GEN_TAC THEN REWRITE_TAC[evaluate_decs_def; PAIR_EQ] THEN
  ONCE_REWRITE_TAC[type_d_cases] THEN
  REWRITE_TAC[distinctness "list"; NOT_CONS_NIL] THEN STRIP_TAC THEN RVEQ_TAC THEN
  MAP_EVERY EXISTS_TAC [`ctMap:ctMap`; `tenvS:tenv_store`] THEN
  CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[weakCT_refl; DIFF_EQ_EMPTY; EMPTY_SUBSET; store_type_extension_refl;
                  TPROPSAUX_extend_empty; type_all_env_def; sem_env_INFO.ri_accessors;
                  type_env_INFO.ri_accessors; nsAll2_nsEmpty]);;

let TPROPSAUX_type_ds_cons = prove
 (`!ec tenv d ds tids tenv'.
     type_ds ec tenv (CONS d ds) tids tenv' <=>
     ?tenv1 tenv2 decls1 decls2.
       type_d ec tenv d decls1 tenv1 /\
       type_ds ec (extend_dec_tenv tenv1 tenv) ds decls2 tenv2 /\
       DISJOINT decls1 decls2 /\ tids = decls1 UNION decls2 /\
       tenv' = extend_dec_tenv tenv2 tenv1`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [type_d_cases] THEN
  REWRITE_TAC[distinctness "list"; injectivity "list"] THEN MESON_TAC[]);;

let TPROPSAUX_disjoint_step = prove
 (`!a b c d:A->bool.
     DISJOINT (a UNION b) c /\ d DIFF c SUBSET a /\ DISJOINT a b ==> DISJOINT b d`,
  SET_TAC[]);;

let TPROPSAUX_dts_cons = prove
 (TPROPSAUX_DTS 1,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[TPROPSAUX_type_ds_cons] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  MP_TAC(ISPEC `evaluate_decs (st:(FFI)state) env [d1]` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `st1:(FFI)state`
    (X_CHOOSE_THEN `r1:(v sem_env,v)result` ASSUME_TAC)) THEN
  REMOVE_THEN "ih1" (MP_TAC o SPECL [`st1:(FFI)state`; `r1:(v sem_env,v)result`;
    `ctMap:ctMap`; `tenvS:tenv_store`; `tenv:type_env`; `decls1:num->bool`;
    `tenv1:type_env`]) THEN
  ASM_REWRITE_TAC[type_ds_sing] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[type_sound_invariant_union]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ctMap1:ctMap` (X_CHOOSE_THEN `tenvS1:tenv_store`
    STRIP_ASSUME_TAC)) THEN
  CASES_ON `r1:(v sem_env,v)result` THEN RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THENL
  [(* the first declaration returns *)
   UNDISCH_TAC `evaluate_decs (st:(FFI)state) env (CONS d1 (CONS d2 ds)) = (st',r)` THEN
   ASM_REWRITE_TAC[evaluate_decs_def] THEN CASE_REWRITE_TAC[] THEN
   MP_TAC(ISPEC `evaluate_decs (st1:(FFI)state) (extend_dec_env a env) (CONS d2 ds)`
     PAIR_SURJECTIVE) THEN
   DISCH_THEN(X_CHOOSE_THEN `st2:(FFI)state`
     (X_CHOOSE_THEN `r2:(v sem_env,v)result` ASSUME_TAC)) THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
   STRIP_TAC THEN RVEQ_TAC THEN
   FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
   REMOVE_THEN "ih2" (MP_TAC o SPECL [`st1:(FFI)state`; `a:v sem_env`]) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(MP_TAC o SPECL [`st':(FFI)state`; `r2:(v sem_env,v)result`;
     `ctMap1:ctMap`; `tenvS1:tenv_store`; `extend_dec_tenv tenv1 tenv`;
     `decls2:num->bool`; `tenv2:type_env`]) THEN
   ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [UNDISCH_TAC `type_sound_invariant (st1:(FFI)state) (extend_dec_env a env) ctMap1
                   tenvS1 {} (extend_dec_tenv tenv1 tenv)` THEN
    UNDISCH_TAC `type_sound_invariant (st:(FFI)state) env ctMap tenvS
                   (decls1 UNION decls2) tenv` THEN
    REWRITE_TAC[type_sound_invariant_def; consistent_ctMap_def] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[TPROPSAUX_disjoint_step];
    ALL_TAC] THEN
   DISCH_THEN(X_CHOOSE_THEN `ctMap2:ctMap` (X_CHOOSE_THEN `tenvS2:tenv_store`
     STRIP_ASSUME_TAC)) THEN
   MAP_EVERY EXISTS_TAC [`ctMap2:ctMap`; `tenvS2:tenv_store`] THEN
   REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[weakCT_trans];
    UNDISCH_TAC `FRANGE ((SND o SND) o_f (ctMap1:ctMap)) DIFF
                 FRANGE ((SND o SND) o_f (ctMap:ctMap)) SUBSET decls1` THEN
    UNDISCH_TAC `FRANGE ((SND o SND) o_f (ctMap2:ctMap)) DIFF
                 FRANGE ((SND o SND) o_f (ctMap1:ctMap)) SUBSET decls2` THEN SET_TAC[];
    ASM_MESON_TAC[store_type_extension_trans];
    ALL_TAC] THEN
   CASES_ON `r2:(v sem_env,v)result` THEN RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
   REWRITE_TAC[combine_dec_result_def] THEN CASE_REWRITE_TAC[] THENL
   [(* the rest returns *)
    REWRITE_TAC[GSYM extend_dec_env_def] THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o
      REWRITE_RULE[extend_dec_env_assoc; extend_dec_tenv_assoc] o
      check (is_conj o concl)) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC type_all_env_extend THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC type_all_env_weakening THEN
    MAP_EVERY EXISTS_TAC [`ctMap1:ctMap`; `tenvS1:tenv_store`] THEN
    ASM_SIMP_TAC[store_type_extension_weakS];
    (* the rest raises or aborts *)
    CASES_ON `a':(v)error_result` THEN RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
    CASE_REWRITE_TAC[] THENL
    [FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN ASM_REWRITE_TAC[] THEN
     UNDISCH_TAC `type_sound_invariant (st':(FFI)state) (extend_dec_env a env) ctMap2
                    tenvS2 {} (extend_dec_tenv tenv1 tenv)` THEN
     UNDISCH_TAC `type_sound_invariant (st:(FFI)state) env ctMap tenvS
                    (decls1 UNION decls2) tenv` THEN
     REWRITE_TAC[type_sound_invariant_def] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC type_all_env_weakening THEN
     MAP_EVERY EXISTS_TAC [`ctMap:ctMap`; `tenvS:tenv_store`] THEN ASM_REWRITE_TAC[] THEN
     ASM_MESON_TAC[weakCT_trans; store_type_extension_trans; store_type_extension_weakS];
     FIRST_ASSUM ACCEPT_TAC]];
   (* the first declaration raises or aborts *)
   UNDISCH_TAC `evaluate_decs (st:(FFI)state) env (CONS d1 (CONS d2 ds)) = (st',r)` THEN
   ASM_REWRITE_TAC[evaluate_decs_def] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
   STRIP_TAC THEN RVEQ_TAC THEN
   MAP_EVERY EXISTS_TAC [`ctMap1:ctMap`; `tenvS1:tenv_store`] THEN
   CASE_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    UNDISCH_TAC `FRANGE ((SND o SND) o_f (ctMap1:ctMap)) DIFF
                 FRANGE ((SND o SND) o_f (ctMap:ctMap)) SUBSET decls1` THEN SET_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]]]);;

(* the invariant after an expression evaluation that keeps the stamps *)
let TPROPSAUX_tsi_after = prove
 (`!(st:(FFI)state) (st1:(FFI)state) env ctMap tenvS tenvS' tids tenv.
     type_sound_invariant st env ctMap tenvS tids tenv /\
     type_s ctMap (state_refs st1) tenvS' /\ store_type_extension tenvS tenvS' /\
     state_next_type_stamp st1 = state_next_type_stamp st /\
     state_next_exn_stamp st1 = state_next_exn_stamp st
     ==> type_sound_invariant st1 env ctMap tenvS' {} tenv`,
  REWRITE_TAC[type_sound_invariant_def; consistent_ctMap_def; DISJOINT_EMPTY] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC type_all_env_weakening THEN
  MAP_EVERY EXISTS_TAC [`ctMap:ctMap`; `tenvS:tenv_store`] THEN
  ASM_SIMP_TAC[weakCT_refl; store_type_extension_weakS]);;

(* the value environment of a typed pattern match *)
let TPROPSAUX_nsAll2_tenv_add_tvs = prove
 (CASE_TERM `!(bindings':(mlstring#v)list) (bindings:(mlstring#t)list) tvs ctMap tenvS.
     ALL2 (\xv xt. match xv with (x,v) -> match xt with (x',t) ->
                     x = x' /\ type_v tvs ctMap tenvS v t) bindings' bindings
     ==> nsAll2 (\i v p. match p with (tvs,t) -> type_v tvs ctMap tenvS v t)
           (alist_to_ns bindings':(mlstring,mlstring,v)namespace)
           (alist_to_ns (tenv_add_tvs tvs bindings))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC nsAll2_alist_to_ns THEN
  REWRITE_TAC[tenv_add_tvs_def; EVERY2_MAP] THEN
  POP_ASSUM MP_TAC THEN MATCH_MP_TAC MONO_ALL2 THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN CASE_REWRITE_TAC[] THEN SIMP_TAC[]);;
(* unfolds the type_sound_invariant assumption into its parts *)
let TPROPSAUX_UNFOLD_TSI_TAC : tactic =
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[type_sound_invariant_def] o
    check (can (term_match [] `type_sound_invariant (a:(FFI)state) b c d e f`) o concl));;

(* Dlet, for both typing rules (tvs = 0 for an expression that is not a value) *)
let TPROPSAUX_dlet_core = prove
 (CASE_TERM
  `!(st:(FFI)state) env locs p e st' r ctMap tenvS tenv tids tvs t bindings.
     evaluate_decs st env [Dlet locs p e] = (st',r) /\
     ALL_DISTINCT (pat_bindings p) /\
     type_p tvs tenv p t bindings /\ type_e tenv (bind_tvar tvs Empty) e t /\
     (~(tvs = 0) ==> is_value e) /\
     tenv_ok (extend_dec_tenv
       (type_env_REC (alist_to_ns (tenv_add_tvs tvs bindings)) nsEmpty nsEmpty) tenv) /\
     type_sound_invariant st env ctMap tenvS tids tenv
     ==> ?ctMap' tenvS'. weakCT ctMap' ctMap /\
           FRANGE ((SND o SND) o_f ctMap') DIFF FRANGE ((SND o SND) o_f ctMap) SUBSET {} /\
           store_type_extension tenvS tenvS' /\
           (match r with
              Rval env' ->
                type_all_env ctMap' tenvS' env'
                  (type_env_REC (alist_to_ns (tenv_add_tvs tvs bindings)) nsEmpty nsEmpty) /\
                type_sound_invariant st' (extend_dec_env env' env) ctMap' tenvS' {}
                  (extend_dec_tenv (type_env_REC (alist_to_ns (tenv_add_tvs tvs bindings))
                                      nsEmpty nsEmpty) tenv)
            | Rerr (Rraise err_v) -> type_v 0 ctMap' tenvS' err_v Texn /\
                type_sound_invariant st' env ctMap' tenvS' {} tenv
            | Rerr (Rabort Rtype_error) -> F
            | Rerr (Rabort Rtimeout_error) -> T
            | Rerr (Rabort (Rffi_error _)) -> T)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN TPROPSAUX_UNFOLD_TSI_TAC THEN
  SUBGOAL_THEN `every_exp (one_con_check (sem_env_c (env:v sem_env))) e` ASSUME_TAC THENL
  [MP_TAC(SPECL [`tenv:type_env`; `bind_tvar tvs Empty`; `e:exp`; `t:t`]
     (CONJUNCT1 (INST [`sem_env_c (env:v sem_env)`,
                       `envc:(mlstring,mlstring,num#stamp)namespace`] type_e_con_check))) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
   FIRST_ASSUM(fun th -> ACCEPT_TAC(CONJUNCT1(REWRITE_RULE[type_all_env_def] th)));
   ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    can (term_match [] `evaluate_decs (a:(FFI)state) b c = d`) (concl th))) THEN
  ASM_REWRITE_TAC[evaluate_decs_def] THEN
  MP_TAC(ISPECL [`evaluate (st:(FFI)state) env [e]`] PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `st1:(FFI)state`
    (X_CHOOSE_THEN `r1:(v list,v)result` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`st:(FFI)state`; `env:v sem_env`; `[e]:exp list`; `r1:(v list,v)result`;
    `st1:(FFI)state`; `tenv:type_env`; `Empty:tenv_val_exp`; `[t]:t list`; `tvs:num`;
    `tenvS:tenv_store`] (CONJUNCT1 exp_type_sound)) THEN
  ASM_REWRITE_TAC[tenv_val_exp_ok_def; num_tvs_def; add_tenvE_def; v_unchanged;
                  type_es_list_rel; ALL2; ALL] THEN
  DISCH_THEN(X_CHOOSE_THEN `tenvS1:tenv_store` STRIP_ASSUME_TAC) THEN
  CASES_ON `r1:(v list,v)result` THEN RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THENL
  [(* the expression returns a value *)
   FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN RVEQ_TAC THEN
   FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[LIST_REL_CONS2; LIST_REL_NIL] o
     check (can (term_match [] `ALL2 (R:v->t->bool) a [t]`) o concl)) THEN
   STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[HD] THEN
   FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[good_ctMap_def] o
     check (can (term_match [] `good_ctMap c`) o concl)) THEN
   FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[type_all_env_def] o
     check (can (term_match [] `type_all_env a b (c:v sem_env) d`) o concl)) THEN
   MP_TAC(SPECL [`sem_env_c (env:v sem_env)`; `state_refs (st':(FFI)state)`; `p:pat`;
     `h':v`; `[]:(mlstring#v)list`; `tenv:type_env`; `ctMap:ctMap`;
     `[]:(mlstring#t)list`; `t:t`; `bindings:(mlstring#t)list`; `tenvS1:tenv_store`;
     `tvs:num`] (CONJUNCT1 pat_type_sound)) THEN
   ASM_REWRITE_TAC[ALL2; APPEND_NIL] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
   CASE_REWRITE_TAC[] THENL
   [(* no match: Bind is raised *)
    MAP_EVERY EXISTS_TAC [`ctMap:ctMap`; `tenvS1:tenv_store`] THEN
    ASM_REWRITE_TAC[weakCT_refl; DIFF_EQ_EMPTY; EMPTY_SUBSET; bind_exn_v_def] THEN
    CONJ_TAC THENL
    [ASM_MESON_TAC[TPROPSAUX_type_v_exn];
     ASM_MESON_TAC[TPROPSAUX_tsi_after]];
    (* match *)
    MAP_EVERY EXISTS_TAC [`ctMap:ctMap`; `tenvS1:tenv_store`] THEN
    ASM_REWRITE_TAC[weakCT_refl; DIFF_EQ_EMPTY; EMPTY_SUBSET] THEN
    SUBGOAL_THEN `type_all_env ctMap tenvS1 (sem_env_REC (alist_to_ns bindings') nsEmpty)
      (type_env_REC (alist_to_ns (tenv_add_tvs tvs bindings)) nsEmpty nsEmpty)`
      ASSUME_TAC THENL
    [REWRITE_TAC[type_all_env_def; sem_env_INFO.ri_accessors; type_env_INFO.ri_accessors;
                 nsAll2_nsEmpty] THEN
     MATCH_MP_TAC TPROPSAUX_nsAll2_tenv_add_tvs THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `type_sound_invariant (st':(FFI)state) env ctMap tenvS1 {} tenv` MP_TAC THENL
    [ASM_MESON_TAC[TPROPSAUX_tsi_after]; ALL_TAC] THEN
    REWRITE_TAC[type_sound_invariant_def] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC type_all_env_extend THEN ASM_REWRITE_TAC[]];
   (* the expression raises or aborts *)
   FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN RVEQ_TAC THEN
   MAP_EVERY EXISTS_TAC [`ctMap:ctMap`; `tenvS1:tenv_store`] THEN
   ASM_REWRITE_TAC[weakCT_refl; DIFF_EQ_EMPTY; EMPTY_SUBSET] THEN
   CASES_ON `a:(v)error_result` THEN RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
   CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[TPROPSAUX_tsi_after]]);;

let TPROPSAUX_dts_Dlet = prove
 (TPROPSAUX_DTS 2,
  REPEAT GEN_TAC THEN REWRITE_TAC[type_ds_sing] THEN STRIP_TAC THEN
  SUBGOAL_THEN `tenv_ok (extend_dec_tenv tenv' tenv)` ASSUME_TAC THENL
  [MATCH_MP_TAC type_d_tenv_ok THEN
   ASM_MESON_TAC[type_sound_invariant_def]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o ONCE_REWRITE_RULE[type_d_cases] o
    check (can (term_match [] `type_d a b c d e`) o concl)) THEN
  REWRITE_TAC[distinctness "dec"; injectivity "dec"] THEN STRIP_TAC THEN RVEQ_TAC THENL
  [MATCH_MP_TAC TPROPSAUX_dlet_core THEN ASM_MESON_TAC[];
   MATCH_MP_TAC TPROPSAUX_dlet_core THEN REWRITE_TAC[bind_tvar_def] THEN ASM_MESON_TAC[]]);;

let TPROPSAUX_letrec_env = prove
 (CASE_TERM `!funs ctMap tenvS tvs tenv (env:v sem_env) bindings.
     tenv_ok tenv /\ type_all_env ctMap tenvS env tenv /\
     type_funs tenv (bind_var_list 0 bindings (bind_tvar tvs Empty)) funs bindings /\
     ALL_DISTINCT (MAP FST funs)
     ==> type_all_env ctMap tenvS
           (sem_env_REC (alist_to_ns (MAP (\fne. match fne with
                                              (f,n,e) -> (f,Recclosure env funs f)) funs))
                        nsEmpty)
           (type_env_REC (alist_to_ns (tenv_add_tvs tvs bindings)) nsEmpty nsEmpty)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[type_all_env_def; sem_env_INFO.ri_accessors; type_env_INFO.ri_accessors;
              nsAll2_nsEmpty] THEN
  MATCH_MP_TAC nsAll2_alist_to_ns THEN REWRITE_TAC[tenv_add_tvs_def] THEN
  MP_TAC(SPECL [`funs:(varN#varN#exp)list`; `ctMap:ctMap`; `tenvS:tenv_store`; `tvs:num`;
                `tenv:type_env`; `Empty:tenv_val_exp`; `env:v sem_env`;
                `bindings:(mlstring#t)list`] type_recfun_env) THEN
  ASM_REWRITE_TAC[add_tenvE_def; v_unchanged; tenv_val_exp_ok_def; num_tvs_def] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN DISCH_THEN ACCEPT_TAC);;

let TPROPSAUX_dts_Dletrec = prove
 (TPROPSAUX_DTS 3,
  REPEAT GEN_TAC THEN REWRITE_TAC[type_ds_sing] THEN STRIP_TAC THEN
  SUBGOAL_THEN `tenv_ok (extend_dec_tenv tenv' tenv)` ASSUME_TAC THENL
  [MATCH_MP_TAC type_d_tenv_ok THEN TPROPSAUX_UNFOLD_TSI_TAC THEN ASM_MESON_TAC[];
   ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o ONCE_REWRITE_RULE[type_d_cases] o
    check (can (term_match [] `type_d a b c d e`) o concl)) THEN
  REWRITE_TAC[distinctness "dec"; injectivity "dec"] THEN STRIP_TAC THEN RVEQ_TAC THEN
  TPROPSAUX_UNFOLD_TSI_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[type_all_env_def] o
    check (can (term_match [] `type_all_env a b (c:v sem_env) d`) o concl)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP type_funs_distinct o
    check (can (term_match [] `type_funs a b c d`) o concl)) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (CONJUNCT2(CONJUNCT2(INST [`sem_env_c (env:v sem_env)`,
      `envc:(mlstring,mlstring,num#stamp)namespace`] type_e_con_check))) o
    check (can (term_match [] `type_funs a b c d`) o concl)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    can (term_match [] `evaluate_decs (a:(FFI)state) b c = d`) (concl th))) THEN
  ASM_REWRITE_TAC[evaluate_decs_def; PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  MAP_EVERY EXISTS_TAC [`ctMap:ctMap`; `tenvS:tenv_store`] THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[weakCT_refl; DIFF_EQ_EMPTY; EMPTY_SUBSET; store_type_extension_refl;
              build_rec_env_merge; nsAppend_nsEmpty] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[fst_triple]) THEN
  MATCH_MP_TAC(TAUT `!a b. a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
  [MATCH_MP_TAC TPROPSAUX_letrec_env THEN EXISTS_TAC `tenv:type_env` THEN
   ASM_REWRITE_TAC[];
   DISCH_TAC THEN ASM_REWRITE_TAC[type_sound_invariant_def] THEN
   MATCH_MP_TAC type_all_env_extend THEN ASM_REWRITE_TAC[]]);;

(* opens a single-declaration case: the typing derivation is inverted, the *)
(* tenv_ok of the extended environment is kept                             *)
let TPROPSAUX_DTS_START_TAC : tactic =
  REPEAT GEN_TAC THEN REWRITE_TAC[type_ds_sing] THEN STRIP_TAC THEN
  SUBGOAL_THEN `tenv_ok (extend_dec_tenv tenv' tenv)` ASSUME_TAC THENL
  [MATCH_MP_TAC type_d_tenv_ok THEN TPROPSAUX_UNFOLD_TSI_TAC THEN ASM_MESON_TAC[];
   ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o ONCE_REWRITE_RULE[type_d_cases] o
    check (can (term_match [] `type_d a b c d e`) o concl)) THEN
  REWRITE_TAC[distinctness "dec"; injectivity "dec"] THEN STRIP_TAC THEN RVEQ_TAC THEN
  TPROPSAUX_UNFOLD_TSI_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[type_all_env_def] o
    check (can (term_match [] `type_all_env a b (c:v sem_env) d`) o concl));;

(* rewrites the evaluation assumption with evaluate_decs_def *)
let TPROPSAUX_DTS_EVAL_TAC : tactic =
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    can (term_match [] `evaluate_decs (a:(FFI)state) b c = d`) (concl th))) THEN
  ASM_REWRITE_TAC[evaluate_decs_def];;

let TPROPSAUX_dts_Dtabbrev = prove
 (TPROPSAUX_DTS 5,
  TPROPSAUX_DTS_START_TAC THEN TPROPSAUX_DTS_EVAL_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  MAP_EVERY EXISTS_TAC [`ctMap:ctMap`; `tenvS:tenv_store`] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[weakCT_refl; DIFF_EQ_EMPTY; EMPTY_SUBSET; store_type_extension_refl;
              TPROPSAUX_extend_empty] THEN
  REWRITE_TAC[type_sound_invariant_def] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[type_all_env_def; extend_dec_tenv_def; sem_env_INFO.ri_accessors;
              type_env_INFO.ri_accessors; nsAppend_nsEmpty; nsAll2_nsEmpty] THEN
  ASM_REWRITE_TAC[]);;

(* there is no typing rule for Denv *)
let TPROPSAUX_dts_Denv = prove
 (TPROPSAUX_DTS 6,
  TPROPSAUX_DTS_START_TAC);;

let TPROPSAUX_type_all_env_lift = prove
 (`!ctMap tenvS (env:v sem_env) tenv mn.
     type_all_env ctMap tenvS env tenv
     ==> type_all_env ctMap tenvS
           (sem_env_REC (nsLift mn (sem_env_v env)) (nsLift mn (sem_env_c env)))
           (tenvLift mn tenv)`,
  REWRITE_TAC[type_all_env_def; tenvLift_def; sem_env_INFO.ri_accessors;
              type_env_INFO.ri_accessors; nsAll2_nsLift] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
  [UNDISCH_TAC `nsAll2 (type_ctor ctMap) (sem_env_c (env:v sem_env)) (type_env_c tenv)` THEN
   MATCH_MP_TAC nsAll2_mono THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
   REWRITE_TAC[FORALL_PAIR_THM; type_ctor_def];
   CONV_TAC(DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[]]);;

let TPROPSAUX_dts_Dmod = prove
 (TPROPSAUX_DTS 8,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "ih") THEN TPROPSAUX_DTS_START_TAC THEN
  TPROPSAUX_DTS_EVAL_TAC THEN
  MP_TAC(ISPEC `evaluate_decs (st:(FFI)state) env ds'` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `st1:(FFI)state`
    (X_CHOOSE_THEN `r1:(v sem_env,v)result` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  REMOVE_THEN "ih" (MP_TAC o SPECL [`st':(FFI)state`; `r1:(v sem_env,v)result`;
    `ctMap:ctMap`; `tenvS:tenv_store`; `tenv:type_env`; `tids:num->bool`;
    `tenv'':type_env`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `ctMap1:ctMap` (X_CHOOSE_THEN `tenvS1:tenv_store`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`ctMap1:ctMap`; `tenvS1:tenv_store`] THEN ASM_REWRITE_TAC[] THEN
  CASES_ON `r1:(v sem_env,v)result` THEN RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
  MATCH_MP_TAC(TAUT `!a b. a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
  [MATCH_MP_TAC TPROPSAUX_type_all_env_lift THEN ASM_REWRITE_TAC[];
   DISCH_TAC THEN
   UNDISCH_TAC `type_sound_invariant (st':(FFI)state) (extend_dec_env a env) ctMap1
                  tenvS1 {} (extend_dec_tenv tenv'' tenv)` THEN
   REWRITE_TAC[type_sound_invariant_def] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC type_all_env_extend THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC type_all_env_weakening THEN
   MAP_EVERY EXISTS_TAC [`ctMap:ctMap`; `tenvS:tenv_store`] THEN
   ASM_SIMP_TAC[store_type_extension_weakS]]);;

let TPROPSAUX_dts_Dlocal = prove
 (TPROPSAUX_DTS 9,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
  TPROPSAUX_DTS_START_TAC THEN TPROPSAUX_DTS_EVAL_TAC THEN
  MP_TAC(ISPEC `evaluate_decs (st:(FFI)state) env lds'` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `st1:(FFI)state`
    (X_CHOOSE_THEN `r1:(v sem_env,v)result` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN DISCH_TAC THEN
  REMOVE_THEN "ih1" (MP_TAC o SPECL [`st1:(FFI)state`; `r1:(v sem_env,v)result`;
    `ctMap:ctMap`; `tenvS:tenv_store`; `tenv:type_env`; `decls1:num->bool`;
    `tenv1:type_env`]) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[type_sound_invariant_union]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ctMap1:ctMap` (X_CHOOSE_THEN `tenvS1:tenv_store`
    STRIP_ASSUME_TAC)) THEN
  CASES_ON `r1:(v sem_env,v)result` THEN RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THENL
  [(* the local declarations return *)
   FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
   REMOVE_THEN "ih2" (MP_TAC o SPECL [`st1:(FFI)state`; `a:v sem_env`]) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(MP_TAC o SPECL [`st':(FFI)state`; `r:(v sem_env,v)result`;
     `ctMap1:ctMap`; `tenvS1:tenv_store`; `extend_dec_tenv tenv1 tenv`;
     `decls2:num->bool`; `tenv':type_env`]) THEN
   ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [UNDISCH_TAC `type_sound_invariant (st1:(FFI)state) (extend_dec_env a env) ctMap1
                   tenvS1 {} (extend_dec_tenv tenv1 tenv)` THEN
    UNDISCH_TAC `type_sound_invariant (st:(FFI)state) env ctMap tenvS
                   (decls1 UNION decls2) tenv` THEN
    REWRITE_TAC[type_sound_invariant_def; consistent_ctMap_def] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[TPROPSAUX_disjoint_step];
    ALL_TAC] THEN
   DISCH_THEN(X_CHOOSE_THEN `ctMap2:ctMap` (X_CHOOSE_THEN `tenvS2:tenv_store`
     STRIP_ASSUME_TAC)) THEN
   MAP_EVERY EXISTS_TAC [`ctMap2:ctMap`; `tenvS2:tenv_store`] THEN
   REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[weakCT_trans];
    UNDISCH_TAC `FRANGE ((SND o SND) o_f (ctMap1:ctMap)) DIFF
                 FRANGE ((SND o SND) o_f (ctMap:ctMap)) SUBSET decls1` THEN
    UNDISCH_TAC `FRANGE ((SND o SND) o_f (ctMap2:ctMap)) DIFF
                 FRANGE ((SND o SND) o_f (ctMap1:ctMap)) SUBSET decls2` THEN SET_TAC[];
    ASM_MESON_TAC[store_type_extension_trans];
    ALL_TAC] THEN
   SUBGOAL_THEN `type_all_env ctMap2 tenvS2 env tenv` ASSUME_TAC THENL
   [MATCH_MP_TAC type_all_env_weakening THEN
    MAP_EVERY EXISTS_TAC [`ctMap:ctMap`; `tenvS:tenv_store`] THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[weakCT_trans; store_type_extension_trans; store_type_extension_weakS];
    ALL_TAC] THEN
   CASES_ON `r:(v sem_env,v)result` THEN RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
   CASE_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (can (term_match []
      `type_sound_invariant (s:(FFI)state) (extend_dec_env x (extend_dec_env y z)) c d e f`) o
      concl)) THEN
    REWRITE_TAC[type_sound_invariant_def] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC type_all_env_extend THEN ASM_REWRITE_TAC[];
    CASES_ON `a':(v)error_result` THEN RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
    CASE_REWRITE_TAC[] THENL
    [FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN ASM_REWRITE_TAC[] THEN
     FIRST_X_ASSUM(MP_TAC o check (can (term_match []
       `type_sound_invariant (s:(FFI)state) (extend_dec_env x y) c d {} f`) o concl)) THEN
     REWRITE_TAC[type_sound_invariant_def] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
     FIRST_ASSUM ACCEPT_TAC]];
   (* the local declarations raise or abort *)
   FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN RVEQ_TAC THEN
   MAP_EVERY EXISTS_TAC [`ctMap1:ctMap`; `tenvS1:tenv_store`] THEN
   CASE_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    UNDISCH_TAC `FRANGE ((SND o SND) o_f (ctMap1:ctMap)) DIFF
                 FRANGE ((SND o SND) o_f (ctMap:ctMap)) SUBSET decls1` THEN SET_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]]]);;

let TPROPSAUX_FLOOKUP_ext = prove
 (`!(f:(A,B)fmap) k v k'.
     FLOOKUP (FUNION (FEMPTY |+ (k,v)) f) k' = if k' = k then SOME v else FLOOKUP f k'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FLOOKUP_FUNION; FLOOKUP_UPDATE; FLOOKUP_EMPTY] THEN
  ASM_CASES_TAC `k':A = k` THEN ASM_REWRITE_TAC[option_CASE] THEN
  ASM_MESON_TAC[]);;

let TPROPSAUX_weakCT_ext = prove
 (`!(f:(A,B)fmap) k v. ~(k IN FDOM f) ==> weakCT (FUNION (FEMPTY |+ (k,v)) f) f`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC disjoint_env_weakCT THEN
  REWRITE_TAC[FDOM_FUPDATE; FDOM_FEMPTY] THEN ASM SET_TAC[]);;

let TPROPSAUX_FRANGE_ext = prove
 (`!(f:(A,B#C#D)fmap) k v w.
     (?k'. FLOOKUP f k' = SOME w /\ SND (SND w) = SND (SND v))
     ==> FRANGE ((SND o SND) o_f FUNION (FEMPTY |+ (k,v)) f) DIFF
         FRANGE ((SND o SND) o_f f) SUBSET {}`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[SUBSET; IN_DIFF; NOT_IN_EMPTY; FRANGE_FLOOKUP; FLOOKUP_o_f;
              TPROPSAUX_FLOOKUP_ext] THEN
  X_GEN_TAC `x:D` THEN
  REWRITE_TAC[TAUT `~(a /\ ~b) <=> a ==> b`] THEN
  DISCH_THEN(X_CHOOSE_THEN `k1:A` MP_TAC) THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_CASE; injectivity "option"; o_THM] THENL
  [DISCH_THEN(SUBST1_TAC o SYM) THEN EXISTS_TAC `k':A` THEN
   ASM_REWRITE_TAC[option_CASE; injectivity "option"; o_THM];
   DISCH_TAC THEN EXISTS_TAC `k1:A` THEN ASM_REWRITE_TAC[]]);;

let TPROPSAUX_EXN_STAMP_TAC : tactic =
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    can (term_match [] `~(x IN FDOM (m:ctMap))`) (concl th))) THEN
  ASM_REWRITE_TAC[FDOM_FLOOKUP; option_DISTINCT];;

let TPROPSAUX_good_ctMap_exn = prove
 (`!ctMap n ts.
     good_ctMap ctMap /\ ~(ExnStamp n IN FDOM ctMap) /\ ALL (check_freevars 0 []) ts
     ==> good_ctMap (FUNION (FEMPTY |+ (ExnStamp n,([]:tvarN list,ts,Texn_num))) ctMap)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[good_ctMap_def; ctMap_ok_def; ctMap_has_bools_def; ctMap_has_exns_def;
              ctMap_has_lists_def; TPROPSAUX_FLOOKUP_ext; FEVERY_ALL_FLOOKUP;
              distinctness "stamp"; injectivity "stamp"; bind_stamp_def; chr_stamp_def;
              div_stamp_def; subscript_stamp_def] THEN
  STRIP_TAC THEN REPEAT CONJ_TAC THENL
  [(* FEVERY *)
   REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[injectivity "option"] THENL
   [DISCH_THEN(SUBST1_TAC o SYM) THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[];
    DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
   (* exception stamps *)
   REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[injectivity "option"; PAIR_EQ] THEN
   STRIP_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[];
   ASM_REWRITE_TAC[];
   (* same_type *)
   REPEAT GEN_TAC THEN REPEAT COND_CASES_TAC THEN
   REWRITE_TAC[injectivity "option"; PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
   ASM_REWRITE_TAC[same_type_def] THENL
   [CASES_ON `stamp2:stamp` THEN REWRITE_TAC[same_type_def] THEN
    RES_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[prim_type_nums_def; MEM]) THEN
    ASM_REWRITE_TAC[];
    CASES_ON `stamp1:stamp` THEN REWRITE_TAC[same_type_def] THEN
    RES_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[prim_type_nums_def; MEM]) THEN
    ASM_REWRITE_TAC[];
    RES_TAC THEN ASM_REWRITE_TAC[]];
   ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[];
   TPROPSAUX_EXN_STAMP_TAC; TPROPSAUX_EXN_STAMP_TAC; TPROPSAUX_EXN_STAMP_TAC;
   TPROPSAUX_EXN_STAMP_TAC;
   ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]]);;

(* Dexn: the new exception stamp is added to ctMap *)
let TPROPSAUX_dexn_core = prove
 (`!(st:(FFI)state) env ctMap tenvS tenv cn ts.
     type_sound_invariant st env ctMap tenvS {} tenv /\
     tenv_ok (extend_dec_tenv
       (type_env_REC nsEmpty
          (nsSing cn ([],MAP (type_name_subst (type_env_t tenv)) ts,Texn_num)) nsEmpty) tenv) /\
     ALL (check_freevars_ast []) ts /\ ALL (check_type_names (type_env_t tenv)) ts
     ==> ?ctMap' tenvS'. weakCT ctMap' ctMap /\
           FRANGE ((SND o SND) o_f ctMap') DIFF FRANGE ((SND o SND) o_f ctMap) SUBSET {} /\
           store_type_extension tenvS tenvS' /\
           type_all_env ctMap' tenvS'
             (sem_env_REC nsEmpty (nsSing cn (LENGTH ts,ExnStamp (state_next_exn_stamp st))))
             (type_env_REC nsEmpty
               (nsSing cn ([],MAP (type_name_subst (type_env_t tenv)) ts,Texn_num)) nsEmpty) /\
           type_sound_invariant
             (state_next_exn_stamp_fupd (K (state_next_exn_stamp st + 1)) st)
             (extend_dec_env
               (sem_env_REC nsEmpty (nsSing cn (LENGTH ts,ExnStamp (state_next_exn_stamp st))))
               env)
             ctMap' tenvS' {}
             (extend_dec_tenv
               (type_env_REC nsEmpty
                 (nsSing cn ([],MAP (type_name_subst (type_env_t tenv)) ts,Texn_num)) nsEmpty)
               tenv)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN TPROPSAUX_UNFOLD_TSI_TAC THEN
  SUBGOAL_THEN `~(ExnStamp (state_next_exn_stamp (st:(FFI)state)) IN FDOM (ctMap:ctMap))`
    ASSUME_TAC THENL
  [UNDISCH_TAC `consistent_ctMap (st:(FFI)state) {} ctMap` THEN
   REWRITE_TAC[consistent_ctMap_def] THEN MESON_TAC[LT_REFL];
   ALL_TAC] THEN
  SUBGOAL_THEN `ALL (check_freevars 0 []) (MAP (type_name_subst (type_env_t tenv)) ts)`
    ASSUME_TAC THENL
  [UNDISCH_TAC `ALL (check_freevars_ast []) ts` THEN
   UNDISCH_TAC `ALL (check_type_names (type_env_t tenv)) ts` THEN
   UNDISCH_TAC `tenv_ok tenv` THEN
   REWRITE_TAC[tenv_ok_def; GSYM ALL_MEM; MEM_MAP] THEN REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC[] THEN MATCH_MP_TAC check_freevars_type_name_subst THEN
   ASM_SIMP_TAC[];
   ALL_TAC] THEN
  ABBREV_TAC `newm = FUNION (FEMPTY |+ (ExnStamp (state_next_exn_stamp (st:(FFI)state)),
     ([]:tvarN list,MAP (type_name_subst (type_env_t tenv)) ts,Texn_num))) (ctMap:ctMap)` THEN
  MAP_EVERY EXISTS_TAC [`newm:ctMap`; `tenvS:tenv_store`] THEN
  REWRITE_TAC[store_type_extension_refl] THEN
  SUBGOAL_THEN `weakCT (newm:ctMap) ctMap` ASSUME_TAC THENL
  [EXPAND_TAC "newm" THEN MATCH_MP_TAC TPROPSAUX_weakCT_ext THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `type_all_env newm tenvS
    (sem_env_REC nsEmpty (nsSing cn (LENGTH ts,ExnStamp (state_next_exn_stamp (st:(FFI)state)))))
    (type_env_REC nsEmpty
      (nsSing cn ([],MAP (type_name_subst (type_env_t tenv)) ts,Texn_num)) nsEmpty)`
    ASSUME_TAC THENL
  [EXPAND_TAC "newm" THEN
   REWRITE_TAC[type_all_env_def; sem_env_INFO.ri_accessors; type_env_INFO.ri_accessors;
               nsAll2_nsEmpty; nsAll2_nsSing; type_ctor_def; TPROPSAUX_FLOOKUP_ext;
               LENGTH_MAP];
   ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
  [EXPAND_TAC "newm" THEN MATCH_MP_TAC TPROPSAUX_FRANGE_ext THEN
   EXISTS_TAC `([],[],Texn_num):tvarN list#t list#num` THEN
   EXISTS_TAC `ExnStamp 0` THEN
   UNDISCH_TAC `good_ctMap ctMap` THEN
   SIMP_TAC[good_ctMap_def; ctMap_has_exns_def; bind_stamp_def];
   ALL_TAC] THEN
  REWRITE_TAC[type_sound_invariant_def] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
  [EXPAND_TAC "newm" THEN MATCH_MP_TAC TPROPSAUX_good_ctMap_exn THEN ASM_REWRITE_TAC[];
   UNDISCH_TAC `consistent_ctMap (st:(FFI)state) {} ctMap` THEN EXPAND_TAC "newm" THEN
   REWRITE_TAC[consistent_ctMap_def; DISJOINT_EMPTY; FDOM_FUNION; FDOM_FUPDATE;
               FDOM_FEMPTY; IN_UNION; IN_INSERT; NOT_IN_EMPTY; state_INFO.ri_accfupds;
               K_THM; distinctness "stamp"; injectivity "stamp"] THEN
   MESON_TAC[ARITH_RULE `x < n ==> x < n + 1`; ARITH_RULE `n < n + 1`];
   MATCH_MP_TAC type_all_env_extend THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC type_all_env_weakening THEN
   MAP_EVERY EXISTS_TAC [`ctMap:ctMap`; `tenvS:tenv_store`] THEN
   ASM_REWRITE_TAC[weakS_refl];
   REWRITE_TAC[state_INFO.ri_accfupds] THEN MATCH_MP_TAC type_s_weakening THEN
   EXISTS_TAC `ctMap:ctMap` THEN ASM_REWRITE_TAC[]]);;

let TPROPSAUX_dts_Dexn = prove
 (TPROPSAUX_DTS 7,
  TPROPSAUX_DTS_START_TAC THEN TPROPSAUX_DTS_EVAL_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN CASE_REWRITE_TAC[] THEN
  MATCH_MP_TAC TPROPSAUX_dexn_core THEN ASM_REWRITE_TAC[]);;

(* lookups in a ctMap extended by an association list *)
let TPROPSAUX_FLOOKUP_alist_ext = prove
 (`!(l:(A#B)list) (m:(A,B)fmap) k.
     FLOOKUP (FUNION (FEMPTY |++ REVERSE l) m) k =
     option_CASE (ALOOKUP l k) (FLOOKUP m k) (\v. SOME v)`,
  REWRITE_TAC[FLOOKUP_FUNION; flookup_fupdate_list; REVERSE_REVERSE; FLOOKUP_EMPTY] THEN
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `ALOOKUP (l:(A#B)list) k` option_nchotomy) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[option_CASE]);;

(* the new stamps of a type definition are not below next *)
let TPROPSAUX_alookup_tdefs_none = prove
 (`!tenvT n tds ids k.
     LENGTH tds = LENGTH ids /\ (!cn i. k = TypeStamp cn i ==> i < n)
     ==> ALOOKUP (type_def_to_ctMap tenvT n tds ids) k = NONE`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `ALOOKUP (type_def_to_ctMap tenvT n tds ids) k` option_nchotomy) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP ALOOKUP_MEM) THEN DISCH_TAC THEN
  FIRST_ASSUM(fun mem -> FIRST_ASSUM(fun len ->
    MP_TAC(MATCH_MP mem_type_def_to_ctMap (CONJ mem len)))) THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`cn:mlstring`; `i:num`]) THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let TPROPSAUX_consistent_tdefs = prove
 (`!(st:(FFI)state) ctMap tenvT tds ids.
     LENGTH tds = LENGTH ids /\ consistent_ctMap st (set_of_list ids) ctMap
     ==> consistent_ctMap
           (state_next_type_stamp_fupd (K (state_next_type_stamp st + LENGTH tds)) st) {}
           (FUNION (FEMPTY |++ REVERSE (type_def_to_ctMap tenvT (state_next_type_stamp st)
                                          tds ids)) ctMap)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[consistent_ctMap_def; DISJOINT_EMPTY; FDOM_FUNION; FDOM_FUPDATE_LIST;
              FDOM_FEMPTY; UNION_EMPTY; IN_UNION; IN_SET_OF_LIST; MEM_MAP; MEM_REVERSE;
              EXISTS_PAIR_THM; FST; state_INFO.ri_accfupds; K_THM] THEN
  STRIP_TAC THEN REPEAT GEN_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o SPECL [`cn:mlstring`; `id:num`]) THEN
  CONJ_TAC THEN STRIP_TAC THEN RVEQ_TAC THENL
  [FIRST_ASSUM(fun mem -> FIRST_ASSUM(fun len ->
     MP_TAC(MATCH_MP mem_type_def_to_ctMap (CONJ mem len)))) THEN
   REWRITE_TAC[injectivity "stamp"] THEN STRIP_TAC THEN ASM_ARITH_TAC;
   RES_TAC THEN ASM_ARITH_TAC;
   FIRST_ASSUM(fun mem -> FIRST_ASSUM(fun len ->
     MP_TAC(MATCH_MP mem_type_def_to_ctMap (CONJ mem len)))) THEN
   REWRITE_TAC[distinctness "stamp"];
   ASM_MESON_TAC[]]);;

let TPROPSAUX_check_ctor_tenv_distinct = prove
 (CASE_TERM `!tenvT tds. check_ctor_tenv tenvT tds
     ==> ALL (\d. match d with (tvs,tn,ctors) -> ALL_DISTINCT (MAP FST ctors)) tds`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP check_ctor_tenv_dups) THEN
  MATCH_MP_TAC MONO_ALL THEN REWRITE_TAC[FORALL_PAIR_THM; check_dup_ctors_thm] THEN
  CASE_REWRITE_TAC[]);;

let TPROPSAUX_subset_disjoint = prove
 (`!a b c:A->bool. a SUBSET b /\ DISJOINT b c ==> DISJOINT a c`,
  SET_TAC[]);;

(* Dtype: the constructors of the new types are added to ctMap *)
let TPROPSAUX_dtype_core = prove
 (`!(st:(FFI)state) env ctMap tenvS tenv tds ids tenvT tenvT0.
     type_sound_invariant st env ctMap tenvS (set_of_list ids) tenv /\
     ALL_DISTINCT ids /\
     DISJOINT (set_of_list ids)
              (set_of_list (CONS Tlist_num (CONS Tbool_num prim_type_nums))) /\
     check_ctor_tenv tenvT tds /\
     LENGTH tds = LENGTH ids /\
     tenv_abbrev_ok tenvT /\
     tenv_ok (extend_dec_tenv (type_env_REC nsEmpty (build_ctor_tenv tenvT tds ids) tenvT0)
                tenv)
     ==> ?ctMap' tenvS'. weakCT ctMap' ctMap /\
           FRANGE ((SND o SND) o_f ctMap') DIFF FRANGE ((SND o SND) o_f ctMap) SUBSET
             set_of_list ids /\
           store_type_extension tenvS tenvS' /\
           type_all_env ctMap' tenvS'
             (sem_env_REC nsEmpty (build_tdefs (state_next_type_stamp st) tds))
             (type_env_REC nsEmpty (build_ctor_tenv tenvT tds ids) tenvT0) /\
           type_sound_invariant
             (state_next_type_stamp_fupd (K (state_next_type_stamp st + LENGTH tds)) st)
             (extend_dec_env
               (sem_env_REC nsEmpty (build_tdefs (state_next_type_stamp st) tds)) env)
             ctMap' tenvS' {}
             (extend_dec_tenv (type_env_REC nsEmpty (build_ctor_tenv tenvT tds ids) tenvT0)
               tenv)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN TPROPSAUX_UNFOLD_TSI_TAC THEN
  ABBREV_TAC `n = state_next_type_stamp (st:(FFI)state)` THEN
  ABBREV_TAC `L = type_def_to_ctMap tenvT n tds ids` THEN
  ABBREV_TAC `newm = FUNION (FEMPTY |++ REVERSE L) (ctMap:ctMap)` THEN
  SUBGOAL_THEN `!cn i. TypeStamp cn i IN FDOM (ctMap:ctMap) ==> i < n` ASSUME_TAC THENL
  [UNDISCH_TAC `consistent_ctMap (st:(FFI)state) (set_of_list ids) ctMap` THEN
   ASM_REWRITE_TAC[consistent_ctMap_def] THEN MESON_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `!stamp x. MEM (stamp,x) (L:(stamp#tvarN list#t list#num)list)
                  ==> ?cn i. stamp = TypeStamp cn i /\ n <= i /\ i < n + LENGTH (tds:type_def)`
    ASSUME_TAC THENL
  [EXPAND_TAC "L" THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC mem_type_def_to_ctMap THEN
   ASM_MESON_TAC[];
   ALL_TAC] THEN
  (* the new map is an extension *)
  SUBGOAL_THEN `weakCT (newm:ctMap) ctMap` ASSUME_TAC THENL
  [EXPAND_TAC "newm" THEN MATCH_MP_TAC disjoint_env_weakCT THEN
   REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; FDOM_FUPDATE_LIST;
               FDOM_FEMPTY; UNION_EMPTY; IN_SET_OF_LIST; MEM_MAP; MEM_REVERSE;
               EXISTS_PAIR_THM; FST] THEN
   X_GEN_TAC `k:stamp` THEN STRIP_TAC THEN RVEQ_TAC THEN
   FIRST_X_ASSUM(fun th -> FIRST_ASSUM(MP_TAC o MATCH_MP th)) THEN STRIP_TAC THEN
   RVEQ_TAC THEN RES_TAC THEN ASM_ARITH_TAC;
   ALL_TAC] THEN
  (* the new type identities are among ids *)
  SUBGOAL_THEN `FRANGE ((SND o SND) o_f (FEMPTY |++ REVERSE (L:(stamp#tvarN list#t list#num)list)))
                  SUBSET set_of_list (ids:num list)`
    ASSUME_TAC THENL
  [REWRITE_TAC[SUBSET; FRANGE_FLOOKUP; FLOOKUP_o_f; flookup_fupdate_list; REVERSE_REVERSE;
               FLOOKUP_EMPTY; IN_SET_OF_LIST] THEN
   X_GEN_TAC `x:num` THEN DISCH_THEN(X_CHOOSE_THEN `k:stamp` MP_TAC) THEN
   MP_TAC(ISPEC `ALOOKUP (L:(stamp#tvarN list#t list#num)list) k` option_nchotomy) THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[option_CASE; option_DISTINCT; injectivity "option";
                                  o_THM] THEN
   DISCH_THEN(SUBST1_TAC o SYM) THEN
   MP_TAC(SPECL [`tenvT:tenv_abbrev`; `n:num`; `tds:type_def`; `ids:num list`]
     (INST [`x':tvarN list#t list#num`,`x:tvarN list#t list#num`]
        type_def_to_ctMap_mem)) THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `FRANGE ((SND o SND) o_f (newm:ctMap)) DIFF
                FRANGE ((SND o SND) o_f (ctMap:ctMap)) SUBSET set_of_list (ids:num list)`
    ASSUME_TAC THENL
  [UNDISCH_TAC `FRANGE ((SND o SND) o_f (FEMPTY |++ REVERSE (L:(stamp#tvarN list#t list#num)list)))
                  SUBSET set_of_list (ids:num list)` THEN
   EXPAND_TAC "newm" THEN
   REWRITE_TAC[SUBSET; IN_DIFF; FRANGE_FLOOKUP; FLOOKUP_o_f; TPROPSAUX_FLOOKUP_alist_ext;
               flookup_fupdate_list; REVERSE_REVERSE; FLOOKUP_EMPTY] THEN
   DISCH_TAC THEN X_GEN_TAC `x:num` THEN
   DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `k:stamp` MP_TAC) MP_TAC) THEN
   MP_TAC(ISPEC `ALOOKUP (L:(stamp#tvarN list#t list#num)list) k` option_nchotomy) THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[option_CASE] THENL
   [DISCH_THEN(MP_TAC o SPEC `k:stamp` o REWRITE_RULE[NOT_EXISTS_THM]) THEN MESON_TAC[];
    DISCH_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `k:stamp` THEN ASM_REWRITE_TAC[option_CASE]];
   ALL_TAC] THEN
  (* the environment of the new constructors *)
  SUBGOAL_THEN `type_all_env newm tenvS (sem_env_REC nsEmpty (build_tdefs n (tds:type_def)))
                  (type_env_REC nsEmpty (build_ctor_tenv tenvT tds ids) tenvT0)`
    ASSUME_TAC THENL
  [EXPAND_TAC "newm" THEN EXPAND_TAC "L" THEN REWRITE_TAC[GSYM fupdate_list_funion] THEN
   REWRITE_TAC[type_all_env_def; sem_env_INFO.ri_accessors; type_env_INFO.ri_accessors;
               nsAll2_nsEmpty] THEN
   MATCH_MP_TAC build_tdefs_build_tenv THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC TPROPSAUX_check_ctor_tenv_distinct THEN
   EXISTS_TAC `tenvT:tenv_abbrev` THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* lookups of the old stamps are unchanged *)
  SUBGOAL_THEN `bool_type_num < n /\ list_type_num < n` STRIP_ASSUME_TAC THENL
  [UNDISCH_TAC `good_ctMap ctMap` THEN
   REWRITE_TAC[good_ctMap_def; ctMap_has_bools_def; ctMap_has_lists_def] THEN
   STRIP_TAC THEN ASM_MESON_TAC[FDOM_FLOOKUP; option_DISTINCT];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `(!cn i. i < n ==> FLOOKUP (newm:ctMap) (TypeStamp cn i) = FLOOKUP ctMap (TypeStamp cn i)) /\
     (!e. FLOOKUP (newm:ctMap) (ExnStamp e) = FLOOKUP ctMap (ExnStamp e))`
    STRIP_ASSUME_TAC THENL
  [EXPAND_TAC "newm" THEN REWRITE_TAC[TPROPSAUX_FLOOKUP_alist_ext] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `ALOOKUP (L:(stamp#tvarN list#t list#num)list) (TypeStamp cn i) = NONE`
      (fun th -> REWRITE_TAC[th; option_CASE]) THEN
    EXPAND_TAC "L" THEN MATCH_MP_TAC TPROPSAUX_alookup_tdefs_none THEN
    ASM_REWRITE_TAC[injectivity "stamp"] THEN ASM_MESON_TAC[];
    GEN_TAC THEN
    SUBGOAL_THEN `ALOOKUP (L:(stamp#tvarN list#t list#num)list) (ExnStamp e) = NONE`
      (fun th -> REWRITE_TAC[th; option_CASE]) THEN
    EXPAND_TAC "L" THEN MATCH_MP_TAC TPROPSAUX_alookup_tdefs_none THEN
    ASM_REWRITE_TAC[distinctness "stamp"]];
   ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`newm:ctMap`; `tenvS:tenv_store`] THEN
  ASM_REWRITE_TAC[store_type_extension_refl] THEN
  REWRITE_TAC[type_sound_invariant_def] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
  [(* good_ctMap *)
   FIRST_ASSUM(STRIP_ASSUME_TAC o
     REWRITE_RULE[good_ctMap_def; ctMap_has_bools_def; ctMap_has_exns_def;
                  ctMap_has_lists_def; bind_stamp_def; chr_stamp_def; div_stamp_def;
                  subscript_stamp_def] o
     check (can (term_match [] `good_ctMap c`) o concl)) THEN
   REWRITE_TAC[good_ctMap_def; ctMap_has_bools_def; ctMap_has_exns_def;
               ctMap_has_lists_def; bind_stamp_def; chr_stamp_def; div_stamp_def;
               subscript_stamp_def] THEN
   ASM_SIMP_TAC[] THEN
   EXPAND_TAC "newm" THEN MATCH_MP_TAC ctMap_ok_merge_imp THEN ASM_REWRITE_TAC[] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC TPROPSAUX_subset_disjoint THEN
    EXISTS_TAC `set_of_list (ids:num list)` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `consistent_ctMap (st:(FFI)state) (set_of_list ids) ctMap` THEN
    SIMP_TAC[consistent_ctMap_def];
    EXPAND_TAC "L" THEN MATCH_MP_TAC ctMap_ok_type_defs THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `DISJOINT (set_of_list (ids:num list))
                   (set_of_list (CONS Tlist_num (CONS Tbool_num prim_type_nums)))` THEN
    REWRITE_TAC[set_of_list] THEN SET_TAC[]];
   (* consistent_ctMap *)
   MP_TAC(SPECL [`st:(FFI)state`; `ctMap:ctMap`; `tenvT:tenv_abbrev`; `tds:type_def`;
                 `ids:num list`] TPROPSAUX_consistent_tdefs) THEN
   ASM_REWRITE_TAC[];
   (* type_all_env *)
   MATCH_MP_TAC type_all_env_extend THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC type_all_env_weakening THEN
   MAP_EVERY EXISTS_TAC [`ctMap:ctMap`; `tenvS:tenv_store`] THEN
   ASM_REWRITE_TAC[weakS_refl];
   (* type_s *)
   REWRITE_TAC[state_INFO.ri_accfupds] THEN MATCH_MP_TAC type_s_weakening THEN
   EXISTS_TAC `ctMap:ctMap` THEN ASM_REWRITE_TAC[]]);;

let TPROPSAUX_dts_Dtype = prove
 (TPROPSAUX_DTS 4,
  TPROPSAUX_DTS_START_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP check_ctor_tenv_dups o
    check (can (term_match [] `check_ctor_tenv a b`) o concl)) THEN
  TPROPSAUX_DTS_EVAL_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN CASE_REWRITE_TAC[] THEN
  MATCH_MP_TAC TPROPSAUX_dtype_core THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (can (term_match [] `tenv_ok (extend_dec_tenv a b)`) o
    concl)) THEN
  REWRITE_TAC[tenv_ok_def; extend_dec_tenv_def; type_env_INFO.ri_accessors] THEN
  SIMP_TAC[]);;

let decs_type_sound_no_check = prove
 (CASE_TERM
  `!(st:(FFI)state) env ds st' r ctMap tenvS tenv tids tenv'.
     evaluate_decs st env ds = (st',r) /\ type_ds F tenv ds tids tenv' /\
     type_sound_invariant st env ctMap tenvS tids tenv
     ==> ?ctMap' tenvS'. weakCT ctMap' ctMap /\
           FRANGE ((SND o SND) o_f ctMap') DIFF FRANGE ((SND o SND) o_f ctMap) SUBSET tids /\
           store_type_extension tenvS tenvS' /\
           (match r with
              Rval env' -> type_all_env ctMap' tenvS' env' tenv' /\
                type_sound_invariant st' (extend_dec_env env' env) ctMap' tenvS' {}
                  (extend_dec_tenv tenv' tenv)
            | Rerr (Rraise err_v) -> type_v 0 ctMap' tenvS' err_v Texn /\
                type_sound_invariant st' env ctMap' tenvS' {} tenv
            | Rerr (Rabort Rtype_error) -> F
            | Rerr (Rabort Rtimeout_error) -> T
            | Rerr (Rabort (Rffi_error _)) -> T)`,
  ACCEPT_TAC (MATCH_MP TPROPSAUX_DTS_IND (end_itlist CONJ
    [TPROPSAUX_dts_nil; TPROPSAUX_dts_cons; TPROPSAUX_dts_Dlet; TPROPSAUX_dts_Dletrec;
     TPROPSAUX_dts_Dtype; TPROPSAUX_dts_Dtabbrev; TPROPSAUX_dts_Denv; TPROPSAUX_dts_Dexn;
     TPROPSAUX_dts_Dmod; TPROPSAUX_dts_Dlocal])));;

let decs_type_sound = prove
 (CASE_TERM
  `!(st:(FFI)state) env ds extra_checks st' r ctMap tenvS tenv tids tenv'.
     evaluate_decs st env ds = (st',r) /\ type_ds extra_checks tenv ds tids tenv' /\
     type_sound_invariant st env ctMap tenvS tids tenv
     ==> ?ctMap' tenvS'. weakCT ctMap' ctMap /\
           FRANGE ((SND o SND) o_f ctMap') DIFF FRANGE ((SND o SND) o_f ctMap) SUBSET tids /\
           store_type_extension tenvS tenvS' /\
           (match r with
              Rval env' -> type_all_env ctMap' tenvS' env' tenv' /\
                type_sound_invariant st' (extend_dec_env env' env) ctMap' tenvS' {}
                  (extend_dec_tenv tenv' tenv)
            | Rerr (Rraise err_v) -> type_v 0 ctMap' tenvS' err_v Texn /\
                type_sound_invariant st' env ctMap' tenvS' {} tenv
            | Rerr (Rabort Rtype_error) -> F
            | Rerr (Rabort (Rffi_error _)) -> T
            | Rerr (Rabort Rtimeout_error) -> T)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC decs_type_sound_no_check THEN
  ASM_MESON_TAC[type_d_check_uniq]);;

let semantics_type_sound = prove
 (`!(st:(FFI)state) env tops r checks ctMap tenvS tenv new_tenv tids.
     semantics_prog st env tops r /\ type_ds checks tenv tops tids new_tenv /\
     type_sound_invariant st env ctMap tenvS tids tenv
     ==> ~(r = Fail)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[semantics_prog_def] o
    check (can (term_match [] `semantics_prog (a:(FFI)state) b c d`) o concl)) THEN
  REWRITE_TAC[evaluate_prog_with_clock_def; NOT_EXISTS_THM] THEN X_GEN_TAC `k:num` THEN
  MP_TAC(ISPEC `evaluate_decs (state_clock_fupd (K k) (st:(FFI)state)) env tops`
    PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `st1:(FFI)state`
    (X_CHOOSE_THEN `r1:(v sem_env,v)result` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[SND] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`state_clock_fupd (K k) (st:(FFI)state)`; `env:v sem_env`;
    `tops:dec list`; `checks:bool`; `st1:(FFI)state`; `r1:(v sem_env,v)result`;
    `ctMap:ctMap`; `tenvS:tenv_store`; `tenv:type_env`; `tids:num->bool`;
    `new_tenv:type_env`] decs_type_sound) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  UNDISCH_TAC `type_sound_invariant (st:(FFI)state) env ctMap tenvS tids tenv` THEN
  REWRITE_TAC[type_sound_invariant_def; consistent_ctMap_def; state_INFO.ri_accfupds] THEN
  SIMP_TAC[]);;
