(* ========================================================================= *)
(* holSoundness: port of HOL4 candle/standard/semantics/holSoundnessScript   *)
(* .sml (CakeML v3479).  Soundness of the inference system: any provable     *)
(* sequent is valid.  Notes on the rendering: the header of holSemantics.ml. *)
(* ========================================================================= *)

needs "candle/set-theory/setSpec.ml";;
needs "candle/syntax-lib/holSyntaxLib.ml";;
needs "candle/standard/syntax/holSyntax.ml";;
needs "candle/standard/syntax/holSyntaxExtra.ml";;
needs "candle/standard/semantics/holSemantics.ml";;
needs "candle/standard/semantics/holSemanticsExtra.ml";;

prioritize_num();;
type_invention_error := true;;
let binary_inference_rule = prove
 (`is_set_theory (mem:U->U->bool) ==>
   !thy h1 h2 p1 p2 q.
     q has_type Tyapp (implode "bool") [] /\ hol_term_ok (FST thy) q /\
     (!i v. is_structure0 mem (FST thy) i v /\
            termsem0 mem (SND (FST thy)) i v p1 = setSpec_true mem /\
            termsem0 mem (SND (FST thy)) i v p2 = setSpec_true mem
            ==> termsem0 mem (SND (FST thy)) i v q = setSpec_true mem) /\
     entails0 mem (thy,h1) p1 /\ entails0 mem (thy,h2) p2
     ==> entails0 mem (thy,term_union h1 h2) q`,
  STRIP_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[entails0_def; ALL] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC EVERY_term_union THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC EVERY_term_union THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC hypset_ok_term_union THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `i:(mlstring->U list->U)#(mlstring->U list->U)` THEN DISCH_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `i:(mlstring->U list->U)#(mlstring->U list->U)` o
                      check (is_forall o concl))) THEN
  ASM_REWRITE_TAC[satisfies0_def] THEN REPEAT DISCH_TAC THEN
  X_GEN_TAC `v:(mlstring->U)#(mlstring#hol_type->U)` THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  SUBGOAL_THEN `is_structure0 (mem:U->U->bool) (FST (thy:thy)) i v` ASSUME_TAC THENL
   [REWRITE_TAC[is_structure0_def] THEN RULE_ASSUM_TAC(REWRITE_RULE[models0_def]) THEN
    ASM_MESON_TAC[theory_ok_sig];
    ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN
   `!t. MEM t h1 \/ MEM t h2
        ==> termsem0 (mem:U->U->bool) (SND (FST (thy:thy))) i v t = setSpec_true mem`
   MP_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`h1:hol_term list`; `h2:hol_term list`; `t:hol_term`] MEM_term_union) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `y:hol_term` STRIP_ASSUME_TAC) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_MEM]) THEN
    SUBGOAL_THEN `welltyped t /\ welltyped y` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[term_ok_welltyped; MEM_term_union_imp]; ALL_TAC] THEN
    TRANS_TAC EQ_TRANS `termsem0 (mem:U->U->bool) (SND (FST (thy:thy))) i v y` THEN
    CONJ_TAC THENL [MATCH_MP_TAC termsem_aconv THEN ASM_REWRITE_TAC[]; ASM_MESON_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[TAUT `(a \/ b ==> c) <=> (a ==> c) /\ (b ==> c)`; FORALL_AND_THM] THEN
  STRIP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_MEM]) THEN ASM_MESON_TAC[]);;
let ABS_correct = prove
 (`is_set_theory (mem:U->U->bool) ==>
   !thy x ty h l r.
     ~EX (VFREE_IN (hol_Var x ty)) h /\ type_ok (FST (FST thy)) ty /\
     entails0 mem (thy,h) (l === r)
     ==> entails0 mem (thy,h) (hol_Abs (hol_Var x ty) l === hol_Abs (hol_Var x ty) r)`,
  STRIP_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[entails0_def; ALL] THEN STRIP_TAC THEN
  SUBGOAL_THEN `is_std_sig (FST (thy:thy))` ASSUME_TAC THENL
   [ASM_MESON_TAC[theory_ok_sig]; ALL_TAC] THEN
  SUBGOAL_THEN `hol_term_ok (FST (thy:thy)) l /\ hol_term_ok (FST thy) r /\ typeof r = typeof l`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[term_ok_equation]; ALL_TAC] THEN
  SUBGOAL_THEN `welltyped l /\ welltyped r` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[term_ok_welltyped]; ALL_TAC] THEN
  SUBGOAL_THEN `hol_term_ok (FST (thy:thy))
                  (hol_Abs (hol_Var x ty) l === hol_Abs (hol_Var x ty) r)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[term_ok_equation; hol_term_ok_def; typeof_def] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[EQUATION_HAS_TYPE_BOOL; WELLTYPED_CLAUSES; typeof_def] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `i:(mlstring->U list->U)#(mlstring->U list->U)` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:(mlstring->U list->U)#(mlstring->U list->U)` o
                check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[satisfies0_def] THEN DISCH_TAC THEN
  X_GEN_TAC `v:(mlstring->U)#(mlstring#hol_type->U)` THEN STRIP_TAC THEN
  SUBGOAL_THEN `is_structure0 (mem:U->U->bool) (FST (thy:thy)) i v` ASSUME_TAC THENL
   [REWRITE_TAC[is_structure0_def] THEN RULE_ASSUM_TAC(REWRITE_RULE[models0_def]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`FST (thy:thy)`; `i:(mlstring->U list->U)#(mlstring->U list->U)`;
                 `v:(mlstring->U)#(mlstring#hol_type->U)`;
                 `hol_Abs (hol_Var x ty) l`; `hol_Abs (hol_Var x ty) r`;
                 `SND (FST (thy:thy))`] (UNDISCH termsem_equation)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[boolean_eq_true; termsem0_def] THEN
  MATCH_MP_TAC(UNDISCH abstract_eq) THEN X_GEN_TAC `m:U` THEN DISCH_TAC THEN BETA_TAC THEN
  ABBREV_TAC `vv = (FST (v:(mlstring->U)#(mlstring#hol_type->U)), ((x,ty) =+ (m:U)) (SND v))` THEN
  SUBGOAL_THEN `is_valuation0 (mem:U->U->bool) (FST (FST (thy:thy))) (FST (i:(mlstring->U list->U)#(mlstring->U list->U))) vv` ASSUME_TAC THENL
   [EXPAND_TAC "vv" THEN
    RULE_ASSUM_TAC(REWRITE_RULE[is_valuation0_def; is_term_valuation0_def]) THEN
    ASM_REWRITE_TAC[is_valuation0_def; is_term_valuation0_def; APPLY_UPDATE_THM] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `is_std_type_assignment0 (mem:U->U->bool) (FST (i:(mlstring->U list->U)#(mlstring->U list->U)))` ASSUME_TAC THENL
   [ASM_MESON_TAC[models0_def; is_std_interpretation_is_type]; ALL_TAC] THEN
  SUBGOAL_THEN `is_interpretation0 (mem:U->U->bool) (FST (thy:thy)) i` ASSUME_TAC THENL
   [ASM_MESON_TAC[models0_def]; ALL_TAC] THEN
  SUBGOAL_THEN `FST (vv:(mlstring->U)#(mlstring#hol_type->U)) =
                FST (v:(mlstring->U)#(mlstring#hol_type->U))` ASSUME_TAC THENL
   [EXPAND_TAC "vv" THEN REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN MATCH_MP_TAC(UNDISCH termsem_typesem) THEN
    ASM_MESON_TAC[];
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) && is_comb(lhs(concl th)) && fst(dest_const(fst(strip_comb(lhs(concl th))))) = "typeof")) THEN
    MATCH_MP_TAC(UNDISCH termsem_typesem) THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `vv:(mlstring->U)#(mlstring#hol_type->U)`) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[GSYM ALL_MEM] THEN X_GEN_TAC `t:hol_term` THEN DISCH_TAC THEN
    TRANS_TAC EQ_TRANS `termsem0 (mem:U->U->bool) (SND (FST (thy:thy))) i v t` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC termsem_frees THEN EXPAND_TAC "vv" THEN REWRITE_TAC[APPLY_UPDATE_THM] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_MEM; NOT_EX]) THEN
      CONJ_TAC THENL [ASM_MESON_TAC[term_ok_welltyped]; ALL_TAC] THEN
      REPEAT STRIP_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN ASM_MESON_TAC[];
      RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_MEM]) THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`FST (thy:thy)`; `i:(mlstring->U list->U)#(mlstring->U list->U)`;
                 `vv:(mlstring->U)#(mlstring#hol_type->U)`; `l:hol_term`; `r:hol_term`;
                 `SND (FST (thy:thy))`] (UNDISCH termsem_equation)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[is_structure0_def] THEN ASM_MESON_TAC[models0_def; is_structure0_def];
    DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[boolean_eq_true]);;
let ASSUME_correct = prove
 (`!thy p.
     theory_ok thy /\ p has_type Tyapp (implode "bool") [] /\ hol_term_ok (FST thy) p
     ==> entails0 (mem:U->U->bool) (thy,[p]) p`,
  SIMP_TAC[entails0_def; satisfies0_def; ALL; hypset_ok_def; SORTED_DEF]);;

let BETA_correct = prove
 (`is_set_theory (mem:U->U->bool) ==>
   !thy x ty t.
     theory_ok thy /\ type_ok (FST (FST thy)) ty /\ hol_term_ok (FST thy) t
     ==> entails0 mem (thy,[])
           (hol_Comb (hol_Abs (hol_Var x ty) t) (hol_Var x ty) === t)`,
  STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `is_std_sig (FST (thy:thy))` ASSUME_TAC THENL
   [ASM_MESON_TAC[theory_ok_sig]; ALL_TAC] THEN
  SUBGOAL_THEN `welltyped t` ASSUME_TAC THENL [ASM_MESON_TAC[term_ok_welltyped]; ALL_TAC] THEN
  SUBGOAL_THEN `hol_term_ok (FST (thy:thy))
                  (hol_Comb (hol_Abs (hol_Var x ty) t) (hol_Var x ty) === t)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[term_ok_equation; hol_term_ok_def; typeof_def; WELLTYPED_CLAUSES;
                 codomain_def] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[entails0_def; ALL; hypset_ok_def; SORTED_DEF; EQUATION_HAS_TYPE_BOOL;
                  WELLTYPED_CLAUSES; typeof_def; codomain_def] THEN
  CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `i:(mlstring->U list->U)#(mlstring->U list->U)` THEN DISCH_TAC THEN
  REWRITE_TAC[satisfies0_def; ALL] THEN
  X_GEN_TAC `v:(mlstring->U)#(mlstring#hol_type->U)` THEN DISCH_TAC THEN
  SUBGOAL_THEN `is_structure0 (mem:U->U->bool) (FST (thy:thy)) i v` ASSUME_TAC THENL
   [REWRITE_TAC[is_structure0_def] THEN RULE_ASSUM_TAC(REWRITE_RULE[models0_def]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`FST (thy:thy)`; `i:(mlstring->U list->U)#(mlstring->U list->U)`;
                 `v:(mlstring->U)#(mlstring#hol_type->U)`;
                 `hol_Comb (hol_Abs (hol_Var x ty) t) (hol_Var x ty)`; `t:hol_term`;
                 `SND (FST (thy:thy))`] (UNDISCH termsem_equation)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[boolean_eq_true; termsem0_def] THEN
  W(fun (asl,w) -> MP_TAC(PART_MATCH (lhand o rand) (UNDISCH apply_abstract) (lhs w))) THEN
  ANTS_TAC THENL
   [BETA_TAC THEN REWRITE_TAC[APPLY_UPDATE_ID; PAIR] THEN CONJ_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[is_structure0_def; is_valuation0_def;
                                  is_term_valuation0_def]) THEN ASM_MESON_TAC[];
      MATCH_MP_TAC(UNDISCH termsem_typesem) THEN EXISTS_TAC `FST (thy:thy)` THEN
      RULE_ASSUM_TAC(REWRITE_RULE[is_structure0_def]) THEN
      ASM_MESON_TAC[is_std_interpretation_is_type]];
    DISCH_THEN SUBST1_TAC THEN BETA_TAC THEN REWRITE_TAC[APPLY_UPDATE_ID; PAIR]]);;
let DEDUCT_ANTISYM_correct = prove
 (`is_set_theory (mem:U->U->bool) ==>
   !thy h1 p1 h2 p2.
     entails0 mem (thy,h1) p1 /\ entails0 mem (thy,h2) p2
     ==> entails0 mem (thy, term_union (term_remove p2 h1) (term_remove p1 h2)) (p1 === p2)`,
  STRIP_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[entails0_def; ALL] THEN STRIP_TAC THEN
  SUBGOAL_THEN `is_std_sig (FST (thy:thy))` ASSUME_TAC THENL
   [ASM_MESON_TAC[theory_ok_sig]; ALL_TAC] THEN
  SUBGOAL_THEN `typeof p1 = Tyapp (implode "bool") [] /\ typeof p2 = Tyapp (implode "bool") []`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[WELLTYPED_LEMMA]; ALL_TAC] THEN
  ASM_SIMP_TAC[term_ok_equation; EQUATION_HAS_TYPE_BOOL] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC EVERY_term_union THEN CONJ_TAC THEN MATCH_MP_TAC EVERY_term_remove THEN
    ASM_REWRITE_TAC[];
    ASM_MESON_TAC[welltyped_def];
    ASM_MESON_TAC[welltyped_def];
    MATCH_MP_TAC EVERY_term_union THEN CONJ_TAC THEN MATCH_MP_TAC EVERY_term_remove THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC hypset_ok_term_union THEN ASM_SIMP_TAC[hypset_ok_term_remove];
    ALL_TAC] THEN
  X_GEN_TAC `i:(mlstring->U list->U)#(mlstring->U list->U)` THEN DISCH_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `i:(mlstring->U list->U)#(mlstring->U list->U)` o
                      check (is_forall o concl))) THEN
  ASM_REWRITE_TAC[satisfies0_def; GSYM ALL_MEM] THEN REPEAT DISCH_TAC THEN
  X_GEN_TAC `v:(mlstring->U)#(mlstring#hol_type->U)` THEN STRIP_TAC THEN
  SUBGOAL_THEN `is_structure0 (mem:U->U->bool) (FST (thy:thy)) i v` ASSUME_TAC THENL
   [REWRITE_TAC[is_structure0_def] THEN RULE_ASSUM_TAC(REWRITE_RULE[models0_def]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `hol_term_ok (FST (thy:thy)) (p1 === p2)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[term_ok_equation]; ALL_TAC] THEN
  MP_TAC(ISPECL [`FST (thy:thy)`; `i:(mlstring->U list->U)#(mlstring->U list->U)`;
                 `v:(mlstring->U)#(mlstring#hol_type->U)`; `p1:hol_term`; `p2:hol_term`;
                 `SND (FST (thy:thy))`] (UNDISCH termsem_equation)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[boolean_eq_true] THEN
  ABBREV_TAC `sem = termsem0 (mem:U->U->bool) (SND (FST (thy:thy))) i v` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_MEM]) THEN
  SUBGOAL_THEN `!t. MEM t h1 \/ MEM t h2 ==> welltyped t` ASSUME_TAC THENL
   [ASM_MESON_TAC[term_ok_welltyped]; ALL_TAC] THEN
  SUBGOAL_THEN `welltyped p1 /\ welltyped p2` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[term_ok_welltyped]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. MEM t (term_union (term_remove p2 h1) (term_remove p1 h2))
        ==> welltyped t`
   ASSUME_TAC THENL
   [ASM_MESON_TAC[MEM_term_union_imp; MEM_term_remove_imp]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(!t. MEM t h1 /\ ~ACONV p2 t ==> (sem:hol_term->U) t = setSpec_true (mem:U->U->bool)) /\
    (!t. MEM t h2 /\ ~ACONV p1 t ==> sem t = setSpec_true mem)`
   STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN X_GEN_TAC `t:hol_term` THEN STRIP_TAC THENL
     [MP_TAC(ISPECL [`term_remove p2 h1`; `term_remove p1 h2`; `t:hol_term`] MEM_term_union);
      MP_TAC(ISPECL [`term_remove p2 h1`; `term_remove p1 h2`; `t:hol_term`] MEM_term_union)] THEN
    ASM_SIMP_TAC[hypset_ok_term_remove; MEM_term_remove] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:hol_term` STRIP_ASSUME_TAC) THEN
    TRANS_TAC EQ_TRANS `(sem:hol_term->U) y` THEN
    (CONJ_TAC THENL [EXPAND_TAC "sem" THEN MATCH_MP_TAC termsem_aconv THEN ASM_MESON_TAC[];
                     ASM_MESON_TAC[]]);
    ALL_TAC] THEN
  SUBGOAL_THEN `((sem:hol_term->U) p2 = setSpec_true (mem:U->U->bool) ==> sem p1 = setSpec_true mem) /\
                (sem p1 = setSpec_true mem ==> sem p2 = setSpec_true mem)`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_TAC THEN EXPAND_TAC "sem" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:hol_term` THEN DISCH_TAC THENL
     [ASM_CASES_TAC `ACONV p2 t` THENL
       [TRANS_TAC EQ_TRANS `(sem:hol_term->U) p2` THEN CONJ_TAC THENL
         [EXPAND_TAC "sem" THEN MATCH_MP_TAC termsem_aconv THEN ASM_MESON_TAC[ACONV_SYM];
          ASM_REWRITE_TAC[]];
        ASM_MESON_TAC[]];
      ASM_CASES_TAC `ACONV p1 t` THENL
       [TRANS_TAC EQ_TRANS `(sem:hol_term->U) p1` THEN CONJ_TAC THENL
         [EXPAND_TAC "sem" THEN MATCH_MP_TAC termsem_aconv THEN ASM_MESON_TAC[ACONV_SYM];
          ASM_REWRITE_TAC[]];
        ASM_MESON_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(mem:U->U->bool) ((sem:hol_term->U) p1) (setSpec_two mem) /\ mem (sem p2) (setSpec_two mem)` MP_TAC THENL
   [EXPAND_TAC "sem" THEN
    SUBGOAL_THEN `is_std_type_assignment0 (mem:U->U->bool) (FST (i:(mlstring->U list->U)#(mlstring->U list->U)))`
      ASSUME_TAC THENL [ASM_MESON_TAC[models0_def; is_std_interpretation_is_type]; ALL_TAC] THEN
    CONJ_TAC THEN
    MATCH_MP_TAC(UNDISCH termsem_typesem_matchable) THEN
    MAP_EVERY EXISTS_TAC [`FST (thy:thy)`;
                          `FST (i:(mlstring->U list->U)#(mlstring->U list->U))`;
                          `FST (v:(mlstring->U)#(mlstring#hol_type->U))`] THEN
    ASM_SIMP_TAC[typesem_Bool] THEN RULE_ASSUM_TAC(REWRITE_RULE[models0_def]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[mem_boolset] THEN ASM_MESON_TAC[true_neq_false]);;
let EQ_MP_correct = prove
 (`is_set_theory (mem:U->U->bool) ==>
   !thy h1 h2 p q p'.
     entails0 mem (thy,h1) (p === q) /\ entails0 mem (thy,h2) p' /\ ACONV p p'
     ==> entails0 mem (thy,term_union h1 h2) q`,
  STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(UNDISCH binary_inference_rule) THEN
  MAP_EVERY EXISTS_TAC [`p === q`; `p':hol_term`] THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[entails0_def; ALL; EQUATION_HAS_TYPE_BOOL]) THEN
  SUBGOAL_THEN `is_std_sig (FST (thy:thy))` ASSUME_TAC THENL
   [ASM_MESON_TAC[theory_ok_sig]; ALL_TAC] THEN
  SUBGOAL_THEN `hol_term_ok (FST (thy:thy)) p /\ hol_term_ok (FST thy) q /\ typeof q = typeof p`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[term_ok_equation]; ALL_TAC] THEN
  SUBGOAL_THEN `welltyped p'` ASSUME_TAC THENL [ASM_MESON_TAC[term_ok_welltyped]; ALL_TAC] THEN
  SUBGOAL_THEN `typeof p = typeof p'` ASSUME_TAC THENL
   [ASM_MESON_TAC[ACONV_TYPE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[WELLTYPED; WELLTYPED_LEMMA]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `hol_term_ok (FST (thy:thy)) (p === q)` ASSUME_TAC THENL
   [ASM_MESON_TAC[term_ok_equation]; ALL_TAC] THEN
  UNDISCH_TAC `termsem0 (mem:U->U->bool) (SND (FST (thy:thy))) i v (p === q) =
                setSpec_true mem` THEN
  MP_TAC(ISPECL [`FST (thy:thy)`; `i:(mlstring->U list->U)#(mlstring->U list->U)`;
                 `v:(mlstring->U)#(mlstring#hol_type->U)`; `p:hol_term`; `q:hol_term`;
                 `SND (FST (thy:thy))`] (UNDISCH termsem_equation)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[boolean_eq_true] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  TRANS_TAC EQ_TRANS `termsem0 (mem:U->U->bool) (SND (FST (thy:thy))) i v p'` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC termsem_aconv THEN ASM_MESON_TAC[term_ok_welltyped]; ASM_REWRITE_TAC[]]);;
(* HOL4: ilist is a free variable of the statement *)
let INST_correct = prove
 (`is_set_theory (mem:U->U->bool) ==>
   !thy h c.
     (!s s'. MEM (s',s) ilist
             ==> ?x ty. s = hol_Var x ty /\ s' has_type ty /\ hol_term_ok (FST thy) s') /\
     entails0 mem (thy,h) c
     ==> entails0 mem (thy,term_image (VSUBST ilist) h) (VSUBST ilist c)`,
  STRIP_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[entails0_def; ALL] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_MEM]) THEN ASM_REWRITE_TAC[GSYM ALL_MEM] THEN
  SUBGOAL_THEN `!s s'. MEM (s',s) ilist ==> ?x ty. s = hol_Var x ty /\ s' has_type ty`
    ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!t. MEM t h ==> welltyped t` ASSUME_TAC THENL
   [ASM_MESON_TAC[term_ok_welltyped]; ALL_TAC] THEN
  SUBGOAL_THEN `welltyped c` ASSUME_TAC THENL [ASM_MESON_TAC[term_ok_welltyped]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC term_ok_VSUBST THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP MEM_term_image_imp) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC term_ok_VSUBST THEN ASM_MESON_TAC[];
    MATCH_MP_TAC VSUBST_HAS_TYPE THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP MEM_term_image_imp) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC VSUBST_HAS_TYPE THEN ASM_MESON_TAC[];
    MATCH_MP_TAC hypset_ok_term_image THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `i:(mlstring->U list->U)#(mlstring->U list->U)` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:(mlstring->U list->U)#(mlstring->U list->U)` o
                check (fun th -> is_forall(concl th) &&
                                 can (find_term (fun t -> try fst(dest_const t) = "models0"
                                                          with _ -> false)) (concl th))) THEN
  ASM_REWRITE_TAC[satisfies0_def; GSYM ALL_MEM] THEN DISCH_TAC THEN
  X_GEN_TAC `v:(mlstring->U)#(mlstring#hol_type->U)` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:hol_term`; `ilist:(hol_term#hol_term)list`] termsem_VSUBST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[is_valuation0_def; is_term_valuation0_def]) THEN
    ASM_REWRITE_TAC[is_valuation0_def; is_term_valuation0_def] THEN
    MAP_EVERY X_GEN_TAC [`x:mlstring`; `ty:hol_type`] THEN DISCH_TAC THEN
    QSPECL_THEN ["ilist"; "SND v"; "termsem0 mem (SND (FST thy)) i v"; "x"; "ty"] MP_TAC
      CSEMAUX_UPDATE_LIST_dest_var THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    CASES_ON `ALOOKUP (MAP (\(s':hol_term,s:hol_term). (s,s')) ilist) (hol_Var x ty)` THEN
    ASM_SIMP_TAC[option_CASE] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP ALOOKUP_MEM) THEN
    REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM] THEN CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq(concl th) &&
                                                         is_var(rhs(concl th))))) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`hol_Var x ty`; `a:hol_term`] o
                  check (fun th -> can (find_term (fun t -> try fst(dest_const t) = "hol_term_ok"
                                                            with _ -> false)) (concl th) &&
                                   is_forall (concl th))) THEN
    ASM_REWRITE_TAC[injectivity "hol_term"] THEN STRIP_TAC THEN
    MATCH_MP_TAC(UNDISCH termsem_typesem_matchable) THEN
    MAP_EVERY EXISTS_TAC [`FST (thy:thy)`;
                          `FST (i:(mlstring->U list->U)#(mlstring->U list->U))`;
                          `FST (v:(mlstring->U)#(mlstring#hol_type->U))`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[models0_def]) THEN
    ASM_REWRITE_TAC[is_valuation0_def; is_term_valuation0_def] THEN
    ASM_MESON_TAC[is_std_interpretation_is_type; WELLTYPED_LEMMA];
    ALL_TAC] THEN
  X_GEN_TAC `t:hol_term` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`h:hol_term list`; `VSUBST ilist`; `t:hol_term`] MEM_term_image) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `y:hol_term` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`t:hol_term`; `ilist:(hol_term#hol_term)list`] termsem_VSUBST) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN(fun th -> REWRITE_TAC[GSYM th])] THEN
  TRANS_TAC EQ_TRANS `termsem0 (mem:U->U->bool) (SND (FST (thy:thy))) i v y` THEN
  CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  MATCH_MP_TAC termsem_aconv THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[VSUBST_WELLTYPED];
    FIRST_X_ASSUM(MP_TAC o MATCH_MP MEM_term_image_imp) THEN STRIP_TAC THEN
    ASM_MESON_TAC[VSUBST_WELLTYPED]]);;
(* HOL4: tyin is a free variable of the statement *)
let INST_TYPE_correct = prove
 (`is_set_theory (mem:U->U->bool) ==>
   !thy h c.
     ALL (type_ok (FST (FST thy))) (MAP FST tyin) /\
     entails0 mem (thy,h) c
     ==> entails0 mem (thy,term_image (INST tyin) h) (INST tyin c)`,
  STRIP_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[entails0_def; ALL] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_MEM]) THEN ASM_REWRITE_TAC[GSYM ALL_MEM] THEN
  SUBGOAL_THEN `!t. MEM t h ==> welltyped t` ASSUME_TAC THENL
   [ASM_MESON_TAC[term_ok_welltyped]; ALL_TAC] THEN
  SUBGOAL_THEN `ALL (type_ok (FST (FST (thy:thy)))) (MAP FST (tyin:(hol_type#hol_type)list))`
    ASSUME_TAC THENL [ASM_REWRITE_TAC[GSYM ALL_MEM]; ALL_TAC] THEN
  SUBGOAL_THEN `!t. t has_type Tyapp (implode "bool") []
                    ==> INST tyin t has_type Tyapp (implode "bool") []` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC INST_HAS_TYPE THEN
    EXISTS_TAC `Tyapp (implode "bool") []` THEN ASM_REWRITE_TAC[TYPE_SUBST_Bool];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC term_ok_INST THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP MEM_term_image_imp) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC term_ok_INST THEN ASM_MESON_TAC[];
    ASM_MESON_TAC[];
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP MEM_term_image_imp) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    MATCH_MP_TAC hypset_ok_term_image THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `i:(mlstring->U list->U)#(mlstring->U list->U)` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:(mlstring->U list->U)#(mlstring->U list->U)` o
                check (fun th -> is_forall(concl th) &&
                                 can (find_term (fun t -> try fst(dest_const t) = "models0"
                                                          with _ -> false)) (concl th))) THEN
  ASM_REWRITE_TAC[satisfies0_def; GSYM ALL_MEM] THEN DISCH_TAC THEN
  X_GEN_TAC `v:(mlstring->U)#(mlstring#hol_type->U)` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`FST (thy:thy)`; `c:hol_term`; `tyin:(hol_type#hol_type)list`;
                 `SND (FST (thy:thy))`] termsem_INST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[is_valuation0_def; is_term_valuation0_def;
                                is_type_valuation0_def]) THEN
    REWRITE_TAC[is_valuation0_def; is_term_valuation0_def; is_type_valuation0_def] THEN
    SUBGOAL_THEN `is_type_assignment0 (mem:U->U->bool) (FST (FST (thy:thy)))
                    (FST (i:(mlstring->U list->U)#(mlstring->U list->U)))` ASSUME_TAC THENL
     [ASM_MESON_TAC[models0_def; is_interpretation0_def]; ALL_TAC] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `x:mlstring` THEN MATCH_MP_TAC(UNDISCH typesem_inhabited) THEN
      EXISTS_TAC `FST (FST (thy:thy))` THEN ASM_REWRITE_TAC[is_type_valuation0_def] THEN
      REWRITE_TAC[TYPE_SUBST_def] THEN
      MP_TAC(ISPECL [`tyin:(hol_type#hol_type)list`; `Tyvar x`; `Tyvar x`] REV_ASSOCD_MEM) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[type_ok_def] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_MEM]) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM] THEN
      ASM_MESON_TAC[FST];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`x:mlstring`; `ty:hol_type`] THEN DISCH_TAC THEN
    CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
    REWRITE_TAC[GSYM typesem_TYPE_SUBST] THEN
    SUBGOAL_THEN `type_ok (FST (FST (thy:thy))) (TYPE_SUBST tyin ty)` ASSUME_TAC THENL
     [MATCH_MP_TAC type_ok_TYPE_SUBST THEN ASM_REWRITE_TAC[]; ASM_MESON_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `t:hol_term` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`h:hol_term list`; `INST tyin`; `t:hol_term`] MEM_term_image) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `y:hol_term` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`FST (thy:thy)`; `t:hol_term`; `tyin:(hol_type#hol_type)list`;
                 `SND (FST (thy:thy))`] termsem_INST) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN(fun th -> REWRITE_TAC[GSYM th])] THEN
  TRANS_TAC EQ_TRANS `termsem0 (mem:U->U->bool) (SND (FST (thy:thy))) i v y` THEN
  CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  MATCH_MP_TAC termsem_aconv THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[INST_WELLTYPED];
    FIRST_X_ASSUM(MP_TAC o MATCH_MP MEM_term_image_imp) THEN STRIP_TAC THEN
    ASM_MESON_TAC[INST_WELLTYPED]]);;
let MK_COMB_correct = prove
 (`is_set_theory (mem:U->U->bool) ==>
   !thy h1 h2 l1 r1 l2 r2.
     entails0 mem (thy,h1) (l1 === r1) /\ entails0 mem (thy,h2) (l2 === r2) /\
     welltyped (hol_Comb l1 l2)
     ==> entails0 mem (thy,term_union h1 h2) (hol_Comb l1 l2 === hol_Comb r1 r2)`,
  STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(UNDISCH binary_inference_rule) THEN
  MAP_EVERY EXISTS_TAC [`l1 === r1`; `l2 === r2`] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `theory_ok (thy:thy) /\ hol_term_ok (FST thy) (l1 === r1) /\
                hol_term_ok (FST thy) (l2 === r2)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[entails0_def; ALL]; ALL_TAC] THEN
  SUBGOAL_THEN `is_std_sig (FST (thy:thy))` ASSUME_TAC THENL
   [ASM_MESON_TAC[theory_ok_sig]; ALL_TAC] THEN
  SUBGOAL_THEN `hol_term_ok (FST (thy:thy)) l1 /\ hol_term_ok (FST thy) r1 /\
                typeof r1 = typeof l1 /\
                hol_term_ok (FST thy) l2 /\ hol_term_ok (FST thy) r2 /\
                typeof r2 = typeof l2`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[term_ok_equation]; ALL_TAC] THEN
  SUBGOAL_THEN `welltyped r1 /\ welltyped r2` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[term_ok_welltyped]; ALL_TAC] THEN
  SUBGOAL_THEN `welltyped (hol_Comb r1 r2) /\
                typeof (hol_Comb r1 r2) = typeof (hol_Comb l1 l2)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `welltyped (hol_Comb l1 l2)` THEN
    ASM_REWRITE_TAC[WELLTYPED_CLAUSES; typeof_def] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `hol_term_ok (FST (thy:thy)) (hol_Comb l1 l2 === hol_Comb r1 r2)`
    ASSUME_TAC THENL
   [ASM_REWRITE_TAC[MATCH_MP term_ok_equation (ASSUME `is_std_sig (FST (thy:thy))`);
                    hol_term_ok_def];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[EQUATION_HAS_TYPE_BOOL] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!s t. hol_term_ok (FST (thy:thy)) (s === t)
          ==> (termsem0 (mem:U->U->bool) (SND (FST thy)) i v (s === t) = setSpec_true mem <=>
               termsem0 mem (SND (FST thy)) i v s = termsem0 mem (SND (FST thy)) i v t)`
   ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`FST (thy:thy)`; `i:(mlstring->U list->U)#(mlstring->U list->U)`;
                   `v:(mlstring->U)#(mlstring#hol_type->U)`; `s:hol_term`; `t:hol_term`;
                   `SND (FST (thy:thy))`] (UNDISCH termsem_equation)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[UNDISCH boolean_eq_true];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th ->
    MP_TAC(MP (SPECL [`l1:hol_term`; `r1:hol_term`] th)
              (ASSUME `hol_term_ok (FST (thy:thy)) (l1 === r1)`)) THEN
    MP_TAC(MP (SPECL [`l2:hol_term`; `r2:hol_term`] th)
              (ASSUME `hol_term_ok (FST (thy:thy)) (l2 === r2)`)) THEN
    MP_TAC(MP (SPECL [`hol_Comb l1 l2`; `hol_Comb r1 r2`] th)
              (ASSUME `hol_term_ok (FST (thy:thy)) (hol_Comb l1 l2 === hol_Comb r1 r2)`))) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[termsem0_def]);;

let REFL_correct = prove
 (`is_set_theory (mem:U->U->bool) ==>
   !thy t. theory_ok thy /\ hol_term_ok (FST thy) t ==> entails0 mem (thy,[]) (t === t)`,
  STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `is_std_sig (FST (thy:thy))` ASSUME_TAC THENL
   [ASM_MESON_TAC[theory_ok_sig]; ALL_TAC] THEN
  SUBGOAL_THEN `welltyped t` ASSUME_TAC THENL [ASM_MESON_TAC[term_ok_welltyped]; ALL_TAC] THEN
  SUBGOAL_THEN `hol_term_ok (FST (thy:thy)) (t === t)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[term_ok_equation]; ALL_TAC] THEN
  ASM_REWRITE_TAC[entails0_def; ALL; EQUATION_HAS_TYPE_BOOL; hypset_ok_def; SORTED_DEF;
                  satisfies0_def] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`FST (thy:thy)`; `i:(mlstring->U list->U)#(mlstring->U list->U)`;
                 `v:(mlstring->U)#(mlstring#hol_type->U)`; `t:hol_term`; `t:hol_term`;
                 `SND (FST (thy:thy))`] (UNDISCH termsem_equation)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[is_structure0_def] THEN RULE_ASSUM_TAC(REWRITE_RULE[models0_def]) THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[boolean_def]]);;

(* The headline: any provable sequent is valid. *)
let proves_sound = prove
 (`is_set_theory (mem:U->U->bool) ==> !thyh c. thyh |- c ==> entails0 mem thyh c`,
  STRIP_TAC THEN MATCH_MP_TAC proves_ind THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[ABS_correct];
    MESON_TAC[ASSUME_correct];
    ASM_MESON_TAC[BETA_correct];
    ASM_MESON_TAC[DEDUCT_ANTISYM_correct];
    ASM_MESON_TAC[EQ_MP_correct];
    ASM_MESON_TAC[INST_correct];
    ASM_MESON_TAC[INST_TYPE_correct];
    ASM_MESON_TAC[MK_COMB_correct];
    ASM_MESON_TAC[REFL_correct];
    SIMP_TAC[entails0_def; theory_ok_def; models0_def; ALL; hypset_ok_def; SORTED_DEF]]);;
