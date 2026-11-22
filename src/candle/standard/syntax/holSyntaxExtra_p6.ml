(* ========================================================================= *)
(* holSyntaxExtra, part 6 (HOL4 holSyntaxExtraScript.sml lines 3036-3400):   *)
(* provable sequents are well formed (proves_term_ok), derived rules of the  *)
(* inference system (addAssum, sym, trans, proveHyp), the system respects    *)
(* alpha-equivalence (proves_ACONV), extension is transitive.  Notes on the *)
(* rendering: holSyntaxExtra_p1.ml.                                          *)
(* - HOL4's proves_theory_ok is hol_proves_theory_ok and sym is hol_sym      *)
(*   (names.tsv).  HOL4's ML values assume (the rule proves_ASSUME) and rws  *)
(*   (a list of EL rewrites) are not bound: the proofs use proves_ASSUME and *)
(*   HOL Light's EL lemmas directly.                                         *)
(* - Local helpers that are not HOL4 theorems are CSYNAUX_P6_.               *)
(* ========================================================================= *)

needs "candle/standard/syntax/holSyntaxExtra_p5.ml";;

prioritize_num();;
type_invention_error := true;;

(* provable terms are ok and of type bool *)

(* HOL4: proves_theory_ok *)
let hol_proves_theory_ok = prove
 (`!thyh c. thyh |- c ==> theory_ok (FST thyh)`,
  MATCH_MP_TAC proves_ind THEN SIMP_TAC[FST]);;

let theory_ok_sig = prove
 (`!thy. theory_ok thy ==> is_std_sig (FST thy)`,
  SIMP_TAC[theory_ok_def]);;

let CSYNAUX_P6_proves_std_sig = prove
 (`!thy h c. (thy,h) |- c ==> is_std_sig (FST thy)`,
  MESON_TAC[hol_proves_theory_ok; theory_ok_sig; FST]);;

let proves_term_ok = prove
 (`!thyh c. thyh |- c
            ==> hypset_ok (SND thyh) /\
                ALL (\p. hol_term_ok (FST (FST thyh)) p /\
                         p has_type Tyapp (implode "bool") [])
                    (CONS c (SND thyh))`,
  let pre_tac =
    REPEAT STRIP_TAC THEN TRY(IMP_RES_TAC CSYNAUX_P6_proves_std_sig) THEN
    TRY(IMP_RES_TAC theory_ok_sig) THEN TRY(IMP_RES_TAC term_ok_welltyped) THEN
    RFS[term_ok_equation; EQUATION_HAS_TYPE_BOOL; hol_term_ok_def;
        WELLTYPED_CLAUSES; typeof_def; hypset_ok_nil; hypset_ok_sing;
        hypset_ok_term_union; hypset_ok_term_remove; hypset_ok_term_image] THEN
    REPEAT CONJ_TAC
  and solve tacs = FIRST (map (fun t -> t THEN NO_TAC) tacs)
  and union_tac =
    MATCH_MP_TAC EVERY_term_union THEN CONJ_TAC THEN
    TRY(MATCH_MP_TAC EVERY_term_remove) THEN ASM_REWRITE_TAC[]
  and image_tac lemmas =
    REWRITE_TAC[GSYM ALL_MEM] THEN X_GEN_TAC `y:hol_term` THEN
    DISCH_THEN(MP_TAC o MATCH_MP MEM_term_image_imp) THEN
    DISCH_THEN(X_CHOOSE_THEN `x:hol_term` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=)
      `ALL:(hol_term->bool)->(hol_term)list->bool`)) (concl th))) THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN DISCH_THEN(MP_TAC o SPEC `x:hol_term`) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC lemmas in
  MATCH_MP_TAC proves_strongind THEN REWRITE_TAC[FST; SND; ALL] THEN
  REPEAT CONJ_TAC THENL
   [pre_tac;
    pre_tac;
    pre_tac;
    pre_tac THEN solve [union_tac; IMP_RES_TAC WELLTYPED_LEMMA THEN ASM_REWRITE_TAC[]];
    pre_tac THEN
    solve [union_tac;
           IMP_RES_TAC WELLTYPED_LEMMA THEN IMP_RES_TAC ACONV_TYPE THEN
           ASM_MESON_TAC[WELLTYPED]];
    pre_tac THEN
    solve [MATCH_MP_TAC term_ok_VSUBST THEN ASM_REWRITE_TAC[];
           MATCH_MP_TAC VSUBST_HAS_TYPE THEN ASM_MESON_TAC[];
           image_tac [term_ok_VSUBST; VSUBST_HAS_TYPE]];
    pre_tac THEN
    solve [MATCH_MP_TAC term_ok_INST THEN ASM_REWRITE_TAC[];
           MATCH_MP_TAC INST_HAS_TYPE THEN
           EXISTS_TAC `Tyapp (implode "bool") []` THEN
           ASM_REWRITE_TAC[TYPE_SUBST_Bool];
           image_tac [term_ok_INST; INST_HAS_TYPE; TYPE_SUBST_Bool]];
    pre_tac THEN solve [union_tac; ASM_MESON_TAC[]];
    pre_tac;
    pre_tac THEN RULE_ASSUM_TAC(REWRITE_RULE[theory_ok_def]) THEN
    ASM_MESON_TAC[]]);;

(* some derived rules *)

let deductAntisym_equation = proves_DEDUCT_ANTISYM;;

let eqMp_equation = REWRITE_RULE[IMP_CONJ] proves_EQ_MP;;

let refl_equation = proves_REFL;;

let appThm_equation = REWRITE_RULE[IMP_CONJ] proves_MK_COMB;;

let addAssum = prove
 (`!thy h c a.
     (thy,h) |- c /\ hol_term_ok (FST thy) a /\
     a has_type Tyapp (implode "bool") []
     ==> (thy,term_union [a] h) |- c`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `theory_ok thy` ASSUME_TAC THENL
   [ASM_MESON_TAC[hol_proves_theory_ok; FST]; ALL_TAC] THEN
  SUBGOAL_THEN `is_std_sig (FST (thy:thy))` ASSUME_TAC THENL
   [ASM_MESON_TAC[theory_ok_sig]; ALL_TAC] THEN
  SUBGOAL_THEN `hol_term_ok (FST (thy:thy)) c /\ c has_type Tyapp (implode "bool") []`
    STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP proves_term_ok) THEN
    REWRITE_TAC[FST; SND; ALL] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(thy,[a]) |- a` ASSUME_TAC THENL
   [MATCH_MP_TAC proves_ASSUME THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(thy,[a]) |- c === c` ASSUME_TAC THENL
   [ASM_CASES_TAC `ACONV (c === c) a` THENL
     [SUBGOAL_THEN `(thy,[]) |- (c === c) === (c === c)` ASSUME_TAC THENL
       [MATCH_MP_TAC refl_equation THEN ASM_SIMP_TAC[term_ok_equation];
        ALL_TAC] THEN
      MP_TAC(SPECL [`[]:(hol_term)list`; `[a]:(hol_term)list`; `c === c`; `a:hol_term`; `c === c`;
                 `thy:thy`] eqMp_equation) THEN
      ASM_REWRITE_TAC[term_union_thm];
      SUBGOAL_THEN `(thy,[]) |- c === c` ASSUME_TAC THENL
       [MATCH_MP_TAC refl_equation THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MP_TAC(SPECL [`a:hol_term`; `c === c`; `[a]:(hol_term)list`; `[]:(hol_term)list`;
                 `thy:thy`] deductAntisym_equation) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `term_remove (c === c) [a] = [a]` SUBST1_TAC THENL
       [ONCE_REWRITE_TAC[term_remove_def] THEN CASE_REWRITE_TAC[] THEN
        REWRITE_TAC[LET_DEF; LET_END_DEF; term_remove_nil] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[ACONV_eq_orda]) THEN
        ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[term_remove_nil; term_union_thm] THEN DISCH_TAC THEN
      MP_TAC(SPECL [`[a]:(hol_term)list`; `[a]:(hol_term)list`; `a:hol_term`; `a:hol_term`;
                 `c === c`; `thy:thy`] eqMp_equation) THEN
      ASM_REWRITE_TAC[ACONV_REFL; term_union_idem]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`[a]:(hol_term)list`; `h:(hol_term)list`; `c:hol_term`; `c:hol_term`;
             `c:hol_term`; `thy:thy`] eqMp_equation) THEN
  ASM_REWRITE_TAC[ACONV_REFL]);;

(* inference system respects alpha-equivalence *)

let proves_concl_ACONV = prove
 (`!thyh c c'. thyh |- c /\ ACONV c c' /\ welltyped c' ==> thyh |- c'`,
  GEN_REWRITE_TAC I [FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`thy:thy`; `h:(hol_term)list`; `c:hol_term`;
                       `c':hol_term`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `theory_ok thy` ASSUME_TAC THENL
   [ASM_MESON_TAC[hol_proves_theory_ok; FST]; ALL_TAC] THEN
  SUBGOAL_THEN `hol_term_ok (FST (thy:thy)) c` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP proves_term_ok) THEN
    REWRITE_TAC[FST; SND; ALL] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(thy,[]) |- c' === c'` ASSUME_TAC THENL
   [MATCH_MP_TAC refl_equation THEN ASM_MESON_TAC[term_ok_aconv]; ALL_TAC] THEN
  MP_TAC(SPECL [`[]:(hol_term)list`; `h:(hol_term)list`; `c':hol_term`; `c:hol_term`;
             `c':hol_term`; `thy:thy`] eqMp_equation) THEN
  ASM_REWRITE_TAC[term_union_thm] THEN ASM_MESON_TAC[ACONV_SYM]);;

let CSYNAUX_P6_hypset_ok_APPEND = prove
 (`!l1 l2. hypset_ok (APPEND l1 l2) <=>
           hypset_ok l1 /\ hypset_ok l2 /\
           (!x y. MEM x l1 ==> MEM y l2 ==> alpha_lt x y)`,
  REWRITE_TAC[hypset_ok_def; MATCH_MP SORTED_APPEND transitive_alpha_lt]);;

let CSYNAUX_P6_ACONV_not_lt = prove
 (`!x y. ACONV x y ==> ~alpha_lt x y /\ ~alpha_lt y x`,
  REWRITE_TAC[alpha_lt_def] THEN MESON_TAC[ACONV_eq_orda; ACONV_SYM;
    distinctness "ordering"]);;

let CSYNAUX_P6_ACONV_head = prove
 (`!x h t. hypset_ok h /\ ALL (alpha_lt x) t /\
           (!z. MEM z h ==> ACONV z x \/ EX (ACONV z) t) /\ EX (ACONV x) h
           ==> ?h0 hr. h = CONS h0 hr /\ ACONV x h0`,
  REPEAT GEN_TAC THEN
  DISJ_CASES_THEN2 SUBST1_TAC
    (X_CHOOSE_THEN `h0:hol_term` (X_CHOOSE_THEN `hr:(hol_term)list` SUBST1_TAC))
    (ISPEC `h:(hol_term)list` list_CASES) THEN
  REWRITE_TAC[EX; CONS_11; MEM; hypset_ok_cons; GSYM ALL_MEM; GSYM EX_MEM] THEN
  STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`h0:hol_term`; `hr:(hol_term)list`] THEN
  REWRITE_TAC[] THEN ASM_CASES_TAC `ACONV x h0` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `?y. ACONV h0 y /\ MEM y t` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[ACONV_SYM]; ALL_TAC] THEN
  SUBGOAL_THEN `?e. ACONV x e /\ MEM e hr` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `alpha_lt x h0` ASSUME_TAC THENL
   [ASM_MESON_TAC[alpha_lt_trans_ACONV; ACONV_SYM]; ALL_TAC] THEN
  SUBGOAL_THEN `alpha_lt x e` ASSUME_TAC THENL
   [ASM_MESON_TAC[REWRITE_RULE[transitive_def] transitive_alpha_lt]; ALL_TAC] THEN
  ASM_MESON_TAC[CSYNAUX_P6_ACONV_not_lt]);;

let proves_ACONV_lemma = prove
 (`!thy c h' h1 h.
     (thy,APPEND h1 h) |- c /\
     hypset_ok (APPEND h1 h') /\
     ALL (\x. EX (ACONV x) h') h /\
     ALL (\x. hol_term_ok (FST thy) x /\ x has_type Tyapp (implode "bool") []) h'
     ==> (thy,APPEND h1 h') |- c`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
   [REWRITE_TAC[EX; ALL] THEN REPEAT GEN_TAC THEN
    STRUCT_CASES_TAC(ISPEC `h:(hol_term)list` list_CASES) THEN
    REWRITE_TAC[ALL] THEN MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:hol_term`; `t:(hol_term)list`] THEN
  DISCH_THEN(LABEL_TAC "IH") THEN
  MAP_EVERY X_GEN_TAC [`h1:(hol_term)list`; `h:(hol_term)list`] THEN
  REWRITE_TAC[ALL; EX] THEN
  DISCH_THEN(fun th ->
    let a1,r = CONJ_PAIR th in let a2,r = CONJ_PAIR r in
    let a3,r = CONJ_PAIR r in let r1,a6 = CONJ_PAIR r in
    let a4,a5 = CONJ_PAIR r1 in
    MAP_EVERY (fun (s,t) -> LABEL_TAC s t)
      ["A1",a1; "A2",a2; "A3",REWRITE_RULE[GSYM ALL_MEM] a3; "A4",a4;
       "A5",a5; "A6",a6]) THEN
  SUBGOAL_THEN `(!u. MEM u h1 ==> alpha_lt u x) /\ ALL (alpha_lt x) t /\ hypset_ok h`
    STRIP_ASSUME_TAC THENL
   [USE_THEN "A2" (MP_TAC o REWRITE_RULE[CSYNAUX_P6_hypset_ok_APPEND; hypset_ok_cons;
                                         MEM]) THEN
    USE_THEN "A1" (MP_TAC o REWRITE_RULE[SND; CSYNAUX_P6_hypset_ok_APPEND] o
                   CONJUNCT1 o MATCH_MP proves_term_ok) THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. MEM z h /\ ~ACONV z x ==> EX (ACONV z) t /\ alpha_lt x z`
    (LABEL_TAC "G2") THENL
   [X_GEN_TAC `z:hol_term` THEN STRIP_TAC THEN
    USE_THEN "A3" (MP_TAC o SPEC `z:hol_term`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM EX_MEM]) THEN
    DISCH_THEN(X_CHOOSE_THEN `y:hol_term` STRIP_ASSUME_TAC) THEN
    ASM_MESON_TAC[alpha_lt_trans_ACONV; ACONV_SYM; ALL_MEM];
    ALL_TAC] THEN
  SUBGOAL_THEN `APPEND (h1:(hol_term)list) (CONS x t) = APPEND (APPEND h1 [x]) t`
    SUBST1_TAC THENL
   [REWRITE_TAC[GSYM APPEND_ASSOC; APPEND]; ALL_TAC] THEN
  USE_THEN "IH" MATCH_MP_TAC THEN
  ASM_CASES_TAC `EX (ACONV x) h` THENL
   [MP_TAC(SPECL [`x:hol_term`; `h:(hol_term)list`; `t:(hol_term)list`]
      CSYNAUX_P6_ACONV_head) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN USE_THEN "A3" ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `h0:hol_term`
      (X_CHOOSE_THEN `hr:(hol_term)list` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `ALL (\z. alpha_lt x z) hr` ASSUME_TAC THENL
     [UNDISCH_TAC `hypset_ok h` THEN ASM_REWRITE_TAC[hypset_ok_cons; GSYM ALL_MEM] THEN
      ASM_MESON_TAC[alpha_lt_trans_ACONV];
      ALL_TAC] THEN
    EXISTS_TAC `hr:(hol_term)list` THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[GSYM APPEND_ASSOC; APPEND] THEN
      SUBGOAL_THEN `APPEND h1 (CONS x hr) = term_union [x] (APPEND h1 h)` SUBST1_TAC THENL
       [ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC term_union_replace THEN
        ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM ALL_MEM] THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC addAssum THEN ASM_REWRITE_TAC[]];
      REWRITE_TAC[GSYM APPEND_ASSOC; APPEND] THEN USE_THEN "A2" ACCEPT_TAC;
      REWRITE_TAC[GSYM ALL_MEM] THEN X_GEN_TAC `z:hol_term` THEN DISCH_TAC THEN
      USE_THEN "G2" (MP_TAC o SPEC `z:hol_term`) THEN ANTS_TAC THENL
       [ASM_REWRITE_TAC[MEM] THEN ASM_MESON_TAC[CSYNAUX_P6_ACONV_not_lt; ALL_MEM];
        SIMP_TAC[]];
      USE_THEN "A6" ACCEPT_TAC];
    SUBGOAL_THEN `!z. MEM z h ==> alpha_lt x z /\ EX (ACONV z) t` ASSUME_TAC THENL
     [X_GEN_TAC `z:hol_term` THEN DISCH_TAC THEN
      USE_THEN "G2" (MP_TAC o SPEC `z:hol_term`) THEN ANTS_TAC THENL
       [ASM_MESON_TAC[ACONV_SYM; EX_MEM]; SIMP_TAC[]];
      ALL_TAC] THEN
    EXISTS_TAC `h:(hol_term)list` THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[GSYM APPEND_ASSOC; APPEND] THEN
      SUBGOAL_THEN `APPEND h1 (CONS x h) = term_union [x] (APPEND h1 h)` SUBST1_TAC THENL
       [CONV_TAC SYM_CONV THEN MATCH_MP_TAC term_union_insert THEN
        REWRITE_TAC[GSYM ALL_MEM] THEN ASM_MESON_TAC[];
        MATCH_MP_TAC addAssum THEN ASM_REWRITE_TAC[]];
      REWRITE_TAC[GSYM APPEND_ASSOC; APPEND] THEN USE_THEN "A2" ACCEPT_TAC;
      REWRITE_TAC[GSYM ALL_MEM] THEN ASM_MESON_TAC[];
      USE_THEN "A6" ACCEPT_TAC]]);;

let proves_ACONV = prove
 (`!thy h' c' h c.
     (thy,h) |- c /\ welltyped c' /\ ACONV c c' /\
     hypset_ok h' /\
     ALL (\x. EX (ACONV x) h') h /\
     ALL (\x. hol_term_ok (FST thy) x /\ x has_type Tyapp (implode "bool") []) h'
     ==> (thy,h') |- c'`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC proves_concl_ACONV THEN
  EXISTS_TAC `c:hol_term` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`thy:thy`; `c:hol_term`; `h':(hol_term)list`;
                `[]:(hol_term)list`; `h:(hol_term)list`] proves_ACONV_lemma) THEN
  ASM_REWRITE_TAC[APPEND]);;

(* more derived rules *)

let CSYNAUX_P6_proves_welltyped = prove
 (`!thyh c. thyh |- c ==> welltyped c`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP proves_term_ok) THEN
  REWRITE_TAC[ALL] THEN MESON_TAC[term_ok_welltyped]);;

let CSYNAUX_P6_Equal_welltyped = prove
 (`!ty p q.
     welltyped (hol_Comb (hol_Comb (hol_Const (implode "=")
       (Tyapp (implode "fun") [ty; Tyapp (implode "fun")
          [ty; Tyapp (implode "bool") []]])) p) q)
     ==> ty = typeof p /\ typeof q = typeof p /\ welltyped p /\ welltyped q`,
  REWRITE_TAC[WELLTYPED_CLAUSES; typeof_def; codomain_def; injectivity "hol_type";
              CONS_11] THEN MESON_TAC[]);;

let sym_equation = prove
 (`!thyh p q. thyh |- p === q ==> thyh |- q === p`,
  GEN_REWRITE_TAC I [FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`thy:thy`; `h:(hol_term)list`; `p:hol_term`; `q:hol_term`] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `theory_ok thy` ASSUME_TAC THENL
   [ASM_MESON_TAC[hol_proves_theory_ok; FST]; ALL_TAC] THEN
  SUBGOAL_THEN `is_std_sig (FST (thy:thy))` ASSUME_TAC THENL
   [ASM_MESON_TAC[theory_ok_sig]; ALL_TAC] THEN
  SUBGOAL_THEN `hol_term_ok (FST (thy:thy)) p /\ hol_term_ok (FST thy) q /\
                typeof q = typeof p /\ welltyped p /\ welltyped q`
    STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP proves_term_ok) THEN
    REWRITE_TAC[FST; SND; ALL; EQUATION_HAS_TYPE_BOOL] THEN
    ASM_MESON_TAC[term_ok_equation];
    ALL_TAC] THEN
  SUBGOAL_THEN `(thy,[]) |- p === p` ASSUME_TAC THENL
   [MATCH_MP_TAC refl_equation THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(thy,[]) |- hol_Const (implode "=") (Tyapp (implode "fun") [typeof p;
                  Tyapp (implode "fun") [typeof p; Tyapp (implode "bool") []]]) ===
                hol_Const (implode "=") (Tyapp (implode "fun") [typeof p;
                  Tyapp (implode "fun") [typeof p; Tyapp (implode "bool") []]])`
    ASSUME_TAC THENL
   [MATCH_MP_TAC refl_equation THEN ASM_SIMP_TAC[term_ok_clauses] THEN
    ASM_MESON_TAC[term_ok_type_ok];
    ALL_TAC] THEN
  MP_TAC(SPECL [`[]:(hol_term)list`; `h:(hol_term)list`;
    `hol_Const (implode "=") (Tyapp (implode "fun") [typeof p;
       Tyapp (implode "fun") [typeof p; Tyapp (implode "bool") []]])`;
    `p:hol_term`;
    `hol_Const (implode "=") (Tyapp (implode "fun") [typeof p;
       Tyapp (implode "fun") [typeof p; Tyapp (implode "bool") []]])`;
    `q:hol_term`; `thy:thy`] appThm_equation) THEN
  ASM_REWRITE_TAC[term_union_thm] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[WELLTYPED_CLAUSES; typeof_def] THEN MESON_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`h:(hol_term)list`; `[]:(hol_term)list`;
    `hol_Comb (hol_Const (implode "=") (Tyapp (implode "fun") [typeof p;
       Tyapp (implode "fun") [typeof p; Tyapp (implode "bool") []]])) p`;
    `p:hol_term`;
    `hol_Comb (hol_Const (implode "=") (Tyapp (implode "fun") [typeof p;
       Tyapp (implode "fun") [typeof p; Tyapp (implode "bool") []]])) q`;
    `p:hol_term`; `thy:thy`] appThm_equation) THEN
  ASM_REWRITE_TAC[term_union_thm] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[WELLTYPED_CLAUSES; typeof_def; codomain_def] THEN MESON_TAC[];
    DISCH_TAC] THEN
  SUBGOAL_THEN `(thy,h) |- (p === p) === (q === p)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> free_in `q:hol_term` (concl th) &&
                                            is_comb (concl th))) THEN
    ASM_REWRITE_TAC[equation_def];
    ALL_TAC] THEN
  MP_TAC(SPECL [`h:(hol_term)list`; `[]:(hol_term)list`; `p === p`; `p === p`; `q === p`;
             `thy:thy`] eqMp_equation) THEN
  ASM_REWRITE_TAC[term_union_thm; ACONV_REFL]);;

(* HOL4: sym *)
let hol_sym = prove
 (`!thyh p q ty.
     thyh |- hol_Comb (hol_Comb (hol_Const (implode "=")
               (Tyapp (implode "fun") [ty; Tyapp (implode "fun")
                  [ty; Tyapp (implode "bool") []]])) p) q
     ==> thyh |- hol_Comb (hol_Comb (hol_Const (implode "=")
                  (Tyapp (implode "fun") [ty; Tyapp (implode "fun")
                     [ty; Tyapp (implode "bool") []]])) q) p`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CSYNAUX_P6_Equal_welltyped o
              MATCH_MP CSYNAUX_P6_proves_welltyped) THEN
  STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl)) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP sym_equation o REWRITE_RULE[GSYM equation_def]) THEN
  ASM_REWRITE_TAC[equation_def]);;

let trans_equation = prove
 (`!thy h1 h2 t1 t2a t2b t3.
     (thy,h2) |- t2b === t3
     ==> (thy,h1) |- t1 === t2a
     ==> ACONV t2a t2b
     ==> (thy,term_union h1 h2) |- t1 === t3`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `theory_ok thy` ASSUME_TAC THENL
   [ASM_MESON_TAC[hol_proves_theory_ok; FST]; ALL_TAC] THEN
  SUBGOAL_THEN `is_std_sig (FST (thy:thy))` ASSUME_TAC THENL
   [ASM_MESON_TAC[theory_ok_sig]; ALL_TAC] THEN
  SUBGOAL_THEN `hol_term_ok (FST (thy:thy)) t3 /\ welltyped t2a /\ welltyped t3 /\
                typeof t2a = typeof t3`
    STRIP_ASSUME_TAC THENL
   [MP_TAC(MATCH_MP proves_term_ok
      (ASSUME `(thy:thy,h2:(hol_term)list) |- t2b === t3`)) THEN
    MP_TAC(MATCH_MP proves_term_ok
      (ASSUME `(thy:thy,h1:(hol_term)list) |- t1 === t2a`)) THEN
    REWRITE_TAC[FST; SND; ALL; EQUATION_HAS_TYPE_BOOL] THEN
    ASM_MESON_TAC[term_ok_equation; ACONV_TYPE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(thy,[]) |- hol_Comb (hol_Const (implode "=") (Tyapp (implode "fun") [typeof t3;
                  Tyapp (implode "fun") [typeof t3; Tyapp (implode "bool") []]])) t3 ===
                hol_Comb (hol_Const (implode "=") (Tyapp (implode "fun") [typeof t3;
                  Tyapp (implode "fun") [typeof t3; Tyapp (implode "bool") []]])) t3`
    ASSUME_TAC THENL
   [MATCH_MP_TAC refl_equation THEN ASM_SIMP_TAC[term_ok_clauses] THEN
    ASM_REWRITE_TAC[WELLTYPED_CLAUSES; typeof_def] THEN
    ASM_MESON_TAC[term_ok_type_ok];
    ALL_TAC] THEN
  SUBGOAL_THEN `(thy,h1) |- t2a === t1` ASSUME_TAC THENL
   [MATCH_MP_TAC sym_equation THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(thy,h2) |- t3 === t2b` ASSUME_TAC THENL
   [MATCH_MP_TAC sym_equation THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`[]:(hol_term)list`; `h1:(hol_term)list`;
    `hol_Comb (hol_Const (implode "=") (Tyapp (implode "fun") [typeof t3;
       Tyapp (implode "fun") [typeof t3; Tyapp (implode "bool") []]])) t3`;
    `t2a:hol_term`;
    `hol_Comb (hol_Const (implode "=") (Tyapp (implode "fun") [typeof t3;
       Tyapp (implode "fun") [typeof t3; Tyapp (implode "bool") []]])) t3`;
    `t1:hol_term`; `thy:thy`] appThm_equation) THEN
  ASM_REWRITE_TAC[term_union_thm] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[WELLTYPED_CLAUSES; typeof_def; codomain_def] THEN MESON_TAC[];
    DISCH_TAC] THEN
  SUBGOAL_THEN `(thy,h1) |- (t3 === t2a) === (t3 === t1)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> free_in `t1:hol_term` (concl th) &&
                                            free_in `t3:hol_term` (concl th))) THEN
    REWRITE_TAC[equation_def];
    ALL_TAC] THEN
  MP_TAC(SPECL [`h1:(hol_term)list`; `h2:(hol_term)list`; `t3 === t2a`; `t3 === t2b`; `t3 === t1`;
             `thy:thy`] eqMp_equation) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REWRITE_TAC[ACONV_def; equation_def; RACONV] THEN
    REWRITE_TAC[GSYM ACONV_def; ACONV_REFL] THEN ASM_REWRITE_TAC[];
    DISCH_THEN(ACCEPT_TAC o MATCH_MP sym_equation)]);;

let trans = prove
 (`!thy h1 h2 t1 t2a t2b t3 ty.
     (thy,h2) |- hol_Comb (hol_Comb (hol_Const (implode "=")
                   (Tyapp (implode "fun") [ty; Tyapp (implode "fun")
                      [ty; Tyapp (implode "bool") []]])) t2b) t3
     ==> (thy,h1) |- hol_Comb (hol_Comb (hol_Const (implode "=")
                       (Tyapp (implode "fun") [ty; Tyapp (implode "fun")
                          [ty; Tyapp (implode "bool") []]])) t1) t2a
     ==> ACONV t2a t2b
     ==> (thy,term_union h1 h2) |- hol_Comb (hol_Comb (hol_Const (implode "=")
                       (Tyapp (implode "fun") [ty; Tyapp (implode "fun")
                          [ty; Tyapp (implode "bool") []]])) t1) t3`,
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  IMP_RES_TAC CSYNAUX_P6_proves_welltyped THEN
  IMP_RES_TAC CSYNAUX_P6_Equal_welltyped THEN
  SUBGOAL_THEN `typeof t2b = typeof t1` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `ty:hol_type = typeof t1`)) THEN
  MP_TAC(SPECL [`thy:thy`; `h1:(hol_term)list`; `h2:(hol_term)list`; `t1:hol_term`;
                `t2a:hol_term`; `t2b:hol_term`; `t3:hol_term`] trans_equation) THEN
  REWRITE_TAC[equation_def; ASSUME `typeof t2b = typeof t1`] THEN
  ASM_MESON_TAC[]);;

let proveHyp = prove
 (`!thy h1 c1 h2 c2.
     (thy,h1) |- c1 /\ (thy,h2) |- c2
     ==> (thy,term_union h2 (term_remove c2 h1)) |- c1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(MATCH_MP proves_term_ok (ASSUME `(thy:thy,h1:(hol_term)list) |- c1`)) THEN
  MP_TAC(MATCH_MP proves_term_ok (ASSUME `(thy:thy,h2:(hol_term)list) |- c2`)) THEN
  REWRITE_TAC[FST; SND; ALL] THEN STRIP_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c2:hol_term`; `c1:hol_term`; `h2:(hol_term)list`; `h1:(hol_term)list`;
             `thy:thy`] deductAntisym_equation) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`term_union (term_remove c1 h2) (term_remove c2 h1)`; `h2:(hol_term)list`;
             `c2:hol_term`; `c2:hol_term`; `c1:hol_term`; `thy:thy`]
    eqMp_equation) THEN
  ASM_REWRITE_TAC[ACONV_REFL] THEN DISCH_TAC THEN
  MATCH_MP_TAC proves_ACONV THEN
  EXISTS_TAC `term_union (term_union (term_remove c1 h2) (term_remove c2 h1)) h2` THEN
  EXISTS_TAC `c1:hol_term` THEN ASM_REWRITE_TAC[ACONV_REFL] THEN
  SUBGOAL_THEN `hypset_ok (term_remove c2 h1)` ASSUME_TAC THENL
   [ASM_MESON_TAC[hypset_ok_term_remove]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[term_ok_welltyped];
    MATCH_MP_TAC hypset_ok_term_union THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[GSYM ALL_MEM; GSYM EX_MEM] THEN X_GEN_TAC `y:hol_term` THEN
    DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP MEM_term_union_imp) THENL
     [FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MEM_term_union_imp) THEN
      IMP_RES_TAC MEM_term_remove_imp;
      ALL_TAC] THEN
    ASM_MESON_TAC[MEM_term_union; ACONV_SYM];
    MATCH_MP_TAC EVERY_term_union THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC EVERY_term_remove THEN ASM_REWRITE_TAC[]]);;

(* extension is transitive *)

let extends_trans = prove
 (`!c1 c2 c3. c1 extends c2 /\ c2 extends c3 ==> c1 extends c3`,
  REWRITE_TAC[extends_def] THEN MESON_TAC[RTC_TRANS]);;
