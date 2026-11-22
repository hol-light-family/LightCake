(* ========================================================================= *)
(* holSyntaxExtra, part 8 of 8: HOL4 candle/standard/syntax/                 *)
(* holSyntaxExtraScript.sml lines 3908-4164 (CakeML v3479): the types        *)
(* occurring in a term, and a type matching algorithm (tymatch,              *)
(* arities_match, match_type).  Notes on the rendering: the header of        *)
(* holSyntaxExtra_p1.ml.  Local helpers that are not HOL4 theorems are       *)
(* CSYNAUX_P8_.                                                              *)
(* ========================================================================= *)

needs "candle/standard/syntax/holSyntaxExtra_p7.ml";;

prioritize_num();;
type_invention_error := true;;

(* types occurring in a term *)

let types_in_def = cake_def
  `(types_in (hol_Var x ty) = {ty}) /\
   (types_in (hol_Const c ty) = {ty}) /\
   (types_in (hol_Comb t1 t2) = types_in t1 UNION types_in t2) /\
   (types_in (hol_Abs v t) = types_in v UNION types_in t)`;;
let _ = cake_add_simps [types_in_def];;

let type_ok_types_in = prove
 (`!sig. is_std_sig sig
         ==> !tm ty. hol_term_ok sig tm /\ ty IN types_in tm ==> type_ok (FST sig) ty`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC hol_term_INDUCT THEN
  REWRITE_TAC[types_in_def; IN_SING; IN_UNION; hol_term_ok_def] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[types_in_def; IN_SING]) THEN ASM_MESON_TAC[]);;

let VFREE_IN_types_in = prove
 (`!t2 t1. VFREE_IN t1 t2 ==> typeof t1 IN types_in t2`,
  MATCH_MP_TAC hol_term_INDUCT THEN
  REWRITE_TAC[VFREE_IN_def; types_in_def; IN_SING; IN_UNION] THEN
  REPEAT STRIP_TAC THEN
  TRY(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (is_eq o concl))) THEN
  ASM_SIMP_TAC[typeof_def]);;

(* HOL4: Var_subterm_types_in [local] *)
let hol_Var_subterm_types_in = prove
 (`!t x ty. RTC subterm1 (hol_Var x ty) t ==> ty IN types_in t`,
  MATCH_MP_TAC hol_term_INDUCT THEN
  REWRITE_TAC[subterm_Var; subterm_Const; subterm_Comb; subterm_Abs; types_in_def;
              IN_SING; IN_UNION; injectivity "hol_term"; distinctness "hol_term"] THEN
  MESON_TAC[]);;

(* HOL4: Const_subterm_types_in [local] *)
let hol_Const_subterm_types_in = prove
 (`!t x ty. RTC subterm1 (hol_Const x ty) t ==> ty IN types_in t`,
  MATCH_MP_TAC hol_term_INDUCT THEN
  REWRITE_TAC[subterm_Var; subterm_Const; subterm_Comb; subterm_Abs; types_in_def;
              IN_SING; IN_UNION; injectivity "hol_term"; distinctness "hol_term"] THEN
  MESON_TAC[]);;

let subterm_typeof_types_in = prove
 (`!t1 t2 name args.
     RTC subtype1 (Tyapp name args) (typeof t1) /\ RTC subterm1 t1 t2 /\
     welltyped t2 /\ ~(name = implode "fun")
     ==> ?ty2. RTC subtype1 (Tyapp name args) ty2 /\ ty2 IN types_in t2`,
  MATCH_MP_TAC hol_term_INDUCT THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[typeof_def] THEN MESON_TAC[hol_Var_subterm_types_in];
    REWRITE_TAC[typeof_def] THEN MESON_TAC[hol_Const_subterm_types_in];
    MAP_EVERY X_GEN_TAC [`s:hol_term`; `t:hol_term`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)) THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `welltyped (hol_Comb s t)` MP_TAC THENL
     [ASM_MESON_TAC[subterm_welltyped]; ALL_TAC] THEN
    REWRITE_TAC[WELLTYPED_CLAUSES] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC RTC_TRANS_L THEN EXISTS_TAC `rty:hol_type` THEN
      UNDISCH_TAC `RTC subtype1 (Tyapp name args) (typeof (hol_Comb s t))` THEN
      ASM_REWRITE_TAC[typeof_def; codomain_def] THEN DISCH_TAC THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC subtype1_rules THEN REWRITE_TAC[MEM];
      MATCH_MP_TAC RTC_TRANS_R THEN EXISTS_TAC `hol_Comb s t` THEN
      ASM_REWRITE_TAC[subterm1_rules]];
    MAP_EVERY X_GEN_TAC [`v:hol_term`; `t:hol_term`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ihv") (LABEL_TAC "iht")) THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `welltyped (hol_Abs v t)` MP_TAC THENL
     [ASM_MESON_TAC[subterm_welltyped]; ALL_TAC] THEN
    REWRITE_TAC[WELLTYPED_CLAUSES] THEN STRIP_TAC THEN
    UNDISCH_TAC `RTC subtype1 (Tyapp name args) (typeof (hol_Abs v t))` THEN
    ASM_REWRITE_TAC[typeof_def; subtype_Tyapp; injectivity "hol_type"; MEM] THEN
    STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THENL
     [USE_THEN "ihv" MATCH_MP_TAC THEN ASM_REWRITE_TAC[typeof_def] THEN
      MATCH_MP_TAC RTC_TRANS_R THEN EXISTS_TAC `hol_Abs v t` THEN
      ASM_REWRITE_TAC[subterm1_rules];
      USE_THEN "iht" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC RTC_TRANS_R THEN EXISTS_TAC `hol_Abs v t` THEN
      ASM_REWRITE_TAC[subterm1_rules]]]);;

(* termination of tymatch and arities_match: the size of the first list   *)
(* (both shapes of termination condition: R a' a and !y. R y a' ==> R y a) *)
let CSYNAUX_P8_TERM_TAC =
  let sz = [list_size_def; type1_size_append; type_size_def "hol_type"] @
           size_aux_eqs "hol_type" in
  REWRITE_TAC[measure_THM] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  REPEAT STRIP_TAC THEN RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV GEN_BETA_CONV)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE sz) THEN ASM_REWRITE_TAC sz THEN ASM_ARITH_TAC;;

(* a type matching algorithm, based on the implementation in HOL4 *)

let tymatch_def = cake_def_wf
  `measure (\(ps:hol_type list,obs:hol_type list,
              sids:(hol_type#hol_type)list#mlstring list). list_size hol_type_size ps)`
  CSYNAUX_P8_TERM_TAC
  `(tymatch [] [] sids = SOME sids) /\
   (tymatch [] _ _ = NONE) /\
   (tymatch _ [] _ = NONE) /\
   (tymatch (CONS (Tyvar name) ps) (CONS ty obs) sids =
      let (s,ids) = sids in
      let v = REV_ASSOCD (Tyvar name) s (Tyvar name) in
      match (if v = Tyvar name then
               if MEM name ids then SOME v else NONE
             else SOME v) with
        NONE -> if v = ty then tymatch ps obs (s,CONS name ids)
                else tymatch ps obs (CONS (ty,v) s,ids)
      | SOME ty1 -> if ty1 = ty then tymatch ps obs sids else NONE) /\
   (tymatch (CONS (Tyapp c1 a1) ps) (CONS (Tyapp c2 a2) obs) sids =
      if c1 = c2 then tymatch (APPEND a1 ps) (APPEND a2 obs) sids else NONE) /\
   (tymatch _ _ _ = NONE)`;;

let tymatch_ind = cake_ind "tymatch";;

let arities_match_def = cake_def_wf
  `measure (\(l1:hol_type list,l2:hol_type list). list_size hol_type_size l1)`
  CSYNAUX_P8_TERM_TAC
  `(arities_match [] [] <=> T) /\
   (arities_match [] _ <=> F) /\
   (arities_match _ [] <=> F) /\
   (arities_match (CONS (Tyapp c1 a1) xs) (CONS (Tyapp c2 a2) ys) <=>
      (c1 = c2 ==> arities_match a1 a2) /\ arities_match xs ys) /\
   (arities_match (CONS _ xs) (CONS _ ys) <=> arities_match xs ys)`;;

let arities_match_ind = cake_ind "arities_match";;

let arities_match_length = prove
 (`!l1 l2. arities_match l1 l2 ==> LENGTH l1 = LENGTH l2`,
  MATCH_MP_TAC arities_match_ind THEN
  REWRITE_TAC[arities_match_def; LENGTH; SUC_INJ] THEN MESON_TAC[]);;

let arities_match_nil = prove
 (`(arities_match [] ls <=> ls = []) /\
   (arities_match ls [] <=> ls = [])`,
  STRUCT_CASES_TAC(ISPEC `ls:hol_type list` list_CASES) THEN
  REWRITE_TAC[arities_match_def; NOT_CONS_NIL]);;
let _ = cake_add_simps [arities_match_nil];;

let arities_match_Tyvar = prove
 (`arities_match (CONS (Tyvar v) ps) (CONS ty obs) <=> arities_match ps obs`,
  REWRITE_TAC[arities_match_def]);;
let _ = cake_add_simps [arities_match_Tyvar];;

let arities_match_append = prove
 (`!l1 l2 l3 l4.
     arities_match l1 l2 /\ arities_match l3 l4
     ==> arities_match (APPEND l1 l3) (APPEND l2 l4)`,
  MATCH_MP_TAC arities_match_ind THEN REWRITE_TAC[arities_match_def; APPEND] THEN
  MESON_TAC[]);;

let CSYNAUX_P8_REV_ASSOCD_APPEND = prove
 (`!(s1:(A#B)list) s x d.
     ~MEM x (MAP SND s1) ==> REV_ASSOCD x (APPEND s1 s) d = REV_ASSOCD x s d`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND; MAP; MEM] THEN
  PAIR_CASES_ON `h:A#B` THEN REWRITE_TAC[REV_ASSOCD; SND; DE_MORGAN_THM] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[]);;

(* a type variable mapped to itself is not a second component, when no pair *)
(* of the substitution maps a type variable to itself                         *)
let CSYNAUX_P8_REV_ASSOCD_Tyvar = prove
 (`!s name.
     (!n. ~MEM (Tyvar n,Tyvar n) s) /\
     REV_ASSOCD (Tyvar name) s (Tyvar name) = Tyvar name
     ==> ~MEM (Tyvar name) (MAP SND s)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; MEM] THEN
  PAIR_CASES_ON `h:hol_type#hol_type` THEN REWRITE_TAC[REV_ASSOCD; SND; MEM] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN MESON_TAC[];
    REWRITE_TAC[DE_MORGAN_THM] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]]);;

let CSYNAUX_P8_REV_ASSOCD_ids = prove
 (`!s' ids' name.
     DISJOINT (set_of_list (MAP SND s')) (set_of_list (MAP Tyvar ids')) /\
     MEM name ids'
     ==> REV_ASSOCD (Tyvar name) s' (Tyvar name) = Tyvar name`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CSYNAUX_P4_REV_ASSOCD_NOT_MEM THEN
  UNDISCH_TAC `DISJOINT (set_of_list (MAP SND (s':(hol_type#hol_type)list)))
                        (set_of_list (MAP Tyvar ids'))` THEN
  REWRITE_TAC[IN_DISJOINT; IN_SET_OF_LIST; MEM_MAP] THEN ASM_MESON_TAC[]);;

let CSYNAUX_P8_REV_ASSOCD_APPEND_DISTINCT = prove
 (`!(s1:(A#B)list) s x d.
     ALL_DISTINCT (MAP SND (APPEND s1 s)) /\ MEM x (MAP SND s)
     ==> REV_ASSOCD x (APPEND s1 s) d = REV_ASSOCD x s d`,
  REWRITE_TAC[MAP_APPEND; ALL_DISTINCT_APPEND] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC CSYNAUX_P8_REV_ASSOCD_APPEND THEN ASM_MESON_TAC[]);;

let tymatch_SOME = prove
 (`!ps obs sids s' ids'.
     arities_match ps obs /\
     DISJOINT (set_of_list (MAP SND (FST sids)))
              (set_of_list (MAP Tyvar (SND sids))) /\
     (!name. ~MEM (Tyvar name,Tyvar name) (FST sids)) /\
     ALL_DISTINCT (MAP SND (FST sids)) /\
     tymatch ps obs sids = SOME (s',ids')
     ==> ?s1 ids1.
           s' = APPEND s1 (FST sids) /\ ids' = APPEND ids1 (SND sids) /\
           DISJOINT (set_of_list (MAP SND s')) (set_of_list (MAP Tyvar ids')) /\
           (!name. ~MEM (Tyvar name,Tyvar name) s') /\
           ALL_DISTINCT (MAP SND s') /\
           MAP (TYPE_SUBST s') ps = obs`,
  MATCH_MP_TAC tymatch_ind THEN
  REWRITE_TAC[tymatch_def; distinctness "option"; injectivity "option"] THEN
  REPEAT CONJ_TAC THENL
   [(* [] [] *)
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MAP_EVERY EXISTS_TAC [`[]:(hol_type#hol_type)list`; `[]:mlstring list`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[FST; SND]) THEN ASM_REWRITE_TAC[APPEND; MAP; FST; SND];
    (* a type variable against a type *)
    MAP_EVERY X_GEN_TAC [`name:mlstring`; `ps:hol_type list`; `ty:hol_type`;
                         `obs:hol_type list`; `sids:(hol_type#hol_type)list#mlstring list`] THEN
    PAIR_CASES_ON `sids:(hol_type#hol_type)list#mlstring list` THEN
    REWRITE_TAC[PAIR_EQ; FST; SND; arities_match_Tyvar] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (CONJUNCTS_THEN2 (LABEL_TAC "ih2")
      (LABEL_TAC "ih3"))) THEN
    MAP_EVERY X_GEN_TAC [`s':(hol_type#hol_type)list`; `ids':mlstring list`] THEN
    SIMP[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN
    POP_ASSUM MP_TAC THEN
    REMOVE_THEN "ih1" (MP_TAC o REWRITE_RULE[] o SPECL
      [`sids1:mlstring list`; `sids0:(hol_type#hol_type)list`]) THEN
    REMOVE_THEN "ih2" (MP_TAC o REWRITE_RULE[] o SPECL
      [`sids0:(hol_type#hol_type)list`; `sids1:mlstring list`]) THEN
    REMOVE_THEN "ih3" (MP_TAC o REWRITE_RULE[] o SPECL
      [`sids0:(hol_type#hol_type)list`; `sids1:mlstring list`]) THEN
    ABBREV_TAC `v = REV_ASSOCD (Tyvar name) sids0 (Tyvar name)` THEN
    ASM_CASES_TAC `v = Tyvar name` THEN ASM_REWRITE_TAC[] THENL
     [ASM_CASES_TAC `MEM (name:mlstring) sids1` THEN ASM_REWRITE_TAC[] THEN
      CASE_REWRITE_TAC[] THEN REWRITE_TAC[injectivity "option"];
      CASE_REWRITE_TAC[] THEN REWRITE_TAC[injectivity "option"]] THENL
     [(* the variable is already fixed: ty is the variable itself *)
      DISCH_THEN(LABEL_TAC "ih") THEN COND_CASES_TAC THEN
      REWRITE_TAC[distinctness "option"] THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN DISCH_TAC THEN
      REMOVE_THEN "ih" (MP_TAC o SPECL [`s':(hol_type#hol_type)list`; `ids':mlstring list`] o
                        REWRITE_RULE[]) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MAP_EVERY EXISTS_TAC [`s1:(hol_type#hol_type)list`; `ids1:mlstring list`] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CSYNAUX_P8_REV_ASSOCD_ids THEN
      EXISTS_TAC `APPEND ids1 sids1:mlstring list` THEN
      ASM_MESON_TAC[MEM_APPEND];
      (* a new variable: fixed (ty is the variable) or bound to ty *)
      DISCH_THEN(LABEL_TAC "ih3") THEN DISCH_THEN(LABEL_TAC "ih2") THEN
      SUBGOAL_THEN `~MEM (Tyvar name) (MAP SND (sids0:(hol_type#hol_type)list))`
        ASSUME_TAC THENL
       [MATCH_MP_TAC CSYNAUX_P8_REV_ASSOCD_Tyvar THEN ASM_MESON_TAC[]; ALL_TAC] THEN
      COND_CASES_TAC THENL
       [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN DISCH_TAC THEN
        REMOVE_THEN "ih3" (MP_TAC o SPECL [`s':(hol_type#hol_type)list`;
                                           `ids':mlstring list`] o REWRITE_RULE[]) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[] THEN
          UNDISCH_TAC `DISJOINT (set_of_list (MAP SND (sids0:(hol_type#hol_type)list)))
                                (set_of_list (MAP Tyvar sids1))` THEN
          UNDISCH_TAC `~MEM (Tyvar name) (MAP SND (sids0:(hol_type#hol_type)list))` THEN
          REWRITE_TAC[IN_DISJOINT; IN_SET_OF_LIST; MAP; MEM] THEN MESON_TAC[];
          ALL_TAC] THEN
        STRIP_TAC THEN
        MAP_EVERY EXISTS_TAC [`s1:(hol_type#hol_type)list`; `APPEND ids1 [name:mlstring]`] THEN
        ASM_REWRITE_TAC[GSYM APPEND_ASSOC; APPEND] THEN
        MATCH_MP_TAC CSYNAUX_P8_REV_ASSOCD_ids THEN EXISTS_TAC `ids':mlstring list` THEN
        CONJ_TAC THENL
         [UNDISCH_TAC `DISJOINT (set_of_list (MAP SND (s':(hol_type#hol_type)list)))
                                (set_of_list (MAP Tyvar ids'))` THEN ASM_REWRITE_TAC[];
          ASM_REWRITE_TAC[MEM_APPEND; MEM]];
        DISCH_TAC THEN
        REMOVE_THEN "ih2" (MP_TAC o SPECL [`s':(hol_type#hol_type)list`;
                                           `ids':mlstring list`] o
          (fun th -> MP th (ASSUME `~(Tyvar name = ty)`))) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[MAP; ALL_DISTINCT; MEM; PAIR_EQ] THEN CONJ_TAC THENL
           [ASM_REWRITE_TAC[set_of_list; DISJOINT_INSERT; IN_SET_OF_LIST; MEM_MAP;
                            injectivity "hol_type"] THEN ASM_MESON_TAC[];
            ASM_MESON_TAC[]];
          ALL_TAC] THEN
        STRIP_TAC THEN
        MAP_EVERY EXISTS_TAC [`APPEND s1 [ty:hol_type,Tyvar name]`; `ids1:mlstring list`] THEN
        ASM_REWRITE_TAC[GSYM APPEND_ASSOC; APPEND] THEN
        MP_TAC(ISPECL [`s1:(hol_type#hol_type)list`; `CONS (ty:hol_type,Tyvar name) sids0`;
                       `Tyvar name`; `Tyvar name`] CSYNAUX_P8_REV_ASSOCD_APPEND_DISTINCT) THEN
        ANTS_TAC THENL
         [CONJ_TAC THENL
           [UNDISCH_TAC `ALL_DISTINCT (MAP SND (s':(hol_type#hol_type)list))` THEN
            ASM_REWRITE_TAC[];
            REWRITE_TAC[MAP; MEM]];
          DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REV_ASSOCD]]];
      (* the variable has a binding in the substitution *)
      DISCH_THEN(LABEL_TAC "ih") THEN COND_CASES_TAC THEN
      REWRITE_TAC[distinctness "option"] THEN DISCH_TAC THEN
      REMOVE_THEN "ih" (MP_TAC o SPECL [`s':(hol_type#hol_type)list`; `ids':mlstring list`] o
        (fun th -> MP th (ASSUME `v:hol_type = ty`))) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MAP_EVERY EXISTS_TAC [`s1:(hol_type#hol_type)list`; `ids1:mlstring list`] THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`s1:(hol_type#hol_type)list`; `sids0:(hol_type#hol_type)list`;
                     `Tyvar name`; `Tyvar name`] CSYNAUX_P8_REV_ASSOCD_APPEND_DISTINCT) THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL
         [UNDISCH_TAC `ALL_DISTINCT (MAP SND (s':(hol_type#hol_type)list))` THEN
          ASM_REWRITE_TAC[];
          ASM_MESON_TAC[CSYNAUX_P4_REV_ASSOCD_NOT_MEM]];
        DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]]];
    (* two type applications *)
    REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "ih") THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[arities_match_def] THEN COND_CASES_TAC THEN
    REWRITE_TAC[distinctness "option"] THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_eq o concl)) THEN STRIP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
    SUBGOAL_THEN `LENGTH (a1:hol_type list) = LENGTH (a2:hol_type list) /\
                  LENGTH (ps:hol_type list) = LENGTH (obs:hol_type list)`
      STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[arities_match_length]; ALL_TAC] THEN
    REMOVE_THEN "ih" (MP_TAC o SPECL [`s':(hol_type#hol_type)list`; `ids':mlstring list`] o
                      REWRITE_RULE[]) THEN
    ASM_SIMP_TAC[arities_match_append] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`s1:(hol_type#hol_type)list`; `ids1:mlstring list`] THEN
    ASM_REWRITE_TAC[MAP; TYPE_SUBST_def; injectivity "hol_type"; CONS_11] THEN
    UNDISCH_TAC `MAP (TYPE_SUBST s') (APPEND a1 ps) = APPEND a2 (obs:hol_type list)` THEN
    ASM_SIMP_TAC[MAP_APPEND; APPEND_LENGTH_EQ; LENGTH_MAP]]);;

let match_type_def = cake_def
  `match_type ty1 ty2 = OPTION_MAP FST (tymatch [ty1] [ty2] ([],[]))`;;

(* lists of equal length whose elements match pairwise *)
let CSYNAUX_P8_arities_match_pairs = prove
 (`!l l'. LENGTH l = LENGTH l' /\
          (!x y. MEM x l /\ MEM y l' ==> arities_match [x] [y])
          ==> arities_match l l'`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; NOT_SUC; GSYM NOT_SUC; SUC_INJ; arities_match_def; MEM] THEN
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[MESON[APPEND]
    `CONS (h:hol_type) t = APPEND [h] t`] THEN
  MATCH_MP_TAC arities_match_append THEN ASM_MESON_TAC[]);;

let type_ok_arities_match = prove
 (`!tys ty1 ty2. type_ok tys ty1 /\ type_ok tys ty2 ==> arities_match [ty1] [ty2]`,
  GEN_TAC THEN MATCH_MP_TAC type_ind THEN
  REWRITE_TAC[arities_match_def] THEN
  MAP_EVERY X_GEN_TAC [`m:mlstring`; `l:hol_type list`] THEN DISCH_TAC THEN
  X_GEN_TAC `ty2:hol_type` THEN
  STRUCT_CASES_TAC(ISPEC `ty2:hol_type` (CONJUNCT1 (cases "hol_type"))) THEN
  REWRITE_TAC[arities_match_def; type_ok_def] THEN STRIP_TAC THEN
  DISCH_THEN SUBST_ALL_TAC THEN MATCH_MP_TAC CSYNAUX_P8_arities_match_pairs THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[option_INJ];
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_MEM]) THEN ASM_MESON_TAC[]]);;

let match_type_SOME = prove
 (`!ty1 ty2 s. arities_match [ty1] [ty2]
               ==> match_type ty1 ty2 = SOME s
               ==> TYPE_SUBST s ty1 = ty2`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[match_type_def] THEN
  MP_TAC(ISPEC `tymatch [ty1] [ty2] ([],[])` (cases "option")) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[OPTION_MAP_DEF; distinctness "option";
                                 injectivity "option"] THEN
  PAIR_CASES_ON `a:(hol_type#hol_type)list#mlstring list` THEN
  REWRITE_TAC[FST] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  MP_TAC(ISPECL [`[ty1:hol_type]`; `[ty2:hol_type]`;
                 `([],[]):(hol_type#hol_type)list#mlstring list`;
                 `a0:(hol_type#hol_type)list`; `a1:mlstring list`] tymatch_SOME) THEN
  ASM_REWRITE_TAC[FST; SND; MAP; MEM; ALL_DISTINCT; set_of_list; DISJOINT_EMPTY] THEN
  STRIP_TAC THEN ASM_MESON_TAC[CONS_11]);;
