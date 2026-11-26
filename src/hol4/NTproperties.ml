(* ========================================================================= *)
(* NTproperties: port of HOL4 examples/formal-languages/context-free/       *)
(* NTpropertiesScript.sml (HOL4 library used by CakeML v3479).               *)
(* Nullability and first sets of sentential forms, with the executable       *)
(* (worklist) versions nullableML and firstSetML and their correctness.      *)
(* This work draws on Aditi Barthwal's formalisation (HOL4 header).          *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - HOL4's overloads derives G and nullableNT G n are RTC (derive G) and    *)
(*   nullable G [NT n]; set l is set_of_list l; BIGUNION is UNIONS.          *)
(* - nullableML and firstSetML are HOL4 [schematic] definitions: the         *)
(*   grammar is their first argument.  Their termination uses the measure    *)
(*   of HOL4 (CARD of the unseen non-terminals, then LENGTH).  firstSetML is  *)
(*   defined with the guard ~(n IN seen) lifted to the top (HOL Light's      *)
(*   recursion package needs it there); firstSetML_def is HOL4's equation    *)
(*   and firstSetML_ind is proved from the measure.                          *)
(* - The commented-out follow-set material of the HOL4 script is not ported. *)
(* - Lemmas named LPARSEAUX_... are helpers of this unit (not HOL4 names);   *)
(*   heads_give_first and MEM_last_strip (local in HOL4) are                 *)
(*   LPARSEAUX_heads_give_first and LPARSEAUX_MEM_last_strip.                *)
(* ========================================================================= *)

needs "hol4/vocab.ml";;
needs "hol4/finite_map.ml";;
needs "hol4/location.ml";;
needs "hol4/grammar.ml";;

(* ------------------------------------------------------------------------- *)
(* Nullability.                                                              *)
(* ------------------------------------------------------------------------- *)

let nullable_def = new_definition
  `nullable (G:(A,B)grammar) sf <=> RTC (derive G) sf []`;;

let LPARSEAUX_CONS_EQ_APPEND_SNOC = prove
 (`!(x:A) s0 l y s.
     CONS x s0 = APPEND (APPEND l [y]) s
     ==> (l = [] /\ x = y /\ s0 = s) \/
         (?l'. l = CONS x l' /\ s0 = APPEND (APPEND l' [y]) s)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[APPEND; CONS_11; NOT_CONS_NIL] THEN MESON_TAC[]);;

let derives_TOK = prove
 (`!(G:(A,B)grammar) p s t sf.
     RTC (derive G) (APPEND (APPEND p [grammar_TOK t]) s) sf
     ==> ?ps ss. sf = APPEND (APPEND ps [grammar_TOK t]) ss /\
                 RTC (derive G) p ps /\ RTC (derive G) s ss`,
  GEN_TAC THEN
  SUBGOAL_THEN
   `!sf0 sf. RTC (derive (G:(A,B)grammar)) sf0 sf
             ==> !p s t. sf0 = APPEND (APPEND p [grammar_TOK t]) s
                         ==> ?ps ss. sf = APPEND (APPEND ps [grammar_TOK t]) ss /\
                                     RTC (derive G) p ps /\
                                     RTC (derive G) s ss`
   (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC RTC_INDUCT_R THEN CONJ_TAC THENL
   [MESON_TAC[RTC_REFL]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:((A,B)symbol)list`; `y:((A,B)symbol)list`;
                       `z:((A,B)symbol)list`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (LABEL_TAC "ih")) THEN
  REWRITE_TAC[derive_def] THEN
  DISCH_THEN(X_CHOOSE_THEN `p0:((A,B)symbol)list` (X_CHOOSE_THEN `N:B+num`
    (X_CHOOSE_THEN `r:((A,B)symbol)list`
    (X_CHOOSE_THEN `s0:((A,B)symbol)list` STRIP_ASSUME_TAC)))) THEN
  MAP_EVERY X_GEN_TAC [`p:((A,B)symbol)list`; `s:((A,B)symbol)list`;
                       `t:A`] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `APPEND (APPEND p [grammar_TOK t:(A,B)symbol]) s =
    APPEND p0 (APPEND [grammar_NT N] s0)` MP_TAC THENL
   [ASM_MESON_TAC[APPEND_ASSOC]; ALL_TAC] THEN
  REWRITE_TAC[LPARSEAUX_APPEND_EQ_APPEND_MID] THEN STRIP_TAC THENL
   [(* the NT is to the right of the token *)
    REMOVE_THEN "ih" (MP_TAC o SPECL
      [`p:((A,B)symbol)list`; `APPEND (APPEND l r) s0:((A,B)symbol)list`;
       `t:A`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[GSYM APPEND_ASSOC; APPEND]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `ps:((A,B)symbol)list` (X_CHOOSE_THEN
      `ss:((A,B)symbol)list` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`ps:((A,B)symbol)list`; `ss:((A,B)symbol)list`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RTC_TRANS_R THEN
    EXISTS_TAC `APPEND (APPEND l r) s0:((A,B)symbol)list` THEN
    ASM_REWRITE_TAC[derive_def] THEN
    MAP_EVERY EXISTS_TAC [`l:((A,B)symbol)list`; `N:B+num`;
                          `r:((A,B)symbol)list`; `s0:((A,B)symbol)list`] THEN
    ASM_REWRITE_TAC[APPEND; GSYM APPEND_ASSOC];
    (* the NT is to the left of the token *)
    FIRST_X_ASSUM(MP_TAC o MATCH_MP LPARSEAUX_CONS_EQ_APPEND_SNOC o
                  REWRITE_RULE[APPEND] o
                  check (fun th -> is_eq(concl th) &&
                                   is_comb(lhs(concl th)) &&
                                   not(is_var(lhs(concl th))))) THEN
    REWRITE_TAC[symbol_distinct] THEN
    DISCH_THEN(X_CHOOSE_THEN `l':((A,B)symbol)list` STRIP_ASSUME_TAC) THEN
    REMOVE_THEN "ih" (MP_TAC o SPECL
      [`APPEND (APPEND p0 r) l':((A,B)symbol)list`; `s:((A,B)symbol)list`;
       `t:A`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[GSYM APPEND_ASSOC; APPEND]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `ps:((A,B)symbol)list` (X_CHOOSE_THEN
      `ss:((A,B)symbol)list` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`ps:((A,B)symbol)list`; `ss:((A,B)symbol)list`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RTC_TRANS_R THEN
    EXISTS_TAC `APPEND (APPEND p0 r) l':((A,B)symbol)list` THEN
    ASM_REWRITE_TAC[derive_def] THEN
    MAP_EVERY EXISTS_TAC [`p0:((A,B)symbol)list`; `N:B+num`;
                          `r:((A,B)symbol)list`; `l':((A,B)symbol)list`] THEN
    ASM_REWRITE_TAC[GSYM APPEND_ASSOC; APPEND]]);;

let nullable_CONS_TOK = prove
 (`!(G:(A,B)grammar) t rest. nullable G (CONS (grammar_TOK t) rest) <=> F`,
  REWRITE_TAC[nullable_def] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(A,B)grammar`; `[]:((A,B)symbol)list`;
                 `rest:((A,B)symbol)list`; `t:A`; `[]:((A,B)symbol)list`]
                derives_TOK) THEN
  ASM_REWRITE_TAC[APPEND; LPARSEAUX_NIL_EQ_APPEND; APPEND_EQ_NIL; NOT_CONS_NIL]);;

let nullable_NIL = prove
 (`!G:(A,B)grammar. nullable G [] <=> T`,
  REWRITE_TAC[nullable_def; RTC_REFL]);;

let nullable_CONS_NT = prove
 (`!(G:(A,B)grammar) n rest.
     nullable G (CONS (grammar_NT n) rest) <=>
     nullable G rest /\ n IN FDOM (grammar_rules G) /\
     ?r. r IN FAPPLY (grammar_rules G) n /\ nullable G r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[nullable_def] THEN EQ_TAC THENL
   [ONCE_REWRITE_TAC[LPARSEAUX_CONS_APPEND] THEN
    REWRITE_TAC[derives_split_horizontally; LPARSEAUX_NIL_EQ_APPEND] THEN
    REWRITE_TAC[LEFT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `RTC (derive (G:(A,B)grammar)) [grammar_NT n] []` THEN
    DISCH_THEN(MP_TAC o ONCE_REWRITE_RULE[RTC_CASES_R]) THEN
    REWRITE_TAC[NOT_CONS_NIL; derive_1NT] THEN MESON_TAC[];
    STRIP_TAC THEN MATCH_MP_TAC RTC_TRANS_R THEN
    EXISTS_TAC `APPEND (r:((A,B)symbol)list) rest` THEN CONJ_TAC THENL
     [REWRITE_TAC[derive_def] THEN
      MAP_EVERY EXISTS_TAC [`[]:((A,B)symbol)list`; `n:B+num`;
                            `r:((A,B)symbol)list`; `rest:((A,B)symbol)list`] THEN
      ASM_REWRITE_TAC[APPEND];
      SUBST1_TAC(SYM(ISPEC `[]:((A,B)symbol)list` (CONJUNCT1 APPEND))) THEN
      MATCH_MP_TAC derives_paste_horizontally THEN ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* The executable nullableML.                                                *)
(* ------------------------------------------------------------------------- *)

let LPARSEAUX_CARD_DIFF_INSERT = prove
 (`!(s:A->bool) t n.
     FINITE s /\ n IN s /\ ~(n IN t)
     ==> CARD (s DIFF (n INSERT t)) < CARD (s DIFF t)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CARD_PSUBSET THEN
  ASM_SIMP_TAC[FINITE_DIFF] THEN ASM SET_TAC[]);;

let LPARSEAUX_NT_TERM_TAC : tactic =
  REWRITE_TAC(WF_REL_THMS @ [FST; SND; LENGTH]) THEN REPEAT STRIP_TAC THEN
  TRY(DISJ1_TAC THEN MATCH_MP_TAC LPARSEAUX_CARD_DIFF_INSERT THEN
      ASM_REWRITE_TAC[FDOM_FINITE] THEN NO_TAC) THEN
  ASM_ARITH_TAC;;

let nullableML_def = cake_def_wf
  `inv_image ((<) LEX (<))
     (\t:(A,B)grammar#((B+num)->bool)#((A,B)symbol)list.
        (CARD (FDOM (grammar_rules (FST t)) DIFF FST (SND t)),
         LENGTH (SND (SND t))))`
  LPARSEAUX_NT_TERM_TAC
  `(nullableML (G:(A,B)grammar) seen [] <=> T) /\
   (nullableML G seen (CONS (grammar_TOK t) u) <=> F) /\
   (nullableML G seen (CONS (grammar_NT n) rest) <=>
      if n IN FDOM (grammar_rules G) /\ ~(n IN seen) then
        if FAPPLY (grammar_rules G) n INTER
           {r | nullableML G (n INSERT seen) r} = {}
        then F
        else nullableML G seen rest
      else F)`;;

let nullableML_ind = cake_ind "nullableML";;

let nullableML_nullable = prove
 (`!(G:(A,B)grammar) sn sf. nullableML G sn sf ==> nullable G sf`,
  MATCH_MP_TAC nullableML_ind THEN
  REWRITE_TAC[nullableML_def; nullable_NIL; nullable_CONS_NT] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `n IN FDOM (grammar_rules (G:(A,B)grammar)) /\ ~(n IN seen)` THEN
  ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `~(FAPPLY (grammar_rules (G:(A,B)grammar)) n INTER
                 {r | nullableML G (n INSERT seen) r} = {})` THEN
  REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY;
              NOT_FORALL_THM] THEN
  ASM_MESON_TAC[]);;

let ptree_NTs_def = new_specification ["ptree_NTs"]
 (prove
  (CASE_TERM
   `?ptree_NTs.
      (!(l:(A,B)symbol) (u:C).
         ptree_NTs (grammar_Lf (l,u)) = (match l with grammar_NT N -> {N} | u1 -> {})) /\
      (!(n:B+num) (u:C) (subs:((A,B,C)parsetree)list).
         ptree_NTs (grammar_Nd (n,u) subs) =
         n INSERT UNIONS (IMAGE ptree_NTs (set_of_list subs)))`,
   MP_TAC(ISPECL
    [CASE_TERM `\p:(A,B)symbol#C. (match FST p with grammar_NT N -> {N} | u1 -> {})`;
     `\(x:(B+num)#C) (subs:((A,B,C)parsetree)list) (rs:((B+num)->bool)list).
        FST x INSERT UNIONS (set_of_list rs)`]
    LPARSEAUX_parsetree_MAP_RECURSION) THEN
   MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
   SIMP_TAC[SET_OF_LIST_MAP]));;

let ptree_rptfree_def = new_specification ["ptree_rptfree"]
 (prove
  (`?ptree_rptfree.
      (!p:(A,B)symbol#C. ptree_rptfree (grammar_Lf p) <=> T) /\
      (!(N:B+num) (u:C) (subs:((A,B,C)parsetree)list).
         ptree_rptfree (grammar_Nd (N,u) subs) <=>
         !s. MEM s subs ==> ptree_rptfree s /\ ~(N IN ptree_NTs s))`,
   MP_TAC(ISPECL
    [`\p:(A,B)symbol#C. T`;
     `\(x:(B+num)#C) (subs:((A,B,C)parsetree)list) (rs:bool list).
        ALL (\b. b) rs /\ !s. MEM s subs ==> ~(FST x IN ptree_NTs s)`]
    LPARSEAUX_parsetree_MAP_RECURSION) THEN
   MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
   REWRITE_TAC[ALL_MAP; o_DEF] THEN REWRITE_TAC[GSYM ALL_MEM] THEN
   SIMP_TAC[] THEN MESON_TAC[]));;

let LPARSEAUX_DISJ_IMP = TAUT `!p q r. (p \/ q ==> r) <=> (p ==> r) /\ (q ==> r)`;;

let nullableML_by_singletons = prove
 (`!(G:(A,B)grammar) sn sf.
     nullableML G sn sf <=> !a. MEM a sf ==> nullableML G sn [a]`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MEM; LPARSEAUX_DISJ_IMP; FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[nullableML_def] THEN
  STRUCT_CASES_TAC(ISPEC `h:(A,B)symbol` symbol_nchotomy) THEN
  ASM_REWRITE_TAC[nullableML_def] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]));;

let nullable_by_singletons = prove
 (`!(G:(A,B)grammar) sf. nullable G sf <=> !a. MEM a sf ==> nullable G [a]`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MEM; LPARSEAUX_DISJ_IMP; FORALL_AND_THM; FORALL_UNWIND_THM2;
              nullable_NIL] THEN
  STRUCT_CASES_TAC(ISPEC `h:(A,B)symbol` symbol_nchotomy) THEN
  ASM_REWRITE_TAC[nullable_CONS_TOK; nullable_CONS_NT; nullable_NIL] THEN
  MESON_TAC[]);;

let LPARSEAUX_FLAT_MAP_EQ_NIL = prove
 (`!(f:A->B list) l. FLAT (MAP f l) = [] <=> !x. MEM x l ==> f x = []`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[MAP; FLAT; MEM; APPEND_EQ_NIL] THEN MESON_TAC[]);;

let ptree_nullableML = prove
 (`!(G:(A,B)grammar) (pt:(A,B,C)parsetree) sn.
     DISJOINT (ptree_NTs pt) sn /\ ptree_fringe pt = [] /\
     valid_ptree G pt /\ ptree_rptfree pt
     ==> nullableML G sn [ptree_head pt]`,
  GEN_TAC THEN MATCH_MP_TAC ptree_ind THEN CONJ_TAC THENL
   [REWRITE_TAC[FORALL_PAIR_THM; ptree_fringe_def; NOT_CONS_NIL];
    ALL_TAC] THEN
  X_GEN_TAC `subs:((A,B,C)parsetree)list` THEN DISCH_TAC THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`N:B+num`; `l:C`; `sn:(B+num)->bool`] THEN
  REWRITE_TAC[ptree_NTs_def; ptree_fringe_def; valid_ptree_def;
              ptree_rptfree_def; ptree_head_def; IN_SET_OF_LIST;
              LPARSEAUX_FLAT_MAP_EQ_NIL] THEN
  STRIP_TAC THEN REWRITE_TAC[nullableML_def] THEN
  SUBGOAL_THEN `~(N IN (sn:(B+num)->bool))` ASSUME_TAC THENL
   [ASM SET_TAC[]; ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY;
              NOT_FORALL_THM] THEN
  REWRITE_TAC[TAUT `(if p then F else T) <=> ~p`; NOT_FORALL_THM] THEN
  EXISTS_TAC `MAP ptree_head (subs:((A,B,C)parsetree)list)` THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[nullableML_by_singletons] THEN
  REWRITE_TAC[MEM_MAP] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:(A,B,C)parsetree` o
    check (fun th -> is_forall(concl th) &&
                     can (find_term (fun t -> try fst(dest_const t) = "nullableML"
                                              with Failure _ -> false))
                         (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN `(x:(A,B,C)parsetree) IN set_of_list subs /\ ~(N IN ptree_NTs x)`
    MP_TAC THENL [ASM_MESON_TAC[IN_SET_OF_LIST]; ALL_TAC] THEN
  UNDISCH_TAC `DISJOINT (N INSERT UNIONS (IMAGE ptree_NTs
                 (set_of_list (subs:((A,B,C)parsetree)list)))) sn` THEN
  SET_TAC[]);;

let rptfree_subtree = prove
 (`!(G:(A,B)grammar) N (pt:(A,B,C)parsetree).
     ptree_rptfree pt /\ N IN ptree_NTs pt /\ ptree_fringe pt = [] /\
     valid_ptree G pt
     ==> ?pt':(A,B,C)parsetree.
           ptree_rptfree pt' /\ ptree_head pt' = grammar_NT N /\
           ptree_fringe pt' = [] /\ valid_ptree G pt'`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC ptree_ind THEN CONJ_TAC THENL
   [REWRITE_TAC[FORALL_PAIR_THM; ptree_fringe_def; NOT_CONS_NIL];
    ALL_TAC] THEN
  X_GEN_TAC `subs:((A,B,C)parsetree)list` THEN DISCH_TAC THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`n:B+num`; `l:C`] THEN
  REWRITE_TAC[ptree_NTs_def; IN_INSERT; IN_UNIONS; IN_IMAGE; IN_SET_OF_LIST] THEN
  STRIP_TAC THENL
   [EXISTS_TAC `grammar_Nd (n,l) subs:(A,B,C)parsetree` THEN
    ASM_REWRITE_TAC[ptree_head_def];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:(A,B,C)parsetree` o
    check (fun th -> is_forall(concl th) && is_imp(snd(dest_forall(concl th))) &&
                     can (find_term (fun t -> try fst(dest_const t) = "ptree_rptfree"
                                              with Failure _ -> false))
                         (concl th) &&
                     can (find_term (fun t -> try fst(dest_const t) = "ptree_head"
                                              with Failure _ -> false))
                         (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ptree_rptfree_def; ptree_fringe_def;
                              valid_ptree_def; IN_SET_OF_LIST;
                              LPARSEAUX_FLAT_MAP_EQ_NIL]) THEN
  ASM_MESON_TAC[]);;

let LPARSEAUX_choose_children = prove
 (`!(P:(A,B,C)parsetree->bool) (subs:((A,B,C)parsetree)list).
     (!a. MEM a subs ==> ?a'. ptree_head a' = ptree_head a /\ P a')
     ==> ?subs'. MAP ptree_head subs' = MAP ptree_head subs /\
                 !p. MEM p subs' ==> P p`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
   [DISCH_TAC THEN EXISTS_TAC `[]:((A,B,C)parsetree)list` THEN
    REWRITE_TAC[MAP; MEM];
    ALL_TAC] THEN
  REWRITE_TAC[MEM] THEN DISCH_THEN(LABEL_TAC "hyp") THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ANTS_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t':((A,B,C)parsetree)list` STRIP_ASSUME_TAC) THEN
  REMOVE_THEN "hyp" (MP_TAC o SPEC `h:(A,B,C)parsetree`) THEN REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h':(A,B,C)parsetree` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `CONS (h':(A,B,C)parsetree) t'` THEN
  ASM_REWRITE_TAC[MAP; MEM] THEN ASM_MESON_TAC[]);;

let rptfree_nullable_ptrees_possible = prove
 (`!(G:(A,B)grammar) (pt:(A,B,C)parsetree).
     valid_ptree G pt /\ ptree_fringe pt = []
     ==> ?pt':(A,B,C)parsetree.
           valid_ptree G pt' /\ ptree_head pt' = ptree_head pt /\
           ptree_fringe pt' = [] /\ ptree_rptfree pt'`,
  GEN_TAC THEN MATCH_MP_TAC ptree_ind THEN CONJ_TAC THENL
   [REWRITE_TAC[FORALL_PAIR_THM; ptree_fringe_def; NOT_CONS_NIL];
    ALL_TAC] THEN
  X_GEN_TAC `subs:((A,B,C)parsetree)list` THEN DISCH_TAC THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`N:B+num`; `l:C`] THEN
  REWRITE_TAC[valid_ptree_def; ptree_fringe_def; IN_SET_OF_LIST;
              LPARSEAUX_FLAT_MAP_EQ_NIL; ptree_head_def] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`\p:(A,B,C)parsetree. valid_ptree (G:(A,B)grammar) p /\
                                       ptree_fringe p = [] /\ ptree_rptfree p`;
                 `subs:((A,B,C)parsetree)list`] LPARSEAUX_choose_children) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [X_GEN_TAC `a:(A,B,C)parsetree` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `a:(A,B,C)parsetree` o
      check (fun th -> is_forall(concl th) &&
               can (find_term (fun t -> try fst(dest_const t) = "ptree_rptfree"
                                        with Failure _ -> false)) (concl th))) THEN
    ASM_SIMP_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `subs':((A,B,C)parsetree)list` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `?pt:(A,B,C)parsetree. MEM pt subs' /\ N IN ptree_NTs pt` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `pt:(A,B,C)parsetree` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`G:(A,B)grammar`; `N:B+num`; `pt:(A,B,C)parsetree`]
                  rptfree_subtree) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; MESON_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `grammar_Nd (N,l) subs':(A,B,C)parsetree` THEN
  ASM_REWRITE_TAC[valid_ptree_def; ptree_fringe_def; IN_SET_OF_LIST;
                  LPARSEAUX_FLAT_MAP_EQ_NIL; ptree_head_def;
                  ptree_rptfree_def] THEN
  ASM_MESON_TAC[]);;

let nullable_nullableML = prove
 (`!(G:(A,B)grammar) sf. nullable G sf ==> nullableML G {} sf`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[nullable_by_singletons] THEN
  ONCE_REWRITE_TAC[nullableML_by_singletons] THEN
  DISCH_TAC THEN X_GEN_TAC `a:(A,B)symbol` THEN DISCH_TAC THEN
  SUBGOAL_THEN `RTC (derive (G:(A,B)grammar)) [a] []` MP_TAC THENL
   [ASM_MESON_TAC[nullable_def]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP singleton_derives_ptree) THEN
  DISCH_THEN(X_CHOOSE_THEN `pt:(A,B,1)parsetree` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`G:(A,B)grammar`; `pt:(A,B,1)parsetree`]
                rptfree_nullable_ptrees_possible) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `pt':(A,B,1)parsetree` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`G:(A,B)grammar`; `pt':(A,B,1)parsetree`;
                 `{}:(B+num)->bool`] ptree_nullableML) THEN
  ASM_REWRITE_TAC[DISJOINT_EMPTY]);;

let nullableML_EQN = prove
 (`!(G:(A,B)grammar) sf. nullable G sf <=> nullableML G {} sf`,
  MESON_TAC[nullable_nullableML; nullableML_nullable]);;

(* ------------------------------------------------------------------------- *)
(* First sets.                                                               *)
(* ------------------------------------------------------------------------- *)

let firstSet_def = new_definition
  `firstSet (G:(A,B)grammar) sf =
     {t | ?rest. RTC (derive G) sf (CONS (grammar_TOK t) rest)}`;;

let firstSet_nonempty_fringe = prove
 (`!(G:(A,B)grammar) (pt:(A,B,C)parsetree) t rest.
     ptree_fringe pt = CONS (grammar_TOK t) rest /\ valid_ptree G pt
     ==> t IN firstSet G [ptree_head pt]`,
  REWRITE_TAC[firstSet_def; IN_ELIM_THM] THEN
  MESON_TAC[valid_ptree_derive]);;

let IN_firstSet = prove
 (`!(G:(A,B)grammar) t sym.
     t IN firstSet G [sym]
     ==> ?pt:(A,B,1)parsetree rest.
           ptree_head pt = sym /\ valid_ptree G pt /\
           ptree_fringe pt = CONS (grammar_TOK t) rest`,
  REWRITE_TAC[firstSet_def; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(A,B)grammar`; `grammar_Lf (sym,one):(A,B,1)parsetree`;
                 `CONS (grammar_TOK t) rest:((A,B)symbol)list`]
                ptrees_derive_extensible) THEN
  ASM_REWRITE_TAC[valid_ptree_def; ptree_fringe_def; ptree_head_def] THEN
  MESON_TAC[]);;

let LPARSEAUX_MAP_TOK_NEQ_NT = prove
 (`!(syms:A list) p (N:B+num) l.
     ~(MAP (grammar_TOK:A->(A,B)symbol) syms = APPEND (APPEND p [grammar_NT N]) l)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o AP_TERM `MEM (grammar_NT N:(A,B)symbol)`) THEN
  REWRITE_TAC[MEM_MAP; MEM_APPEND; MEM; symbol_distinct]);;

let derives_preserves_leading_toks = prove
 (`!(G:(A,B)grammar) syms rest x.
     RTC (derive G) (APPEND (MAP grammar_TOK syms) rest) x <=>
     ?rest'. RTC (derive G) rest rest' /\ x = APPEND (MAP grammar_TOK syms) rest'`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [ALL_TAC;
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC derives_paste_horizontally THEN ASM_REWRITE_TAC[RTC_REFL]] THEN
  SUBGOAL_THEN
   `!x y. RTC (derive (G:(A,B)grammar)) x y
          ==> !syms rest. x = APPEND (MAP grammar_TOK syms) rest
                          ==> ?rest'. RTC (derive G) rest rest' /\
                                      y = APPEND (MAP grammar_TOK syms) rest'`
   (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC RTC_INDUCT_L THEN CONJ_TAC THENL
   [MESON_TAC[RTC_REFL]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:((A,B)symbol)list`; `y:((A,B)symbol)list`;
                       `z:((A,B)symbol)list`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih") MP_TAC) THEN
  REWRITE_TAC[derive_def] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:((A,B)symbol)list` (X_CHOOSE_THEN `N:B+num`
    (X_CHOOSE_THEN `r:((A,B)symbol)list`
    (X_CHOOSE_THEN `s:((A,B)symbol)list` STRIP_ASSUME_TAC)))) THEN
  MAP_EVERY X_GEN_TAC [`syms:A list`; `rest:((A,B)symbol)list`] THEN
  DISCH_TAC THEN
  REMOVE_THEN "ih" (MP_TAC o SPECL [`syms:A list`;
                                   `rest:((A,B)symbol)list`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `rest1:((A,B)symbol)list` (CONJUNCTS_THEN2
    ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[LPARSEAUX_APPEND_EQ_APPEND_MID; LPARSEAUX_MAP_TOK_NEQ_NT] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:((A,B)symbol)list` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `APPEND (APPEND q r) s:((A,B)symbol)list` THEN CONJ_TAC THENL
   [MATCH_MP_TAC RTC_TRANS_L THEN EXISTS_TAC `rest1:((A,B)symbol)list` THEN
    ASM_REWRITE_TAC[derive_def] THEN
    MAP_EVERY EXISTS_TAC [`q:((A,B)symbol)list`; `N:B+num`;
                          `r:((A,B)symbol)list`; `s:((A,B)symbol)list`] THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[APPEND_ASSOC]]);;

let firstSet_NIL = prove
 (`!G:(A,B)grammar. firstSet G [] = {}`,
  GEN_TAC THEN REWRITE_TAC[firstSet_def; EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
  ONCE_REWRITE_TAC[RTC_CASES_R] THEN
  REWRITE_TAC[NOT_CONS_NIL; derive_def; LPARSEAUX_NIL_EQ_APPEND] THEN
  REWRITE_TAC[APPEND_EQ_NIL; NOT_CONS_NIL]);;

let firstSet_TOK = prove
 (`!(G:(A,B)grammar) t rest. firstSet G (CONS (grammar_TOK t) rest) = {t}`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[firstSet_def; EXTENSION; IN_ELIM_THM; IN_SING] THEN
  X_GEN_TAC `t':A` THEN EQ_TAC THENL
   [MP_TAC(ISPECL [`G:(A,B)grammar`; `[t:A]`; `rest:((A,B)symbol)list`]
                  derives_preserves_leading_toks) THEN
    REWRITE_TAC[MAP; APPEND] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[CONS_11; symbol_inject] THEN MESON_TAC[];
    DISCH_THEN SUBST1_TAC THEN MESON_TAC[RTC_REFL]]);;

let LPARSEAUX_firstSet_NT_imp = prove
 (`!(G:(A,B)grammar) N rest t rest'.
     RTC (derive G) (CONS (grammar_NT N) rest) (CONS (grammar_TOK t) rest')
     ==> (?rhs r0. rhs IN FAPPLY (grammar_rules G) N /\
                   RTC (derive G) rhs (CONS (grammar_TOK t) r0)) \/
         (nullable G [grammar_NT N] /\ ?r0. RTC (derive G) rest (CONS (grammar_TOK t) r0))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o ONCE_REWRITE_RULE[LPARSEAUX_CONS_APPEND]) THEN
  REWRITE_TAC[derives_split_horizontally] THEN
  DISCH_THEN(X_CHOOSE_THEN `z1:((A,B)symbol)list` (X_CHOOSE_THEN
    `z2:((A,B)symbol)list` STRIP_ASSUME_TAC)) THEN
  UNDISCH_TAC `APPEND [grammar_TOK t:(A,B)symbol] rest' = APPEND z1 z2` THEN
  REWRITE_TAC[APPEND] THEN DISCH_THEN(MP_TAC o SYM) THEN
  REWRITE_TAC[LPARSEAUX_APPEND_EQ_CONS] THEN STRIP_TAC THEN RVEQ_TAC THENL
   [DISJ2_TAC THEN ASM_REWRITE_TAC[nullable_def] THEN ASM_MESON_TAC[];
    DISJ1_TAC THEN
    UNDISCH_TAC `RTC (derive (G:(A,B)grammar)) [grammar_NT N] (CONS (grammar_TOK t) l1')` THEN
    DISCH_THEN(MP_TAC o ONCE_REWRITE_RULE[RTC_CASES_R]) THEN
    REWRITE_TAC[CONS_11; symbol_distinct; derive_1NT] THEN
    MESON_TAC[]]);;

let LPARSEAUX_firstSet_NT_rhs = prove
 (`!(G:(A,B)grammar) N x t r0 rest.
     N IN FDOM (grammar_rules G) /\ x IN FAPPLY (grammar_rules G) N /\
     RTC (derive G) x (CONS (grammar_TOK t) r0)
     ==> RTC (derive G) (CONS (grammar_NT N) rest) (CONS (grammar_TOK t) (APPEND r0 rest))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RTC_TRANS_R THEN
  EXISTS_TAC `APPEND (x:((A,B)symbol)list) rest` THEN CONJ_TAC THENL
   [REWRITE_TAC[derive_def] THEN
    MAP_EVERY EXISTS_TAC [`[]:((A,B)symbol)list`; `N:B+num`;
                          `x:((A,B)symbol)list`; `rest:((A,B)symbol)list`] THEN
    ASM_REWRITE_TAC[APPEND];
    SUBGOAL_THEN `CONS (grammar_TOK t) (APPEND r0 rest):((A,B)symbol)list =
                  APPEND (CONS (grammar_TOK t) r0) rest` SUBST1_TAC THENL
     [REWRITE_TAC[APPEND]; ALL_TAC] THEN
    MATCH_MP_TAC derives_paste_horizontally THEN ASM_REWRITE_TAC[RTC_REFL]]);;

let LPARSEAUX_firstSet_NT_null = prove
 (`!(G:(A,B)grammar) N t r0 rest.
     nullable G [grammar_NT N] /\ RTC (derive G) rest (CONS (grammar_TOK t) r0)
     ==> RTC (derive G) (CONS (grammar_NT N) rest) (CONS (grammar_TOK t) r0)`,
  REWRITE_TAC[nullable_def] THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[LPARSEAUX_CONS_APPEND] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM(CONJUNCT1 APPEND)] THEN
  MATCH_MP_TAC derives_paste_horizontally THEN
  ASM_REWRITE_TAC[GSYM LPARSEAUX_CONS_APPEND]);;

let firstSet_NT = prove
 (`!(G:(A,B)grammar) N rest.
     firstSet G (CONS (grammar_NT N) rest) =
       if N IN FDOM (grammar_rules G) then
         UNIONS (IMAGE (firstSet G) (FAPPLY (grammar_rules G) N)) UNION
         (if nullable G [grammar_NT N] then firstSet G rest else {})
       else {}`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THENL
   [ALL_TAC;
    ASM_SIMP_TAC[firstSet_def; derives_leading_nonNT; EXTENSION; IN_ELIM_THM;
                 NOT_IN_EMPTY; CONS_11; symbol_distinct]] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `t:A` THEN
  REWRITE_TAC[IN_UNION; IN_UNIONS; IN_IMAGE] THEN
  REWRITE_TAC[MESON[]
   `(?s. (?x:((A,B)symbol)list. s = (f:((A,B)symbol)list->A->bool) x /\
                                P x) /\ (t:A) IN s) <=>
    (?x. P x /\ t IN f x)`] THEN
  COND_CASES_TAC THEN REWRITE_TAC[NOT_IN_EMPTY] THEN
  REWRITE_TAC[firstSet_def; IN_ELIM_THM] THEN
  ASM_MESON_TAC[LPARSEAUX_firstSet_NT_imp; LPARSEAUX_firstSet_NT_rhs;
                LPARSEAUX_firstSet_NT_null]);;

(* ------------------------------------------------------------------------- *)
(* The executable firstSetML.                                                *)
(* ------------------------------------------------------------------------- *)

let LPARSEAUX_ADMISSIBLE_TAC : tactic =
  fun (asl,w as g) ->
    if (try fst(dest_const(fst(strip_comb w))) = "admissible"
        with Failure _ -> false) then
      (REWRITE_TAC[admissible; FORALL_PAIR_THM] THEN
       CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
       REPEAT STRIP_TAC THEN ABS_TAC THEN
       FIRST_X_ASSUM MATCH_MP_TAC THEN LPARSEAUX_NT_TERM_TAC) g
    else failwith "LPARSEAUX_ADMISSIBLE_TAC";;

let LPARSEAUX_NT_TERM_TAC2 : tactic =
  LPARSEAUX_ADMISSIBLE_TAC ORELSE LPARSEAUX_NT_TERM_TAC;;

let LPARSEAUX_firstSetML_raw = cake_def_wf
  `inv_image ((<) LEX (<))
     (\t:(A,B)grammar#((B+num)->bool)#((A,B)symbol)list.
        (CARD (FDOM (grammar_rules (FST t)) DIFF FST (SND t)),
         LENGTH (SND (SND t))))`
  LPARSEAUX_NT_TERM_TAC2
  `(firstSetML (G:(A,B)grammar) seen [] = {}) /\
   (firstSetML G seen (CONS (grammar_TOK t) u) = {t}) /\
   (firstSetML G seen (CONS (grammar_NT n) rest) =
      if n IN FDOM (grammar_rules G) then
        if ~(n IN seen) then
          UNIONS (IMAGE (\r. firstSetML G (n INSERT seen) r)
                        (FAPPLY (grammar_rules G) n)) UNION
          (if nullable G [grammar_NT n] then firstSetML G seen rest else {})
        else
          {} UNION (if nullable G [grammar_NT n] then firstSetML G seen rest else {})
      else {})`;;

let firstSetML_def = prove
 (`(!(G:(A,B)grammar) seen. firstSetML G seen [] = {}) /\
   (!(G:(A,B)grammar) seen t u. firstSetML G seen (CONS (grammar_TOK t) u) = {t}) /\
   (!(G:(A,B)grammar) seen n rest.
      firstSetML G seen (CONS (grammar_NT n) rest) =
      if n IN FDOM (grammar_rules G) then
        (if ~(n IN seen) then
           UNIONS (IMAGE (firstSetML G (n INSERT seen))
                         (FAPPLY (grammar_rules G) n))
         else {}) UNION
        (if nullable G [grammar_NT n] then firstSetML G seen rest else {})
      else {})`,
  REWRITE_TAC[LPARSEAUX_firstSetML_raw; ETA_AX] THEN
  REPEAT GEN_TAC THEN REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]));;


let LPARSEAUX_NT_WF = prove
 (`WF (inv_image ((<) LEX (<))
        (\t:(A,B)grammar#((B+num)->bool)#((A,B)symbol)list.
           (CARD (FDOM (grammar_rules (FST t)) DIFF FST (SND t)),
            LENGTH (SND (SND t)))))`,
  WF_TAC);;

(* HOL4: firstSetML_ind *)

let firstSetML_ind = prove
 (`!P:(A,B)grammar->((B+num)->bool)->((A,B)symbol)list->bool.
       (!(G:(A,B)grammar) seen. P G seen []) /\
       (!(G:(A,B)grammar) seen t u. P G seen (CONS (grammar_TOK t) u)) /\
       (!(G:(A,B)grammar) seen n rest.
          (n IN FDOM (grammar_rules G) /\ nullable G [grammar_NT n] ==> P G seen rest) /\
          (!r. n IN FDOM (grammar_rules G) /\ ~(n IN seen)
               ==> P G (n INSERT seen) r)
          ==> P G seen (CONS (grammar_NT n) rest))
       ==> !G seen sf. P G seen sf`,
  GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "nil")
    (CONJUNCTS_THEN2 (LABEL_TAC "tok") (LABEL_TAC "nt"))) THEN
  SUBGOAL_THEN
   `!x:(A,B)grammar#((B+num)->bool)#((A,B)symbol)list.
      P (FST x) (FST (SND x)) (SND (SND x))`
   (fun th -> REPEAT GEN_TAC THEN
              MP_TAC(SPEC `(G:(A,B)grammar),(seen:(B+num)->bool),
                           (sf:((A,B)symbol)list)` th) THEN
              REWRITE_TAC[FST; SND]) THEN
  MATCH_MP_TAC(REWRITE_RULE[WF_IND] LPARSEAUX_NT_WF) THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN
  MAP_EVERY X_GEN_TAC [`G:(A,B)grammar`; `seen:(B+num)->bool`;
                       `sf:((A,B)symbol)list`] THEN
  STRUCT_CASES_TAC(ISPEC `sf:((A,B)symbol)list` list_CASES) THENL
   [DISCH_TAC THEN USE_THEN "nil" MATCH_ACCEPT_TAC; ALL_TAC] THEN
  STRUCT_CASES_TAC(ISPEC `h:(A,B)symbol` symbol_nchotomy) THENL
   [DISCH_TAC THEN USE_THEN "tok" MATCH_ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "ih") THEN
  USE_THEN "nt" MATCH_MP_TAC THEN CONJ_TAC THEN REPEAT STRIP_TAC THEN
  USE_THEN "ih" MATCH_MP_TAC THEN LPARSEAUX_NT_TERM_TAC);;

let firstSetML_firstSet = prove
 (`!(G:(A,B)grammar) seen sf. firstSetML G seen sf SUBSET firstSet G sf`,
  MATCH_MP_TAC firstSetML_ind THEN
  REWRITE_TAC[firstSetML_def; firstSet_NIL; firstSet_TOK; SUBSET_REFL;
              EMPTY_SUBSET] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[firstSet_NT] THEN
  COND_CASES_TAC THEN REWRITE_TAC[EMPTY_SUBSET] THEN
  MATCH_MP_TAC(SET_RULE
   `(a:A->bool) SUBSET c /\ b SUBSET d ==> a UNION b SUBSET c UNION d`) THEN
  CONJ_TAC THENL
   [COND_CASES_TAC THEN REWRITE_TAC[EMPTY_SUBSET] THEN
    MATCH_MP_TAC UNIONS_MONO_IMAGE THEN ASM_SIMP_TAC[];
    COND_CASES_TAC THEN REWRITE_TAC[SUBSET_REFL] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (is_imp o concl)) THEN
    ASM_REWRITE_TAC[]]);;

let nts_derive_def = cake_def
  `(nts_derive (G:(A,B)grammar) [] (tk:A) <=> F) /\
   (nts_derive G [N] tk <=>
      N IN FDOM (grammar_rules G) /\
      ?p s. APPEND (APPEND p [grammar_TOK tk]) s IN FAPPLY (grammar_rules G) N /\
            nullable G p) /\
   (nts_derive G (CONS N1 (CONS N2 NS)) tk <=>
      N1 IN FDOM (grammar_rules G) /\
      ?p s. APPEND (APPEND p [grammar_NT N2]) s IN FAPPLY (grammar_rules G) N1 /\
            nullable G p /\ nts_derive G (CONS N2 NS) tk)`;;

let LPARSEAUX_nts_derive_CONS = prove
 (`!(G:(A,B)grammar) h l tk.
     nts_derive G (CONS h l) tk /\ ~(l = []) ==> nts_derive G l tk`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[nts_derive_def] THEN MESON_TAC[]);;

let nts_derive_APPEND_E = prove
 (`!(G:(A,B)grammar) n1 n2 tk.
     nts_derive G (APPEND n1 n2) tk /\ ~(n2 = []) ==> nts_derive G n2 tk`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC LPARSEAUX_nts_derive_CONS THEN
  EXISTS_TAC `h:B+num` THEN ASM_REWRITE_TAC[APPEND_EQ_NIL]);;

let firstSetML_nullable_prefix = prove
 (`!(G:(A,B)grammar) sn p sf x.
     x IN firstSetML G sn sf /\ nullable G p ==> x IN firstSetML G sn (APPEND p sf)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND] THEN
  STRUCT_CASES_TAC(ISPEC `h:(A,B)symbol` symbol_nchotomy) THEN
  REWRITE_TAC[nullable_CONS_TOK; nullable_CONS_NT] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[firstSetML_def; IN_UNION] THEN DISJ2_TAC THEN
  SUBGOAL_THEN `nullable (G:(A,B)grammar) [grammar_NT a]` (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[nullable_CONS_NT; nullable_NIL] THEN ASM_MESON_TAC[];
    ASM_MESON_TAC[]]);;

let firstSetML_CONS_I = prove
 (`!(G:(A,B)grammar) sn h t tk.
     tk IN firstSetML G sn [h] ==> tk IN firstSetML G sn (CONS h t)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `h:(A,B)symbol` symbol_nchotomy) THEN
  REWRITE_TAC[firstSetML_def] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  REWRITE_TAC[IN_UNION; NOT_IN_EMPTY] THEN MESON_TAC[]);;

let firstSet_CONS_I = prove
 (`!(G:(A,B)grammar) h t tk.
     tk IN firstSet G [h] ==> tk IN firstSet G (CONS h t)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `h:(A,B)symbol` symbol_nchotomy) THEN
  REWRITE_TAC[firstSet_NT; firstSet_TOK; firstSet_NIL] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  REWRITE_TAC[IN_UNION; NOT_IN_EMPTY] THEN MESON_TAC[]);;

let LPARSEAUX_distinct_nts_derive = prove
 (`!(G:(A,B)grammar) ns h tk sn.
     nts_derive G (CONS h ns) tk /\ ALL_DISTINCT (CONS h ns) /\
     set_of_list (CONS h ns) INTER sn = {}
     ==> tk IN firstSetML G sn [grammar_NT h]`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[nts_derive_def; ALL_DISTINCT; set_of_list] THEN
    MAP_EVERY X_GEN_TAC [`h:B+num`; `tk:A`; `sn:(B+num)->bool`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `p:((A,B)symbol)list` (X_CHOOSE_THEN
        `s:((A,B)symbol)list` STRIP_ASSUME_TAC))) STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `~((h:B+num) IN sn)` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[firstSetML_def; IN_UNION; IN_UNIONS; IN_IMAGE] THEN
    DISJ1_TAC THEN
    EXISTS_TAC `firstSetML (G:(A,B)grammar) (h INSERT sn)
                  (APPEND (APPEND p [grammar_TOK tk]) s)` THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM APPEND_ASSOC; APPEND] THEN
    MATCH_MP_TAC firstSetML_nullable_prefix THEN
    ASM_REWRITE_TAC[firstSetML_def; IN_SING];
    ALL_TAC] THEN
  REWRITE_TAC[nts_derive_def; ALL_DISTINCT; set_of_list; MEM] THEN
  MAP_EVERY X_GEN_TAC [`h0:B+num`; `tk:A`; `sn:(B+num)->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `p:((A,B)symbol)list` (X_CHOOSE_THEN
      `s:((A,B)symbol)list` STRIP_ASSUME_TAC))) STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~((h0:B+num) IN sn)` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[firstSetML_def; IN_UNION; IN_UNIONS; IN_IMAGE] THEN
  DISJ1_TAC THEN
  EXISTS_TAC `firstSetML (G:(A,B)grammar) (h0 INSERT sn)
                (APPEND (APPEND p [grammar_NT h]) s)` THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM APPEND_ASSOC; APPEND] THEN
  MATCH_MP_TAC firstSetML_nullable_prefix THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC firstSetML_CONS_I THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`h:B+num`; `tk:A`; `(h0:B+num) INSERT sn`] o
    check (fun th -> is_forall(concl th))) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[ALL_DISTINCT; set_of_list] THEN
  UNDISCH_TAC `(h0:B+num) INSERT h INSERT set_of_list t INTER sn = {}` THEN
  UNDISCH_TAC `~((h0:B+num) = h \/ MEM h0 t)` THEN
  REWRITE_TAC[GSYM IN_SET_OF_LIST] THEN SET_TAC[]);;

let distinct_nts_derive_firstSetML = prove
 (`!(G:(A,B)grammar) ns tk sn.
     nts_derive G ns tk /\ ALL_DISTINCT ns /\ set_of_list ns INTER sn = {}
     ==> tk IN firstSetML G sn [grammar_NT (HD ns)]`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[nts_derive_def; HD] THEN
  MESON_TAC[LPARSEAUX_distinct_nts_derive]);;

(* HOL4: heads_give_first (local) *)

let LPARSEAUX_heads_give_first = prove
 (`!(subs:((A,B,C)parsetree)list) tk rest.
     FLAT (MAP ptree_fringe subs) = CONS tk rest
     ==> ?p sym s r0. APPEND (APPEND p [sym]) s = subs /\
                      ptree_fringe sym = CONS tk r0 /\
                      FLAT (MAP ptree_fringe p) = []`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; FLAT; NOT_CONS_NIL] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[LPARSEAUX_APPEND_EQ_CONS]) THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`tk:(A,B)symbol`; `rest:((A,B)symbol)list`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:((A,B,C)parsetree)list` (X_CHOOSE_THEN
      `sym:(A,B,C)parsetree` (X_CHOOSE_THEN `s:((A,B,C)parsetree)list`
      (X_CHOOSE_THEN `r0:((A,B)symbol)list` STRIP_ASSUME_TAC)))) THEN
    MAP_EVERY EXISTS_TAC [`CONS (h:(A,B,C)parsetree) p`; `sym:(A,B,C)parsetree`;
                          `s:((A,B,C)parsetree)list`; `r0:((A,B)symbol)list`] THEN
    ASM_REWRITE_TAC[APPEND; MAP; FLAT];
    MAP_EVERY EXISTS_TAC [`[]:((A,B,C)parsetree)list`; `h:(A,B,C)parsetree`;
                          `t:((A,B,C)parsetree)list`; `l1':((A,B)symbol)list`] THEN
    ASM_REWRITE_TAC[APPEND; MAP; FLAT]]);;

let nullable_alltrees = prove
 (`!(G:(A,B)grammar) sf.
     nullable G sf <=>
     !sym. MEM sym sf
           ==> ?pt:(A,B,1)parsetree.
                 valid_ptree G pt /\ ptree_head pt = sym /\ ptree_fringe pt = []`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [nullable_by_singletons] THEN
  REWRITE_TAC[nullable_def] THEN
  MESON_TAC[singleton_derives_ptree; valid_ptree_derive]);;

(* HOL4: MEM_last_strip (local) *)

let LPARSEAUX_MEM_last_strip = prove
 (`!(l:A list) e. MEM e l ==> ?p s. l = APPEND (APPEND p [e]) s /\ ~MEM e s`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MEM] THEN GEN_TAC THEN
  ASM_CASES_TAC `MEM (e:A) t` THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `e:A`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:A list` (X_CHOOSE_THEN `s:A list`
      STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`CONS (h:A) p`; `s:A list`] THEN
    ASM_REWRITE_TAC[APPEND];
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
    MAP_EVERY EXISTS_TAC [`[]:A list`; `t:A list`] THEN
    ASM_REWRITE_TAC[APPEND]]);;

let LPARSEAUX_ALL_DISTINCT_APPEND = prove
 (`!(l1:A list) l2.
     ALL_DISTINCT (APPEND l1 l2) <=>
     ALL_DISTINCT l1 /\ ALL_DISTINCT l2 /\ !e. MEM e l1 ==> ~MEM e l2`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND; ALL_DISTINCT; MEM; MEM_APPEND] THEN
  MESON_TAC[]);;

let LPARSEAUX_ptree_nts_derive = prove
 (`!(G:(A,B)grammar) tk (pt:(A,B,1)parsetree) N rest.
     ptree_head pt = grammar_NT N /\ valid_ptree G pt /\
     ptree_fringe pt = CONS (grammar_TOK tk) rest
     ==> ?Ns. ALL_DISTINCT Ns /\ nts_derive G Ns tk /\ HD Ns = N`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC ptree_ind THEN CONJ_TAC THENL
   [REWRITE_TAC[FORALL_PAIR_THM; ptree_head_def; ptree_fringe_def; CONS_11] THEN
    MESON_TAC[symbol_distinct];
    ALL_TAC] THEN
  X_GEN_TAC `subs:((A,B,1)parsetree)list` THEN DISCH_THEN(LABEL_TAC "ih") THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`N0:B+num`; `l:1`; `N:B+num`;
                       `rest:((A,B)symbol)list`] THEN
  REWRITE_TAC[ptree_head_def; symbol_inject; valid_ptree_def;
              ptree_fringe_def; IN_SET_OF_LIST] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `N0:B+num = N`)) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP LPARSEAUX_heads_give_first o
    check (fun th -> is_eq(concl th) &&
                     (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "FLAT"
                      with Failure _ -> false))) THEN
  DISCH_THEN(X_CHOOSE_THEN `p:((A,B,1)parsetree)list` (X_CHOOSE_THEN
    `sym:(A,B,1)parsetree` (X_CHOOSE_THEN `s:((A,B,1)parsetree)list`
    (X_CHOOSE_THEN `r0:((A,B)symbol)list` STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `!x:(A,B,1)parsetree. MEM x subs ==> valid_ptree G x`
    (LABEL_TAC "vs") THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `nullable (G:(A,B)grammar)
                  (MAP ptree_head (p:((A,B,1)parsetree)list))` ASSUME_TAC THENL
   [REWRITE_TAC[nullable_alltrees; MEM_MAP] THEN REPEAT STRIP_TAC THEN
    EXISTS_TAC `x:(A,B,1)parsetree` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [USE_THEN "vs" MATCH_MP_TAC THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        is_eq(concl th) && is_var(rhs(concl th)) &&
        fst(dest_var(rhs(concl th))) = "subs")) THEN
      ASM_REWRITE_TAC[MEM_APPEND];
      UNDISCH_TAC `FLAT (MAP ptree_fringe (p:((A,B,1)parsetree)list)) = []` THEN
      REWRITE_TAC[LPARSEAUX_FLAT_MAP_EQ_NIL] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `APPEND (APPEND (MAP ptree_head (p:((A,B,1)parsetree)list))
                   [ptree_head (sym:(A,B,1)parsetree)])
           (MAP ptree_head (s:((A,B,1)parsetree)list))
    IN FAPPLY (grammar_rules (G:(A,B)grammar)) N`
    ASSUME_TAC THENL
   [UNDISCH_TAC `MAP ptree_head (subs:((A,B,1)parsetree)list) IN
                 FAPPLY (grammar_rules (G:(A,B)grammar)) N` THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        is_eq(concl th) && is_var(rhs(concl th)) &&
        fst(dest_var(rhs(concl th))) = "subs")) THEN
    REWRITE_TAC[MAP_APPEND; MAP];
    ALL_TAC] THEN
  SUBGOAL_THEN `MEM (sym:(A,B,1)parsetree) subs` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        is_eq(concl th) && is_var(rhs(concl th)) &&
        fst(dest_var(rhs(concl th))) = "subs")) THEN
    REWRITE_TAC[MEM_APPEND; MEM];
    ALL_TAC] THEN
  DISJ_CASES_TAC(ISPEC `sym:(A,B,1)parsetree` parsetree_nchotomy) THENL
   [(* a leaf: the token itself *)
    FIRST_X_ASSUM(X_CHOOSE_THEN `a:(A,B)symbol#1` SUBST_ALL_TAC) THEN
    MP_TAC(ISPEC `a:(A,B)symbol#1` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `x:(A,B)symbol` (X_CHOOSE_THEN `y:1`
      SUBST_ALL_TAC)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ptree_fringe_def; ptree_head_def; CONS_11]) THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th -> is_conj(concl th))) THEN
    RVEQ_TAC THEN
    EXISTS_TAC `[N:B+num]` THEN
    REWRITE_TAC[ALL_DISTINCT; MEM; HD; nts_derive_def] THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`MAP ptree_head (p:((A,B,1)parsetree)list)`;
                          `MAP ptree_head (s:((A,B,1)parsetree)list)`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* an inner node *)
  FIRST_X_ASSUM(X_CHOOSE_THEN `a0:(B+num)#1` (X_CHOOSE_THEN
    `a1:((A,B,1)parsetree)list` SUBST_ALL_TAC)) THEN
  MP_TAC(ISPEC `a0:(B+num)#1` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `x:B+num` (X_CHOOSE_THEN `y:1` SUBST_ALL_TAC)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ptree_head_def]) THEN
  REMOVE_THEN "ih" (MP_TAC o SPEC `grammar_Nd (x,y) a1:(A,B,1)parsetree`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`x:B+num`; `r0:((A,B)symbol)list`]) THEN
  ASM_REWRITE_TAC[ptree_head_def] THEN ANTS_TAC THENL
   [USE_THEN "vs" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Ns:(B+num)list` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `MEM (N:B+num) Ns` THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP LPARSEAUX_MEM_last_strip) THEN
    DISCH_THEN(X_CHOOSE_THEN `Ns0:(B+num)list` (X_CHOOSE_THEN
      `Ns1:(B+num)list` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `CONS (N:B+num) Ns1` THEN REWRITE_TAC[HD] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `ALL_DISTINCT (Ns:(B+num)list)` THEN
      ASM_REWRITE_TAC[GSYM APPEND_ASSOC; APPEND;
                      LPARSEAUX_ALL_DISTINCT_APPEND; ALL_DISTINCT] THEN
      MESON_TAC[];
      MATCH_MP_TAC nts_derive_APPEND_E THEN
      EXISTS_TAC `Ns0:(B+num)list` THEN
      REWRITE_TAC[NOT_CONS_NIL; APPEND] THEN
      UNDISCH_TAC `nts_derive (G:(A,B)grammar) Ns tk` THEN
      ASM_REWRITE_TAC[GSYM APPEND_ASSOC; APPEND]];
    ALL_TAC] THEN
  EXISTS_TAC `CONS (N:B+num) Ns` THEN ASM_REWRITE_TAC[HD; ALL_DISTINCT] THEN
  UNDISCH_TAC `nts_derive (G:(A,B)grammar) Ns tk` THEN
  UNDISCH_TAC `HD (Ns:(B+num)list) = x` THEN
  STRUCT_CASES_TAC(ISPEC `Ns:(B+num)list` list_CASES) THEN
  REWRITE_TAC[nts_derive_def; HD] THEN DISCH_THEN SUBST_ALL_TAC THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`MAP ptree_head (p:((A,B,1)parsetree)list)`;
                        `MAP ptree_head (s:((A,B,1)parsetree)list)`] THEN
  ASM_REWRITE_TAC[]);;

let firstSet_nts_derive = prove
 (`!(G:(A,B)grammar) tk N.
     tk IN firstSet G [grammar_NT N]
     ==> ?Ns. ALL_DISTINCT Ns /\ nts_derive G Ns tk /\ HD Ns = N`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP IN_firstSet) THEN
  MESON_TAC[LPARSEAUX_ptree_nts_derive]);;

let LPARSEAUX_firstSet_singleton_back = prove
 (`!(G:(A,B)grammar) p e s tk.
     nullable G p /\ tk IN firstSet G [e]
     ==> tk IN firstSet G (APPEND (APPEND p [e]) s)`,
  REWRITE_TAC[firstSet_def; IN_ELIM_THM; nullable_def] THEN
  REPEAT STRIP_TAC THEN EXISTS_TAC `APPEND rest s:((A,B)symbol)list` THEN
  SUBGOAL_THEN `CONS (grammar_TOK tk) (APPEND rest s):((A,B)symbol)list =
                APPEND (APPEND [] (CONS (grammar_TOK tk) rest)) s`
    SUBST1_TAC THENL [REWRITE_TAC[APPEND]; ALL_TAC] THEN
  MATCH_MP_TAC derives_paste_horizontally THEN REWRITE_TAC[RTC_REFL] THEN
  MATCH_MP_TAC derives_paste_horizontally THEN ASM_REWRITE_TAC[]);;

let LPARSEAUX_firstSet_singleton_imp = prove
 (`!(G:(A,B)grammar) sf tk.
     tk IN firstSet G sf
     ==> ?p e s. sf = APPEND (APPEND p [e]) s /\ nullable G p /\
                 tk IN firstSet G [e]`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[firstSet_NIL; NOT_IN_EMPTY] THEN X_GEN_TAC `tk:A` THEN
  STRUCT_CASES_TAC(ISPEC `h:(A,B)symbol` symbol_nchotomy) THENL
   [REWRITE_TAC[firstSet_TOK; IN_SING] THEN DISCH_THEN SUBST1_TAC THEN
    MAP_EVERY EXISTS_TAC [`[]:((A,B)symbol)list`; `grammar_TOK a:(A,B)symbol`;
                          `t:((A,B)symbol)list`] THEN
    REWRITE_TAC[APPEND; nullable_NIL; firstSet_TOK; IN_SING];
    ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [firstSet_NT] THEN
  COND_CASES_TAC THEN REWRITE_TAC[NOT_IN_EMPTY; IN_UNION] THEN
  STRIP_TAC THENL
   [MAP_EVERY EXISTS_TAC [`[]:((A,B)symbol)list`; `grammar_NT a:(A,B)symbol`;
                          `t:((A,B)symbol)list`] THEN
    ASM_REWRITE_TAC[APPEND; nullable_NIL; firstSet_NT; IN_UNION];
    ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[NOT_IN_EMPTY] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `tk:A` o check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:((A,B)symbol)list` (X_CHOOSE_THEN
    `e:(A,B)symbol` (X_CHOOSE_THEN `s:((A,B)symbol)list` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`CONS (grammar_NT a:(A,B)symbol) p`; `e:(A,B)symbol`;
                        `s:((A,B)symbol)list`] THEN
  ASM_REWRITE_TAC[APPEND] THEN
  UNDISCH_TAC `nullable (G:(A,B)grammar) [grammar_NT a]` THEN
  ASM_REWRITE_TAC[nullable_CONS_NT; nullable_NIL]);;

let firstSet_singleton = prove
 (`!(G:(A,B)grammar) sf tk.
     tk IN firstSet G sf <=>
     ?p e s. sf = APPEND (APPEND p [e]) s /\ nullable G p /\
             tk IN firstSet G [e]`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [MATCH_ACCEPT_TAC LPARSEAUX_firstSet_singleton_imp;
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LPARSEAUX_firstSet_singleton_back THEN ASM_REWRITE_TAC[]]);;

let firstSet_firstSetML = prove
 (`!(G:(A,B)grammar) sf tk.
     tk IN firstSet G sf ==> tk IN firstSetML G {} sf`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[firstSet_singleton] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:((A,B)symbol)list` (X_CHOOSE_THEN
    `e:(A,B)symbol` (X_CHOOSE_THEN `s:((A,B)symbol)list` STRIP_ASSUME_TAC))) THEN
  ASM_REWRITE_TAC[GSYM APPEND_ASSOC; APPEND] THEN
  MATCH_MP_TAC firstSetML_nullable_prefix THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC firstSetML_CONS_I THEN
  UNDISCH_TAC `(tk:A) IN firstSet (G:(A,B)grammar) [e]` THEN
  STRUCT_CASES_TAC(ISPEC `e:(A,B)symbol` symbol_nchotomy) THENL
   [REWRITE_TAC[firstSet_TOK; firstSetML_def]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP firstSet_nts_derive) THEN
  DISCH_THEN(X_CHOOSE_THEN `Ns:(B+num)list` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC distinct_nts_derive_firstSetML THEN
  ASM_REWRITE_TAC[INTER_EMPTY]);;

let firstSetML_eqn = prove
 (`!(G:(A,B)grammar) sf. firstSet G sf = firstSetML G {} sf`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  REWRITE_TAC[firstSetML_firstSet] THEN
  REWRITE_TAC[SUBSET] THEN MESON_TAC[firstSet_firstSetML]);;

(* ------------------------------------------------------------------------- *)
(* The HOL4 [simp] theorems of this theory, for the project simpset.         *)
(* ------------------------------------------------------------------------- *)

let _ = cake_add_simps
  [nullable_CONS_TOK; nullable_NIL; firstSet_NIL; firstSet_TOK;
   nts_derive_def];;
