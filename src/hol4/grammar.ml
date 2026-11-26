(* ========================================================================= *)
(* grammar: port of HOL4 examples/formal-languages/context-free/            *)
(* grammarScript.sml (HOL4 library used by CakeML v3479).                    *)
(* Context-free grammars, parse trees (with locations), derivations.        *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - HOL4's type abbreviation 'b inf is B + num (HOL Light abbreviations     *)
(*   take no parameters); lfptree (:(A,B,one) parsetree) is (A,B,1)parsetree. *)
(* - The record fields G.start and G.rules are grammar_start G and           *)
(*   grammar_rules G; f ' x is FAPPLY f x; set l is set_of_list l.           *)
(* - HOL4's overload derives G is RTC (derive G) (Library/rstc.ml).          *)
(* - ptree_fringe, real_fringe, valid_ptree and valid_locs recurse through   *)
(*   the child list; they are defined from the recursion theorem             *)
(*   LPARSEAUX_parsetree_MAP_RECURSION, with the HOL4 equations as theorems. *)
(* - Renamed (the bare names belong to other theories of the closure or of   *)
(*   the list layer): destTOK is grammar_destTOK (tokenUtils has destTOK);   *)
(*   the list lemmas FLAT_EQ_NIL, FLAT_EQ_SING, FLAT_EQ_APPEND that grammar  *)
(*   re-proves are grammar_FLAT_EQ_NIL, grammar_FLAT_EQ_SING,                *)
(*   grammar_FLAT_EQ_APPEND.                                                 *)
(* - Lemmas named LPARSEAUX_... are helpers of this unit (not HOL4 names).   *)
(* ========================================================================= *)

needs "hol4/vocab.ml";;
needs "hol4/finite_map.ml";;
needs "hol4/location.ml";;

(* ------------------------------------------------------------------------- *)
(* List helpers (list-layer lemmas, proved here for this unit).              *)
(* ------------------------------------------------------------------------- *)

let LPARSEAUX_FLAT_APPEND = prove
 (`!(l1:(A list)list) l2. FLAT (APPEND l1 l2) = APPEND (FLAT l1) (FLAT l2)`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[FLAT; APPEND; APPEND_ASSOC]);;

let LPARSEAUX_MAP_FLAT = prove
 (`!(f:A->B) l. MAP f (FLAT l) = FLAT (MAP (MAP f) l)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[FLAT; MAP; MAP_APPEND]);;

let LPARSEAUX_FLAT_MAP_SING = prove
 (`!l:A list. FLAT (MAP (\x. [x]) l) = l`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[FLAT; MAP; APPEND]);;

let LPARSEAUX_NIL_EQ_APPEND = prove
 (`!(l:A list) m. [] = APPEND l m <=> l = [] /\ m = []`,
  MESON_TAC[APPEND_EQ_NIL]);;

let LPARSEAUX_APPEND_EQ_CONS = prove
 (`!(l1:A list) l2 h t.
     APPEND l1 l2 = CONS h t <=>
     l1 = [] /\ l2 = CONS h t \/ (?l1'. l1 = CONS h l1' /\ t = APPEND l1' l2)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND; NOT_CONS_NIL; CONS_11] THEN
  MESON_TAC[]);;

let LPARSEAUX_APPEND_EQ_APPEND = prove
 (`!(l1:A list) l2 m1 m2.
     APPEND l1 l2 = APPEND m1 m2 <=>
     (?l. l1 = APPEND m1 l /\ m2 = APPEND l l2) \/
     (?l. m1 = APPEND l1 l /\ l2 = APPEND l m2)`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[APPEND; LPARSEAUX_NIL_EQ_APPEND] THEN REPEAT GEN_TAC THEN
    EQ_TAC THENL
     [DISCH_TAC THEN DISJ2_TAC THEN EXISTS_TAC `m1:A list` THEN
      ASM_REWRITE_TAC[];
      STRIP_TAC THEN ASM_REWRITE_TAC[APPEND]];
    ALL_TAC] THEN
  X_GEN_TAC `l2:A list` THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[APPEND; GSYM NOT_CONS_NIL; UNWIND_THM1] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  GEN_TAC THEN ASM_REWRITE_TAC[APPEND; CONS_11] THEN MESON_TAC[]);;

let LPARSEAUX_APPEND_EQ_SING = prove
 (`!(l1:A list) l2 x.
     APPEND l1 l2 = [x] <=> l1 = [x] /\ l2 = [] \/ l1 = [] /\ l2 = [x]`,
  REWRITE_TAC[LPARSEAUX_APPEND_EQ_CONS; LPARSEAUX_NIL_EQ_APPEND] THEN
  REWRITE_TAC[CONJ_ASSOC; RIGHT_EXISTS_AND_THM; LEFT_EXISTS_AND_THM] THEN
  MESON_TAC[]);;

let LPARSEAUX_SING_EQ_APPEND = prove
 (`!(l1:A list) l2 x.
     [x] = APPEND l1 l2 <=> l1 = [x] /\ l2 = [] \/ l1 = [] /\ l2 = [x]`,
  MESON_TAC[LPARSEAUX_APPEND_EQ_SING]);;

let LPARSEAUX_APPEND_SNOC_EQ_SING = prove
 (`!(p:A list) x s y.
     APPEND (APPEND p [x]) s = [y] <=> p = [] /\ s = [] /\ x = y`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(fun th -> MP_TAC th THEN
                         MP_TAC(AP_TERM `LENGTH:A list->num` th)) THEN
    REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN
    REWRITE_TAC[ARITH_RULE `(a + SUC 0) + b = SUC 0 <=> a = 0 /\ b = 0`] THEN
    REWRITE_TAC[LENGTH_EQ_NIL] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[APPEND; APPEND_NIL; CONS_11];
    STRIP_TAC THEN ASM_REWRITE_TAC[APPEND; APPEND_NIL]]);;

let LPARSEAUX_APPEND_EQ_APPEND_MID = prove
 (`!(l1:A list) e l2 m1 m2.
     APPEND (APPEND l1 [e]) l2 = APPEND m1 m2 <=>
     (?l. m1 = APPEND (APPEND l1 [e]) l /\ l2 = APPEND l m2) \/
     (?l. l1 = APPEND m1 l /\ m2 = APPEND (APPEND l [e]) l2)`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[LPARSEAUX_APPEND_EQ_APPEND] THEN
  REWRITE_TAC[LPARSEAUX_APPEND_EQ_APPEND] THEN
  REWRITE_TAC[LPARSEAUX_APPEND_EQ_SING; LPARSEAUX_NIL_EQ_APPEND;
              LPARSEAUX_SING_EQ_APPEND] THEN
  EQ_TAC THEN REPEAT STRIP_TAC THEN RVEQ_TAC THENL
   [DISJ2_TAC THEN EXISTS_TAC `l':A list`;
    DISJ1_TAC THEN EXISTS_TAC `[]:A list`;
    DISJ2_TAC THEN EXISTS_TAC `[]:A list`;
    DISJ1_TAC THEN EXISTS_TAC `l:A list`;
    DISJ2_TAC THEN EXISTS_TAC `l:A list`;
    DISJ1_TAC THEN EXISTS_TAC `APPEND l [e]:A list` THEN
    REWRITE_TAC[APPEND; APPEND_NIL; APPEND_ASSOC] THEN DISJ1_TAC THEN
    EXISTS_TAC `l:A list`] THEN
  REWRITE_TAC[APPEND; APPEND_NIL; APPEND_ASSOC]);;

let LPARSEAUX_MAP_EQ_CONS = prove
 (`!(f:A->B) l h t.
     MAP f l = CONS h t <=> ?x xs. l = CONS x xs /\ f x = h /\ MAP f xs = t`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP; NOT_CONS_NIL; GSYM NOT_CONS_NIL; CONS_11] THEN
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`h:A`; `t:A list`] THEN
    ASM_REWRITE_TAC[];
    STRIP_TAC THEN ASM_REWRITE_TAC[]]);;

let LPARSEAUX_MAP_EQ_SING = prove
 (`!(f:A->B) l h. MAP f l = [h] <=> ?x. l = [x] /\ f x = h`,
  REWRITE_TAC[LPARSEAUX_MAP_EQ_CONS; MAP_EQ_NIL] THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM; LEFT_EXISTS_AND_THM; UNWIND_THM1;
              UNWIND_THM2] THEN
  MESON_TAC[]);;

let LPARSEAUX_MAP_EQ_APPEND = prove
 (`!(f:A->B) l l1 l2.
     MAP f l = APPEND l1 l2 <=>
     ?m1 m2. l = APPEND m1 m2 /\ MAP f m1 = l1 /\ MAP f m2 = l2`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[MAP; LPARSEAUX_NIL_EQ_APPEND] THEN REPEAT GEN_TAC THEN
    EQ_TAC THENL
     [STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`[]:A list`; `[]:A list`] THEN
      ASM_REWRITE_TAC[MAP; APPEND];
      STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[MAP]];
    ALL_TAC] THEN
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[APPEND] THEN GEN_TAC THEN EQ_TAC THENL
     [DISCH_TAC THEN MAP_EVERY EXISTS_TAC [`[]:A list`; `CONS (h:A) t`] THEN
      ASM_REWRITE_TAC[APPEND; MAP];
      STRIP_TAC THEN GVS[MAP_EQ_NIL]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC) THEN GEN_TAC THEN
  ASM_REWRITE_TAC[MAP; APPEND; CONS_11] THEN
  REWRITE_TAC[LPARSEAUX_MAP_EQ_CONS] THEN EQ_TAC THEN STRIP_TAC THENL
   [MAP_EVERY EXISTS_TAC [`CONS (h:A) m1`; `m2:A list`] THEN
    ASM_REWRITE_TAC[APPEND; CONS_11] THEN
    MAP_EVERY EXISTS_TAC [`h:A`; `m1:A list`] THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `CONS (h:A) t = APPEND m1 m2` THEN
    ASM_REWRITE_TAC[APPEND; CONS_11] THEN STRIP_TAC THEN RVEQ_TAC THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`xs:A list`; `m2:A list`] THEN ASM_REWRITE_TAC[]]);;

(* a non-empty segment in the middle of a FLAT: the element of the list of  *)
(* lists that contains it                                                    *)

let LPARSEAUX_FLAT_EQ_MID = prove
 (`!(ls:(A list)list) p x s.
     FLAT ls = APPEND (APPEND p [x]) s ==>
     ?l1 m l2 ip is.
       ls = APPEND (APPEND l1 [m]) l2 /\ p = APPEND (FLAT l1) ip /\
       s = APPEND is (FLAT l2) /\ m = APPEND (APPEND ip [x]) is`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[FLAT; LPARSEAUX_NIL_EQ_APPEND; APPEND_EQ_NIL; NOT_CONS_NIL];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[FLAT] THEN
  ONCE_REWRITE_TAC[LPARSEAUX_APPEND_EQ_APPEND] THEN STRIP_TAC THENL
   [(* the segment p ++ [x] ends inside h *)
    MAP_EVERY EXISTS_TAC [`[]:(A list)list`; `h:A list`; `t:(A list)list`;
                          `p:A list`; `l:A list`] THEN
    ASM_REWRITE_TAC[APPEND; FLAT; APPEND_NIL];
    ALL_TAC] THEN
  (* h is a prefix of p ++ [x] *)
  UNDISCH_TAC `APPEND (p:A list) [x] = APPEND h l` THEN
  ONCE_REWRITE_TAC[LPARSEAUX_APPEND_EQ_APPEND] THEN
  REWRITE_TAC[LPARSEAUX_SING_EQ_APPEND] THEN STRIP_TAC THEN RVEQ_TAC THENL
   [(* p = h ++ l' and FLAT t = l' ++ [x] ++ s *)
    FIRST_X_ASSUM(MP_TAC o SPECL [`l':A list`; `x:A`; `s:A list`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[GSYM APPEND_ASSOC]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `l1:(A list)list` (X_CHOOSE_THEN `m:A list`
     (X_CHOOSE_THEN `l2:(A list)list` (X_CHOOSE_THEN `ip:A list`
     (X_CHOOSE_THEN `is:A list` STRIP_ASSUME_TAC))))) THEN
    MAP_EVERY EXISTS_TAC [`CONS (h:A list) l1`; `m:A list`; `l2:(A list)list`;
                          `ip:A list`; `is:A list`] THEN
    ASM_REWRITE_TAC[APPEND; FLAT; APPEND_ASSOC];
    (* h = p ++ [x] *)
    MAP_EVERY EXISTS_TAC [`[]:(A list)list`; `APPEND (p:A list) [x]`;
                          `t:(A list)list`; `p:A list`; `[]:A list`] THEN
    ASM_REWRITE_TAC[APPEND; FLAT; APPEND_NIL];
    (* h = p, l = [x] *)
    FIRST_X_ASSUM(MP_TAC o SPECL [`[]:A list`; `x:A`; `s:A list`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[APPEND]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `l1:(A list)list` (X_CHOOSE_THEN `m:A list`
     (X_CHOOSE_THEN `l2:(A list)list` (X_CHOOSE_THEN `ip:A list`
     (X_CHOOSE_THEN `is:A list` STRIP_ASSUME_TAC))))) THEN
    MAP_EVERY EXISTS_TAC [`CONS (p:A list) l1`; `m:A list`; `l2:(A list)list`;
                          `ip:A list`; `is:A list`] THEN
    ASM_REWRITE_TAC[APPEND; FLAT; APPEND_ASSOC; APPEND_NIL] THEN
    UNDISCH_TAC `[]:A list = APPEND (FLAT l1) ip` THEN
    REWRITE_TAC[LPARSEAUX_NIL_EQ_APPEND] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[APPEND_NIL]]);;

let LPARSEAUX_SING_EQ_APPEND_SNOC = prove
 (`!(p:A list) x s y.
     [y] = APPEND (APPEND p [x]) s <=> p = [] /\ s = [] /\ x = y`,
  MESON_TAC[LPARSEAUX_APPEND_SNOC_EQ_SING]);;

(* ------------------------------------------------------------------------- *)
(* Symbols.                                                                  *)
(* ------------------------------------------------------------------------- *)

let symbol_INDUCT,symbol_RECURSION = cake_type
  "symbol = grammar_TOK A | grammar_NT (B + num)";;

let symbol_distinct = distinctness "symbol";;
let symbol_inject = injectivity "symbol";;
let symbol_CASE = case_def "symbol";;
let symbol_case_eq = case_eq "symbol";;
let symbol_nchotomy = cases "symbol";;

let isTOK_def = cake_def
  `(isTOK (grammar_TOK (tok:A):(A,B)symbol) <=> T) /\
   (isTOK (grammar_NT (n:B+num):(A,B)symbol) <=> F)`;;

(* HOL4: destTOK (TOK tk, _) = SOME tk /\ destTOK _ = NONE *)

let grammar_destTOK_def = cake_def
  `(grammar_destTOK (grammar_TOK (tk:A):(A,B)symbol, (l:C)) = SOME tk) /\
   (grammar_destTOK (grammar_NT (n:B+num):(A,B)symbol, (l:C)) = NONE)`;;

(* ------------------------------------------------------------------------- *)
(* Grammars and parse trees.                                                 *)
(* ------------------------------------------------------------------------- *)

let grammar_FIELDS = cake_record "grammar"
  ["start","B + num"; "rules","(B + num,((A,B)symbol)list->bool)fmap"];;

let grammar_component_equality =
  (record_info "grammar").ri_component_equality;;

let parsetree_INDUCT,parsetree_RECURSION = cake_type
  "parsetree = grammar_Lf ((A,B)symbol # C) | grammar_Nd ((B + num) # C) (parsetree list)";;

let parsetree_distinct = distinctness "parsetree";;
let parsetree_inject = injectivity "parsetree";;
let parsetree_CASE = case_def "parsetree";;
let parsetree_case_eq = case_eq "parsetree";;
let parsetree_nchotomy = CONJUNCT1 (cases "parsetree");;
let parsetree_size_def = size_def "parsetree";;

(* the recursion theorem for functions that recurse through MAP over the     *)
(* children of a node                                                        *)

let LPARSEAUX_parsetree_MAP_RECURSION = prove
 (`!(f0:(A,B)symbol#C->Z) (f1:(B+num)#C->((A,B,C)parsetree)list->Z list->Z).
     ?fn. (!a. fn (grammar_Lf a) = f0 a) /\
          (!a0 a1. fn (grammar_Nd a0 a1) = f1 a0 a1 (MAP fn a1))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL
    [`f0:(A,B)symbol#C->Z`;
     `\(a0:(B+num)#C) (a1:((A,B,C)parsetree)list) (r:Z list).
        (f1:(B+num)#C->((A,B,C)parsetree)list->Z list->Z) a0 a1 r`;
     `[]:Z list`;
     `\(h:(A,B,C)parsetree) (t:((A,B,C)parsetree)list) (x:Z) (y:Z list).
        CONS x y`]
    parsetree_RECURSION) THEN
  REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `fn0:((A,B,C)parsetree)list->Z list`
   (X_CHOOSE_THEN `fn1:(A,B,C)parsetree->Z` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `fn1:(A,B,C)parsetree->Z` THEN
  SUBGOAL_THEN `!l. (fn0:((A,B,C)parsetree)list->Z list) l = MAP fn1 l`
   ASSUME_TAC THENL
   [LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP]; ASM_REWRITE_TAC[]]);;

(* HOL4's induction principle of parsetree: the IH holds for every child *)

let ptree_ind = prove
 (`!P:(A,B,C)parsetree->bool.
     (!p. P (grammar_Lf p)) /\
     (!subs. (!a. MEM a subs ==> P a) ==> !p. P (grammar_Nd p subs))
     ==> !pt. P pt`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`P:(A,B,C)parsetree->bool`;
                 `\l:((A,B,C)parsetree)list. !a. MEM a l ==> P a`]
                parsetree_INDUCT) THEN
  REWRITE_TAC[MEM] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[]; SIMP_TAC[]]);;

let ptree_loc_def = cake_def
  `(ptree_loc (grammar_Lf (s:(A,B)symbol, (l:C))) = l) /\
   (ptree_loc (grammar_Nd (n:B+num, (l:C)) (children:((A,B,C)parsetree)list)) = l)`;;

let ptree_list_loc_def = new_definition
  `ptree_list_loc (l:((A,B,locs)parsetree)list) =
     merge_list_locs (MAP ptree_loc l)`;;

let ptree_head_def = cake_def
  `(ptree_head (grammar_Lf (tok:(A,B)symbol, (l:C))) = tok) /\
   (ptree_head (grammar_Nd (nt:B+num, (l:C)) (children:((A,B,C)parsetree)list)) =
      grammar_NT nt)`;;

let valid_ptree_def = new_specification ["valid_ptree"]
 (prove
  (`?valid_ptree.
      (!(G:(A,B)grammar) (p:(A,B)symbol#C). valid_ptree G (grammar_Lf p) <=> T) /\
      (!(G:(A,B)grammar) nt (l:C) children.
         valid_ptree G (grammar_Nd (nt,l) children) <=>
         nt IN FDOM (grammar_rules G) /\
         MAP ptree_head children IN FAPPLY (grammar_rules G) nt /\
         !pt. pt IN set_of_list children ==> valid_ptree G pt)`,
   REWRITE_TAC[AND_FORALL_THM; GSYM SKOLEM_THM] THEN
   X_GEN_TAC `G:(A,B)grammar` THEN
   MP_TAC(ISPECL
    [`\p:(A,B)symbol#C. T`;
     `\(x:(B+num)#C) (children:((A,B,C)parsetree)list) (r:bool list).
        FST x IN FDOM (grammar_rules (G:(A,B)grammar)) /\
        MAP ptree_head children IN FAPPLY (grammar_rules G) (FST x) /\
        ALL (\b. b) r`]
    LPARSEAUX_parsetree_MAP_RECURSION) THEN
   MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
   REWRITE_TAC[ALL_MAP; o_DEF] THEN REWRITE_TAC[GSYM ALL_MEM; IN_SET_OF_LIST] THEN
   SIMP_TAC[]));;

let ptree_fringe_def = new_specification ["ptree_fringe"]
 (prove
  (`?ptree_fringe.
      (!(t:(A,B)symbol) (l:C). ptree_fringe (grammar_Lf (t,l)) = [t]) /\
      (!(x:(B+num)#C) (children:((A,B,C)parsetree)list).
         ptree_fringe (grammar_Nd x children) = FLAT (MAP ptree_fringe children))`,
   MP_TAC(ISPECL
    [`\p:(A,B)symbol#C. [FST p]`;
     `\(x:(B+num)#C) (children:((A,B,C)parsetree)list)
       (r:(((A,B)symbol)list)list). FLAT r`]
    LPARSEAUX_parsetree_MAP_RECURSION) THEN
   MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[]));;

let complete_ptree_def = new_definition
  `complete_ptree (G:(A,B)grammar) (pt:(A,B,C)parsetree) <=>
     valid_ptree G pt /\ ptree_head pt = grammar_NT (grammar_start G) /\
     !t. t IN set_of_list (ptree_fringe pt) ==> isTOK t`;;

let real_fringe_def = new_specification ["real_fringe"]
 (prove
  (`?real_fringe.
      (!t:(A,B)symbol#C. real_fringe (grammar_Lf t) = [t]) /\
      (!(n:(B+num)#C) (ptl:((A,B,C)parsetree)list).
         real_fringe (grammar_Nd n ptl) = FLAT (MAP real_fringe ptl))`,
   MP_TAC(ISPECL
    [`\p:(A,B)symbol#C. [p]`;
     `\(x:(B+num)#C) (children:((A,B,C)parsetree)list)
       (r:(((A,B)symbol#C)list)list). FLAT r`]
    LPARSEAUX_parsetree_MAP_RECURSION) THEN
   MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[]));;

let MAP_TKI_11 = prove
 (`!l1 l2:(A#C)list.
     MAP ((grammar_TOK:A->(A,B)symbol) ## (I:C->C)) l1 = MAP (grammar_TOK ## I) l2 <=>
     l1 = l2`,
  REPEAT GEN_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN
  MATCH_MP_TAC(MESON[] `(!l m. MAP (f:A#C->(A,B)symbol#C) l = MAP f m ==> l = m)
                        ==> MAP f l1 = MAP f l2 ==> l1 = l2`) THEN
  REWRITE_TAC[INJECTIVE_MAP; FORALL_PAIR_THM; PAIR_MAP_THM; I_THM; PAIR_EQ;
              symbol_inject] THEN
  MESON_TAC[]);;

let ptree_fringe_real_fringe = prove
 (`!pt:(A,B,C)parsetree. ptree_fringe pt = MAP FST (real_fringe pt)`,
  MATCH_MP_TAC ptree_ind THEN
  REWRITE_TAC[FORALL_PAIR_THM; ptree_fringe_def; real_fringe_def; MAP] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[LPARSEAUX_MAP_FLAT; MAP_o] THEN
  AP_TERM_TAC THEN REWRITE_TAC[GSYM MAP_o] THEN MATCH_MP_TAC MAP_EQ THEN
  REWRITE_TAC[GSYM ALL_MEM; o_THM] THEN ASM_MESON_TAC[]);;

let LENGTH_real_fringe = prove
 (`!pt:(A,B,C)parsetree. LENGTH (real_fringe pt) = LENGTH (ptree_fringe pt)`,
  REWRITE_TAC[ptree_fringe_real_fringe; LENGTH_MAP]);;

(* ------------------------------------------------------------------------- *)
(* Locations in parse trees.                                                 *)
(* ------------------------------------------------------------------------- *)

let valid_locs_def = new_specification ["valid_locs"]
 (prove
  (`?valid_locs.
      (!p:(A,B)symbol#locs. valid_locs (grammar_Lf p) <=> T) /\
      (!(n:B+num) l (children:((A,B,locs)parsetree)list).
         valid_locs (grammar_Nd (n,l) children) <=>
         l = merge_list_locs (MAP ptree_loc children) /\
         !pt. MEM pt children ==> valid_locs pt)`,
   MP_TAC(ISPECL
    [`\p:(A,B)symbol#locs. T`;
     `\(x:(B+num)#locs) (children:((A,B,locs)parsetree)list) (r:bool list).
        SND x = merge_list_locs (MAP ptree_loc children) /\ ALL (\b. b) r`]
    LPARSEAUX_parsetree_MAP_RECURSION) THEN
   MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
   REWRITE_TAC[ALL_MAP; o_DEF] THEN REWRITE_TAC[GSYM ALL_MEM] THEN
   SIMP_TAC[]));;

let valid_lptree_def = new_definition
  `valid_lptree (G:(A,B)grammar) (pt:(A,B,locs)parsetree) <=>
     valid_locs pt /\ valid_ptree G pt`;;

let valid_lptree_thm = prove
 (`(!(G:(A,B)grammar) p. valid_lptree G (grammar_Lf p) <=> T) /\
   (!(G:(A,B)grammar) n l children.
      valid_lptree G (grammar_Nd (n,l) children) <=>
      l = merge_list_locs (MAP ptree_loc children) /\
      n IN FDOM (grammar_rules G) /\
      MAP ptree_head children IN FAPPLY (grammar_rules G) n /\
      !pt. MEM pt children ==> valid_lptree G pt)`,
  REWRITE_TAC[valid_lptree_def; valid_locs_def; valid_ptree_def;
              IN_SET_OF_LIST] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Languages and derivations.                                                *)
(* ------------------------------------------------------------------------- *)

let language_def = new_definition
  `language (G:(A,B)grammar) =
     {ts | ?pt:(A,B,1)parsetree.
             complete_ptree G pt /\ ptree_fringe pt = MAP grammar_TOK ts}`;;

let derive_def = new_definition
  `derive (G:(A,B)grammar) sf1 sf2 <=>
     ?p sym rhs s. sf1 = APPEND (APPEND p [grammar_NT sym]) s /\
                   sf2 = APPEND (APPEND p rhs) s /\
                   sym IN FDOM (grammar_rules G) /\
                   rhs IN FAPPLY (grammar_rules G) sym`;;

let derive_common_prefix = prove
 (`!(G:(A,B)grammar) sf1 sf2 p.
     derive G sf1 sf2 ==> derive G (APPEND p sf1) (APPEND p sf2)`,
  REWRITE_TAC[derive_def] THEN REPEAT STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`APPEND (p:((A,B)symbol)list) p'`; `sym:B+num`;
                        `rhs:((A,B)symbol)list`; `s:((A,B)symbol)list`] THEN
  ASM_REWRITE_TAC[APPEND_ASSOC]);;

let derive_common_suffix = prove
 (`!(G:(A,B)grammar) sf1 sf2 s.
     derive G sf1 sf2 ==> derive G (APPEND sf1 s) (APPEND sf2 s)`,
  REWRITE_TAC[derive_def] THEN REPEAT STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`p:((A,B)symbol)list`; `sym:B+num`;
                        `rhs:((A,B)symbol)list`;
                        `APPEND (s':((A,B)symbol)list) s`] THEN
  ASM_REWRITE_TAC[APPEND_ASSOC]);;

let derive_paste_horizontally = prove
 (`!(G:(A,B)grammar) sf11 sf12 sf21 sf22.
     derive G sf11 sf12 /\ derive G sf21 sf22
     ==> RTC (derive G) (APPEND sf11 sf21) (APPEND sf12 sf22)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RTC_TRANS THEN
  EXISTS_TAC `APPEND (sf12:((A,B)symbol)list) sf21` THEN
  CONJ_TAC THEN MATCH_MP_TAC RTC_INC THEN
  ASM_MESON_TAC[derive_common_prefix; derive_common_suffix]);;

let derive_1NT = prove
 (`!(G:(A,B)grammar) s l.
     derive G [grammar_NT s] l <=>
     s IN FDOM (grammar_rules G) /\ l IN FAPPLY (grammar_rules G) s`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[derive_def; LPARSEAUX_SING_EQ_APPEND_SNOC; symbol_inject] THEN
  EQ_TAC THENL
   [STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[APPEND; APPEND_NIL];
    STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`[]:((A,B)symbol)list`; `s:B+num`; `l:((A,B)symbol)list`;
                          `[]:((A,B)symbol)list`] THEN
    ASM_REWRITE_TAC[APPEND; APPEND_NIL]]);;

let derives_common_prefix = prove
 (`!(G:(A,B)grammar) sf1 sf2 p.
     RTC (derive G) sf1 sf2 ==> RTC (derive G) (APPEND p sf1) (APPEND p sf2)`,
  GEN_TAC THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  REPEAT GEN_TAC THEN
  SPEC_TAC(`sf2:((A,B)symbol)list`,`sf2:((A,B)symbol)list`) THEN
  SPEC_TAC(`sf1:((A,B)symbol)list`,`sf1:((A,B)symbol)list`) THEN
  MATCH_MP_TAC RTC_INDUCT THEN
  MESON_TAC[RTC_INC; RTC_REFL; RTC_TRANS; derive_common_prefix]);;

let derives_common_suffix = prove
 (`!(G:(A,B)grammar) sf1 sf2 s.
     RTC (derive G) sf1 sf2 ==> RTC (derive G) (APPEND sf1 s) (APPEND sf2 s)`,
  GEN_TAC THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  REPEAT GEN_TAC THEN
  SPEC_TAC(`sf2:((A,B)symbol)list`,`sf2:((A,B)symbol)list`) THEN
  SPEC_TAC(`sf1:((A,B)symbol)list`,`sf1:((A,B)symbol)list`) THEN
  MATCH_MP_TAC RTC_INDUCT THEN
  MESON_TAC[RTC_INC; RTC_REFL; RTC_TRANS; derive_common_suffix]);;

let derives_paste_horizontally = prove
 (`!(G:(A,B)grammar) sf11 sf12 sf21 sf22.
     RTC (derive G) sf11 sf12 /\ RTC (derive G) sf21 sf22
     ==> RTC (derive G) (APPEND sf11 sf21) (APPEND sf12 sf22)`,
  MESON_TAC[RTC_TRANS; derives_common_prefix; derives_common_suffix]);;

let LPARSEAUX_CONS_APPEND = prove
 (`!(x:A) l. CONS x l = APPEND [x] l`,
  REWRITE_TAC[APPEND]);;

let LPARSEAUX_derives_children = prove
 (`!(G:(A,B)grammar) (subs:((A,B,C)parsetree)list).
     (!a. MEM a subs ==> RTC (derive G) [ptree_head a] (ptree_fringe a))
     ==> RTC (derive G) (MAP ptree_head subs) (FLAT (MAP ptree_fringe subs))`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP; FLAT; RTC_REFL; MEM] THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[LPARSEAUX_CONS_APPEND] THEN
  MATCH_MP_TAC derives_paste_horizontally THEN ASM_MESON_TAC[]);;

let valid_ptree_derive = prove
 (`!(G:(A,B)grammar) (pt:(A,B,C)parsetree).
     valid_ptree G pt ==> RTC (derive G) [ptree_head pt] (ptree_fringe pt)`,
  GEN_TAC THEN MATCH_MP_TAC ptree_ind THEN
  REWRITE_TAC[FORALL_PAIR_THM; ptree_head_def; ptree_fringe_def; RTC_REFL;
              valid_ptree_def; IN_SET_OF_LIST] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RTC_TRANS_R THEN
  EXISTS_TAC `MAP ptree_head (subs:((A,B,C)parsetree)list)` THEN
  ASM_REWRITE_TAC[derive_1NT] THEN MATCH_MP_TAC LPARSEAUX_derives_children THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* List lemmas of this theory (the list layer has them as FLAT_EQ_...).      *)
(* ------------------------------------------------------------------------- *)

let grammar_FLAT_EQ_NIL = prove
 (`!l:(A list)list. FLAT l = [] <=> !e. MEM e l ==> e = []`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[FLAT; MEM; APPEND_EQ_NIL] THEN
  MESON_TAC[]);;

let grammar_FLAT_EQ_SING = prove
 (`!(l:(A list)list) x.
     FLAT l = [x] <=>
     ?p s. l = APPEND (APPEND p [[x]]) s /\ FLAT p = [] /\ FLAT s = []`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`l:(A list)list`; `[]:A list`; `x:A`; `[]:A list`]
                  LPARSEAUX_FLAT_EQ_MID) THEN
    ASM_REWRITE_TAC[APPEND; LPARSEAUX_NIL_EQ_APPEND] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`l1:(A list)list`; `l2:(A list)list`] THEN
    RVEQ_TAC THEN ASM_REWRITE_TAC[APPEND; APPEND_NIL];
    STRIP_TAC THEN
    ASM_REWRITE_TAC[LPARSEAUX_FLAT_APPEND; FLAT; APPEND; APPEND_NIL]]);;

let grammar_FLAT_EQ_APPEND = prove
 (`!(l:(A list)list) x y.
     FLAT l = APPEND x y <=>
     (?p s. l = APPEND p s /\ x = FLAT p /\ y = FLAT s) \/
     (?p s ip is.
        l = APPEND (APPEND p [APPEND ip is]) s /\ ~(ip = []) /\ ~(is = []) /\
        x = APPEND (FLAT p) ip /\ y = APPEND is (FLAT s))`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [ALL_TAC;
    STRIP_TAC THEN
    ASM_REWRITE_TAC[LPARSEAUX_FLAT_APPEND; FLAT; APPEND; APPEND_NIL;
                    APPEND_ASSOC]] THEN
  SPEC_TAC(`y:A list`,`y:A list`) THEN SPEC_TAC(`x:A list`,`x:A list`) THEN
  SPEC_TAC(`l:(A list)list`,`l:(A list)list`) THEN
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[FLAT; LPARSEAUX_NIL_EQ_APPEND] THEN REPEAT STRIP_TAC THEN
    DISJ1_TAC THEN
    MAP_EVERY EXISTS_TAC [`[]:(A list)list`; `[]:(A list)list`] THEN
    ASM_REWRITE_TAC[FLAT; APPEND];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[FLAT] THEN
  ONCE_REWRITE_TAC[LPARSEAUX_APPEND_EQ_APPEND] THEN STRIP_TAC THENL
   [ASM_CASES_TAC `x:A list = []` THENL
     [DISJ1_TAC THEN
      MAP_EVERY EXISTS_TAC [`[]:(A list)list`; `CONS (h:A list) t`] THEN
      RVEQ_TAC THEN ASM_REWRITE_TAC[FLAT; APPEND];
      ALL_TAC] THEN
    ASM_CASES_TAC `l:A list = []` THENL
     [DISJ1_TAC THEN
      MAP_EVERY EXISTS_TAC [`[h:A list]`; `t:(A list)list`] THEN
      RVEQ_TAC THEN ASM_REWRITE_TAC[FLAT; APPEND; APPEND_NIL];
      ALL_TAC] THEN
    DISJ2_TAC THEN
    MAP_EVERY EXISTS_TAC [`[]:(A list)list`; `t:(A list)list`; `x:A list`;
                          `l:A list`] THEN
    ASM_REWRITE_TAC[FLAT; APPEND];
    FIRST_X_ASSUM(MP_TAC o SPECL [`l:A list`; `y:A list`]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
     [DISJ1_TAC THEN
      MAP_EVERY EXISTS_TAC [`CONS (h:A list) p`; `s:(A list)list`] THEN
      ASM_REWRITE_TAC[FLAT; APPEND];
      DISJ2_TAC THEN
      MAP_EVERY EXISTS_TAC [`CONS (h:A list) p`; `s:(A list)list`;
                            `ip:A list`; `is:A list`] THEN
      ASM_REWRITE_TAC[FLAT; APPEND; APPEND_ASSOC]]]);;

(* ------------------------------------------------------------------------- *)
(* Parse trees and derivations.                                              *)
(* ------------------------------------------------------------------------- *)

let LPARSEAUX_ONE_EQ = prove
 (`!y:1. y = one <=> T`,
  MESON_TAC[one]);;

let fringe_element = prove
 (`!(pt:(A,B,1)parsetree) p x s.
     ptree_fringe pt = APPEND (APPEND p [x]) s
     ==> pt = grammar_Lf (x,one) /\ p = [] /\ s = [] \/
         ?nt ip is ts1 xpt ts2.
           pt = grammar_Nd (nt,one) (APPEND (APPEND ts1 [xpt]) ts2) /\
           p = APPEND (FLAT (MAP ptree_fringe ts1)) ip /\
           s = APPEND is (FLAT (MAP ptree_fringe ts2)) /\
           ptree_fringe xpt = APPEND (APPEND ip [x]) is`,
  GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `pt:(A,B,1)parsetree` parsetree_nchotomy) THENL
   [MAP_EVERY (fun t -> STRUCT_CASES_TAC (ISPEC t PAIR_SURJECTIVE))
      [`a:(A,B)symbol#1`] THEN
    REWRITE_TAC[ptree_fringe_def; LPARSEAUX_SING_EQ_APPEND_SNOC;
                parsetree_distinct; parsetree_inject; PAIR_EQ;
                LPARSEAUX_ONE_EQ] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY (fun t -> STRUCT_CASES_TAC (ISPEC t PAIR_SURJECTIVE))
    [`a0:(B+num)#1`] THEN
  REWRITE_TAC[ptree_fringe_def; parsetree_distinct; parsetree_inject;
              PAIR_EQ; LPARSEAUX_ONE_EQ] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP LPARSEAUX_FLAT_EQ_MID) THEN
  REWRITE_TAC[LPARSEAUX_MAP_EQ_APPEND; LPARSEAUX_MAP_EQ_SING] THEN
  STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`x:B+num`; `ip:((A,B)symbol)list`;
                        `is:((A,B)symbol)list`; `m1':((A,B,1)parsetree)list`;
                        `x'':(A,B,1)parsetree`; `m2:((A,B,1)parsetree)list`] THEN
  ASM_REWRITE_TAC[]);;

let LPARSEAUX_derive_fringe_Lf = prove
 (`!(G:(A,B)grammar) (p:(A,B)symbol#1) sf.
     derive G (ptree_fringe (grammar_Lf p)) sf
     ==> ?pt':(A,B,1)parsetree.
           ptree_head pt' = ptree_head (grammar_Lf p) /\ valid_ptree G pt' /\
           ptree_fringe pt' = sf`,
  REWRITE_TAC[FORALL_PAIR_THM; ptree_fringe_def; ptree_head_def] THEN
  REWRITE_TAC[derive_def; LPARSEAUX_SING_EQ_APPEND_SNOC] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  EXISTS_TAC `grammar_Nd (sym,one) (MAP (\x. grammar_Lf (x,one)) rhs):(A,B,1)parsetree` THEN
  ASM_REWRITE_TAC[ptree_head_def; ptree_fringe_def; valid_ptree_def;
                  APPEND; APPEND_NIL; GSYM MAP_o; o_DEF; MAP_ID;
                  LPARSEAUX_FLAT_MAP_SING; IN_SET_OF_LIST; MEM_MAP] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[valid_ptree_def]);;

let LPARSEAUX_derive_fringe_Nd = prove
 (`!(G:(A,B)grammar) rootnt (y:1) (subs:((A,B,1)parsetree)list) sf.
     (!a. MEM a subs
          ==> !sf. derive G (ptree_fringe a) sf /\ valid_ptree G a
                   ==> ?pt':(A,B,1)parsetree. ptree_head pt' = ptree_head a /\
                             valid_ptree G pt' /\ ptree_fringe pt' = sf) /\
     derive G (ptree_fringe (grammar_Nd (rootnt,y) subs)) sf /\
     valid_ptree G (grammar_Nd (rootnt,y) subs)
     ==> ?pt':(A,B,1)parsetree.
               ptree_head pt' = ptree_head (grammar_Nd (rootnt,y) subs) /\
               valid_ptree G pt' /\ ptree_fringe pt' = sf`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih")
    (CONJUNCTS_THEN2 MP_TAC (LABEL_TAC "valid"))) THEN
  REWRITE_TAC[derive_def] THEN
  DISCH_THEN(X_CHOOSE_THEN `pfx:((A,B)symbol)list` (X_CHOOSE_THEN `nt:B+num`
    (X_CHOOSE_THEN `rhs:((A,B)symbol)list`
    (X_CHOOSE_THEN `sfx:((A,B)symbol)list` STRIP_ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`grammar_Nd (rootnt,y) subs:(A,B,1)parsetree`;
                 `pfx:((A,B)symbol)list`; `grammar_NT nt:(A,B)symbol`;
                 `sfx:((A,B)symbol)list`] fringe_element) THEN
  ASM_REWRITE_TAC[parsetree_distinct; parsetree_inject; PAIR_EQ] THEN
  DISCH_THEN(X_CHOOSE_THEN `nt':B+num` (X_CHOOSE_THEN `ip:((A,B)symbol)list`
    (X_CHOOSE_THEN `is:((A,B)symbol)list`
    (X_CHOOSE_THEN `ts1:((A,B,1)parsetree)list`
    (X_CHOOSE_THEN `xpt:(A,B,1)parsetree`
    (X_CHOOSE_THEN `ts2:((A,B,1)parsetree)list` STRIP_ASSUME_TAC)))))) THEN
  RVEQ_TAC THEN
  REMOVE_THEN "valid" MP_TAC THEN
  REWRITE_TAC[valid_ptree_def; IN_SET_OF_LIST; MEM_APPEND; MEM] THEN
  STRIP_TAC THEN
  REMOVE_THEN "ih" (MP_TAC o SPEC `xpt:(A,B,1)parsetree`) THEN
  REWRITE_TAC[MEM_APPEND; MEM] THEN
  DISCH_THEN(MP_TAC o SPEC `APPEND (APPEND ip rhs) is:((A,B)symbol)list`) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    ASM_REWRITE_TAC[derive_def] THEN
    MAP_EVERY EXISTS_TAC [`ip:((A,B)symbol)list`; `nt:B+num`;
                          `rhs:((A,B)symbol)list`; `is:((A,B)symbol)list`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `pt2:(A,B,1)parsetree` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `grammar_Nd (nt',one) (APPEND (APPEND ts1 [pt2]) ts2):(A,B,1)parsetree` THEN
  ASM_REWRITE_TAC[ptree_head_def; valid_ptree_def; ptree_fringe_def;
                  IN_SET_OF_LIST; MEM_APPEND; MEM; MAP_APPEND; MAP;
                  LPARSEAUX_FLAT_APPEND; FLAT; APPEND_NIL] THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `MAP ptree_head (APPEND (APPEND (ts1:((A,B,1)parsetree)list)
                   [xpt]) ts2) IN FAPPLY (grammar_rules (G:(A,B)grammar)) nt'` THEN
    REWRITE_TAC[MAP_APPEND; MAP];
    X_GEN_TAC `pt:(A,B,1)parsetree` THEN
    ASM_CASES_TAC `pt:(A,B,1)parsetree = pt2` THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[APPEND_ASSOC]]);;

let derive_fringe = prove
 (`!(G:(A,B)grammar) (pt:(A,B,1)parsetree) sf.
     derive G (ptree_fringe pt) sf /\ valid_ptree G pt
     ==> ?pt':(A,B,1)parsetree.
           ptree_head pt' = ptree_head pt /\ valid_ptree G pt' /\
           ptree_fringe pt' = sf`,
  GEN_TAC THEN MATCH_MP_TAC ptree_ind THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC LPARSEAUX_derive_fringe_Lf THEN
    ASM_REWRITE_TAC[];
    GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC LPARSEAUX_derive_fringe_Nd THEN
    ASM_REWRITE_TAC[]]);;

let ptrees_derive_extensible = prove
 (`!(G:(A,B)grammar) (pt:(A,B,1)parsetree) sf.
     valid_ptree G pt /\ RTC (derive G) (ptree_fringe pt) sf
     ==> ?pt':(A,B,1)parsetree.
           valid_ptree G pt' /\ ptree_head pt' = ptree_head pt /\
           ptree_fringe pt' = sf`,
  GEN_TAC THEN
  SUBGOAL_THEN
   `!sf1 sf2. RTC (derive (G:(A,B)grammar)) sf1 sf2
              ==> !pt:(A,B,1)parsetree.
                    valid_ptree G pt /\ ptree_fringe pt = sf1
                    ==> ?pt':(A,B,1)parsetree.
                          valid_ptree G pt' /\ ptree_head pt' = ptree_head pt /\
                          ptree_fringe pt' = sf2`
   (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC RTC_INDUCT_L THEN CONJ_TAC THENL
   [MESON_TAC[]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:((A,B)symbol)list`; `y:((A,B)symbol)list`;
                       `z:((A,B)symbol)list`] THEN
  STRIP_TAC THEN X_GEN_TAC `pt:(A,B,1)parsetree` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `pt:(A,B,1)parsetree`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `pt1:(A,B,1)parsetree` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`G:(A,B)grammar`; `pt1:(A,B,1)parsetree`;
                 `z:((A,B)symbol)list`] derive_fringe) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `pt2:(A,B,1)parsetree` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `pt2:(A,B,1)parsetree` THEN ASM_REWRITE_TAC[]);;

let singleton_derives_ptree = prove
 (`!(G:(A,B)grammar) h sf.
     RTC (derive G) [h] sf
     ==> ?pt:(A,B,1)parsetree.
           valid_ptree G pt /\ ptree_head pt = h /\ ptree_fringe pt = sf`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(A,B)grammar`; `grammar_Lf (h,one):(A,B,1)parsetree`;
                 `sf:((A,B)symbol)list`] ptrees_derive_extensible) THEN
  ASM_REWRITE_TAC[valid_ptree_def; ptree_fringe_def; ptree_head_def]);;

let derives_language = prove
 (`!G:(A,B)grammar.
     language G = {ts | RTC (derive G) [grammar_NT (grammar_start G)] (MAP grammar_TOK ts)}`,
  GEN_TAC THEN REWRITE_TAC[language_def; EXTENSION; IN_ELIM_THM;
                           complete_ptree_def] THEN
  X_GEN_TAC `ts:A list` THEN EQ_TAC THENL
   [STRIP_TAC THEN
    MP_TAC(ISPECL [`G:(A,B)grammar`; `pt:(A,B,1)parsetree`]
                  valid_ptree_derive) THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC THEN
    MP_TAC(ISPECL [`G:(A,B)grammar`;
                   `grammar_Lf (grammar_NT (grammar_start (G:(A,B)grammar)),one):(A,B,1)parsetree`;
                   `MAP grammar_TOK ts:((A,B)symbol)list`] ptrees_derive_extensible) THEN
    ASM_REWRITE_TAC[valid_ptree_def; ptree_fringe_def; ptree_head_def] THEN
    DISCH_THEN(X_CHOOSE_THEN `pt:(A,B,1)parsetree` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `pt:(A,B,1)parsetree` THEN
    ASM_REWRITE_TAC[IN_SET_OF_LIST; MEM_MAP] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[isTOK_def]]);;

let derives_leading_nonNT_E = prove
 (`!(G:(A,B)grammar) N rest Y.
     ~(N IN FDOM (grammar_rules G)) /\ RTC (derive G) (CONS (grammar_NT N) rest) Y
     ==> ?rest'. Y = CONS (grammar_NT N) rest' /\ RTC (derive G) rest rest'`,
  GEN_TAC THEN
  SUBGOAL_THEN
   `!X Y. RTC (derive (G:(A,B)grammar)) X Y
          ==> !N rest. ~(N IN FDOM (grammar_rules G)) /\
                       X = CONS (grammar_NT N) rest
                       ==> ?rest'. Y = CONS (grammar_NT N) rest' /\
                                   RTC (derive G) rest rest'`
   (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC RTC_INDUCT_L THEN CONJ_TAC THENL
   [MESON_TAC[RTC_REFL]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:((A,B)symbol)list`; `y:((A,B)symbol)list`;
                       `z:((A,B)symbol)list`] THEN
  STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`N:B+num`; `rest:((A,B)symbol)list`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`N:B+num`; `rest:((A,B)symbol)list`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:((A,B)symbol)list` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `derive (G:(A,B)grammar) y z` THEN ASM_REWRITE_TAC[derive_def] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:((A,B)symbol)list` (X_CHOOSE_THEN `sym:B+num`
    (X_CHOOSE_THEN `rhs:((A,B)symbol)list`
    (X_CHOOSE_THEN `s:((A,B)symbol)list` STRIP_ASSUME_TAC)))) THEN
  UNDISCH_TAC `CONS (grammar_NT N:(A,B)symbol) r1 = APPEND (APPEND p [grammar_NT sym]) s` THEN
  ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
  REWRITE_TAC[LPARSEAUX_APPEND_EQ_CONS; APPEND_EQ_NIL; NOT_CONS_NIL] THEN
  REWRITE_TAC[LPARSEAUX_APPEND_EQ_CONS; NOT_CONS_NIL; CONS_11;
              symbol_inject] THEN
  STRIP_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `APPEND (APPEND l1'' rhs) s:((A,B)symbol)list` THEN
  ASM_REWRITE_TAC[APPEND] THEN MATCH_MP_TAC RTC_TRANS_L THEN
  EXISTS_TAC `r1:((A,B)symbol)list` THEN ASM_REWRITE_TAC[derive_def] THEN
  MAP_EVERY EXISTS_TAC [`l1'':((A,B)symbol)list`; `sym:B+num`;
                        `rhs:((A,B)symbol)list`; `s:((A,B)symbol)list`] THEN
  ASM_REWRITE_TAC[]);;

let derives_leading_nonNT = prove
 (`!(G:(A,B)grammar) N rest Y.
     ~(N IN FDOM (grammar_rules G))
     ==> (RTC (derive G) (CONS (grammar_NT N) rest) Y <=>
          ?rest'. Y = CONS (grammar_NT N) rest' /\ RTC (derive G) rest rest')`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [ASM_MESON_TAC[derives_leading_nonNT_E]; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[LPARSEAUX_CONS_APPEND] THEN
  MATCH_MP_TAC derives_paste_horizontally THEN ASM_REWRITE_TAC[RTC_REFL]);;

let derives_split_horizontally = prove
 (`!(G:(A,B)grammar) p s sf.
     RTC (derive G) (APPEND p s) sf <=>
     ?sf1 sf2. sf = APPEND sf1 sf2 /\ RTC (derive G) p sf1 /\
               RTC (derive G) s sf2`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [ALL_TAC; MESON_TAC[derives_paste_horizontally]] THEN
  SUBGOAL_THEN
   `!x y. RTC (derive (G:(A,B)grammar)) x y
          ==> !p s. x = APPEND p s
                    ==> ?sf1 sf2. y = APPEND sf1 sf2 /\
                                  RTC (derive G) p sf1 /\
                                  RTC (derive G) s sf2`
   (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC RTC_INDUCT_L THEN CONJ_TAC THENL
   [MESON_TAC[RTC_REFL]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:((A,B)symbol)list`; `y:((A,B)symbol)list`;
                       `z:((A,B)symbol)list`] THEN
  STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`p:((A,B)symbol)list`;
                                      `s:((A,B)symbol)list`] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`p:((A,B)symbol)list`; `s:((A,B)symbol)list`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `sf1:((A,B)symbol)list` (X_CHOOSE_THEN
    `sf2:((A,B)symbol)list` STRIP_ASSUME_TAC)) THEN
  UNDISCH_TAC `derive (G:(A,B)grammar) y z` THEN REWRITE_TAC[derive_def] THEN
  DISCH_THEN(X_CHOOSE_THEN `pfx:((A,B)symbol)list` (X_CHOOSE_THEN `N:B+num`
    (X_CHOOSE_THEN `r:((A,B)symbol)list`
    (X_CHOOSE_THEN `sfx:((A,B)symbol)list` STRIP_ASSUME_TAC)))) THEN
  UNDISCH_TAC `y:((A,B)symbol)list = APPEND (APPEND pfx [grammar_NT N]) sfx` THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
  REWRITE_TAC[LPARSEAUX_APPEND_EQ_APPEND_MID] THEN STRIP_TAC THENL
   [MAP_EVERY EXISTS_TAC [`APPEND (APPEND pfx r) l:((A,B)symbol)list`;
                          `sf2:((A,B)symbol)list`] THEN
    ASM_REWRITE_TAC[GSYM APPEND_ASSOC] THEN
    MATCH_MP_TAC RTC_TRANS_L THEN EXISTS_TAC `sf1:((A,B)symbol)list` THEN
    ASM_REWRITE_TAC[derive_def] THEN
    MAP_EVERY EXISTS_TAC [`pfx:((A,B)symbol)list`; `N:B+num`;
                          `r:((A,B)symbol)list`; `l:((A,B)symbol)list`] THEN
    ASM_REWRITE_TAC[GSYM APPEND_ASSOC];
    MAP_EVERY EXISTS_TAC [`sf1:((A,B)symbol)list`;
                          `APPEND (APPEND l r) sfx:((A,B)symbol)list`] THEN
    ASM_REWRITE_TAC[GSYM APPEND_ASSOC] THEN
    MATCH_MP_TAC RTC_TRANS_L THEN EXISTS_TAC `sf2:((A,B)symbol)list` THEN
    ASM_REWRITE_TAC[derive_def] THEN
    MAP_EVERY EXISTS_TAC [`l:((A,B)symbol)list`; `N:B+num`;
                          `r:((A,B)symbol)list`; `sfx:((A,B)symbol)list`] THEN
    ASM_REWRITE_TAC[GSYM APPEND_ASSOC]]);;

(* ------------------------------------------------------------------------- *)
(* The HOL4 [simp] theorems of this theory, for the project simpset.         *)
(* ------------------------------------------------------------------------- *)

let _ = cake_add_simps
  [isTOK_def; grammar_destTOK_def; ptree_head_def; valid_ptree_def;
   ptree_fringe_def; real_fringe_def; MAP_TKI_11; valid_locs_def;
   valid_lptree_thm; derive_1NT];;
