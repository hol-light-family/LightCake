(* ========================================================================= *)
(* lprefix_lub: port of HOL4 examples/pl-semantics/lprefix_lub/              *)
(* lprefix_lubScript.sml (the HOL4 library used by CakeML v3479): least      *)
(* upper bounds of chains of lazy lists ordered by LPREFIX, used for the     *)
(* semantics of diverging programs.                                          *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - HOL4 fromList is llist_fromList (see llist.ml); HOL4 l1 isPREFIX l2 is   *)
(*   isPREFIX l1 l2 (infix <<=), IS_PREFIX l1 l2 = isPREFIX l2 l1.           *)
(* - This theory and llist both have a theorem LPREFIX_NTH with different    *)
(*   statements: the one of this theory is lprefix_lub_LPREFIX_NTH.          *)
(* - HOL4 Overload LUB = build_lprefix_lub is not defined: build_lprefix_lub. *)
(* - Lemmas named LLISTAUX_... are helpers (not HOL4 names).                 *)
(* ========================================================================= *)

needs "hol4/vocab.ml";;
needs "hol4/llist.ml";;

(* list facts (list theory; local) *)

let LLISTAUX_isPREFIX_APPEND = prove
 (`!xs ys:A list. isPREFIX xs ys <=> ?zs. ys = APPEND xs zs`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[isPREFIX; APPEND] THENL
   [MESON_TAC[]; ALL_TAC] THEN
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `ys:A list` list_CASES) THEN
  ASM_REWRITE_TAC[list_CASE; NOT_CONS_NIL; CONS_11] THEN MESON_TAC[]);;

let IS_PREFIX_FILTER = prove
 (`!l1 l2:A list. IS_PREFIX l1 l2 ==> IS_PREFIX (FILTER P l1) (FILTER P l2)`,
  REWRITE_TAC[IS_PREFIX_DEF; LLISTAUX_isPREFIX_APPEND] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[FILTER_APPEND] THEN MESON_TAC[]);;

let less_opt_def = new_recursive_definition option_RECURSION
  `(less_opt n NONE <=> T) /\ (less_opt n (SOME m) <=> n < m)`;;

let less_opt_SUC_elim = prove
 (`less_opt (SUC n) z ==> less_opt n z`,
  STRUCT_CASES_TAC(ISPEC `z:num option` (cases "option")) THEN
  REWRITE_TAC[less_opt_def] THEN ARITH_TAC);;

let less_opt_LLENGTH_LNTH_SOME = prove
 (`less_opt n (LLENGTH (l:A llist)) <=> IS_SOME (LNTH n l)`,
  MP_TAC(ISPEC `LLENGTH (l:A llist)` (cases "option")) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[less_opt_def; LLISTAUX_IS_SOME_NONE] THENL
   [FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[LLISTAUX_LLENGTH_NONE_LNTH]) THEN
    MESON_TAC[option_DISTINCT];
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[LLISTAUX_LLENGTH_SOME_LNTH]) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN ARITH_TAC]);;

let IS_SOME_LTAKE_less_opt_LLENGTH = prove
 (`IS_SOME (LTAKE n (ll:A llist)) ==> LLENGTH ll = SOME n \/ less_opt n (LLENGTH ll)`,
  REWRITE_TAC[LLISTAUX_IS_SOME_NONE; LLISTAUX_LTAKE_NONE; NOT_EXISTS_THM] THEN
  DISCH_THEN(LABEL_TAC "h") THEN
  MP_TAC(ISPEC `LLENGTH (ll:A llist)` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `k:num`
    (fun th -> REWRITE_TAC[th] THEN
               MP_TAC(REWRITE_RULE[LLISTAUX_LLENGTH_SOME_LNTH] th)))) THEN
  REWRITE_TAC[less_opt_def; option_INJ] THEN
  DISCH_THEN(MP_TAC o SPEC `k:num`) THEN REWRITE_TAC[LE_REFL] THEN DISCH_TAC THEN
  REMOVE_THEN "h" (MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let lprefix_lub_LPREFIX_NTH = prove
 (`!ll1 ll2:A llist.
     LPREFIX ll1 ll2 <=> !n. less_opt n (LLENGTH ll1) ==> LNTH n ll1 = LNTH n ll2`,
  REWRITE_TAC[LPREFIX_NTH; less_opt_LLENGTH_LNTH_SOME] THEN
  REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_TAC THEN X_GEN_TAC `n:num` THENL
   [MP_TAC(ISPEC `LNTH n (ll1:A llist)` (cases "option")) THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[IS_SOME_DEF] THEN ASM_MESON_TAC[];
    GEN_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
    ASM_REWRITE_TAC[IS_SOME_DEF] THEN ASM_MESON_TAC[]]);;

let lnth_some_length = prove
 (`!(ll:A llist) n x. LNTH n ll = SOME x ==> less_opt n (LLENGTH ll)`,
  SIMP_TAC[less_opt_LLENGTH_LNTH_SOME; IS_SOME_DEF]);;

let llist_shorter_def = new_definition (CASE_TERM
  `llist_shorter (ll1:A llist) (ll2:B llist) <=>
     match (LLENGTH ll1, LLENGTH ll2) with
       (NONE, NONE) -> T
     | (SOME x, NONE) -> T
     | (NONE, SOME x) -> F
     | (SOME x, SOME y) -> x <= y`);;

let llist_shorter_lnth = prove
 (`!(ll1:A llist) (ll2:B llist).
     llist_shorter ll1 ll2 <=> !n x. LNTH n ll1 = SOME x ==> ?y. LNTH n ll2 = SOME y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[llist_shorter_def] THEN
  MP_TAC(ISPEC `LLENGTH (ll1:A llist)` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_TAC `m1:num`)) THEN
  MP_TAC(ISPEC `LLENGTH (ll2:B llist)` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_TAC `m2:num`)) THEN
  ASM_REWRITE_TAC[option_CASE; pair_CASE] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[LLISTAUX_LLENGTH_NONE_LNTH;
                                             LLISTAUX_LLENGTH_SOME_LNTH])) THEN
  REPEAT DISCH_TAC THENL
   [ASM_MESON_TAC[];
    ASM_MESON_TAC[option_DISTINCT; LE_REFL];
    ASM_MESON_TAC[];
    EQ_TAC THENL
     [REPEAT STRIP_TAC THEN
      MP_TAC(ISPEC `LNTH n (ll2:B llist)` (cases "option")) THEN
      ASM_MESON_TAC[option_DISTINCT; LE_TRANS];
      DISCH_TAC THEN REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
      MP_TAC(ISPEC `LNTH m2 (ll1:A llist)` (cases "option")) THEN
      ASM_MESON_TAC[option_DISTINCT; NOT_LT; LE_REFL; LT_IMP_LE]]]);;

let llist_shorter_fromList = prove
 (`!l1:A list l2:B list.
     llist_shorter (llist_fromList l1) (llist_fromList l2) <=> LENGTH l1 <= LENGTH l2`,
  REWRITE_TAC[llist_shorter_def; LLENGTH_fromList; option_CASE; pair_CASE]);;

let lprefix_chain_def = new_definition
  `lprefix_chain (ls:(A llist)->bool) <=>
     !ll1 ll2. ll1 IN ls /\ ll2 IN ls ==> LPREFIX ll1 ll2 \/ LPREFIX ll2 ll1`;;

let lprefix_chain_subset = prove
 (`lprefix_chain (ls:(A llist)->bool) /\ y SUBSET ls ==> lprefix_chain y`,
  REWRITE_TAC[lprefix_chain_def; SUBSET] THEN MESON_TAC[]);;

let lprefix_chain_LNTHs_agree = prove
 (`lprefix_chain (ls:(A llist)->bool) /\
   l1 IN ls /\ l2 IN ls /\
   LNTH n l1 = SOME x1 /\ LNTH n l2 = SOME x2
   ==> x1 = x2`,
  REWRITE_TAC[lprefix_chain_def; LPREFIX_NTH] THEN
  MESON_TAC[option_INJ]);;

let lprefix_chain_nth_def = new_definition
  `lprefix_chain_nth n (ls:(A llist)->bool) =
     some x. ?l. l IN ls /\ LNTH n l = SOME x`;;

(* the lprefix_chain_nth of a chain (local) *)

let LLISTAUX_chain_nth_NONE = prove
 (`!n ls:(A llist)->bool.
     lprefix_chain_nth n ls = NONE <=> !l. l IN ls ==> LNTH n l = NONE`,
  REWRITE_TAC[lprefix_chain_nth_def; some_DEF] THEN REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
  POP_ASSUM MP_TAC THEN MESON_TAC[cases "option"; option_DISTINCT]);;

let LLISTAUX_chain_nth_SOME = prove
 (`!n (ls:(A llist)->bool) x.
     lprefix_chain_nth n ls = SOME x ==> ?l. l IN ls /\ LNTH n l = SOME x`,
  REWRITE_TAC[lprefix_chain_nth_def; some_DEF] THEN REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  FIRST_X_ASSUM(MP_TAC o SELECT_RULE) THEN REWRITE_TAC[]);;

let exists_lprefix_chain_nth = prove
 (`!ls n (x:A).
     lprefix_chain ls /\ (?l. l IN ls /\ LNTH n l = SOME x) ==>
     lprefix_chain_nth n ls = SOME x`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `l:A llist` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`n:num`; `ls:(A llist)->bool`] LLISTAUX_chain_nth_NONE) THEN
  MP_TAC(ISPEC `lprefix_chain_nth n (ls:(A llist)->bool)` (cases "option")) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[option_INJ] THENL
   [ASM_MESON_TAC[option_DISTINCT]; DISCH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP LLISTAUX_chain_nth_SOME) THEN
  ASM_MESON_TAC[lprefix_chain_LNTHs_agree]);;

let not_exists_lprefix_chain_nth = prove
 (`!ls:(A llist)->bool n.
     lprefix_chain ls /\ (!l. l IN ls ==> LNTH n l = NONE) ==>
     lprefix_chain_nth n ls = NONE`,
  SIMP_TAC[LLISTAUX_chain_nth_NONE]);;

let lprefix_chain_nth_none_mono = prove
 (`!m n ls:(A llist)->bool.
     lprefix_chain ls /\ m <= n /\ lprefix_chain_nth m ls = NONE ==>
     lprefix_chain_nth n ls = NONE`,
  REWRITE_TAC[LLISTAUX_chain_nth_NONE] THEN MESON_TAC[LNTH_NONE_MONO]);;

let equiv_lprefix_chain_def = new_definition
  `equiv_lprefix_chain (ls1:(A llist)->bool) ls2 <=>
     !n. lprefix_chain_nth n ls1 = lprefix_chain_nth n ls2`;;

let equiv_lprefix_chain_thm = prove
 (`!ls1 ls2:(A llist)->bool.
     lprefix_chain ls1 /\ lprefix_chain ls2 ==>
     (equiv_lprefix_chain ls1 ls2 <=>
      (!ll1 n x. ll1 IN ls1 /\ LNTH n ll1 = SOME x ==>
                 ?ll2. ll2 IN ls2 /\ LNTH n ll2 = SOME x) /\
      (!ll2 n x. ll2 IN ls2 /\ LNTH n ll2 = SOME x ==>
                 ?ll1. ll1 IN ls1 /\ LNTH n ll1 = SOME x))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[equiv_lprefix_chain_def] THEN EQ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC LLISTAUX_chain_nth_SOME THEN
    ASM_MESON_TAC[exists_lprefix_chain_nth];
    STRIP_TAC THEN X_GEN_TAC `n:num` THEN
    MP_TAC(ISPEC `lprefix_chain_nth n (ls1:(A llist)->bool)` (cases "option")) THEN
    MP_TAC(ISPEC `lprefix_chain_nth n (ls2:(A llist)->bool)` (cases "option")) THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
    ASM_MESON_TAC[LLISTAUX_chain_nth_SOME; exists_lprefix_chain_nth;
                  option_DISTINCT; option_INJ]]);;

let LLISTAUX_shorter_last = prove
 (`!(ll2:A llist) (ll1:B llist) k.
     LLENGTH ll2 = SOME (SUC k) ==>
     (llist_shorter ll2 ll1 <=> ?y. LNTH k ll1 = SOME y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[llist_shorter_lnth] THEN
  FIRST_X_ASSUM(ASSUME_TAC o REWRITE_RULE[LLISTAUX_LLENGTH_SOME_LNTH]) THEN
  EQ_TAC THENL
   [DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(ISPEC `LNTH k (ll2:A llist)` (cases "option")) THEN
    ASM_MESON_TAC[ARITH_RULE `~(SUC k <= k)`];
    STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`n:num`; `x:A`] THEN DISCH_TAC THEN
    MATCH_MP_TAC lnth_some_down_closed THEN
    MAP_EVERY EXISTS_TAC [`y:B`; `k:num`] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(SUC k <= n)` MP_TAC THENL
     [ASM_MESON_TAC[option_DISTINCT]; ARITH_TAC]]);;

let LLISTAUX_chain_agree = prove
 (`!ls l1 l2 n (x1:A) x2.
     lprefix_chain ls /\ l1 IN ls /\ l2 IN ls /\
     LNTH n l1 = SOME x1 /\ LNTH n l2 = SOME x2 ==> x1 = x2`,
  REWRITE_TAC[lprefix_chain_LNTHs_agree]);;

let LLISTAUX_LLENGTH_SUC_LNTH = prove
 (`!(ll:A llist) k. LLENGTH ll = SOME (SUC k) ==> ?x. LNTH k ll = SOME x`,
  REWRITE_TAC[LLISTAUX_LLENGTH_SOME_LNTH] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `LNTH k (ll:A llist)` (cases "option")) THEN
  ASM_REWRITE_TAC[ARITH_RULE `~(SUC k <= k)`]);;

let equiv_lprefix_chain_thm2 = prove
 (`!ls1 ls2:(A llist)->bool.
     lprefix_chain ls1 /\ lprefix_chain ls2 /\ (!ll2. ll2 IN ls2 ==> LFINITE ll2) ==>
     (equiv_lprefix_chain ls1 ls2 <=>
      (!ll1 n x. ll1 IN ls1 /\ LNTH n ll1 = SOME x ==>
                 ?ll2. ll2 IN ls2 /\ LNTH n ll2 = SOME x) /\
      (!ll2 (n:num) (x:A). ll2 IN ls2 /\ ~(ll2 = LNIL) ==>
                 ?ll1. ll1 IN ls1 /\ llist_shorter ll2 ll1))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[equiv_lprefix_chain_thm] THEN
  MATCH_MP_TAC(TAUT `(a ==> (b <=> c)) ==> (a /\ b <=> a /\ c)`) THEN
  DISCH_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [X_GEN_TAC `ll2:A llist` THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `LFINITE (ll2:A llist)`
      (X_CHOOSE_TAC `m:num` o MATCH_MP LFINITE_HAS_LENGTH) THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `LLENGTH (ll2:A llist) = SOME (SUC (m - 1))` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[option_INJ] THEN
      UNDISCH_TAC `~(ll2:A llist = LNIL)` THEN
      ASM_REWRITE_TAC[GSYM LLENGTH_0; option_INJ] THEN ARITH_TAC;
      ALL_TAC] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LLISTAUX_shorter_last th]) THEN
    FIRST_ASSUM(X_CHOOSE_TAC `a:A` o MATCH_MP LLISTAUX_LLENGTH_SUC_LNTH) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`ll2:A llist`; `m - 1`; `a:A`]) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    MAP_EVERY X_GEN_TAC [`ll2:A llist`; `n:num`; `x:A`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `ll2:A llist`) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      UNDISCH_TAC `LNTH n (ll2:A llist) = SOME x` THEN
      ASM_REWRITE_TAC[LNTH_THM; option_DISTINCT];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `ll1:A llist` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[llist_shorter_lnth]) THEN
    DISCH_THEN(MP_TAC o SPECL [`n:num`; `x:A`]) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_TAC `y:A`) THEN
    EXISTS_TAC `ll1:A llist` THEN ASM_REWRITE_TAC[option_INJ] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`ll1:A llist`; `n:num`; `y:A`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `ll3:A llist` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC LLISTAUX_chain_agree THEN
    MAP_EVERY EXISTS_TAC [`ls2:(A llist)->bool`; `ll3:A llist`; `ll2:A llist`;
                          `n:num`] THEN
    ASM_REWRITE_TAC[]]);;

let lprefix_lub_def = new_definition
  `lprefix_lub (ls:(A llist)->bool) lub <=>
     (!ll. ll IN ls ==> LPREFIX ll lub) /\
     (!ub. (!ll. ll IN ls ==> LPREFIX ll ub) ==> LPREFIX lub ub)`;;

let lprefix_lub_is_chain = prove
 (`!ls (ll:A llist). lprefix_lub ls ll ==> lprefix_chain ls`,
  REWRITE_TAC[lprefix_lub_def; lprefix_chain_def] THEN
  MESON_TAC[prefixes_lprefix_total]);;

let lprefix_lub_nth = prove
 (`!ls (lub:A llist).
     lprefix_chain ls ==>
     (lprefix_lub ls lub <=> !n. LNTH n lub = lprefix_chain_nth n ls)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lprefix_lub_def] THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "up") (LABEL_TAC "least")) THEN
    X_GEN_TAC `n:num` THEN
    ASM_CASES_TAC `?l x:A. l IN ls /\ LNTH n l = SOME x` THENL
     [FIRST_X_ASSUM(X_CHOOSE_THEN `l:A llist` (X_CHOOSE_THEN `x:A`
        STRIP_ASSUME_TAC)) THEN
      SUBGOAL_THEN `lprefix_chain_nth n (ls:(A llist)->bool) = SOME x`
        SUBST1_TAC THENL [ASM_MESON_TAC[exists_lprefix_chain_nth]; ALL_TAC] THEN
      REMOVE_THEN "up" (MP_TAC o SPEC `l:A llist`) THEN
      ASM_REWRITE_TAC[LPREFIX_NTH] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `!l:A llist. l IN ls ==> LNTH n l = NONE` ASSUME_TAC THENL
     [ASM_MESON_TAC[cases "option"]; ALL_TAC] THEN
    ASM_SIMP_TAC[not_exists_lprefix_chain_nth] THEN
    MP_TAC(ISPEC `LNTH n (lub:A llist)` (cases "option")) THEN
    DISCH_THEN(DISJ_CASES_THEN2 ACCEPT_TAC (X_CHOOSE_TAC `y:A`)) THEN
    SUBGOAL_THEN `?p:A list. LTAKE n lub = SOME p` STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC(MESON[cases "option"]
        `~((x:(A list)option) = NONE) ==> ?y. x = SOME y`) THEN
      REWRITE_TAC[LLISTAUX_LTAKE_NONE] THEN
      ASM_MESON_TAC[LNTH_NONE_MONO; LT_IMP_LE; option_DISTINCT];
      ALL_TAC] THEN
    FIRST_ASSUM(ASSUME_TAC o SYM o MATCH_MP LTAKE_LENGTH) THEN
    REMOVE_THEN "least" (MP_TAC o SPEC `llist_fromList (p:A list)`) THEN
    ANTS_TAC THENL
     [X_GEN_TAC `ll:A llist` THEN DISCH_TAC THEN
      REWRITE_TAC[LPREFIX_NTH; LNTH_fromList] THEN
      MAP_EVERY X_GEN_TAC [`i:num`; `v:A`] THEN DISCH_TAC THEN
      SUBGOAL_THEN `i < n` ASSUME_TAC THENL
       [ASM_MESON_TAC[LNTH_NONE_MONO; NOT_LT; option_DISTINCT]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `LNTH i (lub:A llist) = SOME v` MP_TAC THENL
       [ASM_MESON_TAC[LPREFIX_NTH]; ALL_TAC] THEN
      ASM_MESON_TAC[LTAKE_LNTH_EL];
      ALL_TAC] THEN
    REWRITE_TAC[LPREFIX_NTH] THEN DISCH_THEN(MP_TAC o SPECL [`n:num`; `y:A`]) THEN
    ASM_REWRITE_TAC[LNTH_fromList; LT_REFL; option_DISTINCT];
    DISCH_THEN(LABEL_TAC "eq") THEN REWRITE_TAC[LPREFIX_NTH] THEN
    USE_THEN "eq" (fun th -> REWRITE_TAC[th]) THEN CONJ_TAC THENL
     [ASM_MESON_TAC[exists_lprefix_chain_nth];
      REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP LLISTAUX_chain_nth_SOME) THEN
      ASM_MESON_TAC[]]]);;

let unique_lprefix_lub = prove
 (`!f (ll1:A llist) ll2. lprefix_lub f ll1 /\ lprefix_lub f ll2 ==> ll1 = ll2`,
  REWRITE_TAC[lprefix_lub_def] THEN MESON_TAC[LPREFIX_ANTISYM]);;

let build_lprefix_lub_f_def = new_definition
  `build_lprefix_lub_f (ls:(A llist)->bool) n =
     OPTION_MAP (\x. (n + 1, x)) (lprefix_chain_nth n ls)`;;

let build_lprefix_lub_def = new_definition
  `build_lprefix_lub (ls:(A llist)->bool) = LUNFOLD (build_lprefix_lub_f ls) 0`;;

let build_lprefix_lub_lem = prove
 (`!ls:(A llist)->bool.
     lprefix_chain ls ==>
     !m n. LNTH n (LUNFOLD (build_lprefix_lub_f ls) m) = lprefix_chain_nth (m + n) ls`,
  GEN_TAC THEN DISCH_TAC THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  INDUCT_TAC THEN GEN_TAC THEN
  REWRITE_TAC[LNTH_LUNFOLD; build_lprefix_lub_f_def; ADD_CLAUSES] THEN
  MP_TAC(ISPEC `lprefix_chain_nth m (ls:(A llist)->bool)` (cases "option")) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[OPTION_MAP_DEF; option_CASE; pair_CASE] THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC lprefix_chain_nth_none_mono THEN
    EXISTS_TAC `m:num` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC]);;

let build_lprefix_lub_thm = prove
 (`!ls:(A llist)->bool. lprefix_chain ls ==> lprefix_lub ls (build_lprefix_lub ls)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[lprefix_lub_nth; build_lprefix_lub_def] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP build_lprefix_lub_lem th; ADD_CLAUSES]));;

let lprefix_lub_equiv_chain = prove
 (`!ls1 ls2 (ll:A llist).
     lprefix_chain ls1 /\ lprefix_chain ls2 /\ equiv_lprefix_chain ls1 ls2 ==>
     (lprefix_lub ls1 ll <=> lprefix_lub ls2 ll)`,
  SIMP_TAC[lprefix_lub_nth; equiv_lprefix_chain_def]);;

let lprefix_lub_equiv_chain2 = prove
 (`!ls1 ls2 (ll1:A llist) ll2.
     lprefix_lub ls1 ll1 /\ lprefix_lub ls2 ll2 ==>
     (ll1 = ll2 <=> equiv_lprefix_chain ls1 ls2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `lprefix_chain (ls1:(A llist)->bool) /\ lprefix_chain (ls2:(A llist)->bool)`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[lprefix_lub_is_chain]; ALL_TAC] THEN
  MP_TAC(ISPECL [`ls1:(A llist)->bool`; `ll1:A llist`] lprefix_lub_nth) THEN
  MP_TAC(ISPECL [`ls2:(A llist)->bool`; `ll2:A llist`] lprefix_lub_nth) THEN
  ASM_REWRITE_TAC[equiv_lprefix_chain_def; LNTH_EQ] THEN
  REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[]);;

let lprefix_lub_new_chain = prove
 (`!ls1 ls2 (ll:A llist).
     lprefix_chain ls2 /\ equiv_lprefix_chain ls1 ls2 /\ lprefix_lub ls1 ll ==>
     lprefix_lub ls2 ll`,
  MESON_TAC[lprefix_lub_equiv_chain; lprefix_lub_is_chain]);;

let prefix_chain_def = new_definition
  `prefix_chain (ls:(A list)->bool) <=>
     !l1 l2. l1 IN ls /\ l2 IN ls ==> isPREFIX l1 l2 \/ isPREFIX l2 l1`;;

let prefix_chain_lprefix_chain = prove
 (`prefix_chain (ls:(A list)->bool) ==> lprefix_chain (IMAGE llist_fromList ls)`,
  REWRITE_TAC[prefix_chain_def; lprefix_chain_def; FORALL_IN_IMAGE_2] THEN
  REWRITE_TAC[LPREFIX_fromList; from_toList; option_CASE]);;

let prefix_chain_FILTER = prove
 (`prefix_chain (ls:(A list)->bool) ==> prefix_chain (IMAGE (FILTER P) ls)`,
  REWRITE_TAC[prefix_chain_def; FORALL_IN_IMAGE_2] THEN
  MESON_TAC[IS_PREFIX_FILTER; IS_PREFIX_DEF]);;

let build_prefix_lub_intro = prove
 (`lprefix_chain (ls:(A llist)->bool) ==>
   (lprefix_lub ls lub <=> lub = build_lprefix_lub ls)`,
  MESON_TAC[build_lprefix_lub_thm; unique_lprefix_lub]);;

let lprefix_rel_def = new_definition
  `lprefix_rel (s1:(A llist)->bool) s2 <=>
     !l1. l1 IN s1 ==> ?l2. l2 IN s2 /\ LPREFIX l1 l2`;;

let lprefix_rel_lnth = prove
 (`lprefix_rel (ls1:(A llist)->bool) ls2 ==>
   (!ll1 n x. ll1 IN ls1 /\ LNTH n ll1 = SOME x ==>
              ?ll2. ll2 IN ls2 /\ LNTH n ll2 = SOME x)`,
  REWRITE_TAC[lprefix_rel_def; LPREFIX_NTH] THEN MESON_TAC[]);;

let IMP_equiv_lprefix_chain = prove
 (`lprefix_chain (ls1:(A llist)->bool) /\ lprefix_chain ls2 /\
   lprefix_rel ls1 ls2 /\ lprefix_rel ls2 ls1
   ==> equiv_lprefix_chain ls1 ls2`,
  STRIP_TAC THEN ASM_SIMP_TAC[equiv_lprefix_chain_thm] THEN
  CONJ_TAC THEN MATCH_MP_TAC lprefix_rel_lnth THEN ASM_REWRITE_TAC[]);;

let IMP_build_lprefix_lub_EQ = prove
 (`lprefix_chain (ls1:(A llist)->bool) /\ lprefix_chain ls2 /\
   lprefix_rel ls1 ls2 /\ lprefix_rel ls2 ls1
   ==> build_lprefix_lub ls1 = build_lprefix_lub ls2`,
  STRIP_TAC THEN
  MP_TAC(ISPECL [`ls1:(A llist)->bool`; `ls2:(A llist)->bool`;
                 `build_lprefix_lub (ls1:(A llist)->bool)`;
                 `build_lprefix_lub (ls2:(A llist)->bool)`]
                lprefix_lub_equiv_chain2) THEN
  ASM_SIMP_TAC[build_lprefix_lub_thm; IMP_equiv_lprefix_chain]);;

let lprefix_chain_LAPPEND = prove
 (`lprefix_chain (X:(A llist)->bool) <=>
   lprefix_chain (IMAGE (\x. LAPPEND (llist_fromList l) x) X)`,
  REWRITE_TAC[lprefix_chain_def; FORALL_IN_IMAGE_2; LPREFIX_LAPPEND_fromList]);;

let LAPPEND_fromList_LUB = prove
 (`lprefix_chain (X:(A llist)->bool) /\ ~(X = {}) ==>
   LAPPEND (llist_fromList l) (build_lprefix_lub X) =
   build_lprefix_lub (IMAGE (\x. LAPPEND (llist_fromList l) x) X)`,
  STRIP_TAC THEN
  SUBGOAL_THEN
   `lprefix_chain (IMAGE (\x. LAPPEND (llist_fromList l) x) (X:(A llist)->bool))`
   ASSUME_TAC THENL [ASM_MESON_TAC[lprefix_chain_LAPPEND]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP build_prefix_lub_intro th)]) THEN
  MP_TAC(ISPEC `X:(A llist)->bool` build_lprefix_lub_thm) THEN
  ASM_REWRITE_TAC[lprefix_lub_def; FORALL_IN_IMAGE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "least")) THEN
  ASM_REWRITE_TAC[LPREFIX_LAPPEND_fromList] THEN
  X_GEN_TAC `ub:A llist` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `x0:A llist` o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) THEN
  SUBGOAL_THEN `?u:A llist. ub = LAPPEND (llist_fromList l) u` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `x0:A llist`) THEN
    ASM_REWRITE_TAC[LPREFIX_APPEND; LAPPEND_ASSOC] THEN MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LPREFIX_LAPPEND_fromList]) THEN
  REWRITE_TAC[LPREFIX_LAPPEND_fromList] THEN
  REMOVE_THEN "least" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;
