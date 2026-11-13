(* ========================================================================= *)
(* backendProps: port of HOL4 compiler/backend/semantics/backendPropsScript  *)
(* .sml (CakeML v3479).  General definitions and theorems that are useful    *)
(* within the proofs about the compiler backend.                             *)
(* ========================================================================= *)

needs "misc/misc.ml";;

prioritize_num();;
type_invention_error := true;;

(* HOL4 [simp] theorems are registered with cake_add_simps after them.  The *)
(* oracle combinators are polymorphic in all their components: the type    *)
(* annotations below only name HOL4's type variables.                      *)

let state_cc_def = cake_def
  `state_cc (f:S->P->T#Q) (cc:C->Q->(D#E#G)option) =
     \sc (prog:P).
       match sc with
         (state,cfg) ->
           match f state prog with
             (state1,prog1) ->
               match cc cfg prog1 with
                 NONE -> NONE
               | SOME (code,data,cfg1) -> SOME (code,data,state1,cfg1)`;;

let pure_cc_def = cake_def
  `pure_cc (f:P->Q) (cc:C->Q->R) =
     \cfg prog. let prog1 = f prog in cc cfg prog1`;;

let state_co_def = cake_def
  `state_co (f:S->P->T#Q) (co:num->(S#C)#P) =
     \n. match co n with
           ((state,cfg),progs) ->
             match f state progs with
               (state1,progs) -> (cfg,progs)`;;

let FST_state_co = prove
 (`FST (state_co (f:S->P->T#Q) (co:num->(S#C)#P) n) = SND (FST (co n))`,
  REWRITE_TAC[state_co_def; pair_CASE_def; FST; SND]);;

let SND_state_co = prove
 (`SND (state_co (f:S->P->T#Q) (co:num->(S#C)#P) n) =
   SND (f (FST (FST (co n))) (SND (co n)))`,
  REWRITE_TAC[state_co_def; pair_CASE_def; FST; SND]);;

let the_eqn = prove
 (CASE_TERM `the (x:A) y = match y with NONE -> x | SOME z -> z`,
  CASES_ON `y:A option` THEN RW[the_def]);;

let the_F_eq = prove
 (`the F opt <=> ?x. opt = SOME x /\ x`,
  CASES_ON `opt:bool option` THEN RW[the_eqn]);;

let pure_co_def = cake_def
  `pure_co (f:P->Q) = (I:C->C) ## f`;;

let SND_pure_co = prove
 (`SND (pure_co (co:P->Q) (x:C#P)) = co (SND x)`,
  CASES_ON `x:C#P` THEN REWRITE_TAC[pure_co_def; PAIR_MAP_THM; SND]);;
let _ = cake_add_simps [SND_pure_co];;

let FST_pure_co = prove
 (`FST (pure_co (co:P->Q) (x:C#P)) = FST x`,
  CASES_ON `x:C#P` THEN REWRITE_TAC[pure_co_def; PAIR_MAP_THM; FST; I_THM]);;
let _ = cake_add_simps [FST_pure_co];;

let pure_co_comb_pure_co = prove
 (`pure_co (f:Q->R) o pure_co (g:P->Q) o (co:A->C#P) = pure_co (f o g) o co`,
  REWRITE_TAC[FUN_EQ_THM; o_THM; pure_co_def] THEN GEN_TAC THEN
  CASES_ON `(co:A->C#P) x` THEN REWRITE_TAC[PAIR_MAP_THM; I_THM; o_THM]);;

let pure_co_I = prove
 (`pure_co (I:P->P) = (I:C#P->C#P)`,
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; pure_co_def; PAIR_MAP_THM; I_THM]);;

let pure_cc_I = prove
 (`pure_cc (I:P->P) = (I:(C->P->R)->C->P->R)`,
  REWRITE_TAC[FUN_EQ_THM; pure_cc_def; I_THM; LET_DEF; LET_END_DEF]);;

(* somewhat generic wrappers for defining standard properties about oracles *)

(* identifiers that appear in the initial state and in oracle steps        *)
(* increase monotonically in some sense.                                   *)

let oracle_monotonic_def = cake_def
  `oracle_monotonic (f:A->B->bool) (R:B->B->bool) (S:B->bool) (orac:num->A) <=>
     (!i j x y. i < j /\ x IN f (orac i) /\ y IN f (orac j) ==> R x y) /\
     (!i x y. x IN S /\ y IN f (orac i) ==> R x y)`;;

(* HOL4 computes the next two theorems from oracle_monotonic_def (its two  *)
(* conjuncts as implications).                                             *)

let oracle_monotonic_step = prove
 (`oracle_monotonic (f:A->B->bool) R S orac
   ==> !i j x y. i < j /\ x IN f (orac i) /\ y IN f (orac j) ==> R x y`,
  REWRITE_TAC[oracle_monotonic_def] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let oracle_monotonic_init = prove
 (`oracle_monotonic (f:A->B->bool) R S orac
   ==> !i x y. x IN S /\ y IN f (orac i) ==> R x y`,
  REWRITE_TAC[oracle_monotonic_def] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let oracle_monotonic_step2 = prove
 (`oracle_monotonic (f:A->B->bool) R St orac ==>
   !i j x y. x IN f (orac i) /\ y IN f (orac j) /\ i < j ==> R x y`,
  MESON_TAC[oracle_monotonic_step]);;

let oracle_monotonic_subset = prove
 (`(St' SUBSET St /\
    (!n. (f':C->B->bool) ((co':num->C) n) SUBSET (f:A->B->bool) ((co:num->A) n)))
   ==> oracle_monotonic f R St co ==> oracle_monotonic f' R St' co'`,
  REWRITE_TAC[oracle_monotonic_def; SUBSET] THEN MESON_TAC[]);;

let oracle_monotonic_shift_subset = prove
 (`(St' SUBSET (IMAGE ((+) (i:num)) St UNION count i) /\
    (!n. (f':C->num->bool) ((co':num->C) n) SUBSET
         IMAGE ((+) i) ((f:A->num->bool) ((co:num->A) n))))
   ==> oracle_monotonic f (<) St co ==> oracle_monotonic f' (<) St' co'`,
  REWRITE_TAC[oracle_monotonic_def; SUBSET; IN_UNION; IN_IMAGE; count_DEF;
              IN_ELIM_THM] THEN
  REPEAT STRIP_TAC THENL
   [SUBGOAL_THEN `?x0. x = i + x0 /\ x0 IN (f:A->num->bool) ((co:num->A) i')`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `?y0. y = i + y0 /\ y0 IN (f:A->num->bool) ((co:num->A) j)`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[LT_ADD_LCANCEL] THEN ASM_MESON_TAC[];
    SUBGOAL_THEN `?y0. y = i + y0 /\ y0 IN (f:A->num->bool) ((co:num->A) i')`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(?x0. x = i + x0 /\ x0 IN St) \/ x < i` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[];
      ASM_REWRITE_TAC[LT_ADD_LCANCEL] THEN ASM_MESON_TAC[];
      ASM_ARITH_TAC]]);;

let oracle_monotonic_shift_seq = prove
 (`!i. oracle_monotonic (f:A->B->bool) R St co /\ i > 0 /\
       St' SUBSET f (co (i - 1)) UNION St
       ==> oracle_monotonic f R St' (shift_seq i co)`,
  REWRITE_TAC[oracle_monotonic_def; shift_seq_def; SUBSET; IN_UNION] THEN
  REPEAT STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`i' + i:num`; `j + i:num`; `x:B`; `y:B`] o
      check (fun th -> is_forall(concl th) &&
                       length(fst(strip_forall(concl th))) = 4)) THEN
    ASM_REWRITE_TAC[LT_ADD_RCANCEL];
    SUBGOAL_THEN `(x:B) IN f ((co:num->A) (i - 1)) \/ x IN St` STRIP_ASSUME_TAC
    THENL
     [ASM_MESON_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPECL [`i - 1`; `i' + i:num`; `x:B`; `y:B`] o
        check (fun th -> is_forall(concl th) &&
                         length(fst(strip_forall(concl th))) = 4)) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
      ASM_MESON_TAC[]]]);;

let oracle_monotonic_DISJOINT_init = prove
 (`!i. oracle_monotonic (f:A->B->bool) R St co /\ irreflexive R
       ==> DISJOINT St (f (co i))`,
  MESON_TAC[oracle_monotonic_init; irreflexive_DEF; IN_DISJOINT]);;

(* check that an oracle with config values lists the config values that   *)
(* would be produced by the incremental compiler.                          *)

let is_state_oracle_def = cake_def
  `is_state_oracle (compile_inc_f:S->P->S#Q) (co:num->(S#C)#P) <=>
     !n. FST (FST (co (SUC n))) =
         FST (compile_inc_f (FST (FST (co n))) (SND (co n)))`;;

let is_state_oracle_shift = prove
 (`is_state_oracle (compile_inc_f:S->P->S#Q) (co:num->(S#C)#P) <=>
   is_state_oracle compile_inc_f (shift_seq 1 co) /\
   FST (FST (co 1)) = FST (compile_inc_f (FST (FST (co 0))) (SND (co 0)))`,
  REWRITE_TAC[is_state_oracle_def; shift_seq_def; GSYM ADD1] THEN
  EQ_TAC THEN REPEAT STRIP_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[ONE];
    STRUCT_CASES_TAC(SPEC `n:num` num_CASES) THEN ASM_REWRITE_TAC[GSYM ONE]]);;

let is_state_oracle_shift_imp = prove
 (`is_state_oracle (compile_inc_f:S->P->S#Q) (co:num->(S#C)#P)
   ==> is_state_oracle compile_inc_f (shift_seq n co)`,
  REWRITE_TAC[is_state_oracle_def; shift_seq_def; ADD_CLAUSES] THEN
  SIMP_TAC[]);;

let is_state_oracle_k = prove
 (`!k. is_state_oracle (compile_inc_f:S->P->S#Q) (co:num->(S#C)#P)
       ==> ?st oth_st prog. co k = ((st,oth_st),prog) /\
                            FST (FST (co (SUC k))) = FST (compile_inc_f st prog)`,
  REWRITE_TAC[is_state_oracle_def] THEN REPEAT STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`FST (FST ((co:num->(S#C)#P) k))`; `SND (FST ((co:num->(S#C)#P) k))`;
    `SND ((co:num->(S#C)#P) k)`] THEN
  ASM_REWRITE_TAC[PAIR]);;

(* constructive combinators for building up the config part of an oracle  *)

let syntax_to_full_oracle_def = cake_def
  `syntax_to_full_oracle (mk:(X->P)->X->M) (progs:X->P) i = (mk progs i,progs i)`;;

let state_orac_states_def = cake_def
  `(state_orac_states (f:S->P->S#Q) st (progs:num->P) 0 = st) /\
   (state_orac_states f st progs (SUC n) =
      FST (f (state_orac_states f st progs n) (progs n)))`;;

let state_co_progs_def = cake_def
  `state_co_progs (f:S->P->S#Q) st (orac:num->P) =
     let states = state_orac_states f st orac in
     \i. SND (f (states i) (orac i))`;;

let add_state_co_def = cake_def
  `add_state_co (f:S->P->S#Q) st (mk:(num->Q)->num->M) (progs:num->P) =
     let states = state_orac_states f st progs in
     let next_progs = state_co_progs f st progs in
     let next_orac = mk next_progs in
     (\i. (states i, next_orac i))`;;

let state_co_add_state_co = prove
 (`state_co (f:S->P->S#Q)
     (syntax_to_full_oracle (add_state_co f st (mk:(num->Q)->num->M)) progs) =
   syntax_to_full_oracle mk (state_co_progs f st progs)`,
  REWRITE_TAC[FUN_EQ_THM; PAIR_FST_SND_EQ; FST_state_co; SND_state_co] THEN
  REWRITE_TAC[syntax_to_full_oracle_def; add_state_co_def; state_co_progs_def;
              LET_DEF; LET_END_DEF; FST; SND]);;

let pure_co_progs_def = cake_def
  `pure_co_progs (f:A->B) (orac:num->A) = f o orac`;;

let pure_co_syntax_to_full_oracle = prove
 (`pure_co (f:A->B) o
   syntax_to_full_oracle ((mk:(num->B)->num->M) o pure_co_progs f) progs =
   syntax_to_full_oracle mk (pure_co_progs f progs)`,
  REWRITE_TAC[FUN_EQ_THM; o_THM; pure_co_def; syntax_to_full_oracle_def;
              pure_co_progs_def; PAIR_MAP_THM; I_THM]);;

let syntax_to_full_oracle_o_assoc = prove
 (`syntax_to_full_oracle ((f:Z->X->M) o (g:Y->Z) o (h:(X->P)->Y)) progs =
   syntax_to_full_oracle ((f o g) o h) progs`,
  REWRITE_TAC[o_ASSOC]);;

let oracle_monotonic_SND_syntax_to_full = prove
 (`(oracle_monotonic ((f:P->B->bool) o SND) R St
      (syntax_to_full_oracle (mk:(num->P)->num->M) progs) <=>
    oracle_monotonic (f o SND) R St (I syntax_to_full_oracle I progs)) /\
   oracle_monotonic ((a:Y->B->bool) o (b:X->Y) o (c:A->X)) =
   oracle_monotonic ((a o b) o c)`,
  REWRITE_TAC[oracle_monotonic_def; syntax_to_full_oracle_def; o_THM; I_THM;
              o_ASSOC]);;

let is_state_oracle_add_state_co = prove
 (`is_state_oracle (f:S->P->S#Q)
     (syntax_to_full_oracle (add_state_co f st (mk:(num->Q)->num->M)) progs)`,
  REWRITE_TAC[is_state_oracle_def; syntax_to_full_oracle_def; add_state_co_def;
              LET_DEF; LET_END_DEF; FST; SND; state_orac_states_def]);;

(* HOL4 computes this theorem as the conjunction of the theorems above    *)
let syntax_oracle_unpack = end_itlist CONJ (map GEN_ALL
  [pure_co_syntax_to_full_oracle; state_co_add_state_co;
   syntax_to_full_oracle_o_assoc; syntax_to_full_oracle_def;
   oracle_monotonic_SND_syntax_to_full; is_state_oracle_add_state_co]);;

let FST_add_state_co_0 = prove
 (`FST (add_state_co (f:S->P->S#Q) st (mk:(num->Q)->num->M) orac 0) = st`,
  REWRITE_TAC[add_state_co_def; state_orac_states_def; LET_DEF; LET_END_DEF;
              FST]);;

let state_orac_states_inv = prove
 (`P st /\
   (!st prog st' prog'. (f_inc:S->Q->S#R) st prog = (st',prog') /\ P st ==> P st')
   ==> P (state_orac_states f_inc st (orac:num->Q) i)`,
  STRIP_TAC THEN SPEC_TAC(`i:num`,`i:num`) THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[state_orac_states_def] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`state_orac_states (f_inc:S->Q->S#R) st (orac:num->Q) i`;
    `(orac:num->Q) i`;
    `SND ((f_inc:S->Q->S#R) (state_orac_states f_inc st orac i) (orac i))`] THEN
  ASM_REWRITE_TAC[PAIR]);;

let backendProps_oracle_monotonic_state_with_inv = prove
 (`!P n_f. P (FST (FST ((orac:num->(S#C)#Q) 0))) /\
     (!x. x IN St ==> x < n_f (FST (FST (orac 0)))) /\
     (!st prog st' prog'. (f_inc:S->Q->S#R) st prog = (st',prog') /\ P st ==>
        P st' /\ n_f st <= n_f st' /\
        (!cfg x. x IN (f:C#R->num->bool) (cfg,prog') ==>
                 n_f st <= x /\ x < n_f st')) /\
     is_state_oracle f_inc orac
     ==> oracle_monotonic f (<) (St:num->bool) (state_co f_inc orac)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "ST")
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ISO")))) THEN
  SUBGOAL_THEN
   `!st prog. P st ==>
      P (FST ((f_inc:S->Q->S#R) st prog)) /\
      n_f st <= n_f (FST (f_inc st prog)) /\
      (!cfg x. x IN (f:C#R->num->bool) (cfg,SND (f_inc st prog)) ==>
               n_f st <= x /\ x < n_f (FST (f_inc st prog)))`
  (LABEL_TAC "H") THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `prog:Q` THEN ASM_REWRITE_TAC[PAIR];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. FST (FST ((orac:num->(S#C)#Q) (SUC i))) =
        FST ((f_inc:S->Q->S#R) (FST (FST (orac i))) (SND (orac i)))`
  (LABEL_TAC "SUC") THENL
   [ASM_MESON_TAC[is_state_oracle_def]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. P (FST (FST ((orac:num->(S#C)#Q) i))) /\
        (!j. j <= i ==>
             n_f (FST (FST (orac j))) <= (n_f:S->num) (FST (FST (orac i))))`
  (LABEL_TAC "C") THENL
   [INDUCT_TAC THENL
     [ASM_REWRITE_TAC[LE; LE_REFL] THEN REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC[LE_REFL];
      FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC) THEN
      USE_THEN "H" (MP_TAC o SPECL [`FST (FST ((orac:num->(S#C)#Q) i))`;
                                    `SND ((orac:num->(S#C)#Q) i)`]) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[LE] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[LE_REFL] THEN
      ASM_MESON_TAC[LE_TRANS]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i cfg x.
      x IN (f:C#R->num->bool)
             (cfg,SND ((f_inc:S->Q->S#R) (FST (FST ((orac:num->(S#C)#Q) i)))
                                         (SND (orac i))))
      ==> n_f (FST (FST (orac i))) <= x /\ x < n_f (FST (FST (orac (SUC i))))`
  (LABEL_TAC "H2") THENL
   [REPEAT GEN_TAC THEN USE_THEN "SUC" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "C" (MP_TAC o CONJUNCT1 o SPEC `i:num`) THEN
    DISCH_THEN(fun th -> USE_THEN "H" (MP_TAC o C MATCH_MP th o
      SPECL [`FST (FST ((orac:num->(S#C)#Q) i))`; `SND ((orac:num->(S#C)#Q) i)`])) THEN
    MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[oracle_monotonic_def] THEN
  SUBGOAL_THEN
   `!i. state_co (f_inc:S->Q->S#R) (orac:num->(S#C)#Q) i =
        (SND (FST (orac i)), SND (f_inc (FST (FST (orac i))) (SND (orac i))))`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[PAIR_FST_SND_EQ; FST_state_co; SND_state_co]; ALL_TAC] THEN
  CONJ_TAC THEN REPEAT STRIP_TAC THENL
   [USE_THEN "H2" (fun h2 -> FIRST_ASSUM(MP_TAC o MP
      (SPECL [`i:num`; `SND (FST ((orac:num->(S#C)#Q) i))`; `x:num`] h2))) THEN
    USE_THEN "H2" (fun h2 -> FIRST_ASSUM(MP_TAC o MP
      (SPECL [`j:num`; `SND (FST ((orac:num->(S#C)#Q) j))`; `y:num`] h2))) THEN
    USE_THEN "C" (MP_TAC o SPEC `SUC i` o CONJUNCT2 o SPEC `j:num`) THEN
    UNDISCH_TAC `i < j:num` THEN ARITH_TAC;
    USE_THEN "H2" (fun h2 -> FIRST_ASSUM(MP_TAC o MP
      (SPECL [`i:num`; `SND (FST ((orac:num->(S#C)#Q) i))`; `y:num`] h2))) THEN
    USE_THEN "C" (MP_TAC o SPEC `0` o CONJUNCT2 o SPEC `i:num`) THEN
    USE_THEN "ST" (fun st -> FIRST_ASSUM(MP_TAC o MP (SPEC `x:num` st))) THEN
    ARITH_TAC]);;

let oracle_monotonic_state_with_inv_init = prove
 (`!P n_f. (f_inc:S->Q->S#R) st0 prog0 = (st,prog) /\ P st0 /\
     St SUBSET (f:C#R->num->bool) (cfg,prog) /\
     FST (FST ((orac:num->(S#C)#Q) 0)) = st /\
     (!st prog st' prog'. f_inc st prog = (st',prog') /\ P st ==>
        P st' /\ n_f st <= n_f st' /\
        (!cfg x. x IN f (cfg,prog') ==> n_f st <= x /\ x < n_f st')) /\
     is_state_oracle f_inc orac
     ==> oracle_monotonic f (<) (St:num->bool) (state_co f_inc orac)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC backendProps_oracle_monotonic_state_with_inv THEN
  MAP_EVERY EXISTS_TAC [`P:S->bool`; `n_f:S->num`] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`st0:S`; `prog0:Q`; `st:S`; `prog:R`] o
    check (is_forall o concl)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBSET]);;

(* HOL4 computes the next two theorems from the two above with P = \x. T *)

let oracle_monotonic_state = prove
 (`!n_f. (!x. x IN St ==> x < n_f (FST (FST ((orac:num->(S#C)#Q) 0)))) /\
     (!st prog st' prog'. (f_inc:S->Q->S#R) st prog = (st',prog') ==>
        n_f st <= n_f st' /\
        (!cfg x. x IN (f:C#R->num->bool) (cfg,prog') ==>
                 n_f st <= x /\ x < n_f st')) /\
     is_state_oracle f_inc orac
     ==> oracle_monotonic f (<) (St:num->bool) (state_co f_inc orac)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC backendProps_oracle_monotonic_state_with_inv THEN
  MAP_EVERY EXISTS_TAC [`\x:S. T`; `n_f:S->num`] THEN
  REWRITE_TAC[] THEN ASM_REWRITE_TAC[]);;

let oracle_monotonic_state_init = prove
 (`!n_f. (f_inc:S->Q->S#R) st0 prog0 = (st,prog) /\
     St SUBSET (f:C#R->num->bool) (cfg,prog) /\
     FST (FST ((orac:num->(S#C)#Q) 0)) = st /\
     (!st prog st' prog'. f_inc st prog = (st',prog') ==>
        n_f st <= n_f st' /\
        (!cfg x. x IN f (cfg,prog') ==> n_f st <= x /\ x < n_f st')) /\
     is_state_oracle f_inc orac
     ==> oracle_monotonic f (<) (St:num->bool) (state_co f_inc orac)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC oracle_monotonic_state_with_inv_init THEN
  MAP_EVERY EXISTS_TAC [`\x:S. T`; `n_f:S->num`] THEN
  REWRITE_TAC[] THEN ASM_REWRITE_TAC[]);;

let restrict_zero_def = cake_def
  `restrict_zero (labels:num#num->bool) = {l | l IN labels /\ SND l = 0}`;;

let restrict_nonzero_def = cake_def
  `restrict_nonzero (labels:num#num->bool) = {l | l IN labels /\ ~(SND l = 0)}`;;

let restrict_nonzero_SUBSET = prove
 (`restrict_nonzero l SUBSET l`,
  REWRITE_TAC[restrict_nonzero_def; SUBSET; IN_ELIM_THM] THEN MESON_TAC[]);;

let restrict_nonzero_SUBSET_left = prove
 (`s SUBSET t ==> restrict_nonzero s SUBSET t`,
  MESON_TAC[restrict_nonzero_SUBSET; SUBSET_TRANS]);;

let restrict_nonzero_left_union = prove
 (`restrict_nonzero s SUBSET a UNION b
   ==> restrict_nonzero s SUBSET restrict_nonzero a UNION b`,
  REWRITE_TAC[restrict_nonzero_def; SUBSET; IN_UNION; IN_ELIM_THM] THEN
  MESON_TAC[]);;

let restrict_nonzero_right_union = prove
 (`restrict_nonzero s SUBSET a UNION b
   ==> restrict_nonzero s SUBSET a UNION restrict_nonzero b`,
  REWRITE_TAC[restrict_nonzero_def; SUBSET; IN_UNION; IN_ELIM_THM] THEN
  MESON_TAC[]);;

let restrict_nonzero_mono = prove
 (`s SUBSET t ==> restrict_nonzero s SUBSET restrict_nonzero t`,
  REWRITE_TAC[restrict_nonzero_def; SUBSET; IN_ELIM_THM] THEN MESON_TAC[]);;

let restrict_nonzero_BIGUNION = prove
 (`restrict_nonzero (UNIONS ss) = UNIONS (IMAGE restrict_nonzero ss)`,
  REWRITE_TAC[restrict_nonzero_def; EXTENSION; IN_UNIONS; EXISTS_IN_IMAGE;
              IN_ELIM_THM] THEN
  MESON_TAC[]);;

let option_le_def = cake_def
  `(option_le (_:num option) NONE <=> T) /\
   (option_le NONE (SOME (_:num)) <=> F) /\
   (option_le (SOME n1) (SOME n2) <=> n1 <= n2)`;;
let _ = cake_add_simps [option_le_def];;

let option_le_refl = prove
 (`!x. option_le x x`,
  GEN_TAC THEN CASES_ON `x:num option` THEN FS[option_le_def]);;
let _ = cake_add_simps [option_le_refl];;

let option_le_SOME_0 = prove
 (`option_le (SOME 0) x`,
  CASES_ON `x:num option` THEN FS[option_le_def]);;
let _ = cake_add_simps [option_le_SOME_0];;

let option_le_trans = prove
 (`!x y z. option_le x y /\ option_le y z ==> option_le x z`,
  REPEAT GEN_TAC THEN CASES_ON `x:num option` THEN CASES_ON `y:num option` THEN
  CASES_ON `z:num option` THEN FS[option_le_def] THEN ARITH_TAC);;

let option_le_max = prove
 (`option_le (OPTION_MAP2 MAX n m) x <=> option_le n x /\ option_le m x`,
  CASES_ON `x:num option` THEN CASES_ON `n:num option` THEN
  CASES_ON `m:num option` THEN RW[option_le_def; OPTION_MAP2_THM] THEN
  ARITH_TAC);;

let option_le_max_right = prove
 (`option_le x (OPTION_MAP2 MAX n m) <=> option_le x n \/ option_le x m`,
  CASES_ON `x:num option` THEN CASES_ON `n:num option` THEN
  CASES_ON `m:num option` THEN RW[option_le_def; OPTION_MAP2_THM] THEN
  ARITH_TAC);;

let option_add_comm = prove
 (`OPTION_MAP2 (+) (n:num option) m = OPTION_MAP2 (+) m n`,
  CASES_ON `n:num option` THEN CASES_ON `m:num option` THEN
  RW[OPTION_MAP2_THM; ADD_SYM]);;

let option_add_assoc = prove
 (`OPTION_MAP2 (+) (n:num option) (OPTION_MAP2 (+) m p) =
   OPTION_MAP2 (+) (OPTION_MAP2 (+) n m) p`,
  CASES_ON `n:num option` THEN CASES_ON `m:num option` THEN
  CASES_ON `p:num option` THEN RW[OPTION_MAP2_THM; ADD_ASSOC]);;

let option_le_eq_eqns = prove
 (`(option_le (OPTION_MAP2 (+) n m) (OPTION_MAP2 (+) n p) <=>
    n = NONE \/ option_le m p) /\
   (option_le (OPTION_MAP2 (+) n m) (OPTION_MAP2 (+) p n) <=>
    n = NONE \/ option_le m p) /\
   (option_le (OPTION_MAP2 (+) n m) (OPTION_MAP2 (+) p m) <=>
    m = NONE \/ option_le n p) /\
   (option_le (OPTION_MAP2 (+) n m) (OPTION_MAP2 (+) m p) <=>
    m = NONE \/ option_le n p)`,
  CASES_ON `n:num option` THEN CASES_ON `m:num option` THEN
  CASES_ON `p:num option` THEN RW[option_le_def; OPTION_MAP2_THM] THEN
  ARITH_TAC);;

let option_map2_max_add = prove
 (`(OPTION_MAP2 (+) n (OPTION_MAP2 MAX m p) =
    OPTION_MAP2 MAX (OPTION_MAP2 (+) n m) (OPTION_MAP2 (+) n p)) /\
   (OPTION_MAP2 (+) (OPTION_MAP2 MAX m p) n =
    OPTION_MAP2 MAX (OPTION_MAP2 (+) m n) (OPTION_MAP2 (+) p n))`,
  CASES_ON `n:num option` THEN CASES_ON `m:num option` THEN
  CASES_ON `p:num option` THEN REWRITE_TAC[OPTION_MAP2_THM; option_INJ] THEN
  ARITH_TAC);;

let option_le_add = prove
 (`option_le n (OPTION_MAP2 (+) n m)`,
  CASES_ON `n:num option` THEN CASES_ON `m:num option` THEN
  RW[option_le_def; OPTION_MAP2_THM] THEN ARITH_TAC);;

let OPTION_MAP2_MAX_COMM = prove
 (`OPTION_MAP2 MAX x y = OPTION_MAP2 MAX y x`,
  CASES_ON `x:num option` THEN CASES_ON `y:num option` THEN
  REWRITE_TAC[OPTION_MAP2_THM; option_INJ] THEN ARITH_TAC);;

let OPTION_MAP2_MAX_ASSOC = prove
 (`OPTION_MAP2 MAX x (OPTION_MAP2 MAX y z) =
   OPTION_MAP2 MAX (OPTION_MAP2 MAX x y) z`,
  CASES_ON `x:num option` THEN CASES_ON `y:num option` THEN
  CASES_ON `z:num option` THEN REWRITE_TAC[OPTION_MAP2_THM; option_INJ] THEN
  ARITH_TAC);;
