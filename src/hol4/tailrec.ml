(* ========================================================================= *)
(* tailrec: port of HOL4 examples/machine-code/hoare-triple/tailrecScript.sml *)
(* (HOL4 library used by CakeML v3479, compiler/backend/proofs/              *)
(* word_bignumProofScript.sml): tail-recursive functions given by a step, a *)
(* guard and an exit function, with their preconditions.                    *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - HOL4 tailrec$TAILREC is tailrec_TAILREC (TAILREC is HOL4 While$TAILREC, *)
(*   defined in hol4/basic.ml); its definition TAILREC_def is                *)
(*   tailrec_TAILREC_def.  The other names are HOL4's.                       *)
(* - FUNPOW f n x is ITER n f x.                                             *)
(* - HOL4's sum recogniser ISL (with its theorem ISL) is defined here: no    *)
(*   other file of the port has it.                                          *)
(* ========================================================================= *)

needs "hol4/basic.ml";;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* HOL4 sum: the recogniser ISL (its theorem ISL is a HOL4 simp rule).       *)
(* ------------------------------------------------------------------------- *)

let ISL =
  let th = new_recursive_definition sum_RECURSION
    `(ISL (INL (x:A):A+B) <=> T) /\ (ISL (INR (y:B):A+B) <=> F)` in
  prove
   (`(!x:A. ISL (INL x:A+B)) /\ (!y:B. ~ISL (INR y:A+B))`,
    REWRITE_TAC[th]);;

(* ------------------------------------------------------------------------- *)
(* Definitions.                                                              *)
(* ------------------------------------------------------------------------- *)

(* the definitions are restated with HOL4's order of the variables *)

let TAILREC_PRE_def =
  let th = new_definition
    `TAILREC_PRE (f1:A->A) guard precondition (x:A) <=>
       (!k. (!m. m < k ==> guard (ITER m f1 x))
            ==> precondition (ITER k f1 x)) /\
       (?n. ~guard (ITER n f1 x))` in
  prove
   (`!(f1:A->A) guard precondition (x:A).
       TAILREC_PRE f1 guard precondition x <=>
       (!k. (!m. m < k ==> guard (ITER m f1 x))
            ==> precondition (ITER k f1 x)) /\
       (?n. ~guard (ITER n f1 x))`,
    REWRITE_TAC[th]);;

(* HOL4: TAILREC_def *)

let tailrec_TAILREC_def =
  let th = new_definition
    `tailrec_TAILREC (f1:A->A) (f2:A->B) g x = f2 (WHILE g f1 x)` in
  prove
   (`!(f1:A->A) (f2:A->B) g x. tailrec_TAILREC f1 f2 g x = f2 (WHILE g f1 x)`,
    REWRITE_TAC[th]);;

let SHORT_TAILREC_def = new_definition
  `SHORT_TAILREC (f:A->(A+B)#bool) =
     tailrec_TAILREC (OUTL o FST o f) (OUTR o FST o f) (ISL o FST o f)`;;

let SHORT_TAILREC_PRE_def = new_definition
  `SHORT_TAILREC_PRE (f:A->(A+B)#bool) =
     TAILREC_PRE (OUTL o FST o f) (ISL o FST o f) (SND o f)`;;

(* ------------------------------------------------------------------------- *)
(* Theorems.                                                                 *)
(* ------------------------------------------------------------------------- *)

(* helpers: splitting a quantifier over num at 0 and SUC *)

let LSMALLAUX_FORALL_NUM = MESON[num_CASES]
  `!P. (!n. P n) <=> P 0 /\ (!n. P (SUC n))`;;

let LSMALLAUX_EXISTS_NUM = MESON[num_CASES]
  `!P. (?n. P n) <=> P 0 \/ (?n. P (SUC n))`;;

let LSMALLAUX_FORALL_LT_SUC = prove
 (`!(R:num->bool) k.
     (!m. m < SUC k ==> R m) <=> R 0 /\ (!m. m < k ==> R (SUC m))`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [MESON_TAC[LT_0; LT_SUC];
    STRIP_TAC THEN INDUCT_TAC THEN ASM_SIMP_TAC[LT_SUC]]);;

let TAILREC_PRE_THM = prove
 (`!f1 g p x. TAILREC_PRE f1 g p (x:A) <=>
              p x /\ (g x ==> TAILREC_PRE f1 g p (f1 x))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[TAILREC_PRE_def] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
    [LSMALLAUX_FORALL_NUM; LSMALLAUX_EXISTS_NUM] THEN
  REWRITE_TAC[LSMALLAUX_FORALL_LT_SUC; CONJUNCT1 LT; ITER_ALT] THEN
  ASM_CASES_TAC `(g:A->bool) x` THEN ASM_REWRITE_TAC[CONJ_ASSOC]);;

let TAILREC_PRE_INDUCT = prove
 (`!P. (!x. TAILREC_PRE f1 g p x /\ p x /\ g x /\ P (f1 x) ==> P x) /\
       (!x. TAILREC_PRE f1 g p x /\ p x /\ ~g x ==> P x) ==>
       (!x. TAILREC_PRE f1 g p x ==> P (x:A))`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!n (x:A). ~(g:A->bool) (ITER n (f1:A->A) x) /\
                          TAILREC_PRE f1 g (p:A->bool) x ==> (P:A->bool) x`
    (fun th -> ASM_MESON_TAC[th; TAILREC_PRE_def]) THEN
  INDUCT_TAC THEN REWRITE_TAC[ITER_ALT] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [TAILREC_PRE_THM]) THEN
  ASM_CASES_TAC `(g:A->bool) x` THEN ASM_MESON_TAC[]);;

let TAILREC_THM = prove
 (`!f1 (f2:A->B) g x.
     tailrec_TAILREC f1 f2 g x =
     if g x then tailrec_TAILREC f1 f2 g (f1 x) else f2 x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tailrec_TAILREC_def] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [WHILE] THEN
  COND_CASES_TAC THEN REWRITE_TAC[]);;

let TAILREC_PRE_IMP = prove
 (`!step guard side.
     (?R. WF R /\ !x. guard x ==> R (step x) x) /\ (!x:A. side x) ==>
     !x. TAILREC_PRE step guard side x <=> T`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `R:A->A->bool` STRIP_ASSUME_TAC)
                             ASSUME_TAC) THEN
  ASM_REWRITE_TAC[TAILREC_PRE_def] THEN X_GEN_TAC `x:A` THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [WF_DCHAIN]) THEN
  REWRITE_TAC[NOT_EXISTS_THM; CONTRAPOS_THM; NOT_FORALL_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `\n. ITER n (step:A->A) x`) THEN
  REWRITE_TAC[ITER] THEN ASM_MESON_TAC[]);;

let TAILREC_EQ_THM = prove
 (`(f1 = f1') /\ (f2 = (f2':A->B)) /\ (g = g') /\ (s = s') ==>
   (tailrec_TAILREC f1 f2 g = tailrec_TAILREC f1' f2' g') /\
   (TAILREC_PRE f1 g s = TAILREC_PRE f1' g' s')`,
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let SHORT_TAILREC_THM = prove
 (`!(f:A->(A+B)#bool) x.
     (SHORT_TAILREC f x =
        if ISL (FST (f x)) then SHORT_TAILREC f (OUTL (FST (f x)))
        else OUTR (FST (f x))) /\
     (SHORT_TAILREC_PRE f x <=>
        SND (f x) /\
        (ISL (FST (f x)) ==> SHORT_TAILREC_PRE f (OUTL (FST (f x)))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SHORT_TAILREC_def; SHORT_TAILREC_PRE_def] THEN
  CONJ_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [TAILREC_THM];
    GEN_REWRITE_TAC LAND_CONV [TAILREC_PRE_THM]] THEN
  REWRITE_TAC[o_THM]);;

let SHORT_TAILREC_PRE_INDUCT = prove
 (`!P. (!x. SHORT_TAILREC_PRE f x /\ SND (f x) /\
            (!y. FST (f x) = INL y ==> P y) ==> P x) ==>
       (!x. SHORT_TAILREC_PRE (f:A->(A+B)#bool) x ==> P x)`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[SHORT_TAILREC_PRE_def] THEN
  MATCH_MP_TAC TAILREC_PRE_INDUCT THEN REWRITE_TAC[o_THM] THEN
  CONJ_TAC THEN X_GEN_TAC `x:A` THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[SHORT_TAILREC_PRE_def] THEN
  X_GEN_TAC `y:A` THEN DISCH_THEN SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ISL; OUTL]) THEN ASM_MESON_TAC[]);;

(* the variable r of the hypothesis is unused, as in HOL4 (type E) *)

let SHORT_TAILREC_SIM = prove
 (`!f g R P.
     (!x s q (r:E).
        R x s /\ (f x = (q,T)) ==>
        (!y. (q = INL y) ==> ?y1. (g s = (INL y1,T)) /\ R y y1) /\
        (!y. (q = INR y) ==> ?y1. (g s = (INR y1,T)) /\ P y y1)) ==>
     !x. SHORT_TAILREC_PRE (f:A->(A+B)#bool) x ==>
         !s. R x s ==>
             P (SHORT_TAILREC f x) (SHORT_TAILREC (g:C->(C+D)#bool) s) /\
             SHORT_TAILREC_PRE g s`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC SHORT_TAILREC_PRE_INDUCT THEN
  X_GEN_TAC `x:A` THEN STRIP_TAC THEN X_GEN_TAC `s:C` THEN DISCH_TAC THEN
  MP_TAC(ISPEC `(f:A->(A+B)#bool) x` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`q:A+B`; `b:bool`] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  SUBGOAL_THEN `(f:A->(A+B)#bool) x = (q,T)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:A`; `s:C`; `q:A+B`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISJ_CASES_THEN2 (X_CHOOSE_THEN `y:A` SUBST_ALL_TAC)
    (X_CHOOSE_THEN `z:B` SUBST_ALL_TAC) (ISPEC `q:A+B` (cases "sum")) THEN
  REWRITE_TAC[injectivity "sum"; distinctness "sum"] THENL
   [DISCH_THEN(MP_TAC o SPEC `y:A`) THEN REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `y1:C` STRIP_ASSUME_TAC);
    DISCH_THEN(MP_TAC o SPEC `z:B`) THEN REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `z1:D` STRIP_ASSUME_TAC)] THEN
  ONCE_REWRITE_TAC[SHORT_TAILREC_THM] THEN ASM_REWRITE_TAC[ISL; OUTL; OUTR] THEN
  ASM_MESON_TAC[]);;

let _ = cake_add_simps [ISL];;
