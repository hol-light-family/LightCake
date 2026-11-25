(* ========================================================================= *)
(* ml_optimise: port of HOL4 translator/ml_optimiseScript.sml (CakeML      *)
(* v3479).  A simple verified optimiser for CakeML expressions, which is   *)
(* applied once the translator has produced some CakeML syntax.            *)
(*                                                                           *)
(* The HOL-->ML translator occasionally produces clunky code.  This file   *)
(* defines a verified optimiser which is used to simplify the clunky parts *)
(* of the generated code.  This optimiser:                                  *)
(*  - first, rewrites (fn x => exp) y to let x = y in exp                   *)
(*  - then, a number of rewrites are applied, e.g.                          *)
(*      x - n + n --> x,  x + n - n --> x,  let x = y in x --> y            *)
(* ========================================================================= *)

needs "translator/ml_prog.ml";;
needs "translator/ml_translator.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/proofs/evaluateProps.ml";;
needs "semantics/evaluate.ml";;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* first an optimisation combinator: BOTTOM_UP_OPT                           *)
(* ------------------------------------------------------------------------- *)

(* HOL4 defines BOTTOM_UP_OPT with an unused let ys = BOTTOM_UP_OPT_LIST f  *)
(* (REVERSE xs) in the Con and App clauses (to get the REVERSE xs case into *)
(* the induction theorem) and then rebinds BOTTOM_UP_OPT_def without the    *)
(* lets.  Here the definition is made directly without them, and           *)
(* BOTTOM_UP_OPT_ind (with the REVERSE xs hypotheses) is proved from the   *)
(* structural induction theorem of the definition.                          *)

let BOTTOM_UP_OPT_def = cake_def
  `(BOTTOM_UP_OPT f (Lit v) = f (Lit v)) /\
   (BOTTOM_UP_OPT f (Raise ex) = f (Raise ex)) /\
   (BOTTOM_UP_OPT f (Var name) = f (Var name)) /\
   (BOTTOM_UP_OPT f (Con tag xs) = f (Con tag (BOTTOM_UP_OPT_LIST f xs))) /\
   (BOTTOM_UP_OPT f (Fun vn x) = f (Fun vn x)) /\
   (BOTTOM_UP_OPT f (App op xs) = f (App op (BOTTOM_UP_OPT_LIST f xs))) /\
   (BOTTOM_UP_OPT f (Log lop x1 x2) =
      f (Log lop (BOTTOM_UP_OPT f x1) (BOTTOM_UP_OPT f x2))) /\
   (BOTTOM_UP_OPT f (If x1 x2 x3) =
      f (If (BOTTOM_UP_OPT f x1) (BOTTOM_UP_OPT f x2) (BOTTOM_UP_OPT f x3))) /\
   (BOTTOM_UP_OPT f (Mat x pes) = f (Mat (BOTTOM_UP_OPT f x) (BOTTOM_UP_OPT_PAT f pes))) /\
   (BOTTOM_UP_OPT f (Let vo x1 x2) =
      f (Let vo (BOTTOM_UP_OPT f x1) (BOTTOM_UP_OPT f x2))) /\
   (BOTTOM_UP_OPT f (Handle x pes) = Handle x pes) /\
   (BOTTOM_UP_OPT f (Letrec z1 z2) = f (Letrec z1 z2)) /\
   (BOTTOM_UP_OPT f (Tannot x t) = Tannot (BOTTOM_UP_OPT f x) t) /\
   (BOTTOM_UP_OPT f (Lannot x lc) = Lannot (BOTTOM_UP_OPT f x) lc) /\
   (BOTTOM_UP_OPT_LIST f [] = []) /\
   (BOTTOM_UP_OPT_LIST f (CONS y ys) =
      CONS (BOTTOM_UP_OPT f y) (BOTTOM_UP_OPT_LIST f ys)) /\
   (BOTTOM_UP_OPT_PAT f [] = []) /\
   (BOTTOM_UP_OPT_PAT f (CONS (p,y) pes) =
      CONS (p,BOTTOM_UP_OPT f y) (BOTTOM_UP_OPT_PAT f pes))`;;

let TR2OPTAUX_BOTTOM_UP_OPT_ind0 = cake_ind "BOTTOM_UP_OPT";;

(* HOL4's induction theorem of BOTTOM_UP_OPT, with the hypotheses for       *)
(* REVERSE xs in the Con and App cases (TFL's let context ys = ... is       *)
(* dropped: it only restates the hypothesis for xs)                          *)

let BOTTOM_UP_OPT_ind = prove
 (`!(P0:(exp->exp)->exp->bool) (P1:(exp->exp)->exp list->bool)
    (P2:(exp->exp)->(pat#exp)list->bool).
     (!f v. P0 f (Lit v)) /\
     (!f ex. P0 f (Raise ex)) /\
     (!f name. P0 f (Var name)) /\
     (!f tag xs. P1 f (REVERSE xs) /\ P1 f xs ==> P0 f (Con tag xs)) /\
     (!f vn x. P0 f (Fun vn x)) /\
     (!f op xs. P1 f (REVERSE xs) /\ P1 f xs ==> P0 f (App op xs)) /\
     (!f lop x1 x2. P0 f x1 /\ P0 f x2 ==> P0 f (Log lop x1 x2)) /\
     (!f x1 x2 x3. P0 f x1 /\ P0 f x2 /\ P0 f x3 ==> P0 f (If x1 x2 x3)) /\
     (!f x pes. P0 f x /\ P2 f pes ==> P0 f (Mat x pes)) /\
     (!f vo x1 x2. P0 f x1 /\ P0 f x2 ==> P0 f (Let vo x1 x2)) /\
     (!f x pes. P0 f (Handle x pes)) /\
     (!f z1 z2. P0 f (Letrec z1 z2)) /\
     (!f x t. P0 f x ==> P0 f (Tannot x t)) /\
     (!f x lc. P0 f x ==> P0 f (Lannot x lc)) /\
     (!f. P1 f []) /\
     (!f y ys. P0 f y /\ P1 f ys ==> P1 f (CONS y ys)) /\
     (!f. P2 f []) /\
     (!f p y pes. P0 f y /\ P2 f pes ==> P2 f (CONS (p,y) pes))
     ==> (!f x. P0 f x) /\ (!f xs. P1 f xs) /\ (!f pes. P2 f pes)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!f xs. ALL ((P0:(exp->exp)->exp->bool) f) xs ==>
                       (P1:(exp->exp)->exp list->bool) f xs`
    ASSUME_TAC THENL
   [GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_SIMP_TAC[ALL]; ALL_TAC] THEN
  MP_TAC(ISPECL [`P0:(exp->exp)->exp->bool`;
    `\f xs. (P1:(exp->exp)->exp list->bool) f xs /\
            ALL ((P0:(exp->exp)->exp->bool) f) xs`;
    `P2:(exp->exp)->(pat#exp)list->bool`] TR2OPTAUX_BOTTOM_UP_OPT_ind0) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[ALL] THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[EVERY_REVERSE];
    SIMP_TAC[]]);;

(* HOL4 [local] *)

let LENGTH_BOTTOM_UP_OPT_LIST = prove
 (`!xs. LENGTH (BOTTOM_UP_OPT_LIST f xs) = LENGTH xs`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[BOTTOM_UP_OPT_def; LENGTH]);;

(* HOL4 [local] *)

let BOTTOM_UP_OPT_LIST_APPEND = prove
 (`!xs ys. BOTTOM_UP_OPT_LIST f (APPEND xs ys) =
           APPEND (BOTTOM_UP_OPT_LIST f xs) (BOTTOM_UP_OPT_LIST f ys)`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[BOTTOM_UP_OPT_def; APPEND]);;

(* HOL4 [local] *)

let REVERSE_BOTTOM_UP_OPT_LIST = prove
 (`!xs. REVERSE (BOTTOM_UP_OPT_LIST f xs) = BOTTOM_UP_OPT_LIST f (REVERSE xs)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[BOTTOM_UP_OPT_def; REVERSE; BOTTOM_UP_OPT_LIST_APPEND]);;

(* HOL4: dec_clock_with_clock [simp] (names.tsv ml_optimise_dec_clock_with_clock) *)

let ml_optimise_dec_clock_with_clock = prove
 (`state_clock_fupd (K c) (dec_clock st1) = state_clock_fupd (K c) (st1:(FFI)state)`,
  REWRITE_TAC[dec_clock_def; state_component_equality] THEN SIMP[]);;
let _ = cake_add_simps [ml_optimise_dec_clock_with_clock];;

let MAP_FST_BOTTOM_UP_OPT_PAT = prove
 (`MAP FST (BOTTOM_UP_OPT_PAT f ys) = MAP FST ys`,
  SPEC_TAC(`ys:(pat#exp)list`,`ys:(pat#exp)list`) THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[BOTTOM_UP_OPT_def; MAP] THEN
  PAIR_CASES_ON `h:pat#exp` THEN ASM_REWRITE_TAC[BOTTOM_UP_OPT_def; MAP]);;

(* helper of the port: clock updates of a state *)

let TR2OPTAUX_clock_fupd = prove
 (`(!a b (s:(FFI)state). state_clock_fupd (K a) (state_clock_fupd (K b) s) =
                         state_clock_fupd (K a) s) /\
   (!s:(FFI)state. state_clock_fupd (K (state_clock s)) s = s) /\
   (!a (s:(FFI)state). state_clock (state_clock_fupd (K a) s) = a) /\
   (!a (s:(FFI)state). state_refs (state_clock_fupd (K a) s) = state_refs s)`,
  REWRITE_TAC[state_component_equality] THEN SIMP[]);;

let evaluate_two_steps_clock = prove
 (`evaluate st1 env1 xs1 = (state_clock_fupd (K ck2) st2,Rval v2) /\
   evaluate (state_clock_fupd (K ck3) st2) env2 xs2 = (st3,Rval v3) ==>
   ?n_ck1 n_ck2 n_ck3.
     evaluate (state_clock_fupd (K n_ck1) st1) env1 xs1 =
       (state_clock_fupd (K n_ck2) (st2:(FFI)state),Rval v2) /\
     evaluate (state_clock_fupd (K n_ck2) st2) env2 xs2 =
       (state_clock_fupd (K n_ck3) st3,Rval v3)`,
  STRIP_TAC THEN
  MP_TAC(ISPECL [`st1:(FFI)state`; `env1:v sem_env`; `xs1:exp list`;
    `state_clock_fupd (K ck2) (st2:(FFI)state)`; `Rval v2:(v list,v)result`; `ck3:num`]
    evaluate_add_to_clock) THEN
  MP_TAC(ISPECL [`state_clock_fupd (K ck3) (st2:(FFI)state)`; `env2:v sem_env`;
    `xs2:exp list`; `st3:(FFI)state`; `Rval v3:(v list,v)result`; `ck2:num`]
    evaluate_add_to_clock) THEN
  ASM_REWRITE_TAC[distinctness "result"; TR2OPTAUX_clock_fupd] THEN
  REPEAT DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC [`state_clock (st1:(FFI)state) + ck3`; `ck2 + ck3:num`;
    `state_clock (st3:(FFI)state) + ck2`] THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    SUBST1_TAC(ARITH_RULE `ck2 + ck3 = ck3 + ck2:num`) THEN ASM_REWRITE_TAC[]]);;

let evaluate_and_match_clock = prove
 (`evaluate st1 env1 xs1 = (state_clock_fupd (K ck2) st2,Rval v2) /\
   evaluate_match (state_clock_fupd (K ck3) st2) env2 m2 p2 exn2 = (st3,Rval v3) ==>
   ?n_ck1 n_ck2 n_ck3.
     evaluate (state_clock_fupd (K n_ck1) st1) env1 xs1 =
       (state_clock_fupd (K n_ck2) (st2:(FFI)state),Rval v2) /\
     evaluate_match (state_clock_fupd (K n_ck2) st2) env2 m2 p2 exn2 =
       (state_clock_fupd (K n_ck3) st3,Rval v3)`,
  STRIP_TAC THEN
  MP_TAC(ISPECL [`st1:(FFI)state`; `env1:v sem_env`; `xs1:exp list`;
    `state_clock_fupd (K ck2) (st2:(FFI)state)`; `Rval v2:(v list,v)result`; `ck3:num`]
    evaluate_add_to_clock) THEN
  MP_TAC(ISPECL [`state_clock_fupd (K ck3) (st2:(FFI)state)`; `env2:v sem_env`;
    `m2:v`; `p2:(pat#exp)list`; `exn2:v`; `st3:(FFI)state`; `Rval v3:(v list,v)result`;
    `ck2:num`] evaluate_match_add_to_clock) THEN
  ASM_REWRITE_TAC[distinctness "result"; TR2OPTAUX_clock_fupd] THEN
  REPEAT DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC [`state_clock (st1:(FFI)state) + ck3`; `ck2 + ck3:num`;
    `state_clock (st3:(FFI)state) + ck2`] THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    SUBST1_TAC(ARITH_RULE `ck2 + ck3 = ck3 + ck2:num`) THEN ASM_REWRITE_TAC[]]);;

(* helpers of the port for BOTTOM_UP_OPT_THM1: evaluations whose final      *)
(* clock is arbitrary, from the eval_rel facts of the induction            *)

let TR2OPTAUX_evaluate_match_set_clock = prove
 (`!(s:(FFI)state) env v pes err_v s1 res.
     evaluate_match s env v pes err_v = (s1,res) /\
     ~(res = Rerr (Rabort Rtimeout_error)) ==>
     !ck. ?ck1. evaluate_match (state_clock_fupd (K ck1) s) env v pes err_v =
                (state_clock_fupd (K ck) s1,res)`,
  MESON_TAC(map (BETA_RULE o MATCH_MP is_clock_io_mono_set_clock o SPEC_ALL)
              (CONJUNCTS is_clock_io_mono_evaluate)));;

let TR2OPTAUX_ANY_EXP = prove
 (`!e e' (s:(FFI)state) env s2 v.
     (!s1 r. eval_rel s env e s1 r ==> eval_rel s env e' s1 r) /\
     evaluate s env [e] = (s2,Rval [v]) ==>
     !ck. ?ck1. evaluate (state_clock_fupd (K ck1) s) env [e'] =
                (state_clock_fupd (K ck) s2,Rval [v])`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(MP_TAC o SPECL
    [`state_clock_fupd (K (state_clock (s:(FFI)state))) (s2:(FFI)state)`; `v:v`]) THEN
  REWRITE_TAC[eval_rel_def; TR2OPTAUX_clock_fupd] THEN ANTS_TAC THENL
   [MAP_EVERY EXISTS_TAC [`state_clock (s:(FFI)state)`; `state_clock (s2:(FFI)state)`] THEN
    ASM_REWRITE_TAC[TR2OPTAUX_clock_fupd];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c1:num` (X_CHOOSE_TAC `c2:num`)) THEN
  X_GEN_TAC `ck:num` THEN
  MP_TAC(ISPECL [`state_clock_fupd (K c1) (s:(FFI)state)`; `env:v sem_env`; `[e']:exp list`;
    `state_clock_fupd (K c2) (s2:(FFI)state)`; `Rval [v]:(v list,v)result`]
    evaluate_set_clock) THEN
  ASM_REWRITE_TAC[distinctness "result"; TR2OPTAUX_clock_fupd] THEN
  DISCH_THEN(MP_TAC o SPEC `ck:num`) THEN REWRITE_TAC[TR2OPTAUX_clock_fupd]);;

let TR2OPTAUX_ANY_LIST = prove
 (`!es es' (s:(FFI)state) env s2 vs.
     (!s1 r. eval_list_rel s env es s1 r ==> eval_list_rel s env es' s1 r) /\
     evaluate s env es = (s2,Rval vs) ==>
     !ck. ?ck1. evaluate (state_clock_fupd (K ck1) s) env es' =
                (state_clock_fupd (K ck) s2,Rval vs)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(MP_TAC o SPECL
    [`state_clock_fupd (K (state_clock (s:(FFI)state))) (s2:(FFI)state)`; `vs:v list`]) THEN
  REWRITE_TAC[eval_list_rel_def; TR2OPTAUX_clock_fupd] THEN ANTS_TAC THENL
   [MAP_EVERY EXISTS_TAC [`state_clock (s:(FFI)state)`; `state_clock (s2:(FFI)state)`] THEN
    ASM_REWRITE_TAC[TR2OPTAUX_clock_fupd];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c1:num` (X_CHOOSE_TAC `c2:num`)) THEN
  X_GEN_TAC `ck:num` THEN
  MP_TAC(ISPECL [`state_clock_fupd (K c1) (s:(FFI)state)`; `env:v sem_env`; `es':exp list`;
    `state_clock_fupd (K c2) (s2:(FFI)state)`; `Rval vs:(v list,v)result`]
    evaluate_set_clock) THEN
  ASM_REWRITE_TAC[distinctness "result"; TR2OPTAUX_clock_fupd] THEN
  DISCH_THEN(MP_TAC o SPEC `ck:num`) THEN REWRITE_TAC[TR2OPTAUX_clock_fupd]);;

let TR2OPTAUX_ANY_MATCH = prove
 (`!pes pes' (s:(FFI)state) env v err s2 r.
     (!s1 r. eval_match_rel s env v pes err s1 r ==>
             eval_match_rel s env v pes' err s1 r) /\
     evaluate_match s env v pes err = (s2,Rval [r]) ==>
     !ck. ?ck1. evaluate_match (state_clock_fupd (K ck1) s) env v pes' err =
                (state_clock_fupd (K ck) s2,Rval [r])`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(MP_TAC o SPECL
    [`state_clock_fupd (K (state_clock (s:(FFI)state))) (s2:(FFI)state)`; `r:v`]) THEN
  REWRITE_TAC[eval_match_rel_def; TR2OPTAUX_clock_fupd] THEN ANTS_TAC THENL
   [MAP_EVERY EXISTS_TAC [`state_clock (s:(FFI)state)`; `state_clock (s2:(FFI)state)`] THEN
    ASM_REWRITE_TAC[TR2OPTAUX_clock_fupd];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c1:num` (X_CHOOSE_TAC `c2:num`)) THEN
  X_GEN_TAC `ck:num` THEN
  MP_TAC(ISPECL [`state_clock_fupd (K c1) (s:(FFI)state)`; `env:v sem_env`; `v:v`;
    `pes':(pat#exp)list`; `err:v`;
    `state_clock_fupd (K c2) (s2:(FFI)state)`; `Rval [r]:(v list,v)result`]
    TR2OPTAUX_evaluate_match_set_clock) THEN
  ASM_REWRITE_TAC[distinctness "result"; TR2OPTAUX_clock_fupd] THEN
  DISCH_THEN(MP_TAC o SPEC `ck:num`) THEN REWRITE_TAC[TR2OPTAUX_clock_fupd]);;

(* the first evaluation step of a successful evaluation, and evaluations to *)
(* an arbitrary final clock built from such steps                           *)

let TR2OPTAUX_DEC_STEP_TAC e1 =
  REPEAT GEN_TAC THEN REWRITE_TAC[evaluate_def] THEN
  MP_TAC(ISPEC e1 PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `st':(FFI)state` (X_CHOOSE_THEN `res:(v list,v)result`
    (fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th))) THEN
  CASES_ON `res:(v list,v)result` THEN
  CASE_REWRITE_TAC[PAIR_EQ; distinctness "result"] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `v1:v` SUBST_ALL_TAC o MATCH_MP evaluate_sing) THEN
  REWRITE_TAC[HD];;

let TR2OPTAUX_DEC_Log = prove
 (`!(st:(FFI)state) env lop e1 e2 s1 vs.
     evaluate st env [Log lop e1 e2] = (s1,Rval vs) ==>
     ?st' v1. evaluate st env [e1] = (st',Rval [v1]) /\
       ((do_log lop v1 e2 = SOME (Exp e2) /\ evaluate st' env [e2] = (s1,Rval vs)) \/
        (?w. do_log lop v1 e2 = SOME (Val w) /\ st' = s1 /\ vs = [w]))`,
  TR2OPTAUX_DEC_STEP_TAC `evaluate (st:(FFI)state) env [e1]` THEN
  DISCH_TAC THEN MAP_EVERY EXISTS_TAC [`st':(FFI)state`; `v1:v`] THEN
  ASM_REWRITE_TAC[] THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[do_log_def] THEN
  REPEAT COND_CASES_TAC THEN CASE_REWRITE_TAC[PAIR_EQ; distinctness "result";
    injectivity "result"; injectivity "option"; distinctness "option";
    injectivity "exp_or_val"; distinctness "exp_or_val"] THEN
  MESON_TAC[]);;

let TR2OPTAUX_EVG_Log = prove
 (`!(s:(FFI)state) env lop e1 e2 st v1 s1 vs.
     (!ck. ?ck1. evaluate (state_clock_fupd (K ck1) s) env [e1] =
                 (state_clock_fupd (K ck) st,Rval [v1])) /\
     ((do_log lop v1 e2 = SOME (Exp e2) /\
       (!ck. ?ck1. evaluate (state_clock_fupd (K ck1) st) env [e2] =
                   (state_clock_fupd (K ck) s1,Rval vs))) \/
      (?w. do_log lop v1 e2 = SOME (Val w) /\ st = s1 /\ vs = [w])) ==>
     !ck. ?ck1. evaluate (state_clock_fupd (K ck1) s) env [Log lop e1 e2] =
                (state_clock_fupd (K ck) s1,Rval vs)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "h1") MP_TAC) THEN
  STRIP_TAC THEN X_GEN_TAC `ck:num` THENL
   [FIRST_X_ASSUM(X_CHOOSE_TAC `c2:num` o SPEC `ck:num`) THEN
    REMOVE_THEN "h1" (X_CHOOSE_TAC `c1:num` o SPEC `c2:num`) THEN
    EXISTS_TAC `c1:num` THEN ASM_REWRITE_TAC[evaluate_def] THEN
    CASE_REWRITE_TAC[HD] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[];
    REMOVE_THEN "h1" (X_CHOOSE_TAC `c1:num` o SPEC `ck:num`) THEN
    EXISTS_TAC `c1:num` THEN ASM_REWRITE_TAC[evaluate_def] THEN
    CASE_REWRITE_TAC[HD] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]]);;

let TR2OPTAUX_DEC_If = prove
 (`!(st:(FFI)state) env e1 e2 e3 s1 vs.
     evaluate st env [If e1 e2 e3] = (s1,Rval vs) ==>
     ?st' v1. evaluate st env [e1] = (st',Rval [v1]) /\
       ((v1 = Boolv T /\ evaluate st' env [e2] = (s1,Rval vs)) \/
        (v1 = Boolv F /\ evaluate st' env [e3] = (s1,Rval vs)))`,
  TR2OPTAUX_DEC_STEP_TAC `evaluate (st:(FFI)state) env [e1]` THEN
  DISCH_TAC THEN MAP_EVERY EXISTS_TAC [`st':(FFI)state`; `v1:v`] THEN
  ASM_REWRITE_TAC[] THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[do_if_def] THEN
  REPEAT COND_CASES_TAC THEN CASE_REWRITE_TAC[PAIR_EQ; distinctness "result"] THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let TR2OPTAUX_EVG_If = prove
 (`!(s:(FFI)state) env e1 e2 e3 st v1 s1 vs.
     (!ck. ?ck1. evaluate (state_clock_fupd (K ck1) s) env [e1] =
                 (state_clock_fupd (K ck) st,Rval [v1])) /\
     ((v1 = Boolv T /\
       (!ck. ?ck1. evaluate (state_clock_fupd (K ck1) st) env [e2] =
                   (state_clock_fupd (K ck) s1,Rval vs))) \/
      (v1 = Boolv F /\
       (!ck. ?ck1. evaluate (state_clock_fupd (K ck1) st) env [e3] =
                   (state_clock_fupd (K ck) s1,Rval vs)))) ==>
     !ck. ?ck1. evaluate (state_clock_fupd (K ck1) s) env [If e1 e2 e3] =
                (state_clock_fupd (K ck) s1,Rval vs)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "h1") MP_TAC) THEN
  STRIP_TAC THEN X_GEN_TAC `ck:num` THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `c2:num` o SPEC `ck:num`) THEN
  REMOVE_THEN "h1" (X_CHOOSE_TAC `c1:num` o SPEC `c2:num`) THEN
  EXISTS_TAC `c1:num` THEN ASM_REWRITE_TAC[evaluate_def] THEN
  CASE_REWRITE_TAC[HD; do_if_def; semanticPrimitivesProps_Boolv_11] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[]);;

let TR2OPTAUX_DEC_Mat = prove
 (`!(st:(FFI)state) env e pes s1 vs.
     evaluate st env [Mat e pes] = (s1,Rval vs) ==>
     ?st' v1. evaluate st env [e] = (st',Rval [v1]) /\
       can_pmatch_all (sem_env_c env) (state_refs st') (MAP FST pes) v1 /\
       evaluate_match st' env v1 pes bind_exn_v = (s1,Rval vs)`,
  TR2OPTAUX_DEC_STEP_TAC `evaluate (st:(FFI)state) env [e]` THEN
  COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ; distinctness "result"] THEN
  DISCH_TAC THEN MAP_EVERY EXISTS_TAC [`st':(FFI)state`; `v1:v`] THEN
  ASM_REWRITE_TAC[]);;

let TR2OPTAUX_EVG_Mat = prove
 (`!(s:(FFI)state) env e pes st v1 s1 vs.
     (!ck. ?ck1. evaluate (state_clock_fupd (K ck1) s) env [e] =
                 (state_clock_fupd (K ck) st,Rval [v1])) /\
     can_pmatch_all (sem_env_c env) (state_refs st) (MAP FST pes) v1 /\
     (!ck. ?ck1. evaluate_match (state_clock_fupd (K ck1) st) env v1 pes bind_exn_v =
                 (state_clock_fupd (K ck) s1,Rval vs)) ==>
     !ck. ?ck1. evaluate (state_clock_fupd (K ck1) s) env [Mat e pes] =
                (state_clock_fupd (K ck) s1,Rval vs)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "h1") (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "h2"))) THEN
  X_GEN_TAC `ck:num` THEN
  REMOVE_THEN "h2" (X_CHOOSE_TAC `c2:num` o SPEC `ck:num`) THEN
  REMOVE_THEN "h1" (X_CHOOSE_TAC `c1:num` o SPEC `c2:num`) THEN
  EXISTS_TAC `c1:num` THEN ASM_REWRITE_TAC[evaluate_def] THEN
  CASE_REWRITE_TAC[HD] THEN ASM_REWRITE_TAC[TR2OPTAUX_clock_fupd]);;

let TR2OPTAUX_DEC_Let = prove
 (`!(st:(FFI)state) env xo e1 e2 s1 vs.
     evaluate st env [Let xo e1 e2] = (s1,Rval vs) ==>
     ?st' v1. evaluate st env [e1] = (st',Rval [v1]) /\
       evaluate st' (sem_env_v_fupd (K (nsOptBind xo v1 (sem_env_v env))) env) [e2] =
       (s1,Rval vs)`,
  TR2OPTAUX_DEC_STEP_TAC `evaluate (st:(FFI)state) env [e1]` THEN
  DISCH_TAC THEN MAP_EVERY EXISTS_TAC [`st':(FFI)state`; `v1:v`] THEN
  ASM_REWRITE_TAC[]);;

let TR2OPTAUX_EVG_Let = prove
 (`!(s:(FFI)state) env xo e1 e2 st v1 s1 vs.
     (!ck. ?ck1. evaluate (state_clock_fupd (K ck1) s) env [e1] =
                 (state_clock_fupd (K ck) st,Rval [v1])) /\
     (!ck. ?ck1. evaluate (state_clock_fupd (K ck1) st)
                   (sem_env_v_fupd (K (nsOptBind xo v1 (sem_env_v env))) env) [e2] =
                 (state_clock_fupd (K ck) s1,Rval vs)) ==>
     !ck. ?ck1. evaluate (state_clock_fupd (K ck1) s) env [Let xo e1 e2] =
                (state_clock_fupd (K ck) s1,Rval vs)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "h1") (LABEL_TAC "h2")) THEN
  X_GEN_TAC `ck:num` THEN
  REMOVE_THEN "h2" (X_CHOOSE_TAC `c2:num` o SPEC `ck:num`) THEN
  REMOVE_THEN "h1" (X_CHOOSE_TAC `c1:num` o SPEC `c2:num`) THEN
  EXISTS_TAC `c1:num` THEN ASM_REWRITE_TAC[evaluate_def] THEN
  CASE_REWRITE_TAC[HD] THEN ASM_REWRITE_TAC[]);;

let TR2OPTAUX_DEC_CONS = prove
 (`!(st:(FFI)state) env e es s1 vs.
     evaluate st env (CONS e es) = (s1,Rval vs) ==>
     ?st' v1 vs'. evaluate st env [e] = (st',Rval [v1]) /\
       evaluate st' env es = (s1,Rval vs') /\ vs = CONS v1 vs'`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [evaluate_cons] THEN
  MP_TAC(ISPEC `evaluate (st:(FFI)state) env [e]` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `st':(FFI)state` (X_CHOOSE_THEN `res:(v list,v)result`
    (fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th))) THEN
  CASES_ON `res:(v list,v)result` THEN
  CASE_REWRITE_TAC[PAIR_EQ; distinctness "result"] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `v1:v` SUBST_ALL_TAC o MATCH_MP evaluate_sing) THEN
  MP_TAC(ISPEC `evaluate (st':(FFI)state) env es` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `st'':(FFI)state` (X_CHOOSE_THEN `res':(v list,v)result`
    (fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th))) THEN
  CASES_ON `res':(v list,v)result` THEN
  CASE_REWRITE_TAC[PAIR_EQ; distinctness "result"; injectivity "result"] THEN
  STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`st':(FFI)state`; `v1:v`; `a':v list`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[APPEND]) THEN ASM_REWRITE_TAC[]);;

let TR2OPTAUX_EVG_CONS = prove
 (`!(s:(FFI)state) env e es st v1 s1 vs.
     (!ck. ?ck1. evaluate (state_clock_fupd (K ck1) s) env [e] =
                 (state_clock_fupd (K ck) st,Rval [v1])) /\
     (!ck. ?ck1. evaluate (state_clock_fupd (K ck1) st) env es =
                 (state_clock_fupd (K ck) s1,Rval vs)) ==>
     !ck. ?ck1. evaluate (state_clock_fupd (K ck1) s) env (CONS e es) =
                (state_clock_fupd (K ck) s1,Rval (CONS v1 vs))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "h1") (LABEL_TAC "h2")) THEN
  X_GEN_TAC `ck:num` THEN
  REMOVE_THEN "h2" (X_CHOOSE_TAC `c2:num` o SPEC `ck:num`) THEN
  REMOVE_THEN "h1" (X_CHOOSE_TAC `c1:num` o SPEC `c2:num`) THEN
  EXISTS_TAC `c1:num` THEN ONCE_REWRITE_TAC[evaluate_cons] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[APPEND]);;

let TR2OPTAUX_DEC_PCONS = prove
 (`!(st:(FFI)state) env v p e pes err s1 vs.
     evaluate_match st env v (CONS (p,e) pes) err = (s1,Rval vs) ==>
     ALL_DISTINCT (pat_bindings p) /\
     ((?bs. pmatch (sem_env_c env) (state_refs st) p v [] = Match bs /\
            evaluate st (sem_env_v_fupd (K (nsAppend (alist_to_ns bs) (sem_env_v env)))
                           env) [e] = (s1,Rval vs)) \/
      (pmatch (sem_env_c env) (state_refs st) p v [] = No_match /\
       evaluate_match st env v pes err = (s1,Rval vs)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[evaluate_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ; distinctness "result"] THEN
  MP_TAC(ISPEC `pmatch (sem_env_c (env:v sem_env)) (state_refs (st:(FFI)state)) p v []`
    (case_info_of_tyname "match_result").ci_nchotomy) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[PAIR_EQ; distinctness "result"; distinctness "match_result";
    injectivity "match_result"] THEN
  MESON_TAC[]);;

let TR2OPTAUX_EVG_PCONS = prove
 (`!(st:(FFI)state) env v p e pes err res.
     ALL_DISTINCT (pat_bindings p) /\
     ((?bs. pmatch (sem_env_c env) (state_refs st) p v [] = Match bs /\
            evaluate st (sem_env_v_fupd (K (nsAppend (alist_to_ns bs) (sem_env_v env)))
                           env) [e] = res) \/
      (pmatch (sem_env_c env) (state_refs st) p v [] = No_match /\
       evaluate_match st env v pes err = res)) ==>
     evaluate_match st env v (CONS (p,e) pes) err = res`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[evaluate_def] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[]);;

let TR2OPTAUX_DEC_App = prove
 (`!(st:(FFI)state) env op es s1 vs.
     evaluate st env [App op es] = (s1,Rval vs) ==>
     ?st' vs'. evaluate st env (REVERSE es) = (st',Rval vs')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[evaluate_def] THEN
  MP_TAC(ISPEC `evaluate (st:(FFI)state) env (REVERSE es)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `st':(FFI)state` (X_CHOOSE_THEN `res:(v list,v)result`
    SUBST1_TAC)) THEN
  CASES_ON `res:(v list,v)result` THEN
  CASE_REWRITE_TAC[PAIR_EQ; distinctness "result"; injectivity "result"] THEN
  MESON_TAC[]);;

let TR2OPTAUX_EQ_App = prove
 (`!(st:(FFI)state) st' env op xs ys.
     evaluate st env (REVERSE xs) = evaluate st' env (REVERSE ys) ==>
     evaluate st env [App op xs] = evaluate st' env [App op ys]`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[evaluate_def] THEN
  ASM_REWRITE_TAC[]);;

let TR2OPTAUX_DEC_Con = prove
 (`!(st:(FFI)state) env cn es s1 vs.
     evaluate st env [Con cn es] = (s1,Rval vs) ==>
     do_con_check (sem_env_c env) cn (LENGTH es) /\
     ?st' vs'. evaluate st env (REVERSE es) = (st',Rval vs')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[evaluate_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ; distinctness "result"] THEN
  MP_TAC(ISPEC `evaluate (st:(FFI)state) env (REVERSE es)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `st':(FFI)state` (X_CHOOSE_THEN `res:(v list,v)result`
    SUBST1_TAC)) THEN
  CASES_ON `res:(v list,v)result` THEN
  CASE_REWRITE_TAC[PAIR_EQ; distinctness "result"; injectivity "result"] THEN
  MESON_TAC[]);;

let TR2OPTAUX_EQ_Con = prove
 (`!(st:(FFI)state) st' env cn xs ys.
     LENGTH ys = LENGTH xs /\ do_con_check (sem_env_c env) cn (LENGTH xs) /\
     evaluate st env (REVERSE xs) = evaluate st' env (REVERSE ys) ==>
     evaluate st env [Con cn xs] = evaluate st' env [Con cn ys]`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[evaluate_def] THEN
  ASM_REWRITE_TAC[]);;

let TR2OPTAUX_ANY_EXP2 = prove
 (`!e e' (s:(FFI)state) env s2 v ck0.
     (!(s:(FFI)state) s1 r env. eval_rel s env e s1 r ==> eval_rel s env e' s1 r) /\
     evaluate (state_clock_fupd (K ck0) s) env [e] = (s2,Rval [v]) ==>
     !ck. ?ck1. evaluate (state_clock_fupd (K ck1) s) env [e'] =
                (state_clock_fupd (K ck) s2,Rval [v])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`e:exp`; `e':exp`; `state_clock_fupd (K ck0) (s:(FFI)state)`;
    `env:v sem_env`; `s2:(FFI)state`; `v:v`] TR2OPTAUX_ANY_EXP) THEN
  ASM_SIMP_TAC[TR2OPTAUX_clock_fupd]);;

let TR2OPTAUX_ANY_LIST2 = prove
 (`!es es' (s:(FFI)state) env s2 vs ck0.
     (!(s:(FFI)state) s1 r env. eval_list_rel s env es s1 r ==>
                                eval_list_rel s env es' s1 r) /\
     evaluate (state_clock_fupd (K ck0) s) env es = (s2,Rval vs) ==>
     !ck. ?ck1. evaluate (state_clock_fupd (K ck1) s) env es' =
                (state_clock_fupd (K ck) s2,Rval vs)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`es:exp list`; `es':exp list`; `state_clock_fupd (K ck0) (s:(FFI)state)`;
    `env:v sem_env`; `s2:(FFI)state`; `vs:v list`] TR2OPTAUX_ANY_LIST) THEN
  ASM_SIMP_TAC[TR2OPTAUX_clock_fupd]);;

let TR2OPTAUX_ANY_MATCH2 = prove
 (`!pes pes' (s:(FFI)state) env v err s2 r ck0.
     (!(s:(FFI)state) s1 v r w env. eval_match_rel s env v pes w s1 r ==>
                                    eval_match_rel s env v pes' w s1 r) /\
     evaluate_match (state_clock_fupd (K ck0) s) env v pes err = (s2,Rval [r]) ==>
     !ck. ?ck1. evaluate_match (state_clock_fupd (K ck1) s) env v pes' err =
                (state_clock_fupd (K ck) s2,Rval [r])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`pes:(pat#exp)list`; `pes':(pat#exp)list`;
    `state_clock_fupd (K ck0) (s:(FFI)state)`; `env:v sem_env`; `v:v`; `err:v`;
    `s2:(FFI)state`; `r:v`] TR2OPTAUX_ANY_MATCH) THEN
  ASM_SIMP_TAC[TR2OPTAUX_clock_fupd]);;

let TR2OPTAUX_do_log_Exp = prove
 (`!lop v (e:exp) e'. do_log lop v e = SOME (Exp e) <=> do_log lop v e' = SOME (Exp e')`,
  REWRITE_TAC[do_log_def] THEN REPEAT GEN_TAC THEN REPEAT COND_CASES_TAC THEN
  ASM_REWRITE_TAC[injectivity "option"; distinctness "option"; injectivity "exp_or_val";
    distinctness "exp_or_val"] THEN ASM_MESON_TAC[]);;

let TR2OPTAUX_do_log_Val = prove
 (`!lop v (e:exp) e' w. do_log lop v e = SOME (Val w) <=> do_log lop v e' = SOME (Val w)`,
  REWRITE_TAC[do_log_def] THEN REPEAT GEN_TAC THEN REPEAT COND_CASES_TAC THEN
  ASM_REWRITE_TAC[injectivity "option"; distinctness "option"; injectivity "exp_or_val";
    distinctness "exp_or_val"] THEN ASM_MESON_TAC[]);;

(* congruence steps: an expression whose subexpressions are replaced by     *)
(* ones with the same successful evaluations has the same successful       *)
(* evaluations                                                               *)

let TR2OPTAUX_CONG_Log = prove
 (`!lop x1 x2 y1 y2 (s:(FFI)state) s1 r env.
     (!(s:(FFI)state) s1 r env. eval_rel s env x1 s1 r ==> eval_rel s env y1 s1 r) /\
     (!(s:(FFI)state) s1 r env. eval_rel s env x2 s1 r ==> eval_rel s env y2 s1 r) /\
     eval_rel s env (Log lop x1 x2) s1 r ==> eval_rel s env (Log lop y1 y2) s1 r`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[eval_rel_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `ck1:num` (X_CHOOSE_THEN `ck2:num`
    (MP_TAC o MATCH_MP TR2OPTAUX_DEC_Log)))) THEN
  DISCH_THEN(X_CHOOSE_THEN `st:(FFI)state` (X_CHOOSE_THEN `v1:v`
    (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`s:(FFI)state`; `env:v sem_env`; `lop:lop`; `y1:exp`; `y2:exp`;
    `st:(FFI)state`; `v1:v`; `state_clock_fupd (K ck2) (s1:(FFI)state)`; `[r:v]`]
    TR2OPTAUX_EVG_Log) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC TR2OPTAUX_ANY_EXP2 THEN
      MAP_EVERY EXISTS_TAC [`x1:exp`; `ck1:num`] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
     [DISJ1_TAC THEN CONJ_TAC THENL
       [ASM_MESON_TAC[TR2OPTAUX_do_log_Exp]; ALL_TAC] THEN
      MATCH_MP_TAC TR2OPTAUX_ANY_EXP2 THEN
      MAP_EVERY EXISTS_TAC [`x2:exp`; `state_clock (st:(FFI)state)`] THEN
      ASM_REWRITE_TAC[TR2OPTAUX_clock_fupd];
      DISJ2_TAC THEN EXISTS_TAC `w:v` THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[TR2OPTAUX_do_log_Val]];
    DISCH_THEN(MP_TAC o SPEC `ck2:num`) THEN REWRITE_TAC[TR2OPTAUX_clock_fupd] THEN
    MESON_TAC[]]);;

let TR2OPTAUX_CONG_If = prove
 (`!x1 x2 x3 y1 y2 y3 (s:(FFI)state) s1 r env.
     (!(s:(FFI)state) s1 r env. eval_rel s env x1 s1 r ==> eval_rel s env y1 s1 r) /\
     (!(s:(FFI)state) s1 r env. eval_rel s env x2 s1 r ==> eval_rel s env y2 s1 r) /\
     (!(s:(FFI)state) s1 r env. eval_rel s env x3 s1 r ==> eval_rel s env y3 s1 r) /\
     eval_rel s env (If x1 x2 x3) s1 r ==> eval_rel s env (If y1 y2 y3) s1 r`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))) THEN
  REWRITE_TAC[eval_rel_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `ck1:num` (X_CHOOSE_THEN `ck2:num`
    (MP_TAC o MATCH_MP TR2OPTAUX_DEC_If)))) THEN
  DISCH_THEN(X_CHOOSE_THEN `st:(FFI)state` (X_CHOOSE_THEN `v1:v`
    (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`s:(FFI)state`; `env:v sem_env`; `y1:exp`; `y2:exp`; `y3:exp`;
    `st:(FFI)state`; `v1:v`; `state_clock_fupd (K ck2) (s1:(FFI)state)`; `[r:v]`]
    TR2OPTAUX_EVG_If) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC TR2OPTAUX_ANY_EXP2 THEN
      MAP_EVERY EXISTS_TAC [`x1:exp`; `ck1:num`] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
     [DISJ1_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC TR2OPTAUX_ANY_EXP2 THEN
      MAP_EVERY EXISTS_TAC [`x2:exp`; `state_clock (st:(FFI)state)`] THEN
      ASM_REWRITE_TAC[TR2OPTAUX_clock_fupd];
      DISJ2_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC TR2OPTAUX_ANY_EXP2 THEN
      MAP_EVERY EXISTS_TAC [`x3:exp`; `state_clock (st:(FFI)state)`] THEN
      ASM_REWRITE_TAC[TR2OPTAUX_clock_fupd]];
    DISCH_THEN(MP_TAC o SPEC `ck2:num`) THEN REWRITE_TAC[TR2OPTAUX_clock_fupd] THEN
    MESON_TAC[]]);;

let TR2OPTAUX_CONG_Mat = prove
 (`!x pes y pes' (s:(FFI)state) s1 r env.
     (!(s:(FFI)state) s1 r env. eval_rel s env x s1 r ==> eval_rel s env y s1 r) /\
     (!(s:(FFI)state) s1 v r w env. eval_match_rel s env v pes w s1 r ==>
                                    eval_match_rel s env v pes' w s1 r) /\
     MAP FST pes' = MAP FST pes /\
     eval_rel s env (Mat x pes) s1 r ==> eval_rel s env (Mat y pes') s1 r`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))) THEN
  REWRITE_TAC[eval_rel_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `ck1:num` (X_CHOOSE_THEN `ck2:num`
    (MP_TAC o MATCH_MP TR2OPTAUX_DEC_Mat)))) THEN
  DISCH_THEN(X_CHOOSE_THEN `st:(FFI)state` (X_CHOOSE_THEN `v1:v` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`s:(FFI)state`; `env:v sem_env`; `y:exp`; `pes':(pat#exp)list`;
    `st:(FFI)state`; `v1:v`; `state_clock_fupd (K ck2) (s1:(FFI)state)`; `[r:v]`]
    TR2OPTAUX_EVG_Mat) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC TR2OPTAUX_ANY_EXP2 THEN
      MAP_EVERY EXISTS_TAC [`x:exp`; `ck1:num`] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC TR2OPTAUX_ANY_MATCH2 THEN
      MAP_EVERY EXISTS_TAC [`pes:(pat#exp)list`; `state_clock (st:(FFI)state)`] THEN
      ASM_REWRITE_TAC[TR2OPTAUX_clock_fupd]];
    DISCH_THEN(MP_TAC o SPEC `ck2:num`) THEN REWRITE_TAC[TR2OPTAUX_clock_fupd] THEN
    MESON_TAC[]]);;

let TR2OPTAUX_CONG_Let = prove
 (`!xo x1 x2 y1 y2 (s:(FFI)state) s1 r env.
     (!(s:(FFI)state) s1 r env. eval_rel s env x1 s1 r ==> eval_rel s env y1 s1 r) /\
     (!(s:(FFI)state) s1 r env. eval_rel s env x2 s1 r ==> eval_rel s env y2 s1 r) /\
     eval_rel s env (Let xo x1 x2) s1 r ==> eval_rel s env (Let xo y1 y2) s1 r`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[eval_rel_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `ck1:num` (X_CHOOSE_THEN `ck2:num`
    (MP_TAC o MATCH_MP TR2OPTAUX_DEC_Let)))) THEN
  DISCH_THEN(X_CHOOSE_THEN `st:(FFI)state` (X_CHOOSE_THEN `v1:v` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`s:(FFI)state`; `env:v sem_env`; `xo:mlstring option`; `y1:exp`; `y2:exp`;
    `st:(FFI)state`; `v1:v`; `state_clock_fupd (K ck2) (s1:(FFI)state)`; `[r:v]`]
    TR2OPTAUX_EVG_Let) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC TR2OPTAUX_ANY_EXP2 THEN
      MAP_EVERY EXISTS_TAC [`x1:exp`; `ck1:num`] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC TR2OPTAUX_ANY_EXP2 THEN
      MAP_EVERY EXISTS_TAC [`x2:exp`; `state_clock (st:(FFI)state)`] THEN
      ASM_REWRITE_TAC[TR2OPTAUX_clock_fupd]];
    DISCH_THEN(MP_TAC o SPEC `ck2:num`) THEN REWRITE_TAC[TR2OPTAUX_clock_fupd] THEN
    MESON_TAC[]]);;

let TR2OPTAUX_CONG_App = prove
 (`!op xs ys (s:(FFI)state) s1 r env.
     (!(s:(FFI)state) s1 r env. eval_list_rel s env (REVERSE xs) s1 r ==>
                                eval_list_rel s env (REVERSE ys) s1 r) /\
     eval_rel s env (App op xs) s1 r ==> eval_rel s env (App op ys) s1 r`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[eval_rel_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `ck1:num` (X_CHOOSE_TAC `ck2:num`))) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `st:(FFI)state` (X_CHOOSE_TAC `vs:v list`) o
    MATCH_MP TR2OPTAUX_DEC_App) THEN
  MP_TAC(ISPECL [`REVERSE xs:exp list`; `REVERSE ys:exp list`; `s:(FFI)state`;
    `env:v sem_env`; `st:(FFI)state`; `vs:v list`; `ck1:num`] TR2OPTAUX_ANY_LIST2) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `c:num` o SPEC `state_clock (st:(FFI)state)`) THEN
  MAP_EVERY EXISTS_TAC [`c:num`; `ck2:num`] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `evaluate (state_clock_fupd (K ck1) (s:(FFI)state)) env [App op xs]` THEN
  CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC TR2OPTAUX_EQ_App THEN ASM_REWRITE_TAC[TR2OPTAUX_clock_fupd]);;

let TR2OPTAUX_CONG_Con = prove
 (`!cn xs ys (s:(FFI)state) s1 r env.
     LENGTH ys = LENGTH xs /\
     (!(s:(FFI)state) s1 r env. eval_list_rel s env (REVERSE xs) s1 r ==>
                                eval_list_rel s env (REVERSE ys) s1 r) /\
     eval_rel s env (Con cn xs) s1 r ==> eval_rel s env (Con cn ys) s1 r`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[eval_rel_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `ck1:num` (X_CHOOSE_TAC `ck2:num`))) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `st:(FFI)state` (X_CHOOSE_TAC `vs:v list`)) o
    MATCH_MP TR2OPTAUX_DEC_Con) THEN
  MP_TAC(ISPECL [`REVERSE xs:exp list`; `REVERSE ys:exp list`; `s:(FFI)state`;
    `env:v sem_env`; `st:(FFI)state`; `vs:v list`; `ck1:num`] TR2OPTAUX_ANY_LIST2) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `c:num` o SPEC `state_clock (st:(FFI)state)`) THEN
  MAP_EVERY EXISTS_TAC [`c:num`; `ck2:num`] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `evaluate (state_clock_fupd (K ck1) (s:(FFI)state)) env [Con cn xs]` THEN
  CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC TR2OPTAUX_EQ_Con THEN ASM_REWRITE_TAC[TR2OPTAUX_clock_fupd]);;

let TR2OPTAUX_eval_rel_Tannot = prove
 (`!(s:(FFI)state) env x t s1 r. eval_rel s env (Tannot x t) s1 r <=> eval_rel s env x s1 r`,
  REWRITE_TAC[eval_rel_def; evaluate_def]);;

let TR2OPTAUX_eval_rel_Lannot = prove
 (`!(s:(FFI)state) env x lc s1 r. eval_rel s env (Lannot x lc) s1 r <=> eval_rel s env x s1 r`,
  REWRITE_TAC[eval_rel_def; evaluate_def]);;

let TR2OPTAUX_CONG_CONS = prove
 (`!x xs y ys (s:(FFI)state) s1 r env.
     (!(s:(FFI)state) s1 r env. eval_rel s env x s1 r ==> eval_rel s env y s1 r) /\
     (!(s:(FFI)state) s1 r env. eval_list_rel s env xs s1 r ==>
                                eval_list_rel s env ys s1 r) /\
     eval_list_rel s env (CONS x xs) s1 r ==> eval_list_rel s env (CONS y ys) s1 r`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[eval_list_rel_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `ck1:num` (X_CHOOSE_THEN `ck2:num`
    (MP_TAC o MATCH_MP TR2OPTAUX_DEC_CONS)))) THEN
  DISCH_THEN(X_CHOOSE_THEN `st:(FFI)state` (X_CHOOSE_THEN `v1:v` (X_CHOOSE_THEN `vs:v list`
    STRIP_ASSUME_TAC))) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`s:(FFI)state`; `env:v sem_env`; `y:exp`; `ys:exp list`;
    `st:(FFI)state`; `v1:v`; `state_clock_fupd (K ck2) (s1:(FFI)state)`; `vs:v list`]
    TR2OPTAUX_EVG_CONS) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC TR2OPTAUX_ANY_EXP2 THEN
      MAP_EVERY EXISTS_TAC [`x:exp`; `ck1:num`] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC TR2OPTAUX_ANY_LIST2 THEN
      MAP_EVERY EXISTS_TAC [`xs:exp list`; `state_clock (st:(FFI)state)`] THEN
      ASM_REWRITE_TAC[TR2OPTAUX_clock_fupd]];
    DISCH_THEN(MP_TAC o SPEC `ck2:num`) THEN REWRITE_TAC[TR2OPTAUX_clock_fupd] THEN
    MESON_TAC[]]);;

let TR2OPTAUX_CONG_PCONS = prove
 (`!p x pes y pes' (s:(FFI)state) s1 v r w env.
     (!(s:(FFI)state) s1 r env. eval_rel s env x s1 r ==> eval_rel s env y s1 r) /\
     (!(s:(FFI)state) s1 v r w env. eval_match_rel s env v pes w s1 r ==>
                                    eval_match_rel s env v pes' w s1 r) /\
     eval_match_rel s env v (CONS (p,x) pes) w s1 r ==>
     eval_match_rel s env v (CONS (p,y) pes') w s1 r`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[eval_match_rel_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `ck1:num` (X_CHOOSE_THEN `ck2:num`
    (MP_TAC o MATCH_MP TR2OPTAUX_DEC_PCONS)))) THEN
  REWRITE_TAC[TR2OPTAUX_clock_fupd] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THENL
   [MP_TAC(ISPECL [`x:exp`; `y:exp`; `s:(FFI)state`;
      `sem_env_v_fupd (K (nsAppend (alist_to_ns bs) (sem_env_v env))) (env:v sem_env)`;
      `state_clock_fupd (K ck2) (s1:(FFI)state)`; `r:v`; `ck1:num`] TR2OPTAUX_ANY_EXP2) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_TAC `c:num` o SPEC `ck2:num`) THEN
    MAP_EVERY EXISTS_TAC [`c:num`; `ck2:num`] THEN
    MATCH_MP_TAC TR2OPTAUX_EVG_PCONS THEN ASM_REWRITE_TAC[TR2OPTAUX_clock_fupd] THEN
    DISJ1_TAC THEN EXISTS_TAC `bs:(mlstring#v)list` THEN
    ASM_REWRITE_TAC[TR2OPTAUX_clock_fupd];
    MP_TAC(ISPECL [`pes:(pat#exp)list`; `pes':(pat#exp)list`; `s:(FFI)state`;
      `env:v sem_env`; `v:v`; `w:v`; `state_clock_fupd (K ck2) (s1:(FFI)state)`; `r:v`;
      `ck1:num`] TR2OPTAUX_ANY_MATCH2) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_TAC `c:num` o SPEC `ck2:num`) THEN
    MAP_EVERY EXISTS_TAC [`c:num`; `ck2:num`] THEN
    MATCH_MP_TAC TR2OPTAUX_EVG_PCONS THEN ASM_REWRITE_TAC[TR2OPTAUX_clock_fupd]]);;

(* HOL4 [local].  HOL4's last conjunct quantifies r twice (!g pats s s1 r v *)
(* r w env); the vacuous outer r is left out.                               *)

let BOTTOM_UP_OPT_THM1 = prove
 (`(!x (s:(FFI)state) env s1 r. eval_rel s env x s1 r ==> eval_rel s env (f x) s1 r) ==>
   (!g x (s:(FFI)state) s1 r env. g = f /\ eval_rel s env x s1 r ==>
      eval_rel s env (BOTTOM_UP_OPT f x) s1 r) /\
   (!g xs (s:(FFI)state) s1 r env. g = f /\ eval_list_rel s env xs s1 r ==>
      eval_list_rel s env (BOTTOM_UP_OPT_LIST f xs) s1 r) /\
   (!g pats (s:(FFI)state) s1 v r w env. g = f /\ eval_match_rel s env v pats w s1 r ==>
      eval_match_rel s env v (BOTTOM_UP_OPT_PAT f pats) w s1 r)`,
  DISCH_THEN(LABEL_TAC "f") THEN
  MP_TAC(ISPECL
   [`\(g:exp->exp) x. !(s:(FFI)state) s1 r env.
       eval_rel s env x s1 r ==> eval_rel s env (BOTTOM_UP_OPT f x) s1 r`;
    `\(g:exp->exp) xs. !(s:(FFI)state) s1 r env.
       eval_list_rel s env xs s1 r ==> eval_list_rel s env (BOTTOM_UP_OPT_LIST f xs) s1 r`;
    `\(g:exp->exp) pats. !(s:(FFI)state) s1 v r w env.
       eval_match_rel s env v pats w s1 r ==>
       eval_match_rel s env v (BOTTOM_UP_OPT_PAT f pats) w s1 r`]
   BOTTOM_UP_OPT_ind) THEN
  BETA_TAC THEN REWRITE_TAC[] THEN ANTS_TAC THENL
   [ALL_TAC; MESON_TAC[]] THEN
  (* the Handle, [] and [] cases are solved by the rewriting *)
  REWRITE_TAC[BOTTOM_UP_OPT_def] THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN USE_THEN "f" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN USE_THEN "f" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN USE_THEN "f" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT STRIP_TAC THEN USE_THEN "f" MATCH_MP_TAC THEN
    MATCH_MP_TAC TR2OPTAUX_CONG_Con THEN EXISTS_TAC `xs:exp list` THEN
    ASM_REWRITE_TAC[LENGTH_BOTTOM_UP_OPT_LIST; REVERSE_BOTTOM_UP_OPT_LIST];
    REPEAT STRIP_TAC THEN USE_THEN "f" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT STRIP_TAC THEN USE_THEN "f" MATCH_MP_TAC THEN
    MATCH_MP_TAC TR2OPTAUX_CONG_App THEN EXISTS_TAC `xs:exp list` THEN
    ASM_REWRITE_TAC[REVERSE_BOTTOM_UP_OPT_LIST];
    REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT STRIP_TAC THEN USE_THEN "f" MATCH_MP_TAC THEN
    MATCH_MP_TAC TR2OPTAUX_CONG_Log THEN
    MAP_EVERY EXISTS_TAC [`x1:exp`; `x2:exp`] THEN ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT STRIP_TAC THEN USE_THEN "f" MATCH_MP_TAC THEN
    MATCH_MP_TAC TR2OPTAUX_CONG_If THEN
    MAP_EVERY EXISTS_TAC [`x1:exp`; `x2:exp`; `x3:exp`] THEN ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT STRIP_TAC THEN USE_THEN "f" MATCH_MP_TAC THEN
    MATCH_MP_TAC TR2OPTAUX_CONG_Mat THEN
    MAP_EVERY EXISTS_TAC [`x:exp`; `pes:(pat#exp)list`] THEN
    ASM_REWRITE_TAC[MAP_FST_BOTTOM_UP_OPT_PAT];
    REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT STRIP_TAC THEN USE_THEN "f" MATCH_MP_TAC THEN
    MATCH_MP_TAC TR2OPTAUX_CONG_Let THEN
    MAP_EVERY EXISTS_TAC [`x1:exp`; `x2:exp`] THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN USE_THEN "f" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[TR2OPTAUX_eval_rel_Tannot];
    REWRITE_TAC[TR2OPTAUX_eval_rel_Lannot];
    REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC TR2OPTAUX_CONG_CONS THEN
    MAP_EVERY EXISTS_TAC [`y:exp`; `ys:exp list`] THEN ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC TR2OPTAUX_CONG_PCONS THEN
    MAP_EVERY EXISTS_TAC [`y:exp`; `pes:(pat#exp)list`] THEN ASM_REWRITE_TAC[]]);;

(* HOL4: BOTTOM_UP_OPT_THM1 |> UNDISCH_ALL |> CONJUNCTS |> hd |> SIMP_RULE  *)
(* bool_ss [] |> DISCH_ALL                                                   *)

let BOTTOM_UP_OPT_THM = prove
 (`(!x (s:(FFI)state) env s1 r. eval_rel s env x s1 r ==> eval_rel s env (f x) s1 r) ==>
   !x (s:(FFI)state) s1 r env.
     eval_rel s env x s1 r ==> eval_rel s env (BOTTOM_UP_OPT f x) s1 r`,
  DISCH_THEN(MP_TAC o CONJUNCT1 o MATCH_MP BOTTOM_UP_OPT_THM1) THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* rewrite optimisation: (fn x => exp) y --> let x = y in exp                *)
(* ------------------------------------------------------------------------- *)

let abs2let_def = cake_def
  `abs2let x =
     match x with
       App Opapp [Fun v exp; y] -> Let (SOME v) y exp
     | rest -> rest`;;

(* helper of the port: the evaluation of (fn v => e) y *)

let TR2OPTAUX_DEC_abs2let = prove
 (`!(st:(FFI)state) env v e y s1 vs.
     evaluate st env [App Opapp [Fun v e; y]] = (s1,Rval vs) ==>
     ?st' vy. evaluate st env [y] = (st',Rval [vy]) /\ ~(state_clock st' = 0) /\
       evaluate (dec_clock st') (sem_env_v_fupd (K (nsBind v vy (sem_env_v env))) env) [e] =
       (s1,Rval vs)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[evaluate_def; REVERSE; APPEND] THEN
  MP_TAC(ISPEC `evaluate (st:(FFI)state) env [y]` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `st':(FFI)state` (X_CHOOSE_THEN `res:(v list,v)result`
    (fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th))) THEN
  CASES_ON `res:(v list,v)result` THEN
  CASE_REWRITE_TAC[PAIR_EQ; distinctness "result"] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `vy:v` SUBST_ALL_TAC o MATCH_MP evaluate_sing) THEN
  REWRITE_TAC[HD; getOpClass_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[REVERSE; APPEND; do_opapp_def] THEN CASE_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ; distinctness "result"] THEN
  DISCH_TAC THEN MAP_EVERY EXISTS_TAC [`st':(FFI)state`; `vy:v`] THEN
  ASM_REWRITE_TAC[]);;

(* HOL4 [local] *)

let abs2let_thm = prove
 (`!env (s:(FFI)state) exp t res.
     eval_rel s env exp t res ==> eval_rel s env (abs2let exp) t res`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `abs2let exp = exp` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `?v e y. exp = App Opapp [Fun v e; y]` STRIP_ASSUME_TAC THENL
   [POP_ASSUM MP_TAC THEN REWRITE_TAC[abs2let_def] THEN
    REPEAT TOP_CASE_TAC THEN REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[abs2let_def] THEN CASE_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_comb (concl th) &&
    (try fst (dest_const (fst (strip_comb (concl th)))) = "eval_rel"
     with Failure _ -> false))) THEN
  REWRITE_TAC[eval_rel_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `ck1:num` (X_CHOOSE_THEN `ck2:num`
    (MP_TAC o MATCH_MP TR2OPTAUX_DEC_abs2let)))) THEN
  DISCH_THEN(X_CHOOSE_THEN `st:(FFI)state` (X_CHOOSE_THEN `vy:v` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`ck1:num`; `ck2 + 1`] THEN
  ASM_REWRITE_TAC[evaluate_def] THEN CASE_REWRITE_TAC[HD; nsOptBind_def] THEN
  MP_TAC(ISPECL [`dec_clock (st:(FFI)state)`;
    `sem_env_v_fupd (K (nsBind v vy (sem_env_v env))) (env:v sem_env)`; `[e:exp]`;
    `state_clock_fupd (K ck2) (t:(FFI)state)`; `Rval [res]:(v list,v)result`; `1`]
    evaluate_add_to_clock) THEN
  ASM_REWRITE_TAC[distinctness "result"; dec_clock_def; TR2OPTAUX_clock_fupd] THEN
  SUBGOAL_THEN `state_clock (st:(FFI)state) - 1 + 1 = state_clock st` SUBST1_TAC THENL
   [ASM_ARITH_TAC; REWRITE_TAC[TR2OPTAUX_clock_fupd]]);;

(* ------------------------------------------------------------------------- *)
(* rewrite optimisation: let x = y in x --> y                                *)
(* ------------------------------------------------------------------------- *)

let let_id_def = cake_def
  `(let_id (Let (SOME v) x y) =
      if y = Var (Short v) then x else Let (SOME v) x y) /\
   (let_id rest = rest)`;;

(* HOL4 [local] *)

let let_id_thm = prove
 (`!env (s:(FFI)state) exp t res.
     eval_rel s env exp t res ==> eval_rel s env (let_id exp) t res`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `let_id exp = exp` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `?v x. exp = Let (SOME v) x (Var (Short v))` STRIP_ASSUME_TAC THENL
   [POP_ASSUM MP_TAC THEN CASES_ON `exp:exp` THEN REWRITE_TAC[let_id_def] THEN
    CASES_ON `a0:mlstring option` THEN REWRITE_TAC[let_id_def] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[injectivity "exp"; injectivity "option"] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[let_id_def] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_comb (concl th) &&
    (try fst (dest_const (fst (strip_comb (concl th)))) = "eval_rel"
     with Failure _ -> false))) THEN
  REWRITE_TAC[eval_rel_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `ck1:num` (X_CHOOSE_THEN `ck2:num`
    (MP_TAC o MATCH_MP TR2OPTAUX_DEC_Let)))) THEN
  DISCH_THEN(X_CHOOSE_THEN `st:(FFI)state` (X_CHOOSE_THEN `v1:v` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN MAP_EVERY EXISTS_TAC [`ck1:num`; `ck2:num`] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> free_in `Var (Short v)` (concl th))) THEN
  REWRITE_TAC[evaluate_def; nsOptBind_def] THEN CASE_REWRITE_TAC[] THEN
  SIMP[nsLookup_nsBind] THEN
  REWRITE_TAC[PAIR_EQ; injectivity "result"; CONS_11] THEN
  STRIP_TAC THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* rewrite optimisations: x - n + n --> x and x + n - n --> x                *)
(* ------------------------------------------------------------------------- *)

let dest_binop_def = cake_def
  `(dest_binop (App (Arith op IntT) [x;y]) = SOME (op,x,y)) /\
   (dest_binop rest = NONE)`;;

(* HOL4's dest_binop_ind (TFL makes one for this non-recursive definition): *)
(* one case for each clause of dest_binop_def as completed by the pattern   *)
(* compiler; the statement is built from the clauses.                        *)

let TR2OPTAUX_SPLIT_TAC : tactic = fun (asl,w as g) ->
  let t = rand w in
  let pick ty = filter (fun v -> type_of v = ty) (frees t) in
  let v = hd (pick `:op` @ pick `:prim_type` @ pick `:exp list`) in
  let ch = if type_of v = `:exp list` then ISPEC v list_CASES
           else ISPEC v (case_info_of_tyname (fst (dest_type (type_of v)))).ci_nchotomy in
  STRUCT_CASES_TAC ch g;;

let dest_binop_ind =
  let cls = CONJUNCTS dest_binop_def in
  let pv = `P:exp->bool` in
  let hyps = map (fun th -> let vs,bod = strip_forall (concl th) in
                            list_mk_forall (vs, mk_comb (pv, rand (lhs bod)))) cls in
  prove
   (mk_forall (pv, mk_imp (list_mk_conj hyps, `!v:exp. (P:exp->bool) v`)),
    GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
    STRUCT_CASES_TAC (ISPEC `v:exp` (case_info_of_tyname "exp").ci_nchotomy) THEN
    REPEAT (FIRST [ASM_REWRITE_TAC[] THEN NO_TAC; TR2OPTAUX_SPLIT_TAC]));;

let opt_sub_add_def = cake_def
  `opt_sub_add x =
     match dest_binop x with
       NONE -> x
     | SOME (op1,y,z) ->
         (match dest_binop y with
            SOME (op2,x1,Lit y1) ->
              if z = Lit y1 then
                if op1 = Add /\ op2 = Sub then x1 else
                if op2 = Add /\ op1 = Sub then x1 else x
              else x
          | _ -> x)`;;

(* HOL4 [local] *)

let dest_binop_thm = prove
 (`!x. dest_binop x = SOME (x1,x2,x3) <=> x = App (Arith x1 IntT) [x2; x3]`,
  MATCH_MP_TAC dest_binop_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[dest_binop_def] THEN SIMP[]);;

(* helpers of the port: the evaluation of x - n + n and x + n - n *)

let TR2OPTAUX_state_self = prove
 (`!s:(FFI)state.
     state_refs_fupd (K (state_refs s)) (state_ffi_fupd (K (state_ffi s)) s) = s`,
  REWRITE_TAC[state_component_equality] THEN SIMP[]);;

let TR2OPTAUX_EV_sub_add = prove
 (`!(st:(FFI)state) env op1 op2 x1 y1 s1 vs.
     ((op1 = Add /\ op2 = Sub) \/ (op1 = Sub /\ op2 = Add)) /\
     evaluate st env [App (Arith op1 IntT) [App (Arith op2 IntT) [x1; Lit y1]; Lit y1]] =
       (s1,Rval vs) ==>
     evaluate st env [x1] = (s1,Rval vs)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN (CONJUNCTS_THEN SUBST1_TAC)) THEN
  REWRITE_TAC[evaluate_def; REVERSE; APPEND] THEN CASE_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `evaluate (st:(FFI)state) env [x1]` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `st':(FFI)state` (X_CHOOSE_THEN `res:(v list,v)result`
    (fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th))) THEN
  CASES_ON `res:(v list,v)result` THEN
  CASE_REWRITE_TAC[PAIR_EQ; distinctness "result"] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `vx:v` SUBST_ALL_TAC o MATCH_MP evaluate_sing) THEN
  REWRITE_TAC[HD; getOpClass_def] THEN CASE_REWRITE_TAC[] THEN
  (ASM_CASES_TAC `?i j. vx = Litv (IntLit i) /\ y1 = IntLit j` THENL
    [FIRST_X_ASSUM(X_CHOOSE_THEN `i:int` (X_CHOOSE_THEN `j:int`
       (CONJUNCTS_THEN SUBST_ALL_TAC))) THEN
     REWRITE_TAC[REVERSE; APPEND; do_app_def] THEN CASE_REWRITE_TAC[] THEN
     SIMP[ALL; check_type_def; do_arith_def; MAP; the_Litv_IntLit_def; list_result_def;
       REVERSE; APPEND] THEN
     CASE_REWRITE_TAC[] THEN
     SIMP[ALL; check_type_def; do_arith_def; MAP; the_Litv_IntLit_def; list_result_def;
       REVERSE; APPEND; TR2OPTAUX_state_self;
       INT_ARITH `!i j:int. (i - j) + j = i /\ (i + j) - j = i`];
     REWRITE_TAC[REVERSE; APPEND; do_app_def] THEN CASE_REWRITE_TAC[] THEN
     COND_CASES_TAC THENL
      [FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[ALL; check_type_def]) THEN
       SIMP[injectivity "v"; injectivity "lit"] THEN ASM_MESON_TAC[];
       CASE_REWRITE_TAC[PAIR_EQ; distinctness "result"]]]));;

(* HOL4 [local] *)

let opt_sub_add_thm = prove
 (`!env (s:(FFI)state) exp t res.
     eval_rel s env exp t res ==> eval_rel s env (opt_sub_add exp) t res`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `opt_sub_add exp = exp` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `?op1 op2 x1 y1. ((op1 = Add /\ op2 = Sub) \/ (op1 = Sub /\ op2 = Add)) /\
      exp = App (Arith op1 IntT) [App (Arith op2 IntT) [x1; Lit y1]; Lit y1] /\
      opt_sub_add exp = x1`
    MP_TAC THENL
   [POP_ASSUM MP_TAC THEN REWRITE_TAC[opt_sub_add_def] THEN REPEAT TOP_CASE_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[dest_binop_thm]) THEN ASM_REWRITE_TAC[] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `op1:arith` (X_CHOOSE_THEN `op2:arith`
    (X_CHOOSE_THEN `x1:exp` (X_CHOOSE_THEN `y1:lit`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (fun th -> REWRITE_TAC[th]))))))) THEN
  UNDISCH_TAC `eval_rel (s:(FFI)state) env exp t res` THEN
  ASM_REWRITE_TAC[eval_rel_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `ck1:num` (X_CHOOSE_TAC `ck2:num`))) THEN
  ASM_REWRITE_TAC[] THEN MAP_EVERY EXISTS_TAC [`ck1:num`; `ck2:num`] THEN
  MATCH_MP_TAC TR2OPTAUX_EV_sub_add THEN
  MAP_EVERY EXISTS_TAC [`op1:arith`; `op2:arith`; `y1:lit`] THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* top-level optimiser                                                       *)
(* ------------------------------------------------------------------------- *)

let OPTIMISE_def = cake_def
  `OPTIMISE = BOTTOM_UP_OPT (opt_sub_add o let_id) o BOTTOM_UP_OPT abs2let`;;

let Eval_OPTIMISE = prove
 (`ml_Eval env exp P ==> ml_Eval env (OPTIMISE exp) P`,
  REWRITE_TAC[ml_Eval_def; OPTIMISE_def; o_THM] THEN DISCH_TAC THEN
  X_GEN_TAC `refs:(v store_v)list` THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `res:v` (X_CHOOSE_THEN `refs':(v store_v)list`
    STRIP_ASSUME_TAC) o SPEC `refs:(v store_v)list`) THEN
  MAP_EVERY EXISTS_TAC [`res:v`; `refs':(v store_v)list`] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `opt_sub_add o let_id`
    (GEN `f:exp->exp` (INST_TYPE [`:1`,`:FFI`] BOTTOM_UP_OPT_THM))) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[o_THM] THEN MESON_TAC[let_id_thm; opt_sub_add_thm]; ALL_TAC] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC(ISPEC `abs2let`
    (GEN `f:exp->exp` (INST_TYPE [`:1`,`:FFI`] BOTTOM_UP_OPT_THM))) THEN
  ANTS_TAC THENL [MESON_TAC[abs2let_thm]; ALL_TAC] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;
