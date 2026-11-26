(* ========================================================================= *)
(* ml_translator: port of HOL4 translator/ml_translatorScript.sml (CakeML    *)
(* v3479).  Defines Eval and other core definitions used by the translator. *)
(* The theorems about Eval serve as an interface between the source        *)
(* semantics and the translator's automation (they are its templates).     *)
(* ========================================================================= *)

needs "hol4/machine_ieee.ml";;
needs "translator/ml_prog.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/proofs/evaluateProps.ml";;
needs "semantics/fpSem.ml";;
needs "basis/pure/mlvector.ml";;
needs "basis/pure/mlstring.ml";;
needs "semantics/evaluate.ml";;

type_invention_error := true;;

(* HOL4: Type state = ``:'ffi semanticPrimitives$state`` (names.tsv ml_state)  *)
(* is an abbreviation with a type variable: written (FFI)state here.         *)
(* HOL4's local overloads True_ast and False_ast are written out:            *)
(* App (Test (Compare Leq) IntT) [Lit (IntLit (&0)); Lit (IntLit (&0))] and  *)
(* App (Test (Compare Lt) IntT) [Lit (IntLit (&0)); Lit (IntLit (&0))].     *)

(* ------------------------------------------------------------------------- *)
(* Definitions                                                               *)
(* ------------------------------------------------------------------------- *)

(* HOL4: empty_state.  The ffi state is forced to unit: the monadic         *)
(* translator must be used for FFI calls.                                    *)

let ml_empty_state_def = cake_def
  `ml_empty_state =
     state_REC 0 empty_store (initial_ffi_state ARB one) 0 0 NONE`;;

(* HOL4: Eval *)

let ml_Eval_def = cake_def
  `ml_Eval env exp (P:v->bool) <=>
     !refs. ?res refs'.
       eval_rel (state_refs_fupd (combin_K refs) ml_empty_state) env exp
                (state_refs_fupd (combin_K (APPEND refs refs')) ml_empty_state) res /\
       P res`;;

(* HOL4: AppReturns; think of this as a Hoare triple {P} cl {Q} *)

let ml_AppReturns_def = cake_def
  `ml_AppReturns (P:v->bool) cl (Q:v->bool) <=>
     !v. P v ==>
       !refs. ?env exp refs' u.
         do_opapp [cl;v] = SOME (env,exp) /\
         eval_rel (state_refs_fupd (combin_K refs) ml_empty_state) env exp
                  (state_refs_fupd (combin_K (APPEND refs refs')) ml_empty_state) u /\
         Q u`;;

(* HOL4: Arrow, with the infix --> (HOL4 Overload "-->" = ``Arrow``) *)

let ml_Arrow_def = cake_def
  `ml_Arrow (a:A->v->bool) (b:B->v->bool) =
     \f v. !x. ml_AppReturns (a x) v (b (f x))`;;

parse_as_infix("-->",(13,"right"));;
override_interface("-->",`ml_Arrow:(A->v->bool)->(B->v->bool)->(A->B)->v->bool`);;

(* HOL4: Eq (its argument abs is renamed a: abs is an interface name) *)

let ml_Eq_def = cake_def
  `ml_Eq (a:A->v->bool) x = (\y v. x = y /\ a y v)`;;

let ml_And_def = cake_def
  `ml_And (a:A->v->bool) P x (v:v) <=> P x /\ a x v`;;

let UNIT_TYPE_def = cake_def
  `UNIT_TYPE (u:1) (v:v) <=> v = Conv NONE []`;;

let ml_INT_def = cake_def
  `ml_INT i = \v:v. v = Litv (IntLit i)`;;

let ml_NUM_def = cake_def
  `ml_NUM n = ml_INT (&n)`;;

let ml_BOOL_def = cake_def
  `ml_BOOL b = \v:v. v = Boolv b`;;

let ml_WORD_def = cake_def
  `ml_WORD (w:A word) =
     \v:v. dimindex (:A) <= 64 /\
           v = Litv (if dimindex (:A) <= 8
                     then Word8 (word_shl (word_zx w) (8 - dimindex (:A)))
                     else Word64 (word_shl (word_zx w) (64 - dimindex (:A))))`;;

let ml_FLOAT64_def = cake_def
  `ml_FLOAT64 (f:(52,11)float) =
     \v:v. v = Litv (Float64 (float_to_fp64 f))`;;

let ml_CHAR_def = cake_def
  `ml_CHAR (c:char) = \v:v. v = Litv (Char c)`;;

let STRING_TYPE_def = cake_def
  `STRING_TYPE s = \v:v. v = Litv (StrLit s)`;;

let explode_eq = prove
 (`!s l. explode s = l <=> s = implode l`,
  MESON_TAC[implode_explode; explode_implode]);;

let eq_explode = prove
 (`!s l. l = explode s <=> s = implode l`,
  MESON_TAC[implode_explode; explode_implode]);;

let HOL_STRING_TYPE_def = cake_def
  `HOL_STRING_TYPE cs = STRING_TYPE (implode cs)`;;

let ml_CONTAINER_def = cake_def
  `ml_CONTAINER (x:A) = x`;;

let ml_TAG_def = cake_def
  `ml_TAG (n:A) (x:B) = x`;;

let ml_PRECONDITION_def = cake_def
  `ml_PRECONDITION b <=> (b:bool)`;;

let ml_PreImp_def = cake_def
  `ml_PreImp b1 b2 <=> (ml_PRECONDITION b1 ==> b2)`;;

let ml_PreImpEval_def = cake_def
  `ml_PreImpEval b env code P <=> ml_PreImp b (ml_Eval env code P)`;;

(* ------------------------------------------------------------------------- *)
(* Theorems                                                                  *)
(* ------------------------------------------------------------------------- *)

let AppReturns_thm = prove
 (`ml_AppReturns P cl Q <=>
     !v. P v ==>
       ?env exp.
         do_opapp [cl;v] = SOME (env,exp) /\
         !refs. ?refs' u.
           eval_rel (state_refs_fupd (combin_K refs) ml_empty_state) env exp
                    (state_refs_fupd (combin_K (APPEND refs refs')) ml_empty_state) u /\
           Q u`,
  REWRITE_TAC[ml_AppReturns_def] THEN REPEAT GEN_TAC THEN EQ_TAC THEN
  REPEAT STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `v:v`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `[]:(v store_v)list`) THEN
    DISCH_THEN(X_CHOOSE_THEN `env:v sem_env` (X_CHOOSE_THEN `exp:exp`
      STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`env:v sem_env`; `exp:exp`] THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `refs:(v store_v)list` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `refs:(v store_v)list`) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[injectivity "option"; PAIR_EQ];
    FIRST_X_ASSUM(MP_TAC o SPEC `v:v`) THEN ASM_REWRITE_TAC[] THEN
    MESON_TAC[]]);;

(* HOL4: the local Eval_lemma of Eval_rw (Eval_rw is evaluate_def with it)  *)

let TR2AUX_Eval_lemma = prove
 (`!env exp P. ml_Eval env exp P <=>
     !refs. ?ck1 res refs' ck2.
       evaluate (state_clock_fupd (combin_K ck1) (state_refs_fupd (combin_K refs) ml_empty_state))
         env [exp] =
       (state_clock_fupd (combin_K ck2)
          (state_refs_fupd (combin_K (APPEND refs refs')) ml_empty_state),
        Rval [res]) /\ P res`,
  REWRITE_TAC[ml_Eval_def; eval_rel_def; ml_empty_state_def] THEN SIMP[] THEN
  MESON_TAC[]);;

(* Clocks: an evaluation that does not time out can be run to any final     *)
(* clock (evaluate_set_clock).                                               *)

let TR2AUX_EVAL_SET_CLOCK = prove
 (`!(s:(FFI)state) env es ck1 ck2 s' r.
     evaluate (state_clock_fupd (combin_K ck1) s) env es =
       (state_clock_fupd (combin_K ck2) s',r) /\
     ~(r = Rerr (Rabort Rtimeout_error)) ==>
     !ck. ?ck1'. evaluate (state_clock_fupd (combin_K ck1') s) env es =
                 (state_clock_fupd (combin_K ck) s',r)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP evaluate_set_clock) THEN
  SIMP[]);;

let TR2AUX_EVAL_SET_CLOCK_RVAL = prove
 (`!(s:(FFI)state) env es ck1 ck2 s' (vs:v list).
     evaluate (state_clock_fupd (combin_K ck1) s) env es =
       (state_clock_fupd (combin_K ck2) s',Rval vs) ==>
     !ck. ?ck1'. evaluate (state_clock_fupd (combin_K ck1') s) env es =
                 (state_clock_fupd (combin_K ck) s',Rval vs)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`s:(FFI)state`; `env:v sem_env`; `es:exp list`; `ck1:num`; `ck2:num`;
                `s':(FFI)state`; `Rval vs:(v list,v)result`] TR2AUX_EVAL_SET_CLOCK) THEN
  ASM_REWRITE_TAC[distinctness "result"]);;

(* Eval with an arbitrary final clock *)

let TR2AUX_Eval_any_clock = prove
 (`!env exp P. ml_Eval env exp P <=>
     !refs. ?res refs'. P res /\
       !ck. ?ck1.
         evaluate (state_clock_fupd (combin_K ck1) (state_refs_fupd (combin_K refs) ml_empty_state))
           env [exp] =
         (state_clock_fupd (combin_K ck)
            (state_refs_fupd (combin_K (APPEND refs refs')) ml_empty_state),
          Rval [res])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[TR2AUX_Eval_lemma] THEN EQ_TAC THEN
  DISCH_TAC THEN X_GEN_TAC `refs:(v store_v)list` THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o SPEC `refs:(v store_v)list`) THENL
   [MAP_EVERY EXISTS_TAC [`res:v`; `refs':(v store_v)list`] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP TR2AUX_EVAL_SET_CLOCK_RVAL);
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o SPEC `0`) THEN ASM_MESON_TAC[]]);;

(* Helpers of the port for the clock reasoning of the Eval lemmas (HOL4    *)
(* uses Eval2_tac and evaluate_add_to_clock): evaluations from the empty    *)
(* state with given refs, run to an arbitrary final clock.                  *)

let TR2AUX_ml_empty_state_accessors = prove
 (`state_clock ml_empty_state = 0 /\
   state_refs ml_empty_state = empty_store /\
   state_ffi ml_empty_state = initial_ffi_state ARB one /\
   state_next_type_stamp ml_empty_state = 0 /\
   state_next_exn_stamp ml_empty_state = 0 /\
   state_eval_state ml_empty_state = NONE`,
  REWRITE_TAC[ml_empty_state_def; state_INFO.ri_accessors]);;

let TR2AUX_eval_rel_any_clock = prove
 (`!env e R R' v.
     eval_rel (state_refs_fupd (combin_K R) ml_empty_state) env e
              (state_refs_fupd (combin_K R') ml_empty_state) v <=>
     !ck. ?ck1.
       evaluate (state_clock_fupd (combin_K ck1) (state_refs_fupd (combin_K R) ml_empty_state)) env [e] =
       (state_clock_fupd (combin_K ck) (state_refs_fupd (combin_K R') ml_empty_state),Rval [v])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[eval_rel_def] THEN
  SIMP[TR2AUX_ml_empty_state_accessors] THEN
  EQ_TAC THEN STRIP_TAC THENL
   [FIRST_X_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP TR2AUX_EVAL_SET_CLOCK_RVAL);
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o SPEC `0`) THEN ASM_MESON_TAC[]]);;

let TR2AUX_EV_NIL = prove
 (`!env R ck. ?ck1.
     evaluate (state_clock_fupd (combin_K ck1) (state_refs_fupd (combin_K R) ml_empty_state)) env [] =
     (state_clock_fupd (combin_K ck) (state_refs_fupd (combin_K R) ml_empty_state),Rval [])`,
  REPEAT GEN_TAC THEN EXISTS_TAC `ck:num` THEN REWRITE_TAC[evaluate_def]);;

let TR2AUX_EV_CONS = prove
 (`!env e1 es R R1 R2 v1 vs.
     (!ck. ?ck1.
        evaluate (state_clock_fupd (combin_K ck1) (state_refs_fupd (combin_K R) ml_empty_state))
          env [e1] =
        (state_clock_fupd (combin_K ck) (state_refs_fupd (combin_K R1) ml_empty_state),Rval [v1])) /\
     (!ck. ?ck1.
        evaluate (state_clock_fupd (combin_K ck1) (state_refs_fupd (combin_K R1) ml_empty_state))
          env es =
        (state_clock_fupd (combin_K ck) (state_refs_fupd (combin_K R2) ml_empty_state),Rval vs)) ==>
     !ck. ?ck1.
        evaluate (state_clock_fupd (combin_K ck1) (state_refs_fupd (combin_K R) ml_empty_state))
          env (CONS e1 es) =
        (state_clock_fupd (combin_K ck) (state_refs_fupd (combin_K R2) ml_empty_state),
         Rval (CONS v1 vs))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "h1") (LABEL_TAC "h2")) THEN
  X_GEN_TAC `ck:num` THEN
  REMOVE_THEN "h2" (X_CHOOSE_TAC `c2:num` o SPEC `ck:num`) THEN
  REMOVE_THEN "h1" (X_CHOOSE_TAC `c1:num` o SPEC `c2:num`) THEN
  EXISTS_TAC `c1:num` THEN ONCE_REWRITE_TAC[evaluate_cons] THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN REWRITE_TAC[APPEND]);;

let TR2AUX_EV_APP_SIMPLE = prove
 (`!env op es R R1 vs R2 res.
     getOpClass op = Simple /\
     (!ck. ?ck1.
        evaluate (state_clock_fupd (combin_K ck1) (state_refs_fupd (combin_K R) ml_empty_state))
          env (REVERSE es) =
        (state_clock_fupd (combin_K ck) (state_refs_fupd (combin_K R1) ml_empty_state),Rval vs)) /\
     do_app (R1,state_ffi ml_empty_state) op (REVERSE vs) =
       SOME ((R2,state_ffi ml_empty_state),Rval res) ==>
     !ck. ?ck1.
        evaluate (state_clock_fupd (combin_K ck1) (state_refs_fupd (combin_K R) ml_empty_state))
          env [App op es] =
        (state_clock_fupd (combin_K ck) (state_refs_fupd (combin_K R2) ml_empty_state),Rval [res])`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "h1") ASSUME_TAC)) THEN
  X_GEN_TAC `ck:num` THEN
  REMOVE_THEN "h1" (X_CHOOSE_TAC `c1:num` o SPEC `ck:num`) THEN
  EXISTS_TAC `c1:num` THEN REWRITE_TAC[evaluate_def] THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  SIMP[] THEN ASM_REWRITE_TAC[] THEN
  CAKE_REWRITE_TAC[] THEN REWRITE_TAC[list_result_def] THEN
  REWRITE_TAC[PAIR_EQ; state_component_equality] THEN SIMP[]);;

let TR2AUX_EV_APP_OPAPP = prove
 (`!env es R R1 vs env' e R2 res.
     (!ck. ?ck1.
        evaluate (state_clock_fupd (combin_K ck1) (state_refs_fupd (combin_K R) ml_empty_state))
          env (REVERSE es) =
        (state_clock_fupd (combin_K ck) (state_refs_fupd (combin_K R1) ml_empty_state),Rval vs)) /\
     do_opapp (REVERSE vs) = SOME (env',e) /\
     (!ck. ?ck1.
        evaluate (state_clock_fupd (combin_K ck1) (state_refs_fupd (combin_K R1) ml_empty_state))
          env' [e] =
        (state_clock_fupd (combin_K ck) (state_refs_fupd (combin_K R2) ml_empty_state),Rval [res])) ==>
     !ck. ?ck1.
        evaluate (state_clock_fupd (combin_K ck1) (state_refs_fupd (combin_K R) ml_empty_state))
          env [App Opapp es] =
        (state_clock_fupd (combin_K ck) (state_refs_fupd (combin_K R2) ml_empty_state),Rval [res])`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "h1") (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "h2"))) THEN
  X_GEN_TAC `ck:num` THEN
  REMOVE_THEN "h2" (X_CHOOSE_TAC `c2:num` o SPEC `ck:num`) THEN
  REMOVE_THEN "h1" (X_CHOOSE_TAC `c1:num` o SPEC `c2 + 1`) THEN
  EXISTS_TAC `c1:num` THEN REWRITE_TAC[evaluate_def; getOpClass_def] THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  CAKE_REWRITE_TAC[] THEN SIMP[dec_clock_def; ARITH_RULE `~(c + 1 = 0) /\ (c + 1) - 1 = c`] THEN
  ASM_REWRITE_TAC[]);;

let TR2AUX_Eval_App1 = prove
 (`!env op x1 P1 Q.
     getOpClass op = Simple /\ ml_Eval env x1 P1 /\
     (!R v1. P1 v1 ==>
        ?res. do_app (R,state_ffi ml_empty_state) op [v1] =
                SOME ((R,state_ffi ml_empty_state),Rval res) /\ Q res) ==>
     ml_Eval env (App op [x1]) Q`,
  REPEAT GEN_TAC THEN REWRITE_TAC[TR2AUX_Eval_any_clock] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "e1") (LABEL_TAC "op"))) THEN
  X_GEN_TAC `refs:(v store_v)list` THEN
  REMOVE_THEN "e1" (X_CHOOSE_THEN `v1:v` (X_CHOOSE_THEN `r1:(v store_v)list`
    STRIP_ASSUME_TAC) o SPEC `refs:(v store_v)list`) THEN
  REMOVE_THEN "op" (MP_TAC o SPECL [`APPEND refs r1:(v store_v)list`; `v1:v`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `res:v` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`res:v`; `r1:(v store_v)list`] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC TR2AUX_EV_APP_SIMPLE THEN
  MAP_EVERY EXISTS_TAC [`APPEND refs r1:(v store_v)list`; `[v1:v]`] THEN
  ASM_REWRITE_TAC[REVERSE; APPEND] THEN
  MATCH_MP_TAC TR2AUX_EV_CONS THEN EXISTS_TAC `APPEND refs r1:(v store_v)list` THEN
  ASM_REWRITE_TAC[TR2AUX_EV_NIL]);;

let TR2AUX_Eval_App2 = prove
 (`!env op x1 x2 P1 P2 Q.
     getOpClass op = Simple /\ ml_Eval env x1 P1 /\ ml_Eval env x2 P2 /\
     (!R v1 v2. P1 v1 /\ P2 v2 ==>
        ?res. do_app (R,state_ffi ml_empty_state) op [v1; v2] =
                SOME ((R,state_ffi ml_empty_state),Rval res) /\ Q res) ==>
     ml_Eval env (App op [x1; x2]) Q`,
  REPEAT GEN_TAC THEN REWRITE_TAC[TR2AUX_Eval_any_clock] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "e1")
    (CONJUNCTS_THEN2 (LABEL_TAC "e2") (LABEL_TAC "op")))) THEN
  X_GEN_TAC `refs:(v store_v)list` THEN
  REMOVE_THEN "e2" (X_CHOOSE_THEN `v2:v` (X_CHOOSE_THEN `r2:(v store_v)list`
    STRIP_ASSUME_TAC) o SPEC `refs:(v store_v)list`) THEN
  REMOVE_THEN "e1" (X_CHOOSE_THEN `v1:v` (X_CHOOSE_THEN `r1:(v store_v)list`
    STRIP_ASSUME_TAC) o SPEC `APPEND refs r2:(v store_v)list`) THEN
  REMOVE_THEN "op" (MP_TAC o SPECL [`APPEND (APPEND refs r2) r1:(v store_v)list`;
    `v1:v`; `v2:v`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `res:v` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`res:v`; `APPEND r2 r1:(v store_v)list`] THEN
  ASM_REWRITE_TAC[APPEND_ASSOC] THEN
  MATCH_MP_TAC TR2AUX_EV_APP_SIMPLE THEN
  MAP_EVERY EXISTS_TAC [`APPEND (APPEND refs r2) r1:(v store_v)list`; `[v2:v; v1]`] THEN
  ASM_REWRITE_TAC[REVERSE; APPEND] THEN
  MATCH_MP_TAC TR2AUX_EV_CONS THEN EXISTS_TAC `APPEND refs r2:(v store_v)list` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC TR2AUX_EV_CONS THEN EXISTS_TAC `APPEND (APPEND refs r2) r1:(v store_v)list` THEN
  ASM_REWRITE_TAC[TR2AUX_EV_NIL]);;

let TR2AUX_Eval_App3 = prove
 (`!env op x1 x2 x3 P1 P2 P3 Q.
     getOpClass op = Simple /\ ml_Eval env x1 P1 /\ ml_Eval env x2 P2 /\
     ml_Eval env x3 P3 /\
     (!R v1 v2 v3. P1 v1 /\ P2 v2 /\ P3 v3 ==>
        ?res. do_app (R,state_ffi ml_empty_state) op [v1; v2; v3] =
                SOME ((R,state_ffi ml_empty_state),Rval res) /\ Q res) ==>
     ml_Eval env (App op [x1; x2; x3]) Q`,
  REPEAT GEN_TAC THEN REWRITE_TAC[TR2AUX_Eval_any_clock] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "e1")
    (CONJUNCTS_THEN2 (LABEL_TAC "e2") (CONJUNCTS_THEN2 (LABEL_TAC "e3")
      (LABEL_TAC "op"))))) THEN
  X_GEN_TAC `refs:(v store_v)list` THEN
  REMOVE_THEN "e3" (X_CHOOSE_THEN `v3:v` (X_CHOOSE_THEN `r3:(v store_v)list`
    STRIP_ASSUME_TAC) o SPEC `refs:(v store_v)list`) THEN
  REMOVE_THEN "e2" (X_CHOOSE_THEN `v2:v` (X_CHOOSE_THEN `r2:(v store_v)list`
    STRIP_ASSUME_TAC) o SPEC `APPEND refs r3:(v store_v)list`) THEN
  REMOVE_THEN "e1" (X_CHOOSE_THEN `v1:v` (X_CHOOSE_THEN `r1:(v store_v)list`
    STRIP_ASSUME_TAC) o SPEC `APPEND (APPEND refs r3) r2:(v store_v)list`) THEN
  REMOVE_THEN "op" (MP_TAC o SPECL
    [`APPEND (APPEND (APPEND refs r3) r2) r1:(v store_v)list`; `v1:v`; `v2:v`; `v3:v`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `res:v` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`res:v`; `APPEND r3 (APPEND r2 r1):(v store_v)list`] THEN
  ASM_REWRITE_TAC[APPEND_ASSOC] THEN
  MATCH_MP_TAC TR2AUX_EV_APP_SIMPLE THEN
  MAP_EVERY EXISTS_TAC [`APPEND (APPEND (APPEND refs r3) r2) r1:(v store_v)list`;
    `[v3:v; v2; v1]`] THEN
  ASM_REWRITE_TAC[REVERSE; APPEND] THEN
  MATCH_MP_TAC TR2AUX_EV_CONS THEN EXISTS_TAC `APPEND refs r3:(v store_v)list` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC TR2AUX_EV_CONS THEN EXISTS_TAC `APPEND (APPEND refs r3) r2:(v store_v)list` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC TR2AUX_EV_CONS THEN
  EXISTS_TAC `APPEND (APPEND (APPEND refs r3) r2) r1:(v store_v)list` THEN
  ASM_REWRITE_TAC[TR2AUX_EV_NIL]);;

let evaluate_empty_state_IMP = prove
 (`eval_rel (state_refs_fupd (combin_K (state_refs (s:(FFI)state))) ml_empty_state) env exp
              (state_refs_fupd (combin_K (APPEND (state_refs s) refs')) ml_empty_state) x ==>
     eval_rel s env exp (state_refs_fupd (combin_K (APPEND (state_refs s) refs')) s) x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[eval_rel_def] THEN SIMP[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`state_clock_fupd (combin_K ck1) (state_refs_fupd (combin_K (state_refs (s:(FFI)state)))
       ml_empty_state)`; `env:v sem_env`; `[exp:exp]`;
    `state_clock_fupd (combin_K ck2) (state_refs_fupd (combin_K (APPEND (state_refs (s:(FFI)state))
       refs')) ml_empty_state)`; `Rval [x]:(v list,v)result`; `s:(FFI)state`]
   evaluate_ffi_etc_intro) THEN
  ASM_REWRITE_TAC[distinctness "result"] THEN SIMP[TR2AUX_ml_empty_state_accessors]);;

let Eval_Arrow = prove
 (`ml_Eval env x1 ((a --> b) (f:A->B)) ==> ml_Eval env x2 (a x) ==>
     ml_Eval env (App Opapp [x1;x2]) (b (f x))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[TR2AUX_Eval_any_clock] THEN
  DISCH_THEN(LABEL_TAC "e1") THEN DISCH_THEN(LABEL_TAC "e2") THEN
  X_GEN_TAC `refs:(v store_v)list` THEN
  REMOVE_THEN "e2" (X_CHOOSE_THEN `v2:v` (X_CHOOSE_THEN `r2:(v store_v)list`
    STRIP_ASSUME_TAC) o SPEC `refs:(v store_v)list`) THEN
  REMOVE_THEN "e1" (X_CHOOSE_THEN `v1:v` (X_CHOOSE_THEN `r1:(v store_v)list`
    STRIP_ASSUME_TAC) o SPEC `APPEND refs r2:(v store_v)list`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:A` o REWRITE_RULE[ml_Arrow_def]) THEN
  REWRITE_TAC[ml_AppReturns_def] THEN
  DISCH_THEN(MP_TAC o SPEC `v2:v`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `APPEND (APPEND refs r2) r1:(v store_v)list`) THEN
  REWRITE_TAC[TR2AUX_eval_rel_any_clock] THEN
  DISCH_THEN(X_CHOOSE_THEN `env':v sem_env` (X_CHOOSE_THEN `e:exp`
    (X_CHOOSE_THEN `r3:(v store_v)list` (X_CHOOSE_THEN `u:v` STRIP_ASSUME_TAC)))) THEN
  MAP_EVERY EXISTS_TAC [`u:v`; `APPEND r2 (APPEND r1 r3):(v store_v)list`] THEN
  ASM_REWRITE_TAC[APPEND_ASSOC] THEN
  MATCH_MP_TAC TR2AUX_EV_APP_OPAPP THEN
  MAP_EVERY EXISTS_TAC [`APPEND (APPEND refs r2) r1:(v store_v)list`; `[v2:v; v1]`;
    `env':v sem_env`; `e:exp`] THEN
  ASM_REWRITE_TAC[REVERSE; APPEND] THEN
  MATCH_MP_TAC TR2AUX_EV_CONS THEN EXISTS_TAC `APPEND refs r2:(v store_v)list` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC TR2AUX_EV_CONS THEN EXISTS_TAC `APPEND (APPEND refs r2) r1:(v store_v)list` THEN
  ASM_REWRITE_TAC[TR2AUX_EV_NIL]);;

let Eval_Fun = prove
 (`(!v x. a x v ==> ml_Eval (ml_write name v env) body (b ((f:A->B) x))) ==>
     ml_Eval env (Fun name body) ((a --> b) f)`,
  REWRITE_TAC[ml_Eval_def; ml_Arrow_def; ml_AppReturns_def] THEN REPEAT STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`Closure env name body`; `[]:(v store_v)list`] THEN
  REWRITE_TAC[TR2AUX_eval_rel_any_clock; evaluate_def; APPEND_NIL] THEN CONJ_TAC THENL
   [MESON_TAC[];
    REPEAT STRIP_TAC THEN SIMP[do_opapp_def; GSYM ml_write_def] THEN
    FIRST_X_ASSUM(fun th -> FIRST_ASSUM(MP_TAC o MATCH_MP th)) THEN
    DISCH_THEN(MP_TAC o SPEC `refs:(v store_v)list`) THEN
    REWRITE_TAC[TR2AUX_eval_rel_any_clock] THEN MESON_TAC[]]);;

let Eval_Fun_Eq = prove
 (`(!v. a (x:A) v ==> ml_Eval (ml_write name v env) body (b ((f:A->B) x))) ==>
     ml_Eval env (Fun name body) ((ml_Eq a x --> b) f)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC Eval_Fun THEN
  REWRITE_TAC[ml_Eq_def] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ASM_SIMP_TAC[]);;

let And_IMP_Eq = prove
 (`ml_Eval env exp ((ml_And a P --> b) (f:A->B)) ==>
     (P x ==> ml_Eval env exp ((ml_Eq a x --> b) f))`,
  REWRITE_TAC[ml_Eval_def; ml_Arrow_def; ml_AppReturns_def; ml_And_def; ml_Eq_def] THEN
  MESON_TAC[]);;

(* HOL4's Eval_Fun_rw (below), proved here for the proofs that need it    *)

let TR2AUX_Eval_Fun_rw = prove
 (`!env n exp P. ml_Eval env (Fun n exp) P <=> P (Closure env n exp)`,
  REWRITE_TAC[TR2AUX_Eval_lemma; evaluate_def] THEN
  REWRITE_TAC[PAIR_EQ; injectivity "result"; CONS_11; state_component_equality] THEN
  SIMP[] THEN MESON_TAC[APPEND_NIL]);;

let Eq_IMP_And = prove
 (`(!x. P x ==> ml_Eval env (Fun name exp) ((ml_Eq a x --> b) (f:A->B))) ==>
     ml_Eval env (Fun name exp) ((ml_And a P --> b) f)`,
  REWRITE_TAC[TR2AUX_Eval_Fun_rw; ml_Arrow_def; ml_AppReturns_def; ml_And_def;
    ml_Eq_def] THEN
  MESON_TAC[]);;
let Eval_Fun_And = prove
 (`(!v x. P x ==> a x v ==> ml_Eval (ml_write name v env) body (b ((f:A->B) x))) ==>
   ml_Eval env (Fun name body) ((ml_And a P --> b) f)`,
  DISCH_TAC THEN MATCH_MP_TAC Eval_Fun THEN REWRITE_TAC[ml_And_def] THEN
  ASM_MESON_TAC[]);;

let TR2AUX_EV_LET = prove
 (`!env xo e1 e2 R R1 R2 v1 v2.
     (!ck. ?ck1.
        evaluate (state_clock_fupd (combin_K ck1) (state_refs_fupd (combin_K R) ml_empty_state))
          env [e1] =
        (state_clock_fupd (combin_K ck) (state_refs_fupd (combin_K R1) ml_empty_state),Rval [v1])) /\
     (!ck. ?ck1.
        evaluate (state_clock_fupd (combin_K ck1) (state_refs_fupd (combin_K R1) ml_empty_state))
          (sem_env_v_fupd (combin_K (nsOptBind xo v1 (sem_env_v env))) env) [e2] =
        (state_clock_fupd (combin_K ck) (state_refs_fupd (combin_K R2) ml_empty_state),Rval [v2])) ==>
     !ck. ?ck1.
        evaluate (state_clock_fupd (combin_K ck1) (state_refs_fupd (combin_K R) ml_empty_state))
          env [Let xo e1 e2] =
        (state_clock_fupd (combin_K ck) (state_refs_fupd (combin_K R2) ml_empty_state),Rval [v2])`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "h1") (LABEL_TAC "h2")) THEN
  X_GEN_TAC `ck:num` THEN
  REMOVE_THEN "h2" (X_CHOOSE_TAC `c2:num` o SPEC `ck:num`) THEN
  REMOVE_THEN "h1" (X_CHOOSE_TAC `c1:num` o SPEC `c2:num`) THEN
  EXISTS_TAC `c1:num` THEN REWRITE_TAC[evaluate_def] THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN REWRITE_TAC[HD] THEN
  ASM_REWRITE_TAC[]);;

let Eval_Let = prove
 (`ml_Eval env exp (a res) /\
   (!v. a res v ==> ml_Eval (ml_write name v env) body (b ((f:A->B) res))) ==>
   ml_Eval env (Let (SOME name) exp body) (b (LET f res))`,
  REWRITE_TAC[TR2AUX_Eval_any_clock; LET_DEF] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "e1") (LABEL_TAC "e2")) THEN
  X_GEN_TAC `refs:(v store_v)list` THEN
  REMOVE_THEN "e1" (X_CHOOSE_THEN `v1:v` (X_CHOOSE_THEN `r1:(v store_v)list`
    STRIP_ASSUME_TAC) o SPEC `refs:(v store_v)list`) THEN
  REMOVE_THEN "e2" (MP_TAC o SPEC `v1:v`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `v2:v` (X_CHOOSE_THEN `r2:(v store_v)list`
    STRIP_ASSUME_TAC) o SPEC `APPEND refs r1:(v store_v)list`) THEN
  MAP_EVERY EXISTS_TAC [`v2:v`; `APPEND r1 r2:(v store_v)list`] THEN
  ASM_REWRITE_TAC[APPEND_ASSOC] THEN MATCH_MP_TAC TR2AUX_EV_LET THEN
  MAP_EVERY EXISTS_TAC [`APPEND refs r1:(v store_v)list`; `v1:v`] THEN
  REWRITE_TAC[nsOptBind_def] THEN CAKE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[GSYM ml_write_def]);;

let Eval_Var_general = prove
 (`P v ==> !iden. nsLookup (sem_env_v env) iden = SOME v ==> ml_Eval env (Var iden) P`,
  REWRITE_TAC[TR2AUX_Eval_any_clock] THEN REPEAT STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`v:v`; `[]:(v store_v)list`] THEN
  ASM_REWRITE_TAC[evaluate_def; APPEND_NIL] THEN CAKE_REWRITE_TAC[] THEN
  MESON_TAC[]);;

let Eval_Var_Short = prove
 (`P v ==> !name env.
     nsLookup (sem_env_v env) (Short name) = SOME v ==>
     ml_Eval env (Var (Short name)) P`,
  MESON_TAC[Eval_Var_general]);;

let Eval_Var_Long = prove
 (`P v ==> !m name env.
     nsLookup (sem_env_v env) (Long m (Short name)) = SOME v ==>
     ml_Eval env (Var (Long m (Short name))) P`,
  MESON_TAC[Eval_Var_general]);;

(* HOL4's Eval_Var_nsLookup (below), proved here for the proofs that need it *)

let TR2AUX_Eval_Var_nsLookup = prove
 (CASE_TERM `!(env:v sem_env) (id:(mlstring,mlstring)id) P. ml_Eval env (Var id) P <=>
     (match nsLookup (sem_env_v env) id with NONE -> F | SOME v -> P v)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[TR2AUX_Eval_lemma; evaluate_def] THEN
  CASES_ON `nsLookup (sem_env_v (env:v sem_env)) (id:(mlstring,mlstring)id)` THEN
  CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ; injectivity "result"; distinctness "result"; CONS_11;
    state_component_equality] THEN
  SIMP[] THEN MESON_TAC[APPEND_NIL]);;

let Eval_Var_SWAP_ENV = prove
 (`!env1. ml_Eval env1 (Var (Short name)) P /\
          ml_lookup_var name env = ml_lookup_var name env1 ==>
          ml_Eval env (Var (Short name)) P`,
  REWRITE_TAC[TR2AUX_Eval_Var_nsLookup; ml_lookup_var_def] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let LOOKUP_VAR_def = cake_def
  `LOOKUP_VAR name env (x:v) <=> ml_lookup_var name env = SOME x`;;

let LOOKUP_VAR_THM = prove
 (`LOOKUP_VAR name env x ==> ml_Eval env (Var (Short name)) ((=) x)`,
  REWRITE_TAC[LOOKUP_VAR_def; ml_lookup_var_def; TR2AUX_Eval_Var_nsLookup] THEN
  DISCH_THEN SUBST1_TAC THEN CAKE_REWRITE_TAC[]);;

let LOOKUP_VAR_SIMP = prove
 (`LOOKUP_VAR name (ml_write x v env) y =
   if x = name then v = y else LOOKUP_VAR name env y`,
  REWRITE_TAC[LOOKUP_VAR_def; ml_write_def; ml_lookup_var_def] THEN
  COND_CASES_TAC THEN SIMP[nsLookup_nsBind] THEN ASM_MESON_TAC[]);;
(* an expression that evaluates in one step, without touching the state *)

let TR2AUX_Eval_const = prove
 (`!env e P v.
     (!st:(1)state. evaluate st env [e] = (st,Rval [v])) /\ P v ==> ml_Eval env e P`,
  REWRITE_TAC[TR2AUX_Eval_any_clock] THEN REPEAT STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`v:v`; `[]:(v store_v)list`] THEN
  ASM_REWRITE_TAC[APPEND_NIL] THEN X_GEN_TAC `ck:num` THEN EXISTS_TAC `ck:num` THEN
  ASM_REWRITE_TAC[]);;

let Eval_Val_INT = prove
 (`!n. ml_Eval env (Lit (IntLit n)) (ml_INT n)`,
  GEN_TAC THEN MATCH_MP_TAC TR2AUX_Eval_const THEN
  EXISTS_TAC `Litv (IntLit n)` THEN REWRITE_TAC[evaluate_def; ml_INT_def]);;

let Eval_Val_NUM = prove
 (`!n. ml_Eval env (Lit (IntLit (&n))) (ml_NUM n)`,
  REWRITE_TAC[ml_NUM_def; Eval_Val_INT]);;

let Eval_Val_UNIT = prove
 (`ml_Eval env (Con NONE []) (UNIT_TYPE one)`,
  MATCH_MP_TAC TR2AUX_Eval_const THEN EXISTS_TAC `Conv NONE []` THEN
  REWRITE_TAC[evaluate_def; UNIT_TYPE_def; LENGTH; REVERSE; do_con_check_def;
    build_conv_def] THEN
  CAKE_REWRITE_TAC[] THEN REWRITE_TAC[REVERSE]);;

(* True_ast and False_ast *)

let TR2AUX_Eval_Val_BOOL = prove
 (`!env opb b.
     (int_cmp opb (&0) (&0) <=> b) ==>
     ml_Eval env (App (Test (Compare opb) IntT) [Lit (IntLit (&0)); Lit (IntLit (&0))])
       (ml_BOOL b)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC TR2AUX_Eval_App2 THEN
  MAP_EVERY EXISTS_TAC [`ml_INT (&0)`; `ml_INT (&0)`] THEN
  REWRITE_TAC[Eval_Val_INT; getOpClass_def] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[ml_INT_def; ml_BOOL_def] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[do_app_def] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[do_test_def; dest_Litv_def] THEN CAKE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let Eval_Val_BOOL_T = prove
 (`ml_Eval env (App (Test (Compare Leq) IntT) [Lit (IntLit (&0)); Lit (IntLit (&0))])
     (ml_BOOL T)`,
  MATCH_MP_TAC TR2AUX_Eval_Val_BOOL THEN REWRITE_TAC[int_cmp_def] THEN
  CAKE_REWRITE_TAC[] THEN INT_ARITH_TAC);;

let Eval_Val_BOOL_F = prove
 (`ml_Eval env (App (Test (Compare Lt) IntT) [Lit (IntLit (&0)); Lit (IntLit (&0))])
     (ml_BOOL F)`,
  MATCH_MP_TAC TR2AUX_Eval_Val_BOOL THEN REWRITE_TAC[int_cmp_def] THEN
  CAKE_REWRITE_TAC[] THEN INT_ARITH_TAC);;

let Eval_Val_CHAR = prove
 (`!c. ml_Eval env (Lit (Char c)) (ml_CHAR c)`,
  GEN_TAC THEN MATCH_MP_TAC TR2AUX_Eval_const THEN
  EXISTS_TAC `Litv (Char c)` THEN REWRITE_TAC[evaluate_def; ml_CHAR_def]);;

let Eval_Val_STRING = prove
 (`!s. ml_Eval env (Lit (StrLit s)) (STRING_TYPE s)`,
  GEN_TAC THEN MATCH_MP_TAC TR2AUX_Eval_const THEN
  EXISTS_TAC `Litv (StrLit s)` THEN REWRITE_TAC[evaluate_def; STRING_TYPE_def]);;

let Eval_Val_WORD = prove
 (`!w:A word.
     dimindex(:A) <= 64 ==>
     ml_Eval env (Lit (if dimindex(:A) <= 8
                       then Word8 (word_shl (word_zx w) (8 - dimindex(:A)))
                       else Word64 (word_shl (word_zx w) (64 - dimindex(:A)))))
             (ml_WORD w)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC TR2AUX_Eval_const THEN
  EXISTS_TAC `Litv (if dimindex(:A) <= 8
                    then Word8 (word_shl (word_zx (w:A word)) (8 - dimindex(:A)))
                    else Word64 (word_shl (word_zx w) (64 - dimindex(:A))))` THEN
  ASM_REWRITE_TAC[evaluate_def; ml_WORD_def]);;

let Eval_Val_FLOAT64 = prove
 (`!f:(52,11)float. ml_Eval env (Lit (Float64 (float_to_fp64 f))) (ml_FLOAT64 f)`,
  GEN_TAC THEN MATCH_MP_TAC TR2AUX_Eval_const THEN
  EXISTS_TAC `Litv (Float64 (float_to_fp64 (f:(52,11)float)))` THEN
  REWRITE_TAC[evaluate_def; ml_FLOAT64_def]);;
(* ------------------------------------------------------------------------- *)
(* Equality                                                                  *)
(* ------------------------------------------------------------------------- *)

let no_closures_def = cake_def
  `(no_closures (Conv _ vs) <=> ALL no_closures vs) /\
   (no_closures (Vectorv vs) <=> ALL no_closures vs) /\
   (no_closures (Closure _ _ _) <=> F) /\
   (no_closures (Recclosure _ _ _) <=> F) /\
   (no_closures (Env _ _) <=> F) /\
   (no_closures _ <=> T)`;;

let no_closures_ind = cake_ind "no_closures";;

let types_match_def = cake_def
  `(types_match (Litv l1) (Litv l2) <=> lit_same_type l1 l2) /\
   (types_match (Loc b1 n1) (Loc b2 n2) <=> b1 /\ b2) /\
   (types_match (Conv cn1 vs1) (Conv cn2 vs2) <=>
      ctor_same_type cn1 cn2 /\ (cn1 = cn2 ==> types_match_list vs1 vs2)) /\
   (types_match _ _ <=> F) /\
   (types_match_list [] [] <=> T) /\
   (types_match_list (CONS v1 vs1) (CONS v2 vs2) <=>
      types_match v1 v2 /\ types_match_list vs1 vs2) /\
   (types_match_list _ _ <=> F)`;;

(* HOL4 names the invariant abs (an interface name in HOL Light): a here *)

let EqualityType_def = cake_def
  `EqualityType (a:A->v->bool) <=>
     (!x1 v1. a x1 v1 ==> no_closures v1) /\
     (!x1 v1 x2 v2. a x1 v1 /\ a x2 v2 ==> (v1 = v2 <=> x1 = x2)) /\
     (!x1 v1 x2 v2. a x1 v1 /\ a x2 v2 ==> types_match v1 v2)`;;

(* HOL4 [local] *)

let LSL_n2w_eq = prove
 (`a < 2 EXP (dimindex (:A) - n) /\ b < 2 EXP (dimindex (:A) - n) /\
   n <= dimindex (:A) ==>
   (word_shl (word a) n = word_shl (word b:A word) n <=> a = b)`,
  STRIP_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SHL; VAL_WORD] THEN
  SUBGOAL_THEN `2 EXP dimindex (:A) = 2 EXP n * 2 EXP (dimindex (:A) - n)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!c. c < 2 EXP (dimindex (:A) - n) ==>
     (2 EXP n * c MOD (2 EXP n * 2 EXP (dimindex (:A) - n))) MOD
     (2 EXP n * 2 EXP (dimindex (:A) - n)) = 2 EXP n * c` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `c < 2 EXP n * 2 EXP (dimindex (:A) - n)` ASSUME_TAC THENL
     [TRANS_TAC LTE_TRANS `2 EXP (dimindex (:A) - n)` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[ARITH_RULE `a <= b * a <=> 1 * a <= b * a`] THEN
      REWRITE_TAC[LE_MULT_RCANCEL] THEN REWRITE_TAC[ARITH_RULE `1 <= x <=> ~(x = 0)`] THEN
      REWRITE_TAC[EXP_EQ_0] THEN ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[MOD_LT] THEN MATCH_MP_TAC MOD_LT THEN
    ASM_REWRITE_TAC[LT_MULT_LCANCEL; EXP_EQ_0] THEN ARITH_TAC;
    ASM_SIMP_TAC[] THEN REWRITE_TAC[EQ_MULT_LCANCEL; EXP_EQ_0] THEN ARITH_TAC]);;

(* a word shifted to the top of a wider word keeps all its bits *)

let TR2AUX_WORD_SHL_ZX_11 = prove
 (`!(w1:A word) (w2:A word).
     dimindex(:A) <= dimindex(:B) ==>
     (word_shl (word_zx w1:B word) (dimindex(:B) - dimindex(:A)) =
      word_shl (word_zx w2:B word) (dimindex(:B) - dimindex(:A)) <=> w1 = w2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_SHL; BIT_WORD_ZX] THEN
  EQ_TAC THEN DISCH_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `i + dimindex(:B) - dimindex(:A)`) THEN
    SUBGOAL_THEN `i + dimindex(:B) - dimindex(:A) < dimindex(:B) /\
                  dimindex(:B) - dimindex(:A) <= i + dimindex(:B) - dimindex(:A) /\
                  (i + dimindex(:B) - dimindex(:A)) - (dimindex(:B) - dimindex(:A)) = i /\
                  i < dimindex(:B)`
      (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC;
    ASM_CASES_TAC `dimindex(:B) - dimindex(:A) <= i` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i - (dimindex(:B) - dimindex(:A))`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]]]);;

let TR2AUX_ml_WORD_11 = prove
 (`!(w1:A word) w2 v1 v2. ml_WORD w1 v1 /\ ml_WORD w2 v2 ==> (v1 = v2 <=> w1 = w2)`,
  REWRITE_TAC[ml_WORD_def] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN
  REWRITE_TAC[injectivity "v"; injectivity "lit"] THENL
   [MP_TAC(ISPECL [`w1:A word`; `w2:A word`] (INST_TYPE [`:8`,`:B`] TR2AUX_WORD_SHL_ZX_11));
    MP_TAC(ISPECL [`w1:A word`; `w2:A word`] (INST_TYPE [`:64`,`:B`] TR2AUX_WORD_SHL_ZX_11))]
  THEN ASM_REWRITE_TAC[DIMINDEX_8; DIMINDEX_64]);;

let EqualityType_NUM_BOOL = prove
 (`EqualityType ml_NUM /\ EqualityType ml_INT /\
   EqualityType ml_BOOL /\ EqualityType (ml_WORD:A word->v->bool) /\
   EqualityType ml_CHAR /\ EqualityType STRING_TYPE /\
   EqualityType UNIT_TYPE /\ EqualityType HOL_STRING_TYPE /\
   EqualityType (ml_WORD:A word->v->bool) /\ EqualityType ml_FLOAT64`,
  REWRITE_TAC[EqualityType_def] THEN REPEAT CONJ_TAC THEN
  TRY(MATCH_ACCEPT_TAC TR2AUX_ml_WORD_11) THEN
  REWRITE_TAC[ml_NUM_def; ml_INT_def; ml_BOOL_def; ml_WORD_def; ml_CHAR_def;
    STRING_TYPE_def; UNIT_TYPE_def; HOL_STRING_TYPE_def; ml_FLOAT64_def] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[semanticPrimitives_Boolv_def] THEN
  REPEAT COND_CASES_TAC THEN
  ASM_REWRITE_TAC[no_closures_def; types_match_def; lit_same_type_def;
    ctor_same_type_def; same_type_def; ALL] THEN
  CAKE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[injectivity "v"; injectivity "lit"; injectivity "option";
    injectivity "stamp"; INT_OF_NUM_EQ; injectivity "mlstring"; float_to_fp64_11;
    same_type_def] THEN
  ASM_SIMP_TAC[] THEN TRY(FIRST_ASSUM(CONTR_TAC o REWRITE_RULE[])) THEN
  ASM_MESON_TAC[one]);;
let EqualityType_at_def = cake_def
  `EqualityType_at (a:A->v->bool) x <=>
     (!v. a x v ==> no_closures v) /\
     (!v x2 v2. a x v /\ a x2 v2 ==> (v = v2 <=> x = x2)) /\
     (!v x2 v2. a x v /\ a x2 v2 ==> types_match v v2)`;;

let EqualityType_eq_at = prove
 (`EqualityType (TY:A->v->bool) <=> (!x. EqualityType_at TY x)`,
  REWRITE_TAC[EqualityType_def; EqualityType_at_def] THEN MESON_TAC[]);;

(* HOL4's marker Case (markerTheory.Case_def: Case X = T), which the        *)
(* library layer does not port (hol4/basic.ml): defined here               *)

let marker_Case_def = new_definition
  `marker_Case (X:A) <=> T`;;

let EqualityType_at_eq_Case_rearranged = prove
 (`EqualityType_at (TY:A->v->bool) x <=>
   !y vx vy. marker_Case (x,y,vx,vy) ==>
     TY x vx /\ TY y vy ==>
     (x = y ==> vx = vy ==> no_closures vx) /\
     (vx = vy <=> x = y) /\ types_match vx vy`,
  REWRITE_TAC[EqualityType_at_def; marker_Case_def] THEN MESON_TAC[]);;

let EqualityType_def_rearranged = prove
 (`EqualityType (a:A->v->bool) <=>
   (!x y vx vy. a x vx /\ a y vy ==>
      (x = y ==> vx = vy ==> no_closures vx) /\
      (vx = vy <=> x = y) /\ types_match vx vy)`,
  REWRITE_TAC[EqualityType_def] THEN MESON_TAC[]);;

(* HOL4 GENLIST is list_of_seq *)

let EqualityType_from_ONTO = prove
 (`(!a:A. ?r. a = num2a r /\ r < (N:num)) ==>
   (!TY stamps stn.
      list_of_seq (\n v. TY (num2a n) v) N =
        MAP (\st v. v = Conv (SOME (TypeStamp st stn)) []) stamps ==>
      ALL_DISTINCT stamps ==>
      EqualityType TY)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `LENGTH (stamps:mlstring list) = N` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o AP_TERM `LENGTH:(v->bool)list->num`) THEN
    REWRITE_TAC[LENGTH_LIST_OF_SEQ; LENGTH_MAP] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!r v. r < N ==> ((TY:A->v->bool) (num2a r) v <=>
      v = Conv (SOME (TypeStamp (EL r stamps) stn)) [])` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o AP_TERM `EL r:(v->bool)list->v->bool`) THEN
    ASM_SIMP_TAC[EL_GENLIST; EL_MAP] THEN DISCH_THEN(MP_TAC o C AP_THM `v:v`) THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[EqualityType_def_rearranged] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `y:A`; `vx:v`; `vy:v`] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `r1:num` STRIP_ASSUME_TAC o SPEC `x:A`) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `r2:num` STRIP_ASSUME_TAC o SPEC `y:A`) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN
  REWRITE_TAC[no_closures_def; ALL; types_match_def; ctor_same_type_def] THEN
  CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[same_type_def; types_match_def; injectivity "v"; injectivity "option";
    injectivity "stamp"] THEN
  EQ_TAC THENL
   [DISCH_TAC THEN SUBGOAL_THEN `r1:num = r2` (fun th -> REWRITE_TAC[th]) THEN
    ASM_MESON_TAC[EL_ALL_DISTINCT_EL_EQ];
    DISCH_TAC THEN
    FIRST_X_ASSUM(fun th ->
      MP_TAC(SPECL [`r1:num`;
        `Conv (SOME (TypeStamp (EL r1 (stamps:mlstring list)) stn)) []`] th) THEN
      MP_TAC(SPECL [`r2:num`;
        `Conv (SOME (TypeStamp (EL r1 (stamps:mlstring list)) stn)) []`] th)) THEN
    ASM_REWRITE_TAC[injectivity "v"; injectivity "option"; injectivity "stamp"] THEN
    MESON_TAC[]]);;

let EqualityType_from_ONTO_Exn = prove
 (`(!a:A. ?r. a = num2a r /\ r < (N:num)) ==>
   (!TY stamps.
      list_of_seq (\n v. TY (num2a n) v) N =
        MAP (\st v. v = Conv (SOME (ExnStamp st)) []) stamps ==>
      ALL_DISTINCT stamps ==>
      EqualityType TY)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `LENGTH (stamps:num list) = N` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o AP_TERM `LENGTH:(v->bool)list->num`) THEN
    REWRITE_TAC[LENGTH_LIST_OF_SEQ; LENGTH_MAP] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!r v. r < N ==> ((TY:A->v->bool) (num2a r) v <=>
      v = Conv (SOME (ExnStamp (EL r stamps))) [])` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o AP_TERM `EL r:(v->bool)list->v->bool`) THEN
    ASM_SIMP_TAC[EL_GENLIST; EL_MAP] THEN DISCH_THEN(MP_TAC o C AP_THM `v:v`) THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[EqualityType_def_rearranged] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `y:A`; `vx:v`; `vy:v`] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `r1:num` STRIP_ASSUME_TAC o SPEC `x:A`) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `r2:num` STRIP_ASSUME_TAC o SPEC `y:A`) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN
  REWRITE_TAC[no_closures_def; ALL; types_match_def; ctor_same_type_def] THEN
  CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[same_type_def; types_match_def; injectivity "v"; injectivity "option";
    injectivity "stamp"] THEN
  EQ_TAC THENL
   [DISCH_TAC THEN SUBGOAL_THEN `r1:num = r2` (fun th -> REWRITE_TAC[th]) THEN
    ASM_MESON_TAC[EL_ALL_DISTINCT_EL_EQ];
    DISCH_TAC THEN
    FIRST_X_ASSUM(fun th ->
      MP_TAC(SPECL [`r1:num`; `Conv (SOME (ExnStamp (EL r1 (stamps:num list)))) []`] th) THEN
      MP_TAC(SPECL [`r2:num`; `Conv (SOME (ExnStamp (EL r1 (stamps:num list)))) []`] th)) THEN
    ASM_REWRITE_TAC[injectivity "v"; injectivity "option"; injectivity "stamp"] THEN
    MESON_TAC[]]);;
let UNIT_v_def = cake_def
  `UNIT_v (u:1) = Conv NONE []`;;

let INT_v_def = cake_def
  `INT_v i = Litv (IntLit i)`;;

let NUM_v_def = cake_def
  `NUM_v n = INT_v (&n)`;;

let BOOL_v_def = cake_def
  `BOOL_v b = Boolv b`;;

let WORD_v_def = cake_def
  `WORD_v (w:A word) =
     if dimindex (:A) <= 8
     then Litv (Word8 (word_shl (word_zx w) (8 - dimindex (:A))))
     else if dimindex (:A) <= 64
     then Litv (Word64 (word_shl (word_zx w) (64 - dimindex (:A))))
     else Conv NONE []`;;

let CHAR_v_def = cake_def
  `CHAR_v (c:char) = Litv (Char c)`;;

let STRING_v_def = cake_def
  `STRING_v s = Litv (StrLit s)`;;

let HOL_STRING_v_def = cake_def
  `HOL_STRING_v cs = STRING_v (implode cs)`;;

(* HOL4 [local] *)

let types_match_list_REPLICATE = prove
 (`!n m. types_match_list (REPLICATE n x) (REPLICATE m y) <=>
         n = m /\ (0 < n ==> types_match x y)`,
  INDUCT_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[REPLICATE; types_match_def; NOT_SUC; SUC_INJ; LT_0; LT_REFL] THEN
  MESON_TAC[]);;

(* nearly all types with equality will be fully representable within v *)

let IsTypeRep_def = cake_def
  `IsTypeRep (f:A->v) R <=> (!x. R x (f x))`;;

let IsTypeRep_EqualityType_Unique = prove
 (`EqualityType R ==> IsTypeRep f R ==> IsTypeRep g R ==> g = (f:A->v)`,
  REWRITE_TAC[EqualityType_def; IsTypeRep_def; FUN_EQ_THM] THEN MESON_TAC[]);;

let IsTypeRep_EqualityType_INJ = prove
 (`EqualityType R ==> IsTypeRep f R ==> INJ (f:A->v) UNIV UNIV`,
  REWRITE_TAC[EqualityType_def; IsTypeRep_def; INJ; IN_UNIV] THEN MESON_TAC[]);;

(* HOL4: Definition DUMMY_TYPE_REP_v (the theorem has the constant's name) *)

let DUMMY_TYPE_REP_v = cake_def
  `DUMMY_TYPE_REP_v (x:A) = UNIT_v one`;;

let IsTypeRep_NUM_BOOL = prove
 (`IsTypeRep NUM_v ml_NUM /\ IsTypeRep INT_v ml_INT /\
   IsTypeRep BOOL_v ml_BOOL /\
   IsTypeRep CHAR_v ml_CHAR /\
   IsTypeRep UNIT_v UNIT_TYPE /\
   IsTypeRep STRING_v STRING_TYPE /\
   IsTypeRep HOL_STRING_v HOL_STRING_TYPE /\
   (dimindex (:A) <= 64 ==> IsTypeRep WORD_v (ml_WORD : A word -> v -> bool))`,
  REWRITE_TAC[IsTypeRep_def; NUM_v_def; INT_v_def; BOOL_v_def; CHAR_v_def; UNIT_v_def;
    STRING_v_def; HOL_STRING_v_def; WORD_v_def; ml_NUM_def; ml_INT_def; ml_BOOL_def;
    ml_CHAR_def; UNIT_TYPE_def; STRING_TYPE_def; HOL_STRING_TYPE_def; ml_WORD_def] THEN
  DISCH_TAC THEN GEN_TAC THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

let types_match_list_length = prove
 (`!vs1 vs2. types_match_list vs1 vs2 ==> LENGTH vs1 = LENGTH vs2`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC[types_match_def; LENGTH; SUC_INJ]);;

let type_match_implies_do_eq_succeeds = prove
 (`(!v1 v2. types_match v1 v2 ==> (do_eq v1 v2 = Eq_val (v1 = v2))) /\
   (!vs1 vs2.
      types_match_list vs1 vs2 ==> (do_eq_list vs1 vs2 = Eq_val (vs1 = vs2)))`,
  MATCH_MP_TAC do_eq_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[types_match_def; do_eq_def; injectivity "v"; distinctness "v";
    NOT_CONS_NIL; injectivity "list"] THEN
  TRY(SIMP_TAC[] THEN NO_TAC) THENL
   [DISCH_THEN(LABEL_TAC "ih") THEN STRIP_TAC THEN
    ASM_CASES_TAC `cn1:(stamp)option = cn2` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      SUBGOAL_THEN `types_match_list vs1 vs2` ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      FIRST_ASSUM(ASSUME_TAC o MATCH_MP types_match_list_length) THEN
      REMOVE_THEN "ih" MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih") (LABEL_TAC "ih0")) THEN STRIP_TAC THEN
    REMOVE_THEN "ih0" MP_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
    ASM_CASES_TAC `v1:v = v2` THEN ASM_REWRITE_TAC[] THEN
    REMOVE_THEN "ih" (MP_TAC o SPEC `T`) THEN
    SUBGOAL_THEN `do_eq v1 v2 = Eq_val T` (fun th -> REWRITE_TAC[th]) THENL
     [UNDISCH_TAC `do_eq v1 v2 = Eq_val (v1 = v2)` THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]]]);;

(* HOL4 [local] *)

let do_eq_succeeds = prove
 (`!a x1 v1 x2 v2. EqualityType (a:A->v->bool) /\ a x1 v1 /\ a x2 v2 ==>
     do_eq v1 v2 = Eq_val (x1 = x2)`,
  REWRITE_TAC[EqualityType_def] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `types_match v1 v2`
    (MP_TAC o MATCH_MP (CONJUNCT1 type_match_implies_do_eq_succeeds)) THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN ASM_MESON_TAC[]);;
(* HOL4 [local] *)

let empty_state_with_refs_eq = prove
 (`state_refs_fupd (combin_K r) ml_empty_state =
   state_refs_fupd (combin_K r') (state_ffi_fupd (combin_K f) (s2:(1)state)) <=>
   ?refs ffi. s2 = state_refs_fupd (combin_K refs) (state_ffi_fupd (combin_K ffi) ml_empty_state) /\
              r' = r /\ f = state_ffi ml_empty_state`,
  REWRITE_TAC[state_component_equality] THEN SIMP[] THEN MESON_TAC[]);;

(* HOL4 [local] *)

let empty_state_with_ffi_elim = prove
 (`state_refs_fupd (combin_K r) (state_ffi_fupd (combin_K (state_ffi ml_empty_state)) ml_empty_state) =
   state_refs_fupd (combin_K r) ml_empty_state`,
  REWRITE_TAC[state_component_equality] THEN SIMP[]);;

let Eval_Equality = prove
 (`ml_Eval env x1 (a y1) /\ ml_Eval env x2 (a y2) ==>
   EqualityType (a:A->v->bool) ==>
   ml_Eval env (App Equality [x1;x2]) (ml_BOOL (y1 = y2))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC TR2AUX_Eval_App2 THEN
  MAP_EVERY EXISTS_TAC [`(a:A->v->bool) y1`; `(a:A->v->bool) y2`] THEN
  ASM_REWRITE_TAC[getOpClass_def] THEN CAKE_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[do_app_def] THEN CAKE_REWRITE_TAC[] THEN
  SUBGOAL_THEN `do_eq v1 v2 = Eq_val ((y1:A) = y2)` SUBST1_TAC THENL
   [MATCH_MP_TAC do_eq_succeeds THEN EXISTS_TAC `a:A->v->bool` THEN ASM_REWRITE_TAC[];
    CAKE_REWRITE_TAC[] THEN REWRITE_TAC[ml_BOOL_def] THEN MESON_TAC[]]);;

(* booleans *)

(* rewriting with the assumptions and the case equations, three rounds *)

let TR2AUX_RED_TAC thl =
  let step = ASM_REWRITE_TAC thl THEN CAKE_REWRITE_TAC thl in
  step THEN step THEN step;;

let TR2AUX_EV_LOG_EXP = prove
 (`!env lop e1 e2 e R R1 R2 v1 v2.
     (!ck. ?ck1.
        evaluate (state_clock_fupd (combin_K ck1) (state_refs_fupd (combin_K R) ml_empty_state))
          env [e1] =
        (state_clock_fupd (combin_K ck) (state_refs_fupd (combin_K R1) ml_empty_state),Rval [v1])) /\
     do_log lop v1 e2 = SOME (Exp e) /\
     (!ck. ?ck1.
        evaluate (state_clock_fupd (combin_K ck1) (state_refs_fupd (combin_K R1) ml_empty_state))
          env [e] =
        (state_clock_fupd (combin_K ck) (state_refs_fupd (combin_K R2) ml_empty_state),Rval [v2])) ==>
     !ck. ?ck1.
        evaluate (state_clock_fupd (combin_K ck1) (state_refs_fupd (combin_K R) ml_empty_state))
          env [Log lop e1 e2] =
        (state_clock_fupd (combin_K ck) (state_refs_fupd (combin_K R2) ml_empty_state),Rval [v2])`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "h1") (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "h2"))) THEN
  X_GEN_TAC `ck:num` THEN
  REMOVE_THEN "h2" (X_CHOOSE_TAC `c2:num` o SPEC `ck:num`) THEN
  REMOVE_THEN "h1" (X_CHOOSE_TAC `c1:num` o SPEC `c2:num`) THEN
  EXISTS_TAC `c1:num` THEN REWRITE_TAC[evaluate_def] THEN TR2AUX_RED_TAC[HD]);;

let TR2AUX_EV_LOG_VAL = prove
 (`!env lop e1 e2 R R1 v1 v.
     (!ck. ?ck1.
        evaluate (state_clock_fupd (combin_K ck1) (state_refs_fupd (combin_K R) ml_empty_state))
          env [e1] =
        (state_clock_fupd (combin_K ck) (state_refs_fupd (combin_K R1) ml_empty_state),Rval [v1])) /\
     do_log lop v1 e2 = SOME (Val v) ==>
     !ck. ?ck1.
        evaluate (state_clock_fupd (combin_K ck1) (state_refs_fupd (combin_K R) ml_empty_state))
          env [Log lop e1 e2] =
        (state_clock_fupd (combin_K ck) (state_refs_fupd (combin_K R1) ml_empty_state),Rval [v])`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "h1") ASSUME_TAC) THEN
  X_GEN_TAC `ck:num` THEN
  REMOVE_THEN "h1" (X_CHOOSE_TAC `c1:num` o SPEC `ck:num`) THEN
  EXISTS_TAC `c1:num` THEN REWRITE_TAC[evaluate_def] THEN TR2AUX_RED_TAC[HD]);;

let TR2AUX_EV_IF = prove
 (`!env e1 e2 e3 e R R1 R2 v1 v2.
     (!ck. ?ck1.
        evaluate (state_clock_fupd (combin_K ck1) (state_refs_fupd (combin_K R) ml_empty_state))
          env [e1] =
        (state_clock_fupd (combin_K ck) (state_refs_fupd (combin_K R1) ml_empty_state),Rval [v1])) /\
     do_if v1 e2 e3 = SOME e /\
     (!ck. ?ck1.
        evaluate (state_clock_fupd (combin_K ck1) (state_refs_fupd (combin_K R1) ml_empty_state))
          env [e] =
        (state_clock_fupd (combin_K ck) (state_refs_fupd (combin_K R2) ml_empty_state),Rval [v2])) ==>
     !ck. ?ck1.
        evaluate (state_clock_fupd (combin_K ck1) (state_refs_fupd (combin_K R) ml_empty_state))
          env [If e1 e2 e3] =
        (state_clock_fupd (combin_K ck) (state_refs_fupd (combin_K R2) ml_empty_state),Rval [v2])`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "h1") (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "h2"))) THEN
  X_GEN_TAC `ck:num` THEN
  REMOVE_THEN "h2" (X_CHOOSE_TAC `c2:num` o SPEC `ck:num`) THEN
  REMOVE_THEN "h1" (X_CHOOSE_TAC `c1:num` o SPEC `c2:num`) THEN
  EXISTS_TAC `c1:num` THEN REWRITE_TAC[evaluate_def] THEN TR2AUX_RED_TAC[HD]);;

let TR2AUX_Boolv_T_F = prove
 (`~(Boolv T = Boolv F) /\ ~(Boolv F = Boolv T)`,
  REWRITE_TAC[semanticPrimitivesProps_Boolv_11]);;

(* the second operand of a short-circuit operator, after the first one *)

let TR2AUX_Eval_Log = prove
 (`!env lop x1 x2 b1 P.
     ml_Eval env x1 (ml_BOOL b1) /\
     (do_log lop (Boolv b1) x2 = SOME (Val (Boolv b1)) ==> P (Boolv b1)) /\
     (!e. do_log lop (Boolv b1) x2 = SOME (Exp e) ==> e = x2 /\ ml_Eval env x2 P) /\
     (?r. do_log lop (Boolv b1) x2 = SOME r /\ (!v. r = Val v ==> v = Boolv b1)) ==>
     ml_Eval env (Log lop x1 x2) P`,
  REPEAT GEN_TAC THEN REWRITE_TAC[TR2AUX_Eval_any_clock; ml_BOOL_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "e1") (CONJUNCTS_THEN2 (LABEL_TAC "val")
    (CONJUNCTS_THEN2 (LABEL_TAC "exp") (X_CHOOSE_THEN `r:exp_or_val` STRIP_ASSUME_TAC)))) THEN
  X_GEN_TAC `refs:(v store_v)list` THEN
  REMOVE_THEN "e1" (X_CHOOSE_THEN `v1:v` (X_CHOOSE_THEN `r1:(v store_v)list`
    STRIP_ASSUME_TAC) o SPEC `refs:(v store_v)list`) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MP_TAC(ISPEC `r:exp_or_val` (cases "exp_or_val")) THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THENL
   [REMOVE_THEN "exp" (MP_TAC o SPEC `a:exp`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC (MP_TAC o SPEC `APPEND refs r1:(v store_v)list`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `v2:v` (X_CHOOSE_THEN `r2:(v store_v)list` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`v2:v`; `APPEND r1 r2:(v store_v)list`] THEN
    ASM_REWRITE_TAC[APPEND_ASSOC] THEN MATCH_MP_TAC TR2AUX_EV_LOG_EXP THEN
    MAP_EVERY EXISTS_TAC [`x2:exp`; `APPEND refs r1:(v store_v)list`; `Boolv b1`] THEN
    ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPEC `a:v`) THEN REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
    MAP_EVERY EXISTS_TAC [`Boolv b1`; `r1:(v store_v)list`] THEN
    REMOVE_THEN "val" MP_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC TR2AUX_EV_LOG_VAL THEN
    EXISTS_TAC `Boolv b1` THEN ASM_REWRITE_TAC[]]);;

let TR2AUX_ml_BOOL_Boolv = prove
 (`!b. ml_BOOL b (Boolv b)`,
  REWRITE_TAC[ml_BOOL_def]);;

let Eval_Or = prove
 (`(a1 ==> ml_Eval env x1 (ml_BOOL b1)) /\
   (a2 ==> ml_Eval env x2 (ml_BOOL b2))
   ==>
   (a1 /\ (~ml_CONTAINER b1 ==> a2) ==>
    ml_Eval env (Log Orelse x1 x2) (ml_BOOL (b1 \/ b2)))`,
  REWRITE_TAC[ml_CONTAINER_def] THEN BOOL_CASES_TAC `b1:bool` THEN
  REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC TR2AUX_Eval_Log THENL [EXISTS_TAC `T`; EXISTS_TAC `F`] THEN
  REWRITE_TAC[do_log_def; semanticPrimitivesProps_Boolv_11; distinctness "lop";
    injectivity "option"; injectivity "exp_or_val"; distinctness "exp_or_val";
    TR2AUX_ml_BOOL_Boolv; UNWIND_THM1] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN ASM_MESON_TAC[]);;

let Eval_And = prove
 (`(a1 ==> ml_Eval env x1 (ml_BOOL b1)) /\
   (a2 ==> ml_Eval env x2 (ml_BOOL b2))
   ==>
   (a1 /\ (ml_CONTAINER b1 ==> a2) ==>
    ml_Eval env (Log Andalso x1 x2) (ml_BOOL (b1 /\ b2)))`,
  REWRITE_TAC[ml_CONTAINER_def] THEN BOOL_CASES_TAC `b1:bool` THEN
  REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC TR2AUX_Eval_Log THENL [EXISTS_TAC `T`; EXISTS_TAC `F`] THEN
  REWRITE_TAC[do_log_def; semanticPrimitivesProps_Boolv_11; distinctness "lop";
    injectivity "option"; injectivity "exp_or_val"; distinctness "exp_or_val";
    TR2AUX_ml_BOOL_Boolv; UNWIND_THM1] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN ASM_MESON_TAC[]);;
let TR2AUX_Eval_If = prove
 (`!env x1 x2 x3 b1 P.
     ml_Eval env x1 (ml_BOOL b1) /\ ml_Eval env (if b1 then x2 else x3) P ==>
     ml_Eval env (If x1 x2 x3) P`,
  REPEAT GEN_TAC THEN REWRITE_TAC[TR2AUX_Eval_any_clock; ml_BOOL_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "e1") (LABEL_TAC "e2")) THEN
  X_GEN_TAC `refs:(v store_v)list` THEN
  REMOVE_THEN "e1" (X_CHOOSE_THEN `v1:v` (X_CHOOSE_THEN `r1:(v store_v)list`
    STRIP_ASSUME_TAC) o SPEC `refs:(v store_v)list`) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  REMOVE_THEN "e2" (X_CHOOSE_THEN `v2:v` (X_CHOOSE_THEN `r2:(v store_v)list`
    STRIP_ASSUME_TAC) o SPEC `APPEND refs r1:(v store_v)list`) THEN
  MAP_EVERY EXISTS_TAC [`v2:v`; `APPEND r1 r2:(v store_v)list`] THEN
  ASM_REWRITE_TAC[APPEND_ASSOC] THEN MATCH_MP_TAC TR2AUX_EV_IF THEN
  MAP_EVERY EXISTS_TAC [`if b1 then x2 else x3:exp`; `APPEND refs r1:(v store_v)list`;
    `Boolv b1`] THEN
  ASM_REWRITE_TAC[do_if_def; semanticPrimitivesProps_Boolv_11] THEN
  BOOL_CASES_TAC `b1:bool` THEN REWRITE_TAC[]);;

let Eval_If = prove
 (`(a1 ==> ml_Eval env x1 (ml_BOOL b1)) /\
   (a2 ==> ml_Eval env x2 (a b2)) /\
   (a3 ==> ml_Eval env x3 (a b3))
   ==>
   (a1 /\ (ml_CONTAINER b1 ==> a2) /\ (~ml_CONTAINER b1 ==> a3) ==>
    ml_Eval env (If x1 x2 x3) (a (if b1 then b2 else (b3:A))))`,
  REWRITE_TAC[ml_CONTAINER_def] THEN BOOL_CASES_TAC `b1:bool` THEN
  REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC TR2AUX_Eval_If THENL [EXISTS_TAC `T`; EXISTS_TAC `F`] THEN
  ASM_SIMP_TAC[]);;

let Eval_Bool_Not = prove
 (`ml_Eval env x1 (ml_BOOL b1) ==>
   ml_Eval env (App (Arith Not BoolT) [x1]) (ml_BOOL (~b1))`,
  DISCH_TAC THEN MATCH_MP_TAC TR2AUX_Eval_App1 THEN
  EXISTS_TAC `ml_BOOL b1` THEN ASM_REWRITE_TAC[getOpClass_def] THEN
  CAKE_REWRITE_TAC[] THEN REWRITE_TAC[ml_BOOL_def] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[do_app_def] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[ALL; check_type_def; semanticPrimitivesProps_Boolv_11; do_arith_def] THEN
  CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[EXCLUDED_MIDDLE; the_Boolv_def; semanticPrimitivesProps_Boolv_11] THEN
  MESON_TAC[]);;

let Eval_Implies = prove
 (`ml_Eval env x1 (ml_BOOL b1) ==>
   ml_Eval env x2 (ml_BOOL b2) ==>
   ml_Eval env (If x1 x2 (App (Test (Compare Leq) IntT) [Lit (IntLit (&0)); Lit (IntLit (&0))]))
     (ml_BOOL (b1 ==> b2))`,
  BOOL_CASES_TAC `b1:bool` THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC TR2AUX_Eval_If THENL [EXISTS_TAC `T`; EXISTS_TAC `F`] THEN
  ASM_REWRITE_TAC[Eval_Val_BOOL_T]);;

let Eval_BOOL_EQ = prove
 (`ml_Eval env x1 (ml_BOOL b1) ==>
   ml_Eval env x2 (ml_BOOL b2) ==>
   ml_Eval env (App (Test Equal BoolT) [x1; x2]) (ml_BOOL (b1 = b2))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC TR2AUX_Eval_App2 THEN
  MAP_EVERY EXISTS_TAC [`ml_BOOL b1`; `ml_BOOL b2`] THEN
  ASM_REWRITE_TAC[getOpClass_def] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[ml_BOOL_def] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[do_app_def] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[do_test_def; check_type_def; semanticPrimitivesProps_Boolv_11;
    distinctness "prim_type"] THEN
  CAKE_REWRITE_TAC[] THEN
  MAP_EVERY BOOL_CASES_TAC [`b1:bool`; `b2:bool`] THEN
  REWRITE_TAC[semanticPrimitives_Boolv_def; do_eq_def; LENGTH; ctor_same_type_def;
    same_type_def] THEN
  CAKE_REWRITE_TAC[same_type_def] THEN
  SIMP[injectivity "option"; injectivity "stamp"; injectivity "mlstring";
    semanticPrimitives_Boolv_def] THEN
  CAKE_REWRITE_TAC[] THEN MESON_TAC[]);;
(* misc *)

let Eval_Var_SIMP = prove
 (`ml_Eval (ml_write x v env) (Var (Short y)) p =
   if x = y then p v else ml_Eval env (Var (Short y)) p`,
  REWRITE_TAC[TR2AUX_Eval_Var_nsLookup; ml_write_def] THEN SIMP[] THEN
  COND_CASES_TAC THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[nsLookup_nsBind] THEN CAKE_REWRITE_TAC[];
    SUBGOAL_THEN `~(Short y = Short x:(mlstring,mlstring)id)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[injectivity "id"] THEN ASM_MESON_TAC[];
      ASM_SIMP_TAC[nsLookup_nsBind]]]);;

let Eval_Eq = prove
 (`ml_Eval env exp (a (x:A)) ==> ml_Eval env exp ((ml_Eq a x) x)`,
  REWRITE_TAC[ml_Eval_def; ml_Eq_def]);;

(* HOL4: FUN_FORALL and FUN_EXISTS, binders (new_binder_definition) *)

let FUN_FORALL = new_definition
  `FUN_FORALL = \(p:A->B->v->bool) a v. !y. p y a v`;;

let FUN_EXISTS = new_definition
  `FUN_EXISTS = \(p:A->B->v->bool) a v. ?y. p y a v`;;

parse_as_binder "FUN_FORALL";;
parse_as_binder "FUN_EXISTS";;

let FUN_FORALL_INTRO = prove
 (`(!x:A. p x (f:B) v) ==> (FUN_FORALL x. p x) f v`,
  REWRITE_TAC[FUN_FORALL; ETA_AX]);;

let eval_rel_11 = prove
 (`eval_rel (s1:(FFI)state) env e s2 x2 /\ eval_rel s1 env e s3 x3 ==>
   s2 = s3 /\ x2 = x3`,
  REWRITE_TAC[eval_rel_def] THEN STRIP_TAC THEN
  MP_TAC (ISPECL [`state_clock_fupd (combin_K ck1) (s1:(FFI)state)`; `env:v sem_env`; `[e:exp]`;
    `state_clock_fupd (combin_K ck2) (s2:(FFI)state)`; `Rval [x2:v]:(v list,v)result`; `ck1':num`]
    evaluate_add_to_clock) THEN
  MP_TAC (ISPECL [`state_clock_fupd (combin_K ck1') (s1:(FFI)state)`; `env:v sem_env`; `[e:exp]`;
    `state_clock_fupd (combin_K ck2') (s3:(FFI)state)`; `Rval [x3:v]:(v list,v)result`; `ck1:num`]
    evaluate_add_to_clock) THEN
  ASM_REWRITE_TAC[distinctness "result"] THEN SIMP[] THEN
  SUBST1_TAC (ARITH_RULE `ck1' + ck1 = ck1 + ck1':num`) THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[PAIR_EQ; injectivity "result"; CONS_11] THEN
  DISCH_THEN (CONJUNCTS_THEN2 (MP_TAC o REWRITE_RULE[state_component_equality]) ASSUME_TAC) THEN
  ASM_REWRITE_TAC[state_component_equality] THEN SIMP[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let Eval_FUN_FORALL = prove
 (`(!x:A. ml_Eval env exp ((p x) (f:B))) ==>
   ml_Eval env exp ((FUN_FORALL x. p x) f)`,
  REWRITE_TAC[ml_Eval_def; FUN_FORALL] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM (STRIP_ASSUME_TAC o SPECL [`ARB:A`; `refs:(v store_v)list`]) THEN
  MAP_EVERY EXISTS_TAC [`res:v`; `refs':(v store_v)list`] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y:A` THEN
  FIRST_X_ASSUM (STRIP_ASSUME_TAC o SPECL [`y:A`; `refs:(v store_v)list`]) THEN
  FIRST_X_ASSUM (MP_TAC o MATCH_MP eval_rel_11 o CONJ (ASSUME
    `eval_rel (state_refs_fupd (combin_K refs) ml_empty_state) env exp
       (state_refs_fupd (combin_K (APPEND refs refs')) ml_empty_state) res`)) THEN
  ASM_MESON_TAC[]);;

let Eval_FUN_FORALL_EQ = prove
 (`(!x:A. ml_Eval env exp ((p x) (f:B))) <=>
   ml_Eval env exp ((FUN_FORALL x. p x) f)`,
  EQ_TAC THEN REWRITE_TAC[Eval_FUN_FORALL] THEN
  REWRITE_TAC[ml_Eval_def; FUN_FORALL] THEN MESON_TAC[]);;

(* HOL4: the local FUN_FORALL_PUSH1, FUN_FORALL_PUSH2 and FUN_EXISTS_Eq   *)
(* (Q.prove values, GEN_ALL'd) of FUN_QUANT_SIMP                           *)

let TR2AUX_FUN_FORALL_PUSH1 = prove
 (`!(a:A->v->bool) (b:C->B->v->bool).
     (FUN_FORALL x. a --> (b x)) = (a --> FUN_FORALL x. b x)`,
  REWRITE_TAC[ml_Arrow_def; FUN_EQ_THM; ml_AppReturns_def; FUN_FORALL] THEN
  REPEAT GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL
  [ALL_TAC; ASM_MESON_TAC[]] THEN
  FIRST_ASSUM (MP_TAC o SPECL [`ARB:C`; `x'':A`; `v':v`] o
    REWRITE_RULE[RIGHT_IMP_FORALL_THM]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN (STRIP_ASSUME_TAC o SPEC `refs:(v store_v)list`) THEN
  MAP_EVERY EXISTS_TAC [`env:v sem_env`; `exp:exp`; `refs':(v store_v)list`; `u:v`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:C` THEN
  FIRST_X_ASSUM (MP_TAC o SPECL [`y:C`; `x'':A`; `v':v`] o
    REWRITE_RULE[RIGHT_IMP_FORALL_THM]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN (STRIP_ASSUME_TAC o SPEC `refs:(v store_v)list`) THEN
  QPAT_X_ASSUM "SOME _ = SOME _"
    (STRIP_ASSUME_TAC o REWRITE_RULE[injectivity "option"; PAIR_EQ]) THEN
  REPEAT (FIRST_X_ASSUM SUBST_ALL_TAC) THEN
  ASM_MESON_TAC[eval_rel_11]);;

let TR2AUX_FUN_FORALL_PUSH2 = prove
 (`!(a:C->A->v->bool) (b:B->v->bool).
     (FUN_FORALL x. (a x) --> b) = ((FUN_EXISTS x. a x) --> b)`,
  REWRITE_TAC[ml_Arrow_def; FUN_EQ_THM; ml_AppReturns_def; FUN_FORALL; FUN_EXISTS] THEN
  MESON_TAC[]);;

let TR2AUX_FUN_EXISTS_Eq = prove
 (`!a:A->v->bool. (FUN_EXISTS x. ml_Eq a x) = a`,
  REWRITE_TAC[FUN_EQ_THM; FUN_EXISTS; ml_Eq_def] THEN MESON_TAC[]);;

let FUN_QUANT_SIMP =
  CONJ TR2AUX_FUN_EXISTS_Eq (CONJ TR2AUX_FUN_FORALL_PUSH1 TR2AUX_FUN_FORALL_PUSH2);;
(* HOL4 writes MAP (\(f,x,e). f) funs; here as in do_opapp_def (a match) *)

let Eval_Recclosure_ALT = prove
 (CASE_TERM `!funs fname name body.
     ALL_DISTINCT (MAP (\fxe. match fxe with (f,x,e) -> f) funs) ==>
     (!v. a n v ==>
          ml_Eval (ml_write name v (ml_write_rec funs env2 env2)) body (b ((f:A->B) n))) ==>
     LOOKUP_VAR fname env (Recclosure env2 funs fname) ==>
     find_recfun fname funs = SOME (name,body) ==>
     ml_Eval env (Var (Short fname)) ((ml_Eq a n --> b) f)`,
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LOOKUP_VAR_def; ml_lookup_var_def]) THEN
  ASM_REWRITE_TAC[TR2AUX_Eval_Var_nsLookup] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[ml_Arrow_def; ml_AppReturns_def; ml_Eq_def] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `w:v`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  X_GEN_TAC `refs:(v store_v)list` THEN
  FIRST_X_ASSUM(fun th -> FIRST_ASSUM(MP_TAC o MATCH_MP th)) THEN
  REWRITE_TAC[ml_Eval_def] THEN DISCH_THEN(MP_TAC o SPEC `refs:(v store_v)list`) THEN
  STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`ml_write name w (ml_write_rec funs env2 env2)`; `body:exp`;
    `refs':(v store_v)list`; `res:v`] THEN
  ASM_REWRITE_TAC[do_opapp_def] THEN CAKE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  CAKE_REWRITE_TAC[] THEN REWRITE_TAC[write_rec_thm; ml_write_def] THEN SIMP[]);;

let Eval_Recclosure = prove
 (`(!v. a n v ==>
        ml_Eval (ml_write name v (ml_write_rec [(fname,name,body)] env2 env2))
          body (b ((f:A->B) n))) ==>
   LOOKUP_VAR fname env (Recclosure env2 [(fname,name,body)] fname) ==>
   ml_Eval env (Var (Short fname)) ((ml_Eq a n --> b) f)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC (REWRITE_RULE[IMP_IMP] (ISPECL
    [`[(fname,name,body):mlstring#mlstring#exp]`; `fname:mlstring`; `name:mlstring`;
     `body:exp`] Eval_Recclosure_ALT)) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[MAP; ALL_DISTINCT; MEM] THEN
  ONCE_REWRITE_TAC[find_recfun_def] THEN CAKE_REWRITE_TAC[]);;

let SafeVar_def = new_definition
  `SafeVar = Var`;;

let Eval_Eq_Recclosure = prove
 (`LOOKUP_VAR name env (Recclosure x1 x2 x3) ==>
   (P (f:A) (Recclosure x1 x2 x3) <=> ml_Eval env (Var (Short name)) (P f))`,
  REWRITE_TAC[LOOKUP_VAR_def; ml_lookup_var_def; TR2AUX_Eval_Var_nsLookup] THEN
  DISCH_THEN SUBST1_TAC THEN CAKE_REWRITE_TAC[]);;

let Eval_Eq_Fun = prove
 (`ml_Eval env (Fun v x) p ==>
   !env2. ml_Eval env2 (Var name) ((=) (Closure env v x)) ==>
          ml_Eval env2 (Var name) p`,
  REWRITE_TAC[TR2AUX_Eval_Fun_rw; TR2AUX_Eval_Var_nsLookup] THEN
  REPEAT STRIP_TAC THEN
  POP_ASSUM MP_TAC THEN CASES_ON `nsLookup (sem_env_v (env2:v sem_env)) name` THEN
  CAKE_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let Eval_WEAKEN = prove
 (`ml_Eval env exp P ==> (!v. P v ==> Q v) ==> ml_Eval env exp Q`,
  REWRITE_TAC[ml_Eval_def] THEN MESON_TAC[]);;

let Eval_CONST = prove
 (`(!v. P v <=> v = x) ==>
   ml_Eval env (Var name) ((=) x) ==> ml_Eval env (Var name) P`,
  REWRITE_TAC[ml_Eval_def] THEN MESON_TAC[]);;
(* arithmetic for integers *)

(* the side goal of TR2AUX_Eval_App1/2/3: unfold the invariants, substitute *)
(* the values, compute do_app and pick the result                          *)

let TR2AUX_DO_APP_TAC thl =
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[do_app_def] THEN CAKE_REWRITE_TAC[] THEN
  SIMP(thl @ [check_type_def; ALL; do_arith_def; do_test_def; do_conversion_def;
    MAP; dest_Litv_def; the_Litv_IntLit_def; int_cmp_def]) THEN
  SIMP(thl @ [injectivity "option"; PAIR_EQ; injectivity "result"; UNWIND_THM1]);;

let TR2AUX_INT_BINOP_TAC thl =
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ml_PRECONDITION_def]) THEN
  MATCH_MP_TAC TR2AUX_Eval_App2 THEN
  MAP_EVERY EXISTS_TAC [`ml_INT n1`; `ml_INT n2`] THEN
  ASM_REWRITE_TAC[getOpClass_def] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[ml_INT_def; ml_BOOL_def; ml_PRECONDITION_def] THEN
  TR2AUX_DO_APP_TAC thl;;

let Eval_INT_ADD = prove
 (`!n1 n2.
     ml_Eval env x1 (ml_INT n1) ==>
     ml_Eval env x2 (ml_INT n2) ==>
     ml_Eval env (App (Arith Add IntT) [x1; x2]) (ml_INT (n1 + n2))`,
  TR2AUX_INT_BINOP_TAC[]);;

let Eval_INT_SUB = prove
 (`!n1 n2.
     ml_Eval env x1 (ml_INT n1) ==>
     ml_Eval env x2 (ml_INT n2) ==>
     ml_Eval env (App (Arith Sub IntT) [x1; x2]) (ml_INT (n1 - n2))`,
  TR2AUX_INT_BINOP_TAC[]);;

let Eval_INT_MULT = prove
 (`!n1 n2.
     ml_Eval env x1 (ml_INT n1) ==>
     ml_Eval env x2 (ml_INT n2) ==>
     ml_Eval env (App (Arith Mul IntT) [x1; x2]) (ml_INT (n1 * n2))`,
  TR2AUX_INT_BINOP_TAC[]);;

(* HOL4 int / and % (floor division) are int_div and integer_int_mod *)

let Eval_INT_DIV = prove
 (`!n1 n2.
     ml_Eval env x1 (ml_INT n1) ==>
     ml_Eval env x2 (ml_INT n2) ==>
     ml_PRECONDITION (~(n2 = &0)) ==>
     ml_Eval env (App (Arith Div IntT) [x1; x2]) (ml_INT (int_div n1 n2))`,
  TR2AUX_INT_BINOP_TAC[]);;

let Eval_INT_MOD = prove
 (`!n1 n2.
     ml_Eval env x1 (ml_INT n1) ==>
     ml_Eval env x2 (ml_INT n2) ==>
     ml_PRECONDITION (~(n2 = &0)) ==>
     ml_Eval env (App (Arith Mod IntT) [x1; x2]) (ml_INT (integer_int_mod n1 n2))`,
  TR2AUX_INT_BINOP_TAC[]);;

(* HOL4 [local] *)

let Eval_INT_CMP = prove
 (`!f n1 n2.
     ml_Eval env x1 (ml_INT n1) ==>
     ml_Eval env x2 (ml_INT n2) ==>
     ml_Eval env (App (Test (Compare f) IntT) [x1;x2]) (ml_BOOL (int_cmp f n1 n2))`,
  TR2AUX_INT_BINOP_TAC[]);;

let Eval_INT_LESS = REWRITE_RULE[int_cmp_def] (SPEC `Lt` Eval_INT_CMP);;
let Eval_INT_LESS_EQ = REWRITE_RULE[int_cmp_def] (SPEC `Leq` Eval_INT_CMP);;
let Eval_INT_GREATER = REWRITE_RULE[int_cmp_def] (SPEC `Gt` Eval_INT_CMP);;
let Eval_INT_GREATER_EQ = REWRITE_RULE[int_cmp_def] (SPEC `Geq` Eval_INT_CMP);;
let Eval_INT_EQ = prove
 (`ml_Eval env x1 (ml_INT i1) ==>
   ml_Eval env x2 (ml_INT i2) ==>
   ml_Eval env (App (Test Equal IntT) [x1; x2]) (ml_BOOL (i1 = i2))`,
  REPEAT DISCH_TAC THEN MATCH_MP_TAC TR2AUX_Eval_App2 THEN
  MAP_EVERY EXISTS_TAC [`ml_INT i1`; `ml_INT i2`] THEN
  ASM_REWRITE_TAC[getOpClass_def] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[ml_INT_def; ml_BOOL_def] THEN
  TR2AUX_DO_APP_TAC[do_eq_def; lit_same_type_def; distinctness "prim_type";
    injectivity "lit"]);;

let Eval_NUM_EQ = prove
 (`ml_Eval env x1 (ml_NUM n1) ==>
   ml_Eval env x2 (ml_NUM n2) ==>
   ml_Eval env (App (Test Equal IntT) [x1; x2]) (ml_BOOL (n1 = n2))`,
  REWRITE_TAC[ml_NUM_def; GSYM INT_OF_NUM_EQ; Eval_INT_EQ]);;

(* HOL4 Num is num_of_int (equal on non-negative integers) *)

let Eval_Num = prove
 (`ml_Eval env x1 (ml_INT i) ==> ml_PRECONDITION (&0 <= i) ==>
   ml_Eval env x1 (ml_NUM (num_of_int i))`,
  REWRITE_TAC[ml_NUM_def; ml_PRECONDITION_def] THEN SIMP_TAC[INT_OF_NUM_OF_INT]);;

(* HOL4's MP_CANON (curried implications into one, free variables          *)
(* generalised), for MATCH_MP_TAC with the curried templates                *)

let TR2AUX_MP_CANON th = GEN_ALL (REWRITE_RULE[IMP_IMP] (GEN_ALL th));;

(* the variable k of a Let, read back *)

let TR2AUX_Eval_write_Var = prove
 (`!n v env P. P v ==> ml_Eval (ml_write n v env) (Var (Short n)) P`,
  REWRITE_TAC[Eval_Var_SIMP]);;

let Eval_Num_ABS = prove
 (`ml_Eval env x1 (ml_INT i) ==>
   ml_Eval env
     (Let (SOME (implode "k")) x1
        (If (App (Test (Compare Lt) IntT) [Var (Short (implode "k")); Lit (IntLit (&0))])
            (App (Arith Sub IntT) [Lit (IntLit (&0)); Var (Short (implode "k"))])
            (Var (Short (implode "k")))))
     (ml_NUM (num_of_int (abs i)))`,
  DISCH_TAC THEN
  SUBGOAL_THEN `ml_NUM (num_of_int (abs i)) =
                ml_INT (LET (\k. if k < &0 then &0 - k else k) i)` SUBST1_TAC THENL
   [REWRITE_TAC[ml_NUM_def; LET_DEF] THEN AP_TERM_TAC THEN
    SIMP_TAC[INT_OF_NUM_OF_INT; INT_ABS_POS] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC (GEN_ALL Eval_Let) THEN EXISTS_TAC `ml_INT` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `w:v` THEN DISCH_TAC THEN MATCH_MP_TAC TR2AUX_Eval_If THEN
  EXISTS_TAC `(i:int) < &0` THEN CONJ_TAC THENL
   [MATCH_MP_TAC (TR2AUX_MP_CANON Eval_INT_LESS) THEN
    ASM_SIMP_TAC[TR2AUX_Eval_write_Var; Eval_Val_INT];
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
     [MATCH_MP_TAC (TR2AUX_MP_CANON Eval_INT_SUB) THEN
      ASM_SIMP_TAC[TR2AUX_Eval_write_Var; Eval_Val_INT];
      ASM_SIMP_TAC[TR2AUX_Eval_write_Var]]]);;

(* HOL4: num_of_int (names.tsv ml_num_of_int; HOL Light has num_of_int) *)

let ml_num_of_int_def = cake_def
  `ml_num_of_int i = num_of_int (abs i)`;;

let num_of_int_num = prove
 (`ml_num_of_int (&n) = n /\ ml_num_of_int (-- &n) = n`,
  REWRITE_TAC[ml_num_of_int_def; INT_ABS_NEG; INT_ABS_NUM; NUM_OF_INT_OF_NUM]);;
let _ = cake_add_simps [num_of_int_num];;

let ml_Eval_num_of_int = REWRITE_RULE[GSYM ml_num_of_int_def] Eval_Num_ABS;;

(* HOL4 int_of_num n is &n *)

let ml_Eval_int_of_num = prove
 (`ml_Eval env x1 (ml_NUM n) ==> ml_Eval env x1 (ml_INT (&n))`,
  REWRITE_TAC[ml_NUM_def]);;

let ml_Eval_int_of_num_o = prove
 (`ml_Eval env x1 ((A --> ml_NUM) f) ==>
   ml_Eval env x1 ((A --> ml_INT) ((int_of_num o f):B->int))`,
  REWRITE_TAC[ml_NUM_def; ml_Arrow_def; o_THM] THEN REWRITE_TAC[GSYM ml_NUM_def]);;

let ml_Eval_o_int_of_num = prove
 (`ml_Eval env x1 ((ml_INT --> A) f) ==>
   ml_Eval env x1 ((ml_NUM --> A) ((f o int_of_num):num->B))`,
  REWRITE_TAC[ml_NUM_def; ml_Arrow_def; ml_Eval_def; o_THM] THEN MESON_TAC[]);;

let ml_Eval_int_negate = prove
 (`ml_Eval env x1 (ml_INT i) ==>
   ml_Eval env (App (Arith Sub IntT) [Lit (IntLit (&0)); x1]) (ml_INT (--i))`,
  DISCH_TAC THEN REWRITE_TAC[INT_ARITH `--(i:int) = &0 - i`] THEN
  MATCH_MP_TAC (TR2AUX_MP_CANON Eval_INT_SUB) THEN ASM_REWRITE_TAC[Eval_Val_INT]);;
(* arithmetic for num *)

let Eval_NUM_SUB = prove
 (`ml_Eval env x1 (ml_NUM n) ==>
   ml_Eval env x2 (ml_NUM m) ==>
   ml_PRECONDITION (m <= n) ==>
   ml_Eval env (App (Arith Sub IntT) [x1; x2]) (ml_NUM (n - m))`,
  REWRITE_TAC[ml_NUM_def; ml_PRECONDITION_def] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB] THEN
  MATCH_MP_TAC (TR2AUX_MP_CANON Eval_INT_SUB) THEN ASM_REWRITE_TAC[]);;

let Eval_NUM_ADD = prove
 (`ml_Eval env x1 (ml_NUM n1) ==>
   ml_Eval env x2 (ml_NUM n2) ==>
   ml_Eval env (App (Arith Add IntT) [x1; x2]) (ml_NUM (n1 + n2))`,
  REWRITE_TAC[ml_NUM_def; GSYM INT_OF_NUM_ADD; Eval_INT_ADD]);;

let Eval_NUM_MULT = prove
 (`ml_Eval env x1 (ml_NUM n1) ==>
   ml_Eval env x2 (ml_NUM n2) ==>
   ml_Eval env (App (Arith Mul IntT) [x1; x2]) (ml_NUM (n1 * n2))`,
  REWRITE_TAC[ml_NUM_def; GSYM INT_OF_NUM_MUL; Eval_INT_MULT]);;

let Eval_NUM_DIV = prove
 (`ml_Eval env x1 (ml_NUM n1) ==>
   ml_Eval env x2 (ml_NUM n2) ==>
   ml_PRECONDITION (~(n2 = 0)) ==>
   ml_Eval env (App (Arith Div IntT) [x1; x2]) (ml_NUM (n1 DIV n2))`,
  REWRITE_TAC[ml_NUM_def; ml_PRECONDITION_def] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[GSYM INT_DIV] THEN
  MATCH_MP_TAC (TR2AUX_MP_CANON Eval_INT_DIV) THEN
  ASM_REWRITE_TAC[ml_PRECONDITION_def; INT_OF_NUM_EQ]);;

let Eval_NUM_MOD = prove
 (`ml_Eval env x1 (ml_NUM n1) ==>
   ml_Eval env x2 (ml_NUM n2) ==>
   ml_PRECONDITION (~(n2 = 0)) ==>
   ml_Eval env (App (Arith Mod IntT) [x1; x2]) (ml_NUM (n1 MOD n2))`,
  REWRITE_TAC[ml_NUM_def; ml_PRECONDITION_def] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[GSYM INT_MOD] THEN
  MATCH_MP_TAC (TR2AUX_MP_CANON Eval_INT_MOD) THEN
  ASM_REWRITE_TAC[ml_PRECONDITION_def; INT_OF_NUM_EQ]);;

let TR2AUX_num_sub_int = prove
 (`!m n. &(m - n):int = if (&m - &n:int) < &0 then &0 else &m - &n`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n <= m:num` THENL
   [ASM_SIMP_TAC[INT_OF_NUM_SUB] THEN REWRITE_TAC[INT_ARITH `~(&a:int < &0)`];
    SUBGOAL_THEN `m - n = 0` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(&m - &n:int) < &0` (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[INT_ARITH `(&m - &n:int) < &0 <=> (&m:int) < &n`; INT_OF_NUM_LT] THEN
    ASM_ARITH_TAC]);;

let sub_check_def = cake_def
  `sub_check (n:num) m = n - m`;;

let Eval_NUM_SUB_check = prove
 (`ml_Eval env x1 (ml_NUM m) ==>
   ml_Eval env x2 (ml_NUM n) ==>
   ml_Eval env
     (Let (SOME (implode "k")) (App (Arith Sub IntT) [x1; x2])
        (If (App (Test (Compare Lt) IntT) [Var (Short (implode "k")); Lit (IntLit (&0))])
            (Lit (IntLit (&0))) (Var (Short (implode "k")))))
     (ml_NUM (sub_check m n))`,
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `ml_NUM (sub_check m n) =
                ml_INT (LET (\k. if k < &0 then &0 else k) (&m - &n))` SUBST1_TAC THENL
   [REWRITE_TAC[ml_NUM_def; LET_DEF; sub_check_def; TR2AUX_num_sub_int];
    ALL_TAC] THEN
  MATCH_MP_TAC (GEN_ALL Eval_Let) THEN EXISTS_TAC `ml_INT` THEN CONJ_TAC THENL
   [MATCH_MP_TAC (TR2AUX_MP_CANON Eval_INT_SUB) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ml_NUM_def]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `w:v` THEN DISCH_TAC THEN MATCH_MP_TAC TR2AUX_Eval_If THEN
  EXISTS_TAC `(&m - &n:int) < &0` THEN CONJ_TAC THENL
   [MATCH_MP_TAC (TR2AUX_MP_CANON Eval_INT_LESS) THEN
    ASM_SIMP_TAC[TR2AUX_Eval_write_Var; Eval_Val_INT];
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[TR2AUX_Eval_write_Var; Eval_Val_INT]]);;

let Eval_NUM_SUB_check' = prove
 (`ml_Eval env x1 (ml_NUM m) ==>
   ml_Eval env x2 (ml_NUM n) ==>
   ml_Eval env
     (Let (SOME (implode "k")) (App (Arith Sub IntT) [x1; x2])
        (If (App (Test (Compare Lt) IntT) [Var (Short (implode "k")); Lit (IntLit (&0))])
            (Lit (IntLit (&0))) (Var (Short (implode "k")))))
     (ml_NUM (m - n))`,
  REWRITE_TAC[GSYM sub_check_def; Eval_NUM_SUB_check]);;

let Eval_NUM_LESS = REWRITE_RULE[GSYM ml_NUM_def; INT_OF_NUM_LT; INT_OF_NUM_LE; INT_GE; INT_GT]
  (ISPECL [`&n1:int`; `&n2:int`] Eval_INT_LESS);;

let Eval_NUM_LESS_EQ = REWRITE_RULE[GSYM ml_NUM_def; INT_OF_NUM_LT; INT_OF_NUM_LE; INT_GE; INT_GT]
  (ISPECL [`&n1:int`; `&n2:int`] Eval_INT_LESS_EQ);;

let Eval_NUM_GREATER = REWRITE_RULE[GSYM GT]
  (REWRITE_RULE[GSYM ml_NUM_def; INT_OF_NUM_LT; INT_OF_NUM_LE; INT_GE; INT_GT]
    (ISPECL [`&n1:int`; `&n2:int`] Eval_INT_GREATER));;

let Eval_NUM_GREATER_EQ = REWRITE_RULE[GSYM GE]
  (REWRITE_RULE[GSYM ml_NUM_def; INT_OF_NUM_LT; INT_OF_NUM_LE; INT_GE; INT_GT]
    (ISPECL [`&n1:int`; `&n2:int`] Eval_INT_GREATER_EQ));;

let Eval_NUM_EQ_0 = prove
 (`!n. ml_Eval env x (ml_NUM n) ==>
       ml_Eval env (App (Test Equal IntT) [x; Lit (IntLit (&0))]) (ml_BOOL (n = 0))`,
  REWRITE_TAC[GSYM INT_OF_NUM_EQ; ml_NUM_def] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC (TR2AUX_MP_CANON Eval_INT_EQ) THEN ASM_REWRITE_TAC[Eval_Val_INT]);;
(* word operations *)

(* ml_WORD represents a word of A bits by its bits moved to the top of a    *)
(* byte or a 64-bit word: F w = word_shl (word_zx w) (M - dimindex(:A)),    *)
(* M = dimindex(:B).  Helpers of the port about F.                          *)

let TR2AUX_EXP_SPLIT = prove
 (`!d m. d <= m ==> 2 EXP m = 2 EXP (m - d) * 2 EXP d`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

let TR2AUX_VAL_WSHZX = prove
 (`!w:A word. dimindex(:A) <= dimindex(:B) ==>
     val (word_shl (word_zx w:B word) (dimindex(:B) - dimindex(:A))) =
     2 EXP (dimindex(:B) - dimindex(:A)) * val w`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_SHL; VAL_WORD_ZX_GEN] THEN
  SUBGOAL_THEN `val (w:A word) MOD 2 EXP dimindex(:B) = val w` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN TRANS_TAC LTE_TRANS `2 EXP dimindex(:A)` THEN
    ASM_REWRITE_TAC[VAL_BOUND; LE_EXP] THEN ARITH_TAC;
    MATCH_MP_TAC MOD_LT THEN
    FIRST_ASSUM(SUBST1_TAC o MATCH_MP TR2AUX_EXP_SPLIT) THEN
    REWRITE_TAC[LT_MULT_LCANCEL; VAL_BOUND; EXP_EQ_0] THEN ARITH_TAC]);;

let TR2AUX_WSHZX_ADD = prove
 (`!w1 w2:A word. dimindex(:A) <= dimindex(:B) ==>
     word_shl (word_zx (word_add w1 w2):B word) (dimindex(:B) - dimindex(:A)) =
     word_add (word_shl (word_zx w1:B word) (dimindex(:B) - dimindex(:A)))
              (word_shl (word_zx w2:B word) (dimindex(:B) - dimindex(:A)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM VAL_EQ] THEN
  ASM_SIMP_TAC[TR2AUX_VAL_WSHZX; VAL_WORD_ADD] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP TR2AUX_EXP_SPLIT) THEN
  REWRITE_TAC[GSYM LEFT_ADD_DISTRIB; MOD_MULT2]);;

let TR2AUX_WSHZX_SUB = prove
 (`!w1 w2:A word. dimindex(:A) <= dimindex(:B) ==>
     word_shl (word_zx (word_sub w1 w2):B word) (dimindex(:B) - dimindex(:A)) =
     word_sub (word_shl (word_zx w1:B word) (dimindex(:B) - dimindex(:A)))
              (word_shl (word_zx w2:B word) (dimindex(:B) - dimindex(:A)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`word_sub w1 w2:A word`; `w2:A word`] TR2AUX_WSHZX_ADD) THEN
  ASM_REWRITE_TAC[WORD_RULE `word_add (word_sub (x:A word) y) y = x`] THEN
  DISCH_THEN SUBST1_TAC THEN CONV_TAC WORD_RULE);;

let TR2AUX_WSHZX_BIT = prove
 (`!(w:A word) i. dimindex(:A) <= dimindex(:B) ==>
     (bit i (word_shl (word_zx w:B word) (dimindex(:B) - dimindex(:A))) <=>
      dimindex(:B) - dimindex(:A) <= i /\ i < dimindex(:B) /\
      bit (i - (dimindex(:B) - dimindex(:A))) w)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[BIT_WORD_SHL; BIT_WORD_ZX] THEN
  ASM_CASES_TAC `i < dimindex(:B)` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `i - (dimindex(:B) - dimindex(:A)) < dimindex(:B)` (fun th -> REWRITE_TAC[th]) THEN
  ASM_ARITH_TAC);;

let TR2AUX_WSHZX_BITWISE = prove
 (`!w1 w2:A word. dimindex(:A) <= dimindex(:B) ==>
     word_shl (word_zx (word_and w1 w2):B word) (dimindex(:B) - dimindex(:A)) =
     word_and (word_shl (word_zx w1:B word) (dimindex(:B) - dimindex(:A)))
              (word_shl (word_zx w2:B word) (dimindex(:B) - dimindex(:A))) /\
     word_shl (word_zx (word_or w1 w2):B word) (dimindex(:B) - dimindex(:A)) =
     word_or (word_shl (word_zx w1:B word) (dimindex(:B) - dimindex(:A)))
             (word_shl (word_zx w2:B word) (dimindex(:B) - dimindex(:A))) /\
     word_shl (word_zx (word_xor w1 w2):B word) (dimindex(:B) - dimindex(:A)) =
     word_xor (word_shl (word_zx w1:B word) (dimindex(:B) - dimindex(:A)))
              (word_shl (word_zx w2:B word) (dimindex(:B) - dimindex(:A)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
  ASM_SIMP_TAC[TR2AUX_WSHZX_BIT; BIT_WORD_AND_ALT; BIT_WORD_OR_ALT; BIT_WORD_XOR_ALT] THEN
  REPEAT STRIP_TAC THEN CONV_TAC TAUT);;

let TR2AUX_WSHZX_8,TR2AUX_WSHZX_64 =
  let thl = [TR2AUX_VAL_WSHZX; TR2AUX_WSHZX_ADD; TR2AUX_WSHZX_SUB; TR2AUX_WSHZX_BITWISE;
             TR2AUX_WORD_SHL_ZX_11] in
  let mk ty dth = end_itlist CONJ
    (map (REWRITE_RULE[dth] o INST_TYPE [ty,`:B`]) thl) in
  mk `:8` DIMINDEX_8, mk `:64` DIMINDEX_64;;

(* HOL4: the local tac of the word operations *)

let TR2AUX_WORD_BINOP_TAC =
  STRIP_TAC THEN MATCH_MP_TAC TR2AUX_Eval_App2 THEN
  MAP_EVERY EXISTS_TAC [`ml_WORD (w1:A word)`; `ml_WORD (w2:A word)`] THEN
  ASM_REWRITE_TAC[getOpClass_def] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[ml_WORD_def] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[do_app_def] THEN CAKE_REWRITE_TAC[] THEN
  SIMP[check_type_def; ALL; do_arith_def; MAP; the_Litv_Word8_def; the_Litv_Word64_def] THEN
  ASM_SIMP_TAC[TR2AUX_WSHZX_8; TR2AUX_WSHZX_64;
    injectivity "option"; PAIR_EQ; injectivity "result"; UNWIND_THM1];;

let ml_Eval_word_and = prove
 (`ml_Eval env x1 (ml_WORD (w1:A word)) /\
   ml_Eval env x2 (ml_WORD (w2:A word)) ==>
   ml_Eval env
     (App (Arith And (if dimindex (:A) <= 8 then WordT W8 else WordT W64)) [x1;x2])
     (ml_WORD (word_and w1 w2))`,
  TR2AUX_WORD_BINOP_TAC);;

let ml_Eval_word_or = prove
 (`ml_Eval env x1 (ml_WORD (w1:A word)) /\
   ml_Eval env x2 (ml_WORD (w2:A word)) ==>
   ml_Eval env
     (App (Arith Or (if dimindex (:A) <= 8 then WordT W8 else WordT W64)) [x1;x2])
     (ml_WORD (word_or w1 w2))`,
  TR2AUX_WORD_BINOP_TAC);;

let ml_Eval_word_xor = prove
 (`ml_Eval env x1 (ml_WORD (w1:A word)) /\
   ml_Eval env x2 (ml_WORD (w2:A word)) ==>
   ml_Eval env
     (App (Arith Xor (if dimindex (:A) <= 8 then WordT W8 else WordT W64)) [x1;x2])
     (ml_WORD (word_xor w1 w2))`,
  TR2AUX_WORD_BINOP_TAC);;

(* HOL4 [local] *)

let DISTRIB_ANY = prove
 (`(p * m + p * n = p * (m + n)) /\
   (p * m + n * p = p * (m + n)) /\
   (m * p + p * n = p * (m + n)) /\
   (m * p + n * p = p * (m + n:num)) /\
   (p * m - p * n = p * (m - n)) /\
   (p * m - n * p = p * (m - n)) /\
   (m * p - p * n = p * (m - n)) /\
   (m * p - n * p = p * (m - n:num))`,
  MESON_TAC[LEFT_ADD_DISTRIB; LEFT_SUB_DISTRIB; MULT_SYM]);;

(* HOL4 [local] *)

let MOD_COMMON_FACTOR_ANY = prove
 (`!n p q. 0 < n /\ 0 < q ==>
     ((n * p) MOD (n * q) = n * (p MOD q)) /\
     ((p * n) MOD (n * q) = n * (p MOD q)) /\
     ((n * p) MOD (q * n) = n * (p MOD q)) /\
     ((p * n) MOD (q * n) = n * (p MOD q))`,
  MESON_TAC[MOD_MULT2; MULT_SYM]);;

(* HOL4 [local] *)

let ml_Eval_word_add_lemma = prove
 (`dimindex (:A) <= k ==>
   (2 EXP (k - dimindex (:A)) * (q MOD dimword (:A))) MOD 2 EXP k =
   (2 EXP (k - dimindex (:A)) * q) MOD 2 EXP k`,
  DISCH_THEN(SUBST1_TAC o MATCH_MP TR2AUX_EXP_SPLIT) THEN
  REWRITE_TAC[dimword_def; MOD_MULT2; MOD_MOD_REFL]);;

let ml_Eval_word_add = prove
 (`ml_Eval env x1 (ml_WORD (w1:A word)) /\
   ml_Eval env x2 (ml_WORD (w2:A word)) ==>
   ml_Eval env
     (App (Arith Add (if dimindex (:A) <= 8 then WordT W8 else WordT W64)) [x1;x2])
     (ml_WORD (word_add w1 w2))`,
  TR2AUX_WORD_BINOP_TAC);;

(* HOL4 [local] *)

let ml_Eval_word_sub_lemma = prove
 (`dimindex (:A) <= k /\ n' < dimword (:A) ==>
   (n * 2 EXP (k - dimindex (:A)) +
    (2 EXP k - (n' * 2 EXP (k - dimindex (:A))) MOD 2 EXP k) MOD 2 EXP k) MOD 2 EXP k =
   (((n + dimword (:A)) - n') * 2 EXP (k - dimindex (:A))) MOD 2 EXP k`,
  REWRITE_TAC[dimword_def] THEN STRIP_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP TR2AUX_EXP_SPLIT) THEN
  ABBREV_TAC `K' = 2 EXP (k - dimindex(:A))` THEN
  ABBREV_TAC `D = 2 EXP dimindex(:A)` THEN
  SUBGOAL_THEN `~(K' = 0) /\ ~(D = 0)` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["K'"; "D"] THEN REWRITE_TAC[EXP_EQ_0] THEN ARITH_TAC; ALL_TAC] THEN
  SUBST1_TAC(ARITH_RULE `n * K' = K' * n:num`) THEN
  SUBST1_TAC(ARITH_RULE `n' * K' = K' * n':num`) THEN
  SUBST1_TAC(ARITH_RULE `((n + D) - n') * K' = K' * ((n + D) - n'):num`) THEN
  ASM_SIMP_TAC[MOD_MULT2; MOD_LT] THEN
  REWRITE_TAC[GSYM LEFT_SUB_DISTRIB; MOD_MULT2; GSYM LEFT_ADD_DISTRIB] THEN
  AP_TERM_TAC THEN
  SUBGOAL_THEN `(n + D) - n' = n + (D - n')` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN REWRITE_TAC[MOD_MOD_REFL]);;

let ml_Eval_word_sub = prove
 (`ml_Eval env x1 (ml_WORD (w1:A word)) /\
   ml_Eval env x2 (ml_WORD (w2:A word)) ==>
   ml_Eval env
     (App (Arith Sub (if dimindex (:A) <= 8 then WordT W8 else WordT W64)) [x1;x2])
     (ml_WORD (word_sub w1 w2))`,
  TR2AUX_WORD_BINOP_TAC);;

let ml_Eval_word_eq = prove
 (`ml_Eval env x1 (ml_WORD (w1:A word)) /\
   ml_Eval env x2 (ml_WORD (w2:A word)) ==>
   ml_Eval env
     (App (Test Equal (WordT (if dimindex (:A) <= 8 then W8 else W64))) [x1;x2])
     (ml_BOOL (w1 = w2))`,
  STRIP_TAC THEN MATCH_MP_TAC TR2AUX_Eval_App2 THEN
  MAP_EVERY EXISTS_TAC [`ml_WORD (w1:A word)`; `ml_WORD (w2:A word)`] THEN
  ASM_REWRITE_TAC[getOpClass_def] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[ml_WORD_def; ml_BOOL_def] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[do_app_def] THEN CAKE_REWRITE_TAC[] THEN
  SIMP[do_test_def; check_type_def; do_eq_def; lit_same_type_def; distinctness "prim_type";
    injectivity "lit"] THEN
  ASM_SIMP_TAC[TR2AUX_WSHZX_8; TR2AUX_WSHZX_64;
    injectivity "option"; PAIR_EQ; injectivity "result"; UNWIND_THM1]);;

(* HOL4 [local] *)

let less_two_pow_lemma = prove
 (`(n:num) < 2 EXP k /\ k <= d ==> n * 2 EXP (d - k) < 2 EXP d`,
  STRIP_TAC THEN FIRST_ASSUM(SUBST1_TAC o MATCH_MP TR2AUX_EXP_SPLIT) THEN
  SUBST1_TAC(ARITH_RULE `n * 2 EXP (d - k) = 2 EXP (d - k) * n`) THEN
  ASM_REWRITE_TAC[LT_MULT_LCANCEL; EXP_EQ_0] THEN ARITH_TAC);;

(* a 64-bit word value converted to an integer *)

let TR2AUX_Eval_w64_to_int = prove
 (`!env x w:A word.
     ml_Eval env x (ml_WORD w) /\ ~(dimindex(:A) <= 8) ==>
     ml_Eval env (App (FromTo (WordT W64) IntT) [x])
       (ml_INT (&(val (word_shl (word_zx w:int64) (64 - dimindex(:A))))))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC TR2AUX_Eval_App1 THEN
  EXISTS_TAC `ml_WORD (w:A word)` THEN ASM_REWRITE_TAC[getOpClass_def] THEN
  CAKE_REWRITE_TAC[] THEN REWRITE_TAC[ml_WORD_def; ml_INT_def] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[do_app_def] THEN CAKE_REWRITE_TAC[] THEN
  SIMP[check_type_def; do_conversion_def; the_Litv_Word64_def] THEN
  SIMP[injectivity "option"; PAIR_EQ; injectivity "result"; UNWIND_THM1]);;

let TR2AUX_Eval_WORD_dimindex = prove
 (`!env x w:A word. ml_Eval env x (ml_WORD w) ==> dimindex(:A) <= 64`,
  REWRITE_TAC[ml_Eval_def; ml_WORD_def] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o SPEC `[]:(v store_v)list`) THEN MESON_TAC[]);;

let TR2AUX_WORD_CMP_TAC =
  STRIP_TAC THEN COND_CASES_TAC THENL
   [MATCH_MP_TAC TR2AUX_Eval_App2 THEN
    MAP_EVERY EXISTS_TAC [`ml_WORD (w1:A word)`; `ml_WORD (w2:A word)`] THEN
    ASM_REWRITE_TAC[getOpClass_def] THEN CAKE_REWRITE_TAC[] THEN
    REWRITE_TAC[ml_WORD_def; ml_BOOL_def] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[do_app_def] THEN CAKE_REWRITE_TAC[] THEN
    SIMP[do_test_def; dest_Litv_def; num_cmp_def] THEN
    ASM_SIMP_TAC[TR2AUX_WSHZX_8; LT_MULT_LCANCEL; LE_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ;
      WORD_ULT; WORD_ULE; WORD_UGT; WORD_UGE; GT; GE;
      injectivity "option"; PAIR_EQ; injectivity "result"; UNWIND_THM1];
    MATCH_MP_TAC TR2AUX_Eval_App2 THEN
    MAP_EVERY EXISTS_TAC
     [`ml_INT (&(val (word_shl (word_zx (w1:A word):int64) (64 - dimindex(:A)))))`;
      `ml_INT (&(val (word_shl (word_zx (w2:A word):int64) (64 - dimindex(:A)))))`] THEN
    ASM_SIMP_TAC[TR2AUX_Eval_w64_to_int; getOpClass_def] THEN CAKE_REWRITE_TAC[] THEN
    REWRITE_TAC[ml_INT_def; ml_BOOL_def] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[do_app_def] THEN CAKE_REWRITE_TAC[] THEN
    SIMP[do_test_def; dest_Litv_def; int_cmp_def; INT_OF_NUM_LT; INT_OF_NUM_LE] THEN
    SUBGOAL_THEN `dimindex(:A) <= 64` ASSUME_TAC THENL
     [ASM_MESON_TAC[TR2AUX_Eval_WORD_dimindex]; ALL_TAC] THEN
    ASM_SIMP_TAC[TR2AUX_WSHZX_64; LT_MULT_LCANCEL; LE_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ;
      WORD_ULT; WORD_ULE; WORD_UGT; WORD_UGE; GT; GE;
      injectivity "option"; PAIR_EQ; injectivity "result"; UNWIND_THM1]];;

let ml_Eval_word_lo = prove
 (`ml_Eval env x1 (ml_WORD (w1:A word)) /\
   ml_Eval env x2 (ml_WORD (w2:A word)) ==>
   ml_Eval env
     (if dimindex (:A) <= 8 then
        App (Test (Compare Lt) (WordT W8)) [x1;x2]
      else
        App (Test (Compare Lt) IntT) [App (FromTo (WordT W64) IntT) [x1];
                                      App (FromTo (WordT W64) IntT) [x2]])
     (ml_BOOL (word_ult w1 w2))`,
  TR2AUX_WORD_CMP_TAC);;

let ml_Eval_word_ls = prove
 (`ml_Eval env x1 (ml_WORD (w1:A word)) /\
   ml_Eval env x2 (ml_WORD (w2:A word)) ==>
   ml_Eval env
     (if dimindex (:A) <= 8 then
        App (Test (Compare Leq) (WordT W8)) [x1;x2]
      else
        App (Test (Compare Leq) IntT) [App (FromTo (WordT W64) IntT) [x1];
                                       App (FromTo (WordT W64) IntT) [x2]])
     (ml_BOOL (word_ule w1 w2))`,
  TR2AUX_WORD_CMP_TAC);;

let TR2AUX_word_higher = prove
 (`!w1 w2:A word. (word_ugt w1 w2 <=> word_ult w2 w1) /\
                  (word_uge w1 w2 <=> word_ule w2 w1)`,
  REWRITE_TAC[WORD_ULT; WORD_ULE; WORD_UGT; WORD_UGE; GT; GE]);;

let ml_Eval_word_hi =
  ONCE_REWRITE_RULE[CONJ_COMM]
   (INST [`x2:exp`,`x1:exp`; `x1:exp`,`x2:exp`; `w2:A word`,`w1:A word`;
          `w1:A word`,`w2:A word`]
     (REWRITE_RULE[GSYM TR2AUX_word_higher] ml_Eval_word_lo));;

let ml_Eval_word_hs =
  ONCE_REWRITE_RULE[CONJ_COMM]
   (INST [`x2:exp`,`x1:exp`; `x1:exp`,`x2:exp`; `w2:A word`,`w1:A word`;
          `w1:A word`,`w2:A word`]
     (REWRITE_RULE[GSYM TR2AUX_word_higher] ml_Eval_word_ls));;
(* HOL4 [local] w2n_w2w_8, w2n_w2w_64 *)

let w2n_w2w_8 = prove
 (`dimindex (:A) < 8 ==>
   val (word_ushr (word_shl (word_zx (w:A word):byte) (8 - dimindex (:A)))
                  (8 - dimindex (:A))) = val w`,
  DISCH_TAC THEN REWRITE_TAC[VAL_WORD_USHR] THEN
  MP_TAC(ISPEC `w:A word` (INST_TYPE [`:8`,`:B`] TR2AUX_VAL_WSHZX)) THEN
  REWRITE_TAC[DIMINDEX_8] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN SIMP_TAC[DIV_MULT; EXP_EQ_0; ARITH_EQ]);;

let w2n_w2w_64 = prove
 (`dimindex (:A) < 64 ==>
   val (word_ushr (word_shl (word_zx (w:A word):int64) (64 - dimindex (:A)))
                  (64 - dimindex (:A))) = val w`,
  DISCH_TAC THEN REWRITE_TAC[VAL_WORD_USHR] THEN
  MP_TAC(ISPEC `w:A word` (INST_TYPE [`:64`,`:B`] TR2AUX_VAL_WSHZX)) THEN
  REWRITE_TAC[DIMINDEX_64] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN SIMP_TAC[DIV_MULT; EXP_EQ_0; ARITH_EQ]);;

(* evaluation steps on word and integer values *)

let TR2AUX_EV_SHIFT8 = prove
 (`!env x sh n a.
     ml_Eval env x (\v. v = Litv (Word8 a)) ==>
     ml_Eval env (App (Shift W8 sh n) [x]) (\v. v = Litv (Word8 (shift8_lookup sh a n)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC TR2AUX_Eval_App1 THEN
  EXISTS_TAC `\v:v. v = Litv (Word8 a)` THEN ASM_REWRITE_TAC[getOpClass_def] THEN
  CAKE_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[do_app_def] THEN CAKE_REWRITE_TAC[] THEN
  SIMP[injectivity "option"; PAIR_EQ; injectivity "result"; UNWIND_THM1]);;

let TR2AUX_EV_SHIFT64 = prove
 (`!env x sh n a.
     ml_Eval env x (\v. v = Litv (Word64 a)) ==>
     ml_Eval env (App (Shift W64 sh n) [x]) (\v. v = Litv (Word64 (shift64_lookup sh a n)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC TR2AUX_Eval_App1 THEN
  EXISTS_TAC `\v:v. v = Litv (Word64 a)` THEN ASM_REWRITE_TAC[getOpClass_def] THEN
  CAKE_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[do_app_def] THEN CAKE_REWRITE_TAC[] THEN
  SIMP[injectivity "option"; PAIR_EQ; injectivity "result"; UNWIND_THM1]);;

let TR2AUX_EV_FROMTO = prove
 (`!env x ty1 ty2 a r.
     ml_Eval env x (\v. v = a) /\ check_type ty1 a /\
     do_conversion a ty1 ty2 = SOME (INR r) ==>
     ml_Eval env (App (FromTo ty1 ty2) [x]) (\v. v = r)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC TR2AUX_Eval_App1 THEN
  EXISTS_TAC `\v:v. v = a` THEN ASM_REWRITE_TAC[getOpClass_def] THEN
  CAKE_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[do_app_def] THEN CAKE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  CAKE_REWRITE_TAC[] THEN
  SIMP[injectivity "option"; PAIR_EQ; injectivity "result"; UNWIND_THM1]);;

let TR2AUX_EV_W8_INT = prove
 (`!env x a. ml_Eval env x (\v. v = Litv (Word8 a)) ==>
     ml_Eval env (App (FromTo (WordT W8) IntT) [x]) (\v. v = Litv (IntLit (&(val a))))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC TR2AUX_EV_FROMTO THEN
  EXISTS_TAC `Litv (Word8 a)` THEN
  ASM_REWRITE_TAC[] THEN SIMP[check_type_def; do_conversion_def; the_Litv_Word8_def]);;

let TR2AUX_EV_W64_INT = prove
 (`!env x a. ml_Eval env x (\v. v = Litv (Word64 a)) ==>
     ml_Eval env (App (FromTo (WordT W64) IntT) [x]) (\v. v = Litv (IntLit (&(val a))))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC TR2AUX_EV_FROMTO THEN
  EXISTS_TAC `Litv (Word64 a)` THEN
  ASM_REWRITE_TAC[] THEN SIMP[check_type_def; do_conversion_def; the_Litv_Word64_def]);;

let TR2AUX_EV_INT_W8 = prove
 (`!env x i. ml_Eval env x (\v. v = Litv (IntLit i)) ==>
     ml_Eval env (App (FromTo IntT (WordT W8)) [x]) (\v. v = Litv (Word8 (iword i)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC TR2AUX_EV_FROMTO THEN
  EXISTS_TAC `Litv (IntLit i)` THEN
  ASM_REWRITE_TAC[] THEN SIMP[check_type_def; do_conversion_def; the_Litv_IntLit_def]);;

let TR2AUX_EV_INT_W64 = prove
 (`!env x i. ml_Eval env x (\v. v = Litv (IntLit i)) ==>
     ml_Eval env (App (FromTo IntT (WordT W64)) [x]) (\v. v = Litv (Word64 (iword i)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC TR2AUX_EV_FROMTO THEN
  EXISTS_TAC `Litv (IntLit i)` THEN
  ASM_REWRITE_TAC[] THEN SIMP[check_type_def; do_conversion_def; the_Litv_IntLit_def]);;

(* ml_WORD as an equation on the value *)

let TR2AUX_ml_WORD_8 = prove
 (`!w:A word. dimindex(:A) <= 8 ==>
     ml_WORD w = (\v. v = Litv (Word8 (word_shl (word_zx w) (8 - dimindex(:A)))))`,
  SIMP_TAC[ml_WORD_def; ARITH_RULE `d <= 8 ==> d <= 64`]);;

let TR2AUX_ml_WORD_64 = prove
 (`!w:A word. ~(dimindex(:A) <= 8) /\ dimindex(:A) <= 64 ==>
     ml_WORD w = (\v. v = Litv (Word64 (word_shl (word_zx w) (64 - dimindex(:A)))))`,
  SIMP_TAC[ml_WORD_def]);;

let ml_Eval_w2n = prove
 (`ml_Eval env x1 (ml_WORD (w:A word)) ==>
   ml_Eval env
     (if dimindex (:A) = 8 then
        App (FromTo (WordT W8) IntT) [x1]
      else if dimindex (:A) = 64 then
        App (FromTo (WordT W64) IntT) [x1]
      else if dimindex (:A) < 8 then
        App (FromTo (WordT W8) IntT) [App (Shift W8 Lsr (8 - dimindex (:A))) [x1]]
      else
        App (FromTo (WordT W64) IntT) [App (Shift W64 Lsr (64 - dimindex (:A))) [x1]])
     (ml_NUM (val w))`,
  DISCH_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP TR2AUX_Eval_WORD_dimindex) THEN
  REWRITE_TAC[ml_NUM_def; ml_INT_def] THEN
  ASM_CASES_TAC `dimindex(:A) <= 8` THENL
   [UNDISCH_TAC `ml_Eval env x1 (ml_WORD (w:A word))` THEN
    SIMP_TAC[TR2AUX_ml_WORD_8; ASSUME `dimindex(:A) <= 8`] THEN DISCH_TAC THEN
    COND_CASES_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o MATCH_MP TR2AUX_EV_W8_INT) THEN
      SIMP_TAC[TR2AUX_WSHZX_8; ASSUME `dimindex(:A) <= 8`] THEN
      ASM_REWRITE_TAC[SUB_REFL; EXP; MULT_CLAUSES];
      SUBGOAL_THEN `~(dimindex(:A) = 64) /\ dimindex(:A) < 8` STRIP_ASSUME_TAC THENL
       [ASM_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP TR2AUX_EV_W8_INT o
        SPECL [`Lsr`; `8 - dimindex(:A)`] o MATCH_MP TR2AUX_EV_SHIFT8) THEN
      REWRITE_TAC[shift8_lookup_def] THEN CAKE_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[w2n_w2w_8]];
    UNDISCH_TAC `ml_Eval env x1 (ml_WORD (w:A word))` THEN
    SIMP_TAC[TR2AUX_ml_WORD_64; ASSUME `dimindex(:A) <= 64`;
      ASSUME `~(dimindex(:A) <= 8)`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(dimindex(:A) = 8) /\ ~(dimindex(:A) < 8)` STRIP_ASSUME_TAC THENL
     [ASM_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
    COND_CASES_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o MATCH_MP TR2AUX_EV_W64_INT) THEN
      SIMP_TAC[TR2AUX_WSHZX_64; ASSUME `dimindex(:A) <= 64`] THEN
      ASM_REWRITE_TAC[SUB_REFL; EXP; MULT_CLAUSES];
      SUBGOAL_THEN `dimindex(:A) < 64` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP TR2AUX_EV_W64_INT o
        SPECL [`Lsr`; `64 - dimindex(:A)`] o MATCH_MP TR2AUX_EV_SHIFT64) THEN
      REWRITE_TAC[shift64_lookup_def] THEN CAKE_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[w2n_w2w_64]]]);;

(* HOL4: Eval_w2i, made from Eval_Let and Eval_w2n (save_thm); HOL4 w2i is *)
(* ival; its INT_MIN (:A) and dimword (:A) are unfolded as in HOL4         *)

let ml_Eval_w2i = prove
 (`ml_Eval env x1 (ml_WORD (w:A word)) ==>
   ml_Eval env
     (Let (SOME (implode "x"))
        (if dimindex (:A) = 8 then
           App (FromTo (WordT W8) IntT) [x1]
         else if dimindex (:A) = 64 then
           App (FromTo (WordT W64) IntT) [x1]
         else if dimindex (:A) < 8 then
           App (FromTo (WordT W8) IntT) [App (Shift W8 Lsr (8 - dimindex (:A))) [x1]]
         else
           App (FromTo (WordT W64) IntT) [App (Shift W64 Lsr (64 - dimindex (:A))) [x1]])
        (If (App (Test (Compare Lt) IntT)
               [Var (Short (implode "x")); Lit (IntLit (&(2 EXP (dimindex (:A) - 1))))])
            (Var (Short (implode "x")))
            (App (Arith Sub IntT)
               [Var (Short (implode "x")); Lit (IntLit (&(2 EXP dimindex (:A))))])))
     (ml_INT (ival w))`,
  DISCH_TAC THEN
  SUBGOAL_THEN `ival (w:A word) =
    LET (\n. if n < 2 EXP (dimindex (:A) - 1) then &n else &n - &(2 EXP dimindex (:A)))
        (val w)` SUBST1_TAC THENL
   [REWRITE_TAC[ival; LET_DEF; INT_OF_NUM_POW]; ALL_TAC] THEN
  MATCH_MP_TAC (GEN_ALL Eval_Let) THEN EXISTS_TAC `ml_NUM` THEN
  ASM_SIMP_TAC[ml_Eval_w2n] THEN X_GEN_TAC `v:v` THEN DISCH_TAC THEN
  MATCH_MP_TAC TR2AUX_Eval_If THEN
  EXISTS_TAC `val (w:A word) < 2 EXP (dimindex (:A) - 1)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC (TR2AUX_MP_CANON Eval_NUM_LESS) THEN
    ASM_SIMP_TAC[TR2AUX_Eval_write_Var; Eval_Val_NUM];
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
     [ASM_SIMP_TAC[TR2AUX_Eval_write_Var; GSYM ml_NUM_def];
      MATCH_MP_TAC (TR2AUX_MP_CANON Eval_INT_SUB) THEN
      ASM_SIMP_TAC[TR2AUX_Eval_write_Var; Eval_Val_INT; GSYM ml_NUM_def]]]);;

let TR2AUX_WSHZX_IWORD = prove
 (`!i. dimindex(:A) <= dimindex(:B) ==>
     word_shl (word_zx (iword i:A word):B word) (dimindex(:B) - dimindex(:A)) =
     word_shl (iword i:B word) (dimindex(:B) - dimindex(:A))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
  ASM_SIMP_TAC[TR2AUX_WSHZX_BIT; BIT_WORD_SHL; BIT_IWORD] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `dimindex(:B) - dimindex(:A) <= j` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `j - (dimindex(:B) - dimindex(:A)) < dimindex(:A) /\
                j - (dimindex(:B) - dimindex(:A)) < dimindex(:B)`
    (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC);;

let ml_Eval_i2w = prove
 (`dimindex (:A) <= 64 ==>
   ml_Eval env x1 (ml_INT n) ==>
   ml_Eval env
     (if dimindex (:A) = 8 then
        App (FromTo IntT (WordT W8)) [x1]
      else if dimindex (:A) = 64 then
        App (FromTo IntT (WordT W64)) [x1]
      else if dimindex (:A) < 8 then
        App (Shift W8 Lsl (8 - dimindex (:A))) [App (FromTo IntT (WordT W8)) [x1]]
      else
        App (Shift W64 Lsl (64 - dimindex (:A))) [App (FromTo IntT (WordT W64)) [x1]])
     (ml_WORD ((iword n):A word))`,
  REPEAT DISCH_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[ml_INT_def]) THEN
  ASM_CASES_TAC `dimindex(:A) <= 8` THENL
   [SIMP_TAC[TR2AUX_ml_WORD_8; ASSUME `dimindex(:A) <= 8`] THEN
    MP_TAC(INST_TYPE [`:8`,`:B`] TR2AUX_WSHZX_IWORD) THEN
    REWRITE_TAC[DIMINDEX_8] THEN DISCH_THEN(MP_TAC o SPEC `n:int`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    COND_CASES_TAC THENL
     [ASM_REWRITE_TAC[SUB_REFL; WORD_SHL_ZERO] THEN ASM_SIMP_TAC[TR2AUX_EV_INT_W8];
      SUBGOAL_THEN `~(dimindex(:A) = 64) /\ dimindex(:A) < 8` STRIP_ASSUME_TAC THENL
       [ASM_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
      MP_TAC(SPECL [`Lsl`; `8 - dimindex(:A)`] (MATCH_MP TR2AUX_EV_SHIFT8
        (MATCH_MP TR2AUX_EV_INT_W8 (ASSUME
          `ml_Eval env x1 (\v. v = Litv (IntLit n))`)))) THEN
      REWRITE_TAC[shift8_lookup_def] THEN CAKE_REWRITE_TAC[]];
    SIMP_TAC[TR2AUX_ml_WORD_64; ASSUME `dimindex(:A) <= 64`;
      ASSUME `~(dimindex(:A) <= 8)`] THEN
    MP_TAC(INST_TYPE [`:64`,`:B`] TR2AUX_WSHZX_IWORD) THEN
    REWRITE_TAC[DIMINDEX_64] THEN DISCH_THEN(MP_TAC o SPEC `n:int`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `~(dimindex(:A) = 8) /\ ~(dimindex(:A) < 8)` STRIP_ASSUME_TAC THENL
     [ASM_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
    COND_CASES_TAC THENL
     [ASM_REWRITE_TAC[SUB_REFL; WORD_SHL_ZERO] THEN ASM_SIMP_TAC[TR2AUX_EV_INT_W64];
      MP_TAC(SPECL [`Lsl`; `64 - dimindex(:A)`] (MATCH_MP TR2AUX_EV_SHIFT64
        (MATCH_MP TR2AUX_EV_INT_W64 (ASSUME
          `ml_Eval env x1 (\v. v = Litv (IntLit n))`)))) THEN
      REWRITE_TAC[shift64_lookup_def] THEN CAKE_REWRITE_TAC[]]]);;

let ml_Eval_n2w = prove
 (`dimindex (:A) <= 64 ==>
   ml_Eval env x1 (ml_NUM n) ==>
   ml_Eval env
     (if dimindex (:A) = 8 then
        App (FromTo IntT (WordT W8)) [x1]
      else if dimindex (:A) = 64 then
        App (FromTo IntT (WordT W64)) [x1]
      else if dimindex (:A) < 8 then
        App (Shift W8 Lsl (8 - dimindex (:A))) [App (FromTo IntT (WordT W8)) [x1]]
      else
        App (Shift W64 Lsl (64 - dimindex (:A))) [App (FromTo IntT (WordT W64)) [x1]])
     (ml_WORD ((word n):A word))`,
  REWRITE_TAC[WORD_IWORD; ml_NUM_def; ml_Eval_i2w]);;
(* word identities for Eval_w2w: w:B word in a C-bit container, zx w:A word *)

let TR2AUX_W2W_SAME_LE = prove
 (`!w:B word. dimindex(:B) <= dimindex(:A) /\ dimindex(:A) <= dimindex(:C) ==>
     word_ushr (word_shl (word_zx w:C word) (dimindex(:C) - dimindex(:B)))
               (dimindex(:A) - dimindex(:B)) =
     word_shl (word_zx (word_zx w:A word):C word) (dimindex(:C) - dimindex(:A))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_USHR] THEN
  SUBGOAL_THEN `dimindex(:B) <= dimindex(:C)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[TR2AUX_VAL_WSHZX; VAL_WORD_ZX] THEN
  SUBGOAL_THEN `2 EXP (dimindex(:C) - dimindex(:B)) =
    2 EXP (dimindex(:C) - dimindex(:A)) * 2 EXP (dimindex(:A) - dimindex(:B))` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBST1_TAC(ARITH_RULE
   `(2 EXP (dimindex(:C) - dimindex(:A)) * 2 EXP (dimindex(:A) - dimindex(:B))) *
    val (w:B word) =
    2 EXP (dimindex(:A) - dimindex(:B)) * (2 EXP (dimindex(:C) - dimindex(:A)) * val w)`) THEN
  SIMP_TAC[DIV_MULT; EXP_EQ_0; ARITH_EQ]);;

let TR2AUX_W2W_SAME_GT = prove
 (`!w:B word. dimindex(:A) < dimindex(:B) /\ dimindex(:B) <= dimindex(:C) ==>
     word_shl (word_shl (word_zx w:C word) (dimindex(:C) - dimindex(:B)))
              (dimindex(:B) - dimindex(:A)) =
     word_shl (word_zx (word_zx w:A word):C word) (dimindex(:C) - dimindex(:A))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `dimindex(:A) <= dimindex(:C)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM VAL_EQ] THEN ASM_SIMP_TAC[TR2AUX_VAL_WSHZX] THEN
  ONCE_REWRITE_TAC[VAL_WORD_SHL] THEN ASM_SIMP_TAC[TR2AUX_VAL_WSHZX; LT_IMP_LE] THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; MULT_ASSOC; GSYM EXP_ADD] THEN
  SUBGOAL_THEN `(dimindex(:B) - dimindex(:A)) + (dimindex(:C) - dimindex(:B)) =
                dimindex(:C) - dimindex(:A)` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP TR2AUX_EXP_SPLIT) THEN
  REWRITE_TAC[MOD_MULT2]);;

let TR2AUX_VAL_USHR_WSHZX = prove
 (`!w:A word. dimindex(:A) <= dimindex(:B) ==>
     val (word_ushr (word_shl (word_zx w:B word) (dimindex(:B) - dimindex(:A)))
                    (dimindex(:B) - dimindex(:A))) = val w`,
  SIMP_TAC[VAL_WORD_USHR; TR2AUX_VAL_WSHZX; DIV_MULT; EXP_EQ_0; ARITH_EQ]);;

let TR2AUX_W2W_8_64 = prove
 (`!w:B word. dimindex(:B) <= 8 /\ 8 < dimindex(:A) /\ dimindex(:A) <= 64 ==>
     word_shl (word_ushr (iword (&(val (word_shl (word_zx w:byte) (8 - dimindex(:B))))):int64)
                         (8 - dimindex(:B))) (64 - dimindex(:A)) =
     word_shl (word_zx (word_zx w:A word):int64) (64 - dimindex(:A))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM WORD_IWORD] THEN
  MP_TAC(ISPEC `w:B word` (INST_TYPE [`:B`,`:A`; `:8`,`:B`] TR2AUX_VAL_WSHZX)) THEN
  REWRITE_TAC[DIMINDEX_8] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ] THEN
  MP_TAC(ISPEC `word_zx (w:B word):A word` (INST_TYPE [`:64`,`:B`] TR2AUX_VAL_WSHZX)) THEN
  REWRITE_TAC[DIMINDEX_64] THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `dimindex(:B) <= dimindex(:A)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[VAL_WORD_ZX] THEN REWRITE_TAC[VAL_WORD_SHL; VAL_WORD_USHR] THEN
  ASM_REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
  SUBGOAL_THEN `2 EXP (8 - dimindex(:B)) * val (w:B word) < 2 EXP 8` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[MULT_SYM] THEN MATCH_MP_TAC less_two_pow_lemma THEN
    ASM_REWRITE_TAC[VAL_BOUND];
    ALL_TAC] THEN
  SUBGOAL_THEN `2 EXP (8 - dimindex(:B)) * val (w:B word) < 2 EXP 64` ASSUME_TAC THENL
   [TRANS_TAC LTE_TRANS `2 EXP 8` THEN ASM_REWRITE_TAC[LE_EXP] THEN ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT; DIV_MULT; EXP_EQ_0; ARITH_EQ] THEN
  MATCH_MP_TAC MOD_LT THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
  MATCH_MP_TAC less_two_pow_lemma THEN CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
  TRANS_TAC LTE_TRANS `2 EXP dimindex(:B)` THEN REWRITE_TAC[VAL_BOUND; LE_EXP] THEN
  ASM_ARITH_TAC);;

let TR2AUX_W2W_64_8 = prove
 (`!w:B word. dimindex(:A) <= 8 /\ 8 < dimindex(:B) /\ dimindex(:B) <= 64 ==>
     word_shl (iword (&(val (word_ushr (word_shl (word_zx w:int64) (64 - dimindex(:B)))
                                       (64 - dimindex(:B))))):byte) (8 - dimindex(:A)) =
     word_shl (word_zx (word_zx w:A word):byte) (8 - dimindex(:A))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `w:B word` (INST_TYPE [`:B`,`:A`; `:64`,`:B`] TR2AUX_VAL_USHR_WSHZX)) THEN
  REWRITE_TAC[DIMINDEX_64] THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM WORD_IWORD; GSYM VAL_EQ] THEN
  MP_TAC(ISPEC `word_zx (w:B word):A word` (INST_TYPE [`:8`,`:B`] TR2AUX_VAL_WSHZX)) THEN
  REWRITE_TAC[DIMINDEX_8] THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[VAL_WORD_SHL; VAL_WORD; VAL_WORD_ZX_GEN; DIMINDEX_8] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
    [MATCH_MP TR2AUX_EXP_SPLIT (ASSUME `dimindex(:A) <= 8`)] THEN
  REWRITE_TAC[MOD_MULT2; MOD_MOD_EXP_MIN] THEN
  SUBGOAL_THEN `MIN 8 (dimindex(:A)) = dimindex(:A)` SUBST1_TAC THENL
   [ASM_ARITH_TAC; REFL_TAC]);;

let ml_Eval_w2w = prove
 (`dimindex (:A) <= 64 /\ dimindex (:B) <= 64 ==>
   ml_Eval env x1 (ml_WORD (w:B word)) ==>
   ml_Eval env
     (if (dimindex (:A) <= 8 <=> dimindex (:B) <= 8) then
        let w = if dimindex (:A) <= 8 then W8 else W64 in
          if dimindex (:B) <= dimindex (:A) then
            App (Shift w Lsr (dimindex (:A) - dimindex (:B))) [x1]
          else
            App (Shift w Lsl (dimindex (:B) - dimindex (:A))) [x1]
      else if dimindex (:B) <= 8 then
        App (Shift W64 Lsl (64 - dimindex (:A)))
          [App (Shift W64 Lsr (8 - dimindex (:B)))
             [App (FromTo IntT (WordT W64)) [App (FromTo (WordT W8) IntT) [x1]]]]
      else
        App (Shift W8 Lsl (8 - dimindex (:A)))
          [App (FromTo IntT (WordT W8)) [App (FromTo (WordT W64) IntT)
             [App (Shift W64 Lsr (64 - dimindex (:B))) [x1]]]])
     (ml_WORD ((word_zx w):A word))`,
  STRIP_TAC THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  ASM_CASES_TAC `dimindex(:B) <= 8` THEN ASM_CASES_TAC `dimindex(:A) <= 8` THEN
  ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[TR2AUX_ml_WORD_8; TR2AUX_ml_WORD_64] THEN DISCH_TAC THENL
   [COND_CASES_TAC THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP TR2AUX_EV_SHIFT8) THENL
     [DISCH_THEN(MP_TAC o SPECL [`Lsr`; `dimindex(:A) - dimindex(:B)`]) THEN
      REWRITE_TAC[shift8_lookup_def] THEN CAKE_REWRITE_TAC[] THEN
      MP_TAC(ISPEC `w:B word` (INST_TYPE [`:8`,`:C`] TR2AUX_W2W_SAME_LE));
      DISCH_THEN(MP_TAC o SPECL [`Lsl`; `dimindex(:B) - dimindex(:A)`]) THEN
      REWRITE_TAC[shift8_lookup_def] THEN CAKE_REWRITE_TAC[] THEN
      MP_TAC(ISPEC `w:B word` (INST_TYPE [`:8`,`:C`] TR2AUX_W2W_SAME_GT))] THEN
    REWRITE_TAC[DIMINDEX_8] THEN ANTS_TAC THEN TRY ASM_ARITH_TAC THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPECL [`Lsl`; `64 - dimindex(:A)`] o
      MATCH_MP TR2AUX_EV_SHIFT64 o SPECL [`Lsr`; `8 - dimindex(:B)`] o
      MATCH_MP TR2AUX_EV_SHIFT64 o MATCH_MP TR2AUX_EV_INT_W64 o
      MATCH_MP TR2AUX_EV_W8_INT) THEN
    REWRITE_TAC[shift64_lookup_def] THEN CAKE_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `w:B word` TR2AUX_W2W_8_64) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]];
    FIRST_X_ASSUM(MP_TAC o SPECL [`Lsl`; `8 - dimindex(:A)`] o
      MATCH_MP TR2AUX_EV_SHIFT8 o MATCH_MP TR2AUX_EV_INT_W8 o
      MATCH_MP TR2AUX_EV_W64_INT o SPECL [`Lsr`; `64 - dimindex(:B)`] o
      MATCH_MP TR2AUX_EV_SHIFT64) THEN
    REWRITE_TAC[shift8_lookup_def; shift64_lookup_def] THEN CAKE_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `w:B word` TR2AUX_W2W_64_8) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]];
    COND_CASES_TAC THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP TR2AUX_EV_SHIFT64) THENL
     [DISCH_THEN(MP_TAC o SPECL [`Lsr`; `dimindex(:A) - dimindex(:B)`]) THEN
      REWRITE_TAC[shift64_lookup_def] THEN CAKE_REWRITE_TAC[] THEN
      MP_TAC(ISPEC `w:B word` (INST_TYPE [`:64`,`:C`] TR2AUX_W2W_SAME_LE));
      DISCH_THEN(MP_TAC o SPECL [`Lsl`; `dimindex(:B) - dimindex(:A)`]) THEN
      REWRITE_TAC[shift64_lookup_def] THEN CAKE_REWRITE_TAC[] THEN
      MP_TAC(ISPEC `w:B word` (INST_TYPE [`:64`,`:C`] TR2AUX_W2W_SAME_GT))] THEN
    REWRITE_TAC[DIMINDEX_64] THEN ANTS_TAC THEN TRY ASM_ARITH_TAC THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]]);;
(* shifts: F (shift w) in terms of shifts of F w *)

let TR2AUX_WSHZX_SHL = prove
 (`!(w:A word) n. dimindex(:A) <= dimindex(:B) ==>
     word_shl (word_zx (word_shl w n):B word) (dimindex(:B) - dimindex(:A)) =
     word_shl (word_shl (word_zx w:B word) (dimindex(:B) - dimindex(:A))) n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM VAL_EQ] THEN
  ASM_SIMP_TAC[TR2AUX_VAL_WSHZX] THEN ONCE_REWRITE_TAC[VAL_WORD_SHL] THEN
  ASM_SIMP_TAC[TR2AUX_VAL_WSHZX] THEN REWRITE_TAC[VAL_WORD_SHL] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP TR2AUX_EXP_SPLIT) THEN
  SUBST1_TAC(ARITH_RULE `2 EXP n * 2 EXP (dimindex(:B) - dimindex(:A)) * val (w:A word) =
    2 EXP (dimindex(:B) - dimindex(:A)) * (2 EXP n * val w)`) THEN
  REWRITE_TAC[MOD_MULT2]);;

let TR2AUX_WSHZX_USHR = prove
 (`!(w:A word) n. dimindex(:A) <= dimindex(:B) ==>
     word_shl (word_zx (word_ushr w n):B word) (dimindex(:B) - dimindex(:A)) =
     word_shl (word_ushr (word_shl (word_zx w:B word) (dimindex(:B) - dimindex(:A)))
                         (n + (dimindex(:B) - dimindex(:A))))
              (dimindex(:B) - dimindex(:A))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM VAL_EQ] THEN
  ASM_SIMP_TAC[TR2AUX_VAL_WSHZX] THEN ONCE_REWRITE_TAC[VAL_WORD_SHL] THEN
  REWRITE_TAC[VAL_WORD_USHR] THEN ASM_SIMP_TAC[TR2AUX_VAL_WSHZX] THEN
  REWRITE_TAC[EXP_ADD] THEN
  SUBST1_TAC(ARITH_RULE `2 EXP n * 2 EXP (dimindex(:B) - dimindex(:A)) =
    2 EXP (dimindex(:B) - dimindex(:A)) * 2 EXP n`) THEN
  SIMP_TAC[DIV_MULT2; EXP_EQ_0; ARITH_EQ] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP TR2AUX_EXP_SPLIT) THEN
  REWRITE_TAC[LT_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ] THEN
  TRANS_TAC LET_TRANS `val (w:A word)` THEN REWRITE_TAC[VAL_BOUND; DIV_LE]);;

let ml_Eval_word_lsl = prove
 (`!n. ml_Eval env x1 (ml_WORD (w1:A word)) ==>
       ml_Eval env (App (Shift (if dimindex (:A) <= 8 then W8 else W64) Lsl n) [x1])
         (ml_WORD (word_shl w1 n))`,
  GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP TR2AUX_Eval_WORD_dimindex) THEN
  ASM_CASES_TAC `dimindex(:A) <= 8` THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
  REPEAT DISCH_TAC THEN ASM_SIMP_TAC[TR2AUX_ml_WORD_8; TR2AUX_ml_WORD_64] THENL
   [MP_TAC(ISPECL [`w1:A word`; `n:num`] (INST_TYPE [`:8`,`:B`] TR2AUX_WSHZX_SHL)) THEN
    REWRITE_TAC[DIMINDEX_8] THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    UNDISCH_TAC `ml_Eval env x1 (ml_WORD (w1:A word))` THEN
    ASM_SIMP_TAC[TR2AUX_ml_WORD_8] THEN
    DISCH_THEN(MP_TAC o SPECL [`Lsl`; `n:num`] o MATCH_MP TR2AUX_EV_SHIFT8) THEN
    REWRITE_TAC[shift8_lookup_def] THEN CAKE_REWRITE_TAC[];
    MP_TAC(ISPECL [`w1:A word`; `n:num`] (INST_TYPE [`:64`,`:B`] TR2AUX_WSHZX_SHL)) THEN
    REWRITE_TAC[DIMINDEX_64] THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    UNDISCH_TAC `ml_Eval env x1 (ml_WORD (w1:A word))` THEN
    ASM_SIMP_TAC[TR2AUX_ml_WORD_64] THEN
    DISCH_THEN(MP_TAC o SPECL [`Lsl`; `n:num`] o MATCH_MP TR2AUX_EV_SHIFT64) THEN
    REWRITE_TAC[shift64_lookup_def] THEN CAKE_REWRITE_TAC[]]);;

let TR2AUX_WSHZX_USHR_8,TR2AUX_WSHZX_USHR_64 =
  let mk ty dth = REWRITE_RULE[dth] (INST_TYPE [ty,`:B`] TR2AUX_WSHZX_USHR) in
  mk `:8` DIMINDEX_8, mk `:64` DIMINDEX_64;;

let ml_Eval_word_lsr = prove
 (`!n. ml_Eval env x1 (ml_WORD (w1:A word)) ==>
       ml_Eval env
         (let w = (if dimindex (:A) <= 8 then W8 else W64) in
          let k = (if dimindex (:A) <= 8 then 8 else 64) - dimindex(:A) in
            if dimindex (:A) = 8 \/ dimindex (:A) = 64 then
              App (Shift w Lsr n) [x1]
            else
              App (Shift w Lsl k) [App (Shift w Lsr (n+k)) [x1]])
         (ml_WORD (word_ushr w1 n))`,
  GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP TR2AUX_Eval_WORD_dimindex) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  ASM_CASES_TAC `dimindex(:A) <= 8` THEN ASM_REWRITE_TAC[] THENL
   [SIMP_TAC[TR2AUX_ml_WORD_8; ASSUME `dimindex(:A) <= 8`] THEN
    UNDISCH_TAC `ml_Eval env x1 (ml_WORD (w1:A word))` THEN
    SIMP_TAC[TR2AUX_ml_WORD_8; ASSUME `dimindex(:A) <= 8`] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`w1:A word`; `n:num`] TR2AUX_WSHZX_USHR_8) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    COND_CASES_TAC THENL
     [SUBGOAL_THEN `dimindex(:A) = 8` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`Lsr`; `n:num`] o MATCH_MP TR2AUX_EV_SHIFT8) THEN
      ASM_REWRITE_TAC[SUB_REFL; ADD_CLAUSES; WORD_SHL_ZERO; shift8_lookup_def] THEN
      CAKE_REWRITE_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPECL [`Lsl`; `8 - dimindex(:A)`] o
        MATCH_MP TR2AUX_EV_SHIFT8 o SPECL [`Lsr`; `n + 8 - dimindex(:A)`] o
        MATCH_MP TR2AUX_EV_SHIFT8) THEN
      REWRITE_TAC[shift8_lookup_def] THEN CAKE_REWRITE_TAC[]];
    SIMP_TAC[TR2AUX_ml_WORD_64; ASSUME `dimindex(:A) <= 64`; ASSUME `~(dimindex(:A) <= 8)`] THEN
    UNDISCH_TAC `ml_Eval env x1 (ml_WORD (w1:A word))` THEN
    SIMP_TAC[TR2AUX_ml_WORD_64; ASSUME `dimindex(:A) <= 64`; ASSUME `~(dimindex(:A) <= 8)`] THEN
    DISCH_TAC THEN
    MP_TAC(SPECL [`w1:A word`; `n:num`] TR2AUX_WSHZX_USHR_64) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    COND_CASES_TAC THENL
     [SUBGOAL_THEN `dimindex(:A) = 64` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`Lsr`; `n:num`] o MATCH_MP TR2AUX_EV_SHIFT64) THEN
      ASM_REWRITE_TAC[SUB_REFL; ADD_CLAUSES; WORD_SHL_ZERO; shift64_lookup_def] THEN
      CAKE_REWRITE_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPECL [`Lsl`; `64 - dimindex(:A)`] o
        MATCH_MP TR2AUX_EV_SHIFT64 o SPECL [`Lsr`; `n + 64 - dimindex(:A)`] o
        MATCH_MP TR2AUX_EV_SHIFT64) THEN
      REWRITE_TAC[shift64_lookup_def] THEN CAKE_REWRITE_TAC[]]]);;

let TR2AUX_WSHZX_ISHR = prove
 (`!(w:A word) n. dimindex(:A) <= dimindex(:B) ==>
     word_shl (word_zx (word_ishr w n):B word) (dimindex(:B) - dimindex(:A)) =
     word_shl (word_ishr (word_shl (word_zx w:B word) (dimindex(:B) - dimindex(:A)))
                         (n + (dimindex(:B) - dimindex(:A))))
              (dimindex(:B) - dimindex(:A))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[TR2AUX_WSHZX_BIT; BIT_WORD_SHL; BIT_WORD_ISHR] THEN
  ASM_CASES_TAC `dimindex(:B) - dimindex(:A) <= i` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `(:A)` DIMINDEX_GE_1) THEN
  ABBREV_TAC `k = dimindex(:B) - dimindex(:A)` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(i - k) + n + k = i + n /\ (i + n) - k = (i - k) + n /\
    ((i - k) + n < dimindex(:A) <=> i + n < dimindex(:B)) /\
    (dimindex(:B) - 1) - k = dimindex(:A) - 1 /\ k <= dimindex(:B) - 1 /\
    dimindex(:B) - 1 < dimindex(:B) /\ i - k < dimindex(:A) /\ i - k < dimindex(:B) /\
    k <= i + n`
  STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

let TR2AUX_WSHZX_ISHR_8,TR2AUX_WSHZX_ISHR_64 =
  let mk ty dth = REWRITE_RULE[dth] (INST_TYPE [ty,`:B`] TR2AUX_WSHZX_ISHR) in
  mk `:8` DIMINDEX_8, mk `:64` DIMINDEX_64;;

let ml_Eval_word_asr = prove
 (`!n. ml_Eval env x1 (ml_WORD (w1:A word)) ==>
       ml_Eval env
         (let w = (if dimindex (:A) <= 8 then W8 else W64) in
          let k = (if dimindex (:A) <= 8 then 8 else 64) - dimindex(:A) in
            if dimindex (:A) = 8 \/ dimindex (:A) = 64 then
              App (Shift w Asr n) [x1]
            else
              App (Shift w Lsl k) [App (Shift w Asr (n+k)) [x1]])
         (ml_WORD (word_ishr w1 n))`,
  GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP TR2AUX_Eval_WORD_dimindex) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  ASM_CASES_TAC `dimindex(:A) <= 8` THEN ASM_REWRITE_TAC[] THENL
   [SIMP_TAC[TR2AUX_ml_WORD_8; ASSUME `dimindex(:A) <= 8`] THEN
    UNDISCH_TAC `ml_Eval env x1 (ml_WORD (w1:A word))` THEN
    SIMP_TAC[TR2AUX_ml_WORD_8; ASSUME `dimindex(:A) <= 8`] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`w1:A word`; `n:num`] TR2AUX_WSHZX_ISHR_8) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    COND_CASES_TAC THENL
     [SUBGOAL_THEN `dimindex(:A) = 8` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`Asr`; `n:num`] o MATCH_MP TR2AUX_EV_SHIFT8) THEN
      ASM_REWRITE_TAC[SUB_REFL; ADD_CLAUSES; WORD_SHL_ZERO; shift8_lookup_def] THEN
      CAKE_REWRITE_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPECL [`Lsl`; `8 - dimindex(:A)`] o
        MATCH_MP TR2AUX_EV_SHIFT8 o SPECL [`Asr`; `n + 8 - dimindex(:A)`] o
        MATCH_MP TR2AUX_EV_SHIFT8) THEN
      REWRITE_TAC[shift8_lookup_def] THEN CAKE_REWRITE_TAC[]];
    SIMP_TAC[TR2AUX_ml_WORD_64; ASSUME `dimindex(:A) <= 64`; ASSUME `~(dimindex(:A) <= 8)`] THEN
    UNDISCH_TAC `ml_Eval env x1 (ml_WORD (w1:A word))` THEN
    SIMP_TAC[TR2AUX_ml_WORD_64; ASSUME `dimindex(:A) <= 64`; ASSUME `~(dimindex(:A) <= 8)`] THEN
    DISCH_TAC THEN
    MP_TAC(SPECL [`w1:A word`; `n:num`] TR2AUX_WSHZX_ISHR_64) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    COND_CASES_TAC THENL
     [SUBGOAL_THEN `dimindex(:A) = 64` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`Asr`; `n:num`] o MATCH_MP TR2AUX_EV_SHIFT64) THEN
      ASM_REWRITE_TAC[SUB_REFL; ADD_CLAUSES; WORD_SHL_ZERO; shift64_lookup_def] THEN
      CAKE_REWRITE_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPECL [`Lsl`; `64 - dimindex(:A)`] o
        MATCH_MP TR2AUX_EV_SHIFT64 o SPECL [`Asr`; `n + 64 - dimindex(:A)`] o
        MATCH_MP TR2AUX_EV_SHIFT64) THEN
      REWRITE_TAC[shift64_lookup_def] THEN CAKE_REWRITE_TAC[]]]);;

let TR2AUX_ZX_ROR = prove
 (`!(w:A word) n. dimindex(:A) = dimindex(:B) ==>
     word_zx (word_ror w n):B word = word_ror (word_zx w:B word) n`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
  REWRITE_TAC[BIT_WORD_ZX; BIT_WORD_ROR] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(i + n MOD dimindex(:B)) - dimindex(:B) < dimindex(:B)`
    (fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(SPECL [`n:num`; `dimindex(:B)`] MOD_LT_EQ) THEN
  REWRITE_TAC[DIMINDEX_NONZERO] THEN ASM_ARITH_TAC);;

let ml_Eval_word_ror = prove
 (`!n. ml_Eval env x1 (ml_WORD (w1:A word)) ==>
       (~(dimindex (:A) = 8) ==> dimindex (:A) = 64) ==>
       ml_Eval env (App (Shift (if dimindex (:A) <= 8 then W8 else W64) Ror n) [x1])
         (ml_WORD (word_ror w1 n))`,
  GEN_TAC THEN REPEAT DISCH_TAC THEN
  ASM_CASES_TAC `dimindex(:A) = 8` THENL
   [ASM_REWRITE_TAC[ARITH_RULE `8 <= 8`] THEN
    UNDISCH_TAC `ml_Eval env x1 (ml_WORD (w1:A word))` THEN
    SIMP_TAC[TR2AUX_ml_WORD_8; ASSUME `dimindex(:A) = 8`; LE_REFL] THEN
    REWRITE_TAC[SUB_REFL; WORD_SHL_ZERO] THEN
    DISCH_THEN(MP_TAC o SPECL [`Ror`; `n:num`] o MATCH_MP TR2AUX_EV_SHIFT8) THEN
    REWRITE_TAC[shift8_lookup_def] THEN CAKE_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`w1:A word`; `n:num`] (INST_TYPE [`:8`,`:B`] TR2AUX_ZX_ROR)) THEN
    ASM_REWRITE_TAC[DIMINDEX_8] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[];
    FIRST_X_ASSUM(fun th -> FIRST_ASSUM(ASSUME_TAC o MATCH_MP th)) THEN
    ASM_REWRITE_TAC[ARITH_RULE `~(64 <= 8)`] THEN
    UNDISCH_TAC `ml_Eval env x1 (ml_WORD (w1:A word))` THEN
    SIMP_TAC[TR2AUX_ml_WORD_64; ASSUME `dimindex(:A) = 64`; LE_REFL;
      ARITH_RULE `~(64 <= 8)`] THEN
    REWRITE_TAC[SUB_REFL; WORD_SHL_ZERO] THEN
    DISCH_THEN(MP_TAC o SPECL [`Ror`; `n:num`] o MATCH_MP TR2AUX_EV_SHIFT64) THEN
    REWRITE_TAC[shift64_lookup_def] THEN CAKE_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`w1:A word`; `n:num`] (INST_TYPE [`:64`,`:B`] TR2AUX_ZX_ROR)) THEN
    ASM_REWRITE_TAC[DIMINDEX_64] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]]);;
(* HOL4: augment_srw_ss [rewrites [float_to_fp64_fp64_to_float]] *)

let _ = cake_add_simps [float_to_fp64_fp64_to_float];;

let lift_fp_top_def = cake_def
  `lift_fp_top f f1 f2 f3 =
     fp64_to_float (fp_top_comp f (float_to_fp64 f1) (float_to_fp64 f2)
                                  (float_to_fp64 f3))`;;

let float64_fma_def = cake_def
  `float64_fma (f1:(52,11)float) f2 f3 =
     SND (float_mul_add roundTiesToEven f1 f2 f3)`;;

(* a floating-point operation on the values of ml_FLOAT64 *)

let TR2AUX_FLOAT_TAC =
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  FIRST [MATCH_MP_TAC TR2AUX_Eval_App1 THEN EXISTS_TAC `ml_FLOAT64 f1`;
         MATCH_MP_TAC TR2AUX_Eval_App2 THEN
         MAP_EVERY EXISTS_TAC [`ml_FLOAT64 f1`; `ml_FLOAT64 f2`];
         MATCH_MP_TAC TR2AUX_Eval_App3 THEN
         MAP_EVERY EXISTS_TAC [`ml_FLOAT64 f1`; `ml_FLOAT64 f2`; `ml_FLOAT64 f3`]] THEN
  ASM_REWRITE_TAC[getOpClass_def] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[ml_FLOAT64_def; ml_BOOL_def; ml_WORD_def] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[do_app_def] THEN CAKE_REWRITE_TAC[] THEN
  SIMP[check_type_def; ALL; do_arith_def; do_test_def; do_conversion_def; MAP;
    dest_Litv_def; the_Litv_Float64_def; the_Litv_Word64_def] THEN
  SIMP[fpfma_def; fp_top_comp_def; fp_bop_comp_def; fp_uop_comp_def; fp_cmp_def;
    fp64_mul_add_def; fp64_add_def; fp64_sub_def; fp64_mul_def; fp64_div_def;
    fp64_abs_def; fp64_negate_def; fp64_sqrt_def; o_THM; fp64_equal_def;
    fp64_to_float_float_to_fp64; DIMINDEX_64; ARITH_RULE `~(64 <= 8)`; SUB_REFL;
    WORD_SHL_ZERO; WORD_ZX_TRIVIAL; semanticPrimitivesProps_Boolv_11;
    injectivity "option"; PAIR_EQ; injectivity "result"; UNWIND_THM1];;

let Eval_FLOAT_FMA = prove
 (`!f1 f2 f3.
     ml_Eval env x2 (ml_FLOAT64 f2) ==>
     ml_Eval env x3 (ml_FLOAT64 f3) ==>
     ml_Eval env x1 (ml_FLOAT64 f1) ==>
     ml_Eval env (App (Arith FMA Float64T) [x1; x2; x3])
       (ml_FLOAT64 (float64_fma f2 f3 f1))`,
  TR2AUX_FLOAT_TAC THEN REWRITE_TAC[float64_fma_def]);;

let lift_fp_bop_def = cake_def
  `lift_fp_bop f f1 f2 =
     fp64_to_float (fp_bop_comp f (float_to_fp64 f1) (float_to_fp64 f2))`;;

let float64_add_def = cake_def
  `float64_add = lift_fp_bop FP_Add`;;

let float64_add_thm = prove
 (`float64_add f1 f2 = SND (float_add roundTiesToEven f1 f2)`,
  REWRITE_TAC[float64_add_def; lift_fp_bop_def; fp_bop_comp_def] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[fp64_add_def; fp64_to_float_float_to_fp64]);;

let float64_sub_def = cake_def
  `float64_sub = lift_fp_bop FP_Sub`;;

let float64_sub_thm = prove
 (`float64_sub f1 f2 = SND (float_sub roundTiesToEven f1 f2)`,
  REWRITE_TAC[float64_sub_def; lift_fp_bop_def; fp_bop_comp_def] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[fp64_sub_def; fp64_to_float_float_to_fp64]);;

let float64_mul_def = cake_def
  `float64_mul = lift_fp_bop FP_Mul`;;

let float64_mul_thm = prove
 (`float64_mul f1 f2 = SND (float_mul roundTiesToEven f1 f2)`,
  REWRITE_TAC[float64_mul_def; lift_fp_bop_def; fp_bop_comp_def] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[fp64_mul_def; fp64_to_float_float_to_fp64]);;

let float64_div_def = cake_def
  `float64_div = lift_fp_bop FP_Div`;;

let float64_div_thm = prove
 (`float64_div f1 f2 = SND (float_div roundTiesToEven f1 f2)`,
  REWRITE_TAC[float64_div_def; lift_fp_bop_def; fp_bop_comp_def] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[fp64_div_def; fp64_to_float_float_to_fp64]);;

let Eval_FLOAT_ADD = prove
 (`!f1 f2.
     ml_Eval env x1 (ml_FLOAT64 f1) ==>
     ml_Eval env x2 (ml_FLOAT64 f2) ==>
     ml_Eval env (App (Arith Add Float64T) [x1; x2]) (ml_FLOAT64 (float64_add f1 f2))`,
  TR2AUX_FLOAT_TAC THEN REWRITE_TAC[float64_add_thm]);;

let Eval_FLOAT_SUB = prove
 (`!f1 f2.
     ml_Eval env x1 (ml_FLOAT64 f1) ==>
     ml_Eval env x2 (ml_FLOAT64 f2) ==>
     ml_Eval env (App (Arith Sub Float64T) [x1; x2]) (ml_FLOAT64 (float64_sub f1 f2))`,
  TR2AUX_FLOAT_TAC THEN REWRITE_TAC[float64_sub_thm]);;

let Eval_FLOAT_MULT = prove
 (`!f1 f2.
     ml_Eval env x1 (ml_FLOAT64 f1) ==>
     ml_Eval env x2 (ml_FLOAT64 f2) ==>
     ml_Eval env (App (Arith Mul Float64T) [x1; x2]) (ml_FLOAT64 (float64_mul f1 f2))`,
  TR2AUX_FLOAT_TAC THEN REWRITE_TAC[float64_mul_thm]);;

let Eval_FLOAT_DIV = prove
 (`!f1 f2.
     ml_Eval env x1 (ml_FLOAT64 f1) ==>
     ml_Eval env x2 (ml_FLOAT64 f2) ==>
     ml_Eval env (App (Arith Div Float64T) [x1; x2]) (ml_FLOAT64 (float64_div f1 f2))`,
  TR2AUX_FLOAT_TAC THEN REWRITE_TAC[float64_div_thm]);;
let lift_fp_cmp_def = cake_def
  `lift_fp_cmp f f1 f2 = fp_cmp f (float_to_fp64 f1) (float_to_fp64 f2)`;;

let float64_less_def = cake_def
  `float64_less = lift_fp_cmp Lt`;;

let float64_less_thm = prove
 (`float64_less f1 f2 <=> float_less_than f1 f2`,
  REWRITE_TAC[float64_less_def; lift_fp_cmp_def; fp_cmp_def] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[fp64_lessThan_def; fp64_to_float_float_to_fp64]);;

let float64_less_equal_def = cake_def
  `float64_less_equal = lift_fp_cmp Leq`;;

let float64_less_equal_thm = prove
 (`float64_less_equal f1 f2 <=> float_less_equal f1 f2`,
  REWRITE_TAC[float64_less_equal_def; lift_fp_cmp_def; fp_cmp_def] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[fp64_lessEqual_def; fp64_to_float_float_to_fp64]);;

let float64_greater_def = cake_def
  `float64_greater = lift_fp_cmp Gt`;;

let float64_greater_thm = prove
 (`float64_greater f1 f2 <=> float_greater_than f1 f2`,
  REWRITE_TAC[float64_greater_def; lift_fp_cmp_def; fp_cmp_def] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[fp64_greaterThan_def; fp64_to_float_float_to_fp64]);;

let float64_greater_equal_def = cake_def
  `float64_greater_equal = lift_fp_cmp Geq`;;

let float64_greater_equal_thm = prove
 (`float64_greater_equal f1 f2 <=> float_greater_equal f1 f2`,
  REWRITE_TAC[float64_greater_equal_def; lift_fp_cmp_def; fp_cmp_def] THEN
  CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[fp64_greaterEqual_def; fp64_to_float_float_to_fp64]);;

let float64_equal_def = cake_def
  `float64_equal f1 f2 <=> fp64_equal (float_to_fp64 f1) (float_to_fp64 f2)`;;

let float64_equal_thm = prove
 (`float64_equal f1 f2 <=> float_equal f1 f2`,
  REWRITE_TAC[float64_equal_def; fp64_equal_def; fp64_to_float_float_to_fp64]);;

(* HOL4 [local] *)

let Eval_FP_cmp = prove
 (`!cmp f1 f2.
     ml_Eval env x1 (ml_FLOAT64 f1) ==>
     ml_Eval env x2 (ml_FLOAT64 f2) ==>
     ml_Eval env (App (Test (Compare cmp) Float64T) [x1;x2])
       (ml_BOOL (lift_fp_cmp cmp f1 f2))`,
  TR2AUX_FLOAT_TAC THEN REWRITE_TAC[lift_fp_cmp_def; fp_cmp_def]);;

(* HOL4 saves these four with SPEC_ALL (no quantifiers) *)

let Eval_FLOAT_LESS = prove
 (`ml_Eval env x1 (ml_FLOAT64 f1) ==>
   ml_Eval env x2 (ml_FLOAT64 f2) ==>
   ml_Eval env (App (Test (Compare Lt) Float64T) [x1;x2]) (ml_BOOL (float64_less f1 f2))`,
  REWRITE_TAC[float64_less_def; Eval_FP_cmp]);;

let Eval_FLOAT_LESS_EQ = prove
 (`ml_Eval env x1 (ml_FLOAT64 f1) ==>
   ml_Eval env x2 (ml_FLOAT64 f2) ==>
   ml_Eval env (App (Test (Compare Leq) Float64T) [x1;x2])
     (ml_BOOL (float64_less_equal f1 f2))`,
  REWRITE_TAC[float64_less_equal_def; Eval_FP_cmp]);;

let Eval_FLOAT_GREATER = prove
 (`ml_Eval env x1 (ml_FLOAT64 f1) ==>
   ml_Eval env x2 (ml_FLOAT64 f2) ==>
   ml_Eval env (App (Test (Compare Gt) Float64T) [x1;x2])
     (ml_BOOL (float64_greater f1 f2))`,
  REWRITE_TAC[float64_greater_def; Eval_FP_cmp]);;

let Eval_FLOAT_GREATER_EQ = prove
 (`ml_Eval env x1 (ml_FLOAT64 f1) ==>
   ml_Eval env x2 (ml_FLOAT64 f2) ==>
   ml_Eval env (App (Test (Compare Geq) Float64T) [x1;x2])
     (ml_BOOL (float64_greater_equal f1 f2))`,
  REWRITE_TAC[float64_greater_equal_def; Eval_FP_cmp]);;

let Eval_FLOAT_EQ = prove
 (`ml_Eval env x1 (ml_FLOAT64 f1) ==>
   ml_Eval env x2 (ml_FLOAT64 f2) ==>
   ml_Eval env (App (Test Equal Float64T) [x1;x2]) (ml_BOOL (float64_equal f1 f2))`,
  TR2AUX_FLOAT_TAC THEN REWRITE_TAC[float64_equal_def; fp64_equal_def;
    fp64_to_float_float_to_fp64]);;

let lift_fp_uop_def = cake_def
  `lift_fp_uop f f1 = fp64_to_float (fp_uop_comp f (float_to_fp64 f1))`;;

let float64_abs_def = cake_def
  `float64_abs = lift_fp_uop FP_Abs`;;

let float64_abs_thm = prove
 (`float64_abs f1 = float_abs f1`,
  REWRITE_TAC[float64_abs_def; lift_fp_uop_def; fp_uop_comp_def] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[fp64_abs_def; o_THM; fp64_to_float_float_to_fp64]);;

let float64_neg_def = cake_def
  `float64_neg = lift_fp_uop FP_Neg`;;

let float64_neg_thm = prove
 (`float64_neg f1 = float_negate f1`,
  REWRITE_TAC[float64_neg_def; lift_fp_uop_def; fp_uop_comp_def] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[fp64_negate_def; o_THM; fp64_to_float_float_to_fp64]);;

let float64_sqrt_def = cake_def
  `float64_sqrt = lift_fp_uop FP_Sqrt`;;

let float64_sqrt_thm = prove
 (`float64_sqrt f1 = SND (float_sqrt roundTiesToEven f1)`,
  REWRITE_TAC[float64_sqrt_def; lift_fp_uop_def; fp_uop_comp_def] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[fp64_sqrt_def; o_THM; fp64_to_float_float_to_fp64]);;

let Eval_FLOAT_ABS = prove
 (`!f1. ml_Eval env x1 (ml_FLOAT64 f1) ==>
        ml_Eval env (App (Arith Abs Float64T) [x1]) (ml_FLOAT64 (float64_abs f1))`,
  TR2AUX_FLOAT_TAC THEN REWRITE_TAC[float64_abs_thm]);;

let Eval_FLOAT_NEG = prove
 (`!f1. ml_Eval env x1 (ml_FLOAT64 f1) ==>
        ml_Eval env (App (Arith Neg Float64T) [x1]) (ml_FLOAT64 (float64_neg f1))`,
  TR2AUX_FLOAT_TAC THEN REWRITE_TAC[float64_neg_thm]);;

let Eval_FLOAT_SQRT = prove
 (`!f1. ml_Eval env x1 (ml_FLOAT64 f1) ==>
        ml_Eval env (App (Arith Sqrt Float64T) [x1]) (ml_FLOAT64 (float64_sqrt f1))`,
  TR2AUX_FLOAT_TAC THEN REWRITE_TAC[float64_sqrt_thm]);;

let Eval_FP_fromWord = prove
 (`!w1. ml_Eval env x1 (ml_WORD (w1:int64)) ==>
        ml_Eval env (App (FromTo (WordT W64) Float64T) [x1]) (ml_FLOAT64 (fp64_to_float w1))`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC TR2AUX_Eval_App1 THEN
  EXISTS_TAC `ml_WORD (w1:int64)` THEN ASM_REWRITE_TAC[getOpClass_def] THEN
  CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[ml_FLOAT64_def; ml_WORD_def; DIMINDEX_64; ARITH_RULE `~(64 <= 8)`;
    SUB_REFL; WORD_SHL_ZERO; WORD_ZX_TRIVIAL] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[do_app_def] THEN CAKE_REWRITE_TAC[] THEN
  SIMP[check_type_def; do_conversion_def; the_Litv_Word64_def;
    injectivity "option"; PAIR_EQ; injectivity "result"; UNWIND_THM1]);;

let Eval_FP_toWord = prove
 (`!f1. ml_Eval env x1 (ml_FLOAT64 f1) ==>
        ml_Eval env (App (FromTo Float64T (WordT W64)) [x1]) (ml_WORD (float_to_fp64 f1))`,
  TR2AUX_FLOAT_TAC);;
(* list definition *)

let LIST_TYPE_def = cake_def
  `(LIST_TYPE (a:A->v->bool) (CONS x_2 x_1) v <=>
      ?v2_1 v2_2.
        v = Conv (SOME (TypeStamp (implode "::") 1)) [v2_1; v2_2] /\
        a x_2 v2_1 /\ LIST_TYPE a x_1 v2_2) /\
   (LIST_TYPE a [] v <=> v = Conv (SOME (TypeStamp (implode "[]") 1)) [])`;;

(* HOL4: LIST_TYPE_SIMP' is the GSYM of the proved statement *)

let LIST_TYPE_SIMP' = prove
 (`!xs b. LIST_TYPE (p:A->v->bool) xs =
          ml_CONTAINER LIST_TYPE (\x v. if b x \/ MEM x xs then p x v else ARB) xs`,
  REWRITE_TAC[ml_CONTAINER_def] THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; LIST_TYPE_def; MEM] THEN REPEAT GEN_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `\x:A. b x \/ x = h`) THEN
  REWRITE_TAC[FUN_EQ_THM; GSYM DISJ_ASSOC] THEN DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]));;

let LIST_TYPE_SIMP = REWRITE_RULE[]
  (ISPECL [`xs:A list`; `\x:A. F`] LIST_TYPE_SIMP');;

let LIST_TYPE_IF_ELIM = prove
 (`!v. LIST_TYPE (\x v. if MEM x l then P x v else Q x v) (l:A list) v = LIST_TYPE P l v`,
  SUBGOAL_THEN `!l' v. (!x:A. MEM x l ==> MEM x l') ==>
    LIST_TYPE (\x v. if MEM x l' then P x v else Q x v) l v = LIST_TYPE P l v`
    (fun th -> MESON_TAC[th]) THEN
  SPEC_TAC(`l:A list`,`l:A list`) THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LIST_TYPE_def; MEM] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `MEM (h:A) l'` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!v. LIST_TYPE (\x v. if MEM x l' then P x v else Q x v) t v <=>
                    LIST_TYPE P (t:A list) v` (fun th -> REWRITE_TAC[th]) THEN
  GEN_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]);;

let LIST_TYPE_mono = prove
 (`!P Q (l:A list) v.
     LIST_TYPE P l v /\ (!x v. MEM x l /\ P x v ==> Q x v) ==> LIST_TYPE Q l v`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LIST_TYPE_def; MEM] THEN ASM_MESON_TAC[]);;

let LIST_v_def = cake_def
  `(LIST_v (a_v:A->v) [] = Conv (SOME (TypeStamp (implode "[]") 1)) []) /\
   (LIST_v a_v (CONS x xs) =
      Conv (SOME (TypeStamp (implode "::") 1)) [a_v x; LIST_v a_v xs])`;;

let IsTypeRep_LIST = prove
 (`IsTypeRep (a_v:A->v) a ==> IsTypeRep (LIST_v a_v) (LIST_TYPE a)`,
  REWRITE_TAC[IsTypeRep_def] THEN DISCH_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[LIST_v_def; LIST_TYPE_def] THEN ASM_MESON_TAC[]);;

(* pair definition *)

let PAIR_TYPE_def = cake_def
  `PAIR_TYPE (a:A->v->bool) (b:B->v->bool) (x_2,x_1) v <=>
     ?v1_1 v1_2. v = Conv NONE [v1_1; v1_2] /\ a x_2 v1_1 /\ b x_1 v1_2`;;

let PAIR_TYPE_SIMP = prove
 (`PAIR_TYPE (a:A->v->bool) (b:B->v->bool) x =
   ml_CONTAINER PAIR_TYPE (\y v. if y = FST x then a y v else ARB)
                          (\y v. if y = SND x then b y v else ARB) x`,
  PAIR_CASES_ON `x:A#B` THEN
  REWRITE_TAC[PAIR_TYPE_def; ml_CONTAINER_def; FUN_EQ_THM; FST; SND]);;

let PAIR_v_def = cake_def
  `PAIR_v (a_v:A->v) (b_v:B->v) (x,y) = Conv NONE [a_v x; b_v y]`;;

let IsTypeRep_PAIR = prove
 (`IsTypeRep (a_v:A->v) a /\ IsTypeRep (b_v:B->v) b ==>
   IsTypeRep (PAIR_v a_v b_v) (PAIR_TYPE a b)`,
  REWRITE_TAC[IsTypeRep_def; FORALL_PAIR_THM; PAIR_v_def; PAIR_TYPE_def] THEN
  MESON_TAC[]);;
(* characters *)

let TR2AUX_CHAR_TAC =
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  FIRST [MATCH_MP_TAC TR2AUX_Eval_App1 THEN EXISTS_TAC `ml_CHAR c`;
         MATCH_MP_TAC TR2AUX_Eval_App2 THEN MAP_EVERY EXISTS_TAC [`ml_CHAR c1`; `ml_CHAR c2`]]
  THEN ASM_REWRITE_TAC[getOpClass_def] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[ml_CHAR_def; ml_BOOL_def; ml_NUM_def; ml_INT_def; ml_WORD_def; DIMINDEX_8;
    ARITH_RULE `8 <= 8 /\ 8 <= 64`; SUB_REFL; WORD_SHL_ZERO; WORD_ZX_TRIVIAL] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[do_app_def] THEN CAKE_REWRITE_TAC[] THEN
  SIMP[check_type_def; do_conversion_def; do_test_def; dest_Litv_def; num_cmp_def;
    the_Litv_Char_def; the_Litv_Word8_def; do_eq_def; lit_same_type_def;
    distinctness "prim_type"; injectivity "lit"; char_lt_def; char_le_def;
    injectivity "option"; PAIR_EQ; injectivity "result"; UNWIND_THM1];;

let Eval_Ord = prove
 (`ml_Eval env x (ml_CHAR c) ==>
   ml_Eval env (App (FromTo CharT IntT) [x]) (ml_NUM (ORD c))`,
  TR2AUX_CHAR_TAC);;

let Eval_Chr = prove
 (`ml_Eval env x (ml_NUM n) ==>
   n < 256 ==>
   ml_Eval env (App (FromTo IntT CharT) [x]) (ml_CHAR (CHR n))`,
  REPEAT DISCH_TAC THEN MATCH_MP_TAC TR2AUX_Eval_App1 THEN
  EXISTS_TAC `ml_NUM n` THEN ASM_REWRITE_TAC[getOpClass_def] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[ml_CHAR_def; ml_NUM_def; ml_INT_def] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[do_app_def] THEN CAKE_REWRITE_TAC[] THEN
  SIMP[check_type_def; do_conversion_def; the_Litv_IntLit_def; LET_DEF; LET_END_DEF;
    INT_ABS_NUM; NUM_OF_INT_OF_NUM; INT_OF_NUM_LT; INT_GT; INT_OF_NUM_LT] THEN
  SUBGOAL_THEN `~(n < 0) /\ ~(255 < n)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SIMP[injectivity "option"; PAIR_EQ; injectivity "result"; UNWIND_THM1]);;

let ml_Eval_char_to_word8 = prove
 (`ml_Eval env x (ml_CHAR c) ==>
   ml_Eval env (App (FromTo CharT (WordT W8)) [x]) (ml_WORD (char_to_word8 c))`,
  TR2AUX_CHAR_TAC);;

let ml_Eval_word8_to_char = prove
 (`ml_Eval env x (ml_WORD c) ==>
   ml_Eval env (App (FromTo (WordT W8) CharT) [x]) (ml_CHAR (word8_to_char c))`,
  DISCH_TAC THEN MATCH_MP_TAC TR2AUX_Eval_App1 THEN
  EXISTS_TAC `ml_WORD (c:byte)` THEN ASM_REWRITE_TAC[getOpClass_def] THEN
  CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[ml_CHAR_def; ml_WORD_def; DIMINDEX_8; ARITH_RULE `8 <= 8 /\ 8 <= 64`;
    SUB_REFL; WORD_SHL_ZERO; WORD_ZX_TRIVIAL] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[do_app_def] THEN CAKE_REWRITE_TAC[] THEN
  SIMP[check_type_def; do_conversion_def; the_Litv_Word8_def;
    injectivity "option"; PAIR_EQ; injectivity "result"; UNWIND_THM1]);;

(* HOL4: Boolv_11 (semanticPrimitivesProps has it too, quantified) *)

let ml_Boolv_11 = SPEC_ALL semanticPrimitivesProps_Boolv_11;;

let ml_Eval_char_lt = prove
 (`ml_Eval env x1 (ml_CHAR c1) ==>
   ml_Eval env x2 (ml_CHAR c2) ==>
   ml_Eval env (App (Test (Compare Lt) CharT) [x1;x2]) (ml_BOOL (char_lt c1 c2))`,
  TR2AUX_CHAR_TAC);;

let ml_Eval_char_le = prove
 (`ml_Eval env x1 (ml_CHAR c1) ==>
   ml_Eval env x2 (ml_CHAR c2) ==>
   ml_Eval env (App (Test (Compare Leq) CharT) [x1;x2]) (ml_BOOL (char_le c1 c2))`,
  TR2AUX_CHAR_TAC);;

let TR2AUX_char_gt_ge = prove
 (`!a b. (char_gt a b <=> char_lt b a) /\ (char_ge a b <=> char_le b a)`,
  REWRITE_TAC[char_gt_def; char_ge_def; char_lt_def; char_le_def; GT; GE]);;

let ml_Eval_char_gt =
  REWRITE_RULE[GSYM IMP_IMP]
   (ONCE_REWRITE_RULE[CONJ_COMM]
     (REWRITE_RULE[IMP_IMP; GSYM TR2AUX_char_gt_ge]
       (INST [`x2:exp`,`x1:exp`; `x1:exp`,`x2:exp`; `c2:char`,`c1:char`;
              `c1:char`,`c2:char`] ml_Eval_char_lt)));;

let ml_Eval_char_ge =
  REWRITE_RULE[GSYM IMP_IMP]
   (ONCE_REWRITE_RULE[CONJ_COMM]
     (REWRITE_RULE[IMP_IMP; GSYM TR2AUX_char_gt_ge]
       (INST [`x2:exp`,`x1:exp`; `x1:exp`,`x2:exp`; `c2:char`,`c1:char`;
              `c1:char`,`c2:char`] ml_Eval_char_le)));;

let ml_Eval_char_eq = prove
 (`ml_Eval env x1 (ml_CHAR c1) ==>
   ml_Eval env x2 (ml_CHAR c2) ==>
   ml_Eval env (App (Test Equal CharT) [x1; x2]) (ml_BOOL (c1 = c2))`,
  TR2AUX_CHAR_TAC);;
(* strings *)

let LIST_TYPE_CHAR_v_to_char_list = prove
 (`!l v. LIST_TYPE ml_CHAR l v ==> v_to_char_list v = SOME l`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LIST_TYPE_def; ml_CHAR_def] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[v_to_char_list_def; list_type_num_def] THEN
  RES_TAC THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[]);;

(* HOL4: the local tac1 and tac2 (one and two operands) *)

let TR2AUX_STR_TAC thl =
  REPEAT STRIP_TAC THEN
  FIRST [MATCH_MP_TAC TR2AUX_Eval_App3;
         MATCH_MP_TAC TR2AUX_Eval_App2;
         MATCH_MP_TAC TR2AUX_Eval_App1] THEN
  ASM_EXISTS_TAC THEN ASM_REWRITE_TAC[getOpClass_def] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[STRING_TYPE_def; ml_CHAR_def; ml_BOOL_def; ml_NUM_def; ml_INT_def] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[do_app_def] THEN CAKE_REWRITE_TAC[] THEN
  SIMP(thl @ [ARITH_ss; check_type_def; do_test_def; dest_Litv_def; do_eq_def; lit_same_type_def;
    distinctness "prim_type"; injectivity "lit"; LET_DEF; LET_END_DEF; I_THM;
    INT_ABS_NUM; NUM_OF_INT_OF_NUM; INT_OF_NUM_LT; INT_LT_REFL; GE; str_cmp_def;
    injectivity "option"; PAIR_EQ; injectivity "result"; UNWIND_THM1]);;

let ml_Eval_implode = prove
 (`!env x1 l.
     ml_Eval env x1 (LIST_TYPE ml_CHAR l) ==>
     ml_Eval env (App Implode [x1]) (STRING_TYPE (implode l))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC TR2AUX_Eval_App1 THEN
  EXISTS_TAC `LIST_TYPE ml_CHAR l` THEN ASM_REWRITE_TAC[getOpClass_def] THEN
  CAKE_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP LIST_TYPE_CHAR_v_to_char_list) THEN
  REWRITE_TAC[do_app_def] THEN CAKE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  CAKE_REWRITE_TAC[] THEN
  SIMP[STRING_TYPE_def; injectivity "option"; PAIR_EQ; injectivity "result";
    UNWIND_THM1]);;

let TR2AUX_LIST_TYPE_CHAR_list_to_v = prove
 (`!l. LIST_TYPE ml_CHAR l (list_to_v (MAP (\c. Litv (Char c)) l))`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[MAP; list_to_v_def; LIST_TYPE_def; ml_CHAR_def; list_type_num_def;
    injectivity "v"; CONS_11] THEN
  ASM_MESON_TAC[]);;

(* HOL4 quantifies a variable l that the statement does not use *)

let ml_Eval_explode = prove
 (`!env x1 (l:A).
     ml_Eval env x1 (STRING_TYPE s) ==>
     ml_Eval env (App Explode [x1]) (LIST_TYPE ml_CHAR (explode s))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC TR2AUX_Eval_App1 THEN
  EXISTS_TAC `STRING_TYPE s` THEN ASM_REWRITE_TAC[getOpClass_def] THEN
  CAKE_REWRITE_TAC[] THEN REWRITE_TAC[STRING_TYPE_def] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[do_app_def] THEN CAKE_REWRITE_TAC[] THEN
  SIMP[TR2AUX_LIST_TYPE_CHAR_list_to_v; injectivity "option"; PAIR_EQ;
    injectivity "result"; UNWIND_THM1]);;

let ml_Eval_strlen = prove
 (`!env x1 s.
     ml_Eval env x1 (STRING_TYPE s) ==>
     ml_Eval env (App Strlen [x1]) (ml_NUM (strlen s))`,
  TR2AUX_STR_TAC[]);;

let ml_Eval_strsub = prove
 (`!env x1 x2 s n.
     ml_Eval env x1 (STRING_TYPE s) ==>
     ml_Eval env x2 (ml_NUM n) ==>
     n < strlen s ==>
     ml_Eval env (App Strsub [x1; x2]) (ml_CHAR (strsub s n))`,
  REPEAT GEN_TAC THEN MP_TAC(ISPEC `s:mlstring` (cases "mlstring")) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[strlen_def; strsub_def] THEN
  TR2AUX_STR_TAC[explode_implode; NOT_LE; strlen_def]);;

let TR2AUX_LIST_TYPE_STRING_concat = prove
 (`!ls v. LIST_TYPE STRING_TYPE ls v ==>
          ?vs. v_to_list v = SOME vs /\ vs_to_string vs = SOME (mlstring_concat ls)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LIST_TYPE_def; STRING_TYPE_def] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[v_to_list_def; list_type_num_def] THENL
   [CAKE_REWRITE_TAC[] THEN REWRITE_TAC[injectivity "option"; UNWIND_THM1; vs_to_string_def;
      concat_nil];
    FIRST_X_ASSUM(fun th -> FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP th)) THEN
    ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
    REWRITE_TAC[injectivity "option"; UNWIND_THM1; vs_to_string_def] THEN
    ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN REWRITE_TAC[concat_cons]]);;

let ml_Eval_concat = prove
 (`!env x ls.
     ml_Eval env x (LIST_TYPE STRING_TYPE ls) ==>
     ml_Eval env (App Strcat [x]) (STRING_TYPE (mlstring_concat ls))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC TR2AUX_Eval_App1 THEN
  EXISTS_TAC `LIST_TYPE STRING_TYPE ls` THEN ASM_REWRITE_TAC[getOpClass_def] THEN
  CAKE_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP TR2AUX_LIST_TYPE_STRING_concat) THEN
  REWRITE_TAC[do_app_def] THEN CAKE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  CAKE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  SIMP[STRING_TYPE_def; injectivity "option"; PAIR_EQ; injectivity "result";
    UNWIND_THM1]);;

let ml_Eval_substring = prove
 (`!env x1 x2 x3 len off st.
     ml_Eval env x1 (STRING_TYPE st) ==>
     ml_Eval env x2 (ml_NUM off) ==>
     ml_Eval env x3 (ml_NUM len) ==>
     off + len <= strlen st ==>
     ml_Eval env (App CopyStrStr [x1; x2; x3]) (STRING_TYPE (substring st off len))`,
  REPEAT GEN_TAC THEN MP_TAC(ISPEC `st:mlstring` (cases "mlstring")) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[strlen_def; substring_def] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC TR2AUX_Eval_App3 THEN
  MAP_EVERY EXISTS_TAC [`STRING_TYPE (implode a)`; `ml_NUM off`; `ml_NUM len`] THEN
  ASM_REWRITE_TAC[getOpClass_def] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[STRING_TYPE_def; ml_NUM_def; ml_INT_def] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[do_app_def] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[copy_array_def; explode_implode; I_THM; INT_OF_NUM_ADD; INT_ABS_NUM;
    NUM_OF_INT_OF_NUM; INT_OF_NUM_LT; LT; LET_DEF; LET_END_DEF] THEN
  SUBGOAL_THEN `len + off <= LENGTH (a:string)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[ARITH_RULE `a <= b ==> ~(b < a)`; SEG_TAKE_DROP] THEN
  CAKE_REWRITE_TAC[] THEN
  SIMP[injectivity "option"; PAIR_EQ; injectivity "result"; UNWIND_THM1]);;

(* HOL4: the local str_cmp_tac *)

let TR2AUX_STR_CMP_TAC =
  REPEAT STRIP_TAC THEN MATCH_MP_TAC TR2AUX_Eval_App2 THEN
  MAP_EVERY EXISTS_TAC [`STRING_TYPE s1`; `STRING_TYPE s2`] THEN
  ASM_REWRITE_TAC[getOpClass_def] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[STRING_TYPE_def; ml_BOOL_def] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[do_app_def] THEN CAKE_REWRITE_TAC[] THEN
  SIMP[check_type_def; do_test_def; dest_Litv_def; do_eq_def; lit_same_type_def;
    distinctness "prim_type"; injectivity "lit"; str_cmp_def;
    injectivity "option"; PAIR_EQ; injectivity "result"; UNWIND_THM1];;

let ml_Eval_str_eq = prove
 (`ml_Eval env x1 (STRING_TYPE s1) ==>
   ml_Eval env x2 (STRING_TYPE s2) ==>
   ml_Eval env (App (Test Equal StrT) [x1; x2]) (ml_BOOL (s1 = s2))`,
  TR2AUX_STR_CMP_TAC);;

let ml_Eval_mlstring_lt = prove
 (`ml_Eval env x1 (STRING_TYPE s1) ==>
   ml_Eval env x2 (STRING_TYPE s2) ==>
   ml_Eval env (App (Test (Compare Lt) StrT) [x1; x2]) (ml_BOOL (mlstring_lt s1 s2))`,
  TR2AUX_STR_CMP_TAC);;

let ml_Eval_mlstring_le = prove
 (`ml_Eval env x1 (STRING_TYPE s1) ==>
   ml_Eval env x2 (STRING_TYPE s2) ==>
   ml_Eval env (App (Test (Compare Leq) StrT) [x1; x2]) (ml_BOOL (mlstring_le s1 s2))`,
  TR2AUX_STR_CMP_TAC);;

let ml_Eval_mlstring_gt = prove
 (`ml_Eval env x1 (STRING_TYPE s1) ==>
   ml_Eval env x2 (STRING_TYPE s2) ==>
   ml_Eval env (App (Test (Compare Gt) StrT) [x1; x2]) (ml_BOOL (mlstring_gt s1 s2))`,
  TR2AUX_STR_CMP_TAC);;

let ml_Eval_mlstring_ge = prove
 (`ml_Eval env x1 (STRING_TYPE s1) ==>
   ml_Eval env x2 (STRING_TYPE s2) ==>
   ml_Eval env (App (Test (Compare Geq) StrT) [x1; x2]) (ml_BOOL (mlstring_ge s1 s2))`,
  TR2AUX_STR_CMP_TAC);;

let ml_Eval_fast_lt = prove
 (`ml_Eval env x1 (STRING_TYPE s1) ==>
   ml_Eval env x2 (STRING_TYPE s2) ==>
   ml_Eval env (App (Test (AltCompare Lt) StrT) [x1; x2]) (ml_BOOL (fast_lt s1 s2))`,
  TR2AUX_STR_CMP_TAC);;

let ml_Eval_fast_le = prove
 (`ml_Eval env x1 (STRING_TYPE s1) ==>
   ml_Eval env x2 (STRING_TYPE s2) ==>
   ml_Eval env (App (Test (AltCompare Leq) StrT) [x1; x2]) (ml_BOOL (fast_le s1 s2))`,
  TR2AUX_STR_CMP_TAC);;

let ml_Eval_fast_gt = prove
 (`ml_Eval env x1 (STRING_TYPE s1) ==>
   ml_Eval env x2 (STRING_TYPE s2) ==>
   ml_Eval env (App (Test (AltCompare Gt) StrT) [x1; x2]) (ml_BOOL (fast_gt s1 s2))`,
  TR2AUX_STR_CMP_TAC);;

let ml_Eval_fast_ge = prove
 (`ml_Eval env x1 (STRING_TYPE s1) ==>
   ml_Eval env x2 (STRING_TYPE s2) ==>
   ml_Eval env (App (Test (AltCompare Geq) StrT) [x1; x2]) (ml_BOOL (fast_ge s1 s2))`,
  TR2AUX_STR_CMP_TAC);;
(* HOL4's Eval_Con_lemma, Eval_Con and Eval_Con_NONE (below) for the       *)
(* string lemmas: helpers with the same statements, proved here            *)

let TR2AUX_Eval_list = prove
 (`!ps env R.
     (!p x. MEM (p,x) ps ==> ml_Eval env x p) ==>
     ?R' vals.
       (!ck. ?ck1.
          evaluate (state_clock_fupd (combin_K ck1) (state_refs_fupd (combin_K R) ml_empty_state))
            env (MAP SND ps) =
          (state_clock_fupd (combin_K ck) (state_refs_fupd (combin_K (APPEND R R')) ml_empty_state),
           Rval vals)) /\
       ALL2 (\(p,x) v. p v) ps vals`,
  LIST_INDUCT_TAC THENL
   [REPEAT STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`[]:(v store_v)list`; `[]:v list`] THEN
    REWRITE_TAC[MAP; APPEND_NIL; ALL2; TR2AUX_EV_NIL];
    ALL_TAC] THEN
  PAIR_CASES_ON `h:(v->bool)#exp` THEN REWRITE_TAC[MEM; MAP; ALL2] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ml_Eval env h1 h0` MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[TR2AUX_Eval_any_clock] THEN
  DISCH_THEN(X_CHOOSE_THEN `v1:v` (X_CHOOSE_THEN `r1:(v store_v)list`
    STRIP_ASSUME_TAC) o SPEC `R:(v store_v)list`) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`env:v sem_env`; `APPEND R r1:(v store_v)list`]) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r2:(v store_v)list` (X_CHOOSE_THEN `vs:v list`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`APPEND r1 r2:(v store_v)list`; `CONS (v1:v) vs`] THEN
  ASM_REWRITE_TAC[ALL2; APPEND_ASSOC] THEN
  MATCH_MP_TAC TR2AUX_EV_CONS THEN EXISTS_TAC `APPEND R r1:(v store_v)list` THEN
  ASM_REWRITE_TAC[]);;

let TR2AUX_EV_CON = prove
 (`!env cn es R R1 vs v.
     (!ck. ?ck1.
        evaluate (state_clock_fupd (combin_K ck1) (state_refs_fupd (combin_K R) ml_empty_state))
          env (REVERSE es) =
        (state_clock_fupd (combin_K ck) (state_refs_fupd (combin_K R1) ml_empty_state),Rval vs)) /\
     do_con_check (sem_env_c env) cn (LENGTH es) /\
     build_conv (sem_env_c env) cn (REVERSE vs) = SOME v ==>
     !ck. ?ck1.
        evaluate (state_clock_fupd (combin_K ck1) (state_refs_fupd (combin_K R) ml_empty_state))
          env [Con cn es] =
        (state_clock_fupd (combin_K ck) (state_refs_fupd (combin_K R1) ml_empty_state),Rval [v])`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "h1") STRIP_ASSUME_TAC) THEN
  X_GEN_TAC `ck:num` THEN
  REMOVE_THEN "h1" (X_CHOOSE_TAC `c1:num` o SPEC `ck:num`) THEN
  EXISTS_TAC `c1:num` THEN REWRITE_TAC[evaluate_def] THEN TR2AUX_RED_TAC[]);;

let TR2AUX_Eval_Con = prove
 (`!ps stamp.
     ml_lookup_cons name env = SOME (LENGTH ps,stamp) /\
     ALL (\(p,x). ml_Eval env x p) ps /\
     (!vals. ALL2 (\(p,x) v. p v) ps vals ==> q (Conv (SOME stamp) vals)) ==>
     ml_Eval env (Con (SOME name) (MAP SND ps)) q`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[TR2AUX_Eval_any_clock] THEN
  X_GEN_TAC `refs:(v store_v)list` THEN
  MP_TAC(ISPECL [`REVERSE ps:((v->bool)#exp)list`; `env:v sem_env`;
    `refs:(v store_v)list`] TR2AUX_Eval_list) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[MEM_REVERSE] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(p,x):(v->bool)#exp` o REWRITE_RULE[GSYM ALL_MEM]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:(v store_v)list` (X_CHOOSE_THEN `vals:v list`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`Conv (SOME stamp) (REVERSE vals)`; `r:(v store_v)list`] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[EVERY2_REVERSE1]; ALL_TAC] THEN
  MATCH_MP_TAC TR2AUX_EV_CON THEN EXISTS_TAC `vals:v list` THEN
  ASM_REWRITE_TAC[MAP_REVERSE; REVERSE_REVERSE] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ml_lookup_cons_def]) THEN
  TR2AUX_RED_TAC[do_con_check_def; build_conv_def; LENGTH_MAP]);;

let TR2AUX_Eval_Con_NONE = prove
 (`!ps.
     ALL (\(p,x). ml_Eval env x p) ps /\
     (!vals. ALL2 (\(p,x) v. p v) ps vals ==> q (Conv NONE vals)) ==>
     ml_Eval env (Con NONE (MAP SND ps)) q`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[TR2AUX_Eval_any_clock] THEN
  X_GEN_TAC `refs:(v store_v)list` THEN
  MP_TAC(ISPECL [`REVERSE ps:((v->bool)#exp)list`; `env:v sem_env`;
    `refs:(v store_v)list`] TR2AUX_Eval_list) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[MEM_REVERSE] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(p,x):(v->bool)#exp` o REWRITE_RULE[GSYM ALL_MEM]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:(v store_v)list` (X_CHOOSE_THEN `vals:v list`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`Conv NONE (REVERSE vals)`; `r:(v store_v)list`] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[EVERY2_REVERSE1]; ALL_TAC] THEN
  MATCH_MP_TAC TR2AUX_EV_CON THEN EXISTS_TAC `vals:v list` THEN
  ASM_REWRITE_TAC[MAP_REVERSE; REVERSE_REVERSE] THEN
  REWRITE_TAC[do_con_check_def; build_conv_def] THEN CAKE_REWRITE_TAC[]);;

(* char list as string *)

let ml_Eval_implode_nop = prove
 (`ml_Eval env x (HOL_STRING_TYPE cs) ==> ml_Eval env x (STRING_TYPE (implode cs))`,
  REWRITE_TAC[HOL_STRING_TYPE_def]);;

let Eval_HOL_STRING_explode = prove
 (`ml_Eval env x (STRING_TYPE s) ==> ml_Eval env x (HOL_STRING_TYPE (explode s))`,
  REWRITE_TAC[HOL_STRING_TYPE_def; implode_explode]);;

let Eval_HOL_STRING_INTRO = prove
 (`ml_Eval env x (LIST_TYPE ml_CHAR cs) ==>
   ml_Eval env (App Implode [x]) (HOL_STRING_TYPE cs)`,
  REWRITE_TAC[HOL_STRING_TYPE_def; ml_Eval_implode]);;

let Eval_HOL_STRING_DEST = prove
 (`ml_Eval env x (HOL_STRING_TYPE cs) ==>
   ml_Eval env (App Explode [x]) (LIST_TYPE ml_CHAR cs)`,
  REWRITE_TAC[HOL_STRING_TYPE_def] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (INST_TYPE [`:num`,`:A`] ml_Eval_explode)) THEN
  REWRITE_TAC[explode_implode]);;

let Eval_HOL_STRING_LENGTH = prove
 (`!env x1 s.
     ml_Eval env x1 (HOL_STRING_TYPE s) ==>
     ml_Eval env (App Strlen [x1]) (ml_NUM (LENGTH s))`,
  REWRITE_TAC[HOL_STRING_TYPE_def] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP ml_Eval_strlen) THEN REWRITE_TAC[strlen_def]);;

let Eval_HOL_STRING_EL = prove
 (`!env x1 x2 s n.
     ml_Eval env x2 (ml_NUM n) ==>
     ml_Eval env x1 (HOL_STRING_TYPE s) ==>
     n < LENGTH s ==>
     ml_Eval env (App Strsub [x1; x2]) (ml_CHAR (EL n s))`,
  REWRITE_TAC[HOL_STRING_TYPE_def] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`env:v sem_env`; `x1:exp`; `x2:exp`; `implode s`; `n:num`]
    ml_Eval_strsub) THEN
  ASM_REWRITE_TAC[strlen_def; strsub_def]);;

let Eval_HOL_STRING_HD = prove
 (`!env x1 s (n:A).
     ml_Eval env x1 (HOL_STRING_TYPE s) ==>
     ~(s = []) ==>
     ml_Eval env (App Strsub [x1; Lit (IntLit (&0))]) (ml_CHAR (HD s))`,
  REPEAT STRIP_TAC THEN SUBGOAL_THEN `HD s = EL 0 (s:string)` SUBST1_TAC THENL
   [REWRITE_TAC[EL]; ALL_TAC] THEN
  MATCH_MP_TAC (TR2AUX_MP_CANON Eval_HOL_STRING_EL) THEN
  ASM_REWRITE_TAC[Eval_Val_NUM; LT_NZ; LENGTH_EQ_NIL]);;

(* the list constructors (the translator makes these from Eval_Con) *)

let TR2AUX_Eval_nil = prove
 (`!env c (a:A->v->bool).
     ml_lookup_cons c env = SOME (0,TypeStamp (implode "[]") 1) ==>
     ml_Eval env (Con (SOME c) []) (LIST_TYPE a [])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`[]:((v->bool)#exp)list`; `TypeStamp (implode "[]") 1`]
    (INST [`c:(mlstring,mlstring)id`,`name:(mlstring,mlstring)id`;
           `LIST_TYPE (a:A->v->bool) []`,`q:v->bool`] TR2AUX_Eval_Con)) THEN
  ASM_REWRITE_TAC[LENGTH; ALL; MAP; LIST_TYPE_def] THEN DISCH_THEN MATCH_MP_TAC THEN
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `vals:v list` list_CASES) THEN REWRITE_TAC[ALL2]);;

let TR2AUX_Eval_cons = prove
 (`!env c x1 x2 (a:A->v->bool) h t.
     ml_lookup_cons c env = SOME (2,TypeStamp (implode "::") 1) ==>
     ml_Eval env x1 (a h) ==> ml_Eval env x2 (LIST_TYPE a t) ==>
     ml_Eval env (Con (SOME c) [x1; x2]) (LIST_TYPE a (CONS h t))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`[(a:A->v->bool) h,x1:exp; LIST_TYPE a t,x2]`;
    `TypeStamp (implode "::") 1`]
    (INST [`c:(mlstring,mlstring)id`,`name:(mlstring,mlstring)id`;
           `LIST_TYPE (a:A->v->bool) (CONS h t)`,`q:v->bool`] TR2AUX_Eval_Con)) THEN
  ASM_REWRITE_TAC[LENGTH; ALL; MAP; ARITH] THEN DISCH_THEN MATCH_MP_TAC THEN
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `vals:v list` list_CASES) THEN REWRITE_TAC[ALL2] THEN
  STRUCT_CASES_TAC (ISPEC `t':v list` list_CASES) THEN REWRITE_TAC[ALL2] THEN
  STRUCT_CASES_TAC (ISPEC `t'':v list` list_CASES) THEN REWRITE_TAC[ALL2] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIST_TYPE_def] THEN ASM_MESON_TAC[]);;

let Eval_HOL_STRING_APPEND = prove
 (`!env x1 x2 s1 s2 (n:A).
     ml_Eval env x1 (HOL_STRING_TYPE s1) ==>
     ml_Eval env x2 (HOL_STRING_TYPE s2) ==>
     ml_lookup_cons (Short (implode "::")) env = SOME (2,TypeStamp (implode "::") 1) /\
     ml_lookup_cons (Short (implode "[]")) env = SOME (0,TypeStamp (implode "[]") 1) ==>
     ml_Eval env
       (App Strcat [Con (SOME (Short (implode "::")))
                     [x1; Con (SOME (Short (implode "::")))
                            [x2; Con (SOME (Short (implode "[]"))) []]]])
       (HOL_STRING_TYPE (APPEND s1 s2))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `HOL_STRING_TYPE (APPEND s1 s2) =
                STRING_TYPE (mlstring_concat [implode s1; implode s2])` SUBST1_TAC THENL
   [REWRITE_TAC[HOL_STRING_TYPE_def; concat_thm; MAP; explode_implode; FLAT; APPEND_NIL];
    ALL_TAC] THEN
  MATCH_MP_TAC ml_Eval_concat THEN
  REPEAT(MATCH_MP_TAC (TR2AUX_MP_CANON TR2AUX_Eval_cons) THEN
         ASM_REWRITE_TAC[GSYM HOL_STRING_TYPE_def]) THEN
  MATCH_MP_TAC TR2AUX_Eval_nil THEN ASM_REWRITE_TAC[]);;

let Eval_HOL_STRING_CONS = prove
 (`!env x1 x2 c s (n:A).
     ml_Eval env x1 (ml_CHAR c) ==>
     ml_Eval env x2 (HOL_STRING_TYPE s) ==>
     ml_lookup_cons (Short (implode "::")) env = SOME (2,TypeStamp (implode "::") 1) /\
     ml_lookup_cons (Short (implode "[]")) env = SOME (0,TypeStamp (implode "[]") 1) ==>
     ml_Eval env
       (App Strcat [Con (SOME (Short (implode "::")))
                     [App Implode [Con (SOME (Short (implode "::")))
                                    [x1; Con (SOME (Short (implode "[]"))) []]];
                      Con (SOME (Short (implode "::")))
                        [x2; Con (SOME (Short (implode "[]"))) []]]])
       (HOL_STRING_TYPE (CONS c s))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `CONS (c:char) s = APPEND [c] s` SUBST1_TAC THENL
   [REWRITE_TAC[APPEND]; ALL_TAC] THEN
  MATCH_MP_TAC (TR2AUX_MP_CANON (INST_TYPE [`:A`,`:A`] Eval_HOL_STRING_APPEND)) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC Eval_HOL_STRING_INTRO THEN
  MATCH_MP_TAC (TR2AUX_MP_CANON TR2AUX_Eval_cons) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC TR2AUX_Eval_nil THEN ASM_REWRITE_TAC[]);;

let TR2AUX_LIST_TYPE_HOL_STRING = prove
 (`!ls. LIST_TYPE HOL_STRING_TYPE ls = LIST_TYPE STRING_TYPE (MAP implode ls)`,
  REWRITE_TAC[FUN_EQ_THM] THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[LIST_TYPE_def; MAP; HOL_STRING_TYPE_def]);;

let Eval_HOL_STRING_FLAT = prove
 (`!env x ls.
     ml_Eval env x (LIST_TYPE HOL_STRING_TYPE ls) ==>
     ml_Eval env (App Strcat [x]) (HOL_STRING_TYPE (FLAT ls))`,
  REWRITE_TAC[TR2AUX_LIST_TYPE_HOL_STRING] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP ml_Eval_concat) THEN
  SUBGOAL_THEN `MAP explode (MAP implode ls) = ls` ASSUME_TAC THENL
   [SPEC_TAC(`ls:string list`,`ls:string list`) THEN LIST_INDUCT_TAC THEN
    ASM_REWRITE_TAC[MAP; explode_implode];
    ASM_REWRITE_TAC[HOL_STRING_TYPE_def; concat_thm]]);;

let Eval_HOL_STRING_IMPLODE = prove
 (`!env x1 s.
     ml_Eval env x1 (LIST_TYPE ml_CHAR s) ==>
     ml_Eval env (App Implode [x1]) (HOL_STRING_TYPE (IMPLODE s))`,
  REWRITE_TAC[IMPLODE_EXPLODE_I; Eval_HOL_STRING_INTRO]);;

let Eval_HOL_STRING_EXPLODE = prove
 (`!env x1 s.
     ml_Eval env x1 (HOL_STRING_TYPE s) ==>
     ml_Eval env (App Explode [x1]) (LIST_TYPE ml_CHAR (EXPLODE s))`,
  REWRITE_TAC[IMPLODE_EXPLODE_I; Eval_HOL_STRING_DEST]);;

let Eval_HOL_STRING_LITERAL = prove
 (`!s. ml_Eval env (Lit (StrLit (implode s))) (HOL_STRING_TYPE s)`,
  REWRITE_TAC[HOL_STRING_TYPE_def; Eval_Val_STRING]);;
(* vectors (HOL4 sub and length are regexp_compiler_sub and              *)
(* regexp_compiler_length, see basis/pure/mlvector.ml)                       *)

let VECTOR_TYPE_def = cake_def
  `VECTOR_TYPE (a:A->v->bool) (Vector l) v <=>
     ?l'. v = Vectorv l' /\ LENGTH l = LENGTH l' /\ ALL2 a l l'`;;

let VECTOR_v_def = cake_def
  `VECTOR_v (v_a:A->v) (Vector l) = Vectorv (MAP v_a l)`;;

let IsTypeRep_VECTOR = prove
 (`IsTypeRep (v_a:A->v) a ==> IsTypeRep (VECTOR_v v_a) (VECTOR_TYPE a)`,
  REWRITE_TAC[IsTypeRep_def] THEN DISCH_TAC THEN MATCH_MP_TAC vector_INDUCT THEN
  REWRITE_TAC[VECTOR_TYPE_def; VECTOR_v_def; injectivity "v"; UNWIND_THM1; LENGTH_MAP] THEN
  REWRITE_TAC[ALL2_MAP2] THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; ALL2]);;

let ml_Eval_sub = prove
 (`!env x1 x2 a n v.
     ml_Eval env x1 (VECTOR_TYPE a v) ==>
     ml_Eval env x2 (ml_NUM n) ==>
     n < regexp_compiler_length v ==>
     ml_Eval env (App Vsub [x1; x2]) ((a:A->v->bool) (regexp_compiler_sub v n))`,
  REPEAT GEN_TAC THEN MP_TAC(ISPEC `v:A vector` vector_nchotomy) THEN
  DISCH_THEN(X_CHOOSE_THEN `l:A list` SUBST1_TAC) THEN
  REWRITE_TAC[regexp_compiler_length_def; regexp_compiler_sub_def] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC TR2AUX_Eval_App2 THEN
  MAP_EVERY EXISTS_TAC [`VECTOR_TYPE (a:A->v->bool) (Vector l)`; `ml_NUM n`] THEN
  ASM_REWRITE_TAC[getOpClass_def] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[VECTOR_TYPE_def; ml_NUM_def; ml_INT_def] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[do_app_def] THEN CAKE_REWRITE_TAC[] THEN
  SIMP[ARITH_ss; LET_DEF; LET_END_DEF; I_THM; INT_ABS_NUM; NUM_OF_INT_OF_NUM; INT_OF_NUM_LT;
    GE; injectivity "option"; PAIR_EQ; injectivity "result"; UNWIND_THM1] THEN
  REWRITE_TAC[INT_ARITH `~(&n:int < &0)`] THEN
  ASM_MESON_TAC[LIST_REL_EL_EQN]);;

let ml_Eval_sub_unsafe = prove
 (`!env x1 x2 a n v.
     ml_Eval env x1 (VECTOR_TYPE a v) ==>
     ml_Eval env x2 (ml_NUM n) ==>
     n < regexp_compiler_length v ==>
     ml_Eval env (App Vsub_unsafe [x1; x2]) ((a:A->v->bool) (sub_unsafe v n))`,
  REPEAT GEN_TAC THEN MP_TAC(ISPEC `v:A vector` vector_nchotomy) THEN
  DISCH_THEN(X_CHOOSE_THEN `l:A list` SUBST1_TAC) THEN
  REWRITE_TAC[regexp_compiler_length_def; sub_unsafe_def] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC TR2AUX_Eval_App2 THEN
  MAP_EVERY EXISTS_TAC [`VECTOR_TYPE (a:A->v->bool) (Vector l)`; `ml_NUM n`] THEN
  ASM_REWRITE_TAC[getOpClass_def] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[VECTOR_TYPE_def; ml_NUM_def; ml_INT_def] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[do_app_def] THEN CAKE_REWRITE_TAC[] THEN
  SIMP[ARITH_ss; INT_POS; NUM_OF_INT_OF_NUM;
    injectivity "option"; PAIR_EQ; injectivity "result"; UNWIND_THM1] THEN
  ASM_MESON_TAC[LIST_REL_EL_EQN]);;

let ml_Eval_vector = prove
 (`!env x1 a l.
     ml_Eval env x1 (LIST_TYPE a l) ==>
     ml_Eval env (App VfromList [x1]) (VECTOR_TYPE (a:A->v->bool) (Vector l))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC TR2AUX_Eval_App1 THEN
  EXISTS_TAC `LIST_TYPE (a:A->v->bool) l` THEN ASM_REWRITE_TAC[getOpClass_def] THEN
  CAKE_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[do_app_def] THEN CAKE_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!l v. LIST_TYPE (a:A->v->bool) l v ==>
      ?vs. v_to_list v = SOME vs /\ LENGTH l = LENGTH vs /\ ALL2 a l vs`
    (fun th -> FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP th)) THENL
   [LIST_INDUCT_TAC THEN REWRITE_TAC[LIST_TYPE_def] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[v_to_list_def; list_type_num_def] THENL
     [EXISTS_TAC `[]:v list` THEN REWRITE_TAC[LENGTH; ALL2];
      FIRST_X_ASSUM(fun th -> FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP th)) THEN
      ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
      EXISTS_TAC `CONS (v2_1:v) vs` THEN ASM_REWRITE_TAC[LENGTH; ALL2]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  SIMP[VECTOR_TYPE_def; injectivity "option"; PAIR_EQ; injectivity "result";
    UNWIND_THM1] THEN ASM_MESON_TAC[]);;

let list_to_v_LIST_TYPE = prove
 (`!xs v ys.
     LIST_TYPE (a:A->v->bool) xs v /\ v_to_list v = SOME ys ==>
     LIST_TYPE a xs (list_to_v ys)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LIST_TYPE_def] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  REWRITE_TAC[v_to_list_def; list_type_num_def] THEN CAKE_REWRITE_TAC[] THENL
   [DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[list_to_v_def; list_type_num_def];
    CASES_ON `v_to_list v2_2` THEN CAKE_REWRITE_TAC[] THEN
    REWRITE_TAC[injectivity "option"; distinctness "option"] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[list_to_v_def; list_type_num_def; injectivity "v"; CONS_11] THEN
    ASM_MESON_TAC[]]);;
(* ListAppend theorems *)

let list_to_v_LIST_TYPE_APPEND = prove
 (`!xs ys x y.
     LIST_TYPE (a:A->v->bool) x (list_to_v xs) /\ LIST_TYPE a y (list_to_v ys) ==>
     LIST_TYPE a (APPEND x y) (list_to_v (APPEND xs ys))`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `x:A list` list_CASES) THEN
  REWRITE_TAC[list_to_v_def; LIST_TYPE_def; APPEND; list_type_num_def; injectivity "v";
    injectivity "option"; injectivity "stamp"; injectivity "mlstring"; CONS_11;
    distinctness "list"] THEN
  SIMP[] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_MESON_TAC[]);;

let v_to_list_LIST_TYPE = prove
 (`!x v. LIST_TYPE (a:A->v->bool) x v ==> ?xs. v_to_list v = SOME xs`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LIST_TYPE_def] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[v_to_list_def; list_type_num_def] THEN
  RES_TAC THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN MESON_TAC[]);;

let Eval_ListAppend = prove
 (`!env x1 x2 a l1 l2.
     ml_Eval env x2 (LIST_TYPE a l1) ==>
     ml_Eval env x1 (LIST_TYPE a l2) ==>
     ml_Eval env (App ListAppend [x2;x1]) (LIST_TYPE (a:A->v->bool) (APPEND l1 l2))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC TR2AUX_Eval_App2 THEN
  MAP_EVERY EXISTS_TAC [`LIST_TYPE (a:A->v->bool) l1`; `LIST_TYPE (a:A->v->bool) l2`] THEN
  ASM_REWRITE_TAC[getOpClass_def] THEN CAKE_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[do_app_def] THEN CAKE_REWRITE_TAC[] THEN
  X_CHOOSE_TAC `xs:v list` (MATCH_MP v_to_list_LIST_TYPE
    (ASSUME `LIST_TYPE (a:A->v->bool) l1 v1`)) THEN
  X_CHOOSE_TAC `ys:v list` (MATCH_MP v_to_list_LIST_TYPE
    (ASSUME `LIST_TYPE (a:A->v->bool) l2 v2`)) THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[injectivity "option"; PAIR_EQ; injectivity "result"; UNWIND_THM1] THEN
  MATCH_MP_TAC list_to_v_LIST_TYPE_APPEND THEN CONJ_TAC THEN
  MATCH_MP_TAC list_to_v_LIST_TYPE THEN ASM_MESON_TAC[]);;

let ml_Eval_length = prove
 (`!env x1 (x2:B) a (n:C) v.
     ml_Eval env x1 (VECTOR_TYPE a v) ==>
     ml_Eval env (App Vlength [x1]) (ml_NUM (regexp_compiler_length (v:A vector)))`,
  REPEAT GEN_TAC THEN MP_TAC(ISPEC `v:A vector` vector_nchotomy) THEN
  DISCH_THEN(X_CHOOSE_THEN `l:A list` SUBST1_TAC) THEN
  REWRITE_TAC[regexp_compiler_length_def] THEN DISCH_TAC THEN
  MATCH_MP_TAC TR2AUX_Eval_App1 THEN
  EXISTS_TAC `VECTOR_TYPE (a:A->v->bool) (Vector l)` THEN
  ASM_REWRITE_TAC[getOpClass_def] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[VECTOR_TYPE_def; ml_NUM_def; ml_INT_def] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[do_app_def] THEN CAKE_REWRITE_TAC[] THEN
  SIMP[injectivity "option"; PAIR_EQ; injectivity "result"; UNWIND_THM1]);;
(* pattern matching on the value of an expression *)

let TR2AUX_EV_MAT = prove
 (`!env e pes R R1 R2 v res.
     (!ck. ?ck1.
        evaluate (state_clock_fupd (combin_K ck1) (state_refs_fupd (combin_K R) ml_empty_state))
          env [e] =
        (state_clock_fupd (combin_K ck) (state_refs_fupd (combin_K R1) ml_empty_state),Rval [v])) /\
     can_pmatch_all (sem_env_c env) R1 (MAP FST pes) v /\
     (!ck. ?ck1.
        evaluate_match (state_clock_fupd (combin_K ck1) (state_refs_fupd (combin_K R1) ml_empty_state))
          env v pes bind_exn_v =
        (state_clock_fupd (combin_K ck) (state_refs_fupd (combin_K R2) ml_empty_state),Rval [res])) ==>
     !ck. ?ck1.
        evaluate (state_clock_fupd (combin_K ck1) (state_refs_fupd (combin_K R) ml_empty_state))
          env [Mat e pes] =
        (state_clock_fupd (combin_K ck) (state_refs_fupd (combin_K R2) ml_empty_state),Rval [res])`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "h1") (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "h2"))) THEN
  X_GEN_TAC `ck:num` THEN
  REMOVE_THEN "h2" (X_CHOOSE_TAC `c2:num` o SPEC `ck:num`) THEN
  REMOVE_THEN "h1" (X_CHOOSE_TAC `c1:num` o SPEC `c2:num`) THEN
  EXISTS_TAC `c1:num` THEN REWRITE_TAC[evaluate_def] THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN REWRITE_TAC[HD] THEN
  SIMP[] THEN ASM_REWRITE_TAC[]);;

(* one matching row of evaluate_match *)

let TR2AUX_EV_MATCH_ROW = prove
 (`!env v p e pes R R2 bs res err.
     ALL_DISTINCT (pat_bindings p) /\
     pmatch (sem_env_c env) R p v [] = Match bs /\
     (!ck. ?ck1.
        evaluate (state_clock_fupd (combin_K ck1) (state_refs_fupd (combin_K R) ml_empty_state))
          (sem_env_v_fupd (combin_K (nsAppend (alist_to_ns bs) (sem_env_v env))) env) [e] =
        (state_clock_fupd (combin_K ck) (state_refs_fupd (combin_K R2) ml_empty_state),Rval [res])) ==>
     !ck. ?ck1.
        evaluate_match (state_clock_fupd (combin_K ck1) (state_refs_fupd (combin_K R) ml_empty_state))
          env v (CONS (p,e) pes) err =
        (state_clock_fupd (combin_K ck) (state_refs_fupd (combin_K R2) ml_empty_state),Rval [res])`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "h"))) THEN
  X_GEN_TAC `ck:num` THEN REMOVE_THEN "h" (X_CHOOSE_TAC `c1:num` o SPEC `ck:num`) THEN
  EXISTS_TAC `c1:num` THEN REWRITE_TAC[evaluate_match_def] THEN
  SIMP[] THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[]);;

(* a row that does not match *)

let TR2AUX_EV_MATCH_SKIP = prove
 (`!env v p e pes R st err.
     ALL_DISTINCT (pat_bindings p) /\
     pmatch (sem_env_c env) R p v [] = No_match ==>
     evaluate_match (state_clock_fupd (combin_K st) (state_refs_fupd (combin_K R) ml_empty_state))
       env v (CONS (p,e) pes) err =
     evaluate_match (state_clock_fupd (combin_K st) (state_refs_fupd (combin_K R) ml_empty_state))
       env v pes err`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[evaluate_match_def] THEN
  SIMP[] THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[]);;

(* This is useful to force the type inferencer to give the type unit to an *)
(* unused argument.                                                         *)

let force_unit_type_def = cake_def
  `force_unit_type (u:1) (x:A) = x`;;
let _ = cake_add_simps [force_unit_type_def];;

let ml_Eval_force_unit_type = prove
 (`ml_Eval env x1 (UNIT_TYPE u) ==>
   ml_Eval env x2 ((a:A->v->bool) y) ==>
   ml_Eval env (Mat x1 [(Pcon NONE [], x2)]) (a (force_unit_type u y))`,
  REWRITE_TAC[TR2AUX_Eval_any_clock; UNIT_TYPE_def; force_unit_type_def] THEN
  DISCH_THEN(LABEL_TAC "e1") THEN DISCH_THEN(LABEL_TAC "e2") THEN
  X_GEN_TAC `refs:(v store_v)list` THEN
  REMOVE_THEN "e1" (X_CHOOSE_THEN `v1:v` (X_CHOOSE_THEN `r1:(v store_v)list`
    STRIP_ASSUME_TAC) o SPEC `refs:(v store_v)list`) THEN
  REMOVE_THEN "e2" (X_CHOOSE_THEN `v2:v` (X_CHOOSE_THEN `r2:(v store_v)list`
    STRIP_ASSUME_TAC) o SPEC `APPEND refs r1:(v store_v)list`) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MAP_EVERY EXISTS_TAC [`v2:v`; `APPEND r1 r2:(v store_v)list`] THEN
  ASM_REWRITE_TAC[APPEND_ASSOC] THEN MATCH_MP_TAC TR2AUX_EV_MAT THEN
  MAP_EVERY EXISTS_TAC [`APPEND refs r1:(v store_v)list`; `Conv NONE []`] THEN
  ASM_REWRITE_TAC[MAP; FST; can_pmatch_all_def; pmatch_def; LENGTH] THEN
  REWRITE_TAC[distinctness "match_result"] THEN
  MATCH_MP_TAC TR2AUX_EV_MATCH_ROW THEN EXISTS_TAC `[]:(mlstring#v)list` THEN
  REWRITE_TAC[pat_bindings_def; ALL_DISTINCT; pmatch_def; LENGTH] THEN
  REWRITE_TAC[alist_to_ns_nil; nsAppend_nsEmpty] THEN
  SUBGOAL_THEN `sem_env_v_fupd (combin_K (sem_env_v env)) env = env:v sem_env`
    (fun th -> ASM_REWRITE_TAC[th]) THEN
  REWRITE_TAC[sem_env_component_equality] THEN SIMP[]);;

let force_gc_to_run_def = cake_def
  `force_gc_to_run (i1:int) (i2:int) = one`;;

let ml_Eval_force_gc_to_run = prove
 (`ml_Eval env x1 (ml_INT i1) ==>
   ml_Eval env x2 (ml_INT i2) ==>
   ml_Eval env (App ConfigGC [x1; x2]) (UNIT_TYPE (force_gc_to_run i1 i2))`,
  REPEAT DISCH_TAC THEN MATCH_MP_TAC TR2AUX_Eval_App2 THEN
  MAP_EVERY EXISTS_TAC [`ml_INT i1`; `ml_INT i2`] THEN
  ASM_REWRITE_TAC[getOpClass_def] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[ml_INT_def; UNIT_TYPE_def] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[do_app_def] THEN CAKE_REWRITE_TAC[] THEN
  SIMP[injectivity "option"; PAIR_EQ; injectivity "result"; UNWIND_THM1]);;

let force_out_of_memory_error_def = cake_def
  `force_out_of_memory_error (x:A) = x`;;

(* evaluation steps: a literal and a variable *)

let TR2AUX_EV_LIT = prove
 (`!env l R ck. ?ck1.
     evaluate (state_clock_fupd (combin_K ck1) (state_refs_fupd (combin_K R) ml_empty_state))
       env [Lit l] =
     (state_clock_fupd (combin_K ck) (state_refs_fupd (combin_K R) ml_empty_state),Rval [Litv l])`,
  REPEAT GEN_TAC THEN EXISTS_TAC `ck:num` THEN REWRITE_TAC[evaluate_def]);;

let TR2AUX_EV_VAR = prove
 (`!env id v R.
     nsLookup (sem_env_v env) id = SOME v ==>
     !ck. ?ck1.
       evaluate (state_clock_fupd (combin_K ck1) (state_refs_fupd (combin_K R) ml_empty_state))
         env [Var id] =
       (state_clock_fupd (combin_K ck) (state_refs_fupd (combin_K R) ml_empty_state),Rval [v])`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `ck:num` THEN ASM_REWRITE_TAC[evaluate_def] THEN
  CAKE_REWRITE_TAC[]);;

let TR2AUX_nsLookup_write = prove
 (`!n v env m. nsLookup (sem_env_v (ml_write n v env)) (Short m) =
     if n = m then SOME v else nsLookup (sem_env_v env) (Short m)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ml_write_def] THEN SIMP[] THEN COND_CASES_TAC THENL
   [ASM_REWRITE_TAC[nsLookup_nsBind];
    SUBGOAL_THEN `~(Short m = Short n:(mlstring,mlstring)id)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[injectivity "id"] THEN ASM_MESON_TAC[];
      ASM_SIMP_TAC[nsLookup_nsBind]]]);;

let ml_Eval_force_out_of_memory_error = prove
 (`ml_Eval env x ((a:A->v->bool) i) ==>
   ml_Eval env
     (Let (SOME (implode "a")) x
       (Let (SOME (implode "n")) (Lit (IntLit (&18446744073709551616)))
         (Let NONE (App Aalloc [Var (Short (implode "n")); Var (Short (implode "n"))])
           (Var (Short (implode "a"))))))
     (a (force_out_of_memory_error i))`,
  REWRITE_TAC[TR2AUX_Eval_any_clock; force_out_of_memory_error_def] THEN
  DISCH_THEN(LABEL_TAC "e1") THEN X_GEN_TAC `refs:(v store_v)list` THEN
  REMOVE_THEN "e1" (X_CHOOSE_THEN `v1:v` (X_CHOOSE_THEN `r1:(v store_v)list`
    STRIP_ASSUME_TAC) o SPEC `refs:(v store_v)list`) THEN
  ABBREV_TAC `N = Litv (IntLit (&18446744073709551616))` THEN
  MAP_EVERY EXISTS_TAC [`v1:v`;
    `APPEND r1 [Varray (REPLICATE 18446744073709551616 (N:v))]`] THEN
  ASM_REWRITE_TAC[APPEND_ASSOC] THEN MATCH_MP_TAC TR2AUX_EV_LET THEN
  MAP_EVERY EXISTS_TAC [`APPEND refs r1:(v store_v)list`; `v1:v`] THEN
  ASM_REWRITE_TAC[nsOptBind_def] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM ml_write_def] THEN MATCH_MP_TAC TR2AUX_EV_LET THEN
  MAP_EVERY EXISTS_TAC [`APPEND refs r1:(v store_v)list`; `N:v`] THEN
  CONJ_TAC THENL [EXPAND_TAC "N" THEN REWRITE_TAC[TR2AUX_EV_LIT]; ALL_TAC] THEN
  REWRITE_TAC[nsOptBind_def] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM ml_write_def] THEN MATCH_MP_TAC TR2AUX_EV_LET THEN
  MAP_EVERY EXISTS_TAC
   [`APPEND (APPEND refs r1) [Varray (REPLICATE 18446744073709551616 (N:v))]`;
    `Loc T (LENGTH (APPEND refs r1:(v store_v)list))`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC TR2AUX_EV_APP_SIMPLE THEN
    MAP_EVERY EXISTS_TAC [`APPEND refs r1:(v store_v)list`; `[N:v; N]`] THEN
    REWRITE_TAC[getOpClass_def; REVERSE; APPEND] THEN CAKE_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC TR2AUX_EV_CONS THEN EXISTS_TAC `APPEND refs r1:(v store_v)list` THEN
      SIMP[TR2AUX_EV_VAR; TR2AUX_nsLookup_write];
      EXPAND_TAC "N" THEN REWRITE_TAC[do_app_def] THEN CAKE_REWRITE_TAC[] THEN
      SIMP[I_THM; INT_ABS_NUM; NUM_OF_INT_OF_NUM; INT_LT; store_alloc_def]];
    REWRITE_TAC[nsOptBind_def] THEN CAKE_REWRITE_TAC[] THEN
    SUBGOAL_THEN `!e:v sem_env. sem_env_v_fupd (combin_K (sem_env_v e)) e = e`
      (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[sem_env_component_equality] THEN SIMP[]; ALL_TAC] THEN
    MATCH_MP_TAC TR2AUX_EV_VAR THEN SIMP[TR2AUX_nsLookup_write] THEN
    SIMP[injectivity "mlstring"; injectivity "char"]]);;

let ml_Eval_empty_ffi = prove
 (`ml_Eval env x (STRING_TYPE s) ==>
   ml_Eval env
     (App (FFI (implode "")) [x; App Aw8alloc [Lit (IntLit (&0)); Lit (Word8 (word 0))]])
     (UNIT_TYPE (empty_ffi s))`,
  REWRITE_TAC[TR2AUX_Eval_any_clock; STRING_TYPE_def; UNIT_TYPE_def] THEN
  DISCH_THEN(LABEL_TAC "e1") THEN X_GEN_TAC `refs:(v store_v)list` THEN
  REMOVE_THEN "e1" (X_CHOOSE_THEN `v1:v` (X_CHOOSE_THEN `r1:(v store_v)list`
    STRIP_ASSUME_TAC) o SPEC `APPEND refs [W8array []]:(v store_v)list`) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MAP_EVERY EXISTS_TAC [`Conv NONE []`; `APPEND [W8array []] r1:(v store_v)list`] THEN
  REWRITE_TAC[APPEND_ASSOC] THEN MATCH_MP_TAC TR2AUX_EV_APP_SIMPLE THEN
  MAP_EVERY EXISTS_TAC
   [`APPEND (APPEND refs [W8array []]) r1:(v store_v)list`;
    `[Loc T (LENGTH (refs:(v store_v)list)); Litv (StrLit s)]`] THEN
  REWRITE_TAC[getOpClass_def; REVERSE; APPEND] THEN CAKE_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC TR2AUX_EV_CONS THEN
    EXISTS_TAC `APPEND refs [W8array []]:(v store_v)list` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC TR2AUX_EV_APP_SIMPLE THEN
    MAP_EVERY EXISTS_TAC [`refs:(v store_v)list`;
      `[Litv (Word8 (word 0)); Litv (IntLit (&0))]`] THEN
    REWRITE_TAC[getOpClass_def; REVERSE; APPEND] THEN CAKE_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC TR2AUX_EV_CONS THEN EXISTS_TAC `refs:(v store_v)list` THEN
      REWRITE_TAC[TR2AUX_EV_LIT] THEN
      MATCH_MP_TAC TR2AUX_EV_CONS THEN EXISTS_TAC `refs:(v store_v)list` THEN
      REWRITE_TAC[TR2AUX_EV_LIT; TR2AUX_EV_NIL];
      REWRITE_TAC[do_app_def] THEN CAKE_REWRITE_TAC[] THEN
      SIMP[I_THM; INT_ABS_NUM; NUM_OF_INT_OF_NUM; INT_LT_REFL; REPLICATE;
        store_alloc_def]];
    ALL_TAC] THEN
  ABBREV_TAC `S = APPEND (APPEND refs [W8array []]) r1:(v store_v)list` THEN
  SUBGOAL_THEN `LENGTH (refs:(v store_v)list) < LENGTH (S:(v store_v)list) /\
                EL (LENGTH refs) S = W8array []` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN
    SIMP_TAC[ARITH_RULE `n < (n + SUC 0) + m`] THEN
    SIMP_TAC[EL_APPEND1; LENGTH_APPEND; LENGTH; ARITH_RULE `n < n + SUC 0`] THEN
    SIMP_TAC[EL_LENGTH_APPEND; NULL; HD];
    ALL_TAC] THEN
  REWRITE_TAC[do_app_def] THEN CAKE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[store_lookup_def] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[call_FFI_def] THEN CAKE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[store_assign_def; store_v_same_type_def] THEN CAKE_REWRITE_TAC[] THEN
  UNDISCH_TAC `EL (LENGTH (refs:(v store_v)list)) (S:(v store_v)list) = W8array []` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC LUPDATE_SAME THEN
  ASM_REWRITE_TAC[]);;

let pure_seq_def = cake_def
  `pure_seq (x:A) (y:B) = y`;;

let ml_Eval_pure_seq = prove
 (`ml_Eval env x ((a:A->v->bool) a1) ==>
   ml_Eval env y ((b:B->v->bool) b1) ==>
   ml_Eval env (Let NONE x y) (b (pure_seq a1 b1))`,
  REWRITE_TAC[TR2AUX_Eval_any_clock; pure_seq_def] THEN
  DISCH_THEN(LABEL_TAC "e1") THEN DISCH_THEN(LABEL_TAC "e2") THEN
  X_GEN_TAC `refs:(v store_v)list` THEN
  REMOVE_THEN "e1" (X_CHOOSE_THEN `v1:v` (X_CHOOSE_THEN `r1:(v store_v)list`
    STRIP_ASSUME_TAC) o SPEC `refs:(v store_v)list`) THEN
  REMOVE_THEN "e2" (X_CHOOSE_THEN `v2:v` (X_CHOOSE_THEN `r2:(v store_v)list`
    STRIP_ASSUME_TAC) o SPEC `APPEND refs r1:(v store_v)list`) THEN
  MAP_EVERY EXISTS_TAC [`v2:v`; `APPEND r1 r2:(v store_v)list`] THEN
  ASM_REWRITE_TAC[APPEND_ASSOC] THEN MATCH_MP_TAC TR2AUX_EV_LET THEN
  MAP_EVERY EXISTS_TAC [`APPEND refs r1:(v store_v)list`; `v1:v`] THEN
  ASM_REWRITE_TAC[nsOptBind_def] THEN CAKE_REWRITE_TAC[] THEN
  SUBGOAL_THEN `sem_env_v_fupd (combin_K (sem_env_v env)) env = env:v sem_env`
    (fun th -> ASM_REWRITE_TAC[th]) THEN
  REWRITE_TAC[sem_env_component_equality] THEN SIMP[]);;
(* a few misc. lemmas that help the automation *)

let IMP_PreImp = prove
 (`!b1 b2 b3. (b1 /\ b2 ==> b3) ==> b1 ==> ml_PreImp b2 b3`,
  REWRITE_TAC[ml_PreImp_def; ml_PRECONDITION_def] THEN MESON_TAC[]);;

(* HOL4's evaluate_list_SIMP is in a comment of the script *)

(* HOL4 [local] *)

let UNCURRY1 = prove
 (CASE_TERM `!f:A->B->C. UNCURRY f = \x. match x with (x,y) -> f x y`,
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; UNCURRY_DEF] THEN CAKE_REWRITE_TAC[]);;

(* HOL4 [local] *)

let UNCURRY2 = prove
 (`!x (y:C) (f:A->B->C->D). pair_CASE x f y = pair_CASE x (\z1 z2. f z1 z2 y)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN CAKE_REWRITE_TAC[]);;

let TR2AUX_UNCURRY3 = prove
 (`!(x:A) (y:B) (f:A->B->C). pair_CASE (x,y) f = f x y`,
  CAKE_REWRITE_TAC[]);;

let UNCURRY_SIMP = CONJ UNCURRY1 (CONJ UNCURRY2 TR2AUX_UNCURRY3);;

let num_case_thm = prove
 (`num_CASE = \n (b:A) f. if n = 0 then b else f (n - 1)`,
  REWRITE_TAC[FUN_EQ_THM] THEN INDUCT_TAC THEN
  REWRITE_TAC[num_CASE; NOT_SUC; SUC_SUB1]);;

let PUSH_FORALL_INTO_IMP = prove
 (`!P Q. (!x:A. P x ==> Q x) ==> (!x. P x) ==> (!x. Q x)`,
  MESON_TAC[]);;

let FALSE_def = new_definition
  `FALSE <=> F`;;

let TRUE_def = new_definition
  `TRUE <=> T`;;

let Eval_Val_BOOL_FALSE = prove
 (`ml_Eval env (App (Test (Compare Lt) IntT) [Lit (IntLit (&0)); Lit (IntLit (&0))])
     (ml_BOOL FALSE)`,
  REWRITE_TAC[FALSE_def; Eval_Val_BOOL_F]);;

let Eval_Val_BOOL_TRUE = prove
 (`ml_Eval env (App (Test (Compare Leq) IntT) [Lit (IntLit (&0)); Lit (IntLit (&0))])
     (ml_BOOL TRUE)`,
  REWRITE_TAC[TRUE_def; Eval_Val_BOOL_T]);;

let MEMBER_def = cake_def
  `(MEMBER (x:A) [] <=> F) /\
   (MEMBER x (CONS y ys) <=> x = y \/ MEMBER x ys)`;;

(* HOL4 [local] *)

let MEM_EQ_MEMBER = prove
 (`!ys (x:A). MEM x ys <=> MEMBER x ys`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MEM; MEMBER_def]);;

let MEMBER_INTRO = prove
 (`((MEM:A->A list->bool) = MEMBER) /\ (MEM (x:A) = MEMBER x) /\
   (MEM (x:A) ys <=> MEMBER x ys)`,
  REWRITE_TAC[FUN_EQ_THM; MEM_EQ_MEMBER]);;

(* lookup cons *)

let lookup_cons_write = prove
 (`!funs n x env name env1.
     ml_lookup_cons name (ml_write n x env) = ml_lookup_cons name env /\
     ml_lookup_cons name (ml_write_rec funs env1 env) = ml_lookup_cons name env`,
  REWRITE_TAC[write_rec_thm; ml_write_def; ml_lookup_cons_def] THEN SIMP[]);;

let DISJOINT_set_SIMP = prove
 (`(DISJOINT (set_of_list []) (s:A->bool) <=> T) /\
   (DISJOINT (set_of_list (CONS x xs)) s <=> ~(x IN s) /\ DISJOINT (set_of_list xs) s)`,
  REWRITE_TAC[set_of_list] THEN SET_TAC[]);;
(* removing shadowed elements from an alist *)

let ASHADOW_def = cake_def_wf `MEASURE (LENGTH:(A#B)list->num)`
  (REPEAT STRIP_TAC THEN REWRITE_TAC[MEASURE; LENGTH] THEN
   TRY(MATCH_MP_TAC(ARITH_RULE `a <= b ==> a < SUC b`) THEN
       REWRITE_TAC[LENGTH_FILTER] THEN NO_TAC) THEN
   ARITH_TAC)
  `(ASHADOW ([]:(A#B)list) = []) /\
   (ASHADOW (CONS x xs) =
      if EX (\y. FST x = FST y) xs
      then CONS x (ASHADOW (FILTER (\y. ~(FST x = FST y)) xs))
      else CONS x (ASHADOW xs))`;;

let ASHADOW_ind = cake_ind "ASHADOW";;

(* HOL4 [local] *)

let ASHADOW_PREFIX = prove
 (`!xs ys.
     ALL_DISTINCT (MAP FST xs) /\
     ALL (\y. ~(MEM y (MAP FST ys))) (MAP FST xs) ==>
     ASHADOW (APPEND xs ys) = APPEND xs (ASHADOW (ys:(A#B)list))`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND; MAP; ALL_DISTINCT; ALL] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[ASHADOW_def] THEN
  SUBGOAL_THEN `~EX (\y:A#B. FST (h:A#B) = FST y) (APPEND t ys)` (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[GSYM EX_MEM; MEM_APPEND] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MEM_MAP]) THEN ASM_MESON_TAC[];
    AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* HOL4 [local] *)

let MEM_MAP_ASHADOW = prove
 (`!xs y. MEM y (MAP FST (ASHADOW xs)) <=> MEM (y:A) (MAP FST (xs:(A#B)list))`,
  MATCH_MP_TAC ASHADOW_ind THEN REWRITE_TAC[ASHADOW_def; MAP; MEM] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[MAP; MEM] THEN
  REWRITE_TAC[MEM_MAP; MEM_FILTER] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM EX_MEM]) THEN ASM_MESON_TAC[]);;

(* HOL4 [local] *)

let EVERY_ALOOKUP_LEMMA = prove
 (`!xs. ALL_DISTINCT (MAP FST xs) ==>
        ALL (\(x,y,z). ALOOKUP xs x = SOME ((y:B),(z:C))) (xs:(A#B#C)list)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; MAP; ALL_DISTINCT] THEN
  PAIR_CASES_ON `h:A#B#C` THEN REWRITE_TAC[ALOOKUP_THM; FST; SND] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(fun th -> FIRST_ASSUM(MP_TAC o MATCH_MP th)) THEN
  REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM] THEN REPEAT STRIP_TAC THEN
  COND_CASES_TAC THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    UNDISCH_TAC `~MEM (p1:A) (MAP FST (t:(A#B#C)list))` THEN
    REWRITE_TAC[MEM_MAP] THEN ASM_MESON_TAC[FST];
    ASM_MESON_TAC[]]);;

(* HOL4 [local] ALOOKUP_FILTER (names.tsv ml_ALOOKUP_FILTER) *)

let ml_ALOOKUP_FILTER = prove
 (`!t a q. ~(q = a) ==> ALOOKUP (FILTER (\y. ~(q = FST y)) t) a = ALOOKUP (t:(A#B)list) a`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[FILTER; ALOOKUP_DEF] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[ALOOKUP_DEF] THEN
  SUBGOAL_THEN `~(FST (h:A#B) = a)` (fun th -> REWRITE_TAC[th]) THEN
  ASM_MESON_TAC[]);;

(* HOL4 [local] *)

let ALOOKUP_ASHADOW = prove
 (`!xs a. ALOOKUP (ASHADOW xs) a = ALOOKUP (xs:(A#B)list) a`,
  MATCH_MP_TAC ASHADOW_ind THEN REWRITE_TAC[ASHADOW_def; ALOOKUP_DEF] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[ALOOKUP_DEF] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC ml_ALOOKUP_FILTER THEN ASM_REWRITE_TAC[]);;

(* HOL4 [local] *)

let ALL_DISTINCT_MAP_FST_ASHADOW = prove
 (`!xs. ALL_DISTINCT (MAP FST (ASHADOW (xs:(A#B)list)))`,
  MATCH_MP_TAC ASHADOW_ind THEN REWRITE_TAC[ASHADOW_def; MAP; ALL_DISTINCT] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[MAP; ALL_DISTINCT; MEM_MAP_ASHADOW] THEN
  REWRITE_TAC[MEM_MAP; MEM_FILTER] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM EX_MEM]) THEN ASM_MESON_TAC[]);;
(* size lemmas.  HOL4's v1_size (the size of a v list) is list_size v_size *)

(* HOL4 [local] *)

let v1_size = prove
 (`!vs v. MEM v vs ==> v_size v < list_size v_size vs`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; list_size] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [ARITH_TAC; FIRST_X_ASSUM(MP_TAC o SPEC `v:v`) THEN ASM_REWRITE_TAC[] THEN ARITH_TAC]);;

(* introducing a module (Tmod) *)

let type_names_def = cake_def
  `(type_names [] (names:mlstring list) = names) /\
   (type_names (CONS (Dtype _ tds) xs) names =
      type_names xs (APPEND (MAP (FST o SND) tds) names)) /\
   (type_names (CONS x xs) names = type_names xs names)`;;

(* HOL4 [local] *)

let type_names_eq = prove
 (CASE_TERM `!ds (names:mlstring list).
     type_names ds names =
     APPEND (FLAT (REVERSE (MAP (\d.
               match d with
                 Dlet _ v6 v7 -> []
               | Dletrec _ v8 -> []
               | Dmod _ ds -> []
               | Dtype _ tds -> MAP (\(tvs,tn,ctors). tn) tds
               | Dtabbrev _ tvs tn t -> []
               | Dlocal _ _ -> []
               | Denv _ -> []
               | Dexn _ v10 v11 -> []) ds))) names`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[type_names_def; MAP; REVERSE; FLAT; APPEND] THEN
  GEN_TAC THEN CASES_ON `h:dec` THEN
  ASM_REWRITE_TAC[type_names_def] THEN CAKE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[FLAT_APPEND; FLAT; APPEND_NIL; GSYM APPEND_ASSOC] THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; o_THM; FST; SND]);;

(* HOL4 [local] *)

let lookup_APPEND = prove
 (`!xs ys n. ~(MEM n (MAP FST ys)) ==>
             ALOOKUP (APPEND xs ys) n = ALOOKUP (xs:(A#B)list) n`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND; ALOOKUP_DEF] THENL
   [LIST_INDUCT_TAC THEN REWRITE_TAC[ALOOKUP_DEF; MAP; MEM] THEN ASM_MESON_TAC[];
    ASM_MESON_TAC[]]);;

let FEVERY_DRESTRICT_FUPDATE = prove
 (`FEVERY P (DRESTRICT (f |+ (x,y)) (COMPL s)) <=>
   (~(x IN s) ==> P ((x:A),(y:B))) /\
   FEVERY P (DRESTRICT f (COMPL (x INSERT s)))`,
  REWRITE_TAC[FEVERY_DEF; DRESTRICT_DEF; FDOM_FUPDATE; FAPPLY_FUPDATE_THM; IN_INTER;
    IN_INSERT; FMAPAUX_IN_COMPL] THEN
  MESON_TAC[]);;

let PULL_EXISTS_EXTRA = prove
 (`(Q ==> ?x:A. P x) <=> ?x. Q ==> P x`,
  MESON_TAC[]);;

let Eval_Fun_rw = prove
 (`ml_Eval env (Fun n exp) P <=> P (Closure env n exp)`,
  REWRITE_TAC[TR2AUX_Eval_Fun_rw]);;

(* HOL4 [local]; HOL4 binds a variable v that the body does not use *)

let evaluate_Var_nsLookup = prove
 (`eval_rel (s:(FFI)state) env (Var id) s' r <=>
   ?v:A. nsLookup (sem_env_v env) id = SOME r /\ s' = s`,
  REWRITE_TAC[eval_rel_def; evaluate_def] THEN
  CASES_ON `nsLookup (sem_env_v (env:v sem_env)) (id:(mlstring,mlstring)id)` THEN
  CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ; injectivity "result"; distinctness "result"; CONS_11;
    injectivity "option"; distinctness "option"; state_component_equality] THEN
  SIMP[] THEN MESON_TAC[]);;

(* HOL4 [local] *)

let evaluate_Var = prove
 (`eval_rel (s:(FFI)state) env (Var (Short n)) s' r <=>
   ?v:A. ml_lookup_var n env = SOME r /\ s' = s`,
  REWRITE_TAC[evaluate_Var_nsLookup; ml_lookup_var_def]);;

let Eval_Var_nsLookup = prove
 (CASE_TERM `ml_Eval env (Var id) P <=>
   (match nsLookup (sem_env_v env) id with NONE -> F | SOME v -> P v)`,
  REWRITE_TAC[TR2AUX_Eval_Var_nsLookup]);;

let Eval_Var = prove
 (`ml_Eval env (Var (Short n)) P <=> ?v. ml_lookup_var n env = SOME v /\ P v`,
  REWRITE_TAC[TR2AUX_Eval_Var_nsLookup; ml_lookup_var_def] THEN
  CASES_ON `nsLookup (sem_env_v (env:v sem_env)) (Short n:(mlstring,mlstring)id)` THEN
  CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[injectivity "option"; distinctness "option"] THEN MESON_TAC[]);;

let Eval_Fun_Var_intro = prove
 (`ml_Eval cl_env (Fun n exp) P ==>
   !name. LOOKUP_VAR name env (Closure cl_env n exp) ==>
          ml_Eval env (Var (Short name)) P`,
  REWRITE_TAC[Eval_Fun_rw; Eval_Var; LOOKUP_VAR_def] THEN MESON_TAC[]);;

let Eval_Var_LOOKUP_VAR_elim = prove
 (`(!env. LOOKUP_VAR name env v ==> ml_Eval env (Var (Short name)) P) ==> P v`,
  REWRITE_TAC[Eval_Var; LOOKUP_VAR_def] THEN DISCH_THEN(MP_TAC o SPEC
    `sem_env_REC (nsSing name (v:v)) (nsEmpty:(mlstring,mlstring,num#stamp)namespace)`) THEN
  REWRITE_TAC[ml_lookup_var_def; sem_env_INFO.ri_accessors] THEN
  SIMP[nsSing_def; nsLookup_def; ALOOKUP_THM] THEN
  REWRITE_TAC[injectivity "option"] THEN MESON_TAC[]);;

let PRECONDITION_T = prove
 (`ml_PRECONDITION T <=> T`,
  REWRITE_TAC[ml_PRECONDITION_def]);;
let no_change_refs_def = cake_def_wf `MEASURE exp_size`
  (REPEAT STRIP_TAC THEN
   TRY(FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[MEM_MAP; EXISTS_PAIR_THM; SND])) THEN
   TERM_TAC)
  `(no_change_refs (Lit _) <=> T) /\
   (no_change_refs (Var _) <=> T) /\
   (no_change_refs (Fun _ _) <=> T) /\
   (no_change_refs (Let _ e1 e2) <=> no_change_refs e1 /\ no_change_refs e2) /\
   (no_change_refs (If e1 e2 e3) <=>
      no_change_refs e1 /\ no_change_refs e2 /\ no_change_refs e3) /\
   (no_change_refs (Raise e) <=> no_change_refs e) /\
   (no_change_refs (Letrec _ e) <=> no_change_refs e) /\
   (no_change_refs (Con _ es) <=> ALL no_change_refs es) /\
   (no_change_refs (Tannot e _) <=> no_change_refs e) /\
   (no_change_refs (Lannot e _) <=> no_change_refs e) /\
   (no_change_refs (Mat e pats) <=>
      no_change_refs e /\ ALL no_change_refs (MAP SND pats)) /\
   (no_change_refs (App oper es) <=>
      (match oper with
         Opassign -> F
       | Opapp -> F
       | Eval -> F
       | Opref -> F
       | Aw8alloc -> F
       | Aw8update -> F
       | Aw8update_unsafe -> F
       | CopyStrAw8 -> F
       | CopyAw8Aw8 -> F
       | XorAw8Str_unsafe -> F
       | Aalloc -> F
       | AallocEmpty -> F
       | AallocFixed -> F
       | Aupdate -> F
       | Aupdate_unsafe -> F
       | FFI _ -> F
       | ThunkOp _ -> F
       | _ -> T) /\ ALL no_change_refs es) /\
   (no_change_refs _ <=> F)`;;

let no_change_refs_ind = cake_ind "no_change_refs";;

(* the operators that no_change_refs allows do not change the store *)

let TR2AUX_do_app_no_change_refs = prove
 (`!(s:(v store_v)list) (t:(FFI)ffi_state) op vs s' t' r.
     do_app (s,t) op vs = SOME ((s',t'),r) /\ no_change_refs (App op []) ==> s' = s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[no_change_refs_def; ALL] THEN
  REWRITE_TAC[do_app_cases] THEN
  RW[] THEN GVS([thunk_op_def; store_alloc_def; store_assign_def; sum_case_eq;
                 case_eq "ffi_result"; case_eq "thunk_op"; case_eq "thunk_mode"] @
                EVALAUX_do_app_eqs));;

let TR2AUX_ncr_simple = prove
 (`!op. no_change_refs (App op []) ==> getOpClass op = Simple`,
  MATCH_MP_TAC op_INDUCT THEN REWRITE_TAC[no_change_refs_def; getOpClass_def; ALL] THEN
  CAKE_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN TRY COND_CASES_TAC THEN
  REWRITE_TAC[distinctness "op_class"] THEN
  MP_TAC(ISPEC `a:thunk_op` (cases "thunk_op")) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[]);;

(* unfold the evaluation assumption and split its cases *)

let TR2AUX_NCR_TAC =
  FIRST_X_ASSUM(MP_TAC o check (fun th -> let c = concl th in is_eq c &&
    (try mem (fst(dest_const(fst(strip_comb(lhs c))))) ["evaluate";"evaluate_match"]
     with Failure _ -> false))) THEN
  REWRITE_TAC[evaluate_def] THEN DISCH_TAC THEN
  GVS(do_if_def :: all_case_eqs());;

let evaluate_no_change_refs = prove
 (`(!(s:(FFI)state) env es s1 vs.
      evaluate s env es = (s1,Rval vs) /\ ALL no_change_refs es ==>
      state_refs s1 = state_refs s) /\
   (!(s:(FFI)state) env v pes errv s1 vs.
      evaluate_match s env v pes errv = (s1,Rval vs) /\
      ALL no_change_refs (MAP SND pes) ==>
      state_refs s1 = state_refs s)`,
  MATCH_MP_TAC evaluate_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[no_change_refs_def; ALL; MAP] THEN REPEAT STRIP_TAC THEN
  TRY(TR2AUX_NCR_TAC THEN NO_TAC) THEN
  SUBGOAL_THEN `no_change_refs (App op [])` ASSUME_TAC THENL
   [REWRITE_TAC[no_change_refs_def; ALL] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP TR2AUX_ncr_simple) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> let c = concl th in is_eq c &&
    (try fst(dest_const(fst(strip_comb(lhs c)))) = "evaluate" with Failure _ -> false))) THEN
  REWRITE_TAC[evaluate_def] THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  REPEAT TOP_CASE_TAC THEN
  REWRITE_TAC[list_result_def; PAIR_EQ; injectivity "result"; distinctness "result"] THEN
  TRY(DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) ASSUME_TAC)) THEN
  SIMP[] THEN
  FIRST_X_ASSUM(fun th -> if is_eq (concl th) &&
      (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "do_app" with Failure _ -> false)
     then MP_TAC(MP (MATCH_MP (REWRITE_RULE[IMP_CONJ] TR2AUX_do_app_no_change_refs) th)
                    (ASSUME `no_change_refs (App op [])`)) else NO_TAC) THEN
  DISCH_THEN SUBST1_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[EVERY_REVERSE] THEN ASM_MESON_TAC[]);;

let eval_rel_no_change_refs = prove
 (`!exp (s1:(FFI)state) s2 env res.
     eval_rel s1 env exp s2 res /\ no_change_refs exp ==> state_refs s1 = state_refs s2`,
  REWRITE_TAC[eval_rel_def] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`state_clock_fupd (combin_K ck1) (s1:(FFI)state)`; `env:v sem_env`;
    `[exp:exp]`; `state_clock_fupd (combin_K ck2) (s2:(FFI)state)`; `[res:v]`]
    (CONJUNCT1 evaluate_no_change_refs)) THEN
  ASM_REWRITE_TAC[ALL] THEN SIMP[]);;

let ml_Eval_constant = prove
 (`!refs. ml_Eval env exp P ==>
          ?v refs'. eval_rel (state_refs_fupd (combin_K refs) ml_empty_state) env exp
                             (state_refs_fupd (combin_K (APPEND refs refs')) ml_empty_state) v /\
                    (no_change_refs exp ==> refs' = [])`,
  REWRITE_TAC[ml_Eval_def] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o SPEC `refs:(v store_v)list`) THEN
  MAP_EVERY EXISTS_TAC [`res:v`; `refs':(v store_v)list`] THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`exp:exp`; `state_refs_fupd (combin_K refs) ml_empty_state`;
    `state_refs_fupd (combin_K (APPEND refs refs')) ml_empty_state`; `env:v sem_env`; `res:v`]
    eval_rel_no_change_refs) THEN
  ASM_REWRITE_TAC[] THEN SIMP[] THEN
  DISCH_THEN(MP_TAC o AP_TERM `LENGTH:(v store_v)list->num`) THEN
  REWRITE_TAC[LENGTH_APPEND; ARITH_RULE `a = a + b <=> b = 0`; LENGTH_EQ_NIL]);;

let Eval_evaluate_IMP = prove
 (`ml_Eval env exp P /\ eval_rel (s:(FFI)state) env exp s' v ==> P v`,
  REWRITE_TAC[ml_Eval_def] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o SPEC `state_refs (s:(FFI)state)`) THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP evaluate_empty_state_IMP) THEN
  MP_TAC(MATCH_MP eval_rel_11 (CONJ
    (ASSUME `eval_rel (s:(FFI)state) env exp
               (state_refs_fupd (combin_K (APPEND (state_refs s) refs')) s) res`)
    (ASSUME `eval_rel (s:(FFI)state) env exp s' v`))) THEN
  ASM_MESON_TAC[]);;
(* HOL4: pair_CASE_UNCURRY (names.tsv ml_pair_CASE_UNCURRY) *)

let ml_pair_CASE_UNCURRY = prove
 (`!x (y:A->B->C). pair_CASE x y = UNCURRY y x`,
  REWRITE_TAC[FORALL_PAIR_THM; UNCURRY_DEF] THEN CAKE_REWRITE_TAC[]);;

(* HOL4: IF_T, IF_F (names.tsv ml_IF_T, ml_IF_F) *)

let ml_IF_T = prove
 (`(if T then x else y) = x:A`,
  REWRITE_TAC[]);;

let ml_IF_F = prove
 (`(if F then x else y) = y:A`,
  REWRITE_TAC[]);;

let sat_hyp_lemma = prove
 (`(b1 ==> (x1 <=> x2)) /\ (x1 ==> y) ==> b1 /\ x2 ==> y`,
  MESON_TAC[]);;

let IMP_EQ_F = prove
 (`~b ==> (b <=> F)`,
  REWRITE_TAC[]);;

(* HOL4: IMP_EQ_T (names.tsv ml_IMP_EQ_T) *)

let ml_IMP_EQ_T = prove
 (`b ==> (b <=> T)`,
  REWRITE_TAC[]);;

let IF_TAKEN = prove
 (`!b x y. b ==> ((if b then x else y) = x:unlikely)`,
  SIMP_TAC[]);;

let EQ_COND_INTRO = prove
 (`(b ==> c) ==> (c <=> if b then T else c)`,
  MESON_TAC[]);;

let LIST_TYPE_And = prove
 (`LIST_TYPE (ml_And a P) = ml_And (LIST_TYPE a) (ALL (P:A->bool))`,
  REWRITE_TAC[FUN_EQ_THM; ml_And_def] THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[LIST_TYPE_def; ALL; ml_And_def] THEN MESON_TAC[]);;

let EVERY_MEM_CONTAINER = prove
 (`!P l. ALL P l <=> !e:A. ml_CONTAINER (MEM e l) ==> P e`,
  REWRITE_TAC[GSYM ALL_MEM; ml_CONTAINER_def]);;

let PRECONDITION_EQ_CONTAINER = prove
 (`(ml_PRECONDITION p <=> ml_CONTAINER p) /\
   (ml_CONTAINER (~p) <=> ~ml_CONTAINER p) /\ ml_CONTAINER T`,
  REWRITE_TAC[ml_PRECONDITION_def; ml_CONTAINER_def]);;

let CONTAINER_NOT_ZERO = prove
 (`!P. (~(ml_CONTAINER (b = 0)) ==> P b) <=>
       !n. ml_CONTAINER (b = SUC n) ==> P (SUC n:num)`,
  GEN_TAC THEN REWRITE_TAC[ml_CONTAINER_def] THEN
  STRUCT_CASES_TAC(SPEC `b:num` num_CASES) THEN
  REWRITE_TAC[NOT_SUC; SUC_INJ] THEN MESON_TAC[]);;

let IMP_PreImp_LEMMA = prove
 (`!b1 b2 b3. (b1 ==> b3 ==> b2) ==> b3 ==> ml_PreImp b1 b2`,
  REWRITE_TAC[ml_PreImp_def; ml_PRECONDITION_def] THEN MESON_TAC[]);;

let PRE_IMP = prove
 (`T /\ ml_PRECONDITION b ==> ml_PRECONDITION b`,
  REWRITE_TAC[]);;

let PreImp_IMP_T = prove
 (`ml_PreImp b1 b2 /\ T ==> ml_PreImp b1 b2`,
  REWRITE_TAC[]);;

(* HOL4: CONJ_IMP and IMP_SPLIT are SPEC_ALL'd *)

let CONJ_IMP = prove
 (`(b1 /\ b2 ==> b12) /\ (b3 /\ b4 ==> b34) ==>
   ((b1 /\ b3) /\ (b2 /\ b4) ==> b12 /\ b34)`,
  MESON_TAC[]);;

let IMP_SPLIT = prove
 (`((b12:bool) = b12) /\ (b3 /\ b4 ==> b34) ==>
   ((b12 ==> b3) /\ (b12 ==> b4) ==> (b12 ==> b34))`,
  MESON_TAC[]);;

let FORALL_SPLIT = prove
 (`(!x:A. P1 x /\ P2 x ==> P x) ==> (!) P1 /\ (!) P2 ==> (!) P`,
  REWRITE_TAC[GSYM(ONCE_REWRITE_RULE[GSYM ETA_AX] FORALL_DEF)] THEN
  REWRITE_TAC[FORALL_DEF] THEN REWRITE_TAC[FUN_EQ_THM] THEN MESON_TAC[]);;

let DEFAULT_IMP = prove
 (`!b1. b1 /\ b1 ==> b1`,
  REWRITE_TAC[]);;

let combine_lemma = prove
 (`!b1 b2 b3 b4. (b1 /\ b2 ==> b3) /\ (b3 ==> b4) ==> b2 ==> b1 ==> b4`,
  MESON_TAC[]);;

let IMP_PreImp_THM = prove
 (`(b ==> ml_PreImp x y) ==> ((x ==> b) ==> ml_PreImp x y)`,
  REWRITE_TAC[ml_PreImp_def; ml_PRECONDITION_def] THEN MESON_TAC[]);;

let PreImp_IMP = prove
 (`(ml_PRECONDITION x ==> ml_PreImp x y) ==> ml_PreImp x y`,
  REWRITE_TAC[ml_PreImp_def] THEN MESON_TAC[]);;

let PreImp_LEMMA = prove
 (`(b1 ==> ml_PreImp b1 b2) ==> ml_PreImp b1 b2`,
  REWRITE_TAC[ml_PreImp_def; ml_PRECONDITION_def] THEN MESON_TAC[]);;

let SUC_SUB1_LEMMA = prove
 (`SUC n - 1 = n`,
  ARITH_TAC);;

let LENGTH_EQ_SUC_IMP = prove
 (`LENGTH xs = SUC n ==> ~(xs:A list = [])`,
  STRUCT_CASES_TAC(ISPEC `xs:A list` list_CASES) THEN
  REWRITE_TAC[LENGTH; NOT_SUC; NOT_CONS_NIL]);;
(* pattern match translation *)

let ml_Mat_cases_def = cake_def
  `(Mat_cases (INL (vars,x:exp)) = [(Pcon NONE (MAP Pvar vars),x)]) /\
   (Mat_cases (INR ps) =
      MAP (\(name,vars,(x:exp),(t:stamp)). (Pcon (SOME name) (MAP Pvar vars),x)) ps)`;;

let good_cons_env_def = cake_def
  `good_cons_env (ps:((mlstring,mlstring)id#mlstring list#exp#stamp)list) env <=>
     ALL (\(name,vars,x,t).
            ALL_DISTINCT (pats_bindings (MAP Pvar vars)) /\
            ml_lookup_cons name env = SOME (LENGTH vars,t)) ps /\
     (let (name,vars,x,t1) = HD ps in
      ALL (\(name,vars,x,t2). same_type t1 t2) ps)`;;

(* helpers of the port for evaluate_match_MAP and IMP_Eval_Mat_cases *)

let TR2AUX_same_type_refl = prove
 (`!t. same_type t t`,
  GEN_TAC THEN CASES_ON `t:stamp` THEN REWRITE_TAC[same_type_def]);;

let TR2AUX_good_cons_env_MEM = prove
 (`!ps env name vars x t name' vars' x' t'.
     good_cons_env ps env /\ MEM (name,vars,x,t) ps /\ MEM (name',vars',x',t') ps ==>
     ALL_DISTINCT (pats_bindings (MAP Pvar vars)) /\
     nsLookup (sem_env_c env) name = SOME (LENGTH vars,t) /\
     same_type t t'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[good_cons_env_def; ml_lookup_cons_def] THEN
  SUBGOAL_THEN `?a0 a1 a2 a3. HD ps = (a0,a1,a2,a3):(mlstring,mlstring)id#mlstring list#exp#stamp`
    STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM] THEN SIMP[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `MEM (a0,a1,a2,a3) (ps:((mlstring,mlstring)id#mlstring list#exp#stamp)list)`
    ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPEC `ps:((mlstring,mlstring)id#mlstring list#exp#stamp)list` list_CASES) THEN
    STRIP_TAC THEN ASM_MESON_TAC[MEM; HD];
    ALL_TAC] THEN
  ASM_MESON_TAC[same_type_trans]);;

(* HOL4 states evaluate_match_MAP with Q.prove and GEN_ALL: the outer      *)
(* variables are quantified here explicitly, before !l1 xs                  *)

let evaluate_match_MAP = prove
 (`!x1 x2 x3 t1 full_ps env (s:(FFI)state) vals err l1 xs.
     MEM (x1,x2,x3,t1) full_ps /\ ~(full_ps = []) /\
     good_cons_env full_ps env /\ set_of_list l1 SUBSET set_of_list full_ps /\
     ~MEM t1 (MAP (SND o SND o SND) l1) ==>
     evaluate_match s env (Conv (SOME t1) vals)
       (APPEND (MAP (\(name,vars,x,t). (Pcon (SOME name) (MAP Pvar vars),x)) l1) xs) err =
     evaluate_match s env (Conv (SOME t1) vals) xs err`,
  MAP_EVERY X_GEN_TAC [`x1:(mlstring,mlstring)id`; `x2:mlstring list`; `x3:exp`;
    `t1:stamp`; `full_ps:((mlstring,mlstring)id#mlstring list#exp#stamp)list`;
    `env:v sem_env`; `s:(FFI)state`; `vals:v list`; `err:v`] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; APPEND] THEN
  X_GEN_TAC `xs:(pat#exp)list` THEN
  PAIR_CASES_ON `h:(mlstring,mlstring)id#mlstring list#exp#stamp` THEN
  REWRITE_TAC[MAP; MEM; set_of_list; INSERT_SUBSET; IN_SET_OF_LIST; o_THM; DE_MORGAN_THM] THEN
  SIMP[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `xs:(pat#exp)list`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`full_ps:((mlstring,mlstring)id#mlstring list#exp#stamp)list`;
    `env:v sem_env`; `h0:(mlstring,mlstring)id`; `h1:mlstring list`; `h2:exp`; `h3:stamp`;
    `x1:(mlstring,mlstring)id`; `x2:mlstring list`; `x3:exp`; `t1:stamp`]
    TR2AUX_good_cons_env_MEM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [evaluate_match_def] THEN
  ASM_REWRITE_TAC[pat_bindings_def; pmatch_def] THEN CAKE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[same_ctor_def; LENGTH_MAP] THEN CAKE_REWRITE_TAC[]);;

(* HOL4: pmatch_list_MAP_Pvar (names.tsv ml_pmatch_list_MAP_Pvar); HOL4's   *)
(* ZIP (vars,vals) is ZIP vars vals (the lengths are equal)                  *)

let ml_pmatch_list_MAP_Pvar = prove
 (`!vars vals aux.
     LENGTH vars = LENGTH vals ==>
     pmatch_list env refs (MAP Pvar vars) vals aux =
     Match (APPEND (REVERSE (ZIP vars vals)) aux)`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP; LENGTH; NOT_SUC; SUC_INJ; ZIP; REVERSE; APPEND; pmatch_def] THEN
  CAKE_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  REWRITE_TAC[GSYM APPEND_ASSOC; APPEND]);;

let ml_write_list_def = cake_def
  `(ml_write_list [] (env:v sem_env) = env) /\
   (ml_write_list (CONS (n,v) xs) env = ml_write_list xs (ml_write n v env))`;;

let write_list_thm = prove
 (`!xs env.
     ml_write_list xs (env:v sem_env) =
     sem_env_v_fupd (combin_K (nsAppend (alist_to_ns (REVERSE xs)) (sem_env_v env))) env`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[ml_write_list_def; REVERSE; alist_to_ns_nil; nsAppend_nsEmpty] THEN
    REWRITE_TAC[sem_env_component_equality] THEN SIMP[];
    PAIR_CASES_ON `h:mlstring#v` THEN
    ASM_REWRITE_TAC[ml_write_list_def; ml_write_def; REVERSE] THEN
    GEN_TAC THEN REWRITE_TAC[sem_env_component_equality] THEN SIMP[] THEN
    MP_TAC(ISPEC `sem_env_v (env:v sem_env)` (case_info_of_tyname "namespace").ci_nchotomy) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[nsBind_def; nsAppend_def; alist_to_ns_def] THEN
    REWRITE_TAC[GSYM APPEND_ASSOC; APPEND]]);;

(* helpers of the port for IMP_Eval_Mat_cases: the INL and INR cases *)

let TR2AUX_Mat_cases_INL = prove
 (`!a (r1:A) env exp r2 vars x.
     ml_Eval env exp (a r1) /\
     ALL_DISTINCT (pats_bindings (MAP Pvar vars)) /\
     (!v. a r1 v ==>
          ?vals. v = Conv NONE vals /\ LENGTH vals = LENGTH vars /\
                 ml_Eval (ml_write_list (ZIP vars vals) env) x r2) ==>
     ml_Eval env (Mat exp [(Pcon NONE (MAP Pvar vars),x)]) r2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "h"))) THEN
  REWRITE_TAC[TR2AUX_Eval_any_clock] THEN DISCH_THEN(LABEL_TAC "e") THEN
  X_GEN_TAC `refs:(v store_v)list` THEN
  REMOVE_THEN "e" (X_CHOOSE_THEN `v1:v` (X_CHOOSE_THEN `rr1:(v store_v)list`
    STRIP_ASSUME_TAC) o SPEC `refs:(v store_v)list`) THEN
  REMOVE_THEN "h" (MP_TAC o SPEC `v1:v`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `vals:v list`
    (CONJUNCTS_THEN2 SUBST_ALL_TAC (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) MP_TAC))) THEN
  REWRITE_TAC[TR2AUX_Eval_any_clock] THEN
  DISCH_THEN(X_CHOOSE_THEN `v2:v` (X_CHOOSE_THEN `rr2:(v store_v)list`
    STRIP_ASSUME_TAC) o SPEC `APPEND refs rr1:(v store_v)list`) THEN
  MAP_EVERY EXISTS_TAC [`v2:v`; `APPEND rr1 rr2:(v store_v)list`] THEN
  ASM_REWRITE_TAC[APPEND_ASSOC] THEN MATCH_MP_TAC TR2AUX_EV_MAT THEN
  MAP_EVERY EXISTS_TAC [`APPEND refs rr1:(v store_v)list`; `Conv NONE vals`] THEN
  ASM_REWRITE_TAC[MAP; FST; can_pmatch_all_def; pmatch_def; LENGTH_MAP] THEN
  ASM_SIMP_TAC[ml_pmatch_list_MAP_Pvar; APPEND_NIL; distinctness "match_result"] THEN
  MATCH_MP_TAC TR2AUX_EV_MATCH_ROW THEN
  EXISTS_TAC `REVERSE (ZIP vars vals):(mlstring#v)list` THEN
  ASM_SIMP_TAC[pat_bindings_def; pmatch_def; LENGTH_MAP; ml_pmatch_list_MAP_Pvar;
    APPEND_NIL; GSYM write_list_thm]);;

let TR2AUX_Mat_cases_stamp = prove
 (`!ps l1 l2 (name:(mlstring,mlstring)id) (vars:mlstring list) (x:exp) (t:stamp).
     ALL_DISTINCT (MAP (SND o SND o SND) ps) /\
     ps = APPEND l1 (CONS (name,vars,x,t) l2) ==>
     ~MEM t (MAP (SND o SND o SND) l1) /\
     (!name' vars' x'. MEM (name',vars',x',t) ps ==> vars' = vars)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC SUBST1_TAC) THEN
  REWRITE_TAC[MAP_APPEND; MAP; ALL_DISTINCT_APPEND; ALL_DISTINCT; MEM_APPEND; MEM;
    o_THM] THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THENL
   [UNDISCH_TAC `!e:stamp.
       MEM e (MAP (SND o SND o SND)
         (l1:((mlstring,mlstring)id#mlstring list#exp#stamp)list)) ==>
       ~(e = t \/ MEM e (MAP (SND o SND o SND)
         (l2:((mlstring,mlstring)id#mlstring list#exp#stamp)list)))` THEN
    REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM; o_THM] THEN ASM_MESON_TAC[];
    RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `~MEM (t:stamp) (MAP (SND o SND o SND)
      (l2:((mlstring,mlstring)id#mlstring list#exp#stamp)list))` THEN
    REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM; o_THM] THEN ASM_MESON_TAC[]]);;

let TR2AUX_Mat_cases_INR = prove
 (`!a (r1:A) env exp r2 ps.
     ml_Eval env exp (a r1) /\
     ALL_DISTINCT (MAP (SND o SND o SND) ps) /\ good_cons_env ps env /\
     (!v. a r1 v ==>
          ?name vals t vars x.
            v = Conv (SOME t) vals /\ MEM (name,vars,x,t) ps /\
            LENGTH vals = LENGTH vars /\
            ml_Eval (ml_write_list (ZIP vars vals) env) x r2) ==>
     ml_Eval env
       (Mat exp (MAP (\(name,vars,x,t). (Pcon (SOME name) (MAP Pvar vars),x)) ps)) r2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "h")))) THEN
  REWRITE_TAC[TR2AUX_Eval_any_clock] THEN DISCH_THEN(LABEL_TAC "e") THEN
  X_GEN_TAC `refs:(v store_v)list` THEN
  REMOVE_THEN "e" (X_CHOOSE_THEN `v1:v` (X_CHOOSE_THEN `rr1:(v store_v)list`
    STRIP_ASSUME_TAC) o SPEC `refs:(v store_v)list`) THEN
  REMOVE_THEN "h" (MP_TAC o SPEC `v1:v`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `name:(mlstring,mlstring)id` (X_CHOOSE_THEN `vals:v list`
    (X_CHOOSE_THEN `t:stamp` (X_CHOOSE_THEN `vars:mlstring list` (X_CHOOSE_THEN `x:exp`
    (CONJUNCTS_THEN2 SUBST_ALL_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) MP_TAC)))))))) THEN
  REWRITE_TAC[TR2AUX_Eval_any_clock] THEN
  DISCH_THEN(X_CHOOSE_THEN `v2:v` (X_CHOOSE_THEN `rr2:(v store_v)list`
    STRIP_ASSUME_TAC) o SPEC `APPEND refs rr1:(v store_v)list`) THEN
  MAP_EVERY EXISTS_TAC [`v2:v`; `APPEND rr1 rr2:(v store_v)list`] THEN
  ASM_REWRITE_TAC[APPEND_ASSOC] THEN MATCH_MP_TAC TR2AUX_EV_MAT THEN
  MAP_EVERY EXISTS_TAC [`APPEND refs rr1:(v store_v)list`; `Conv (SOME t) vals`] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`ps:((mlstring,mlstring)id#mlstring list#exp#stamp)list`;
    `env:v sem_env`; `name:(mlstring,mlstring)id`; `vars:mlstring list`; `x:exp`;
    `t:stamp`; `name:(mlstring,mlstring)id`; `vars:mlstring list`; `x:exp`; `t:stamp`]
    TR2AUX_good_cons_env_MEM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `?l2. !st:(1)state.
      evaluate_match st env (Conv (SOME t) vals)
        (MAP (\(name,vars,x,t:stamp). (Pcon (SOME name) (MAP Pvar vars),x)) ps)
        bind_exn_v =
      evaluate_match st env (Conv (SOME t) vals)
        (CONS (Pcon (SOME name) (MAP Pvar vars),x) l2) bind_exn_v`
    STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(name,vars,x,t):(mlstring,mlstring)id#mlstring list#exp#stamp`;
      `ps:((mlstring,mlstring)id#mlstring list#exp#stamp)list`] MEM_APPEND_DECOMPOSE) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `l1:((mlstring,mlstring)id#mlstring list#exp#stamp)list`
      (X_CHOOSE_TAC `l2:((mlstring,mlstring)id#mlstring list#exp#stamp)list`)) THEN
    MP_TAC(ISPECL [`ps:((mlstring,mlstring)id#mlstring list#exp#stamp)list`;
      `l1:((mlstring,mlstring)id#mlstring list#exp#stamp)list`;
      `l2:((mlstring,mlstring)id#mlstring list#exp#stamp)list`;
      `name:(mlstring,mlstring)id`; `vars:mlstring list`; `x:exp`; `t:stamp`]
      TR2AUX_Mat_cases_stamp) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    EXISTS_TAC `MAP (\(name,vars,x,t:stamp). (Pcon (SOME name) (MAP Pvar vars),x))
      (l2:((mlstring,mlstring)id#mlstring list#exp#stamp)list)` THEN
    GEN_TAC THEN REWRITE_TAC[MAP_APPEND; MAP] THEN SIMP[] THEN
    MATCH_MP_TAC evaluate_match_MAP THEN
    MAP_EVERY EXISTS_TAC [`name:(mlstring,mlstring)id`; `vars:mlstring list`; `x:exp`;
      `ps:((mlstring,mlstring)id#mlstring list#exp#stamp)list`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[MEM]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_SET_OF_LIST] THEN ASM_REWRITE_TAC[MEM_APPEND] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `!name' vars' x'.
        MEM (name',vars',x',t) (ps:((mlstring,mlstring)id#mlstring list#exp#stamp)list) ==>
        vars' = vars`
      (LABEL_TAC "uniq") THENL
     [MP_TAC(ISPECL [`(name,vars,x,t):(mlstring,mlstring)id#mlstring list#exp#stamp`;
        `ps:((mlstring,mlstring)id#mlstring list#exp#stamp)list`] MEM_APPEND_DECOMPOSE) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_MESON_TAC[TR2AUX_Mat_cases_stamp];
      ALL_TAC] THEN
    REWRITE_TAC[can_pmatch_all_EVERY; MAP_MAP_o] THEN
    REWRITE_TAC[GSYM ALL_MEM; MEM_MAP; LEFT_IMP_EXISTS_THM; FORALL_PAIR_THM] THEN
    SIMP[o_THM] THEN
    MAP_EVERY X_GEN_TAC [`n':(mlstring,mlstring)id`; `vs':mlstring list`;
      `x':exp`; `t':stamp`] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`ps:((mlstring,mlstring)id#mlstring list#exp#stamp)list`;
      `env:v sem_env`; `n':(mlstring,mlstring)id`; `vs':mlstring list`; `x':exp`;
      `t':stamp`; `name:(mlstring,mlstring)id`; `vars:mlstring list`; `x:exp`; `t:stamp`]
      TR2AUX_good_cons_env_MEM) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[pmatch_def] THEN CAKE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[LENGTH_MAP; same_ctor_def] THEN
    ASM_CASES_TAC `t':stamp = t` THEN ASM_REWRITE_TAC[distinctness "match_result"] THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `vs':mlstring list = vars` SUBST_ALL_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SIMP_TAC[ASSUME `LENGTH (vars:mlstring list) = LENGTH (vals:v list)`;
      ml_pmatch_list_MAP_Pvar; distinctness "match_result"];
    ALL_TAC] THEN
  MATCH_MP_TAC TR2AUX_EV_MATCH_ROW THEN
  EXISTS_TAC `REVERSE (ZIP vars vals):(mlstring#v)list` THEN
  ASM_SIMP_TAC[pat_bindings_def; pmatch_def; LENGTH_MAP; ml_pmatch_list_MAP_Pvar;
    APPEND_NIL; GSYM write_list_thm] THEN
  CAKE_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[TR2AUX_same_type_refl; same_ctor_def; LENGTH_MAP; ml_pmatch_list_MAP_Pvar;
    APPEND_NIL; GSYM write_list_thm]);;

(* HOL4: IMP_Eval_Mat_cases.  The vacuous name and t of the INL branch are *)
(* given the types of the INR branch (HOL4 leaves them polymorphic), and    *)
(* HOL4 ZIP (vars,vals) is ZIP vars vals.                                   *)

let IMP_Eval_Mat_cases = prove
 (CASE_TERM `!a (r1:A) env exp r2 y.
     ml_Eval env exp (a r1) /\
     (match y with
        INL (vars,exp) ->
          ALL_DISTINCT (pats_bindings (MAP Pvar vars)) /\
          (!v. a r1 v ==>
               ?(name:(mlstring,mlstring)id) vals (t:stamp).
                 v = Conv NONE vals /\
                 LENGTH vals = LENGTH vars /\
                 ml_Eval (ml_write_list (ZIP vars vals) env) exp r2)
      | INR ps ->
          ALL_DISTINCT (MAP (SND o SND o SND) ps) /\
          good_cons_env ps env /\
          (!v. a r1 v ==>
               ?name vals t vars exp.
                 v = Conv (SOME t) vals /\
                 MEM (name,vars,exp,t) ps /\
                 LENGTH vals = LENGTH vars /\
                 ml_Eval (ml_write_list (ZIP vars vals) env) exp r2)) ==>
     ml_Eval env (Mat exp (Mat_cases y)) r2`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `y:(mlstring list#exp)+((mlstring,mlstring)id#mlstring list#exp#stamp)list`
    (case_info_of_tyname "sum").ci_nchotomy) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `p:mlstring list#exp` SUBST1_TAC)
    (X_CHOOSE_THEN `ps:((mlstring,mlstring)id#mlstring list#exp#stamp)list` SUBST1_TAC))
  THENL
   [PAIR_CASES_ON `p:mlstring list#exp` THEN
    CAKE_REWRITE_TAC[ml_Mat_cases_def] THEN REWRITE_TAC[EXISTS_SIMP] THEN
    MATCH_ACCEPT_TAC TR2AUX_Mat_cases_INL;
    CAKE_REWRITE_TAC[ml_Mat_cases_def] THEN
    MATCH_ACCEPT_TAC TR2AUX_Mat_cases_INR]);;

(* HOL4: Eval_Con_lemma [local] *)

let Eval_Con_lemma = prove
 (`!ps refs.
     (!p_1 p_2. MEM (p_1,p_2) ps ==> ml_Eval env p_2 p_1) ==>
     ?ck1 ck2 refs' vals.
       evaluate (state_clock_fupd (combin_K ck1) (state_refs_fupd (combin_K refs) ml_empty_state)) env
         (MAP SND ps) =
       (state_clock_fupd (combin_K ck2)
          (state_refs_fupd (combin_K (APPEND refs refs')) ml_empty_state),Rval vals) /\
       ALL2 (\(p,x) v. p v) ps vals`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`ps:((v->bool)#exp)list`; `env:v sem_env`; `refs:(v store_v)list`]
    TR2AUX_Eval_list) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:(v store_v)list` (X_CHOOSE_THEN `vals:v list`
    (CONJUNCTS_THEN2 (X_CHOOSE_TAC `c1:num` o SPEC `0`) ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`c1:num`; `0`; `r:(v store_v)list`; `vals:v list`] THEN
  ASM_REWRITE_TAC[]);;

let Eval_Con = prove
 (`!ps stamp.
     ml_lookup_cons name env = SOME (LENGTH ps,stamp) /\
     ALL (\(p,x). ml_Eval env x p) ps /\
     (!vals. ALL2 (\(p,x) v. p v) ps vals ==> q (Conv (SOME stamp) vals)) ==>
     ml_Eval env (Con (SOME name) (MAP SND ps)) q`,
  ACCEPT_TAC TR2AUX_Eval_Con);;

let Eval_Con_NONE = prove
 (`!ps.
     ALL (\(p,x). ml_Eval env x p) ps /\
     (!vals. ALL2 (\(p,x) v. p v) ps vals ==> q (Conv NONE vals)) ==>
     ml_Eval env (Con NONE (MAP SND ps)) q`,
  ACCEPT_TAC TR2AUX_Eval_Con_NONE);;

(* translation of a new ref *)

let ml_new_ref_thm = prove
 (`ml_Eval env e ((a:A->v->bool) x) ==>
   no_change_refs e ==>
   !refs. ?init_v loc_v.
     eval_rel (state_refs_fupd (combin_K refs) ml_empty_state) env (App Opref [e])
              (state_refs_fupd (combin_K (APPEND refs [Refv init_v])) ml_empty_state) loc_v /\
     a x init_v /\ loc_v = Loc T (LENGTH refs)`,
  REWRITE_TAC[ml_Eval_def] THEN DISCH_THEN(LABEL_TAC "e") THEN DISCH_TAC THEN
  X_GEN_TAC `refs:(v store_v)list` THEN
  REMOVE_THEN "e" (X_CHOOSE_THEN `res:v` (X_CHOOSE_THEN `rr:(v store_v)list`
    STRIP_ASSUME_TAC) o SPEC `refs:(v store_v)list`) THEN
  MP_TAC(ISPECL [`e:exp`; `state_refs_fupd (combin_K refs) ml_empty_state`;
    `state_refs_fupd (combin_K (APPEND refs rr)) ml_empty_state`; `env:v sem_env`; `res:v`]
    eval_rel_no_change_refs) THEN
  ASM_REWRITE_TAC[state_INFO.ri_accfupds; K_THM] THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  MAP_EVERY EXISTS_TAC [`res:v`; `Loc T (LENGTH (refs:(v store_v)list))`] THEN
  ASM_REWRITE_TAC[TR2AUX_eval_rel_any_clock] THEN
  MATCH_MP_TAC TR2AUX_EV_APP_SIMPLE THEN
  MAP_EVERY EXISTS_TAC [`refs:(v store_v)list`; `[res:v]`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[TR2AUX_eval_rel_any_clock]) THEN
  ASM_REWRITE_TAC[REVERSE; APPEND; getOpClass_def] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[do_app_def] THEN CAKE_REWRITE_TAC[store_alloc_def]);;
