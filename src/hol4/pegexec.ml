(* ========================================================================= *)
(* pegexec: port of HOL4 examples/formal-languages/context-free/            *)
(* pegexecScript.sml (HOL4 library used by CakeML v3479).                    *)
(* An executable interpreter for PEGs (a continuation-passing machine run   *)
(* by OWHILE), its equations, and its correctness against peg_eval.          *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - HOL4's local overloads OME and EOF are optmax MAXerr and                *)
(*   Locs EOFpt EOFpt; HOL4's let-bound error pairs in peg_exec_thm and      *)
(*   applykont_thm are substituted (the equations are otherwise HOL4's).     *)
(* - coreloop_def is HOL4's definition (OWHILE of the one-step function,    *)
(*   written with match); the wildcards of its patterns are named variables *)
(*   u1, u2, ... (unused).                                                   *)
(* - Renamed: destResult is pegexec_destResult (cmlParse defines its own);   *)
(*   the pegresult constructor Success of peg.ml is peg_Success.             *)
(* - Lemmas named LPARSEAUX_... are helpers of this unit (not HOL4 names);   *)
(*   LPARSEAUX_OWHILE_THM and LPARSEAUX_OWHILE_EQ_NONE are the While         *)
(*   theorems OWHILE_THM and OWHILE_EQ_NONE.                                 *)
(* - HOL4 done is pegexec_done (a short or common word).                     *)
(* ========================================================================= *)

needs "hol4/vocab.ml";;
needs "hol4/finite_map.ml";;
needs "hol4/location.ml";;
needs "hol4/peg.ml";;

(* ------------------------------------------------------------------------- *)
(* While: OWHILE (helpers of this unit).                                     *)
(* ------------------------------------------------------------------------- *)

let LPARSEAUX_OWHILE_THM = prove
 (`!(G:A->bool) f s. OWHILE G f s = if G s then OWHILE G f (f s) else SOME s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[OWHILE_DEF] THEN
  ASM_CASES_TAC `(G:A->bool) s` THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC;
    SUBGOAL_THEN `?n. ~(G:A->bool) (ITER n f s)` (fun th -> REWRITE_TAC[th]) THENL
     [EXISTS_TAC `0` THEN ASM_REWRITE_TAC[ITER]; ALL_TAC] THEN
    AP_TERM_TAC THEN
    SUBGOAL_THEN `(minimal n. ~(G:A->bool) (ITER n f s)) = 0`
      (fun th -> REWRITE_TAC[th; ITER]) THEN
    MATCH_MP_TAC MINIMAL_UNIQUE THEN ASM_REWRITE_TAC[ITER; LT]] THEN
  SUBGOAL_THEN `(?n. ~(G:A->bool) (ITER n f s)) <=> (?n. ~G (ITER n f (f s)))`
    SUBST1_TAC THENL
   [EQ_TAC THEN STRIP_TAC THENL
     [UNDISCH_TAC `~(G:A->bool) (ITER n f s)` THEN
      STRUCT_CASES_TAC(SPEC `n:num` num_CASES) THEN
      ASM_REWRITE_TAC[ITER_ALT] THEN MESON_TAC[];
      EXISTS_TAC `SUC n` THEN ASM_REWRITE_TAC[ITER_ALT]];
    ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN
  SUBGOAL_THEN
   `(minimal n. ~(G:A->bool) (ITER n f s)) =
    SUC (minimal n. ~G (ITER n f (f s)))`
    (fun th -> REWRITE_TAC[th; ITER_ALT]) THEN
  MATCH_MP_TAC MINIMAL_UNIQUE THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [MINIMAL]) THEN
  REWRITE_TAC[ITER_ALT] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[ITER_ALT; LT_SUC]);;

let LPARSEAUX_OWHILE_EQ_NONE = prove
 (`!(G:A->bool) f s. OWHILE G f s = NONE <=> !n. G (ITER n f s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[OWHILE_DEF] THEN
  COND_CASES_TAC THEN ASM_MESON_TAC[option_DISTINCT]);;

(* ------------------------------------------------------------------------- *)
(* The machine: continuations and states.                                    *)
(* ------------------------------------------------------------------------- *)

let kont_INDUCT,kont_RECURSION = cake_type
  "kont = ksym ((A,B,C,E)pegsym) kont kont
        | appf1 (C -> C) kont
        | appf2 (C -> C -> C) kont
        | dropErr kont
        | addErr locs E kont
        | cmpErrs kont
        | cmpEO ((locs # E) option) kont
        | returnTo ((A # locs) list) ((C option) list) kont
        | restoreEO ((locs # E) option) kont
        | poplist ((C list) -> C) kont
        | listsym ((A,B,C,E)pegsym) ((C list) -> C) kont
        | pegexec_done
        | failed";;

let kont_distinct = distinctness "kont";;
let kont_inject = injectivity "kont";;
let kont_CASE = case_def "kont";;
let kont_case_eq = case_eq "kont";;
let kont_nchotomy = cases "kont";;

let poplist_aux_def = cake_def
  `(poplist_aux (acc:C list) (CONS (SOME h) t) = poplist_aux (CONS h acc) t) /\
   (poplist_aux acc (CONS NONE t) = (acc,t)) /\
   (poplist_aux acc [] = (acc,[]))`;;

let poplistval_def = cake_def
  `poplistval (f:C list->C) l =
     match poplist_aux [] l with (values,rest) -> CONS (SOME (f values)) rest`;;

let evalcase_INDUCT,evalcase_RECURSION = cake_type
  "evalcase = pegexec_EV ((A,B,C,E)pegsym) ((A # locs) list) ((C option) list)
                 ((locs # E) option) ((locs # E) list)
                 ((A,B,C,E)kont) ((A,B,C,E)kont)
            | AP ((A,B,C,E)kont) ((A # locs) list) ((C option) list)
                 ((locs # E) option) ((locs # E) list)
            | Result (((A # locs) list,C,E)pegresult)
            | Looped";;

let evalcase_distinct = distinctness "evalcase";;
let evalcase_inject = injectivity "evalcase";;
let evalcase_CASE = case_def "evalcase";;
let evalcase_case_eq = case_eq "evalcase";;
let evalcase_nchotomy = cases "evalcase";;

let LPARSEAUX_option_nchotomy = cases "option";;

let LPARSEAUX_CASE_RWS = all_case_rewrites();;

let coreloop_def = cake_def
 `coreloop (G:(A,B,C,E)peg) =
   OWHILE (\s:(A,B,C,E)evalcase. match s with Result u1 -> F | u2 -> T)
    (\s. match s with
       pegexec_EV (empty v) i r eo errs k fk -> AP k i (CONS (SOME v) r) eo errs
     | pegexec_EV (peg_any tf) i r eo errs k fk ->
         (match i with
            [] -> (let err = (Locs EOFpt EOFpt, peg_anyEOF G)
                   in AP fk i r (optmax MAXerr eo (SOME err)) (CONS err errs))
          | CONS h t -> AP k t (CONS (SOME (tf h)) r) eo errs)
     | pegexec_EV (peg_tok P tf2) i r eo errs k fk ->
         (match i with
            [] -> (let err = (Locs EOFpt EOFpt, peg_tokEOF G)
                   in AP fk i r (optmax MAXerr eo (SOME err)) (CONS err errs))
          | CONS h t ->
              if P (FST h) then AP k t (CONS (SOME (tf2 h)) r) eo errs
              else (let err = (peg_sloc i, peg_tokFALSE G)
                    in AP fk i r (optmax MAXerr eo (SOME err)) (CONS err errs)))
     | pegexec_EV (peg_nt n tf3) i r eo errs k fk ->
         if n IN FDOM (peg_rules G)
         then pegexec_EV (FAPPLY (peg_rules G) n) i r eo errs (appf1 tf3 k) fk
         else Looped
     | pegexec_EV (peg_seq e1 e2 f) i r eo errs k fk ->
         pegexec_EV e1 i r eo errs
            (restoreEO eo (ksym e2 (appf2 f k) (cmpEO eo (returnTo i r fk))))
            fk
     | pegexec_EV (choice e1 e2 cf) i r eo errs k fk ->
         pegexec_EV e1 i r eo errs (appf1 (cf o INL) k)
            (returnTo i r (ksym e2 (dropErr (appf1 (cf o INR) k)) (cmpErrs fk)))
     | pegexec_EV (peg_rpt e lf) i r eo errs k fk ->
         pegexec_EV e i (CONS NONE r) eo errs (restoreEO eo (listsym e lf k))
            (poplist lf k)
     | pegexec_EV (peg_not e v) i r eo errs k fk ->
         pegexec_EV e i r eo errs
            (restoreEO eo (returnTo i r (addErr (peg_sloc i) (peg_notFAIL G) fk)))
            (restoreEO eo (returnTo i (CONS (SOME v) r) (dropErr k)))
     | pegexec_EV (peg_error err0) i r eo errs k fk ->
         (let err = (peg_sloc i, err0)
          in AP fk i r (optmax MAXerr eo (SOME err)) (CONS err errs))
     | AP pegexec_done i [] u3 u4 -> Looped
     | AP pegexec_done i (CONS NONE t) u5 u6 -> Looped
     | AP pegexec_done i (CONS (SOME rv) u7) eo u8 -> Result (peg_Success i rv eo)
     | AP failed i r u9 [] -> Looped
     | AP failed i r u10 (CONS (l,e) u11) -> Result (Failure l e)
     | AP (dropErr u12) i r u13 [] -> Looped
     | AP (dropErr k) i r eo (CONS u14 t) -> AP k i r eo t
     | AP (addErr l e k) i r eo errs ->
         AP k i r (optmax MAXerr eo (SOME (l,e))) (CONS (l,e) errs)
     | AP (cmpErrs k) i r u15 [] -> Looped
     | AP (cmpErrs k) i r u16 [u17] -> Looped
     | AP (cmpErrs k) i r eo (CONS (l2,er2) (CONS (l1,er1) rest)) ->
         AP k i r eo
            (CONS (if locsle l1 l2 then (l2,er2) else (l1,er1)) rest)
     | AP (cmpEO eo1 k) i r eo2 [] -> Looped
     | AP (cmpEO eo1 k) i r eo2 (CONS (l,err) rest) ->
         AP k i r (optmax MAXerr eo1 (SOME (l,err))) (CONS (l,err) rest)
     | AP (ksym e k fk) i r eo errs -> pegexec_EV e i r eo errs k fk
     | AP (appf1 f1 k) i (CONS (SOME v) r) eo errs ->
         AP k i (CONS (SOME (f1 v)) r) eo errs
     | AP (appf1 u18 u19) u20 u21 u22 u23 -> Looped
     | AP (appf2 f2 k) i (CONS (SOME v1) (CONS (SOME v2) r)) eo errs ->
         AP k i (CONS (SOME (f2 v2 v1)) r) eo errs
     | AP (appf2 u24 u25) u26 u27 u28 u29 -> Looped
     | AP (returnTo i r k) i' r' eo errs -> AP k i r eo errs
     | AP (restoreEO eo k) i r eo' errs -> AP k i r eo errs
     | AP (listsym e f k) i r eo errs ->
         pegexec_EV e i r eo errs (restoreEO eo (listsym e f k)) (poplist f k)
     | AP (poplist f k) i r eo [] -> Looped
     | AP (poplist f k) i r eo (CONS e errs) ->
         AP k i (poplistval f r) eo errs
     | Result r -> Result r
     | Looped -> Looped)`;;

let peg_exec_def = cake_def
  `peg_exec (G:(A,B,C,E)peg) e i r eo errs k fk =
     match coreloop G (pegexec_EV e i r eo errs k fk) with
       SOME res -> res
     | NONE -> Looped`;;

let applykont_def = cake_def
  `applykont (G:(A,B,C,E)peg) k i r eo errs =
     match coreloop G (AP k i r eo errs) with
       SOME res -> res
     | NONE -> Looped`;;

let LPARSEAUX_coreloop_THM =
  let th = SPEC `G:(A,B,C,E)peg` coreloop_def in
  let tm = rhs(concl th) in
  let g = rand(rator tm) and f = rand tm in
  let s = `s:(A,B,C,E)evalcase` in
  let cg = lhs(concl th) in
  let stmt = mk_forall(`G:(A,B,C,E)peg`, mk_forall(s,
    mk_eq(mk_comb(cg,s),
          mk_cond(mk_comb(g,s), mk_comb(cg,mk_comb(f,s)),
                  mk_comb(`SOME:(A,B,C,E)evalcase->((A,B,C,E)evalcase)option`,s))))) in
  prove(stmt,
    REPEAT GEN_TAC THEN GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV) [th] THEN
    GEN_REWRITE_TAC LAND_CONV [LPARSEAUX_OWHILE_THM] THEN
    REWRITE_TAC[GSYM th]);;

let coreloop_result = prove
 (`!(G:(A,B,C,E)peg) x. coreloop G (Result x) = SOME (Result x)`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [LPARSEAUX_coreloop_THM] THEN
  REWRITE_TAC(LPARSEAUX_CASE_RWS));;

let coreloop_Looped = prove
 (`!G:(A,B,C,E)peg. coreloop G Looped = NONE`,
  GEN_TAC THEN
  let th = SPEC `G:(A,B,C,E)peg` coreloop_def in
  let f = rand(rhs(concl th)) in
  let fix = prove
   (mk_eq(mk_comb(f,`Looped:(A,B,C,E)evalcase`),`Looped:(A,B,C,E)evalcase`),
    CONV_TAC(LAND_CONV BETA_CONV) THEN REWRITE_TAC LPARSEAUX_CASE_RWS) in
  REWRITE_TAC[th; LPARSEAUX_OWHILE_EQ_NONE] THEN
  REWRITE_TAC[MATCH_MP ITER_FIXPOINT fix] THEN REWRITE_TAC LPARSEAUX_CASE_RWS);;

(* ------------------------------------------------------------------------- *)
(* The equations of the interpreter.                                         *)
(* ------------------------------------------------------------------------- *)

let LPARSEAUX_EXEC_TAC : tactic =
  REPEAT GEN_TAC THEN REWRITE_TAC[peg_exec_def; applykont_def] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [LPARSEAUX_coreloop_THM] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC(LET_DEF :: LET_END_DEF :: LPARSEAUX_CASE_RWS) THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC(LET_DEF :: LET_END_DEF :: coreloop_result :: coreloop_Looped ::
              LPARSEAUX_CASE_RWS);;

let peg_exec_thm = prove
 (`(!(G:(A,B,C,E)peg) v i r eo errs k fk.
      peg_exec G (empty v) i r eo errs k fk =
      applykont G k i (CONS (SOME v) r) eo errs) /\
   (!(G:(A,B,C,E)peg) P f r eo errs k fk.
      peg_exec G (peg_tok P f) [] r eo errs k fk =
      applykont G fk [] r
        (optmax MAXerr eo (SOME (Locs EOFpt EOFpt, peg_tokEOF G)))
        (CONS (Locs EOFpt EOFpt, peg_tokEOF G) errs)) /\
   (!(G:(A,B,C,E)peg) P f x xs r eo errs k fk.
      peg_exec G (peg_tok P f) (CONS x xs) r eo errs k fk =
      if P (FST x) then applykont G k xs (CONS (SOME (f x)) r) eo errs
      else applykont G fk (CONS x xs) r
             (optmax MAXerr eo (SOME (peg_sloc (CONS x xs), peg_tokFALSE G)))
             (CONS (peg_sloc (CONS x xs), peg_tokFALSE G) errs)) /\
   (!(G:(A,B,C,E)peg) f r eo errs k fk.
      peg_exec G (peg_any f) [] r eo errs k fk =
      applykont G fk [] r
        (optmax MAXerr eo (SOME (Locs EOFpt EOFpt, peg_anyEOF G)))
        (CONS (Locs EOFpt EOFpt, peg_anyEOF G) errs)) /\
   (!(G:(A,B,C,E)peg) f x xs r eo errs k fk.
      peg_exec G (peg_any f) (CONS x xs) r eo errs k fk =
      applykont G k xs (CONS (SOME (f x)) r) eo errs) /\
   (!(G:(A,B,C,E)peg) e1 e2 sf i r eo errs k fk.
      peg_exec G (peg_seq e1 e2 sf) i r eo errs k fk =
      peg_exec G e1 i r eo errs
        (restoreEO eo (ksym e2 (appf2 sf k) (cmpEO eo (returnTo i r fk)))) fk) /\
   (!(G:(A,B,C,E)peg) e1 e2 cf i r eo errs k fk.
      peg_exec G (choice e1 e2 cf) i r eo errs k fk =
      peg_exec G e1 i r eo errs (appf1 (cf o INL) k)
        (returnTo i r (ksym e2 (dropErr (appf1 (cf o INR) k)) (cmpErrs fk)))) /\
   (!(G:(A,B,C,E)peg) e v i r eo errs k fk.
      peg_exec G (peg_not e v) i r eo errs k fk =
      peg_exec G e i r eo errs
        (restoreEO eo (returnTo i r (addErr (peg_sloc i) (peg_notFAIL G) fk)))
        (restoreEO eo (returnTo i (CONS (SOME v) r) (dropErr k)))) /\
   (!(G:(A,B,C,E)peg) e lf i r eo errs k fk.
      peg_exec G (peg_rpt e lf) i r eo errs k fk =
      peg_exec G e i (CONS NONE r) eo errs (restoreEO eo (listsym e lf k))
        (poplist lf k)) /\
   (!(G:(A,B,C,E)peg) err i r eo errs k fk.
      peg_exec G (peg_error err) i r eo errs k fk =
      applykont G fk i r (optmax MAXerr eo (SOME (peg_sloc i, err)))
        (CONS (peg_sloc i, err) errs))`,
  REPEAT CONJ_TAC THEN LPARSEAUX_EXEC_TAC THEN
  TRY(COND_CASES_TAC THEN REWRITE_TAC[]));;

let peg_nt_thm = prove
 (`!(G:(A,B,C,E)peg) n nfn i r eo errs k fk.
     peg_exec G (peg_nt n nfn) i r eo errs k fk =
     if n IN FDOM (peg_rules G)
     then peg_exec G (FAPPLY (peg_rules G) n) i r eo errs (appf1 nfn k) fk
     else Looped`,
  LPARSEAUX_EXEC_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC(coreloop_Looped :: LPARSEAUX_CASE_RWS));;

let applykont_thm = prove
 (`(!(G:(A,B,C,E)peg) e k fk i r eo errs.
      applykont G (ksym e k fk) i r eo errs = peg_exec G e i r eo errs k fk) /\
   (!(G:(A,B,C,E)peg) f k i v r eo errs.
      applykont G (appf1 f k) i (CONS (SOME v) r) eo errs =
      applykont G k i (CONS (SOME (f v)) r) eo errs) /\
   (!(G:(A,B,C,E)peg) f k i v1 v2 r eo errs.
      applykont G (appf2 f k) i (CONS (SOME v1) (CONS (SOME v2) r)) eo errs =
      applykont G k i (CONS (SOME (f v2 v1)) r) eo errs) /\
   (!(G:(A,B,C,E)peg) i' r' k i r eo errs.
      applykont G (returnTo i' r' k) i r eo errs = applykont G k i' r' eo errs) /\
   (!(G:(A,B,C,E)peg) l e k i r eo errs.
      applykont G (addErr l e k) i r eo errs =
      applykont G k i r (optmax MAXerr eo (SOME (l,e))) (CONS (l,e) errs)) /\
   (!(G:(A,B,C,E)peg) k i r eo.
      applykont G (dropErr k) i r eo [] = Looped) /\
   (!(G:(A,B,C,E)peg) k i r eo e errs.
      applykont G (dropErr k) i r eo (CONS e errs) =
      applykont G k i r eo errs) /\
   (!(G:(A,B,C,E)peg) k i r eo l1 er1 l2 er2 errs.
      applykont G (cmpErrs k) i r eo (CONS (l1,er1) (CONS (l2,er2) errs)) =
      applykont G k i r eo
        (CONS (if locsle l2 l1 then (l1,er1) else (l2,er2)) errs)) /\
   (!(G:(A,B,C,E)peg) i eo errs. applykont G pegexec_done i [] eo errs = Looped) /\
   (!(G:(A,B,C,E)peg) i rs eo errs.
      applykont G pegexec_done i (CONS NONE rs) eo errs = Looped) /\
   (!(G:(A,B,C,E)peg) i rv rs eo errs.
      applykont G pegexec_done i (CONS (SOME rv) rs) eo errs = Result (peg_Success i rv eo)) /\
   (!(G:(A,B,C,E)peg) i r eo. applykont G failed i r eo [] = Looped) /\
   (!(G:(A,B,C,E)peg) i r eo l e errs.
      applykont G failed i r eo (CONS (l,e) errs) = Result (Failure l e)) /\
   (!(G:(A,B,C,E)peg) f k i r eo.
      applykont G (poplist f k) i r eo [] = Looped) /\
   (!(G:(A,B,C,E)peg) f k i r eo le errs.
      applykont G (poplist f k) i r eo (CONS le errs) =
      applykont G k i (poplistval f r) eo errs) /\
   (!(G:(A,B,C,E)peg) e f k i r eo errs.
      applykont G (listsym e f k) i r eo errs =
      peg_exec G e i r eo errs (restoreEO eo (listsym e f k)) (poplist f k)) /\
   (!(G:(A,B,C,E)peg) eo0 k i r eo errs.
      applykont G (restoreEO eo0 k) i r eo errs = applykont G k i r eo0 errs) /\
   (!(G:(A,B,C,E)peg) eo0 k i r eo l err errs.
      applykont G (cmpEO eo0 k) i r eo (CONS (l,err) errs) =
      applykont G k i r (optmax MAXerr eo0 (SOME (l,err))) (CONS (l,err) errs))`,
  REPEAT CONJ_TAC THEN LPARSEAUX_EXEC_TAC);;

(* ------------------------------------------------------------------------- *)
(* Correctness of the interpreter.                                           *)
(* ------------------------------------------------------------------------- *)

(* HOL4: OME_NONE, OME_ASSOC (local; OME is optmax MAXerr) *)

let LPARSEAUX_OME_NONE = prove
 (`!eo:(locs#E)option.
     optmax MAXerr NONE eo = eo /\ optmax MAXerr eo NONE = eo`,
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `eo:(locs#E)option` LPARSEAUX_option_nchotomy) THEN
  REWRITE_TAC[optmax_def]);;

let LPARSEAUX_MAXerr_ASSOC = prove
 (`!e1 e2 e3:locs#E.
     MAXerr e1 (MAXerr e2 e3) = MAXerr (MAXerr e1 e2) e3`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`l1:locs`; `x1:E`; `l2:locs`; `x2:E`; `l3:locs`;
                       `x3:E`] THEN
  REWRITE_TAC[MAXerr_def] THEN
  MAP_EVERY ASM_CASES_TAC [`locsle l1 l2`; `locsle l2 l3`; `locsle l1 l3`] THEN
  ASM_REWRITE_TAC[MAXerr_def] THEN
  ASM_MESON_TAC[locsle_total; locsle_TRANS]);;

let LPARSEAUX_OME_ASSOC = prove
 (`!eo1 eo2 eo3:(locs#E)option.
     optmax MAXerr eo1 (optmax MAXerr eo2 eo3) =
     optmax MAXerr (optmax MAXerr eo1 eo2) eo3`,
  REPEAT GEN_TAC THEN
  MAP_EVERY (fun t -> STRUCT_CASES_TAC(ISPEC t LPARSEAUX_option_nchotomy))
    [`eo1:(locs#E)option`; `eo2:(locs#E)option`; `eo3:(locs#E)option`] THEN
  REWRITE_TAC[optmax_def; LPARSEAUX_MAXerr_ASSOC]);;

let MAXerr_id = prove
 (`!x:locs#E. MAXerr x x = x`,
  REWRITE_TAC[FORALL_PAIR_THM; MAXerr_def; locsle_REFL]);;

let LPARSEAUX_poplist_aux = prove
 (`!(vs:C list) a stk.
     poplist_aux a (APPEND (MAP SOME vs) (CONS NONE stk)) =
     (APPEND (REVERSE vs) a, stk)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[MAP; APPEND; REVERSE; poplist_aux_def; GSYM APPEND_ASSOC]);;

let LPARSEAUX_poplistval = prove
 (`!(f:C list->C) vs stk.
     poplistval f (APPEND (MAP SOME vs) (CONS NONE stk)) =
     CONS (SOME (f (REVERSE vs))) stk`,
  REWRITE_TAC[poplistval_def; LPARSEAUX_poplist_aux; APPEND_NIL] THEN
  REWRITE_TAC LPARSEAUX_CASE_RWS);;

let LPARSEAUX_EC_RWS =
  [GSYM CONJ_ASSOC; IMP_CONJ; RIGHT_FORALL_IMP_THM;
   FORALL_UNWIND_THM1; FORALL_UNWIND_THM2; LEFT_IMP_EXISTS_THM] @
  LPARSEAUX_RESULT_RWS;;

let LPARSEAUX_EXEC_FIN_RWS =
  [peg_exec_thm; peg_nt_thm; applykont_thm; LPARSEAUX_OME_NONE; peg_sloc_def;
   o_THM; LPARSEAUX_OME_ASSOC; LPARSEAUX_poplistval; APPEND_NIL];;

let LPARSEAUX_EC_NT_TAC : tactic =
  RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE LPARSEAUX_EC_RWS) THEN
  ASM_REWRITE_TAC LPARSEAUX_EXEC_FIN_RWS THEN NO_TAC;;

let LPARSEAUX_EC_CHOICE_TAC : tactic =
  FIRST_X_ASSUM(fun th -> if is_cond(concl th) then MP_TAC th
                          else failwith "") THEN
  COND_CASES_TAC THEN STRIP_TAC THEN RVEQ_TAC THEN
  ASM_REWRITE_TAC[GSYM LPARSEAUX_OME_ASSOC; optmax_def; MAXerr_def] THEN
  NO_TAC;;

let LPARSEAUX_INST_VS_TAC (inst_fn:term->term) : tactic =
  FIRST_X_ASSUM(fun th ->
    let th' = SPEC_ALL th in
    let vs = find (fun v -> fst(dest_var v) = "vs") (frees (concl th')) in
    let th'' = GEN_ALL(REWRITE_RULE[MAP; APPEND; REVERSE; GSYM APPEND_ASSOC]
                         (INST [inst_fn vs, vs] th')) in
    ASM_REWRITE_TAC[th''] THEN NO_TAC);;

let LPARSEAUX_EC_LIST_TAC : tactic =
  LPARSEAUX_INST_VS_TAC (fun _ -> `[]:C list`) ORELSE
  LPARSEAUX_INST_VS_TAC
    (fun vs -> mk_comb(mk_comb(`CONS:C->C list->C list`,`c:C`),vs));;

(* HOL4: exec_correct0 (local) *)

let LPARSEAUX_exec_correct0 = prove
 (`!G:(A,B,C,E)peg.
   (!i e r. peg_eval G (i,e) r ==>
     (!j v eo eo0 k fk stk errs.
        r = peg_Success j v eo ==>
        peg_exec G e i stk eo0 errs k fk =
        applykont G k j (CONS (SOME v) stk) (optmax MAXerr eo0 eo) errs) /\
     (!k fk stk eo errs l err.
        r = Failure l err ==>
        peg_exec G e i stk eo errs k fk =
        applykont G fk i stk (optmax MAXerr eo (SOME (l,err)))
          (CONS (l,err) errs))) /\
   (!i e j vlist err.
     peg_eval_list G (i,e) (j,vlist,err) ==>
     !f k stk eo errs vs.
       peg_exec G e i (APPEND (MAP SOME vs) (CONS NONE stk)) eo errs
                (restoreEO eo (listsym e f k)) (poplist f k) =
       applykont G k j (CONS (SOME (f (APPEND (REVERSE vs) vlist))) stk)
                 (optmax MAXerr eo (SOME err)) errs)`,
  GEN_TAC THEN MATCH_MP_TAC peg_eval_strongind' THEN REPEAT CONJ_TAC THEN
  REPEAT GEN_TAC THEN TRY(DISCH_THEN STRIP_ASSUME_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LPARSEAUX_isSuccess_EXISTS;
                              LPARSEAUX_isFailure_EXISTS]) THEN
  LPARSEAUX_STRIP_EX_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE LPARSEAUX_EC_RWS) THEN
  REWRITE_TAC LPARSEAUX_EC_RWS THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC LPARSEAUX_EXEC_FIN_RWS THEN
  TRY(FIRST [LPARSEAUX_EC_NT_TAC; LPARSEAUX_EC_CHOICE_TAC;
             LPARSEAUX_EC_LIST_TAC]));;

let exec_correct = prove
 (`!G:(A,B,C,E)peg.
   (!i e j v eo eo0 k fk stk errs.
      peg_eval G (i,e) (peg_Success j v eo) ==>
      peg_exec G e i stk eo0 errs k fk =
      applykont G k j (CONS (SOME v) stk) (optmax MAXerr eo0 eo) errs) /\
   (!i e k fk stk eo errs l err.
      peg_eval G (i,e) (Failure l err) ==>
      peg_exec G e i stk eo errs k fk =
      applykont G fk i stk (optmax MAXerr eo (SOME (l,err)))
        (CONS (l,err) errs)) /\
   (!i e j vlist err f k stk eo errs vs.
      peg_eval_list G (i,e) (j,vlist,err) ==>
      peg_exec G e i (APPEND (MAP SOME vs) (CONS NONE stk)) eo errs
               (restoreEO eo (listsym e f k)) (poplist f k) =
      applykont G k j (CONS (SOME (f (APPEND (REVERSE vs) vlist))) stk)
                (optmax MAXerr eo (SOME err)) errs)`,
  GEN_TAC THEN MP_TAC(SPEC `G:(A,B,C,E)peg` LPARSEAUX_exec_correct0) THEN
  MESON_TAC[]);;

let pegexec_succeeds = prove
 (`!(G:(A,B,C,E)peg) i e j v eo eo0.
     peg_eval G (i,e) (peg_Success j v eo) ==>
     peg_exec G e i [] eo0 [] pegexec_done failed =
     Result (peg_Success j v (optmax MAXerr eo0 eo))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP (CONJUNCT1 (SPEC_ALL exec_correct)) th]) THEN
  REWRITE_TAC[applykont_thm]);;

let pegexec_fails = prove
 (`!(G:(A,B,C,E)peg) i e eo l err.
     peg_eval G (i,e) (Failure l err) ==>
     peg_exec G e i [] eo [] pegexec_done failed = Result (Failure l err)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP
    (CONJUNCT1(CONJUNCT2 (SPEC_ALL exec_correct))) th]) THEN
  REWRITE_TAC[applykont_thm]);;

let pegexec = prove
 (`!(G:(A,B,C,E)peg) s e r.
     peg_eval G (s,e) r ==> peg_exec G e s [] NONE [] pegexec_done failed = Result r`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `r:((A#locs)list,C,E)pegresult` pegresult_nchotomy) THEN
  DISCH_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP pegexec_succeeds);
    FIRST_ASSUM(MP_TAC o MATCH_MP pegexec_fails)] THEN
  SIMP_TAC[LPARSEAUX_OME_NONE]);;

let peg_eval_executed = prove
 (`!(G:(A,B,C,E)peg) e s r.
     wfG G /\ e IN Gexprs G ==>
     (peg_eval G (s,e) r <=> peg_exec G e s [] NONE [] pegexec_done failed = Result r)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL [MESON_TAC[pegexec]; ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(SPEC `G:(A,B,C,E)peg` peg_eval_total) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`s:(A#locs)list`; `e:(A,B,C,E)pegsym`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `r':((A#locs)list,C,E)pegresult`) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP pegexec) THEN
  ASM_REWRITE_TAC[evalcase_inject] THEN DISCH_THEN SUBST_ALL_TAC THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Parsing with the interpreter; totality.                                   *)
(* ------------------------------------------------------------------------- *)

(* HOL4: destResult (cmlParse defines its own destResult) *)

let pegexec_destResult_def = new_recursive_definition evalcase_RECURSION
  `pegexec_destResult (Result (r:((A#locs)list,C,E)pegresult):(A,B,C,E)evalcase) = r`;;

let pegparse_def = cake_def
  `pegparse (G:(A,B,C,E)peg) s =
     if wfG G then
       match pegexec_destResult (peg_exec G (peg_start G) s [] NONE [] pegexec_done failed)
       with peg_Success s v eo -> SOME (s,v,eo)
          | u1 -> NONE
     else NONE`;;

let LPARSEAUX_peg_eval_start = prove
 (`!(G:(A,B,C,E)peg) s.
     wfG G ==> ?r. peg_eval G (s,peg_start G) r`,
  MESON_TAC[peg_eval_total; start_IN_Gexprs]);;

let pegparse_eq_SOME = prove
 (`!(G:(A,B,C,E)peg) s s' v eo.
     pegparse G s = SOME (s', v, eo) <=>
     wfG G /\ peg_eval G (s,peg_start G) (peg_Success s' v eo)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `wfG (G:(A,B,C,E)peg)` THEN
  ASM_REWRITE_TAC[pegparse_def; option_DISTINCT] THEN
  FIRST_ASSUM(X_CHOOSE_TAC `r:((A#locs)list,C,E)pegresult` o
    SPEC `s:(A#locs)list` o MATCH_MP LPARSEAUX_peg_eval_start) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP pegexec th]) THEN
  REWRITE_TAC[pegexec_destResult_def] THEN
  MP_TAC(SPEC `G:(A,B,C,E)peg` peg_deterministic) THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  DISCH_THEN(fun th -> FIRST_ASSUM(fun th' -> REWRITE_TAC[MATCH_MP th th'])) THEN
  STRUCT_CASES_TAC(ISPEC `r:((A#locs)list,C,E)pegresult` pegresult_nchotomy) THEN
  REWRITE_TAC(option_INJ :: PAIR_EQ :: option_DISTINCT :: LPARSEAUX_CASE_RWS) THEN
  MESON_TAC[]);;

let pegparse_eq_NONE = prove
 (`!(G:(A,B,C,E)peg) s.
     pegparse G s = NONE <=>
     ~wfG G \/ ?l e. peg_eval G (s,peg_start G) (Failure l e)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `wfG (G:(A,B,C,E)peg)` THEN
  ASM_REWRITE_TAC[pegparse_def] THEN
  FIRST_ASSUM(X_CHOOSE_TAC `r:((A#locs)list,C,E)pegresult` o
    SPEC `s:(A#locs)list` o MATCH_MP LPARSEAUX_peg_eval_start) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP pegexec th]) THEN
  REWRITE_TAC[pegexec_destResult_def] THEN
  MP_TAC(SPEC `G:(A,B,C,E)peg` peg_deterministic) THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  DISCH_THEN(fun th -> FIRST_ASSUM(fun th' -> REWRITE_TAC[MATCH_MP th th'])) THEN
  STRUCT_CASES_TAC(ISPEC `r:((A#locs)list,C,E)pegresult` pegresult_nchotomy) THEN
  REWRITE_TAC(option_INJ :: PAIR_EQ :: option_DISTINCT :: LPARSEAUX_CASE_RWS) THEN
  MESON_TAC[]);;

let peg_exec_total = prove
 (`!(G:(A,B,C,E)peg) i.
     wfG G ==> ?r. peg_exec G (peg_start G) i [] NONE [] pegexec_done failed = Result r`,
  MESON_TAC[LPARSEAUX_peg_eval_start; pegexec]);;

let coreloop_total = prove
 (`!(G:(A,B,C,E)peg) i.
     wfG G ==>
     ?r. coreloop G (pegexec_EV (peg_start G) i [] NONE [] pegexec_done failed) = SOME (Result r)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_TAC `r:((A#locs)list,C,E)pegresult` o
    SPEC `i:(A#locs)list` o MATCH_MP peg_exec_total) THEN
  EXISTS_TAC `r:((A#locs)list,C,E)pegresult` THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[peg_exec_def] THEN
  STRUCT_CASES_TAC(ISPEC
    `coreloop (G:(A,B,C,E)peg) (pegexec_EV (peg_start G) i [] NONE [] pegexec_done failed)`
    LPARSEAUX_option_nchotomy) THEN
  REWRITE_TAC(option_INJ :: evalcase_distinct :: LPARSEAUX_CASE_RWS));;

(* ------------------------------------------------------------------------- *)
(* The HOL4 [simp] theorems of this theory, for the project simpset.         *)
(* ------------------------------------------------------------------------- *)

let _ = cake_add_simps
  [coreloop_result; coreloop_Looped; MAXerr_id; pegexec_destResult_def];;
