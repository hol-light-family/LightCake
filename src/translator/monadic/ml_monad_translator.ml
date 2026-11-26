(* ========================================================================= *)
(* ml_monad_translator: port of HOL4                                         *)
(* translator/monadic/ml_monad_translatorScript.sml (CakeML v3479).          *)
(* Defines EvalM and other judgements that are central to the monadic       *)
(* translator.                                                               *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - EvalM_PMATCH_NIL and EvalM_PMATCH (ml_pmatch) are not ported (D5).      *)
(* - HOL4 star is STAR, its & is set_sep_cond, REF is cf_REF, ARRAY is      *)
(*   cf_ARRAY, GC is cf_GC, emp is set_sep_emp; HOL4 () is one; the unit    *)
(*   state of EvalSt is (1)state; Eval, write, lookup_cons, NUM, CONTAINER, *)
(*   PRECONDITION, PreImp are ml_translator's ml_ constants; run is         *)
(*   ml_monadBase_run.                                                       *)
(* - Bound variables renamed: HOL4 F is F', abs (EqSt_def) is ab, init_state *)
(*   (EvalM_to_EvalSt) is init_st: F and abs are HOL Light constants,      *)
(*   init_state a constant of compiler/inference/infer.ml.                  *)
(* - HOL4 ZIP (a,b) is ZIP a b; FOLDR f e l is ITLIST f l e; MAP (\(f,x,e).  *)
(*   f) funs is written with match, as in LightCake's evaluate_def.          *)
(* - HOL4's EVAL-computed Conv_Subscript and Stamp_Subscript are written    *)
(*   Conv (SOME (ExnStamp 3)) [] and ExnStamp 3; mlstring literals such as  *)
(*   Subscript are implode of a string.                                      *)
(* - Vacuous quantified variables get a type: x (EvalM_R/F_Marray_length)   *)
(*   is x:A, st_name (EvalSt_Opref, EvalSt_AllocEmpty) is an mlstring, the  *)
(*   name and t of the INL branch of IMP_EvalM_Mat_cases have the types of  *)
(*   the INR branch.                                                         *)
(* - LOOKUP_ASSUM_SIMP is end_itlist CONJ of its theorems; EVAL_T_F and      *)
(*   EVAL_PRECONDITION_T are proved statements of HOL4's EVAL results.      *)
(* - MON1AUX_ names are helpers of this port; MON1AUX_store2heap_REF_SAT is *)
(*   ml_monadStore's store2heap_REF_SAT (that theory is not an ancestor).   *)
(* ========================================================================= *)

needs "hol4/set_sep.ml";;
needs "semantics/proofs/evaluateProps.ml";;
needs "translator/ml_prog.ml";;
needs "translator/ml_translator.ml";;
needs "translator/monadic/monad_base/ml_monadBase.ml";;
needs "characteristic/cfHeapsBase.ml";;
needs "characteristic/cfStore.ml";;
needs "characteristic/cfLetAuto.ml";;
needs "translator/monadic/ml_monad_translatorBase.ml";;

type_invention_error := true;;

(* TODO: move *)
let s_with_same_clock = prove
 (`!s:(FFI)state. state_clock_fupd (combin_K (state_clock s)) s = s`,
  REWRITE_TAC[ml_monad_translatorBase_with_same_clock]);;
let _ = cake_add_simps [s_with_same_clock];;
(* -- *)

let ml_monad_translator_GC_ABSORB_L = prove
 (`!A B s. (A STAR B STAR cf_GC) s ==> (A STAR cf_GC) s`,
  REWRITE_TAC[ml_monad_translatorBase_GC_ABSORB_L]);;

let GC_ABSORB_R = prove
 (`!A B s. (A STAR cf_GC STAR B) s ==> (A STAR cf_GC) s`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `A STAR cf_GC STAR B = A STAR B STAR cf_GC` SUBST1_TAC THENL
   [MESON_TAC[STAR_COMM; STAR_ASSOC];
    REWRITE_TAC[ml_monad_translator_GC_ABSORB_L]]);;

let REF_EXISTS_LOC = prove
 (`(cf_REF rv v STAR H) s ==> ?l. rv = Loc T l`,
  REWRITE_TAC[cf_REF_def; SEP_CLAUSES; SEP_EXISTS_THM; GSYM STAR_ASSOC;
    cf_HCOND_EXTRACT] THEN
  MESON_TAC[]);;

let ARRAY_EXISTS_LOC = prove
 (`(cf_ARRAY rv v STAR H) s ==> ?l. rv = Loc T l`,
  REWRITE_TAC[cf_ARRAY_def; SEP_CLAUSES; SEP_EXISTS_THM; GSYM STAR_ASSOC;
    cf_HCOND_EXTRACT] THEN
  MESON_TAC[]);;

let UNIQUE_CELLS = prove
 (`!p (s:(FFI)state) l xv xv' H H'.
     (cf_cell l xv STAR H) (st2heap p s) /\ (cf_cell l xv' STAR H') (st2heap p s) ==>
     xv' = xv`,
  REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP st2heap_CELL_MEM)) THEN
  ASM_MESON_TAC[store2heap_IN_unique_key]);;

(* HOL4's list_dest, dest_pure_fact (from cfLetAutoLib), PURE_FACTS_FIRST_CONV, *)
(* EXTRACT_PURE_FACTS_CONV and EXTRACT_PURE_FACTS_TAC are SML functions of   *)
(* the script; here MON1AUX_list_star, MON1AUX_is_pure_fact,                  *)
(* MON1AUX_PURE_FACTS_FIRST_CONV, MON1AUX_EXTRACT_PURE_FACTS_CONV and         *)
(* MON1AUX_EXTRACT_PURE_FACTS_TAC (HOL4's STAR_AC_CONV is AC with             *)
(* LSORTAUX_STAR_AC of set_sep.ml).                                           *)

let MON1AUX_dest_star tm =
  match tm with
    Comb(Comb(Const("STAR",_),p),q) -> p,q
  | _ -> failwith "MON1AUX_dest_star";;

let rec MON1AUX_list_star tm =
  try let p,q = MON1AUX_dest_star tm in MON1AUX_list_star p @ MON1AUX_list_star q
  with Failure _ -> [tm];;

let MON1AUX_is_pure_fact tm =
  match tm with
    Comb(Const("set_sep_cond",_),_) -> true
  | _ -> false;;

let MON1AUX_PURE_FACTS_FIRST_CONV tm =
  let preds = MON1AUX_list_star tm in
  let pfl,hpl = partition MON1AUX_is_pure_fact preds in
  match pfl @ hpl with
    [] | [_] -> REFL tm
  | h::t ->
      let star = rator(rator tm) in
      let tm' = itlist (fun x acc -> mk_comb(mk_comb(star,acc),x)) (rev t) h in
      if tm' = tm then REFL tm else AC LSORTAUX_STAR_AC (mk_eq(tm,tm'));;

let MON1AUX_EXTRACT_PURE_FACTS_CONV =
  RATOR_CONV MON1AUX_PURE_FACTS_FIRST_CONV THENC
  PURE_REWRITE_CONV[GSYM STAR_ASSOC] THENC
  PURE_REWRITE_CONV[cf_HCOND_EXTRACT] THENC
  PURE_REWRITE_CONV[STAR_ASSOC];;

let MON1AUX_EXTRACT_PURE_FACTS_TAC : tactic = fun (asl,w as g) ->
  let is_hprop a = try type_of (rator a) = `:hprop` with Failure _ -> false in
  let hps = filter is_hprop (map (concl o snd) asl) in
  let eqs = mapfilter (fun a -> let th = MON1AUX_PURE_FACTS_FIRST_CONV (rator a) in
                                let l,r = dest_eq (concl th) in
                                if l = r then fail() else th) hps in
  (RFS eqs THEN RFS[GSYM STAR_ASSOC] THEN RFS[cf_HCOND_EXTRACT] THEN
   RFS[STAR_ASSOC]) g;;

(* HOL4: Type state = ``:'ffi semanticPrimitives$state`` (names.tsv         *)
(* ml_monad_translator_state), written (FFI)state.                           *)

(* Definition of EvalM; ro: references only *)

let EvalM_def = cake_def
  `EvalM ro env (st:REFS) exp (P:REFS->REFS#(v list,v)result->bool) H <=>
     !(s:(FFI)state).
       REFS_PRED H st s ==>
       ?s2 res st2 ck.
         evaluate (state_clock_fupd (combin_K ck) s) env [exp] = (s2,res) /\
         P st (st2,res) /\ REFS_PRED_FRAME ro H (st,s) (st2,s2)`;;

(* refinement invariant for (REFS,A,B) M = REFS->(A,B)exc#REFS (HOL4 Type M,  *)
(* names.tsv ml_monad_translator_M, written out)                             *)

let MONAD_def = cake_def
  `MONAD (a:A->v->bool) (b:B->v->bool) (x:REFS->(A,B)exc#REFS) (state1:REFS)
         (state2,(res:(v list,v)result)) <=>
     match (x state1,res) with
       ((M_success y,st),Rval [v]) -> st = state2 /\ a y v
     | ((M_failure e,st),Rerr (Rraise v)) -> st = state2 /\ b e v
     | _ -> F`;;

(* Eval gives an evaluation from any state, to any final clock (HOL4's proofs *)
(* do this with evaluate_empty_state_IMP, eval_rel_def and                    *)
(* evaluate_set_clock at each use)                                            *)

let MON1AUX_Eval_evaluate = prove
 (`!env exp P. ml_Eval env exp P ==>
     !s:(FFI)state. ?res refs'. P res /\
       !ck. ?ck1.
         evaluate (state_clock_fupd (combin_K ck1) s) env [exp] =
         (state_clock_fupd (combin_K ck) (state_refs_fupd (combin_K (APPEND (state_refs s) refs')) s),
          Rval [res])`,
  REWRITE_TAC[ml_Eval_def] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `res:v` (X_CHOOSE_THEN `refs':(v store_v)list`
    STRIP_ASSUME_TAC) o SPEC `state_refs (s:(FFI)state)`) THEN
  MAP_EVERY EXISTS_TAC [`res:v`; `refs':(v store_v)list`] THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP evaluate_empty_state_IMP) THEN
  REWRITE_TAC[eval_rel_def] THEN SIMP[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] evaluate_set_clock)) THEN
  REWRITE_TAC[distinctness "result"] THEN SIMP[]);;

(* return *)

let EvalM_return = prove
 (`!(H:(REFS->hprop)#((FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)))
    (b:B->v->bool).
     ml_Eval env exp ((a:A->v->bool) x) ==>
     EvalM ro env st exp (MONAD a b (st_ex_return x)) H`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EvalM_def] THEN X_GEN_TAC `s:(FFI)state` THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `s:(FFI)state` o MATCH_MP MON1AUX_Eval_evaluate) THEN
  DISCH_THEN(X_CHOOSE_THEN `res:v` (X_CHOOSE_THEN `refs':(v store_v)list`
    (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `state_clock (s:(FFI)state)`)))) THEN
  DISCH_THEN(X_CHOOSE_TAC `ck1:num`) THEN
  MAP_EVERY EXISTS_TAC
   [`state_refs_fupd (combin_K (APPEND (state_refs s) refs')) (s:(FFI)state)`;
    `Rval [res]:(v list,v)result`; `st:REFS`; `ck1:num`] THEN
  ASM_REWRITE_TAC[REFS_PRED_FRAME_append] THEN CONJ_TAC THENL
   [SIMP[state_component_equality];
    REWRITE_TAC[MONAD_def; st_ex_return_def] THEN CAKE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[]]);;

(* Helpers for the EvalM proofs: a MONAD result is never a timeout, so an    *)
(* EvalM evaluation can be run to any final clock (HOL4's proofs apply        *)
(* evaluate_set_clock at each use).                                           *)

let MON1AUX_MONAD_not_timeout = prove
 (`!(a:A->v->bool) (b:B->v->bool) (x:REFS->(A,B)exc#REFS) st st2 res.
     MONAD a b x st (st2,res) ==> ~(res = Rerr (Rabort Rtimeout_error))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MONAD_def] THEN
  REPEAT(TOP_CASE_TAC THEN SIMP[]));;

let MON1AUX_MONAD_eq = prove
 (`!(a:A->v->bool) (b:B->v->bool) (x:REFS->(A,B)exc#REFS) x' st st'.
     x st = x' st' ==> MONAD a b x st = MONAD a b x' st'`,
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; MONAD_def] THEN SIMP[]);;

let MON1AUX_EvalM_run = prove
 (`!ro env (st:REFS) exp P H (s:(FFI)state).
     EvalM ro env st exp P H /\
     (!st2 res. P st (st2,res) ==> ~(res = Rerr (Rabort Rtimeout_error))) /\
     REFS_PRED H st s ==>
     ?s2 res st2.
       P st (st2,res) /\ REFS_PRED_FRAME ro H (st,s) (st2,s2) /\
       !ck. ?ck1. evaluate (state_clock_fupd (combin_K ck1) s) env [exp] =
                  (state_clock_fupd (combin_K ck) s2,res)`,
  REWRITE_TAC[EvalM_def] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:(FFI)state`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s2:(FFI)state` (X_CHOOSE_THEN `res:(v list,v)result`
    (X_CHOOSE_THEN `st2:REFS` (X_CHOOSE_THEN `ck:num` STRIP_ASSUME_TAC)))) THEN
  MAP_EVERY EXISTS_TAC [`s2:(FFI)state`; `res:(v list,v)result`; `st2:REFS`] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] evaluate_set_clock)) THEN
  ASM_SIMP_TAC[] THEN SIMP[]);;

let MON1AUX_evaluate_Let_Rval = prove
 (`!(s:(FFI)state) env xo e1 e2 s1 v.
     evaluate s env [e1] = (s1,Rval [v]) ==>
     evaluate s env [Let xo e1 e2] =
     evaluate s1 (sem_env_v_fupd (combin_K (nsOptBind xo v (sem_env_v env))) env) [e2]`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[evaluate_def] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[HD]);;

let MON1AUX_evaluate_Let_Rerr = prove
 (`!(s:(FFI)state) env xo e1 e2 s1 err.
     evaluate s env [e1] = (s1,Rerr err) ==>
     evaluate s env [Let xo e1 e2] = (s1,Rerr err)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[evaluate_def] THEN CAKE_REWRITE_TAC[]);;

let MON1AUX_MONAD_THM = prove
 (`!(a:A->v->bool) (b:B->v->bool) (x:REFS->(A,B)exc#REFS) st st2 res.
     MONAD a b x st (st2,res) <=>
     (?y v. x st = (M_success y,st2) /\ res = Rval [v] /\ a y v) \/
     (?e v. x st = (M_failure e,st2) /\ res = Rerr (Rraise v) /\ b e v)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MONAD_def] THEN
  PAIR_CASES_ON `(x:REFS->(A,B)exc#REFS) st` THEN ASM_REWRITE_TAC[] THEN
  REPEAT(TOP_CASE_TAC THEN SIMP[]) THEN MESON_TAC[]);;

let MON1AUX_EvalM_MONAD_run = prove
 (`!ro env (st:REFS) exp (a:A->v->bool) (b:B->v->bool) x H (s:(FFI)state).
     EvalM ro env st exp (MONAD a b x) H /\ REFS_PRED H st s ==>
     ?s2 res st2.
       MONAD a b x st (st2,res) /\ REFS_PRED_FRAME ro H (st,s) (st2,s2) /\
       !ck. ?ck1. evaluate (state_clock_fupd (combin_K ck1) s) env [exp] =
                  (state_clock_fupd (combin_K ck) s2,res)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MON1AUX_EvalM_run THEN
  REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[MON1AUX_MONAD_not_timeout]);;

let MON1AUX_nsOptBind_write = prove
 (`!name v (env:v sem_env).
     sem_env_v_fupd (combin_K (nsOptBind (SOME name) v (sem_env_v env))) env = ml_write name v env`,
  REWRITE_TAC[nsOptBind_def; ml_write_def] THEN CAKE_REWRITE_TAC[]);;

let MON1AUX_nsOptBind_NONE = prove
 (`!v (env:v sem_env). sem_env_v_fupd (combin_K (nsOptBind NONE v (sem_env_v env))) env = env`,
  REWRITE_TAC[nsOptBind_def; sem_env_component_equality] THEN CAKE_REWRITE_TAC[] THEN
  SIMP[]);;

(* closing REFS_PRED and REFS_PRED_FRAME goals from the assumptions        *)

let MON1AUX_FRAME_IMP_TAC : tactic =
  FIRST_ASSUM(fun rp -> FIRST_ASSUM(fun fr ->
    ACCEPT_TAC(MATCH_MP (MATCH_MP REFS_PRED_FRAME_imp rp) fr)));;

let MON1AUX_FRAME_trans = GEN_ALL REFS_PRED_FRAME_trans;;

let MON1AUX_FRAME_CHAIN_TAC : tactic =
  let is_frame th = try fst(dest_const(fst(strip_comb(concl th)))) = "REFS_PRED_FRAME"
                    with Failure _ -> false in
  let rec chain (asl,w as g) =
    if exists (fun (_,th) -> concl th = w) asl then FIRST_ASSUM ACCEPT_TAC g else
    let frs = filter is_frame (map snd asl) in
    let news = mapfilter (fun (fa,fb) -> MATCH_MP (MATCH_MP MON1AUX_FRAME_trans fa) fb)
                 (allpairs (fun a b -> (a,b)) frs frs) in
    let olds = map concl frs in
    let news = filter (fun th -> not (mem (concl th) olds)) news in
    if news = [] then failwith "MON1AUX_FRAME_CHAIN_TAC" else
    (MAP_EVERY ASSUME_TAC news THEN chain) g in
  chain;;

(* bind *)

let EvalM_bind = prove
 (`(a1 ==> EvalM ro env st e1 (MONAD b c (x:REFS->(B,C)exc#REFS))
             (H:(REFS->hprop)#((FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)))) /\
   (!z v. b z v ==> a2 z ==>
      EvalM ro (ml_write name v env) (SND (x st)) e2
        (MONAD (a:A->v->bool) c ((f:B->REFS->(A,C)exc#REFS) z)) H) ==>
   (a1 /\ !z. (ml_CONTAINER (FST (x st) = M_success z) ==> a2 z)) ==>
   EvalM ro env st (Let (SOME name) e1 e2) (MONAD a c (st_ex_bind x f)) H`,
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "A1") (LABEL_TAC "A2")) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "a1") (LABEL_TAC "A4")) THEN
  REMOVE_THEN "A1" (fun th -> REMOVE_THEN "a1" (fun a -> LABEL_TAC "E1" (MP th a))) THEN
  REWRITE_TAC[EvalM_def] THEN X_GEN_TAC `s:(FFI)state` THEN DISCH_TAC THEN
  USE_THEN "E1" (fun e1 -> FIRST_ASSUM(fun rp ->
    MP_TAC(MATCH_MP MON1AUX_EvalM_MONAD_run (CONJ e1 rp)))) THEN
  DISCH_THEN(X_CHOOSE_THEN `s2:(FFI)state` (X_CHOOSE_THEN `res1:(v list,v)result`
    (X_CHOOSE_THEN `st2:REFS` (CONJUNCTS_THEN2
      (STRIP_ASSUME_TAC o REWRITE_RULE[MON1AUX_MONAD_THM])
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "R1")))))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `res1:(v list,v)result`))
  THENL
   [(* success: run e2 from s2 *)
    SUBGOAL_THEN `REFS_PRED H (st2:REFS) (s2:(FFI)state)` ASSUME_TAC THENL
     [MON1AUX_FRAME_IMP_TAC; ALL_TAC] THEN
    REMOVE_THEN "A2" (MP_TAC o SPECL [`y:B`; `v:v`]) THEN ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL
     [REMOVE_THEN "A4" MATCH_MP_TAC THEN ASM_REWRITE_TAC[ml_CONTAINER_def]; ALL_TAC] THEN
    DISCH_THEN(fun e2 -> FIRST_ASSUM(fun rp ->
      MP_TAC(MATCH_MP MON1AUX_EvalM_MONAD_run (CONJ e2 rp)))) THEN
    DISCH_THEN(X_CHOOSE_THEN `s3:(FFI)state` (X_CHOOSE_THEN `res3:(v list,v)result`
      (X_CHOOSE_THEN `st3:REFS` (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `state_clock (s3:(FFI)state)`)))))) THEN
    REWRITE_TAC[s_with_same_clock] THEN
    DISCH_THEN(X_CHOOSE_TAC `ck2:num`) THEN
    REMOVE_THEN "R1" (X_CHOOSE_TAC `ck1:num` o SPEC `ck2:num`) THEN
    MAP_EVERY EXISTS_TAC [`s3:(FFI)state`; `res3:(v list,v)result`; `st3:REFS`;
      `ck1:num`] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP MON1AUX_evaluate_Let_Rval th]) THEN
    ASM_REWRITE_TAC[MON1AUX_nsOptBind_write] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `st_ex_bind (x:REFS->(B,C)exc#REFS) (f:B->REFS->(A,C)exc#REFS) st =
                    f y st2` (fun th -> REWRITE_TAC[MATCH_MP MON1AUX_MONAD_eq th]) THENL
       [ASM_REWRITE_TAC[st_ex_bind_def] THEN CAKE_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
      MON1AUX_FRAME_CHAIN_TAC];
    (* failure: the exception propagates *)
    REMOVE_THEN "R1" (X_CHOOSE_TAC `ck1:num` o SPEC `state_clock (s2:(FFI)state)`) THEN
    MAP_EVERY EXISTS_TAC [`s2:(FFI)state`; `Rerr (Rraise v):(v list,v)result`; `st2:REFS`;
      `ck1:num`] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP MON1AUX_evaluate_Let_Rerr
      (REWRITE_RULE[s_with_same_clock] th)]) THEN
    ASM_REWRITE_TAC[MON1AUX_MONAD_THM; st_ex_bind_def] THEN CAKE_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`e:C`; `v:v`] THEN ASM_REWRITE_TAC[]]);;

(* bind ignore *)

let EvalM_bind_ignore = prove
 (`EvalM ro env st e1 (MONAD b c (x:REFS->(B,C)exc#REFS))
     (H:(REFS->hprop)#((FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list))) /\
   EvalM ro env (SND (x st)) e2 (MONAD (a:A->v->bool) c (f:REFS->(A,C)exc#REFS)) H ==>
   EvalM ro env st (Let NONE e1 e2) (MONAD a c (st_ex_ignore_bind x f)) H`,
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "E1") (LABEL_TAC "A2")) THEN
  REWRITE_TAC[EvalM_def] THEN X_GEN_TAC `s:(FFI)state` THEN DISCH_TAC THEN
  USE_THEN "E1" (fun e1 -> FIRST_ASSUM(fun rp ->
    MP_TAC(MATCH_MP MON1AUX_EvalM_MONAD_run (CONJ e1 rp)))) THEN
  DISCH_THEN(X_CHOOSE_THEN `s2:(FFI)state` (X_CHOOSE_THEN `res1:(v list,v)result`
    (X_CHOOSE_THEN `st2:REFS` (CONJUNCTS_THEN2
      (STRIP_ASSUME_TAC o REWRITE_RULE[MON1AUX_MONAD_THM])
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "R1")))))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `res1:(v list,v)result`))
  THENL
   [SUBGOAL_THEN `REFS_PRED H (st2:REFS) (s2:(FFI)state)` ASSUME_TAC THENL
     [MON1AUX_FRAME_IMP_TAC; ALL_TAC] THEN
    REMOVE_THEN "A2" MP_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun e2 -> FIRST_ASSUM(fun rp ->
      MP_TAC(MATCH_MP MON1AUX_EvalM_MONAD_run (CONJ e2 rp)))) THEN
    DISCH_THEN(X_CHOOSE_THEN `s3:(FFI)state` (X_CHOOSE_THEN `res3:(v list,v)result`
      (X_CHOOSE_THEN `st3:REFS` (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `state_clock (s3:(FFI)state)`)))))) THEN
    REWRITE_TAC[s_with_same_clock] THEN
    DISCH_THEN(X_CHOOSE_TAC `ck2:num`) THEN
    REMOVE_THEN "R1" (X_CHOOSE_TAC `ck1:num` o SPEC `ck2:num`) THEN
    MAP_EVERY EXISTS_TAC [`s3:(FFI)state`; `res3:(v list,v)result`; `st3:REFS`;
      `ck1:num`] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP MON1AUX_evaluate_Let_Rval th]) THEN
    ASM_REWRITE_TAC[MON1AUX_nsOptBind_NONE] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `st_ex_ignore_bind (x:REFS->(B,C)exc#REFS) (f:REFS->(A,C)exc#REFS) st =
                    f st2` (fun th -> REWRITE_TAC[MATCH_MP MON1AUX_MONAD_eq th]) THENL
       [ASM_REWRITE_TAC[st_ex_ignore_bind_def] THEN CAKE_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
      MON1AUX_FRAME_CHAIN_TAC];
    REMOVE_THEN "R1" (X_CHOOSE_TAC `ck1:num` o SPEC `state_clock (s2:(FFI)state)`) THEN
    MAP_EVERY EXISTS_TAC [`s2:(FFI)state`; `Rerr (Rraise v):(v list,v)result`; `st2:REFS`;
      `ck1:num`] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP MON1AUX_evaluate_Let_Rerr
      (REWRITE_RULE[s_with_same_clock] th)]) THEN
    ASM_REWRITE_TAC[MON1AUX_MONAD_THM; st_ex_ignore_bind_def] THEN CAKE_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`e:C`; `v:v`] THEN ASM_REWRITE_TAC[]]);;

let EvalM_pure_seq = prove
 (`ml_Eval env e1 ((c:D->v->bool) y) /\
   EvalM ro env st e2 (MONAD (a:A->v->bool) (b:B->v->bool) (x:REFS->(A,B)exc#REFS))
     (H:(REFS->hprop)#((FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list))) ==>
   EvalM ro env st (Let NONE e1 e2) (MONAD a b (pure_seq y x)) H`,
  STRIP_TAC THEN
  SUBGOAL_THEN `pure_seq (y:D) (x:REFS->(A,B)exc#REFS) =
                st_ex_ignore_bind (st_ex_return y) x` SUBST1_TAC THENL
   [REWRITE_TAC[pure_seq_def; st_ex_ignore_bind_def; st_ex_return_def; FUN_EQ_THM] THEN
    CAKE_REWRITE_TAC[];
    MATCH_MP_TAC(GEN_ALL EvalM_bind_ignore) THEN
    EXISTS_TAC `c:D->v->bool` THEN CONJ_TAC THENL
     [MATCH_MP_TAC EvalM_return THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[st_ex_return_def]]]);;

(* lift ro refinement invariants: HOL4 Type H = :'a -> 'refs -> 'refs #     *)
(* (v list,v) result -> bool (names.tsv H), written out                       *)

let PURE_def = cake_def
  `PURE (a:A->v->bool) (x:A) (st1:REFS) (st2,(res:(v list,v)result)) <=>
     ?v:v. res = Rval [v] /\ st1 = st2 /\ a x v`;;

let EqSt_def = cake_def
  `EqSt (ab:A->REFS->REFS#(v list,v)result->bool) (st:REFS) =
     \x st1 (st2,res). st = st1 /\ ab x st1 (st2,res)`;;

let state_update_clock_id = prove
 (`state_clock_fupd (combin_K (state_clock s)) (state_refs_fupd (combin_K refs') (s:(FFI)state)) =
   state_refs_fupd (combin_K refs') s`,
  REWRITE_TAC[state_component_equality] THEN SIMP[]);;
let _ = cake_add_simps [state_update_clock_id];;

let Eval_IMP_PURE = prove
 (`!(H:(REFS->hprop)#((FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)))
    env exp (P:A->v->bool) x.
     ml_Eval env exp (P x) ==> EvalM ro env st exp (PURE P x) H`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EvalM_def] THEN X_GEN_TAC `s:(FFI)state` THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `s:(FFI)state` o MATCH_MP MON1AUX_Eval_evaluate) THEN
  DISCH_THEN(X_CHOOSE_THEN `res:v` (X_CHOOSE_THEN `refs':(v store_v)list`
    (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `state_clock (s:(FFI)state)`)))) THEN
  DISCH_THEN(X_CHOOSE_TAC `ck1:num`) THEN
  MAP_EVERY EXISTS_TAC
   [`state_refs_fupd (combin_K (APPEND (state_refs s) refs')) (s:(FFI)state)`;
    `Rval [res]:(v list,v)result`; `st:REFS`; `ck1:num`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[state_update_clock_id]) THEN
  ASM_REWRITE_TAC[REFS_PRED_FRAME_append; PURE_def] THEN
  EXISTS_TAC `res:v` THEN ASM_REWRITE_TAC[]);;

let Eval_IMP_PURE_EvalM_T = prove
 (`!(H:(REFS->hprop)#((FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)))
    env exp (P:A->v->bool) x.
     ml_Eval env exp (P x) ==> EvalM T env st exp (PURE P x) H`,
  REWRITE_TAC[Eval_IMP_PURE]);;

(* function abstraction and application *)

let ArrowP_def = cake_def
  `ArrowP ro H (a:A->REFS->REFS#(v list,v)result->bool)
          (b:B->REFS->REFS#(v list,v)result->bool) (f:A->B) c <=>
     !x st1 (s1:(FFI)state) st2 (res:(v list,v)result).
       a x st1 (st2,res) /\ REFS_PRED H st1 s1 ==>
       ?v env exp.
         st2 = st1 /\ res = Rval [v] /\ do_opapp [c;v] = SOME (env,exp) /\
         !junk. ?st3 s3 res3 ck.
           evaluate (state_clock_fupd (combin_K ck)
                      (state_refs_fupd (combin_K (APPEND (state_refs s1) junk)) s1))
             env [exp] = (s3,res3) /\
           b (f x) st1 (st3,res3) /\
           REFS_PRED_FRAME ro H (st1,s1) (st3,s3)`;;

let ArrowM_def = cake_def
  `ArrowM ro
     (H:(REFS->hprop)#((FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)))
     (a:A->REFS->REFS#(v list,v)result->bool)
     (b:B->REFS->REFS#(v list,v)result->bool) =
   (PURE (ArrowP ro H a b):(A->B)->REFS->REFS#(v list,v)result->bool)`;;

let MON1AUX_EvalM_PURE_run = prove
 (`!ro env (st:REFS) exp (a:A->v->bool) x H (s:(FFI)state).
     EvalM ro env st exp (PURE a x) H /\ REFS_PRED H st s ==>
     ?s2 v.
       a x v /\ REFS_PRED_FRAME ro H (st,s) (st,s2) /\
       !ck. ?ck1. evaluate (state_clock_fupd (combin_K ck1) s) env [exp] =
                  (state_clock_fupd (combin_K ck) s2,Rval [v])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`ro:bool`; `env:v sem_env`; `st:REFS`; `exp:exp`;
    `PURE (a:A->v->bool) x:REFS->REFS#(v list,v)result->bool`; `H:(REFS->hprop)#((FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list))`;
    `s:(FFI)state`] MON1AUX_EvalM_run) THEN
  ASM_REWRITE_TAC[PURE_def] THEN ANTS_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[distinctness "result"]; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM; RIGHT_AND_EXISTS_THM; LEFT_AND_EXISTS_THM] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl))) THEN
  MAP_EVERY EXISTS_TAC [`s2:(FFI)state`; `v:v`] THEN ASM_REWRITE_TAC[]);;

let MON1AUX_evaluate_two = prove
 (`!(s:(FFI)state) env e1 e2 s1 v1 s2 v2.
     evaluate s env [e1] = (s1,Rval [v1]) /\ evaluate s1 env [e2] = (s2,Rval [v2]) ==>
     evaluate s env [e1; e2] = (s2,Rval [v1; v2])`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [evaluate_cons] THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  CAKE_REWRITE_TAC[] THEN REWRITE_TAC[APPEND]);;

let MON1AUX_evaluate_Opapp = prove
 (`!(s:(FFI)state) env x1 x2 s2 v2 s3 v1 env' e.
     evaluate s env [x2] = (s2,Rval [v2]) /\ evaluate s2 env [x1] = (s3,Rval [v1]) /\
     do_opapp [v1;v2] = SOME (env',e) /\ ~(state_clock s3 = 0) ==>
     evaluate s env [App Opapp [x1;x2]] = evaluate (dec_clock s3) env' [e]`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [evaluate_def] THEN
  REWRITE_TAC[REVERSE; APPEND] THEN
  FIRST_ASSUM(fun th1 -> FIRST_ASSUM(fun th2 ->
    REWRITE_TAC[MATCH_MP MON1AUX_evaluate_two (CONJ th1 th2)])) THEN
  REWRITE_TAC[getOpClass_def] THEN CAKE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[REVERSE; APPEND] THEN CAKE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[]);;

let MON1AUX_dec_clock = prove
 (`!(s:(FFI)state) ck. dec_clock (state_clock_fupd (combin_K (ck + 1)) s) = state_clock_fupd (combin_K ck) s`,
  REWRITE_TAC[dec_clock_def] THEN SIMP[ADD_SUB]);;

(* HOL4's EvalM_Arrow_tac, as one lemma for the four ArrowM application     *)
(* rules: the argument refinement A must accept the value of the argument.  *)

let MON1AUX_EvalM_ArrowM_gen = prove
 (`!ro env (st:REFS) x1 x2 (A:A->REFS->REFS#(v list,v)result->bool)
    (b:B->REFS->REFS#(v list,v)result->bool) (f:A->B) (a:A->v->bool) x
    (H:(REFS->hprop)#((FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list))).
     EvalM ro env st x1 (ArrowM ro H A b f) H ==>
     EvalM ro env st x2 (PURE a x) H ==>
     (!v. a x v ==> A x st (st,Rval [v])) ==>
     EvalM ro env st (App Opapp [x1;x2]) (b (f x)) H`,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "E1") THEN DISCH_THEN(LABEL_TAC "E2") THEN
  DISCH_THEN(LABEL_TAC "AX") THEN
  REWRITE_TAC[EvalM_def] THEN X_GEN_TAC `s:(FFI)state` THEN DISCH_TAC THEN
  USE_THEN "E2" (fun e2 -> FIRST_ASSUM(fun rp ->
    MP_TAC(MATCH_MP MON1AUX_EvalM_PURE_run (CONJ e2 rp)))) THEN
  DISCH_THEN(X_CHOOSE_THEN `s2:(FFI)state` (X_CHOOSE_THEN `v2:v`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "R2"))))) THEN
  SUBGOAL_THEN `REFS_PRED H (st:REFS) (s2:(FFI)state)` ASSUME_TAC THENL
   [MON1AUX_FRAME_IMP_TAC; ALL_TAC] THEN
  USE_THEN "E1" (fun e1 -> FIRST_ASSUM(fun rp ->
    MP_TAC(MATCH_MP MON1AUX_EvalM_PURE_run (CONJ (REWRITE_RULE[ArrowM_def] e1) rp)))) THEN
  DISCH_THEN(X_CHOOSE_THEN `s3:(FFI)state` (X_CHOOSE_THEN `v1:v`
    (CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "R1"))))) THEN
  SUBGOAL_THEN `REFS_PRED H (st:REFS) (s3:(FFI)state)` ASSUME_TAC THENL
   [MON1AUX_FRAME_IMP_TAC; ALL_TAC] THEN
  REWRITE_TAC[ArrowP_def] THEN
  DISCH_THEN(MP_TAC o SPECL [`x:A`; `st:REFS`; `s3:(FFI)state`; `st:REFS`;
    `Rval [v2]:(v list,v)result`]) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[injectivity "result"; CONS_11] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:v` (X_CHOOSE_THEN `env':v sem_env` (X_CHOOSE_THEN `e:exp`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (MP_TAC o SPEC `[]:(v store_v)list`)))))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `v2:v`)) THEN
  REWRITE_TAC[APPEND_NIL; with_same_refs] THEN
  DISCH_THEN(X_CHOOSE_THEN `st3:REFS` (X_CHOOSE_THEN `s4:(FFI)state`
    (X_CHOOSE_THEN `res4:(v list,v)result` (X_CHOOSE_THEN `ck:num` STRIP_ASSUME_TAC)))) THEN
  REMOVE_THEN "R1" (X_CHOOSE_TAC `c1:num` o SPEC `ck + 1`) THEN
  REMOVE_THEN "R2" (X_CHOOSE_TAC `c0:num` o SPEC `c1:num`) THEN
  MAP_EVERY EXISTS_TAC [`s4:(FFI)state`; `res4:(v list,v)result`; `st3:REFS`; `c0:num`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`state_clock_fupd (combin_K c0) (s:(FFI)state)`; `env:v sem_env`; `x1:exp`;
      `x2:exp`; `state_clock_fupd (combin_K c1) (s2:(FFI)state)`; `v:v`;
      `state_clock_fupd (combin_K (ck + 1)) (s3:(FFI)state)`; `v1:v`; `env':v sem_env`; `e:exp`]
      MON1AUX_evaluate_Opapp) THEN
    ASM_REWRITE_TAC[MON1AUX_dec_clock] THEN SIMP[ADD_EQ_0; ARITH_EQ];
    MON1AUX_FRAME_CHAIN_TAC]);;

let MON1AUX_ArrowM_TAC : tactic =
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(fun e2 -> FIRST_X_ASSUM(fun e1 ->
    MATCH_MP_TAC (MATCH_MP (MATCH_MP MON1AUX_EvalM_ArrowM_gen e1) e2))) THEN
  SIMP[EqSt_def; PURE_def; ml_Eq_def] THEN MESON_TAC[];;

let EvalM_ArrowM = prove
 (`EvalM ro env st x1 ((ArrowM ro H (PURE (a:A->v->bool)) (b:B->REFS->REFS#(v list,v)result->bool)) f) H ==>
   EvalM ro env st x2 (PURE a x) H ==>
   EvalM ro env st (App Opapp [x1;x2]) (b (f x))
     (H:(REFS->hprop)#((FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)))`,
  MON1AUX_ArrowM_TAC);;

let EvalM_ArrowM_EqSt = prove
 (`EvalM ro env st x1 ((ArrowM ro H (EqSt (PURE (a:A->v->bool)) st) (b:B->REFS->REFS#(v list,v)result->bool)) f) H ==>
   EvalM ro env st x2 (PURE a x) H ==>
   EvalM ro env st (App Opapp [x1;x2]) (b (f x))
     (H:(REFS->hprop)#((FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)))`,
  MON1AUX_ArrowM_TAC);;

let EvalM_ArrowM_Eq = prove
 (`EvalM ro env st x1 ((ArrowM ro H (PURE (ml_Eq (a:A->v->bool) x)) (b:B->REFS->REFS#(v list,v)result->bool)) f) H ==>
   EvalM ro env st x2 (PURE a x) H ==>
   EvalM ro env st (App Opapp [x1;x2]) (b (f x))
     (H:(REFS->hprop)#((FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)))`,
  MON1AUX_ArrowM_TAC);;

let EvalM_ArrowM_EqSt_Eq = prove
 (`EvalM ro env st x1 ((ArrowM ro H (EqSt (PURE (ml_Eq (a:A->v->bool) x)) st) (b:B->REFS->REFS#(v list,v)result->bool)) f) H ==>
   EvalM ro env st x2 (PURE a x) H ==>
   EvalM ro env st (App Opapp [x1;x2]) (b (f x))
     (H:(REFS->hprop)#((FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)))`,
  MON1AUX_ArrowM_TAC);;

let MON1AUX_evaluate_Fun = prove
 (`!(s:(FFI)state) env name body.
     evaluate s env [Fun name body] = (s,Rval [Closure env name body])`,
  REWRITE_TAC[evaluate_def]);;

let MON1AUX_do_opapp_Closure = prove
 (`!env name body v.
     do_opapp [Closure env name body; v] = SOME (ml_write name v env,body)`,
  REWRITE_TAC[do_opapp_def; ml_write_def] THEN CAKE_REWRITE_TAC[]);;

(* EvalM of a closure, for an argument refinement A that fixes the state     *)
(* n_st and accepts values only                                               *)

let MON1AUX_EvalM_Fun_gen = prove
 (`!ro env (st:REFS) name body (A:A->REFS->REFS#(v list,v)result->bool)
    (b:B->REFS->REFS#(v list,v)result->bool) (f:A->B) n_st
    (H:(REFS->hprop)#((FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list))).
     (!x st1 st2 res. A x st1 (st2,res) ==>
        ?v. st1 = n_st /\ st2 = n_st /\ res = Rval [v] /\
            EvalM ro (ml_write name v env) n_st body (b (f x)) H) ==>
     EvalM ro env st (Fun name body) (ArrowM ro H A b f) H`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[EvalM_def; ArrowM_def; PURE_def] THEN
  X_GEN_TAC `s:(FFI)state` THEN DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC [`s:(FFI)state`; `Rval [Closure env name body]:(v list,v)result`;
    `st:REFS`; `state_clock (s:(FFI)state)`] THEN
  REWRITE_TAC[s_with_same_clock; MON1AUX_evaluate_Fun; REFS_PRED_FRAME_same] THEN
  EXISTS_TAC `Closure env name body` THEN REWRITE_TAC[ArrowP_def] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `st1:REFS`; `s1:(FFI)state`; `st2:REFS`;
    `res:(v list,v)result`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`x:A`; `st1:REFS`; `st2:REFS`;
    `res:(v list,v)result`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `v:v` STRIP_ASSUME_TAC) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl))) THEN
  MAP_EVERY EXISTS_TAC [`v:v`; `ml_write name v env`; `body:exp`] THEN
  REWRITE_TAC[MON1AUX_do_opapp_Closure] THEN X_GEN_TAC `junk:(v store_v)list` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
    `state_refs_fupd (combin_K (APPEND (state_refs s1) junk)) (s1:(FFI)state)` o
    REWRITE_RULE[EvalM_def]) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REFS_PRED_append]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s3:(FFI)state` (X_CHOOSE_THEN `res3:(v list,v)result`
    (X_CHOOSE_THEN `st3:REFS` (X_CHOOSE_THEN `ck:num` STRIP_ASSUME_TAC)))) THEN
  MAP_EVERY EXISTS_TAC [`st3:REFS`; `s3:(FFI)state`; `res3:(v list,v)result`;
    `ck:num`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(GEN_ALL REFS_PRED_FRAME_remove_junk) THEN
  EXISTS_TAC `junk:(v store_v)list` THEN ASM_REWRITE_TAC[]);;

let EvalM_Fun = prove
 (`(!v x. (a:A->v->bool) x v ==>
          EvalM ro (ml_write name v env) n_st body
            ((b:B->REFS->REFS#(v list,v)result->bool) ((f:A->B) x)) H) ==>
   EvalM ro env st (Fun name body) (ArrowM ro H (EqSt (PURE a) n_st) b f)
     (H:(REFS->hprop)#((FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)))`,
  DISCH_TAC THEN MATCH_MP_TAC MON1AUX_EvalM_Fun_gen THEN
  EXISTS_TAC `n_st:REFS` THEN SIMP[EqSt_def; PURE_def] THEN
  REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl))) THEN
  EXISTS_TAC `v:v` THEN ASM_SIMP_TAC[]);;

let EvalM_Fun_Var_intro = prove
 (`EvalM ro cl_env st (Fun n exp) (PURE (P:A->v->bool) f)
     (H:(REFS->hprop)#((FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list))) ==>
   !name. LOOKUP_VAR name env (Closure cl_env n exp) ==>
          EvalM ro env st (Var (Short name)) (PURE P f) H`,
  REWRITE_TAC[EvalM_def; PURE_def; LOOKUP_VAR_def; ml_lookup_var_def;
    MON1AUX_evaluate_Fun] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `s:(FFI)state`) THEN
  ASM_REWRITE_TAC[evaluate_def] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[]);;

let EvalM_Fun_Eq = prove
 (`(!v. (a:A->v->bool) x v ==>
        EvalM ro (ml_write name v env) n_st body
          ((b:B->REFS->REFS#(v list,v)result->bool) ((f:A->B) x)) H) ==>
   EvalM ro env st (Fun name body)
     ((ArrowM ro H (EqSt (PURE (ml_Eq a x)) n_st) b) f)
     (H:(REFS->hprop)#((FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)))`,
  DISCH_TAC THEN MATCH_MP_TAC MON1AUX_EvalM_Fun_gen THEN
  EXISTS_TAC `n_st:REFS` THEN SIMP[EqSt_def; PURE_def; ml_Eq_def] THEN
  REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl))) THEN
  EXISTS_TAC `v:v` THEN ASM_SIMP_TAC[]);;

(* More proofs *)

let MON1AUX_evaluate_Var_Short = prove
 (`!(s:(FFI)state) env n v.
     nsLookup (sem_env_v env) (Short n) = SOME v ==>
     evaluate s env [Var (Short n)] = (s,Rval [v])`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[evaluate_def] THEN CAKE_REWRITE_TAC[]);;

(* an expression that evaluates to a value without effects *)

let MON1AUX_EvalM_value = prove
 (`!ro env (st:REFS) e cl (P:REFS->REFS#(v list,v)result->bool)
    (H:(REFS->hprop)#((FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list))).
     (!s:(FFI)state. evaluate s env [e] = (s,Rval [cl])) /\ P st (st,Rval [cl]) ==>
     EvalM ro env st e P H`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EvalM_def] THEN X_GEN_TAC `s:(FFI)state` THEN
  DISCH_TAC THEN MAP_EVERY EXISTS_TAC [`s:(FFI)state`; `Rval [cl]:(v list,v)result`;
    `st:REFS`; `state_clock (s:(FFI)state)`] THEN
  ASM_REWRITE_TAC[s_with_same_clock; REFS_PRED_FRAME_same]);;

(* ArrowP from the evaluation of the body of the closure, as in EvalM_Fun's  *)
(* proof                                                                       *)

let MON1AUX_ArrowP_intro = prove
 (`!ro (H:(REFS->hprop)#((FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)))
    (A:A->REFS->REFS#(v list,v)result->bool) (b:B->REFS->REFS#(v list,v)result->bool)
    (f:A->B) cl.
     (!x st1 st2 res. A x st1 (st2,res) ==>
        ?v env' exp. st2 = st1 /\ res = Rval [v] /\ do_opapp [cl;v] = SOME (env',exp) /\
                     EvalM ro env' st1 exp (b (f x)) H) ==>
     ArrowP ro H A b f cl`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[ArrowP_def] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `st1:REFS`; `s1:(FFI)state`; `st2:REFS`;
    `res:(v list,v)result`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`x:A`; `st1:REFS`; `st2:REFS`;
    `res:(v list,v)result`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `v:v` (X_CHOOSE_THEN `env':v sem_env`
    (X_CHOOSE_THEN `exp:exp` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`v:v`; `env':v sem_env`; `exp:exp`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `junk:(v store_v)list` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
    `state_refs_fupd (combin_K (APPEND (state_refs s1) junk)) (s1:(FFI)state)` o
    REWRITE_RULE[EvalM_def]) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REFS_PRED_append]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s3:(FFI)state` (X_CHOOSE_THEN `res3:(v list,v)result`
    (X_CHOOSE_THEN `st3:REFS` (X_CHOOSE_THEN `ck:num` STRIP_ASSUME_TAC)))) THEN
  MAP_EVERY EXISTS_TAC [`st3:REFS`; `s3:(FFI)state`; `res3:(v list,v)result`;
    `ck:num`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(GEN_ALL REFS_PRED_FRAME_remove_junk) THEN
  EXISTS_TAC `junk:(v store_v)list` THEN ASM_REWRITE_TAC[]);;

(* the value of a variable implements f in every state iff ArrowP holds      *)

let MON1AUX_head_is name tm =
  try fst(dest_const(fst(strip_comb tm))) = name with Failure _ -> false;;

let MON1AUX_EvalM_Var_ArrowM = prove
 (`!ro env n v (H:(REFS->hprop)#((FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)))
    (A:A->REFS->REFS#(v list,v)result->bool) (b:B->REFS->REFS#(v list,v)result->bool)
    (f:A->B).
     LOOKUP_VAR n env v ==>
     ((!st. EvalM ro env st (Var (Short n)) (ArrowM ro H A b f) H) <=>
      ArrowP ro H A b f v)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LOOKUP_VAR_def; ml_lookup_var_def] THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o GEN `s:(FFI)state` o MATCH_MP MON1AUX_evaluate_Var_Short) THEN
  EQ_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `!st1 (s1:(FFI)state). REFS_PRED H st1 s1 ==>
                  ArrowP ro H (A:A->REFS->REFS#(v list,v)result->bool)
                    (b:B->REFS->REFS#(v list,v)result->bool) (f:A->B) v`
    MP_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `st1:REFS`) THEN
      REWRITE_TAC[EvalM_def; ArrowM_def; PURE_def] THEN
      DISCH_THEN(MP_TAC o SPEC `s1:(FFI)state`) THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
      STRIP_TAC THEN GVS[];
      DISCH_TAC THEN GEN_REWRITE_TAC I [ArrowP_def] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `REFS_PRED H (st1:REFS) (s1:(FFI)state)`)) THEN
      REWRITE_TAC[ArrowP_def] THEN
      DISCH_THEN(MP_TAC o SPECL [`x:A`; `st1:REFS`; `s1:(FFI)state`; `st2:REFS`;
        `res:(v list,v)result`]) THEN ASM_REWRITE_TAC[]];
    DISCH_TAC THEN X_GEN_TAC `st:REFS` THEN MATCH_MP_TAC MON1AUX_EvalM_value THEN
    EXISTS_TAC `v:v` THEN ASM_REWRITE_TAC[ArrowM_def; PURE_def] THEN
    EXISTS_TAC `v:v` THEN ASM_REWRITE_TAC[]]);;

let LOOKUP_VAR_EvalM_ArrowM_IMP = prove
 (`(!st env. LOOKUP_VAR n env v ==>
             EvalM ro env st (Var (Short n)) (ArrowM ro H a b f) H) ==>
   ArrowP ro (H:(REFS->hprop)#((FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)))
     (a:A->REFS->REFS#(v list,v)result->bool) (b:B->REFS->REFS#(v list,v)result->bool)
     (f:A->B) v`,
  DISCH_THEN(MP_TAC o SPEC `sem_env_REC (nsBind (n:mlstring) (v:v) nsEmpty) nsEmpty` o
    GEN_REWRITE_RULE I [SWAP_FORALL_THM]) THEN
  SUBGOAL_THEN `LOOKUP_VAR n (sem_env_REC (nsBind (n:mlstring) (v:v) nsEmpty) nsEmpty) v` ASSUME_TAC THENL
   [SIMP[LOOKUP_VAR_def; ml_lookup_var_def; nsLookup_nsBind]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[MON1AUX_EvalM_Var_ArrowM]);;

let MON1AUX_evaluate_Var_write = prove
 (`!(s:(FFI)state) n x env y.
     ~(n = y) ==>
     evaluate s (ml_write n x env) [Var (Short y)] = evaluate s env [Var (Short y)]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[evaluate_def; ml_write_def] THEN SIMP[] THEN
  SUBGOAL_THEN `~(Short y = Short n:(mlstring,mlstring)id)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[injectivity "id"]; ASM_SIMP_TAC[nsLookup_nsBind]]);;

let EvalM_Var_SIMP = prove
 (`EvalM ro (ml_write n x env) st (Var (Short y)) P
     (H:(REFS->hprop)#((FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list))) =
   if n = y then EvalM ro (ml_write n x env) st (Var (Short y)) P H
   else EvalM ro env st (Var (Short y)) P H`,
  COND_CASES_TAC THEN ASM_SIMP_TAC[EvalM_def; MON1AUX_evaluate_Var_write]);;

let EvalM_Var_SIMP_ArrowM = prove
 (`(!st. EvalM ro (ml_write nv v env) st (Var (Short n))
           (ArrowM ro H (a:A->REFS->REFS#(v list,v)result->bool)
              (b:B->REFS->REFS#(v list,v)result->bool) (x:A->B)) H) =
   if nv = n then ArrowP ro H a b x v
   else (!st. EvalM ro env st (Var (Short n)) (ArrowM ro H a b x)
                (H:(REFS->hprop)#((FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list))))`,
  COND_CASES_TAC THENL
   [MATCH_MP_TAC MON1AUX_EvalM_Var_ArrowM THEN ASM_REWRITE_TAC[LOOKUP_VAR_SIMP];
    ONCE_REWRITE_TAC[EvalM_Var_SIMP] THEN ASM_REWRITE_TAC[]]);;

let MON1AUX_do_opapp_Recclosure = prove
 (CASE_TERM `!env2 funs fname name body v.
     ALL_DISTINCT (MAP (\fxe. match fxe with (f,x,e) -> f) funs) /\
     find_recfun fname funs = SOME (name,body) ==>
     do_opapp [Recclosure env2 funs fname; v] =
     SOME (ml_write name v (ml_write_rec funs env2 env2),body)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[do_opapp_def] THEN CAKE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[write_rec_thm; ml_write_def] THEN SIMP[]);;

let MON1AUX_RECCLOSURE_TAC : tactic =
  REPEAT(GEN_TAC ORELSE DISCH_TAC) THEN
  FIRST_ASSUM(fun lv -> SPEC_TAC(`st:REFS`,`st:REFS`) THEN
    REWRITE_TAC[MATCH_MP MON1AUX_EvalM_Var_ArrowM lv]) THEN
  MATCH_MP_TAC MON1AUX_ArrowP_intro THEN
  SIMP[EqSt_def; PURE_def; ml_Eq_def] THEN REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl))) THEN
  FIRST_ASSUM(fun th -> FIRST_ASSUM(fun th' ->
    MP_TAC(MATCH_MP MON1AUX_do_opapp_Recclosure (CONJ th th')))) THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[injectivity "result"; CONS_11; RIGHT_EXISTS_AND_THM;
    UNWIND_THM1; injectivity "option"; PAIR_EQ] THEN
  ASM_MESON_TAC[];;

let EvalM_Recclosure_ALT = prove
 (CASE_TERM `!(H:(REFS->hprop)#((FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)))
    funs fname name body.
     ALL_DISTINCT (MAP (\fxe. match fxe with (f,x,e) -> f) funs) ==>
     (!st v. (a:A->v->bool) n v ==>
        EvalM ro (ml_write name v (ml_write_rec funs env2 env2)) st body
          ((b:B->REFS->REFS#(v list,v)result->bool) ((f:A->B) n)) H) ==>
     LOOKUP_VAR fname env (Recclosure env2 funs fname) ==>
     find_recfun fname funs = SOME (name,body) ==>
     EvalM ro env st (Var (Short fname)) ((ArrowM ro H (PURE (ml_Eq a n)) b) f) H`,
  MON1AUX_RECCLOSURE_TAC);;

let EvalM_Recclosure_ALT2 = prove
 (CASE_TERM `!(H:(REFS->hprop)#((FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)))
    funs fname.
     A n_st ==>
     !name body.
     ALL_DISTINCT (MAP (\fxe. match fxe with (f,x,e) -> f) funs) ==>
     (!st v. A st ==> (a:A->v->bool) n v ==>
        EvalM ro (ml_write name v (ml_write_rec funs env2 env2)) st body
          ((b:B->REFS->REFS#(v list,v)result->bool) ((f:A->B) n)) H) ==>
     LOOKUP_VAR fname env (Recclosure env2 funs fname) ==>
     find_recfun fname funs = SOME (name,body) ==>
     EvalM ro env st (Var (Short fname))
       ((ArrowM ro H (EqSt (PURE (ml_Eq a n)) n_st) b) f) H`,
  MON1AUX_RECCLOSURE_TAC);;

let EvalM_Recclosure_ALT3 = prove
 (CASE_TERM `!(H:(REFS->hprop)#((FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)))
    funs fname name body.
     (!st v. A st ==> (a:A->v->bool) n v ==>
        EvalM ro (ml_write name v (ml_write_rec funs env2 env2)) st body
          ((b:B->REFS->REFS#(v list,v)result->bool) ((f:A->B) n)) H) ==>
     A n_st ==>
     ALL_DISTINCT (MAP (\fxe. match fxe with (f,x,e) -> f) funs) ==>
     LOOKUP_VAR fname env (Recclosure env2 funs fname) ==>
     find_recfun fname funs = SOME (name,body) ==>
     EvalM ro env st (Var (Short fname))
       ((ArrowM ro H (EqSt (PURE (ml_Eq a n)) n_st) b) f) H`,
  MON1AUX_RECCLOSURE_TAC);;

let EvalM_Recclosure = prove
 (`!(H:(REFS->hprop)#((FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list))).
     (!st v. (a:A->v->bool) n v ==>
        EvalM ro (ml_write name v (ml_write_rec [(fname,name,body)] env2 env2)) st body
          ((b:B->REFS->REFS#(v list,v)result->bool) ((f:A->B) n)) H) ==>
     LOOKUP_VAR fname env (Recclosure env2 [(fname,name,body)] fname) ==>
     EvalM ro env st (Var (Short fname)) ((ArrowM ro H (PURE (ml_Eq a n)) b) f) H`,
  GEN_TAC THEN
  SUBGOAL_THEN (CASE_TERM `ALL_DISTINCT (MAP (\fxe. match fxe with (f,x,e) -> f)
                 [(fname:mlstring,name:mlstring,body:exp)])`) ASSUME_TAC THENL
   [REWRITE_TAC[MAP; ALL_DISTINCT; MEM] THEN CAKE_REWRITE_TAC[] THEN REWRITE_TAC[MEM];
    ALL_TAC] THEN
  SUBGOAL_THEN `find_recfun fname [(fname:mlstring,name:mlstring,body:exp)] =
                SOME (name,body)` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[find_recfun_def] THEN CAKE_REWRITE_TAC[]; ALL_TAC] THEN
  MON1AUX_RECCLOSURE_TAC);;

let EvalM_Eq_Recclosure = prove
 (`LOOKUP_VAR name env (Recclosure x1 x2 x3) ==>
   (ArrowP ro H (a:A->REFS->REFS#(v list,v)result->bool)
      (b:B->REFS->REFS#(v list,v)result->bool) (f:A->B) (Recclosure x1 x2 x3) =
    (!st. EvalM ro env st (Var (Short name)) (ArrowM ro H a b f)
            (H:(REFS->hprop)#((FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)))))`,
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP MON1AUX_EvalM_Var_ArrowM th]));;

let EvalM_Var_ArrowP = prove
 (`(!st. EvalM ro env st (Var (Short n))
           (ArrowM ro H (PURE (a:A->v->bool)) (b:B->REFS->REFS#(v list,v)result->bool)
              (x:A->B)) H) ==>
   LOOKUP_VAR n env v ==>
   ArrowP ro (H:(REFS->hprop)#((FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)))
     (PURE a) b x v`,
  DISCH_TAC THEN DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC) THEN
    REWRITE_TAC[MATCH_MP MON1AUX_EvalM_Var_ArrowM th]));;

let EvalM_Var_ArrowP_EqSt = prove
 (`(!st. EvalM ro env st (Var (Short n))
           (ArrowM ro H (EqSt (PURE (a:A->v->bool)) n_st)
              (b:B->REFS->REFS#(v list,v)result->bool) (x:A->B)) H) ==>
   LOOKUP_VAR n env v ==>
   ArrowP ro (H:(REFS->hprop)#((FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)))
     (EqSt (PURE a) n_st) b x v`,
  DISCH_TAC THEN DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC) THEN
    REWRITE_TAC[MATCH_MP MON1AUX_EvalM_Var_ArrowM th]));;

(* Eq simps *)

(* two runs from one state with different clocks that do not time out give  *)
(* the same result (HOL4's proofs use evaluate_add_to_clock twice)            *)

let MON1AUX_evaluate_det = prove
 (`!(s:(FFI)state) env es c1 c2 s1 r1 s2 r2.
     evaluate (state_clock_fupd (combin_K c1) s) env es = (s1,r1) /\
     ~(r1 = Rerr (Rabort Rtimeout_error)) /\
     evaluate (state_clock_fupd (combin_K c2) s) env es = (s2,r2) /\
     ~(r2 = Rerr (Rabort Rtimeout_error)) ==>
     r1 = r2 /\ state_clock_fupd (combin_K 0) s1 = state_clock_fupd (combin_K 0) s2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`state_clock_fupd (combin_K c1) (s:(FFI)state)`; `env:v sem_env`; `es:exp list`;
    `s1:(FFI)state`; `r1:(v list,v)result`; `c2:num`] evaluate_add_to_clock) THEN
  MP_TAC(ISPECL [`state_clock_fupd (combin_K c2) (s:(FFI)state)`; `env:v sem_env`; `es:exp list`;
    `s2:(FFI)state`; `r2:(v list,v)result`; `c1:num`] evaluate_add_to_clock) THEN
  ASM_REWRITE_TAC[] THEN SIMP[] THEN
  SUBST1_TAC(ARITH_RULE `c2 + c1 = c1 + c2:num`) THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (ASSUME_TAC o SYM)) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o AP_TERM `state_clock_fupd (combin_K 0):(FFI)state->(FFI)state`) THEN
  SIMP[] THEN MESON_TAC[]);;

let MON1AUX_EvalM_mono = prove
 (`!ro env (st:REFS) exp (P:REFS->REFS#(v list,v)result->bool) Q
    (H:(REFS->hprop)#((FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list))).
     EvalM ro env st exp P H /\ (!st2 res. P st (st2,res) ==> Q st (st2,res)) ==>
     EvalM ro env st exp Q H`,
  REWRITE_TAC[EvalM_def] THEN MESON_TAC[]);;

let EvalM_FUN_FORALL = prove
 (`(!x. EvalM ro env st exp (PURE ((P:X->A->v->bool) x) f) H) ==>
   EvalM ro env st exp (PURE (FUN_FORALL x. P x) f)
     (H:(REFS->hprop)#((FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)))`,
  REWRITE_TAC[EvalM_def; PURE_def; FUN_FORALL] THEN DISCH_TAC THEN
  X_GEN_TAC `s:(FFI)state` THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th -> FIRST_ASSUM(MP_TAC o MATCH_MP (SPECL [`ARB:X`; `s:(FFI)state`] th))) THEN
  DISCH_THEN(X_CHOOSE_THEN `s2:(FFI)state` (X_CHOOSE_THEN `res:(v list,v)result`
    (X_CHOOSE_THEN `st2:REFS` (X_CHOOSE_THEN `ck:num` STRIP_ASSUME_TAC)))) THEN
  MAP_EVERY EXISTS_TAC [`s2:(FFI)state`; `res:(v list,v)result`; `st2:REFS`; `ck:num`] THEN
  ASM_REWRITE_TAC[] THEN EXISTS_TAC `v:v` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y:X` THEN
  FIRST_X_ASSUM(fun th -> FIRST_ASSUM(MP_TAC o MATCH_MP (SPECL [`y:X`; `s:(FFI)state`] th))) THEN
  DISCH_THEN(X_CHOOSE_THEN `s2':(FFI)state` (X_CHOOSE_THEN `res':(v list,v)result`
    (X_CHOOSE_THEN `st2':REFS` (X_CHOOSE_THEN `ck':num` STRIP_ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`s:(FFI)state`; `env:v sem_env`; `[exp:exp]`; `ck:num`; `ck':num`;
    `s2:(FFI)state`; `res:(v list,v)result`; `s2':(FFI)state`; `res':(v list,v)result`]
    MON1AUX_evaluate_det) THEN
  ASM_REWRITE_TAC[distinctness "result"; injectivity "result"; CONS_11] THEN
  ASM_MESON_TAC[]);;

let EvalM_FUN_FORALL_EQ = prove
 (`(!x. EvalM ro env st exp (PURE ((P:X->A->v->bool) x) f) H) =
   EvalM ro env st exp (PURE (FUN_FORALL x. P x) f)
     (H:(REFS->hprop)#((FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)))`,
  EQ_TAC THEN REWRITE_TAC[EvalM_FUN_FORALL] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MON1AUX_EvalM_mono THEN
  EXISTS_TAC `PURE (FUN_FORALL x. (P:X->A->v->bool) x) f:REFS->REFS#(v list,v)result->bool` THEN
  ASM_REWRITE_TAC[PURE_def; FUN_FORALL] THEN MESON_TAC[]);;

let MON1AUX_ArrowP_mono = prove
 (`!ro (H:(REFS->hprop)#((FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)))
    (a:A->REFS->REFS#(v list,v)result->bool) (b:B->REFS->REFS#(v list,v)result->bool)
    b' (f:A->B) c.
     ArrowP ro H a b f c /\ (!x st st2 res. b x st (st2,res) ==> b' x st (st2,res)) ==>
     ArrowP ro H a b' f c`,
  REWRITE_TAC[ArrowP_def] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> FIRST_ASSUM(MP_TAC o MATCH_MP th o CONJ
    (ASSUME `(a:A->REFS->REFS#(v list,v)result->bool) x st1 (st2,res)`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `v:v` (X_CHOOSE_THEN `env:v sem_env` (X_CHOOSE_THEN `exp:exp`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "J"))))))) THEN
  MAP_EVERY EXISTS_TAC [`v:v`; `env:v sem_env`; `exp:exp`] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `junk:(v store_v)list` THEN
  REMOVE_THEN "J" (X_CHOOSE_THEN `st3:REFS` (X_CHOOSE_THEN `s3:(FFI)state`
    (X_CHOOSE_THEN `res3:(v list,v)result` (X_CHOOSE_THEN `ck:num` STRIP_ASSUME_TAC))) o
    SPEC `junk:(v store_v)list`) THEN
  MAP_EVERY EXISTS_TAC [`st3:REFS`; `s3:(FFI)state`; `res3:(v list,v)result`; `ck:num`] THEN
  ASM_SIMP_TAC[]);;

let M_FUN_FORALL_PUSH1 = prove
 (`(FUN_FORALL x. ArrowP ro
     (H:(REFS->hprop)#((FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)))
     (a:A->REFS->REFS#(v list,v)result->bool) (PURE ((b:X->B->v->bool) x))) =
   (ArrowP ro H a (PURE (FUN_FORALL x. b x)))`,
  REWRITE_TAC[FUN_EQ_THM; FUN_FORALL] THEN
  MAP_EVERY X_GEN_TAC [`f:A->B`; `c:v`] THEN EQ_TAC THENL
   [DISCH_TAC THEN GEN_REWRITE_TAC I [ArrowP_def] THEN
    MAP_EVERY X_GEN_TAC [`x0:A`; `st1:REFS`; `s1:(FFI)state`; `st2:REFS`;
      `res:(v list,v)result`] THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPECL [`x0:A`; `st1:REFS`; `s1:(FFI)state`; `st2:REFS`;
      `res:(v list,v)result`] o REWRITE_RULE[ArrowP_def] o SPEC `ARB:X`) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:v` (X_CHOOSE_THEN `env:v sem_env` (X_CHOOSE_THEN `exp:exp`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "J"))))))) THEN
    MAP_EVERY EXISTS_TAC [`v:v`; `env:v sem_env`; `exp:exp`] THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `junk:(v store_v)list` THEN
    REMOVE_THEN "J" (X_CHOOSE_THEN `st3:REFS` (X_CHOOSE_THEN `s3:(FFI)state`
      (X_CHOOSE_THEN `res3:(v list,v)result` (X_CHOOSE_THEN `ck:num` STRIP_ASSUME_TAC))) o
      SPEC `junk:(v store_v)list`) THEN
    MAP_EVERY EXISTS_TAC [`st3:REFS`; `s3:(FFI)state`; `res3:(v list,v)result`; `ck:num`] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[PURE_def] o
      check (MON1AUX_head_is "PURE" o concl)) THEN
    REWRITE_TAC[PURE_def; FUN_FORALL] THEN EXISTS_TAC `v':v` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `y:X` THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x0:A`; `st1:REFS`; `s1:(FFI)state`; `st2:REFS`;
      `res:(v list,v)result`] o REWRITE_RULE[ArrowP_def] o SPEC `y:X`) THEN
    ASM_REWRITE_TAC[injectivity "result"; CONS_11; RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
    DISCH_THEN(X_CHOOSE_THEN `env':v sem_env` (X_CHOOSE_THEN `exp':exp`
      (CONJUNCTS_THEN2 MP_TAC (MP_TAC o SPEC `junk:(v store_v)list`)))) THEN
    ASM_REWRITE_TAC[injectivity "option"; PAIR_EQ] THEN
    DISCH_THEN(X_CHOOSE_THEN `st3':REFS` (X_CHOOSE_THEN `s3':(FFI)state`
      (X_CHOOSE_THEN `res3':(v list,v)result` (X_CHOOSE_THEN `ck':num`
        STRIP_ASSUME_TAC)))) THEN
    DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[PURE_def] o
      check (MON1AUX_head_is "PURE" o concl)) THEN
    MP_TAC(ISPECL [`state_refs_fupd (combin_K (APPEND (state_refs s1) junk)) (s1:(FFI)state)`;
      `env:v sem_env`; `[exp:exp]`; `ck:num`; `ck':num`; `s3:(FFI)state`;
      `res3:(v list,v)result`; `s3':(FFI)state`; `res3':(v list,v)result`]
      MON1AUX_evaluate_det) THEN
    ASM_REWRITE_TAC[distinctness "result"; injectivity "result"; CONS_11] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[];
    DISCH_TAC THEN X_GEN_TAC `y:X` THEN MATCH_MP_TAC MON1AUX_ArrowP_mono THEN
    EXISTS_TAC `PURE (FUN_FORALL x. (b:X->B->v->bool) x):B->REFS->REFS#(v list,v)result->bool` THEN
    ASM_REWRITE_TAC[PURE_def; FUN_FORALL] THEN MESON_TAC[]]);;

(* HOL4's M_FUN_FORALL_PUSH2, M_FUN_FORALL_PUSH3 and FUN_EXISTS_Eq are SML    *)
(* values of the script (MON1AUX_ here; FUN_EXISTS_Eq is ml_translator.ml's   *)
(* TR2AUX_FUN_EXISTS_Eq), exported only in M_FUN_QUANT_SIMP                   *)

let MON1AUX_M_FUN_FORALL_PUSH2 = prove
 (`!ro H (a:X->A->v->bool) (b:B->REFS->REFS#(v list,v)result->bool).
     (FUN_FORALL x. ArrowP ro H (PURE (a x)) b) =
     (ArrowP ro (H:(REFS->hprop)#((FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)))
        (PURE (FUN_EXISTS x. a x)) b)`,
  REWRITE_TAC[ArrowP_def; FUN_EQ_THM; FUN_FORALL; FUN_EXISTS; PURE_def] THEN
  MESON_TAC[]);;

let MON1AUX_M_FUN_FORALL_PUSH3 = prove
 (`!ro H (a:A->REFS->REFS#(v list,v)result->bool) (b:B->REFS->REFS#(v list,v)result->bool).
     (FUN_FORALL st. ArrowP ro H (EqSt a st) b) =
     (ArrowP ro (H:(REFS->hprop)#((FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)))
        a b)`,
  REWRITE_TAC[ArrowP_def; FUN_EQ_THM; FUN_FORALL; EqSt_def] THEN SIMP[] THEN
  MESON_TAC[]);;

let M_FUN_QUANT_SIMP = end_itlist CONJ
  [TR2AUX_FUN_EXISTS_Eq; M_FUN_FORALL_PUSH1; MON1AUX_M_FUN_FORALL_PUSH2;
   MON1AUX_M_FUN_FORALL_PUSH3];;

let EvalM_Eq = prove
 (`EvalM ro env st exp (PURE (a:A->v->bool) x) H ==>
   EvalM ro env st exp (PURE (ml_Eq a x) x)
     (H:(REFS->hprop)#((FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)))`,
  DISCH_TAC THEN MATCH_MP_TAC MON1AUX_EvalM_mono THEN
  EXISTS_TAC `PURE (a:A->v->bool) x:REFS->REFS#(v list,v)result->bool` THEN
  ASM_REWRITE_TAC[PURE_def; ml_Eq_def]);;

let ArrowP_EqSt_elim = prove
 (`(!st_v. ArrowP ro H (EqSt a st_v) b f v) ==>
   ArrowP ro (H:(REFS->hprop)#((FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)))
     (a:A->REFS->REFS#(v list,v)result->bool) (b:B->REFS->REFS#(v list,v)result->bool)
     (f:A->B) v`,
  REWRITE_TAC[EqSt_def; ArrowP_def] THEN SIMP[] THEN MESON_TAC[]);;

let ArrowM_EqSt_elim = prove
 (`(!st_v. EvalM ro env st exp (ArrowM ro H (EqSt a st_v) b f) H) ==>
   EvalM ro env st exp
     (ArrowM ro H (a:A->REFS->REFS#(v list,v)result->bool)
        (b:B->REFS->REFS#(v list,v)result->bool) (f:A->B))
     (H:(REFS->hprop)#((FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)))`,
  DISCH_TAC THEN REWRITE_TAC[EvalM_def; ArrowM_def; PURE_def] THEN
  X_GEN_TAC `s:(FFI)state` THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th -> FIRST_ASSUM(MP_TAC o MATCH_MP
    (REWRITE_RULE[EvalM_def; ArrowM_def; PURE_def] (SPEC `st:REFS` th)))) THEN
  DISCH_THEN(X_CHOOSE_THEN `s2:(FFI)state` (X_CHOOSE_THEN `res:(v list,v)result`
    (X_CHOOSE_THEN `st2:REFS` (X_CHOOSE_THEN `ck:num` STRIP_ASSUME_TAC)))) THEN
  MAP_EVERY EXISTS_TAC [`s2:(FFI)state`; `res:(v list,v)result`; `st2:REFS`; `ck:num`] THEN
  ASM_REWRITE_TAC[] THEN EXISTS_TAC `v:v` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC ArrowP_EqSt_elim THEN X_GEN_TAC `st_v:REFS` THEN
  FIRST_X_ASSUM(fun th -> FIRST_ASSUM(MP_TAC o MATCH_MP
    (REWRITE_RULE[EvalM_def; ArrowM_def; PURE_def] (SPEC `st_v:REFS` th)))) THEN
  DISCH_THEN(X_CHOOSE_THEN `s2':(FFI)state` (X_CHOOSE_THEN `res':(v list,v)result`
    (X_CHOOSE_THEN `st2':REFS` (X_CHOOSE_THEN `ck':num` STRIP_ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`s:(FFI)state`; `env:v sem_env`; `[exp:exp]`; `ck:num`; `ck':num`;
    `s2:(FFI)state`; `res:(v list,v)result`; `s2':(FFI)state`; `res':(v list,v)result`]
    MON1AUX_evaluate_det) THEN
  ASM_REWRITE_TAC[distinctness "result"; injectivity "result"; CONS_11] THEN
  DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[]);;

(* otherwise *)

let MON1AUX_nsAppend_sing = prove
 (`!(n:N) (v:V) (e:(M,N,V)namespace). nsAppend (alist_to_ns [(n,v)]) e = nsBind n v e`,
  REPEAT GEN_TAC THEN QCASES_ON "e" THEN
  REWRITE_TAC[nsAppend_def; alist_to_ns_def; nsBind_def; APPEND]);;

let MON1AUX_evaluate_Handle_Rval = prove
 (`!(s:(FFI)state) env e pes s1 vs.
     evaluate s env [e] = (s1,Rval vs) ==>
     evaluate s env [Handle e pes] = (s1,Rval vs)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[evaluate_def] THEN CAKE_REWRITE_TAC[]);;

let MON1AUX_evaluate_Handle_Rabort = prove
 (`!(s:(FFI)state) env e pes s1 a.
     evaluate s env [e] = (s1,Rerr (Rabort a)) ==>
     evaluate s env [Handle e pes] = (s1,Rerr (Rabort a))`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[evaluate_def] THEN CAKE_REWRITE_TAC[]);;

let MON1AUX_evaluate_Handle_Pvar = prove
 (`!(s:(FFI)state) env e1 n e2 s1 v.
     evaluate s env [e1] = (s1,Rerr (Rraise v)) ==>
     evaluate s env [Handle e1 [(Pvar n,e2)]] = evaluate s1 (ml_write n v env) [e2]`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[evaluate_def] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[MAP; FST; can_pmatch_all_def; pmatch_def; pat_bindings_def;
    ALL_DISTINCT; MEM; distinctness "match_result"] THEN
  CAKE_REWRITE_TAC[] THEN REWRITE_TAC[MON1AUX_nsAppend_sing; ml_write_def]);;

let EvalM_otherwise = prove
 (`!(H:(REFS->hprop)#((FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)))
    (b:B->v->bool) n.
     ((a1 ==> EvalM ro env st exp1 (MONAD (a:A->v->bool) b x1) H) /\
      (!st i. a2 st ==> EvalM ro (ml_write n i env) st exp2 (MONAD a b x2) H)) ==>
     (a1 /\ !st'. (ml_CONTAINER (SND (x1 st) = st') ==> a2 st')) ==>
     EvalM ro env st (Handle exp1 [(Pvar n,exp2)]) (MONAD a b (x1 otherwise x2)) H`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "A1") (LABEL_TAC "A2")) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "a1") (LABEL_TAC "A4")) THEN
  REMOVE_THEN "A1" (fun th -> REMOVE_THEN "a1" (fun a -> LABEL_TAC "E1" (MP th a))) THEN
  REWRITE_TAC[EvalM_def] THEN X_GEN_TAC `s:(FFI)state` THEN DISCH_TAC THEN
  USE_THEN "E1" (fun e1 -> FIRST_ASSUM(fun rp ->
    MP_TAC(MATCH_MP MON1AUX_EvalM_MONAD_run (CONJ e1 rp)))) THEN
  DISCH_THEN(X_CHOOSE_THEN `s2:(FFI)state` (X_CHOOSE_THEN `res1:(v list,v)result`
    (X_CHOOSE_THEN `st2:REFS` (CONJUNCTS_THEN2
      (STRIP_ASSUME_TAC o REWRITE_RULE[MON1AUX_MONAD_THM])
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "R1")))))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `res1:(v list,v)result`))
  THENL
   [(* success: the handler is not used *)
    REMOVE_THEN "R1" (X_CHOOSE_TAC `ck1:num` o SPEC `state_clock (s2:(FFI)state)`) THEN
    MAP_EVERY EXISTS_TAC [`s2:(FFI)state`; `Rval [v]:(v list,v)result`; `st2:REFS`;
      `ck1:num`] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP MON1AUX_evaluate_Handle_Rval
      (REWRITE_RULE[s_with_same_clock] th)]) THEN
    ASM_REWRITE_TAC[MON1AUX_MONAD_THM; otherwise_def] THEN CAKE_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`y:A`; `v:v`] THEN ASM_REWRITE_TAC[];
    (* failure: run the handler from s2 *)
    SUBGOAL_THEN `REFS_PRED H (st2:REFS) (s2:(FFI)state)` ASSUME_TAC THENL
     [MON1AUX_FRAME_IMP_TAC; ALL_TAC] THEN
    REMOVE_THEN "A2" (MP_TAC o SPECL [`st2:REFS`; `v:v`]) THEN
    ANTS_TAC THENL
     [REMOVE_THEN "A4" MATCH_MP_TAC THEN ASM_REWRITE_TAC[ml_CONTAINER_def]; ALL_TAC] THEN
    DISCH_THEN(fun e2 -> FIRST_ASSUM(fun rp ->
      MP_TAC(MATCH_MP MON1AUX_EvalM_MONAD_run (CONJ e2 rp)))) THEN
    DISCH_THEN(X_CHOOSE_THEN `s3:(FFI)state` (X_CHOOSE_THEN `res3:(v list,v)result`
      (X_CHOOSE_THEN `st3:REFS` (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `state_clock (s3:(FFI)state)`)))))) THEN
    REWRITE_TAC[s_with_same_clock] THEN
    DISCH_THEN(X_CHOOSE_TAC `ck2:num`) THEN
    REMOVE_THEN "R1" (X_CHOOSE_TAC `ck1:num` o SPEC `ck2:num`) THEN
    MAP_EVERY EXISTS_TAC [`s3:(FFI)state`; `res3:(v list,v)result`; `st3:REFS`;
      `ck1:num`] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP MON1AUX_evaluate_Handle_Pvar th]) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `((x1:REFS->(A,B)exc#REFS) otherwise (x2:REFS->(A,B)exc#REFS)) st =
                    x2 st2` (fun th -> REWRITE_TAC[MATCH_MP MON1AUX_MONAD_eq th]) THENL
       [ASM_REWRITE_TAC[otherwise_def] THEN CAKE_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
      MON1AUX_FRAME_CHAIN_TAC]]);;

(* if *)

let MON1AUX_evaluate_If = prove
 (`!(s:(FFI)state) env e1 e2 e3 s1 b.
     evaluate s env [e1] = (s1,Rval [Boolv b]) ==>
     evaluate s env [If e1 e2 e3] = evaluate s1 env [if b then e2 else e3]`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[evaluate_def] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[HD; do_if_def; semanticPrimitivesProps_Boolv_11] THEN
  BOOL_CASES_TAC `b:bool` THEN CAKE_REWRITE_TAC[]);;

(* a pure evaluation of e1 followed by an EvalM evaluation from the state it  *)
(* leaves (HOL4's proofs use Eval_IMP_PURE and REFS_PRED_append)              *)

let MON1AUX_Eval_then_EvalM = prove
 (`!ro env (st:REFS) e1 (P1:v->bool)
    (H:(REFS->hprop)#((FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)))
    (s:(FFI)state).
     ml_Eval env e1 P1 /\ REFS_PRED H st s ==>
     ?v refs'. P1 v /\
       (!ck. ?ck1. evaluate (state_clock_fupd (combin_K ck1) s) env [e1] =
                   (state_clock_fupd (combin_K ck) (state_refs_fupd (combin_K (APPEND (state_refs s) refs')) s),
                    Rval [v])) /\
       REFS_PRED H st (state_refs_fupd (combin_K (APPEND (state_refs s) refs')) s) /\
       REFS_PRED_FRAME ro H (st,s) (st,state_refs_fupd (combin_K (APPEND (state_refs s) refs')) s)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:(FFI)state` o MATCH_MP MON1AUX_Eval_evaluate) THEN
  DISCH_THEN(X_CHOOSE_THEN `v:v` (X_CHOOSE_THEN `refs':(v store_v)list`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`v:v`; `refs':(v store_v)list`] THEN
  ASM_SIMP_TAC[REFS_PRED_append; REFS_PRED_FRAME_append]);;

let EvalM_If = prove
 (`!(H:(REFS->hprop)#((FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list))).
     (a1 ==> ml_Eval env x1 (ml_BOOL b1)) /\
     (a2 ==> EvalM ro env st x2 ((a:C->REFS->REFS#(v list,v)result->bool) b2) H) /\
     (a3 ==> EvalM ro env st x3 (a b3) H) ==>
     (a1 /\ (ml_CONTAINER b1 ==> a2) /\ (~ml_CONTAINER b1 ==> a3) ==>
      EvalM ro env st (If x1 x2 x3) (a (if b1 then b2 else b3)) H)`,
  REWRITE_TAC[ml_CONTAINER_def] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[EvalM_def] THEN X_GEN_TAC `s:(FFI)state` THEN DISCH_TAC THEN
  SUBGOAL_THEN `ml_Eval env x1 (ml_BOOL b1)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`ro:bool`; `env:v sem_env`; `st:REFS`; `x1:exp`; `ml_BOOL b1`;
    `H:(REFS->hprop)#((FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list))`;
    `s:(FFI)state`] MON1AUX_Eval_then_EvalM) THEN
  ASM_REWRITE_TAC[ml_BOOL_def] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:v` (X_CHOOSE_THEN `refs':(v store_v)list`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "R1")
      (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `v:v`)) THEN
  SUBGOAL_THEN `EvalM ro env st (if b1 then x2 else x3)
                  ((a:C->REFS->REFS#(v list,v)result->bool) (if b1 then b2 else b3))
                  (H:(REFS->hprop)#((FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)))`
    MP_TAC THENL
   [ASM_CASES_TAC `b1:bool` THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[EvalM_def] THEN
  DISCH_THEN(fun th -> FIRST_ASSUM(MP_TAC o MATCH_MP th)) THEN
  DISCH_THEN(X_CHOOSE_THEN `s3:(FFI)state` (X_CHOOSE_THEN `res3:(v list,v)result`
    (X_CHOOSE_THEN `st3:REFS` (X_CHOOSE_THEN `ck:num` STRIP_ASSUME_TAC)))) THEN
  REMOVE_THEN "R1" (X_CHOOSE_TAC `ck1:num` o SPEC `ck:num`) THEN
  MAP_EVERY EXISTS_TAC [`s3:(FFI)state`; `res3:(v list,v)result`; `st3:REFS`;
    `ck1:num`] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP MON1AUX_evaluate_If th]) THEN
  ASM_REWRITE_TAC[] THEN MON1AUX_FRAME_CHAIN_TAC);;

(* Let *)

let EvalM_Let = prove
 (`!(H:(REFS->hprop)#((FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list))).
     ml_Eval env exp ((a:A->v->bool) res) /\
     (!v. a res v ==> EvalM ro (ml_write name v env) st body
                       ((b:B->REFS->REFS#(v list,v)result->bool) ((f:A->B) res)) H) ==>
     EvalM ro env st (Let (SOME name) exp body) (b (LET f res)) H`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EvalM_def; LET_DEF] THEN
  X_GEN_TAC `s:(FFI)state` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`ro:bool`; `env:v sem_env`; `st:REFS`; `exp:exp`; `(a:A->v->bool) res`;
    `H:(REFS->hprop)#((FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list))`;
    `s:(FFI)state`] MON1AUX_Eval_then_EvalM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:v` (X_CHOOSE_THEN `refs':(v store_v)list`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "R1")
      (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))))) THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[EvalM_def] o C MATCH_MP
    (ASSUME `(a:A->v->bool) res v`)) THEN
  DISCH_THEN(fun th -> FIRST_ASSUM(MP_TAC o MATCH_MP th)) THEN
  DISCH_THEN(X_CHOOSE_THEN `s3:(FFI)state` (X_CHOOSE_THEN `res3:(v list,v)result`
    (X_CHOOSE_THEN `st3:REFS` (X_CHOOSE_THEN `ck:num` STRIP_ASSUME_TAC)))) THEN
  REMOVE_THEN "R1" (X_CHOOSE_TAC `ck1:num` o SPEC `ck:num`) THEN
  MAP_EVERY EXISTS_TAC [`s3:(FFI)state`; `res3:(v list,v)result`; `st3:REFS`;
    `ck1:num`] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP MON1AUX_evaluate_Let_Rval th]) THEN
  ASM_REWRITE_TAC[MON1AUX_nsOptBind_write] THEN MON1AUX_FRAME_CHAIN_TAC);;

(* Exception handling *)

let ml_monad_translator_write_list_def = cake_def
  `(ml_monad_translator_write_list [] [] (env:v sem_env) = env) /\
   (ml_monad_translator_write_list (CONS n nl) (CONS (v:v) vl) env =
      ml_monad_translator_write_list nl vl (ml_write n v env))`;;

let pats_bindings_MAP_Pvar = prove
 (`!bind_names. pats_bindings (MAP (\x. Pvar x) bind_names) = REVERSE bind_names`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; REVERSE; pat_bindings_def]);;

let ALL_DISTINCT_pats_bindings = prove
 (`!bind_names. ALL_DISTINCT bind_names ==>
                ALL_DISTINCT (pats_bindings (MAP (\x. Pvar x) bind_names))`,
  REWRITE_TAC[pats_bindings_MAP_Pvar; ALL_DISTINCT_REVERSE]);;

let ml_monad_translator_pmatch_list_MAP_Pvar = prove
 (`!bind_names paramsv env already_bound s.
     LENGTH paramsv = LENGTH bind_names ==>
     pmatch_list env s (MAP (\x. Pvar x) bind_names) paramsv already_bound =
     Match (APPEND (REVERSE (ZIP bind_names paramsv)) already_bound)`,
  REWRITE_TAC[ETA_AX] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(GEN_ALL ml_pmatch_list_MAP_Pvar) THEN ASM_REWRITE_TAC[]);;

let nsAppend_append = prove
 (`!a b (env:(M,N,V)namespace).
     nsAppend (Bind (APPEND a b) []) env = nsAppend (Bind a []) (nsAppend (Bind b []) env)`,
  REPEAT GEN_TAC THEN QCASES_ON "env" THEN
  REWRITE_TAC[nsAppend_def; APPEND_ASSOC; APPEND_NIL; APPEND]);;

let write_list_eq = prove
 (`!bind_names paramsv l1 l2 cenv.
     LENGTH paramsv = LENGTH bind_names ==>
     ml_monad_translator_write_list bind_names paramsv (sem_env_REC (Bind l1 l2) cenv) =
     sem_env_REC (Bind (APPEND (REVERSE (ZIP bind_names paramsv)) l1) l2) cenv`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ; ml_monad_translator_write_list_def; ZIP;
    REVERSE; APPEND] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[ml_write_def] THEN SIMP[nsBind_def] THEN
  ASM_SIMP_TAC[] THEN REWRITE_TAC[GSYM APPEND_ASSOC; APPEND]);;

let nsAppend_write_list_eq = prove
 (`!bind_names paramsv (env:v sem_env).
     LENGTH paramsv = LENGTH bind_names ==>
     sem_env_v_fupd
       (combin_K (nsAppend (alist_to_ns (REVERSE (ZIP bind_names paramsv))) (sem_env_v env))) env =
     ml_monad_translator_write_list bind_names paramsv env`,
  REPEAT STRIP_TAC THEN QCASES_ON "env" THEN
  RENAME_TAC ["sem_env_REC vv cc"] THEN QCASES_ON "vv" THEN
  ASM_SIMP_TAC[write_list_eq] THEN SIMP[nsAppend_def; alist_to_ns_def]);;

let MON1AUX_pmatch_Pcon_exn = prove
 (`!envC (refs:(v store_v)list) cons_name bind_names stamp stamp' paramsv arity.
     nsLookup envC cons_name = SOME (arity,ExnStamp stamp) /\
     LENGTH bind_names = arity /\ LENGTH paramsv = arity ==>
     pmatch envC refs (Pcon (SOME cons_name) (MAP (\x. Pvar x) bind_names))
       (Conv (SOME (ExnStamp stamp')) paramsv) [] =
     if stamp' = stamp then Match (REVERSE (ZIP bind_names paramsv)) else No_match`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[pmatch_def] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[same_type_def; same_ctor_def; LENGTH_MAP; injectivity "stamp"] THEN
  ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[ml_monad_translator_pmatch_list_MAP_Pvar; APPEND_NIL] THEN
  ASM_MESON_TAC[]);;

let MON1AUX_evaluate_Handle_Pcon = prove
 (`!(s:(FFI)state) env e1 cons_name bind_names e2 s1 stamp stamp' paramsv arity.
     evaluate s env [e1] = (s1,Rerr (Rraise (Conv (SOME (ExnStamp stamp')) paramsv))) /\
     ml_lookup_cons cons_name env = SOME (arity,ExnStamp stamp) /\
     LENGTH bind_names = arity /\ LENGTH paramsv = arity /\ ALL_DISTINCT bind_names ==>
     evaluate s env [Handle e1 [(Pcon (SOME cons_name) (MAP (\x. Pvar x) bind_names),e2)]] =
     if stamp' = stamp
     then evaluate s1 (ml_monad_translator_write_list bind_names paramsv env) [e2]
     else (s1,Rerr (Rraise (Conv (SOME (ExnStamp stamp')) paramsv)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ml_lookup_cons_def] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[evaluate_def] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[MAP; FST; can_pmatch_all_def; pat_bindings_def] THEN
  ASM_SIMP_TAC[MON1AUX_pmatch_Pcon_exn; ALL_DISTINCT_pats_bindings] THEN
  ASM_CASES_TAC `stamp':num = stamp` THEN
  ASM_REWRITE_TAC[distinctness "match_result"] THEN CAKE_REWRITE_TAC[] THEN
  SUBGOAL_THEN `LENGTH (paramsv:v list) = LENGTH (bind_names:mlstring list)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ASM_SIMP_TAC[nsAppend_write_list_eq]]);;

let MON1AUX_evaluate_Handle_Pcon_nomatch = prove
 (`!(s:(FFI)state) env e1 cons_name bind_names e2 s1 stamp stamp' paramsv arity.
     evaluate s env [e1] = (s1,Rerr (Rraise (Conv (SOME (ExnStamp stamp')) paramsv))) /\
     ml_lookup_cons cons_name env = SOME (arity,ExnStamp stamp) /\
     LENGTH bind_names = arity /\ ~(stamp' = stamp) /\ ALL_DISTINCT bind_names ==>
     evaluate s env [Handle e1 [(Pcon (SOME cons_name) (MAP (\x. Pvar x) bind_names),e2)]] =
     (s1,Rerr (Rraise (Conv (SOME (ExnStamp stamp')) paramsv)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ml_lookup_cons_def] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[evaluate_def] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[MAP; FST; can_pmatch_all_def; pat_bindings_def] THEN
  ASM_SIMP_TAC[pmatch_def; ALL_DISTINCT_pats_bindings] THEN CAKE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[same_type_def; same_ctor_def; LENGTH_MAP; injectivity "stamp";
    distinctness "match_result"] THEN
  CAKE_REWRITE_TAC[] THEN REWRITE_TAC[evaluate_def]);;

let EvalM_handle = prove
 (`!cons_name stamp (CORRECT_CONS:E->bool) (PARAMS_CONDITIONS:E->v list->bool)
    (EXN_TYPE:E->v->bool) (handle_fun:(REFS->(A,E)exc#REFS)->(E->REFS->(A,E)exc#REFS)->
                                       REFS->(A,E)exc#REFS)
    x1 x2 arity (a2:REFS->E->bool) bind_names (a:A->v->bool)
    (H:(REFS->hprop)#((FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list))).
     (!s E s1. CORRECT_CONS E ==> x1 s = (M_failure E,s1) ==>
               handle_fun x1 x2 s = x2 E s1) ==>
     (!s. (!E s1. CORRECT_CONS E ==> ~(x1 s = (M_failure E,s1))) ==>
          handle_fun x1 x2 s = x1 s) ==>
     (!E ev. EXN_TYPE E ev ==> CORRECT_CONS E ==>
        ?paramsv. ev = Conv (SOME (ExnStamp stamp)) paramsv /\
                  PARAMS_CONDITIONS E paramsv /\ LENGTH paramsv = arity) ==>
     (!E ev. EXN_TYPE E ev ==> ~CORRECT_CONS E ==>
        ?paramsv stamp_1. ev = Conv (SOME (ExnStamp stamp_1)) paramsv /\
                          ~(stamp_1 = stamp)) ==>
     ALL_DISTINCT bind_names ==>
     LENGTH bind_names = arity ==>
     ml_lookup_cons cons_name env = SOME (arity,ExnStamp stamp) ==>
     ((a1 ==> EvalM ro env st exp1 (MONAD a EXN_TYPE x1) H) /\
      (!st E paramsv.
         PARAMS_CONDITIONS E paramsv ==> a2 st E ==>
         EvalM ro (ml_monad_translator_write_list bind_names paramsv env) st exp2
           (MONAD a EXN_TYPE (x2 E)) H)) ==>
     (!st' E. a1 /\
        (ml_CONTAINER (x1 st = (M_failure E,st') /\ CORRECT_CONS E) ==> a2 st' E)) ==>
     EvalM ro env st
       (Handle exp1 [(Pcon (SOME cons_name) (MAP (\x. Pvar x) bind_names),exp2)])
       (MONAD a EXN_TYPE (handle_fun x1 x2)) H`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(LABEL_TAC "HF1") THEN DISCH_THEN(LABEL_TAC "HF2") THEN
  DISCH_THEN(LABEL_TAC "EX1") THEN DISCH_THEN(LABEL_TAC "EX2") THEN
  DISCH_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "A1") (LABEL_TAC "A2")) THEN
  DISCH_THEN(LABEL_TAC "A4") THEN
  SUBGOAL_THEN `a1:bool` ASSUME_TAC THENL
   [USE_THEN "A4" (MP_TAC o SPECL [`ARB:REFS`; `ARB:E`]) THEN SIMP_TAC[]; ALL_TAC] THEN
  REMOVE_THEN "A1" (fun th -> FIRST_ASSUM(fun a -> LABEL_TAC "E1" (MP th a))) THEN
  REWRITE_TAC[EvalM_def] THEN X_GEN_TAC `s:(FFI)state` THEN DISCH_TAC THEN
  USE_THEN "E1" (fun e1 -> FIRST_ASSUM(fun rp ->
    MP_TAC(MATCH_MP MON1AUX_EvalM_MONAD_run (CONJ e1 rp)))) THEN
  DISCH_THEN(X_CHOOSE_THEN `s2:(FFI)state` (X_CHOOSE_THEN `res1:(v list,v)result`
    (X_CHOOSE_THEN `st2:REFS` (CONJUNCTS_THEN2
      (STRIP_ASSUME_TAC o REWRITE_RULE[MON1AUX_MONAD_THM])
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "R1")))))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `res1:(v list,v)result`))
  THENL
   [(* success *)
    REMOVE_THEN "R1" (X_CHOOSE_TAC `ck1:num` o SPEC `state_clock (s2:(FFI)state)`) THEN
    MAP_EVERY EXISTS_TAC [`s2:(FFI)state`; `Rval [v]:(v list,v)result`; `st2:REFS`;
      `ck1:num`] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP MON1AUX_evaluate_Handle_Rval
      (REWRITE_RULE[s_with_same_clock] th)]) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(handle_fun:(REFS->(A,E)exc#REFS)->(E->REFS->(A,E)exc#REFS)->
                     REFS->(A,E)exc#REFS) x1 x2 st = x1 st`
      (fun th -> REWRITE_TAC[MATCH_MP MON1AUX_MONAD_eq th]) THENL
     [USE_THEN "HF2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[PAIR_EQ; distinctness "exc"];
      ASM_REWRITE_TAC[MON1AUX_MONAD_THM; PAIR_EQ; injectivity "exc"; RIGHT_EXISTS_AND_THM;
        UNWIND_THM1] THEN ASM_MESON_TAC[]];
    (* an exception *)
    ASM_CASES_TAC `(CORRECT_CONS:E->bool) e` THENL
     [(* handled *)
      USE_THEN "EX1" (fun th -> FIRST_ASSUM(fun a1 -> FIRST_ASSUM(fun a2 ->
        MP_TAC(MATCH_MP (MATCH_MP th a1) a2)))) THEN
      DISCH_THEN(X_CHOOSE_THEN `paramsv:v list` STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `v:v`)) THEN
      SUBGOAL_THEN `REFS_PRED H (st2:REFS) (s2:(FFI)state)` ASSUME_TAC THENL
       [MON1AUX_FRAME_IMP_TAC; ALL_TAC] THEN
      REMOVE_THEN "A2" (MP_TAC o SPECL [`st2:REFS`; `e:E`; `paramsv:v list`]) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [USE_THEN "A4" (fun th -> MATCH_MP_TAC (CONJUNCT2 (SPECL [`st2:REFS`; `e:E`] th))) THEN
        ASM_REWRITE_TAC[ml_CONTAINER_def];
        ALL_TAC] THEN
      DISCH_THEN(fun e2 -> FIRST_ASSUM(fun rp ->
        MP_TAC(MATCH_MP MON1AUX_EvalM_MONAD_run (CONJ e2 rp)))) THEN
      DISCH_THEN(X_CHOOSE_THEN `s3:(FFI)state` (X_CHOOSE_THEN `res3:(v list,v)result`
        (X_CHOOSE_THEN `st3:REFS` (CONJUNCTS_THEN2 ASSUME_TAC
          (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `state_clock (s3:(FFI)state)`)))))) THEN
      REWRITE_TAC[s_with_same_clock] THEN
      DISCH_THEN(X_CHOOSE_TAC `ck2:num`) THEN
      REMOVE_THEN "R1" (X_CHOOSE_TAC `ck1:num` o SPEC `ck2:num`) THEN
      MAP_EVERY EXISTS_TAC [`s3:(FFI)state`; `res3:(v list,v)result`; `st3:REFS`;
        `ck1:num`] THEN
      MP_TAC(ISPECL [`state_clock_fupd (combin_K ck1) (s:(FFI)state)`; `env:v sem_env`;
        `exp1:exp`; `cons_name:(mlstring,mlstring)id`; `bind_names:mlstring list`;
        `exp2:exp`; `state_clock_fupd (combin_K ck2) (s2:(FFI)state)`; `stamp:num`; `stamp:num`;
        `paramsv:v list`; `arity:num`] MON1AUX_evaluate_Handle_Pcon) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [SUBGOAL_THEN `(handle_fun:(REFS->(A,E)exc#REFS)->(E->REFS->(A,E)exc#REFS)->
                         REFS->(A,E)exc#REFS) x1 x2 st = x2 e st2`
          (fun th -> REWRITE_TAC[MATCH_MP MON1AUX_MONAD_eq th]) THENL
         [USE_THEN "HF1" (fun th -> MATCH_MP_TAC (REWRITE_RULE[IMP_IMP] th)) THEN
          ASM_REWRITE_TAC[];
          ASM_REWRITE_TAC[]];
        MON1AUX_FRAME_CHAIN_TAC];
      (* not handled: the exception propagates *)
      USE_THEN "EX2" (fun th -> FIRST_ASSUM(fun a1 -> FIRST_ASSUM(fun a2 ->
        MP_TAC(MATCH_MP (MATCH_MP th a1) a2)))) THEN
      DISCH_THEN(X_CHOOSE_THEN `paramsv:v list` (X_CHOOSE_THEN `stamp_1:num`
        STRIP_ASSUME_TAC)) THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `v:v`)) THEN
      REMOVE_THEN "R1" (X_CHOOSE_TAC `ck1:num` o SPEC `state_clock (s2:(FFI)state)`) THEN
      MAP_EVERY EXISTS_TAC [`s2:(FFI)state`;
        `Rerr (Rraise (Conv (SOME (ExnStamp stamp_1)) paramsv)):(v list,v)result`;
        `st2:REFS`; `ck1:num`] THEN
      MP_TAC(ISPECL [`state_clock_fupd (combin_K ck1) (s:(FFI)state)`; `env:v sem_env`;
        `exp1:exp`; `cons_name:(mlstring,mlstring)id`; `bind_names:mlstring list`;
        `exp2:exp`; `state_clock_fupd (combin_K (state_clock s2)) (s2:(FFI)state)`; `stamp:num`;
        `stamp_1:num`; `paramsv:v list`; `arity:num`]
        MON1AUX_evaluate_Handle_Pcon_nomatch) THEN
      ASM_REWRITE_TAC[s_with_same_clock] THEN DISCH_THEN SUBST1_TAC THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(handle_fun:(REFS->(A,E)exc#REFS)->(E->REFS->(A,E)exc#REFS)->
                       REFS->(A,E)exc#REFS) x1 x2 st = x1 st`
        (fun th -> REWRITE_TAC[MATCH_MP MON1AUX_MONAD_eq th]) THENL
       [USE_THEN "HF2" MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[PAIR_EQ; injectivity "exc"] THEN ASM_MESON_TAC[];
        ASM_REWRITE_TAC[MON1AUX_MONAD_THM; PAIR_EQ; injectivity "exc";
          distinctness "exc"; RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
        ASM_MESON_TAC[]]]]);;

let ZIP3_def = cake_def
  `(ZIP3 ([]:A list,[]:B list,[]:C list) = []) /\
   (ZIP3 (CONS (x1:A) l1,CONS (x2:B) l2,CONS (x3:C) l3) =
      CONS (x1,x2,x3) (ZIP3 (l1,l2,l3)))`;;

let LIST_CONJ_def = cake_def
  `(LIST_CONJ [] <=> T) /\
   (LIST_CONJ (CONS x l) <=> x /\ LIST_CONJ l)`;;

let LIST_CONJ_APPEND = prove
 (`!a b. LIST_CONJ (APPEND a b) <=> LIST_CONJ a /\ LIST_CONJ b`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[LIST_CONJ_def; APPEND; CONJ_ASSOC]);;

let LIST_CONJ_REVERSE = prove
 (`!x. LIST_CONJ (REVERSE x) <=> LIST_CONJ x`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[LIST_CONJ_def; LIST_CONJ_APPEND; REVERSE] THEN
  CONV_TAC TAUT);;

let MON1AUX_LIST_CONJ_Eval_clock = prove
 (`!xs Ps (s:(FFI)state).
     LIST_CONJ (MAP (\(exp,P). ml_Eval env exp P) (ZIP xs Ps)) /\
     LENGTH xs = LENGTH Ps ==>
     ?vs junk. ALL2 (\f x. f x) Ps vs /\
       !ck. ?ck1. evaluate (state_clock_fupd (combin_K ck1) s) env xs =
                  (state_clock_fupd (combin_K ck) (state_refs_fupd (combin_K (APPEND (state_refs s) junk)) s),
                   Rval vs)`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ; ZIP; MAP; LIST_CONJ_def; ALL2] THENL
   [GEN_TAC THEN MAP_EVERY EXISTS_TAC [`[]:v list`; `[]:(v store_v)list`] THEN
    REWRITE_TAC[APPEND_NIL; with_same_refs; evaluate_def; ALL2] THEN
    X_GEN_TAC `ck:num` THEN EXISTS_TAC `ck:num` THEN REWRITE_TAC[];
    ALL_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:(FFI)state` o MATCH_MP MON1AUX_Eval_evaluate) THEN
  DISCH_THEN(X_CHOOSE_THEN `v:v` (X_CHOOSE_THEN `refs1:(v store_v)list`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "R1")))) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`t':(v->bool)list`;
    `state_refs_fupd (combin_K (APPEND (state_refs s) refs1)) (s:(FFI)state)`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `vs:v list` (X_CHOOSE_THEN `junk2:(v store_v)list`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "R2")))) THEN
  MAP_EVERY EXISTS_TAC [`CONS (v:v) vs`; `APPEND refs1 junk2:(v store_v)list`] THEN
  ASM_REWRITE_TAC[ALL2] THEN X_GEN_TAC `ck:num` THEN
  REMOVE_THEN "R2" (X_CHOOSE_TAC `c2:num` o SPEC `ck:num`) THEN
  REMOVE_THEN "R1" (X_CHOOSE_TAC `c1:num` o SPEC `c2:num`) THEN
  EXISTS_TAC `c1:num` THEN ONCE_REWRITE_TAC[evaluate_cons] THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(SIMP_RULE[]) THEN SIMP[] THEN ASM_REWRITE_TAC[] THEN
  CAKE_REWRITE_TAC[] THEN REWRITE_TAC[APPEND; APPEND_ASSOC]);;

let LIST_CONJ_Eval = prove
 (`!xs Ps (s:(FFI)state).
     LIST_CONJ (MAP (\(exp,P). ml_Eval env exp P) (ZIP xs Ps)) /\
     LENGTH xs = LENGTH Ps ==>
     ?ck vs junk.
       evaluate (state_clock_fupd (combin_K ck) s) env xs =
       (state_refs_fupd (combin_K (APPEND (state_refs s) junk)) s,Rval vs) /\
       ALL2 (\f x. f x) Ps vs`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`xs:exp list`; `Ps:(v->bool)list`; `s:(FFI)state`]
    MON1AUX_LIST_CONJ_Eval_clock) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `vs:v list` (X_CHOOSE_THEN `junk:(v store_v)list`
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `ck:num` o
      SPEC `state_clock (s:(FFI)state)`)))) THEN
  MAP_EVERY EXISTS_TAC [`ck:num`; `vs:v list`; `junk:(v store_v)list`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[state_update_clock_id]) THEN ASM_REWRITE_TAC[]);;

let LIST_REL_EQ_LIST_CONJ_MAP = prove
 (`!(xs:(A->bool)list) (ys:A list). LENGTH xs = LENGTH ys ==>
           (ALL2 (\f x. f x) xs ys <=> LIST_CONJ (MAP (\(P,v). P v) (ZIP xs ys)))`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ; ZIP; MAP; LIST_CONJ_def; ALL2] THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN ASM_SIMP_TAC[]);;

let MON1AUX_evaluate_Raise_Con = prove
 (`!(s:(FFI)state) env cons_name exprs s1 vs stamp.
     evaluate s env (REVERSE exprs) = (s1,Rval vs) /\
     ml_lookup_cons cons_name env = SOME (LENGTH exprs,stamp) ==>
     evaluate s env [Raise (Con (SOME cons_name) exprs)] =
     (s1,Rerr (Rraise (Conv (SOME stamp) (REVERSE vs))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ml_lookup_cons_def] THEN STRIP_TAC THEN
  REWRITE_TAC[evaluate_def] THEN
  ASM_REWRITE_TAC[do_con_check_def; build_conv_def] THEN CAKE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN REWRITE_TAC[HD]);;

let EvalM_raise = prove
 (`!cons_name stamp (EXN_TYPE:E->v->bool) EVAL_CONDS arity (E:E) exprs
    (f:REFS->(A,E)exc#REFS) (a:A->v->bool)
    (H:(REFS->hprop)#((FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list))).
     (!values. LENGTH values = arity ==>
               LIST_CONJ (MAP (\(P,v). P v) (ZIP EVAL_CONDS values)) ==>
               EXN_TYPE E (Conv (SOME (ExnStamp stamp)) values)) ==>
     f st = (M_failure E,st) ==>
     LENGTH exprs = arity ==>
     LENGTH EVAL_CONDS = arity ==>
     ml_lookup_cons cons_name env = SOME (arity,ExnStamp stamp) ==>
     LIST_CONJ (MAP (\(exp,P). ml_Eval env exp P) (ZIP exprs EVAL_CONDS)) ==>
     EvalM ro env st (Raise (Con (SOME cons_name) exprs)) (MONAD a EXN_TYPE f) H`,
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN REWRITE_TAC[EvalM_def] THEN
  X_GEN_TAC `s:(FFI)state` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`REVERSE exprs:exp list`; `REVERSE EVAL_CONDS:(v->bool)list`;
    `s:(FFI)state`] LIST_CONJ_Eval) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_REVERSE] THEN
    MP_TAC(ISPECL [`exprs:exp list`; `EVAL_CONDS:(v->bool)list`] REVERSE_ZIP) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC[GSYM MAP_REVERSE; LIST_CONJ_REVERSE];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN `vs:v list`
    (X_CHOOSE_THEN `junk:(v store_v)list` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC
   [`state_refs_fupd (combin_K (APPEND (state_refs s) junk)) (s:(FFI)state)`;
    `Rerr (Rraise (Conv (SOME (ExnStamp stamp)) (REVERSE vs))):(v list,v)result`;
    `st:REFS`; `ck:num`] THEN
  ASM_REWRITE_TAC[REFS_PRED_FRAME_append] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MON1AUX_evaluate_Raise_Con THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[MON1AUX_MONAD_THM; PAIR_EQ; distinctness "exc"; injectivity "exc";
      injectivity "result"; injectivity "error_result"; distinctness "result";
      RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[IMP_IMP] o check (is_forall o concl)) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP LIST_REL_LENGTH) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_REVERSE]) THEN
    SUBGOAL_THEN `LENGTH (vs:v list) = arity` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[LENGTH_REVERSE] THEN
    SUBGOAL_THEN `LENGTH (EVAL_CONDS:(v->bool)list) = LENGTH (REVERSE vs:v list)` ASSUME_TAC
    THENL [ASM_REWRITE_TAC[LENGTH_REVERSE]; ALL_TAC] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP LIST_REL_EQ_LIST_CONJ_MAP th)]) THEN
    ASM_REWRITE_TAC[EVERY2_REVERSE1]]);;

(* read and update refs *)

let MON1AUX_evaluate_Opderef = prove
 (`!(s:(FFI)state) env vname l v.
     nsLookup (sem_env_v env) (Short vname) = SOME (Loc T l) /\
     store_lookup l (state_refs s) = SOME (Refv v) ==>
     evaluate s env [App Opderef [Var (Short vname)]] = (s,Rval [v])`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[evaluate_def; REVERSE; APPEND] THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[getOpClass_def; REVERSE; APPEND] THEN CAKE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[do_app_def] THEN CAKE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[list_result_def; with_same_ffi; with_same_refs]);;

let MON1AUX_store_lookup_REF = prove
 (`!l xv H p (s:(FFI)state).
     (cf_REF (Loc T l) xv STAR H) (st2heap p s) ==>
     store_lookup l (state_refs s) = SOME (Refv xv)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP st2heap_REF_MEM) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP store2heap_IN_EL) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP store2heap_IN_LENGTH) THEN
  SIMP[store_lookup_def]);;

let EvalM_read_heap = prove
 (`!vname loc (TYPE:A->v->bool) (EXC_TYPE:E->v->bool) (H:REFS->hprop) (get_var:REFS->A).
     nsLookup (sem_env_v env) (Short vname) = SOME loc ==>
     EvalM ro env st (App Opderef [Var (Short vname)])
       (MONAD TYPE EXC_TYPE (\refs. (M_success (get_var refs),refs)))
       ((\refs. REF_REL TYPE loc (get_var refs) STAR H refs),
        (p:(FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[EvalM_def] THEN
  X_GEN_TAC `s:(FFI)state` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[REFS_PRED_def; REF_REL_def; SEP_CLAUSES;
    SEP_EXISTS_THM]) THEN
  DISCH_THEN(X_CHOOSE_TAC `v:v`) THEN MON1AUX_EXTRACT_PURE_FACTS_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM STAR_ASSOC]) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `l:num` SUBST_ALL_TAC o MATCH_MP REF_EXISTS_LOC o
    check (MON1AUX_head_is "STAR" o rator o concl)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MON1AUX_store_lookup_REF o
    check (MON1AUX_head_is "STAR" o rator o concl)) THEN
  MAP_EVERY EXISTS_TAC [`s:(FFI)state`; `Rval [v]:(v list,v)result`; `st:REFS`;
    `state_clock (s:(FFI)state)`] THEN
  REWRITE_TAC[s_with_same_clock; REFS_PRED_FRAME_same] THEN
  ASM_SIMP_TAC[MON1AUX_evaluate_Opderef] THEN
  REWRITE_TAC[MON1AUX_MONAD_THM; PAIR_EQ; injectivity "exc"; distinctness "exc";
    injectivity "result"; distinctness "result"; CONS_11; RIGHT_EXISTS_AND_THM;
    UNWIND_THM1] THEN
  ASM_REWRITE_TAC[]);;

let MON1AUX_do_app_Opassign = prove
 (`!refs (ffi:(FFI)ffi_state) l xv refs'.
     store_assign l (Refv xv) refs = SOME refs' ==>
     do_app (refs,ffi) Opassign [Loc T l; xv] = SOME ((refs',ffi),Rval (Conv NONE []))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN QCASES_ON "xv" THEN
  ASM_REWRITE_TAC[do_app_def] THEN CAKE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  CAKE_REWRITE_TAC[]);;

let MON1AUX_evaluate_Opassign = prove
 (`!(s:(FFI)state) env vname e s1 xv l refs'.
     evaluate s env [e] = (s1,Rval [xv]) /\
     nsLookup (sem_env_v env) (Short vname) = SOME (Loc T l) /\
     store_assign l (Refv xv) (state_refs s1) = SOME refs' ==>
     evaluate s env [App Opassign [Var (Short vname); e]] =
     (state_refs_fupd (combin_K refs') s1,Rval [Conv NONE []])`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `evaluate (s1:(FFI)state) env [Var (Short vname)] = (s1,Rval [Loc T l])`
    ASSUME_TAC THENL
   [MATCH_MP_TAC MON1AUX_evaluate_Var_Short THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [evaluate_def] THEN REWRITE_TAC[REVERSE; APPEND] THEN
  REWRITE_TAC[MATCH_MP MON1AUX_evaluate_two
    (CONJ (ASSUME `evaluate (s:(FFI)state) env [e] = (s1,Rval [xv:v])`)
          (ASSUME `evaluate (s1:(FFI)state) env [Var (Short vname)] =
                   (s1,Rval [Loc T l])`))] THEN
  REWRITE_TAC[getOpClass_def; HD; REVERSE; APPEND] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[HD; REVERSE; APPEND] THEN
  ASM_SIMP_TAC[MON1AUX_do_app_Opassign] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[list_result_def; with_same_ffi]);;

let MON1AUX_REF_IN_LENGTH = prove
 (`!l v H p (s:(FFI)state).
     (cf_REF (Loc T l) v STAR H) (st2heap p s) ==> l < LENGTH (state_refs s)`,
  MESON_TAC[st2heap_REF_MEM; store2heap_IN_LENGTH]);;

let MON1AUX_store_assign_REF = prove
 (`!l v H p (s:(FFI)state) xv junk.
     (cf_REF (Loc T l) v STAR H) (st2heap p s) ==>
     store_assign l (Refv xv) (APPEND (state_refs s) junk) =
     SOME (LUPDATE (Refv xv) l (APPEND (state_refs s) junk))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MON1AUX_REF_IN_LENGTH) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP STATE_EXTRACT_FROM_HPROP_REF) THEN
  DISCH_THEN(MP_TAC o SPEC `junk:(v store_v)list`) THEN
  ASM_SIMP_TAC[store_assign_def; LENGTH_APPEND; ARITH_RULE `l < a ==> l < a + b`] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[store_v_same_type_def] THEN
  CAKE_REWRITE_TAC[]);;

let MON1AUX_REF_update_frame = prove
 (`!l v0 xv G p (s:(FFI)state) junk.
     (cf_REF (Loc T l) v0 STAR G) (st2heap p s) ==>
     (cf_REF (Loc T l) xv STAR G STAR cf_GC)
       (st2heap p (state_refs_fupd (combin_K (LUPDATE (Refv xv) l (APPEND (state_refs s) junk))) s))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MON1AUX_REF_IN_LENGTH) THEN
  ASM_SIMP_TAC[LUPDATE_APPEND1] THEN MATCH_MP_TAC STATE_APPEND_JUNK THEN
  MATCH_MP_TAC(GEN_ALL STATE_UPDATE_HPROP_REF) THEN EXISTS_TAC `v0:v` THEN
  ASM_REWRITE_TAC[]);;

(* closing a goal H1 h from an assumption H2 h with H1 and H2 equal up to   *)
(* associativity and commutativity of STAR                                   *)

let MON1AUX_HPROP_AC_TAC : tactic = fun (asl,w as g) ->
  let hp,h = dest_comb w in
  tryfind (fun (_,th) ->
    let hq,h' = dest_comb (concl th) in
    if not (aconv h' h) then fail() else
    let eq = AC LSORTAUX_STAR_AC (mk_eq(hq,hp)) in
    ACCEPT_TAC (EQ_MP (AP_THM eq h) th) g) asl;;

let EvalM_write_heap = prove
 (`!vname loc (TYPE:A->v->bool) (PINV:REFS->bool) (EXC_TYPE:E->v->bool) (H:REFS->hprop)
    (get_var:REFS->A) set_var x exp env.
     (!refs x. get_var (set_var x refs) = x) ==>
     (!refs x. H (set_var x refs) = H refs) ==>
     nsLookup (sem_env_v env) (Short vname) = SOME loc ==>
     ml_CONTAINER (PINV st ==> PINV (set_var x st)) ==>
     ml_Eval env exp (TYPE x) ==>
     EvalM ro env st (App Opassign [Var (Short vname); exp])
       ((MONAD UNIT_TYPE EXC_TYPE) (\refs. (M_success one,set_var x refs)))
       ((\refs. REF_REL TYPE loc (get_var refs) STAR H refs STAR set_sep_cond (PINV refs)),
        (p:(FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)))`,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "GET") THEN DISCH_THEN(LABEL_TAC "HSET") THEN
  DISCH_TAC THEN REWRITE_TAC[ml_CONTAINER_def] THEN DISCH_THEN(LABEL_TAC "CONT") THEN
  DISCH_THEN(LABEL_TAC "EV") THEN
  REWRITE_TAC[EvalM_def] THEN X_GEN_TAC `s:(FFI)state` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[REFS_PRED_def; REF_REL_def; SEP_CLAUSES;
    SEP_EXISTS_THM] o check (MON1AUX_head_is "REFS_PRED" o concl)) THEN
  DISCH_THEN(X_CHOOSE_THEN `v0:v` (STRIP_ASSUME_TAC o
    REWRITE_RULE[GSYM STAR_ASSOC] o CONV_RULE MON1AUX_EXTRACT_PURE_FACTS_CONV)) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `l:num` SUBST_ALL_TAC o MATCH_MP REF_EXISTS_LOC o
    check (MON1AUX_head_is "STAR" o rator o concl)) THEN
  REMOVE_THEN "EV" (MP_TAC o SPEC `s:(FFI)state` o MATCH_MP MON1AUX_Eval_evaluate) THEN
  DISCH_THEN(X_CHOOSE_THEN `xv:v` (X_CHOOSE_THEN `junk:(v store_v)list`
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `c1:num` o
      SPEC `state_clock (s:(FFI)state)`)))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[state_update_clock_id]) THEN
  FIRST_ASSUM(ASSUME_TAC o SPECL [`xv:v`; `junk:(v store_v)list`] o
    MATCH_MP MON1AUX_store_assign_REF o check (MON1AUX_head_is "STAR" o rator o concl)) THEN
  MAP_EVERY EXISTS_TAC
   [`state_refs_fupd (combin_K (LUPDATE (Refv xv) l (APPEND (state_refs s) junk))) (s:(FFI)state)`;
    `Rval [Conv NONE []]:(v list,v)result`; `(set_var:A->REFS->REFS) x st`; `c1:num`] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`state_clock_fupd (combin_K c1) (s:(FFI)state)`; `env:v sem_env`;
      `vname:mlstring`; `exp:exp`;
      `state_refs_fupd (combin_K (APPEND (state_refs s) junk)) (s:(FFI)state)`; `xv:v`; `l:num`;
      `LUPDATE (Refv xv) l (APPEND (state_refs (s:(FFI)state)) junk)`]
      MON1AUX_evaluate_Opassign) THEN
    SIMP[] THEN ASM_REWRITE_TAC[] THEN SIMP[];
    REWRITE_TAC[MON1AUX_MONAD_THM; PAIR_EQ; injectivity "exc"; distinctness "exc";
      injectivity "result"; distinctness "result"; CONS_11; RIGHT_EXISTS_AND_THM;
      UNWIND_THM1; UNIT_TYPE_def] THEN MESON_TAC[];
    REWRITE_TAC[REFS_PRED_FRAME_def] THEN SIMP[] THEN CONJ_TAC THENL
     [MESON_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `F':hprop` THEN USE_THEN "GET" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "HSET" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[REF_REL_def; SEP_CLAUSES; SEP_EXISTS_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `v1:v` (STRIP_ASSUME_TAC o
      REWRITE_RULE[GSYM STAR_ASSOC] o CONV_RULE MON1AUX_EXTRACT_PURE_FACTS_CONV)) THEN
    FIRST_X_ASSUM(ASSUME_TAC o SPECL [`xv:v`; `junk:(v store_v)list`] o
      MATCH_MP MON1AUX_REF_update_frame o
      check (fun th -> free_in `F':hprop` (concl th))) THEN
    EXISTS_TAC `xv:v` THEN CONV_TAC MON1AUX_EXTRACT_PURE_FACTS_CONV THEN
    ASM_REWRITE_TAC[] THEN MON1AUX_HPROP_AC_TAC]);;

(* Dynamic allocation of references *)

let STATE_REF_def = cake_def
  `STATE_REF (A:A->v->bool) r x = SEP_EXISTS v. cf_REF r v STAR set_sep_cond (A x v)`;;

let STATE_REFS_def = cake_def
  `(STATE_REFS (A:A->v->bool) [] [] = set_sep_emp) /\
   (STATE_REFS A (CONS r refs) (CONS x state) =
      STATE_REF A r x STAR STATE_REFS A refs state) /\
   (STATE_REFS A [] (CONS x state) = set_sep_cond F) /\
   (STATE_REFS A (CONS r refs) [] = set_sep_cond F)`;;

let RES_MONAD = cake_def
  `RES_MONAD (A:A->v->bool) =
     (MONAD A (\x v. F):(REFS->(A,B)exc#REFS)->REFS->REFS#(v list,v)result->bool)`;;

let MON1AUX_store2heap_REF_SAT = prove
 (`!l v. cf_REF (Loc T l) v (store2heap_aux l [Refv v])`,
  REWRITE_TAC[store2heap_aux_def; REF_HPROP_SAT_EQ]);;

let MON1AUX_STATE_REF_cell = prove
 (`!(A:A->v->bool) x v l. A x v ==> STATE_REF A (Loc T l) x (store2heap_aux l [Refv v])`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[STATE_REF_def; SEP_EXISTS_THM] THEN
  EXISTS_TAC `v:v` THEN ASM_REWRITE_TAC[cf_HCOND_EXTRACT; MON1AUX_store2heap_REF_SAT]);;

(* Validity of a store extension *)

let valid_state_refs_frame_extension = prove
 (`!H junk. (A:A->v->bool) ((cons:B->A) x) res ==>
     (STATE_REFS A ptrs state STAR H) (st2heap p (s:(FFI)state)) ==>
     (STATE_REFS A (CONS (Loc T (LENGTH (APPEND (state_refs s) junk))) ptrs)
        (CONS (cons x) state) STAR H STAR cf_GC)
       (st2heap p (state_refs_fupd
         (combin_K (APPEND (APPEND (state_refs s) junk) [Refv res])) s))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[STATE_REFS_def] THEN
  SUBGOAL_THEN
   `((STATE_REFS (A:A->v->bool) ptrs state STAR H) STAR cf_GC)
      (st2heap p (state_refs_fupd (combin_K (APPEND (state_refs s) junk)) (s:(FFI)state)))`
    ASSUME_TAC THENL
   [MATCH_MP_TAC STATE_APPEND_JUNK THEN ASM_REWRITE_TAC[with_same_refs]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(STATE_REF (A:A->v->bool) (Loc T (LENGTH (APPEND (state_refs s) junk)))
       ((cons:B->A) x) STAR
     ((STATE_REFS A ptrs state STAR H) STAR cf_GC))
       (st2heap p (state_refs_fupd
         (combin_K (APPEND (APPEND (state_refs s) junk) [Refv res])) (s:(FFI)state)))`
    MP_TAC THENL
   [MATCH_MP_TAC MON1AUX_STAR_I THEN
    MAP_EVERY EXISTS_TAC
     [`store2heap_aux (LENGTH (APPEND (state_refs (s:(FFI)state)) junk)) [Refv (res:v)]`;
      `st2heap p (state_refs_fupd (combin_K (APPEND (state_refs s) junk)) (s:(FFI)state))`] THEN
    ASM_SIMP_TAC[MON1AUX_STATE_REF_cell] THEN
    ONCE_REWRITE_TAC[SPLIT_SYM] THEN REWRITE_TAC[STATE_SPLIT_REFS];
    DISCH_TAC THEN MON1AUX_HPROP_AC_TAC]);;

let valid_state_refs_extension = prove
 (`(A:A->v->bool) ((cons:B->A) x) res ==>
   REFS_PRED (STATE_REFS A ptrs,p) refs (s:(FFI)state) ==>
   REFS_PRED (STATE_REFS A (CONS (Loc T (LENGTH (APPEND (state_refs s) junk))) ptrs),p)
     (CONS (cons x) refs)
     (state_refs_fupd (combin_K (APPEND (APPEND (state_refs s) junk) [Refv res])) s)`,
  REWRITE_TAC[REFS_PRED_def] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th1 -> FIRST_ASSUM(fun th2 ->
    MP_TAC(MATCH_MP (MATCH_MP (SPECL [`cf_GC`; `junk:(v store_v)list`]
      valid_state_refs_frame_extension) th1) th2))) THEN
  REWRITE_TAC[GSYM STAR_ASSOC; GC_STAR_GC]);;

(* proving p = q for STAR terms equal up to associativity and commutativity *)

let MON1AUX_STAR_AC_TAC : tactic = fun (asl,w as g) ->
  ACCEPT_TAC (AC LSORTAUX_STAR_AC w) g;;

let STATE_REFS_LENGTH = prove
 (`!ptrs state H. (STATE_REFS (A:A->v->bool) ptrs state STAR H) s ==>
                  LENGTH ptrs = LENGTH state`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[STATE_REFS_def; LENGTH; SEP_CLAUSES; SEP_F_def; NOT_SUC; SUC_INJ] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  EXISTS_TAC `STATE_REF (A:A->v->bool) h h' STAR H` THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> not (is_forall (concl th)))) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN MESON_TAC[STAR_ASSOC; STAR_COMM]);;

let valid_state_refs_reduction = prove
 (`(STATE_REFS (A:A->v->bool) (CONS rv ptrs) refs STAR H STAR cf_GC) s ==>
   (STATE_REFS A ptrs (TL refs) STAR H STAR cf_GC) s`,
  DISCH_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP STATE_REFS_LENGTH o
    REWRITE_RULE[GSYM STAR_ASSOC]) THEN
  NAMED_CASES_ON "refs" [""; "h t"] THEN REWRITE_TAC[LENGTH; NOT_SUC; TL] THEN DISCH_TAC THEN
  MATCH_MP_TAC ml_monad_translator_GC_ABSORB_L THEN
  EXISTS_TAC `STATE_REF (A:A->v->bool) rv h` THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[STATE_REFS_def] o
    check (MON1AUX_head_is "STAR" o rator o concl)) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN MON1AUX_STAR_AC_TAC);;

(* Validity of ref_bind *)

let MON1AUX_evaluate_Opref = prove
 (`!(s:(FFI)state) env e s1 v.
     evaluate s env [e] = (s1,Rval [v]) ==>
     evaluate s env [App Opref [e]] =
     (state_refs_fupd (combin_K (APPEND (state_refs s1) [Refv v])) s1,
      Rval [Loc T (LENGTH (state_refs s1))])`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [evaluate_def] THEN
  ASM_REWRITE_TAC[REVERSE; APPEND] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[getOpClass_def; REVERSE; APPEND] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[do_app_def; store_alloc_def] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[list_result_def; with_same_ffi]);;

let EvalM_ref_bind = prove
 (`ml_Eval env xexpr ((A:A->v->bool) ((cons:X->A) x)) ==>
   (!rv r. EvalM ro (ml_write rname rv env) (CONS (cons x) st) exp
             (MONAD (TYPE:B->v->bool) (MON_EXN_TYPE:E->v->bool)
                ((f:store_ref->(A)list->(B,E)exc#(A)list) r))
             (STATE_REFS A (CONS rv ptrs),
              (p:(FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)))) ==>
   EvalM ro env st (Let (SOME rname) (App Opref [xexpr]) exp)
     (MONAD TYPE MON_EXN_TYPE (ref_bind (Mref cons x) f (Mpop_ref e)))
     (STATE_REFS A ptrs,p)`,
  DISCH_THEN(LABEL_TAC "EV") THEN DISCH_THEN(LABEL_TAC "IN") THEN
  REWRITE_TAC[EvalM_def] THEN X_GEN_TAC `s:(FFI)state` THEN DISCH_TAC THEN
  REMOVE_THEN "EV" (MP_TAC o SPEC `s:(FFI)state` o MATCH_MP MON1AUX_Eval_evaluate) THEN
  DISCH_THEN(X_CHOOSE_THEN `v:v` (X_CHOOSE_THEN `junk:(v store_v)list`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "R1")))) THEN
  SUBGOAL_THEN `REFS_PRED (STATE_REFS (A:A->v->bool) (CONS (Loc T (LENGTH (APPEND (state_refs (s:(FFI)state)) junk))) ptrs),
                  (p:(FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)))
                  (CONS ((cons:X->A) x) st) (state_refs_fupd (combin_K (APPEND (APPEND (state_refs s) junk) [Refv v])) (s:(FFI)state))` ASSUME_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] (GEN_ALL valid_state_refs_extension)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "IN" (MP_TAC o SPECL [`Loc T (LENGTH (APPEND (state_refs (s:(FFI)state)) junk))`; `StoreRef (LENGTH (st:(A)list))`]) THEN
  DISCH_THEN(fun e2 -> FIRST_ASSUM(fun rp ->
    MP_TAC(MATCH_MP MON1AUX_EvalM_MONAD_run (CONJ e2 rp)))) THEN
  DISCH_THEN(X_CHOOSE_THEN `s3:(FFI)state` (X_CHOOSE_THEN `res3:(v list,v)result`
    (X_CHOOSE_THEN `st3:(A)list` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `state_clock (s3:(FFI)state)`)))))) THEN
  REWRITE_TAC[s_with_same_clock] THEN DISCH_THEN(X_CHOOSE_TAC `ck2:num`) THEN
  REMOVE_THEN "R1" (X_CHOOSE_TAC `ck1:num` o SPEC `ck2:num`) THEN
  SUBGOAL_THEN `LENGTH (st3:(A)list) = SUC (LENGTH (ptrs:v list))` ASSUME_TAC THENL
   [SUBGOAL_THEN `REFS_PRED (STATE_REFS (A:A->v->bool) (CONS (Loc T (LENGTH (APPEND (state_refs (s:(FFI)state)) junk))) ptrs),
                    (p:(FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)))
                    st3 (s3:(FFI)state)` MP_TAC THENL
     [MON1AUX_FRAME_IMP_TAC; ALL_TAC] THEN
    REWRITE_TAC[REFS_PRED_def] THEN DISCH_THEN(MP_TAC o MATCH_MP STATE_REFS_LENGTH) THEN
    REWRITE_TAC[LENGTH] THEN MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`s3:(FFI)state`; `res3:(v list,v)result`; `TL (st3:(A)list)`;
    `ck1:num`] THEN
  REPEAT CONJ_TAC THENL
   [(* the evaluation *)
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP MON1AUX_evaluate_Let_Rval
      (MATCH_MP MON1AUX_evaluate_Opref th)]) THEN
    REWRITE_TAC[MON1AUX_nsOptBind_write] THEN SIMP[] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> free_in `s3:(FFI)state` (concl th) &&
      MON1AUX_head_is "evaluate" (lhs (concl th)))) THEN
    SIMP[];
    (* MONAD *)
    FIRST_X_ASSUM(MP_TAC o check (fun th -> length (snd(strip_comb(concl th))) = 5 &&
      MON1AUX_head_is "MONAD" (concl th))) THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
      MON1AUX_head_is "LENGTH" (lhs (concl th)) && free_in `st3:(A)list` (concl th))) THEN
    NAMED_CASES_ON "st3" [""; "h t"] THEN REWRITE_TAC[LENGTH; NOT_SUC; TL] THEN
    DISCH_TAC THEN
    REWRITE_TAC[MON1AUX_MONAD_THM; ref_bind_def; ml_monadBase_Mref_def;
      ml_monadBase_Mpop_ref_def] THEN
    CAKE_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
    REWRITE_TAC[PAIR_EQ; injectivity "exc"; distinctness "exc"; injectivity "result";
      distinctness "result"; injectivity "error_result"; CONS_11; RIGHT_EXISTS_AND_THM;
      UNWIND_THM1] THEN
    ASM_REWRITE_TAC[];
    (* frame *)
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[REFS_PRED_FRAME_def] o
      check (MON1AUX_head_is "REFS_PRED_FRAME" o concl)) THEN
    REWRITE_TAC[REFS_PRED_FRAME_def] THEN SIMP[LENGTH_APPEND] THEN STRIP_TAC THEN
    X_GEN_TAC `F1:hprop` THEN DISCH_TAC THEN
    MATCH_MP_TAC(GEN_ALL valid_state_refs_reduction) THEN
    EXISTS_TAC `Loc T (LENGTH (state_refs (s:(FFI)state)) + LENGTH (junk:(v store_v)list))` THEN
    ONCE_REWRITE_TAC[GSYM GC_STAR_GC] THEN REWRITE_TAC[STAR_ASSOC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `F1 STAR cf_GC` o check (is_forall o concl)) THEN
    REWRITE_TAC[STAR_ASSOC] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[GSYM LENGTH_APPEND] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] (GEN_ALL valid_state_refs_frame_extension)) THEN
    ASM_REWRITE_TAC[]]);;


(* Validity of a deref operation *)

let STATE_REFS_EXTRACT = prove
 (`!ptrs1 r ptrs2 refs (TYPE:A->v->bool) H p (s:(FFI)state).
     (STATE_REFS TYPE (APPEND (APPEND ptrs1 [r]) ptrs2) refs STAR H) (st2heap p s) ==>
     (STATE_REFS TYPE ptrs1 (TAKE (LENGTH ptrs1) refs) STAR
      STATE_REF TYPE r (EL (LENGTH ptrs1) refs) STAR
      STATE_REFS TYPE ptrs2 (DROP (LENGTH ptrs1 + 1) refs) STAR H) (st2heap p s)`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP STATE_REFS_LENGTH) THEN POP_ASSUM MP_TAC THEN
  NAMED_CASES_ON "refs" [""; "x xs"] THEN
  REWRITE_TAC[APPEND; LENGTH; NOT_SUC; GSYM NOT_SUC; SUC_INJ] THENL
   [REWRITE_TAC[STATE_REFS_def; TAKE; DROP; EL; HD; ADD_CLAUSES; GSYM ONE;
      SEP_CLAUSES] THEN
    REWRITE_TAC[ONE; DROP] THEN REPEAT DISCH_TAC THEN MON1AUX_HPROP_AC_TAC;
    REWRITE_TAC[STATE_REFS_def] THEN REPEAT DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`r:v`; `ptrs2:v list`; `xs:(A)list`; `TYPE:A->v->bool`;
      `STATE_REF (TYPE:A->v->bool) h x STAR H`;
      `p:(FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)`;
      `s:(FFI)state`]) THEN
    ANTS_TAC THENL [MON1AUX_HPROP_AC_TAC; ALL_TAC] THEN
    REWRITE_TAC[TAKE; DROP; EL; TL; STATE_REFS_def; ARITH_RULE `SUC n + 1 = SUC (n + 1)`] THEN
    DISCH_TAC THEN MON1AUX_HPROP_AC_TAC]);;

let MON1AUX_split3_parts = prove
 (`!(refs1:A list) x refs2 n.
     n = LENGTH refs1 ==>
     TAKE n (APPEND (APPEND refs1 [x]) refs2) = refs1 /\
     EL n (APPEND (APPEND refs1 [x]) refs2) = x /\
     DROP (n + 1) (APPEND (APPEND refs1 [x]) refs2) = refs2`,
  REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[el_append3; GSYM APPEND_ASSOC; TAKE_LENGTH_APPEND] THEN
  REWRITE_TAC[APPEND_ASSOC] THEN
  SUBGOAL_THEN `LENGTH (refs1:A list) + 1 = LENGTH (APPEND refs1 [x])` SUBST1_TAC THENL
   [REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ARITH_TAC;
    REWRITE_TAC[DROP_LENGTH_APPEND]]);;

let STATE_REFS_EXTRACT_2 = prove
 (`!ptrs1 r ptrs2 refs1 x refs2 (TYPE:A->v->bool) H p (s:(FFI)state).
     LENGTH ptrs1 = LENGTH refs1 ==>
     LENGTH ptrs2 = LENGTH refs2 ==>
     (STATE_REFS TYPE (APPEND (APPEND ptrs1 [r]) ptrs2) (APPEND (APPEND refs1 [x]) refs2)
        STAR H) (st2heap p s) ==>
     (STATE_REFS TYPE ptrs1 refs1 STAR STATE_REF TYPE r x STAR
      STATE_REFS TYPE ptrs2 refs2 STAR H) (st2heap p s)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP STATE_REFS_EXTRACT) THEN
  ASM_SIMP_TAC[MON1AUX_split3_parts]);;

let STATE_REFS_RECONSTRUCT = prove
 (`!ptrs1 r ptrs2 refs1 y refs2 (TYPE:A->v->bool) H p (s:(FFI)state).
     (STATE_REFS TYPE ptrs1 refs1 STAR STATE_REF TYPE r y STAR
      STATE_REFS TYPE ptrs2 refs2 STAR H) (st2heap p s) ==>
     (STATE_REFS TYPE (APPEND (APPEND ptrs1 [r]) ptrs2) (APPEND (APPEND refs1 [y]) refs2)
        STAR H) (st2heap p s)`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  NAMED_CASES_ON "refs1" [""; "x xs"] THEN
  REWRITE_TAC[APPEND; STATE_REFS_def; SEP_CLAUSES; SEP_F_def] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`r:v`; `ptrs2:v list`; `xs:(A)list`; `y:A`;
    `refs2:(A)list`; `TYPE:A->v->bool`; `STATE_REF (TYPE:A->v->bool) h x STAR H`;
    `p:(FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)`; `s:(FFI)state`]) THEN
  ANTS_TAC THENL [MON1AUX_HPROP_AC_TAC; DISCH_TAC THEN MON1AUX_HPROP_AC_TAC]);;

let STATE_REFS_DECOMPOSE = prove
 (`!ptrs1 r ptrs2 refs (TYPE:A->v->bool) H p (s:(FFI)state).
     (STATE_REFS TYPE (APPEND (APPEND ptrs1 [r]) ptrs2) refs STAR H) (st2heap p s) <=>
     ?refs1 y refs2.
       refs = APPEND (APPEND refs1 [y]) refs2 /\
       (STATE_REFS TYPE ptrs1 refs1 STAR STATE_REF TYPE r y STAR
        STATE_REFS TYPE ptrs2 refs2 STAR H) (st2heap p s)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP STATE_REFS_LENGTH) THEN
    REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC [`TAKE (LENGTH (ptrs1:v list)) (refs:(A)list)`;
      `EL (LENGTH (ptrs1:v list)) (refs:(A)list)`;
      `DROP (LENGTH (ptrs1:v list) + 1) (refs:(A)list)`] THEN
    ASM_SIMP_TAC[STATE_REFS_EXTRACT] THEN
    REWRITE_TAC[GSYM APPEND_ASSOC; APPEND] THEN
    SUBGOAL_THEN `LENGTH (ptrs1:v list) < LENGTH (refs:(A)list)` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM DROP_EL_CONS; TAKE_DROP];
    STRIP_TAC THEN ASM_SIMP_TAC[STATE_REFS_RECONSTRUCT]]);;

let STATE_REFS_DECOMPOSE_2 = prove
 (`!ptrs1 r ptrs2 refs1 x refs2 (TYPE:A->v->bool) H p (s:(FFI)state).
     LENGTH ptrs1 = LENGTH refs1 ==>
     LENGTH ptrs2 = LENGTH refs2 ==>
     ((STATE_REFS TYPE (APPEND (APPEND ptrs1 [r]) ptrs2) (APPEND (APPEND refs1 [x]) refs2)
         STAR H) (st2heap p s) <=>
      (STATE_REFS TYPE ptrs1 refs1 STAR STATE_REF TYPE r x STAR
       STATE_REFS TYPE ptrs2 refs2 STAR H) (st2heap p s))`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  ASM_SIMP_TAC[STATE_REFS_EXTRACT_2; STATE_REFS_RECONSTRUCT]);;

let store_lookup_CELL_st2heap = prove
 (`(cf_cell l res STAR H) (st2heap p (s:(FFI)state)) ==>
   store_lookup l (APPEND (state_refs s) junk) = SOME res`,
  DISCH_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP STATE_EXTRACT_FROM_HPROP) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP store2heap_IN_LENGTH o MATCH_MP st2heap_CELL_MEM) THEN
  SIMP[store_lookup_def; LENGTH_APPEND; ARITH_RULE `l < a ==> l < a + b:num`]);;

let store_lookup_REF_st2heap = prove
 (`(cf_REF (Loc T l) v STAR H) (st2heap p (s:(FFI)state)) ==>
   store_lookup l (state_refs s) = SOME (Refv v)`,
  REWRITE_TAC[MON1AUX_store_lookup_REF]);;

let store_lookup_REF_st2heap_junk = prove
 (`(cf_REF (Loc T l) v STAR H) (st2heap p (s:(FFI)state)) ==>
   store_lookup l (APPEND (state_refs s) junk) = SOME (Refv v)`,
  DISCH_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP STATE_EXTRACT_FROM_HPROP_REF) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MON1AUX_REF_IN_LENGTH) THEN
  SIMP[store_lookup_def; LENGTH_APPEND; ARITH_RULE `l < a ==> l < a + b:num`]);;

let store_lookup_ARRAY_st2heap = prove
 (`(cf_ARRAY (Loc T l) av STAR H) (st2heap p (s:(FFI)state)) ==>
   store_lookup l (state_refs s) = SOME (Varray av)`,
  DISCH_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP st2heap_ARRAY_MEM) THEN
  DISCH_THEN(fun th -> MP_TAC(MATCH_MP store2heap_IN_EL th) THEN
                       MP_TAC(MATCH_MP store2heap_IN_LENGTH th)) THEN
  SIMP[store_lookup_def]);;

let MON1AUX_STATE_REFS_lookup = prove
 (`!ptrs1 rv ptrs2 st (TYPE:A->v->bool) H p (s:(FFI)state).
     (STATE_REFS TYPE (APPEND (APPEND ptrs1 [rv]) ptrs2) st STAR H) (st2heap p s) ==>
     ?l v. rv = Loc T l /\ store_lookup l (state_refs s) = SOME (Refv v) /\
           TYPE (EL (LENGTH ptrs1) st) v /\
           LENGTH st = LENGTH ptrs1 + 1 + LENGTH ptrs2`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP STATE_REFS_LENGTH) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP STATE_REFS_EXTRACT) THEN
  REWRITE_TAC[STATE_REF_def; SEP_CLAUSES; SEP_EXISTS_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:v` (STRIP_ASSUME_TAC o REWRITE_RULE[GSYM STAR_ASSOC] o
    CONV_RULE MON1AUX_EXTRACT_PURE_FACTS_CONV)) THEN
  REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN DISCH_TAC THEN
  SUBGOAL_THEN `?l. rv = Loc T l` (X_CHOOSE_THEN `l:num` SUBST_ALL_TAC) THENL
   [MATCH_MP_TAC(GEN_ALL REF_EXISTS_LOC) THEN
    MAP_EVERY EXISTS_TAC [`v:v`; `STATE_REFS (TYPE:A->v->bool) ptrs2
      (DROP (LENGTH (ptrs1:v list) + 1) st) STAR H STAR
      STATE_REFS TYPE ptrs1 (TAKE (LENGTH ptrs1) st)`; `st2heap p (s:(FFI)state)`] THEN
    MON1AUX_HPROP_AC_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`l:num`; `v:v`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
  MATCH_MP_TAC(GEN_ALL store_lookup_REF_st2heap) THEN
  MAP_EVERY EXISTS_TAC [`STATE_REFS (TYPE:A->v->bool) ptrs2
      (DROP (LENGTH (ptrs1:v list) + 1) st) STAR H STAR
      STATE_REFS TYPE ptrs1 (TAKE (LENGTH ptrs1) st)`;
    `p:(FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)`] THEN
  MON1AUX_HPROP_AC_TAC);;

let EvalM_Mdref = prove
 (`nsLookup (sem_env_v env) (Short rname) = SOME rv ==>
   r = LENGTH ptrs2 ==>
   EvalM ro env st (App Opderef [Var (Short rname)])
     (MONAD (TYPE:A->v->bool) (\x v. F) (Mdref (e:E) (StoreRef r)))
     (STATE_REFS TYPE (APPEND (APPEND ptrs1 [rv]) ptrs2),
      (p:(FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)))`,
  REPEAT DISCH_TAC THEN REWRITE_TAC[EvalM_def; REFS_PRED_def] THEN
  X_GEN_TAC `s:(FFI)state` THEN
  DISCH_THEN(MP_TAC o MATCH_MP MON1AUX_STATE_REFS_lookup) THEN
  DISCH_THEN(X_CHOOSE_THEN `l:num` (X_CHOOSE_THEN `v:v` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `rv:v`)) THEN
  MAP_EVERY EXISTS_TAC [`s:(FFI)state`; `Rval [v]:(v list,v)result`; `st:(A)list`;
    `state_clock (s:(FFI)state)`] THEN
  REWRITE_TAC[s_with_same_clock; REFS_PRED_FRAME_same] THEN
  ASM_SIMP_TAC[MON1AUX_evaluate_Opderef] THEN
  SUBGOAL_THEN `LENGTH (ptrs2:v list) < LENGTH (st:(A)list)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[MON1AUX_MONAD_THM; PAIR_EQ; injectivity "exc"; distinctness "exc";
    injectivity "result"; distinctness "result"; CONS_11; RIGHT_EXISTS_AND_THM;
    UNWIND_THM1] THEN
  ASM_SIMP_TAC[ml_monadBase_Mdref_eq; dref_def; PAIR_EQ; injectivity "exc";
    UNWIND_THM1] THEN
  ASM_REWRITE_TAC[ARITH_RULE `(a + 1 + b) - b - 1 = a`]);;

(* Validity of an assigment operation *)

let store_assign_REF_st2heap = prove
 (`(cf_REF (Loc T l) v STAR H) (st2heap p (s:(FFI)state)) ==>
   store_assign l (Refv res) (APPEND (state_refs s) junk) =
   SOME (LUPDATE (Refv res) l (APPEND (state_refs s) junk))`,
  REWRITE_TAC[MON1AUX_store_assign_REF]);;

let MON1AUX_STATE_REFS_REF = prove
 (`!ptrs1 rv ptrs2 st (TYPE:A->v->bool) H p (s:(FFI)state).
     (STATE_REFS TYPE (APPEND (APPEND ptrs1 [rv]) ptrs2) st STAR H) (st2heap p s) ==>
     ?l v G. rv = Loc T l /\ (cf_REF (Loc T l) v STAR G) (st2heap p s) /\
             TYPE (EL (LENGTH ptrs1) st) v /\
             LENGTH st = LENGTH ptrs1 + 1 + LENGTH ptrs2`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP STATE_REFS_LENGTH) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP STATE_REFS_EXTRACT) THEN
  REWRITE_TAC[STATE_REF_def; SEP_CLAUSES; SEP_EXISTS_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:v` (STRIP_ASSUME_TAC o REWRITE_RULE[GSYM STAR_ASSOC] o
    CONV_RULE MON1AUX_EXTRACT_PURE_FACTS_CONV)) THEN
  REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN DISCH_TAC THEN
  ABBREV_TAC `G = STATE_REFS (TYPE:A->v->bool) ptrs2
      (DROP (LENGTH (ptrs1:v list) + 1) st) STAR H STAR
      STATE_REFS TYPE ptrs1 (TAKE (LENGTH ptrs1) st)` THEN
  SUBGOAL_THEN `(cf_REF rv v STAR G) (st2heap p (s:(FFI)state))` ASSUME_TAC THENL
   [EXPAND_TAC "G" THEN MON1AUX_HPROP_AC_TAC; ALL_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `l:num` SUBST_ALL_TAC o MATCH_MP REF_EXISTS_LOC) THEN
  MAP_EVERY EXISTS_TAC [`l:num`; `v:v`; `G:hprop`] THEN ASM_REWRITE_TAC[] THEN
  ASM_ARITH_TAC);;

let MON1AUX_STATE_REFS_LENGTH = prove
 (`!(A:A->v->bool) ptrs state H (s:heap).
     (STATE_REFS A ptrs state STAR H) s ==> LENGTH ptrs = LENGTH state`,
  MESON_TAC[STATE_REFS_LENGTH]);;

let UPDATE_STATE_REFS = prove
 (`!ptrs2 l ptrs1 x res (TYPE:A->v->bool) junk refs p (s:(FFI)state).
     TYPE x res ==>
     REFS_PRED_FRAME ro (STATE_REFS TYPE (APPEND (APPEND ptrs1 [Loc T l]) ptrs2),p)
       (refs,s)
       (ref_assign (LENGTH ptrs2) x refs,
        state_refs_fupd (combin_K (LUPDATE (Refv res) l (APPEND (state_refs s) junk))) s)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[REFS_PRED_FRAME_def] THEN SIMP[] THEN
  CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `F1:hprop` THEN REWRITE_TAC[STATE_REFS_DECOMPOSE] THEN
  DISCH_THEN(X_CHOOSE_THEN `refs1:(A)list` (X_CHOOSE_THEN `y:A`
    (X_CHOOSE_THEN `refs2:(A)list` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `LENGTH (ptrs1:v list) = LENGTH (refs1:(A)list)` ASSUME_TAC THENL
   [MATCH_MP_TAC MON1AUX_STATE_REFS_LENGTH THEN
    MAP_EVERY EXISTS_TAC [`TYPE:A->v->bool`;
      `STATE_REF (TYPE:A->v->bool) (Loc T l) y STAR STATE_REFS TYPE ptrs2 refs2 STAR F1`;
      `st2heap p (s:(FFI)state)`] THEN
    MON1AUX_HPROP_AC_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (ptrs2:v list) = LENGTH (refs2:(A)list)` ASSUME_TAC THENL
   [MATCH_MP_TAC MON1AUX_STATE_REFS_LENGTH THEN
    MAP_EVERY EXISTS_TAC [`TYPE:A->v->bool`;
      `STATE_REFS (TYPE:A->v->bool) ptrs1 refs1 STAR STATE_REF TYPE (Loc T l) y STAR F1`;
      `st2heap p (s:(FFI)state)`] THEN
    MON1AUX_HPROP_AC_TAC; ALL_TAC] THEN
  REWRITE_TAC[ref_assign_def; LENGTH_APPEND; LENGTH] THEN
  SUBGOAL_THEN `((LENGTH (refs1:(A)list) + SUC 0) + LENGTH (refs2:(A)list)) -
                LENGTH (ptrs2:v list) - 1 = LENGTH refs1` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[lupdate_append2] THEN
  REWRITE_TAC[GSYM STAR_ASSOC] THEN
  SIMP_TAC[ASSUME `LENGTH (ptrs1:v list) = LENGTH (refs1:(A)list)`;
           ASSUME `LENGTH (ptrs2:v list) = LENGTH (refs2:(A)list)`;
           STATE_REFS_DECOMPOSE_2] THEN
  SUBGOAL_THEN `?v0. (cf_REF (Loc T l) v0 STAR
      (STATE_REFS (TYPE:A->v->bool) ptrs1 refs1 STAR STATE_REFS TYPE ptrs2 refs2 STAR F1))
      (st2heap p (s:(FFI)state))` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(STATE_REFS (TYPE:A->v->bool) ptrs1 refs1 STAR STATE_REF TYPE (Loc T l) y STAR
       STATE_REFS TYPE ptrs2 refs2 STAR F1) (st2heap p (s:(FFI)state))` THEN
    REWRITE_TAC[STATE_REF_def; SEP_CLAUSES; SEP_EXISTS_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `v0:v`
      (STRIP_ASSUME_TAC o CONV_RULE MON1AUX_EXTRACT_PURE_FACTS_CONV)) THEN
    EXISTS_TAC `v0:v` THEN MON1AUX_HPROP_AC_TAC; ALL_TAC] THEN
  REWRITE_TAC[STATE_REF_def; SEP_CLAUSES; SEP_EXISTS_THM] THEN
  EXISTS_TAC `res:v` THEN CONV_TAC MON1AUX_EXTRACT_PURE_FACTS_CONV THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`res:v`; `junk:(v store_v)list`] o
    MATCH_MP MON1AUX_REF_update_frame) THEN
  DISCH_TAC THEN MON1AUX_HPROP_AC_TAC);;


let EvalM_Mref_assign = prove
 (`nsLookup (sem_env_v env) (Short rname) = SOME rv ==>
   r = LENGTH ptrs2 ==>
   ml_Eval env xexpr ((TYPE:A->v->bool) x) ==>
   EvalM ro env st (App Opassign [Var (Short rname); xexpr])
     (MONAD UNIT_TYPE (\x v. F) (Mref_assign (e:E) (StoreRef r) x))
     (STATE_REFS TYPE (APPEND (APPEND ptrs1 [rv]) ptrs2),
      (p:(FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)))`,
  REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `r:num`)) THEN
  REWRITE_TAC[EvalM_def; REFS_PRED_def] THEN
  X_GEN_TAC `s:(FFI)state` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MON1AUX_STATE_REFS_REF) THEN
  DISCH_THEN(X_CHOOSE_THEN `l:num` (X_CHOOSE_THEN `v0:v`
    (X_CHOOSE_THEN `G:hprop` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `rv:v`)) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:(FFI)state` o MATCH_MP MON1AUX_Eval_evaluate o
    check (MON1AUX_head_is "ml_Eval" o concl)) THEN
  DISCH_THEN(X_CHOOSE_THEN `xv:v` (X_CHOOSE_THEN `junk:(v store_v)list`
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `c1:num` o
      SPEC `state_clock (s:(FFI)state)`)))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[state_update_clock_id]) THEN
  FIRST_ASSUM(ASSUME_TAC o SPECL [`xv:v`; `junk:(v store_v)list`] o
    MATCH_MP MON1AUX_store_assign_REF) THEN
  SUBGOAL_THEN `LENGTH (ptrs2:v list) < LENGTH (st:(A)list)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`state_refs_fupd (combin_K (LUPDATE (Refv xv) l (APPEND (state_refs s) junk))) (s:(FFI)state)`;
    `Rval [Conv NONE []]:(v list,v)result`; `ref_assign (LENGTH (ptrs2:v list)) (x:A) st`;
    `c1:num`] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`state_clock_fupd (combin_K c1) (s:(FFI)state)`; `env:v sem_env`;
      `rname:mlstring`; `xexpr:exp`;
      `state_refs_fupd (combin_K (APPEND (state_refs s) junk)) (s:(FFI)state)`; `xv:v`; `l:num`;
      `LUPDATE (Refv xv) l (APPEND (state_refs (s:(FFI)state)) junk)`]
      MON1AUX_evaluate_Opassign) THEN
    SIMP[] THEN ASM_REWRITE_TAC[] THEN SIMP[];
    REWRITE_TAC[MON1AUX_MONAD_THM] THEN ASM_SIMP_TAC[ml_monadBase_Mref_assign_eq] THEN
    REWRITE_TAC[PAIR_EQ; injectivity "exc"; distinctness "exc";
      injectivity "result"; distinctness "result"; CONS_11; RIGHT_EXISTS_AND_THM;
      UNWIND_THM1; UNIT_TYPE_def] THEN MESON_TAC[];
    MATCH_MP_TAC(GEN_ALL UPDATE_STATE_REFS) THEN ASM_REWRITE_TAC[]]);;

(* Allocation of the initial store for dynamic references *)

let STATE_REFS_EXTEND = prove
 (`!H (s:(FFI)state) refs.
     (STATE_REFS (A:A->v->bool) ptrs refs STAR H)
       (st2heap (p:(FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)) s) ==>
     !x xv. A x xv ==>
       (STATE_REFS A (CONS (Loc T (LENGTH (state_refs s))) ptrs) (CONS x refs) STAR H)
         (st2heap p (state_refs_fupd (combin_K (APPEND (state_refs s) [Refv xv])) s))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[STATE_REFS_def] THEN
  SUBGOAL_THEN
   `(STATE_REF (A:A->v->bool) (Loc T (LENGTH (state_refs (s:(FFI)state)))) x STAR
     (STATE_REFS A ptrs refs STAR H))
       (st2heap p (state_refs_fupd (combin_K (APPEND (state_refs s) [Refv xv])) s))`
    MP_TAC THENL
   [MATCH_MP_TAC MON1AUX_STAR_I THEN
    MAP_EVERY EXISTS_TAC
     [`store2heap_aux (LENGTH (state_refs (s:(FFI)state))) [Refv (xv:v)]`;
      `st2heap p (s:(FFI)state)`] THEN
    ASM_SIMP_TAC[MON1AUX_STATE_REF_cell] THEN
    ONCE_REWRITE_TAC[SPLIT_SYM] THEN
    SUBGOAL_THEN `st2heap p (s:(FFI)state) =
                  st2heap p (state_refs_fupd (combin_K (state_refs s)) s)` SUBST1_TAC THENL
     [REWRITE_TAC[with_same_refs]; REWRITE_TAC[STATE_SPLIT_REFS]];
    DISCH_TAC THEN MON1AUX_HPROP_AC_TAC]);;


(* Resizable arrays *)

let ABS_NUM_EQ = prove
 (`num_of_int (abs (&n)) = n`,
  REWRITE_TAC[INT_ABS_NUM; NUM_OF_INT_OF_NUM]);;

let do_app_Opderef_REF = prove
 (`(cf_REF (Loc T loc) v STAR (H:REFS->hprop) refs)
     (st2heap (p:(FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)) (s:(FFI)state)) ==>
   !junk. do_app (APPEND (state_refs s) junk,state_ffi s) Opderef [Loc T loc] =
          SOME ((APPEND (state_refs s) junk,state_ffi s),Rval v)`,
  DISCH_TAC THEN X_GEN_TAC `junk:(v store_v)list` THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP (GEN_ALL store_lookup_REF_st2heap_junk)) THEN
  ASM_REWRITE_TAC[do_app_def] THEN CAKE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  CAKE_REWRITE_TAC[]);;

let MON1AUX_store_lookup_ARRAY_junk = prove
 (`!l av H p (s:(FFI)state) junk.
     (cf_ARRAY (Loc T l) av STAR H) (st2heap p s) ==>
     store_lookup l (APPEND (state_refs s) junk) = SOME (Varray av)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[cf_ARRAY_def; SEP_CLAUSES; SEP_EXISTS_THM; GSYM STAR_ASSOC; cf_HCOND_EXTRACT;
    injectivity "v"] THEN
  DISCH_THEN(X_CHOOSE_THEN `l':num` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  MATCH_MP_TAC(GEN_ALL store_lookup_CELL_st2heap) THEN
  MAP_EVERY EXISTS_TAC [`H:hprop`; `p:(FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)`] THEN
  ASM_REWRITE_TAC[]);;

let do_app_Alength_ARRAY = prove
 (`(cf_ARRAY rv v STAR H)
     (st2heap (p:(FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)) (s:(FFI)state)) ==>
   do_app (state_refs s,state_ffi s) Alength [rv] =
   SOME ((state_refs s,state_ffi s),Rval (Litv (IntLit (&(LENGTH v)))))`,
  DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `l:num` SUBST_ALL_TAC o MATCH_MP (GEN_ALL ARRAY_EXISTS_LOC)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP (GEN_ALL store_lookup_ARRAY_st2heap)) THEN
  ASM_REWRITE_TAC[do_app_def] THEN CAKE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  CAKE_REWRITE_TAC[]);;

let do_app_Asub_ARRAY = prove
 (`(cf_ARRAY rv v STAR H)
     (st2heap (p:(FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)) (s:(FFI)state)) ==>
   !junk. do_app (APPEND (state_refs s) junk,state_ffi s) Asub [rv; Litv (IntLit (&n))] =
     if n < LENGTH v then SOME ((APPEND (state_refs s) junk,state_ffi s),Rval (EL n v))
     else SOME ((APPEND (state_refs s) junk,state_ffi s),
                Rerr (Rraise (Conv (SOME (ExnStamp 3)) [])))`,
  DISCH_TAC THEN X_GEN_TAC `junk:(v store_v)list` THEN
  FIRST_ASSUM(X_CHOOSE_THEN `l:num` SUBST_ALL_TAC o MATCH_MP (GEN_ALL ARRAY_EXISTS_LOC)) THEN
  FIRST_ASSUM(ASSUME_TAC o SPEC `junk:(v store_v)list` o
    MATCH_MP MON1AUX_store_lookup_ARRAY_junk) THEN
  ASM_REWRITE_TAC[do_app_def] THEN CAKE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[INT_OF_NUM_LT; LT; I_THM; ABS_NUM_EQ; sub_exn_v_def; subscript_stamp_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_CASES_TAC `n < LENGTH (v:v list)` THEN ASM_REWRITE_TAC[GE; GSYM NOT_LT]);;

let MON1AUX_evaluate_App_Simple = prove
 (`!(s:(FFI)state) env op es s1 vs refs' ffi' r.
     evaluate s env (REVERSE es) = (s1,Rval vs) /\ getOpClass op = Simple /\
     do_app (state_refs s1,state_ffi s1) op (REVERSE vs) = SOME ((refs',ffi'),r) ==>
     evaluate s env [App op es] =
     (state_refs_fupd (combin_K refs') (state_ffi_fupd (combin_K ffi') s1),list_result r)`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [evaluate_def] THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  CAKE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[]);;

(* evaluation with an arbitrary final clock *)

let MON1AUX_ck_App_Simple = prove
 (`!(s:(FFI)state) env op es s1 vs refs' r.
     (!ck. ?ck1. evaluate (state_clock_fupd (combin_K ck1) s) env (REVERSE es) =
                 (state_clock_fupd (combin_K ck) s1,Rval vs)) /\
     getOpClass op = Simple /\
     do_app (state_refs s1,state_ffi s1) op (REVERSE vs) = SOME ((refs',state_ffi s1),r) ==>
     !ck. ?ck1. evaluate (state_clock_fupd (combin_K ck1) s) env [App op es] =
                (state_clock_fupd (combin_K ck) (state_refs_fupd (combin_K refs') s1),list_result r)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `ck1:num` o SPEC `ck:num`) THEN
  EXISTS_TAC `ck1:num` THEN
  MP_TAC(ISPECL [`state_clock_fupd (combin_K ck1) (s:(FFI)state)`; `env:v sem_env`; `op:op`;
    `es:exp list`; `state_clock_fupd (combin_K ck) (s1:(FFI)state)`; `vs:v list`;
    `refs':(v store_v)list`; `state_ffi (s1:(FFI)state)`; `r:(v,v)result`]
    MON1AUX_evaluate_App_Simple) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[state_INFO.ri_accfupds; K_THM]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  REWRITE_TAC[state_component_equality; state_INFO.ri_accfupds; K_THM]);;

let MON1AUX_ck_two = prove
 (`!(s:(FFI)state) env e1 e2 s1 v1 s2 v2.
     (!ck. ?ck1. evaluate (state_clock_fupd (combin_K ck1) s) env [e1] =
                 (state_clock_fupd (combin_K ck) s1,Rval [v1])) /\
     (!ck. ?ck1. evaluate (state_clock_fupd (combin_K ck1) s1) env [e2] =
                 (state_clock_fupd (combin_K ck) s2,Rval [v2])) ==>
     !ck. ?ck1. evaluate (state_clock_fupd (combin_K ck1) s) env [e1; e2] =
                (state_clock_fupd (combin_K ck) s2,Rval [v1; v2])`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `ck2:num` o SPEC `ck:num`) THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `ck1:num` o SPEC `ck2:num`) THEN
  EXISTS_TAC `ck1:num` THEN MATCH_MP_TAC MON1AUX_evaluate_two THEN
  EXISTS_TAC `state_clock_fupd (combin_K ck2) (s1:(FFI)state)` THEN ASM_REWRITE_TAC[]);;

let MON1AUX_ck_three = prove
 (`!(s:(FFI)state) env e1 e2 e3 s1 v1 s2 v2 s3 v3.
     (!ck. ?ck1. evaluate (state_clock_fupd (combin_K ck1) s) env [e1] =
                 (state_clock_fupd (combin_K ck) s1,Rval [v1])) /\
     (!ck. ?ck1. evaluate (state_clock_fupd (combin_K ck1) s1) env [e2] =
                 (state_clock_fupd (combin_K ck) s2,Rval [v2])) /\
     (!ck. ?ck1. evaluate (state_clock_fupd (combin_K ck1) s2) env [e3] =
                 (state_clock_fupd (combin_K ck) s3,Rval [v3])) ==>
     !ck. ?ck1. evaluate (state_clock_fupd (combin_K ck1) s) env [e1; e2; e3] =
                (state_clock_fupd (combin_K ck) s3,Rval [v1; v2; v3])`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(MP_TAC o MATCH_MP MON1AUX_ck_two) THEN DISCH_TAC THEN X_GEN_TAC `ck:num` THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `ck2:num` o SPEC `ck:num`) THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `ck1:num` o SPEC `ck2:num`) THEN
  EXISTS_TAC `ck1:num` THEN ONCE_REWRITE_TAC[evaluate_cons] THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  CAKE_REWRITE_TAC[] THEN REWRITE_TAC[APPEND]);;

let MON1AUX_ck_same = prove
 (`!(s:(FFI)state) env e r.
     (!ck. evaluate (state_clock_fupd (combin_K ck) s) env [e] = (state_clock_fupd (combin_K ck) s,r)) ==>
     !ck. ?ck1. evaluate (state_clock_fupd (combin_K ck1) s) env [e] = (state_clock_fupd (combin_K ck) s,r)`,
  MESON_TAC[]);;

let MON1AUX_ck_final = prove
 (`!(s:(FFI)state) env e refs' r.
     (!ck. ?ck1. evaluate (state_clock_fupd (combin_K ck1) s) env [e] =
                 (state_clock_fupd (combin_K ck) (state_refs_fupd (combin_K refs') s),r)) ==>
     ?ck1. evaluate (state_clock_fupd (combin_K ck1) s) env [e] = (state_refs_fupd (combin_K refs') s,r)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `state_clock (s:(FFI)state)`) THEN
  REWRITE_TAC[state_update_clock_id]);;

let MON1AUX_ck_Handle_Rval = prove
 (`!(s:(FFI)state) env e pes s1 vs.
     (!ck. ?ck1. evaluate (state_clock_fupd (combin_K ck1) s) env [e] =
                 (state_clock_fupd (combin_K ck) s1,Rval vs)) ==>
     !ck. ?ck1. evaluate (state_clock_fupd (combin_K ck1) s) env [Handle e pes] =
                (state_clock_fupd (combin_K ck) s1,Rval vs)`,
  MESON_TAC[MON1AUX_evaluate_Handle_Rval]);;

let MON1AUX_ck_Handle_Subscript = prove
 (`!(s:(FFI)state) env e rexp s1 s2 ev.
     ml_lookup_cons (Short (implode "Subscript")) env = SOME (0,ExnStamp 3) /\
     (!ck. ?ck1. evaluate (state_clock_fupd (combin_K ck1) s) env [e] =
                 (state_clock_fupd (combin_K ck) s1,Rerr (Rraise (Conv (SOME (ExnStamp 3)) [])))) /\
     (!ck. ?ck1. evaluate (state_clock_fupd (combin_K ck1) s1) env [rexp] =
                 (state_clock_fupd (combin_K ck) s2,Rval [ev])) ==>
     !ck. ?ck1. evaluate (state_clock_fupd (combin_K ck1) s) env
                  [Handle e [(Pcon (SOME (Short (implode "Subscript"))) [],Raise rexp)]] =
                (state_clock_fupd (combin_K ck) s2,Rerr (Rraise ev))`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `ck2:num` o SPEC `ck:num`) THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `ck1:num` o SPEC `ck2:num`) THEN
  EXISTS_TAC `ck1:num` THEN
  MP_TAC(ISPECL [`state_clock_fupd (combin_K ck1) (s:(FFI)state)`; `env:v sem_env`; `e:exp`;
    `Short (implode "Subscript"):(mlstring,mlstring)id`; `[]:mlstring list`; `Raise rexp`;
    `state_clock_fupd (combin_K ck2) (s1:(FFI)state)`; `3`; `3`; `[]:v list`; `0`]
    MON1AUX_evaluate_Handle_Pcon) THEN
  ASM_REWRITE_TAC[LENGTH; ALL_DISTINCT; MAP; ml_monad_translator_write_list_def] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[evaluate_def] THEN ASM_REWRITE_TAC[] THEN
  CAKE_REWRITE_TAC[] THEN REWRITE_TAC[HD]);;

let MON1AUX_do_app_Alength = prove
 (`!refs (ffi:(FFI)ffi_state) b l av.
     store_lookup l refs = SOME (Varray av) ==>
     do_app (refs,ffi) Alength [Loc b l] =
     SOME ((refs,ffi),Rval (Litv (IntLit (&(LENGTH av)))))`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[do_app_def] THEN CAKE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[]);;

let MON1AUX_do_app_Asub = prove
 (`!refs (ffi:(FFI)ffi_state) b l av n.
     store_lookup l refs = SOME (Varray av) ==>
     do_app (refs,ffi) Asub [Loc b l; Litv (IntLit (&n))] =
     SOME ((refs,ffi),if n < LENGTH av then Rval (EL n av)
                      else Rerr (Rraise (Conv (SOME (ExnStamp 3)) [])))`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[do_app_def] THEN CAKE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[INT_OF_NUM_LT; LT; I_THM; ABS_NUM_EQ; sub_exn_v_def; subscript_stamp_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_CASES_TAC `n < LENGTH (av:v list)` THEN ASM_REWRITE_TAC[GE; GSYM NOT_LT]);;

let MON1AUX_do_app_Aupdate = prove
 (`!refs (ffi:(FFI)ffi_state) b l av n xv.
     store_lookup l refs = SOME (Varray av) ==>
     do_app (refs,ffi) Aupdate [Loc b l; Litv (IntLit (&n)); xv] =
     if n < LENGTH av
     then SOME ((LUPDATE (Varray (LUPDATE xv n av)) l refs,ffi),Rval (Conv NONE []))
     else SOME ((refs,ffi),Rerr (Rraise (Conv (SOME (ExnStamp 3)) [])))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `l < LENGTH (refs:(v store_v)list) /\ EL l refs = Varray av` STRIP_ASSUME_TAC
  THENL
   [UNDISCH_TAC `store_lookup l (refs:(v store_v)list) = SOME (Varray av)` THEN
    REWRITE_TAC[store_lookup_def] THEN COND_CASES_TAC THEN
    REWRITE_TAC[distinctness "option"; injectivity "option"] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[do_app_def] THEN CAKE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[INT_OF_NUM_LT; LT; I_THM; ABS_NUM_EQ; sub_exn_v_def; subscript_stamp_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_CASES_TAC `n < LENGTH (av:v list)` THEN ASM_REWRITE_TAC[GE; GSYM NOT_LT] THEN
  ASM_REWRITE_TAC[store_assign_def; store_v_same_type_def] THEN CAKE_REWRITE_TAC[]);;

let MON1AUX_do_app_Aalloc = prove
 (`!refs (ffi:(FFI)ffi_state) n xv.
     do_app (refs,ffi) Aalloc [Litv (IntLit (&n)); xv] =
     SOME ((APPEND refs [Varray (REPLICATE n xv)],ffi),Rval (Loc T (LENGTH refs)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[do_app_def] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[INT_OF_NUM_LT; LT; I_THM; ABS_NUM_EQ; store_alloc_def] THEN
  CAKE_REWRITE_TAC[]);;

let MON1AUX_getOpClass_Simple = prove
 (`getOpClass Alength = Simple /\ getOpClass Asub = Simple /\
   getOpClass Aupdate = Simple /\ getOpClass Aalloc = Simple /\
   getOpClass Opassign = Simple /\ getOpClass Opderef = Simple`,
  REWRITE_TAC[getOpClass_def] THEN CAKE_REWRITE_TAC[]);;

let MON1AUX_ck_Alength = prove
 (`!(s:(FFI)state) env X l1 av.
     (!ck. evaluate (state_clock_fupd (combin_K ck) s) env [X] =
           (state_clock_fupd (combin_K ck) s,Rval [Loc T l1])) /\
     store_lookup l1 (state_refs s) = SOME (Varray av) ==>
     !ck. ?ck1. evaluate (state_clock_fupd (combin_K ck1) s) env [App Alength [X]] =
                (state_clock_fupd (combin_K ck) s,Rval [Litv (IntLit (&(LENGTH av)))])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:(FFI)state`; `env:v sem_env`; `Alength`; `[X:exp]`; `s:(FFI)state`;
    `[Loc T l1]`; `state_refs (s:(FFI)state)`;
    `Rval (Litv (IntLit (&(LENGTH (av:v list))))):(v,v)result`] MON1AUX_ck_App_Simple) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[REVERSE; APPEND; MON1AUX_getOpClass_Simple] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MON1AUX_ck_same THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MON1AUX_do_app_Alength THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[with_same_refs; list_result_def] THEN MESON_TAC[]]);;

let MON1AUX_ck_Asub = prove
 (`!(s:(FFI)state) env X nexp n s1 l1 av.
     (!ck. ?ck1. evaluate (state_clock_fupd (combin_K ck1) s) env [nexp] =
                 (state_clock_fupd (combin_K ck) s1,Rval [Litv (IntLit (&n))])) /\
     (!ck. evaluate (state_clock_fupd (combin_K ck) s1) env [X] =
           (state_clock_fupd (combin_K ck) s1,Rval [Loc T l1])) /\
     store_lookup l1 (state_refs s1) = SOME (Varray av) ==>
     !ck. ?ck1. evaluate (state_clock_fupd (combin_K ck1) s) env [App Asub [X; nexp]] =
       (state_clock_fupd (combin_K ck) s1,
        if n < LENGTH av then Rval [EL n av]
        else Rerr (Rraise (Conv (SOME (ExnStamp 3)) [])))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:(FFI)state`; `env:v sem_env`; `Asub`; `[X; nexp]:exp list`;
    `s1:(FFI)state`; `[Litv (IntLit (&n)); Loc T l1]`; `state_refs (s1:(FFI)state)`;
    `if n < LENGTH (av:v list) then Rval (EL n av):(v,v)result
     else Rerr (Rraise (Conv (SOME (ExnStamp 3)) []))`] MON1AUX_ck_App_Simple) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[REVERSE; APPEND; MON1AUX_getOpClass_Simple] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MON1AUX_ck_two THEN EXISTS_TAC `s1:(FFI)state` THEN
      CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      MATCH_MP_TAC MON1AUX_ck_same THEN FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC MON1AUX_do_app_Asub THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[with_same_refs] THEN COND_CASES_TAC THEN
    REWRITE_TAC[list_result_def] THEN MESON_TAC[]]);;

let MON1AUX_ck_Aupdate = prove
 (`!(s:(FFI)state) env X nexp xexp n xv s1 s2 l1 av.
     (!ck. ?ck1. evaluate (state_clock_fupd (combin_K ck1) s) env [xexp] =
                 (state_clock_fupd (combin_K ck) s1,Rval [xv])) /\
     (!ck. ?ck1. evaluate (state_clock_fupd (combin_K ck1) s1) env [nexp] =
                 (state_clock_fupd (combin_K ck) s2,Rval [Litv (IntLit (&n))])) /\
     (!ck. evaluate (state_clock_fupd (combin_K ck) s2) env [X] =
           (state_clock_fupd (combin_K ck) s2,Rval [Loc T l1])) /\
     store_lookup l1 (state_refs s2) = SOME (Varray av) ==>
     !ck. ?ck1. evaluate (state_clock_fupd (combin_K ck1) s) env [App Aupdate [X; nexp; xexp]] =
       if n < LENGTH av
       then (state_clock_fupd (combin_K ck)
               (state_refs_fupd (combin_K (LUPDATE (Varray (LUPDATE xv n av)) l1 (state_refs s2))) s2),
             Rval [Conv NONE []])
       else (state_clock_fupd (combin_K ck) s2,Rerr (Rraise (Conv (SOME (ExnStamp 3)) [])))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!ck. ?ck1. evaluate (state_clock_fupd (combin_K ck1) (s:(FFI)state)) env (REVERSE [X; nexp; xexp]) =
               (state_clock_fupd (combin_K ck) s2,Rval [xv; Litv (IntLit (&n)); Loc T l1])`
    ASSUME_TAC THENL
   [REWRITE_TAC[REVERSE; APPEND] THEN MATCH_MP_TAC MON1AUX_ck_three THEN
    MAP_EVERY EXISTS_TAC [`s1:(FFI)state`; `s2:(FFI)state`] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    MATCH_MP_TAC MON1AUX_ck_same THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `n < LENGTH (av:v list)` THEN ASM_REWRITE_TAC[] THENL
   [MP_TAC(ISPECL [`s:(FFI)state`; `env:v sem_env`; `Aupdate`; `[X; nexp; xexp]:exp list`;
      `s2:(FFI)state`; `[xv; Litv (IntLit (&n)); Loc T l1]`;
      `LUPDATE (Varray (LUPDATE xv n av)) l1 (state_refs (s2:(FFI)state))`;
      `Rval (Conv NONE []):(v,v)result`] MON1AUX_ck_App_Simple);
    MP_TAC(ISPECL [`s:(FFI)state`; `env:v sem_env`; `Aupdate`; `[X; nexp; xexp]:exp list`;
      `s2:(FFI)state`; `[xv; Litv (IntLit (&n)); Loc T l1]`;
      `state_refs (s2:(FFI)state)`;
      `Rerr (Rraise (Conv (SOME (ExnStamp 3)) [])):(v,v)result`] MON1AUX_ck_App_Simple)] THEN
  (ANTS_TAC THENL
    [ASM_REWRITE_TAC[MON1AUX_getOpClass_Simple] THEN REWRITE_TAC[REVERSE; APPEND] THEN
     ASM_SIMP_TAC[MON1AUX_do_app_Aupdate];
     REWRITE_TAC[list_result_def; with_same_refs] THEN MESON_TAC[]]));;

let MON1AUX_refs_fupd_fupd = prove
 (`!a b (s:(FFI)state). state_refs_fupd (combin_K a) (state_refs_fupd (combin_K b) s) = state_refs_fupd (combin_K a) s`,
  REWRITE_TAC[state_component_equality; state_INFO.ri_accfupds; K_THM]);;

let MON1AUX_ck_Alloc_assign = prove
 (`!(s:(FFI)state) env vname nexp xexp n xv s1 s2 l0 v0.
     (!ck. ?ck1. evaluate (state_clock_fupd (combin_K ck1) s) env [xexp] =
                 (state_clock_fupd (combin_K ck) s1,Rval [xv])) /\
     (!ck. ?ck1. evaluate (state_clock_fupd (combin_K ck1) s1) env [nexp] =
                 (state_clock_fupd (combin_K ck) s2,Rval [Litv (IntLit (&n))])) /\
     nsLookup (sem_env_v env) (Short vname) = SOME (Loc T l0) /\
     store_lookup l0 (state_refs s2) = SOME (Refv v0) ==>
     !ck. ?ck1. evaluate (state_clock_fupd (combin_K ck1) s) env
                  [App Opassign [Var (Short vname); App Aalloc [nexp; xexp]]] =
       (state_clock_fupd (combin_K ck)
          (state_refs_fupd (combin_K (LUPDATE (Refv (Loc T (LENGTH (state_refs s2)))) l0
             (APPEND (state_refs s2) [Varray (REPLICATE n xv)]))) s2),
        Rval [Conv NONE []])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `l0 < LENGTH (state_refs (s2:(FFI)state)) /\ EL l0 (state_refs s2) = Refv v0`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `store_lookup l0 (state_refs (s2:(FFI)state)) = SOME (Refv v0)` THEN
    REWRITE_TAC[store_lookup_def] THEN COND_CASES_TAC THEN
    REWRITE_TAC[distinctness "option"; injectivity "option"] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!ck. ?ck1. evaluate (state_clock_fupd (combin_K ck1) (s:(FFI)state)) env [App Aalloc [nexp; xexp]] =
      (state_clock_fupd (combin_K ck)
         (state_refs_fupd (combin_K (APPEND (state_refs s2) [Varray (REPLICATE n xv)])) s2),
       Rval [Loc T (LENGTH (state_refs (s2:(FFI)state)))])` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`s:(FFI)state`; `env:v sem_env`; `Aalloc`; `[nexp; xexp]:exp list`;
      `s2:(FFI)state`; `[xv; Litv (IntLit (&n))]`;
      `APPEND (state_refs (s2:(FFI)state)) [Varray (REPLICATE n xv)]`;
      `Rval (Loc T (LENGTH (state_refs (s2:(FFI)state)))):(v,v)result`]
      MON1AUX_ck_App_Simple) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[REVERSE; APPEND; MON1AUX_getOpClass_Simple; MON1AUX_do_app_Aalloc] THEN
      MATCH_MP_TAC MON1AUX_ck_two THEN EXISTS_TAC `s1:(FFI)state` THEN
      CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[list_result_def] THEN MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!ck. ?ck1. evaluate (state_clock_fupd (combin_K ck1) (s:(FFI)state)) env
        (REVERSE [Var (Short vname); App Aalloc [nexp; xexp]]) =
      (state_clock_fupd (combin_K ck)
         (state_refs_fupd (combin_K (APPEND (state_refs s2) [Varray (REPLICATE n xv)])) s2),
       Rval [Loc T (LENGTH (state_refs (s2:(FFI)state))); Loc T l0])` ASSUME_TAC THENL
   [REWRITE_TAC[REVERSE; APPEND] THEN MATCH_MP_TAC MON1AUX_ck_two THEN
    EXISTS_TAC `state_refs_fupd (combin_K (APPEND (state_refs s2) [Varray (REPLICATE n xv)]))
                  (s2:(FFI)state)` THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    MATCH_MP_TAC MON1AUX_ck_same THEN GEN_TAC THEN MATCH_MP_TAC MON1AUX_evaluate_Var_Short THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:(FFI)state`; `env:v sem_env`; `Opassign`;
    `[Var (Short vname); App Aalloc [nexp; xexp]]`;
    `state_refs_fupd (combin_K (APPEND (state_refs s2) [Varray (REPLICATE n xv)])) (s2:(FFI)state)`;
    `[Loc T (LENGTH (state_refs (s2:(FFI)state))); Loc T l0]`;
    `LUPDATE (Refv (Loc T (LENGTH (state_refs (s2:(FFI)state))))) l0
       (APPEND (state_refs s2) [Varray (REPLICATE n xv)])`;
    `Rval (Conv NONE []):(v,v)result`] MON1AUX_ck_App_Simple) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    REWRITE_TAC[MON1AUX_getOpClass_Simple; REVERSE; APPEND] THEN
    MATCH_MP_TAC MON1AUX_do_app_Opassign THEN
    REWRITE_TAC[state_INFO.ri_accfupds; K_THM; store_assign_def] THEN
    ASM_REWRITE_TAC[LENGTH_APPEND; EL_APPEND; ARITH_RULE `a < b ==> a < b + c:num`] THEN
    ASM_SIMP_TAC[ARITH_RULE `a < b ==> a < b + c:num`] THEN
    REWRITE_TAC[store_v_same_type_def] THEN CAKE_REWRITE_TAC[];
    REWRITE_TAC[list_result_def; MON1AUX_refs_fupd_fupd] THEN MESON_TAC[]]);;

let MON1AUX_RARRAY_open = prove
 (`!(TYPE:A->v->bool) loc l G p (s:(FFI)state).
     (RARRAY_REL TYPE loc l STAR G) (st2heap p s) ==>
     ?l0 l1 av. loc = Loc T l0 /\ ALL2 TYPE l av /\
       (cf_REF (Loc T l0) (Loc T l1) STAR cf_ARRAY (Loc T l1) av STAR G) (st2heap p s)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[RARRAY_REL_def; RARRAY_def; SEP_CLAUSES; SEP_EXISTS_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `av:v list` (X_CHOOSE_THEN `arv:v`
    (STRIP_ASSUME_TAC o CONV_RULE MON1AUX_EXTRACT_PURE_FACTS_CONV))) THEN
  SUBGOAL_THEN `?l0. loc = Loc T l0` (X_CHOOSE_THEN `l0:num` SUBST_ALL_TAC) THENL
   [MATCH_MP_TAC(GEN_ALL REF_EXISTS_LOC) THEN
    MAP_EVERY EXISTS_TAC [`arv:v`; `cf_ARRAY arv av STAR G`; `st2heap p (s:(FFI)state)`] THEN
    MON1AUX_HPROP_AC_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `?l1. arv = Loc T l1` (X_CHOOSE_THEN `l1:num` SUBST_ALL_TAC) THENL
   [MATCH_MP_TAC(GEN_ALL ARRAY_EXISTS_LOC) THEN
    MAP_EVERY EXISTS_TAC [`av:v list`; `cf_REF (Loc T l0) arv STAR G`;
      `st2heap p (s:(FFI)state)`] THEN
    MON1AUX_HPROP_AC_TAC; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`l0:num`; `l1:num`; `av:v list`] THEN ASM_REWRITE_TAC[] THEN
  MON1AUX_HPROP_AC_TAC);;

let MON1AUX_ARRAY_open = prove
 (`!(TYPE:A->v->bool) loc l G p (s:(FFI)state).
     (ARRAY_REL TYPE loc l STAR G) (st2heap p s) ==>
     ?l1 av. loc = Loc T l1 /\ ALL2 TYPE l av /\
       (cf_ARRAY (Loc T l1) av STAR G) (st2heap p s)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ARRAY_REL_def; SEP_CLAUSES; SEP_EXISTS_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `av:v list`
    (STRIP_ASSUME_TAC o CONV_RULE MON1AUX_EXTRACT_PURE_FACTS_CONV)) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `l1:num` SUBST_ALL_TAC o MATCH_MP (GEN_ALL ARRAY_EXISTS_LOC)) THEN
  MAP_EVERY EXISTS_TAC [`l1:num`; `av:v list`] THEN ASM_REWRITE_TAC[]);;

let MON1AUX_RARRAY_lookups = prove
 (`!l0 l1 av G p (s:(FFI)state) junk.
     (cf_REF (Loc T l0) (Loc T l1) STAR cf_ARRAY (Loc T l1) av STAR G) (st2heap p s) ==>
     store_lookup l0 (APPEND (state_refs s) junk) = SOME (Refv (Loc T l1)) /\
     store_lookup l1 (APPEND (state_refs s) junk) = SOME (Varray av)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC(GEN_ALL store_lookup_REF_st2heap_junk) THEN
    MAP_EVERY EXISTS_TAC [`cf_ARRAY (Loc T l1) av STAR G`;
      `p:(FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)`] THEN
    MON1AUX_HPROP_AC_TAC;
    MATCH_MP_TAC MON1AUX_store_lookup_ARRAY_junk THEN
    MAP_EVERY EXISTS_TAC [`cf_REF (Loc T l0) (Loc T l1) STAR G`;
      `p:(FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)`] THEN
    MON1AUX_HPROP_AC_TAC]);;

let MON1AUX_ARRAY_IN_LENGTH = prove
 (`!l av H p (s:(FFI)state).
     (cf_ARRAY (Loc T l) av STAR H) (st2heap p s) ==> l < LENGTH (state_refs s)`,
  MESON_TAC[st2heap_ARRAY_MEM; store2heap_IN_LENGTH]);;

let MON1AUX_ARRAY_update_frame = prove
 (`!l av av' G p (s:(FFI)state) junk.
     (cf_ARRAY (Loc T l) av STAR G) (st2heap p s) ==>
     (cf_ARRAY (Loc T l) av' STAR G STAR cf_GC)
       (st2heap p (state_refs_fupd (combin_K (LUPDATE (Varray av') l (APPEND (state_refs s) junk))) s))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MON1AUX_ARRAY_IN_LENGTH) THEN
  ASM_SIMP_TAC[LUPDATE_APPEND1] THEN MATCH_MP_TAC STATE_APPEND_JUNK THEN
  MATCH_MP_TAC(GEN_ALL STATE_UPDATE_HPROP_ARRAY) THEN EXISTS_TAC `av:v list` THEN
  ASM_REWRITE_TAC[]);;

let HPROP_TO_GC_R = prove
 (`(A STAR B) (s:heap) ==> (A STAR cf_GC) s`,
  REWRITE_TAC[STAR_def] THEN MESON_TAC[SAT_GC]);;

let HPROP_TO_GC_L = prove
 (`(A STAR B) (s:heap) ==> (cf_GC STAR B) s`,
  REWRITE_TAC[STAR_def] THEN MESON_TAC[SAT_GC]);;

let MON1AUX_store2heap_ARRAY_SAT = prove
 (`!l av. cf_ARRAY (Loc T l) av (store2heap_aux l [Varray av])`,
  REWRITE_TAC[store2heap_aux_def; ARRAY_HPROP_SAT_EQ]);;

(* the array rules, for any expression X that evaluates to the array      *)
(* location without changing the state                                     *)

let MON1AUX_EvalM_Marray_length_gen = prove
 (`!ro env X (TYPE:A->v->bool) (EXC_TYPE:E->v->bool) (get_arr:REFS->A list) st
    (H:(REFS->hprop)#((FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)))
    (s:(FFI)state) l1 av.
     ALL2 TYPE (get_arr st) av /\
     (!junk. store_lookup l1 (APPEND (state_refs s) junk) = SOME (Varray av)) /\
     (!junk ck. evaluate (state_clock_fupd (combin_K ck) (state_refs_fupd (combin_K (APPEND (state_refs s) junk)) s))
                  env [X] =
                (state_clock_fupd (combin_K ck) (state_refs_fupd (combin_K (APPEND (state_refs s) junk)) s),
                 Rval [Loc T l1])) ==>
     ?s2 res st2 ck.
       evaluate (state_clock_fupd (combin_K ck) s) env [App Alength [X]] = (s2,res) /\
       MONAD ml_NUM EXC_TYPE (Marray_length get_arr) st (st2,res) /\
       REFS_PRED_FRAME ro H (st,s) (st2,s2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:(FFI)state`; `env:v sem_env`; `X:exp`; `l1:num`; `av:v list`]
    MON1AUX_ck_Alength) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [GEN_TAC THEN FIRST_ASSUM(fun th -> ACCEPT_TAC(REWRITE_RULE[APPEND_NIL; with_same_refs]
        (SPECL [`[]:(v store_v)list`; `ck:num`] th)));
      FIRST_ASSUM(fun th -> ACCEPT_TAC(REWRITE_RULE[APPEND_NIL]
        (SPEC `[]:(v store_v)list` th)))];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `ck1:num` o REWRITE_RULE[s_with_same_clock] o
    SPEC `state_clock (s:(FFI)state)`) THEN
  SUBGOAL_THEN `LENGTH ((get_arr:REFS->A list) st) = LENGTH (av:v list)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LIST_REL_LENGTH]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`s:(FFI)state`;
    `Rval [Litv (IntLit (&(LENGTH (av:v list))))]:(v list,v)result`; `st:REFS`; `ck1:num`] THEN
  ASM_REWRITE_TAC[REFS_PRED_FRAME_same] THEN
  REWRITE_TAC[MON1AUX_MONAD_THM; ml_monadBase_Marray_length_def; PAIR_EQ;
    injectivity "exc"; distinctness "exc"; injectivity "result"; distinctness "result";
    CONS_11; RIGHT_EXISTS_AND_THM; UNWIND_THM1; ml_NUM_def; ml_INT_def] THEN
  ASM_REWRITE_TAC[]);;

let MON1AUX_EvalM_Marray_sub_gen = prove
 (`!ro env X nexp n (TYPE:A->v->bool) (EXC_TYPE:E->v->bool) (get_arr:REFS->A list) e st
    (H:(REFS->hprop)#((FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)))
    (s:(FFI)state) l1 av.
     EXC_TYPE e (Conv (SOME (ExnStamp 3)) []) /\
     ml_Eval env nexp (ml_NUM n) /\ ALL2 TYPE (get_arr st) av /\
     (!junk. store_lookup l1 (APPEND (state_refs s) junk) = SOME (Varray av)) /\
     (!junk ck. evaluate (state_clock_fupd (combin_K ck) (state_refs_fupd (combin_K (APPEND (state_refs s) junk)) s))
                  env [X] =
                (state_clock_fupd (combin_K ck) (state_refs_fupd (combin_K (APPEND (state_refs s) junk)) s),
                 Rval [Loc T l1])) ==>
     ?s2 res st2 ck.
       evaluate (state_clock_fupd (combin_K ck) s) env [App Asub [X; nexp]] = (s2,res) /\
       MONAD TYPE EXC_TYPE (Marray_sub get_arr e n) st (st2,res) /\
       REFS_PRED_FRAME ro H (st,s) (st2,s2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:(FFI)state` o MATCH_MP MON1AUX_Eval_evaluate o
    check (MON1AUX_head_is "ml_Eval" o concl)) THEN
  REWRITE_TAC[ml_NUM_def; ml_INT_def] THEN
  DISCH_THEN(X_CHOOSE_THEN `nv:v` (X_CHOOSE_THEN `junk:(v store_v)list` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `nv:v`)) THEN
  MP_TAC(ISPECL [`s:(FFI)state`; `env:v sem_env`; `X:exp`; `nexp:exp`; `n:num`;
    `state_refs_fupd (combin_K (APPEND (state_refs s) junk)) (s:(FFI)state)`; `l1:num`; `av:v list`]
    MON1AUX_ck_Asub) THEN
  ASM_REWRITE_TAC[state_INFO.ri_accfupds; K_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC `ck1:num` o REWRITE_RULE[state_update_clock_id] o
    SPEC `state_clock (s:(FFI)state)`) THEN
  SUBGOAL_THEN `LENGTH ((get_arr:REFS->A list) st) = LENGTH (av:v list)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LIST_REL_LENGTH]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`state_refs_fupd (combin_K (APPEND (state_refs s) junk)) (s:(FFI)state)`;
    `if n < LENGTH (av:v list) then Rval [EL n av]:(v list,v)result
     else Rerr (Rraise (Conv (SOME (ExnStamp 3)) []))`; `st:REFS`; `ck1:num`] THEN
  ASM_REWRITE_TAC[REFS_PRED_FRAME_append] THEN
  REWRITE_TAC[MON1AUX_MONAD_THM; ml_monadBase_Marray_sub_def] THEN COND_CASES_TAC THENL
   [SUBGOAL_THEN `Msub (e:E) n ((get_arr:REFS->A list) st) = M_success (EL n (get_arr st))`
      SUBST1_TAC THENL
     [MATCH_MP_TAC ml_monadBase_Msub_eq THEN ASM_REWRITE_TAC[]; ALL_TAC];
    SUBGOAL_THEN `Msub (e:E) n ((get_arr:REFS->A list) st) = M_failure e` SUBST1_TAC THENL
     [MATCH_MP_TAC ml_monadBase_Msub_exn_eq THEN ASM_REWRITE_TAC[GE] THEN ASM_ARITH_TAC;
      ALL_TAC]] THEN
  REWRITE_TAC[PAIR_EQ; injectivity "exc"; distinctness "exc"; injectivity "result";
    distinctness "result"; CONS_11; RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[LIST_REL_EL_EQN]);;

let MON1AUX_EvalM_Marray_sub_handle_gen = prove
 (`!ro env X nexp rexp n (TYPE:A->v->bool) (EXC_TYPE:E->v->bool) (get_arr:REFS->A list) e st
    (H:(REFS->hprop)#((FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)))
    (s:(FFI)state) l1 av.
     ml_lookup_cons (Short (implode "Subscript")) env = SOME (0,ExnStamp 3) /\
     ml_Eval env nexp (ml_NUM n) /\ ml_Eval env rexp (EXC_TYPE e) /\
     ALL2 TYPE (get_arr st) av /\
     (!junk. store_lookup l1 (APPEND (state_refs s) junk) = SOME (Varray av)) /\
     (!junk ck. evaluate (state_clock_fupd (combin_K ck) (state_refs_fupd (combin_K (APPEND (state_refs s) junk)) s))
                  env [X] =
                (state_clock_fupd (combin_K ck) (state_refs_fupd (combin_K (APPEND (state_refs s) junk)) s),
                 Rval [Loc T l1])) ==>
     ?s2 res st2 ck.
       evaluate (state_clock_fupd (combin_K ck) s) env
         [Handle (App Asub [X; nexp])
            [(Pcon (SOME (Short (implode "Subscript"))) [],Raise rexp)]] = (s2,res) /\
       MONAD TYPE EXC_TYPE (Marray_sub get_arr e n) st (st2,res) /\
       REFS_PRED_FRAME ro H (st,s) (st2,s2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:(FFI)state` o MATCH_MP MON1AUX_Eval_evaluate o
    check (fun th -> MON1AUX_head_is "ml_Eval" (concl th) && free_in `nexp:exp` (concl th))) THEN
  REWRITE_TAC[ml_NUM_def; ml_INT_def] THEN
  DISCH_THEN(X_CHOOSE_THEN `nv:v` (X_CHOOSE_THEN `junk:(v store_v)list` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `nv:v`)) THEN
  SUBGOAL_THEN `LENGTH ((get_arr:REFS->A list) st) = LENGTH (av:v list)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LIST_REL_LENGTH]; ALL_TAC] THEN
  ASM_CASES_TAC `n < LENGTH (av:v list)` THEN
  MP_TAC(ISPECL [`s:(FFI)state`; `env:v sem_env`; `X:exp`; `nexp:exp`; `n:num`;
    `state_refs_fupd (combin_K (APPEND (state_refs s) junk)) (s:(FFI)state)`; `l1:num`; `av:v list`]
    MON1AUX_ck_Asub) THEN
  ASM_REWRITE_TAC[state_INFO.ri_accfupds; K_THM] THEN DISCH_TAC THENL
   [SUBGOAL_THEN
     `?ck1. evaluate (state_clock_fupd (combin_K ck1) (s:(FFI)state)) env
         [Handle (App Asub [X; nexp])
            [(Pcon (SOME (Short (implode "Subscript"))) [],Raise rexp)]] =
       (state_refs_fupd (combin_K (APPEND (state_refs s) junk)) s,Rval [EL n (av:v list)])`
      (X_CHOOSE_TAC `ck1:num`) THENL
     [MATCH_MP_TAC MON1AUX_ck_final THEN MATCH_MP_TAC MON1AUX_ck_Handle_Rval THEN
      FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC
     [`state_refs_fupd (combin_K (APPEND (state_refs s) junk)) (s:(FFI)state)`;
      `Rval [EL n (av:v list)]:(v list,v)result`; `st:REFS`; `ck1:num`] THEN
    ASM_REWRITE_TAC[REFS_PRED_FRAME_append] THEN
    REWRITE_TAC[MON1AUX_MONAD_THM; ml_monadBase_Marray_sub_def] THEN
    SUBGOAL_THEN `Msub (e:E) n ((get_arr:REFS->A list) st) = M_success (EL n (get_arr st))`
      SUBST1_TAC THENL
     [MATCH_MP_TAC ml_monadBase_Msub_eq THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[PAIR_EQ; injectivity "exc"; distinctness "exc"; injectivity "result";
      distinctness "result"; CONS_11; RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
    ASM_MESON_TAC[LIST_REL_EL_EQN];
    FIRST_X_ASSUM(MP_TAC o
      SPEC `state_refs_fupd (combin_K (APPEND (state_refs s) junk)) (s:(FFI)state)` o
      MATCH_MP MON1AUX_Eval_evaluate o
      check (fun th -> MON1AUX_head_is "ml_Eval" (concl th) && free_in `rexp:exp` (concl th))) THEN
    DISCH_THEN(X_CHOOSE_THEN `ev:v` (X_CHOOSE_THEN `junk2:(v store_v)list`
      STRIP_ASSUME_TAC)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[state_INFO.ri_accfupds; K_THM; MON1AUX_refs_fupd_fupd;
      GSYM APPEND_ASSOC]) THEN
    SUBGOAL_THEN
     `?ck1. evaluate (state_clock_fupd (combin_K ck1) (s:(FFI)state)) env
         [Handle (App Asub [X; nexp])
            [(Pcon (SOME (Short (implode "Subscript"))) [],Raise rexp)]] =
       (state_refs_fupd (combin_K (APPEND (state_refs s) (APPEND junk junk2))) s,Rerr (Rraise ev))`
      (X_CHOOSE_TAC `ck1:num`) THENL
     [MATCH_MP_TAC MON1AUX_ck_final THEN MATCH_MP_TAC MON1AUX_ck_Handle_Subscript THEN
      EXISTS_TAC `state_refs_fupd (combin_K (APPEND (state_refs s) junk)) (s:(FFI)state)` THEN
      REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC
     [`state_refs_fupd (combin_K (APPEND (state_refs s) (APPEND junk junk2))) (s:(FFI)state)`;
      `Rerr (Rraise ev):(v list,v)result`; `st:REFS`; `ck1:num`] THEN
    ASM_REWRITE_TAC[REFS_PRED_FRAME_append] THEN
    REWRITE_TAC[MON1AUX_MONAD_THM; ml_monadBase_Marray_sub_def] THEN
    SUBGOAL_THEN `Msub (e:E) n ((get_arr:REFS->A list) st) = M_failure e` SUBST1_TAC THENL
     [MATCH_MP_TAC ml_monadBase_Msub_exn_eq THEN ASM_REWRITE_TAC[GE] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[PAIR_EQ; injectivity "exc"; distinctness "exc"; injectivity "result";
      distinctness "result"; injectivity "error_result"; CONS_11; RIGHT_EXISTS_AND_THM;
      UNWIND_THM1] THEN
    ASM_REWRITE_TAC[]]);;

let MON1AUX_EvalM_Marray_update_gen = prove
 (`!ro env X nexp xexp n x (TYPE:A->v->bool) (EXC_TYPE:E->v->bool) (get_arr:REFS->A list)
    set_arr e st
    (H:(REFS->hprop)#((FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)))
    (s:(FFI)state) l1 av.
     EXC_TYPE e (Conv (SOME (ExnStamp 3)) []) /\
     ml_Eval env nexp (ml_NUM n) /\ ml_Eval env xexp (TYPE x) /\
     ALL2 TYPE (get_arr st) av /\
     (!junk. store_lookup l1 (APPEND (state_refs s) junk) = SOME (Varray av)) /\
     (!junk ck. evaluate (state_clock_fupd (combin_K ck) (state_refs_fupd (combin_K (APPEND (state_refs s) junk)) s))
                  env [X] =
                (state_clock_fupd (combin_K ck) (state_refs_fupd (combin_K (APPEND (state_refs s) junk)) s),
                 Rval [Loc T l1])) /\
     (!xv junk. TYPE x xv /\ n < LENGTH av ==>
        REFS_PRED_FRAME ro H (st,s)
          (set_arr (LUPDATE x n (get_arr st)) st,
           state_refs_fupd (combin_K (LUPDATE (Varray (LUPDATE xv n av)) l1
             (APPEND (state_refs s) junk))) s)) ==>
     ?s2 res st2 ck.
       evaluate (state_clock_fupd (combin_K ck) s) env [App Aupdate [X; nexp; xexp]] = (s2,res) /\
       MONAD UNIT_TYPE EXC_TYPE (Marray_update get_arr set_arr e n x) st (st2,res) /\
       REFS_PRED_FRAME ro H (st,s) (st2,s2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:(FFI)state` o MATCH_MP MON1AUX_Eval_evaluate o
    check (fun th -> MON1AUX_head_is "ml_Eval" (concl th) && free_in `xexp:exp` (concl th))) THEN
  DISCH_THEN(X_CHOOSE_THEN `xv:v` (X_CHOOSE_THEN `junk1:(v store_v)list` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `state_refs_fupd (combin_K (APPEND (state_refs s) junk1)) (s:(FFI)state)` o
    MATCH_MP MON1AUX_Eval_evaluate o
    check (fun th -> MON1AUX_head_is "ml_Eval" (concl th) && free_in `nexp:exp` (concl th))) THEN
  REWRITE_TAC[ml_NUM_def; ml_INT_def] THEN
  DISCH_THEN(X_CHOOSE_THEN `nv:v` (X_CHOOSE_THEN `junk2:(v store_v)list` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `nv:v`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[state_INFO.ri_accfupds; K_THM; MON1AUX_refs_fupd_fupd;
    GSYM APPEND_ASSOC]) THEN
  SUBGOAL_THEN `LENGTH ((get_arr:REFS->A list) st) = LENGTH (av:v list)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LIST_REL_LENGTH]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:(FFI)state`; `env:v sem_env`; `X:exp`; `nexp:exp`; `xexp:exp`; `n:num`;
    `xv:v`; `state_refs_fupd (combin_K (APPEND (state_refs s) junk1)) (s:(FFI)state)`;
    `state_refs_fupd (combin_K (APPEND (state_refs s) (APPEND junk1 junk2))) (s:(FFI)state)`;
    `l1:num`; `av:v list`] MON1AUX_ck_Aupdate) THEN
  ASM_REWRITE_TAC[state_INFO.ri_accfupds; K_THM; MON1AUX_refs_fupd_fupd] THEN
  ASM_CASES_TAC `n < LENGTH (av:v list)` THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `ck1:num` o MATCH_MP MON1AUX_ck_final) THENL
   [MAP_EVERY EXISTS_TAC
     [`state_refs_fupd (combin_K (LUPDATE (Varray (LUPDATE xv n av)) l1
         (APPEND (state_refs s) (APPEND junk1 junk2)))) (s:(FFI)state)`;
      `Rval [Conv NONE []]:(v list,v)result`;
      `(set_arr:A list->REFS->REFS) (LUPDATE x n (get_arr st)) st`; `ck1:num`] THEN
    ASM_SIMP_TAC[] THEN
    REWRITE_TAC[MON1AUX_MONAD_THM; ml_monadBase_Marray_update_def] THEN
    SUBGOAL_THEN `Mupdate (e:E) (x:A) n ((get_arr:REFS->A list) st) =
                  M_success (LUPDATE x n (get_arr st))` SUBST1_TAC THENL
     [MATCH_MP_TAC ml_monadBase_Mupdate_eq THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CAKE_REWRITE_TAC[] THEN
    REWRITE_TAC[PAIR_EQ; injectivity "exc"; distinctness "exc"; injectivity "result";
      distinctness "result"; CONS_11; RIGHT_EXISTS_AND_THM; UNWIND_THM1; UNIT_TYPE_def] THEN
    MESON_TAC[];
    MAP_EVERY EXISTS_TAC
     [`state_refs_fupd (combin_K (APPEND (state_refs s) (APPEND junk1 junk2))) (s:(FFI)state)`;
      `Rerr (Rraise (Conv (SOME (ExnStamp 3)) [])):(v list,v)result`; `st:REFS`; `ck1:num`] THEN
    ASM_REWRITE_TAC[REFS_PRED_FRAME_append] THEN
    REWRITE_TAC[MON1AUX_MONAD_THM; ml_monadBase_Marray_update_def] THEN
    SUBGOAL_THEN `Mupdate (e:E) (x:A) n ((get_arr:REFS->A list) st) = M_failure e`
      SUBST1_TAC THENL
     [MATCH_MP_TAC ml_monadBase_Mupdate_exn_eq THEN ASM_REWRITE_TAC[GE] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    CAKE_REWRITE_TAC[] THEN
    REWRITE_TAC[PAIR_EQ; injectivity "exc"; distinctness "exc"; injectivity "result";
      distinctness "result"; injectivity "error_result"; CONS_11; RIGHT_EXISTS_AND_THM;
      UNWIND_THM1] THEN
    ASM_REWRITE_TAC[]]);;

let MON1AUX_EvalM_Marray_update_handle_gen = prove
 (`!ro env X nexp xexp rexp n x (TYPE:A->v->bool) (EXC_TYPE:E->v->bool)
    (get_arr:REFS->A list) set_arr e st
    (H:(REFS->hprop)#((FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)))
    (s:(FFI)state) l1 av.
     ml_lookup_cons (Short (implode "Subscript")) env = SOME (0,ExnStamp 3) /\
     ml_Eval env nexp (ml_NUM n) /\ ml_Eval env rexp (EXC_TYPE e) /\
     ml_Eval env xexp (TYPE x) /\ ALL2 TYPE (get_arr st) av /\
     (!junk. store_lookup l1 (APPEND (state_refs s) junk) = SOME (Varray av)) /\
     (!junk ck. evaluate (state_clock_fupd (combin_K ck) (state_refs_fupd (combin_K (APPEND (state_refs s) junk)) s))
                  env [X] =
                (state_clock_fupd (combin_K ck) (state_refs_fupd (combin_K (APPEND (state_refs s) junk)) s),
                 Rval [Loc T l1])) /\
     (!xv junk. TYPE x xv /\ n < LENGTH av ==>
        REFS_PRED_FRAME ro H (st,s)
          (set_arr (LUPDATE x n (get_arr st)) st,
           state_refs_fupd (combin_K (LUPDATE (Varray (LUPDATE xv n av)) l1
             (APPEND (state_refs s) junk))) s)) ==>
     ?s2 res st2 ck.
       evaluate (state_clock_fupd (combin_K ck) s) env
         [Handle (App Aupdate [X; nexp; xexp])
            [(Pcon (SOME (Short (implode "Subscript"))) [],Raise rexp)]] = (s2,res) /\
       MONAD UNIT_TYPE EXC_TYPE (Marray_update get_arr set_arr e n x) st (st2,res) /\
       REFS_PRED_FRAME ro H (st,s) (st2,s2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:(FFI)state` o MATCH_MP MON1AUX_Eval_evaluate o
    check (fun th -> MON1AUX_head_is "ml_Eval" (concl th) && free_in `xexp:exp` (concl th))) THEN
  DISCH_THEN(X_CHOOSE_THEN `xv:v` (X_CHOOSE_THEN `junk1:(v store_v)list` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `state_refs_fupd (combin_K (APPEND (state_refs s) junk1)) (s:(FFI)state)` o
    MATCH_MP MON1AUX_Eval_evaluate o
    check (fun th -> MON1AUX_head_is "ml_Eval" (concl th) && free_in `nexp:exp` (concl th))) THEN
  REWRITE_TAC[ml_NUM_def; ml_INT_def] THEN
  DISCH_THEN(X_CHOOSE_THEN `nv:v` (X_CHOOSE_THEN `junk2:(v store_v)list` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `nv:v`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[state_INFO.ri_accfupds; K_THM; MON1AUX_refs_fupd_fupd;
    GSYM APPEND_ASSOC]) THEN
  SUBGOAL_THEN `LENGTH ((get_arr:REFS->A list) st) = LENGTH (av:v list)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LIST_REL_LENGTH]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:(FFI)state`; `env:v sem_env`; `X:exp`; `nexp:exp`; `xexp:exp`; `n:num`;
    `xv:v`; `state_refs_fupd (combin_K (APPEND (state_refs s) junk1)) (s:(FFI)state)`;
    `state_refs_fupd (combin_K (APPEND (state_refs s) (APPEND junk1 junk2))) (s:(FFI)state)`;
    `l1:num`; `av:v list`] MON1AUX_ck_Aupdate) THEN
  ASM_REWRITE_TAC[state_INFO.ri_accfupds; K_THM; MON1AUX_refs_fupd_fupd] THEN
  ASM_CASES_TAC `n < LENGTH (av:v list)` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THENL
   [SUBGOAL_THEN
     `?ck1. evaluate (state_clock_fupd (combin_K ck1) (s:(FFI)state)) env
         [Handle (App Aupdate [X; nexp; xexp])
            [(Pcon (SOME (Short (implode "Subscript"))) [],Raise rexp)]] =
       (state_refs_fupd (combin_K (LUPDATE (Varray (LUPDATE xv n av)) l1
          (APPEND (state_refs s) (APPEND junk1 junk2)))) s,Rval [Conv NONE []])`
      (X_CHOOSE_TAC `ck1:num`) THENL
     [MATCH_MP_TAC MON1AUX_ck_final THEN MATCH_MP_TAC MON1AUX_ck_Handle_Rval THEN
      FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC
     [`state_refs_fupd (combin_K (LUPDATE (Varray (LUPDATE xv n av)) l1
         (APPEND (state_refs s) (APPEND junk1 junk2)))) (s:(FFI)state)`;
      `Rval [Conv NONE []]:(v list,v)result`;
      `(set_arr:A list->REFS->REFS) (LUPDATE x n (get_arr st)) st`; `ck1:num`] THEN
    ASM_SIMP_TAC[] THEN
    REWRITE_TAC[MON1AUX_MONAD_THM; ml_monadBase_Marray_update_def] THEN
    SUBGOAL_THEN `Mupdate (e:E) (x:A) n ((get_arr:REFS->A list) st) =
                  M_success (LUPDATE x n (get_arr st))` SUBST1_TAC THENL
     [MATCH_MP_TAC ml_monadBase_Mupdate_eq THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CAKE_REWRITE_TAC[] THEN
    REWRITE_TAC[PAIR_EQ; injectivity "exc"; distinctness "exc"; injectivity "result";
      distinctness "result"; CONS_11; RIGHT_EXISTS_AND_THM; UNWIND_THM1; UNIT_TYPE_def] THEN
    MESON_TAC[];
    FIRST_X_ASSUM(MP_TAC o
      SPEC `state_refs_fupd (combin_K (APPEND (state_refs s) (APPEND junk1 junk2))) (s:(FFI)state)` o
      MATCH_MP MON1AUX_Eval_evaluate o
      check (fun th -> MON1AUX_head_is "ml_Eval" (concl th) && free_in `rexp:exp` (concl th))) THEN
    DISCH_THEN(X_CHOOSE_THEN `ev:v` (X_CHOOSE_THEN `junk3:(v store_v)list`
      STRIP_ASSUME_TAC)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[state_INFO.ri_accfupds; K_THM; MON1AUX_refs_fupd_fupd;
      GSYM APPEND_ASSOC]) THEN
    SUBGOAL_THEN
     `?ck1. evaluate (state_clock_fupd (combin_K ck1) (s:(FFI)state)) env
         [Handle (App Aupdate [X; nexp; xexp])
            [(Pcon (SOME (Short (implode "Subscript"))) [],Raise rexp)]] =
       (state_refs_fupd (combin_K (APPEND (state_refs s) (APPEND junk1 (APPEND junk2 junk3)))) s,
        Rerr (Rraise ev))`
      (X_CHOOSE_TAC `ck1:num`) THENL
     [MATCH_MP_TAC MON1AUX_ck_final THEN MATCH_MP_TAC MON1AUX_ck_Handle_Subscript THEN
      EXISTS_TAC `state_refs_fupd (combin_K (APPEND (state_refs s) (APPEND junk1 junk2)))
                    (s:(FFI)state)` THEN
      REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC
     [`state_refs_fupd (combin_K (APPEND (state_refs s) (APPEND junk1 (APPEND junk2 junk3))))
         (s:(FFI)state)`;
      `Rerr (Rraise ev):(v list,v)result`; `st:REFS`; `ck1:num`] THEN
    ASM_REWRITE_TAC[REFS_PRED_FRAME_append] THEN
    REWRITE_TAC[MON1AUX_MONAD_THM; ml_monadBase_Marray_update_def] THEN
    SUBGOAL_THEN `Mupdate (e:E) (x:A) n ((get_arr:REFS->A list) st) = M_failure e`
      SUBST1_TAC THENL
     [MATCH_MP_TAC ml_monadBase_Mupdate_exn_eq THEN ASM_REWRITE_TAC[GE] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    CAKE_REWRITE_TAC[] THEN
    REWRITE_TAC[PAIR_EQ; injectivity "exc"; distinctness "exc"; injectivity "result";
      distinctness "result"; injectivity "error_result"; CONS_11; RIGHT_EXISTS_AND_THM;
      UNWIND_THM1] THEN
    ASM_REWRITE_TAC[]]);;

let MON1AUX_RARRAY_update_frame = prove
 (`!ro (TYPE:A->v->bool) (get_arr:REFS->A list) set_arr (H:REFS->hprop)
    (p:(FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)) st (s:(FFI)state)
    l0 l1 av n x xv junk.
     (!refs x. get_arr (set_arr x refs) = x) /\ (!refs x. H (set_arr x refs) = H refs) /\
     store_lookup l0 (state_refs s) = SOME (Refv (Loc T l1)) /\
     store_lookup l1 (state_refs s) = SOME (Varray av) /\ TYPE x xv ==>
     REFS_PRED_FRAME ro ((\refs. RARRAY_REL TYPE (Loc T l0) (get_arr refs) STAR H refs),p)
       (st,s)
       (set_arr (LUPDATE x n (get_arr st)) st,
        state_refs_fupd (combin_K (LUPDATE (Varray (LUPDATE xv n av)) l1
          (APPEND (state_refs s) junk))) s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[REFS_PRED_FRAME_def] THEN SIMP[] THEN
  CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `F1:hprop` THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM STAR_ASSOC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MON1AUX_RARRAY_open) THEN
  DISCH_THEN(X_CHOOSE_THEN `l0':num` (X_CHOOSE_THEN `l1':num` (X_CHOOSE_THEN `av':v list`
    STRIP_ASSUME_TAC))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[injectivity "v"]) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `l0:num = l0'`)) THEN
  SUBGOAL_THEN `l1':num = l1` SUBST_ALL_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o SPEC `[]:(v store_v)list` o
      MATCH_MP MON1AUX_RARRAY_lookups) THEN
    ASM_REWRITE_TAC[APPEND_NIL; injectivity "option"; injectivity "store_v";
      injectivity "v"] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `av':v list = av` SUBST_ALL_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT2 o SPEC `[]:(v store_v)list` o
      MATCH_MP MON1AUX_RARRAY_lookups) THEN
    ASM_REWRITE_TAC[APPEND_NIL; injectivity "option"; injectivity "store_v"] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(cf_ARRAY (Loc T l1) av STAR
     (cf_REF (Loc T l0) (Loc T l1) STAR (H:REFS->hprop) st STAR F1))
      (st2heap p (s:(FFI)state))`
    (MP_TAC o SPECL [`LUPDATE xv n (av:v list)`; `junk:(v store_v)list`] o
     MATCH_MP MON1AUX_ARRAY_update_frame) THENL
   [MON1AUX_HPROP_AC_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `ALL2 (TYPE:A->v->bool) (LUPDATE x n ((get_arr:REFS->A list) st))
                  (LUPDATE xv n av)` ASSUME_TAC THENL
   [MATCH_MP_TAC EVERY2_LUPDATE_same THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[RARRAY_REL_def; RARRAY_def; SEP_CLAUSES; SEP_EXISTS_THM] THEN
  MAP_EVERY EXISTS_TAC [`LUPDATE xv n (av:v list)`; `Loc T l1`] THEN
  CONV_TAC MON1AUX_EXTRACT_PURE_FACTS_CONV THEN ASM_REWRITE_TAC[] THEN
  MON1AUX_HPROP_AC_TAC);;

let MON1AUX_ARRAY_REL_update_frame = prove
 (`!ro (TYPE:A->v->bool) (get_arr:REFS->A list) set_arr (H:REFS->hprop)
    (p:(FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)) st (s:(FFI)state)
    l1 av n x xv junk.
     (!refs x. get_arr (set_arr x refs) = x) /\ (!refs x. H (set_arr x refs) = H refs) /\
     store_lookup l1 (state_refs s) = SOME (Varray av) /\ TYPE x xv ==>
     REFS_PRED_FRAME ro ((\refs. ARRAY_REL TYPE (Loc T l1) (get_arr refs) STAR H refs),p)
       (st,s)
       (set_arr (LUPDATE x n (get_arr st)) st,
        state_refs_fupd (combin_K (LUPDATE (Varray (LUPDATE xv n av)) l1
          (APPEND (state_refs s) junk))) s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[REFS_PRED_FRAME_def] THEN SIMP[] THEN
  CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `F1:hprop` THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM STAR_ASSOC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MON1AUX_ARRAY_open) THEN
  DISCH_THEN(X_CHOOSE_THEN `l1':num` (X_CHOOSE_THEN `av':v list` STRIP_ASSUME_TAC)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[injectivity "v"]) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `l1:num = l1'`)) THEN
  SUBGOAL_THEN `av':v list = av` SUBST_ALL_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `[]:(v store_v)list` o
      MATCH_MP MON1AUX_store_lookup_ARRAY_junk) THEN
    ASM_REWRITE_TAC[APPEND_NIL; injectivity "option"; injectivity "store_v"] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`LUPDATE xv n (av:v list)`; `junk:(v store_v)list`] o
    MATCH_MP MON1AUX_ARRAY_update_frame o
    check (MON1AUX_head_is "STAR" o rator o concl)) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `ALL2 (TYPE:A->v->bool) (LUPDATE x n ((get_arr:REFS->A list) st))
                  (LUPDATE xv n av)` ASSUME_TAC THENL
   [MATCH_MP_TAC EVERY2_LUPDATE_same THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[ARRAY_REL_def; SEP_CLAUSES; SEP_EXISTS_THM] THEN
  EXISTS_TAC `LUPDATE xv n (av:v list)` THEN
  CONV_TAC MON1AUX_EXTRACT_PURE_FACTS_CONV THEN ASM_REWRITE_TAC[] THEN
  MON1AUX_HPROP_AC_TAC);;

let MON1AUX_RARRAY_alloc_frame = prove
 (`!ro (TYPE:A->v->bool) (get_arr:REFS->A list) set_arr (H:REFS->hprop)
    (p:(FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)) st (s:(FFI)state)
    l0 n x xv junk.
     (!refs x. get_arr (set_arr x refs) = x) /\ (!refs x. H (set_arr x refs) = H refs) /\
     TYPE x xv ==>
     REFS_PRED_FRAME ro ((\refs. RARRAY_REL TYPE (Loc T l0) (get_arr refs) STAR H refs),p)
       (st,s)
       (set_arr (REPLICATE n x) st,
        state_refs_fupd (combin_K (LUPDATE (Refv (Loc T (LENGTH (APPEND (state_refs s) junk)))) l0
          (APPEND (APPEND (state_refs s) junk) [Varray (REPLICATE n xv)]))) s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[REFS_PRED_FRAME_def] THEN SIMP[] THEN
  REWRITE_TAC[GSYM LENGTH_APPEND] THEN
  CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `F1:hprop` THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM STAR_ASSOC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MON1AUX_RARRAY_open) THEN
  DISCH_THEN(X_CHOOSE_THEN `l0':num` (X_CHOOSE_THEN `l1:num` (X_CHOOSE_THEN `av:v list`
    STRIP_ASSUME_TAC))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[injectivity "v"]) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `l0:num = l0'`)) THEN
  (* the junk *)
  SUBGOAL_THEN
   `((cf_REF (Loc T l0) (Loc T l1) STAR cf_ARRAY (Loc T l1) av STAR
      (H:REFS->hprop) st STAR F1) STAR cf_GC)
      (st2heap p (state_refs_fupd (combin_K (APPEND (state_refs s) junk)) (s:(FFI)state)))`
    ASSUME_TAC THENL
   [MATCH_MP_TAC STATE_APPEND_JUNK THEN REWRITE_TAC[with_same_refs] THEN
    MON1AUX_HPROP_AC_TAC; ALL_TAC] THEN
  (* the new array cell *)
  SUBGOAL_THEN
   `(cf_ARRAY (Loc T (LENGTH (APPEND (state_refs s) junk))) (REPLICATE n xv) STAR
     ((cf_REF (Loc T l0) (Loc T l1) STAR cf_ARRAY (Loc T l1) av STAR
       (H:REFS->hprop) st STAR F1) STAR cf_GC))
      (st2heap p (state_refs_fupd
        (combin_K (APPEND (APPEND (state_refs s) junk) [Varray (REPLICATE n xv)])) (s:(FFI)state)))`
    ASSUME_TAC THENL
   [MATCH_MP_TAC MON1AUX_STAR_I THEN
    MAP_EVERY EXISTS_TAC
     [`store2heap_aux (LENGTH (APPEND (state_refs (s:(FFI)state)) junk))
         [Varray (REPLICATE n (xv:v))]`;
      `st2heap p (state_refs_fupd (combin_K (APPEND (state_refs s) junk)) (s:(FFI)state))`] THEN
    ASM_REWRITE_TAC[MON1AUX_store2heap_ARRAY_SAT] THEN
    ONCE_REWRITE_TAC[SPLIT_SYM] THEN REWRITE_TAC[STATE_SPLIT_REFS];
    ALL_TAC] THEN
  (* the reference now points to the new array *)
  SUBGOAL_THEN
   `(cf_REF (Loc T l0) (Loc T l1) STAR
     (cf_ARRAY (Loc T (LENGTH (APPEND (state_refs s) junk))) (REPLICATE n xv) STAR
      cf_ARRAY (Loc T l1) av STAR (H:REFS->hprop) st STAR F1 STAR cf_GC))
      (st2heap p (state_refs_fupd
        (combin_K (APPEND (APPEND (state_refs s) junk) [Varray (REPLICATE n xv)])) (s:(FFI)state)))`
    (MP_TAC o SPECL [`Loc T (LENGTH (APPEND (state_refs (s:(FFI)state)) junk))`;
                     `[]:(v store_v)list`] o MATCH_MP MON1AUX_REF_update_frame) THENL
   [MON1AUX_HPROP_AC_TAC; ALL_TAC] THEN
  REWRITE_TAC[state_INFO.ri_accfupds; K_THM; MON1AUX_refs_fupd_fupd; APPEND_NIL] THEN
  DISCH_TAC THEN
  (* the old array is garbage *)
  SUBGOAL_THEN
   `((cf_REF (Loc T l0) (Loc T (LENGTH (APPEND (state_refs (s:(FFI)state)) junk))) STAR
      cf_ARRAY (Loc T (LENGTH (APPEND (state_refs s) junk))) (REPLICATE n xv) STAR
      (H:REFS->hprop) st STAR F1) STAR
     (cf_ARRAY (Loc T l1) av STAR cf_GC STAR cf_GC))
      (st2heap p (state_refs_fupd
        (combin_K (LUPDATE (Refv (Loc T (LENGTH (APPEND (state_refs s) junk)))) l0
          (APPEND (APPEND (state_refs s) junk) [Varray (REPLICATE n xv)]))) s))`
    (ASSUME_TAC o MATCH_MP (GEN_ALL HPROP_TO_GC_R)) THENL
   [MON1AUX_HPROP_AC_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `ALL2 (TYPE:A->v->bool) (REPLICATE n x) (REPLICATE n xv)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LIST_REL_REPLICATE_same]; ALL_TAC] THEN
  REWRITE_TAC[RARRAY_REL_def; RARRAY_def; SEP_CLAUSES; SEP_EXISTS_THM] THEN
  MAP_EVERY EXISTS_TAC [`REPLICATE n (xv:v)`;
    `Loc T (LENGTH (APPEND (state_refs (s:(FFI)state)) junk))`] THEN
  CONV_TAC MON1AUX_EXTRACT_PURE_FACTS_CONV THEN ASM_REWRITE_TAC[] THEN
  MON1AUX_HPROP_AC_TAC);;

let EvalM_R_Marray_length = prove
 (`!vname loc (TYPE:A->v->bool) (EXC_TYPE:E->v->bool) (H:REFS->hprop)
    (get_arr:REFS->A list) (x:A) env.
     nsLookup (sem_env_v env) (Short vname) = SOME loc ==>
     EvalM ro env st (App Alength [App Opderef [Var (Short vname)]])
       ((MONAD ml_NUM EXC_TYPE) (Marray_length get_arr))
       ((\refs. RARRAY_REL TYPE loc (get_arr refs) STAR H refs),
        (p:(FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[EvalM_def; REFS_PRED_def] THEN
  X_GEN_TAC `s:(FFI)state` THEN REWRITE_TAC[GSYM STAR_ASSOC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MON1AUX_RARRAY_open) THEN
  DISCH_THEN(X_CHOOSE_THEN `l0:num` (X_CHOOSE_THEN `l1:num` (X_CHOOSE_THEN `av:v list`
    STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `loc:v`)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MON1AUX_RARRAY_lookups) THEN
  MATCH_MP_TAC MON1AUX_EvalM_Marray_length_gen THEN
  MAP_EVERY EXISTS_TAC [`TYPE:A->v->bool`; `l1:num`; `av:v list`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
  MATCH_MP_TAC MON1AUX_evaluate_Opderef THEN EXISTS_TAC `l0:num` THEN
  ASM_REWRITE_TAC[state_INFO.ri_accfupds; K_THM]);;

let EvalM_R_Marray_sub_subscript = prove
 (`!vname loc (TYPE:A->v->bool) (EXC_TYPE:E->v->bool) (H:REFS->hprop)
    (get_arr:REFS->A list) e env n nexp.
     EXC_TYPE e (Conv (SOME (ExnStamp 3)) []) ==>
     nsLookup (sem_env_v env) (Short vname) = SOME loc ==>
     ml_lookup_cons (Short (implode "Subscript")) env = SOME (0,ExnStamp 3) ==>
     ml_Eval env nexp (ml_NUM n) ==>
     EvalM ro env st (App Asub [App Opderef [Var (Short vname)]; nexp])
       ((MONAD TYPE EXC_TYPE) (Marray_sub get_arr e n))
       ((\refs. RARRAY_REL TYPE loc (get_arr refs) STAR H refs),
        (p:(FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)))`,
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN REWRITE_TAC[EvalM_def; REFS_PRED_def] THEN
  X_GEN_TAC `s:(FFI)state` THEN REWRITE_TAC[GSYM STAR_ASSOC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MON1AUX_RARRAY_open) THEN
  DISCH_THEN(X_CHOOSE_THEN `l0:num` (X_CHOOSE_THEN `l1:num` (X_CHOOSE_THEN `av:v list`
    STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `loc:v`)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MON1AUX_RARRAY_lookups) THEN
  MATCH_MP_TAC MON1AUX_EvalM_Marray_sub_gen THEN
  MAP_EVERY EXISTS_TAC [`l1:num`; `av:v list`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
  MATCH_MP_TAC MON1AUX_evaluate_Opderef THEN EXISTS_TAC `l0:num` THEN
  ASM_REWRITE_TAC[state_INFO.ri_accfupds; K_THM]);;

let EvalM_R_Marray_sub_handle = prove
 (`!vname loc (TYPE:A->v->bool) (EXC_TYPE:E->v->bool) (H:REFS->hprop)
    (get_arr:REFS->A list) e rexp env n nexp.
     nsLookup (sem_env_v env) (Short vname) = SOME loc ==>
     ml_lookup_cons (Short (implode "Subscript")) env = SOME (0,ExnStamp 3) ==>
     ml_Eval env nexp (ml_NUM n) ==>
     ml_Eval env rexp (EXC_TYPE e) ==>
     EvalM ro env st
       (Handle (App Asub [App Opderef [Var (Short vname)]; nexp])
          [(Pcon (SOME (Short (implode "Subscript"))) [],Raise rexp)])
       ((MONAD TYPE EXC_TYPE) (Marray_sub get_arr e n))
       ((\refs. RARRAY_REL TYPE loc (get_arr refs) STAR H refs),
        (p:(FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)))`,
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN REWRITE_TAC[EvalM_def; REFS_PRED_def] THEN
  X_GEN_TAC `s:(FFI)state` THEN REWRITE_TAC[GSYM STAR_ASSOC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MON1AUX_RARRAY_open) THEN
  DISCH_THEN(X_CHOOSE_THEN `l0:num` (X_CHOOSE_THEN `l1:num` (X_CHOOSE_THEN `av:v list`
    STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `loc:v`)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MON1AUX_RARRAY_lookups) THEN
  MATCH_MP_TAC MON1AUX_EvalM_Marray_sub_handle_gen THEN
  MAP_EVERY EXISTS_TAC [`l1:num`; `av:v list`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
  MATCH_MP_TAC MON1AUX_evaluate_Opderef THEN EXISTS_TAC `l0:num` THEN
  ASM_REWRITE_TAC[state_INFO.ri_accfupds; K_THM]);;

let EvalM_R_Marray_update_subscript = prove
 (`!vname loc (TYPE:A->v->bool) (EXC_TYPE:E->v->bool) (H:REFS->hprop)
    (get_arr:REFS->A list) set_arr e env n x xexp nexp.
     nsLookup (sem_env_v env) (Short vname) = SOME loc ==>
     ml_lookup_cons (Short (implode "Subscript")) env = SOME (0,ExnStamp 3) ==>
     EXC_TYPE e (Conv (SOME (ExnStamp 3)) []) ==>
     (!refs x. get_arr (set_arr x refs) = x) ==>
     (!refs x. H (set_arr x refs) = H refs) ==>
     ml_Eval env nexp (ml_NUM n) ==>
     ml_Eval env xexp (TYPE x) ==>
     EvalM ro env st (App Aupdate [App Opderef [Var (Short vname)]; nexp; xexp])
       ((MONAD UNIT_TYPE EXC_TYPE) (Marray_update get_arr set_arr e n x))
       ((\refs. RARRAY_REL TYPE loc (get_arr refs) STAR H refs),
        (p:(FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)))`,
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN REWRITE_TAC[EvalM_def; REFS_PRED_def] THEN
  X_GEN_TAC `s:(FFI)state` THEN REWRITE_TAC[GSYM STAR_ASSOC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MON1AUX_RARRAY_open) THEN
  DISCH_THEN(X_CHOOSE_THEN `l0:num` (X_CHOOSE_THEN `l1:num` (X_CHOOSE_THEN `av:v list`
    STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `loc:v`)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MON1AUX_RARRAY_lookups) THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[APPEND_NIL] o SPEC `[]:(v store_v)list` o
    check (is_forall o concl)) THEN
  MATCH_MP_TAC MON1AUX_EvalM_Marray_update_gen THEN
  MAP_EVERY EXISTS_TAC [`TYPE:A->v->bool`; `l1:num`; `av:v list`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN
    MATCH_MP_TAC MON1AUX_evaluate_Opderef THEN EXISTS_TAC `l0:num` THEN
    ASM_REWRITE_TAC[state_INFO.ri_accfupds; K_THM];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MON1AUX_RARRAY_update_frame THEN
    ASM_REWRITE_TAC[]]);;

let EvalM_R_Marray_update_handle = prove
 (`!vname loc (TYPE:A->v->bool) (EXC_TYPE:E->v->bool) (H:REFS->hprop)
    (get_arr:REFS->A list) set_arr e rexp env n x xexp nexp.
     nsLookup (sem_env_v env) (Short vname) = SOME loc ==>
     ml_lookup_cons (Short (implode "Subscript")) env = SOME (0,ExnStamp 3) ==>
     (!refs x. get_arr (set_arr x refs) = x) ==>
     (!refs x. H (set_arr x refs) = H refs) ==>
     ml_Eval env nexp (ml_NUM n) ==>
     ml_Eval env rexp (EXC_TYPE e) ==>
     ml_Eval env xexp (TYPE x) ==>
     EvalM ro env st
       (Handle (App Aupdate [App Opderef [Var (Short vname)]; nexp; xexp])
          [(Pcon (SOME (Short (implode "Subscript"))) [],Raise rexp)])
       ((MONAD UNIT_TYPE EXC_TYPE) (Marray_update get_arr set_arr e n x))
       ((\refs. RARRAY_REL TYPE loc (get_arr refs) STAR H refs),
        (p:(FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)))`,
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN REWRITE_TAC[EvalM_def; REFS_PRED_def] THEN
  X_GEN_TAC `s:(FFI)state` THEN REWRITE_TAC[GSYM STAR_ASSOC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MON1AUX_RARRAY_open) THEN
  DISCH_THEN(X_CHOOSE_THEN `l0:num` (X_CHOOSE_THEN `l1:num` (X_CHOOSE_THEN `av:v list`
    STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `loc:v`)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MON1AUX_RARRAY_lookups) THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[APPEND_NIL] o SPEC `[]:(v store_v)list` o
    check (is_forall o concl)) THEN
  MATCH_MP_TAC MON1AUX_EvalM_Marray_update_handle_gen THEN
  MAP_EVERY EXISTS_TAC [`TYPE:A->v->bool`; `l1:num`; `av:v list`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN
    MATCH_MP_TAC MON1AUX_evaluate_Opderef THEN EXISTS_TAC `l0:num` THEN
    ASM_REWRITE_TAC[state_INFO.ri_accfupds; K_THM];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MON1AUX_RARRAY_update_frame THEN
    ASM_REWRITE_TAC[]]);;

let EvalM_R_Marray_alloc = prove
 (`!vname loc (TYPE:A->v->bool) (EXC_TYPE:E->v->bool) (H:REFS->hprop)
    (get_arr:REFS->A list) set_arr n x env nexp xexp.
     nsLookup (sem_env_v env) (Short vname) = SOME loc ==>
     (!refs x. get_arr (set_arr x refs) = x) ==>
     (!refs x. H (set_arr x refs) = H refs) ==>
     ml_Eval env nexp (ml_NUM n) ==>
     ml_Eval env xexp (TYPE x) ==>
     EvalM ro env st (App Opassign [Var (Short vname); App Aalloc [nexp; xexp]])
       ((MONAD UNIT_TYPE EXC_TYPE) (Marray_alloc set_arr n x))
       ((\refs. RARRAY_REL TYPE loc (get_arr refs) STAR H refs),
        (p:(FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)))`,
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN REWRITE_TAC[EvalM_def; REFS_PRED_def] THEN
  X_GEN_TAC `s:(FFI)state` THEN REWRITE_TAC[GSYM STAR_ASSOC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MON1AUX_RARRAY_open) THEN
  DISCH_THEN(X_CHOOSE_THEN `l0:num` (X_CHOOSE_THEN `l1:num` (X_CHOOSE_THEN `av:v list`
    STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `loc:v`)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MON1AUX_RARRAY_lookups) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:(FFI)state` o MATCH_MP MON1AUX_Eval_evaluate o
    check (fun th -> MON1AUX_head_is "ml_Eval" (concl th) && free_in `xexp:exp` (concl th))) THEN
  DISCH_THEN(X_CHOOSE_THEN `xv:v` (X_CHOOSE_THEN `junk1:(v store_v)list` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `state_refs_fupd (combin_K (APPEND (state_refs s) junk1)) (s:(FFI)state)` o
    MATCH_MP MON1AUX_Eval_evaluate o
    check (fun th -> MON1AUX_head_is "ml_Eval" (concl th) && free_in `nexp:exp` (concl th))) THEN
  REWRITE_TAC[ml_NUM_def; ml_INT_def] THEN
  DISCH_THEN(X_CHOOSE_THEN `nv:v` (X_CHOOSE_THEN `junk2:(v store_v)list` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `nv:v`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[state_INFO.ri_accfupds; K_THM; MON1AUX_refs_fupd_fupd;
    GSYM APPEND_ASSOC]) THEN
  MP_TAC(ISPECL [`s:(FFI)state`; `env:v sem_env`; `vname:mlstring`; `nexp:exp`; `xexp:exp`;
    `n:num`; `xv:v`; `state_refs_fupd (combin_K (APPEND (state_refs s) junk1)) (s:(FFI)state)`;
    `state_refs_fupd (combin_K (APPEND (state_refs s) (APPEND junk1 junk2))) (s:(FFI)state)`;
    `l0:num`; `Loc T l1`] MON1AUX_ck_Alloc_assign) THEN
  ASM_REWRITE_TAC[state_INFO.ri_accfupds; K_THM; MON1AUX_refs_fupd_fupd] THEN
  DISCH_THEN(X_CHOOSE_TAC `ck1:num` o MATCH_MP MON1AUX_ck_final) THEN
  MAP_EVERY EXISTS_TAC
   [`state_refs_fupd (combin_K (LUPDATE (Refv (Loc T (LENGTH (APPEND (state_refs s)
        (APPEND junk1 junk2))))) l0
       (APPEND (APPEND (state_refs s) (APPEND junk1 junk2)) [Varray (REPLICATE n xv)])))
       (s:(FFI)state)`;
    `Rval [Conv NONE []]:(v list,v)result`;
    `(set_arr:A list->REFS->REFS) (REPLICATE n x) st`; `ck1:num`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[MON1AUX_MONAD_THM; ml_monadBase_Marray_alloc_def; PAIR_EQ; injectivity "exc";
      distinctness "exc"; injectivity "result"; distinctness "result"; CONS_11;
      RIGHT_EXISTS_AND_THM; UNWIND_THM1; UNIT_TYPE_def] THEN MESON_TAC[];
    MATCH_MP_TAC MON1AUX_RARRAY_alloc_frame THEN ASM_REWRITE_TAC[]]);;

(* Fixed-size arrays *)

let EvalM_F_Marray_length = prove
 (`!vname loc (TYPE:A->v->bool) (EXC_TYPE:E->v->bool) (H:REFS->hprop)
    (get_arr:REFS->A list) (x:A) env.
     nsLookup (sem_env_v env) (Short vname) = SOME loc ==>
     EvalM ro env st (App Alength [Var (Short vname)])
       ((MONAD ml_NUM EXC_TYPE) (Marray_length get_arr))
       ((\refs. ARRAY_REL TYPE loc (get_arr refs) STAR H refs),
        (p:(FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[EvalM_def; REFS_PRED_def] THEN
  X_GEN_TAC `s:(FFI)state` THEN REWRITE_TAC[GSYM STAR_ASSOC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MON1AUX_ARRAY_open) THEN
  DISCH_THEN(X_CHOOSE_THEN `l1:num` (X_CHOOSE_THEN `av:v list` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `loc:v`)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MON1AUX_store_lookup_ARRAY_junk) THEN
  MATCH_MP_TAC MON1AUX_EvalM_Marray_length_gen THEN
  MAP_EVERY EXISTS_TAC [`TYPE:A->v->bool`; `l1:num`; `av:v list`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
  MATCH_MP_TAC MON1AUX_evaluate_Var_Short THEN ASM_REWRITE_TAC[]);;

let EvalM_F_Marray_sub_subscript = prove
 (`!vname loc (TYPE:A->v->bool) (EXC_TYPE:E->v->bool) (H:REFS->hprop)
    (get_arr:REFS->A list) e env n nexp.
     EXC_TYPE e (Conv (SOME (ExnStamp 3)) []) ==>
     nsLookup (sem_env_v env) (Short vname) = SOME loc ==>
     ml_lookup_cons (Short (implode "Subscript")) env = SOME (0,ExnStamp 3) ==>
     ml_Eval env nexp (ml_NUM n) ==>
     EvalM ro env st (App Asub [Var (Short vname); nexp])
       ((MONAD TYPE EXC_TYPE) (Marray_sub get_arr e n))
       ((\refs. ARRAY_REL TYPE loc (get_arr refs) STAR H refs),
        (p:(FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)))`,
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN REWRITE_TAC[EvalM_def; REFS_PRED_def] THEN
  X_GEN_TAC `s:(FFI)state` THEN REWRITE_TAC[GSYM STAR_ASSOC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MON1AUX_ARRAY_open) THEN
  DISCH_THEN(X_CHOOSE_THEN `l1:num` (X_CHOOSE_THEN `av:v list` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `loc:v`)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MON1AUX_store_lookup_ARRAY_junk) THEN
  MATCH_MP_TAC MON1AUX_EvalM_Marray_sub_gen THEN
  MAP_EVERY EXISTS_TAC [`l1:num`; `av:v list`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
  MATCH_MP_TAC MON1AUX_evaluate_Var_Short THEN ASM_REWRITE_TAC[]);;

let EvalM_F_Marray_sub_handle = prove
 (`!vname loc (TYPE:A->v->bool) (EXC_TYPE:E->v->bool) (H:REFS->hprop)
    (get_arr:REFS->A list) e rexp env n nexp.
     nsLookup (sem_env_v env) (Short vname) = SOME loc ==>
     ml_lookup_cons (Short (implode "Subscript")) env = SOME (0,ExnStamp 3) ==>
     ml_Eval env nexp (ml_NUM n) ==>
     ml_Eval env rexp (EXC_TYPE e) ==>
     EvalM ro env st
       (Handle (App Asub [Var (Short vname); nexp])
          [(Pcon (SOME (Short (implode "Subscript"))) [],Raise rexp)])
       ((MONAD TYPE EXC_TYPE) (Marray_sub get_arr e n))
       ((\refs. ARRAY_REL TYPE loc (get_arr refs) STAR H refs),
        (p:(FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)))`,
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN REWRITE_TAC[EvalM_def; REFS_PRED_def] THEN
  X_GEN_TAC `s:(FFI)state` THEN REWRITE_TAC[GSYM STAR_ASSOC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MON1AUX_ARRAY_open) THEN
  DISCH_THEN(X_CHOOSE_THEN `l1:num` (X_CHOOSE_THEN `av:v list` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `loc:v`)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MON1AUX_store_lookup_ARRAY_junk) THEN
  MATCH_MP_TAC MON1AUX_EvalM_Marray_sub_handle_gen THEN
  MAP_EVERY EXISTS_TAC [`l1:num`; `av:v list`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
  MATCH_MP_TAC MON1AUX_evaluate_Var_Short THEN ASM_REWRITE_TAC[]);;

let EvalM_F_Marray_update_subscript = prove
 (`!vname loc (TYPE:A->v->bool) (EXC_TYPE:E->v->bool) (H:REFS->hprop)
    (get_arr:REFS->A list) set_arr e env n x xexp nexp.
     nsLookup (sem_env_v env) (Short vname) = SOME loc ==>
     ml_lookup_cons (Short (implode "Subscript")) env = SOME (0,ExnStamp 3) ==>
     EXC_TYPE e (Conv (SOME (ExnStamp 3)) []) ==>
     (!refs x. get_arr (set_arr x refs) = x) ==>
     (!refs x. H (set_arr x refs) = H refs) ==>
     ml_Eval env nexp (ml_NUM n) ==>
     ml_Eval env xexp (TYPE x) ==>
     EvalM ro env st (App Aupdate [Var (Short vname); nexp; xexp])
       ((MONAD UNIT_TYPE EXC_TYPE) (Marray_update get_arr set_arr e n x))
       ((\refs. ARRAY_REL TYPE loc (get_arr refs) STAR H refs),
        (p:(FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)))`,
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN REWRITE_TAC[EvalM_def; REFS_PRED_def] THEN
  X_GEN_TAC `s:(FFI)state` THEN REWRITE_TAC[GSYM STAR_ASSOC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MON1AUX_ARRAY_open) THEN
  DISCH_THEN(X_CHOOSE_THEN `l1:num` (X_CHOOSE_THEN `av:v list` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `loc:v`)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MON1AUX_store_lookup_ARRAY_junk) THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[APPEND_NIL] o SPEC `[]:(v store_v)list` o
    check (is_forall o concl)) THEN
  MATCH_MP_TAC MON1AUX_EvalM_Marray_update_gen THEN
  MAP_EVERY EXISTS_TAC [`TYPE:A->v->bool`; `l1:num`; `av:v list`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC MON1AUX_evaluate_Var_Short THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MON1AUX_ARRAY_REL_update_frame THEN
    ASM_REWRITE_TAC[]]);;

let EvalM_F_Marray_update_handle = prove
 (`!vname loc (TYPE:A->v->bool) (EXC_TYPE:E->v->bool) (H:REFS->hprop)
    (get_arr:REFS->A list) set_arr e rexp env n x xexp nexp.
     nsLookup (sem_env_v env) (Short vname) = SOME loc ==>
     ml_lookup_cons (Short (implode "Subscript")) env = SOME (0,ExnStamp 3) ==>
     (!refs x. get_arr (set_arr x refs) = x) ==>
     (!refs x. H (set_arr x refs) = H refs) ==>
     ml_Eval env nexp (ml_NUM n) ==>
     ml_Eval env rexp (EXC_TYPE e) ==>
     ml_Eval env xexp (TYPE x) ==>
     EvalM ro env st
       (Handle (App Aupdate [Var (Short vname); nexp; xexp])
          [(Pcon (SOME (Short (implode "Subscript"))) [],Raise rexp)])
       ((MONAD UNIT_TYPE EXC_TYPE) (Marray_update get_arr set_arr e n x))
       ((\refs. ARRAY_REL TYPE loc (get_arr refs) STAR H refs),
        (p:(FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)))`,
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN REWRITE_TAC[EvalM_def; REFS_PRED_def] THEN
  X_GEN_TAC `s:(FFI)state` THEN REWRITE_TAC[GSYM STAR_ASSOC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MON1AUX_ARRAY_open) THEN
  DISCH_THEN(X_CHOOSE_THEN `l1:num` (X_CHOOSE_THEN `av:v list` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `loc:v`)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MON1AUX_store_lookup_ARRAY_junk) THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[APPEND_NIL] o SPEC `[]:(v store_v)list` o
    check (is_forall o concl)) THEN
  MATCH_MP_TAC MON1AUX_EvalM_Marray_update_handle_gen THEN
  MAP_EVERY EXISTS_TAC [`TYPE:A->v->bool`; `l1:num`; `av:v list`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC MON1AUX_evaluate_Var_Short THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MON1AUX_ARRAY_REL_update_frame THEN
    ASM_REWRITE_TAC[]]);;


(* TODO: implement support for 2d arrays *)

let ARRAY2D_def = cake_def
  `ARRAY2D av (l:((v)list)list) =
     SEP_EXISTS fl. cf_ARRAY av fl STAR set_sep_cond (fl = FLAT l)`;;

let RARRAY2D_def = cake_def
  `RARRAY2D rv (l:((v)list)list) = SEP_EXISTS av. cf_REF rv av STAR ARRAY2D av l`;;

(* TODO: implement support for n-dimensional arrays? *)

(* translation of cases and cons terms *)

let MON1AUX_evaluate_Mat = prove
 (`!(s:(FFI)state) env e pes s1 v.
     evaluate s env [e] = (s1,Rval [v]) /\
     can_pmatch_all (sem_env_c env) (state_refs s1) (MAP FST pes) v ==>
     evaluate s env [Mat e pes] = evaluate_match s1 env v pes bind_exn_v`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [evaluate_def] THEN
  ASM_REWRITE_TAC[HD] THEN CAKE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[HD]);;

let MON1AUX_evaluate_match_first = prove
 (`!(s:(FFI)state) env v p e pes err bs.
     ALL_DISTINCT (pat_bindings p) /\
     pmatch (sem_env_c env) (state_refs s) p v [] = Match bs ==>
     evaluate_match s env v (CONS (p,e) pes) err =
     evaluate s (sem_env_v_fupd (combin_K (nsAppend (alist_to_ns bs) (sem_env_v env))) env) [e]`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [evaluate_def] THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[]);;

let MON1AUX_EvalM_Mat_gen = prove
 (`!ro env (st:REFS) exp pes (r2:REFS->REFS#(v list,v)result->bool)
    (H:(REFS->hprop)#((FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)))
    (a:B->v->bool) r1.
     ml_Eval env exp (a r1) /\
     (!v. a r1 v ==>
          ?env' x. (!s1:(FFI)state.
                      can_pmatch_all (sem_env_c env) (state_refs s1) (MAP FST pes) v /\
                      evaluate_match s1 env v pes bind_exn_v = evaluate s1 env' [x]) /\
                   EvalM ro env' st x r2 H) ==>
     EvalM ro env st (Mat exp pes) r2 H`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "h")) THEN
  REWRITE_TAC[EvalM_def] THEN X_GEN_TAC `s:(FFI)state` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:(FFI)state` o MATCH_MP MON1AUX_Eval_evaluate o
    check (MON1AUX_head_is "ml_Eval" o concl)) THEN
  DISCH_THEN(X_CHOOSE_THEN `v1:v` (X_CHOOSE_THEN `junk:(v store_v)list`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ev")))) THEN
  REMOVE_THEN "h" (MP_TAC o SPEC `v1:v`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `env':v sem_env` (X_CHOOSE_THEN `x:exp`
    (CONJUNCTS_THEN2 (LABEL_TAC "m") MP_TAC))) THEN
  REWRITE_TAC[EvalM_def] THEN
  DISCH_THEN(MP_TAC o SPEC `state_refs_fupd (combin_K (APPEND (state_refs s) junk)) (s:(FFI)state)`) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC(GEN_ALL REFS_PRED_append) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s2:(FFI)state` (X_CHOOSE_THEN `res:(v list,v)result`
    (X_CHOOSE_THEN `st2:REFS` (X_CHOOSE_THEN `ck:num` STRIP_ASSUME_TAC)))) THEN
  REMOVE_THEN "ev" (X_CHOOSE_TAC `ck1:num` o SPEC `ck:num`) THEN
  MAP_EVERY EXISTS_TAC [`s2:(FFI)state`; `res:(v list,v)result`; `st2:REFS`; `ck1:num`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`state_clock_fupd (combin_K ck1) (s:(FFI)state)`; `env:v sem_env`; `exp:exp`;
      `pes:(pat#exp)list`;
      `state_clock_fupd (combin_K ck) (state_refs_fupd (combin_K (APPEND (state_refs s) junk))
         (s:(FFI)state))`;
      `v1:v`] MON1AUX_evaluate_Mat) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC(GEN_ALL REFS_PRED_FRAME_remove_junk) THEN
    EXISTS_TAC `junk:(v store_v)list` THEN ASM_REWRITE_TAC[]]);;

let MON1AUX_Mat_INL_match = prove
 (`!(s:(FFI)state) env vars vals x.
     ALL_DISTINCT (pats_bindings (MAP Pvar vars)) /\ LENGTH vals = LENGTH vars ==>
     can_pmatch_all (sem_env_c env) (state_refs s) (MAP FST [(Pcon NONE (MAP Pvar vars),x)])
       (Conv NONE vals) /\
     evaluate_match s env (Conv NONE vals) [(Pcon NONE (MAP Pvar vars),x)] bind_exn_v =
     evaluate s (ml_write_list (ZIP vars vals) env) [x]`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[MAP; FST; can_pmatch_all_def; pmatch_def; LENGTH_MAP;
      ml_pmatch_list_MAP_Pvar; distinctness "match_result"];
    MP_TAC(ISPECL [`s:(FFI)state`; `env:v sem_env`; `Conv NONE vals`;
      `Pcon NONE (MAP Pvar vars)`; `x:exp`; `[]:(pat#exp)list`; `bind_exn_v`;
      `REVERSE (ZIP vars vals):(mlstring#v)list`] MON1AUX_evaluate_match_first) THEN
    ASM_SIMP_TAC[pat_bindings_def; pmatch_def; LENGTH_MAP; ml_pmatch_list_MAP_Pvar;
      APPEND_NIL; GSYM write_list_thm]]);;

let MON1AUX_Mat_INR_match = prove
 (`!(s:(FFI)state) env ps name vals t vars x.
     ALL_DISTINCT (MAP (SND o SND o SND) ps) /\ good_cons_env ps env /\
     MEM (name,vars,x,t) ps /\ LENGTH vals = LENGTH vars ==>
     can_pmatch_all (sem_env_c env) (state_refs s)
       (MAP FST (MAP (\(name,vars,x,t:stamp). (Pcon (SOME name) (MAP Pvar vars),x)) ps))
       (Conv (SOME t) vals) /\
     evaluate_match s env (Conv (SOME t) vals)
       (MAP (\(name,vars,x,t:stamp). (Pcon (SOME name) (MAP Pvar vars),x)) ps) bind_exn_v =
     evaluate s (ml_write_list (ZIP vars vals) env) [x]`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`ps:((mlstring,mlstring)id#mlstring list#exp#stamp)list`;
    `env:v sem_env`; `name:(mlstring,mlstring)id`; `vars:mlstring list`; `x:exp`;
    `t:stamp`; `name:(mlstring,mlstring)id`; `vars:mlstring list`; `x:exp`; `t:stamp`]
    TR2AUX_good_cons_env_MEM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!name' vars' x'.
      MEM (name',vars',x',t) (ps:((mlstring,mlstring)id#mlstring list#exp#stamp)list) ==>
      vars' = vars` (LABEL_TAC "uniq") THENL
   [MP_TAC(ISPECL [`(name,vars,x,t):(mlstring,mlstring)id#mlstring list#exp#stamp`;
      `ps:((mlstring,mlstring)id#mlstring list#exp#stamp)list`] MEM_APPEND_DECOMPOSE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_MESON_TAC[TR2AUX_Mat_cases_stamp];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[can_pmatch_all_EVERY; MAP_MAP_o] THEN
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
     [USE_THEN "uniq" MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`n':(mlstring,mlstring)id`; `x':exp`] THEN
      FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    SIMP_TAC[ASSUME `LENGTH (vals:v list) = LENGTH (vars:mlstring list)`;
      ml_pmatch_list_MAP_Pvar; distinctness "match_result"];
    ALL_TAC] THEN
  REMOVE_THEN "uniq" (K ALL_TAC) THEN
  MP_TAC(ISPECL [`(name,vars,x,t):(mlstring,mlstring)id#mlstring list#exp#stamp`;
    `ps:((mlstring,mlstring)id#mlstring list#exp#stamp)list`] MEM_APPEND_DECOMPOSE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `l1:((mlstring,mlstring)id#mlstring list#exp#stamp)list`
    (X_CHOOSE_THEN `l2:((mlstring,mlstring)id#mlstring list#exp#stamp)list`
      (LABEL_TAC "dec"))) THEN
  USE_THEN "dec" (fun dec -> ASSUME_TAC(CONJUNCT1(MATCH_MP TR2AUX_Mat_cases_stamp (CONJ
    (ASSUME `ALL_DISTINCT (MAP (SND o SND o SND)
       (ps:((mlstring,mlstring)id#mlstring list#exp#stamp)list))`) dec)))) THEN
  SUBGOAL_THEN
   `evaluate_match (s:(FFI)state) env (Conv (SOME t) vals)
      (MAP (\(name,vars,x,t:stamp). (Pcon (SOME name) (MAP Pvar vars),x)) ps) bind_exn_v =
    evaluate_match s env (Conv (SOME t) vals)
      (CONS (Pcon (SOME name) (MAP Pvar vars),x)
        (MAP (\(name,vars,x,t:stamp). (Pcon (SOME name) (MAP Pvar vars),x)) l2)) bind_exn_v`
    SUBST1_TAC THENL
   [USE_THEN "dec" (fun th -> GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th]) THEN
    REWRITE_TAC[MAP_APPEND; MAP] THEN SIMP[] THEN
    MATCH_MP_TAC evaluate_match_MAP THEN
    MAP_EVERY EXISTS_TAC [`name:(mlstring,mlstring)id`; `vars:mlstring list`; `x:exp`;
      `ps:((mlstring,mlstring)id#mlstring list#exp#stamp)list`] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [USE_THEN "dec" SUBST1_TAC THEN REWRITE_TAC[APPEND_EQ_NIL; NOT_CONS_NIL];
      USE_THEN "dec" SUBST1_TAC THEN
      REWRITE_TAC[SUBSET; IN_SET_OF_LIST; MEM_APPEND] THEN MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:(FFI)state`; `env:v sem_env`; `Conv (SOME t) vals`;
    `Pcon (SOME name) (MAP Pvar vars)`; `x:exp`;
    `MAP (\(name,vars,x,t:stamp). (Pcon (SOME name) (MAP Pvar vars),x))
       (l2:((mlstring,mlstring)id#mlstring list#exp#stamp)list)`; `bind_exn_v`;
    `REVERSE (ZIP vars vals):(mlstring#v)list`] MON1AUX_evaluate_match_first) THEN
  ASM_REWRITE_TAC[pat_bindings_def; pmatch_def] THEN CAKE_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[TR2AUX_same_type_refl; same_ctor_def; LENGTH_MAP; ml_pmatch_list_MAP_Pvar;
    APPEND_NIL; GSYM write_list_thm]);;

let MON1AUX_EvalM_Mat_cases_INL = prove
 (`!ro (st:REFS) (a:B->v->bool) (r1:B) env exp (r2:REFS->REFS#(v list,v)result->bool)
    (H:(REFS->hprop)#((FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list))) vars x.
     ml_Eval env exp (a r1) /\
     ALL_DISTINCT (pats_bindings (MAP Pvar vars)) /\
     (!v. a r1 v ==>
          ?vals. v = Conv NONE vals /\ LENGTH vals = LENGTH vars /\
                 EvalM ro (ml_write_list (ZIP vars vals) env) st x r2 H) ==>
     EvalM ro env st (Mat exp [(Pcon NONE (MAP Pvar vars),x)]) r2 H`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC MON1AUX_EvalM_Mat_gen THEN
  MAP_EVERY EXISTS_TAC [`a:B->v->bool`; `r1:B`] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `v:v` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `v:v`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `vals:v list` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`ml_write_list (ZIP vars vals) env`; `x:exp`] THEN
  ASM_REWRITE_TAC[] THEN GEN_TAC THEN MATCH_MP_TAC MON1AUX_Mat_INL_match THEN
  ASM_REWRITE_TAC[]);;

let MON1AUX_EvalM_Mat_cases_INR = prove
 (`!ro (st:REFS) (a:B->v->bool) (r1:B) env exp (r2:REFS->REFS#(v list,v)result->bool)
    (H:(REFS->hprop)#((FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list))) ps.
     ml_Eval env exp (a r1) /\
     ALL_DISTINCT (MAP (SND o SND o SND) ps) /\ good_cons_env ps env /\
     (!v. a r1 v ==>
          ?name vals t vars x.
            v = Conv (SOME t) vals /\ MEM (name,vars,x,t) ps /\
            LENGTH vals = LENGTH vars /\
            EvalM ro (ml_write_list (ZIP vars vals) env) st x r2 H) ==>
     EvalM ro env st
       (Mat exp (MAP (\(name,vars,(x:exp),(t:stamp)). (Pcon (SOME name) (MAP Pvar vars),x)) ps))
       r2 H`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC MON1AUX_EvalM_Mat_gen THEN
  MAP_EVERY EXISTS_TAC [`a:B->v->bool`; `r1:B`] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `v:v` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `v:v`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `name:(mlstring,mlstring)id` (X_CHOOSE_THEN `vals:v list`
    (X_CHOOSE_THEN `t:stamp` (X_CHOOSE_THEN `vars:mlstring list` (X_CHOOSE_THEN `x:exp`
      STRIP_ASSUME_TAC))))) THEN
  MAP_EVERY EXISTS_TAC [`ml_write_list (ZIP vars vals) env`; `x:exp`] THEN
  ASM_REWRITE_TAC[] THEN GEN_TAC THEN MATCH_MP_TAC MON1AUX_Mat_INR_match THEN
  EXISTS_TAC `name:(mlstring,mlstring)id` THEN ASM_REWRITE_TAC[]);;

(* HOL4: IMP_EvalM_Mat_cases.  As for IMP_Eval_Mat_cases (ml_translator), the *)
(* vacuous name and t of the INL branch get the types of the INR branch, and  *)
(* HOL4 write_list (ZIP (vars,vals)) is ml_write_list (ZIP vars vals).         *)

let IMP_EvalM_Mat_cases = prove
 (CASE_TERM `!(st:REFS) (a:B->v->bool) (r1:B) env exp (r2:REFS->REFS#(v list,v)result->bool) y.
     ml_Eval env exp (a r1) /\
     (match y with
        INL (vars,exp) ->
          ALL_DISTINCT (pats_bindings (MAP Pvar vars)) /\
          (!v. a r1 v ==>
               ?(name:(mlstring,mlstring)id) vals (t:stamp).
                 v = Conv NONE vals /\
                 LENGTH vals = LENGTH vars /\
                 EvalM ro (ml_write_list (ZIP vars vals) env) st exp r2
                   (H:(REFS->hprop)#((FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list))))
      | INR ps ->
          ALL_DISTINCT (MAP (SND o SND o SND) ps) /\
          good_cons_env ps env /\
          (!v. a r1 v ==>
               ?name vals t vars exp.
                 v = Conv (SOME t) vals /\
                 MEM (name,vars,exp,t) ps /\
                 LENGTH vals = LENGTH vars /\
                 EvalM ro (ml_write_list (ZIP vars vals) env) st exp r2 H)) ==>
     EvalM ro env st (Mat exp (Mat_cases y)) r2 H`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `y:(mlstring list#exp)+((mlstring,mlstring)id#mlstring list#exp#stamp)list`
    (case_info_of_tyname "sum").ci_nchotomy) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `p:mlstring list#exp` SUBST1_TAC)
    (X_CHOOSE_THEN `ps:((mlstring,mlstring)id#mlstring list#exp#stamp)list` SUBST1_TAC))
  THENL
   [PAIR_CASES_ON `p:mlstring list#exp` THEN
    CAKE_REWRITE_TAC[ml_Mat_cases_def] THEN REWRITE_TAC[EXISTS_SIMP] THEN
    MATCH_ACCEPT_TAC MON1AUX_EvalM_Mat_cases_INL;
    CAKE_REWRITE_TAC[ml_Mat_cases_def] THEN
    MATCH_ACCEPT_TAC MON1AUX_EvalM_Mat_cases_INR]);;


(* Run *)

let EvalSt_def = cake_def
  `EvalSt env (st:REFS) exp (P:v->bool)
     (H:(REFS->hprop)#((1->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list))) <=>
     !(s:(1)state). REFS_PRED H st s ==>
       ?s2 res st2 ck.
         evaluate (state_clock_fupd (combin_K ck) s) env [exp] = (s2,Rval [res]) /\
         P res /\ REFS_PRED_FRAME T H (st,s) (st2,s2)`;;

let MON1AUX_Mem_IN_store2heap_aux = prove
 (`!refs k n. n < LENGTH refs ==> cf_Mem (k + n) (EL n refs) IN store2heap_aux k refs`,
  LIST_INDUCT_TAC THENL [REWRITE_TAC[LENGTH; LT]; ALL_TAC] THEN REWRITE_TAC[LENGTH] THEN
  X_GEN_TAC `k:num` THEN INDUCT_TAC THEN
  REWRITE_TAC[store2heap_aux_def; EL; HD; TL; IN_INSERT; ADD_CLAUSES; LT_SUC] THEN
  DISCH_TAC THEN DISJ2_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`k + 1`; `n:num`] o check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[ARITH_RULE `(k + 1) + n = SUC (k + n)`]);;

let LENGTH_Mem_IN_store2heap = prove
 (`!refs n. n < LENGTH refs ==> (cf_Mem n (EL n refs)) IN (store2heap refs)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[store2heap_def] THEN
  MP_TAC(SPECL [`refs:(v store_v)list`; `0`; `n:num`] MON1AUX_Mem_IN_store2heap_aux) THEN
  ASM_REWRITE_TAC[ADD_CLAUSES]);;

let REFS_PRED_FRAME_partial_frame_rule = prove
 (`!(s:(FFI)state) refs'.
     (!F'. F' (st2heap p s) ==>
           (F' STAR cf_GC) (st2heap p (state_refs_fupd (combin_K refs') s))) ==>
     ?junk. refs' = APPEND (state_refs s) junk`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o SPEC `\h:heap. h = st2heap p (s:(FFI)state)`) THEN
  REWRITE_TAC[STAR_def; SPLIT_def] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:heap` (X_CHOOSE_THEN `w:heap` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `!x. x IN st2heap p (s:(FFI)state) ==>
                    x IN st2heap p (state_refs_fupd (combin_K refs') s)` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. n < LENGTH (state_refs (s:(FFI)state)) ==>
                    n < LENGTH (refs':(v store_v)list) /\ EL n refs' = EL n (state_refs s)`
    ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `cf_Mem n (EL n (state_refs (s:(FFI)state))) IN store2heap refs'`
      ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `cf_Mem n (EL n (state_refs (s:(FFI)state)))`) THEN
      REWRITE_TAC[st2heap_def; IN_UNION; Mem_NOT_IN_ffi2heap; state_INFO.ri_accfupds;
        K_THM] THEN
      ASM_SIMP_TAC[LENGTH_Mem_IN_store2heap];
      ASM_MESON_TAC[store2heap_IN_EL; store2heap_IN_LENGTH]];
    ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (state_refs (s:(FFI)state)) <= LENGTH (refs':(v store_v)list)`
    ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `LENGTH (refs':(v store_v)list)`) THEN
    ASM_REWRITE_TAC[LT_REFL];
    ALL_TAC] THEN
  EXISTS_TAC `DROP (LENGTH (state_refs (s:(FFI)state))) (refs':(v store_v)list)` THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM(ISPECL [`LENGTH (state_refs (s:(FFI)state))`;
    `refs':(v store_v)list`] TAKE_DROP)] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[LIST_EQ] THEN ASM_SIMP_TAC[LENGTH_TAKE; EL_TAKE]);;

let EvalSt_to_Eval = prove
 (`EvalSt env (st:REFS) exp P ((\s. set_sep_emp),
     (p:(1->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list))) ==> ml_Eval env exp P`,
  REWRITE_TAC[EvalSt_def; ml_Eval_def; REFS_PRED_def; EMP_STAR_GC; SAT_GC] THEN
  DISCH_TAC THEN X_GEN_TAC `refs:(v store_v)list` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `state_refs_fupd (combin_K refs) (ml_empty_state:(1)state)`) THEN
  DISCH_THEN(X_CHOOSE_THEN `s2:(1)state` (X_CHOOSE_THEN `res:v` (X_CHOOSE_THEN `st2:REFS`
    (X_CHOOSE_THEN `ck:num` STRIP_ASSUME_TAC)))) THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[REFS_PRED_FRAME_def; EMP_STAR_GC] o
    check (MON1AUX_head_is "REFS_PRED_FRAME" o concl)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `refs2:(v store_v)list`)
    (ASSUME_TAC o CONJUNCT2 o CONJUNCT2)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `s2:(1)state`)) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP REFS_PRED_FRAME_partial_frame_rule o
    check (is_forall o concl)) THEN
  REWRITE_TAC[state_INFO.ri_accfupds; K_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `junk:(v store_v)list` SUBST_ALL_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MON1AUX_refs_fupd_fupd]) THEN
  MAP_EVERY EXISTS_TAC [`res:v`; `junk:(v store_v)list`] THEN
  ASM_REWRITE_TAC[eval_rel_def; state_INFO.ri_accfupds; K_THM] THEN
  MAP_EVERY EXISTS_TAC [`ck:num`; `state_clock (ml_empty_state:(1)state)`] THEN
  ASM_REWRITE_TAC[state_update_clock_id]);;

let handle_mult_def = cake_def
  `(handle_mult [] exp1 (ename:mlstring) = exp1) /\
   (handle_mult (CONS (v2:string) v3) exp1 ename =
      Handle exp1 [(Pvar (implode "e"),Con (SOME (Short ename)) [Var (Short (implode "e"))])])`;;

let evaluate_handle_mult_Rval = prove
 (`!cons_names exp1 ename res (s:(FFI)state) s2 env.
     evaluate s env [exp1] = (s2,Rval res) ==>
     evaluate s env [handle_mult cons_names exp1 ename] = (s2,Rval res)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[handle_mult_def] THEN
  MESON_TAC[MON1AUX_evaluate_Handle_Rval]);;

let evaluate_handle_mult_Rabort = prove
 (`!cons_names exp1 ename res (s:(FFI)state) s2 env.
     evaluate s env [exp1] = (s2,Rerr (Rabort res)) ==>
     evaluate s env [handle_mult cons_names exp1 ename] = (s2,Rerr (Rabort res))`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[handle_mult_def] THEN
  MESON_TAC[MON1AUX_evaluate_Handle_Rabort]);;

(* EvalM_to_EvalSt *)

let handle_all_def = cake_def
  `handle_all exp (ename:mlstring) =
     Handle exp [(Pvar (implode "e"),Con (SOME (Short ename)) [Var (Short (implode "e"))])]`;;

let evaluate_handle_all_Rval = prove
 (`!exp1 ename res (s:(FFI)state) s2 env.
     evaluate s env [exp1] = (s2,Rval res) ==>
     evaluate s env [handle_all exp1 ename] = (s2,Rval res)`,
  REWRITE_TAC[handle_all_def] THEN MESON_TAC[MON1AUX_evaluate_Handle_Rval]);;

let evaluate_handle_all_Rabort = prove
 (`!exp1 ename res (s:(FFI)state) s2 env.
     evaluate s env [exp1] = (s2,Rerr (Rabort res)) ==>
     evaluate s env [handle_all exp1 ename] = (s2,Rerr (Rabort res))`,
  REWRITE_TAC[handle_all_def] THEN MESON_TAC[MON1AUX_evaluate_Handle_Rabort]);;

let MON1AUX_evaluate_Con_one = prove
 (`!(s:(FFI)state) env cn e s1 r stamp.
     ml_lookup_cons cn env = SOME (1,stamp) /\ evaluate s env [e] = (s1,r) ==>
     evaluate s env [Con (SOME cn) [e]] =
     (s1,match r with Rval vs -> Rval [Conv (SOME stamp) (REVERSE vs)] | Rerr err -> Rerr err)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ml_lookup_cons_def] THEN STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [evaluate_def] THEN
  ASM_REWRITE_TAC[do_con_check_def; build_conv_def; LENGTH; REVERSE; APPEND] THEN
  CAKE_REWRITE_TAC[] THEN REWRITE_TAC[ARITH_RULE `SUC 0 = 1`] THEN
  QCASES_ON "r" THEN CAKE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  CAKE_REWRITE_TAC[] THEN REWRITE_TAC[REVERSE; APPEND]);;

let evaluate_Success_CONS = prove
 (`evaluate (s:(FFI)state) env [e] = (s',Rval [v]) ==>
   ml_lookup_cons (Short (implode "M_success")) env =
     SOME (1,TypeStamp (implode "M_success") exc_stamp) ==>
   evaluate s env [Con (SOME (Short (implode "M_success"))) [e]] =
     (s',Rval [Conv (SOME (TypeStamp (implode "M_success") exc_stamp)) [v]])`,
  REPEAT DISCH_TAC THEN
  MP_TAC(ISPECL [`s:(FFI)state`; `env:v sem_env`;
    `Short (implode "M_success"):(mlstring,mlstring)id`; `e:exp`; `s':(FFI)state`;
    `Rval [v]:(v list,v)result`; `TypeStamp (implode "M_success") exc_stamp`]
    MON1AUX_evaluate_Con_one) THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN REWRITE_TAC[REVERSE; APPEND]);;

let evaluate_Success_CONS_err = prove
 (`evaluate (s:(FFI)state) env [e] = (s',Rerr v) ==>
   ml_lookup_cons (Short (implode "M_success")) env =
     SOME (1,TypeStamp (implode "M_success") exc_stamp) ==>
   evaluate s env [Con (SOME (Short (implode "M_success"))) [e]] = (s',Rerr v)`,
  REPEAT DISCH_TAC THEN
  MP_TAC(ISPECL [`s:(FFI)state`; `env:v sem_env`;
    `Short (implode "M_success"):(mlstring,mlstring)id`; `e:exp`; `s':(FFI)state`;
    `Rerr v:(v list,v)result`; `TypeStamp (implode "M_success") exc_stamp`]
    MON1AUX_evaluate_Con_one) THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN REWRITE_TAC[REVERSE; APPEND]);;

(* For the dynamic store initialisation *)
(* It is not possible to use register_type here... *)

let EXC_TYPE_aux_def = cake_def
  `(EXC_TYPE_aux stamp (a:A->v->bool) (b:B->v->bool) (M_failure x_2) v <=>
      ?v2_1. v = Conv (SOME (TypeStamp (implode "M_failure") stamp)) [v2_1] /\ b x_2 v2_1) /\
   (EXC_TYPE_aux stamp a b (M_success x_1) v <=>
      ?v1_1. v = Conv (SOME (TypeStamp (implode "M_success") stamp)) [v1_1] /\ a x_1 v1_1)`;;

let EvalM_to_EvalSt = prove
 (`!exc_stamp (TYPE:A->v->bool) (EXN_TYPE:B->v->bool) (x:REFS->(A,B)exc#REFS) exp
    (H:(REFS->hprop)#((1->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)))
    init_st env.
     EvalM T env init_st exp (MONAD TYPE EXN_TYPE x) H ==>
     ml_lookup_cons (Short (implode "M_success")) env =
       SOME (1,TypeStamp (implode "M_success") exc_stamp) ==>
     ml_lookup_cons (Short (implode "M_failure")) env =
       SOME (1,TypeStamp (implode "M_failure") exc_stamp) ==>
     EvalSt env init_st
       (handle_all (Con (SOME (Short (implode "M_success"))) [exp]) (implode "M_failure"))
       (EXC_TYPE_aux exc_stamp TYPE EXN_TYPE (ml_monadBase_run x init_st)) H`,
  REPEAT GEN_TAC THEN REWRITE_TAC[EvalM_def; EvalSt_def] THEN REPEAT DISCH_TAC THEN
  X_GEN_TAC `s:(1)state` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:(1)state` o check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s2:(1)state` (X_CHOOSE_THEN `res:(v list,v)result`
    (X_CHOOSE_THEN `st2:REFS` (X_CHOOSE_THEN `ck:num` STRIP_ASSUME_TAC)))) THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[MON1AUX_MONAD_THM] o
    check (MON1AUX_head_is "MONAD" o concl)) THEN
  STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `res:(v list,v)result`)) THENL
   [MAP_EVERY EXISTS_TAC [`s2:(1)state`;
      `Conv (SOME (TypeStamp (implode "M_success") exc_stamp)) [v]`; `st2:REFS`; `ck:num`] THEN
    ASM_REWRITE_TAC[ml_monadBase_run_def; EXC_TYPE_aux_def; injectivity "v";
      injectivity "option"; CONS_11; UNWIND_THM1] THEN
    MATCH_MP_TAC evaluate_handle_all_Rval THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] (GEN_ALL evaluate_Success_CONS)) THEN ASM_REWRITE_TAC[];
    MAP_EVERY EXISTS_TAC [`s2:(1)state`;
      `Conv (SOME (TypeStamp (implode "M_failure") exc_stamp)) [v]`; `st2:REFS`; `ck:num`] THEN
    ASM_REWRITE_TAC[ml_monadBase_run_def; EXC_TYPE_aux_def; injectivity "v";
      injectivity "option"; CONS_11; UNWIND_THM1] THEN
    REWRITE_TAC[handle_all_def] THEN
    MP_TAC(ISPECL [`state_clock_fupd (combin_K ck) (s:(1)state)`; `env:v sem_env`;
      `Con (SOME (Short (implode "M_success"))) [exp]`; `implode "e"`;
      `Con (SOME (Short (implode "M_failure"))) [Var (Short (implode "e"))]`;
      `s2:(1)state`; `v:v`] MON1AUX_evaluate_Handle_Pvar) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] (GEN_ALL evaluate_Success_CONS_err)) THEN
      EXISTS_TAC `exc_stamp:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`s2:(1)state`; `ml_write (implode "e") v env`;
      `Short (implode "M_failure"):(mlstring,mlstring)id`; `Var (Short (implode "e"))`;
      `s2:(1)state`; `Rval [v]:(v list,v)result`;
      `TypeStamp (implode "M_failure") exc_stamp`] MON1AUX_evaluate_Con_one) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC `ml_lookup_cons (Short (implode "M_failure")) env =
          SOME (1,TypeStamp (implode "M_failure") exc_stamp)` THEN
        REWRITE_TAC[ml_lookup_cons_def; ml_write_def] THEN SIMP[];
        MATCH_MP_TAC MON1AUX_evaluate_Var_Short THEN
        REWRITE_TAC[ml_write_def] THEN SIMP[nsLookup_nsBind]];
      DISCH_THEN SUBST1_TAC THEN CAKE_REWRITE_TAC[] THEN REWRITE_TAC[REVERSE; APPEND]]]);;

let EvalSt_Let_Fun = prove
 (`EvalSt (ml_write vname (Closure env xv fexp) env) (st:REFS) exp P H ==>
   EvalSt env st (Let (SOME vname) (Fun xv fexp) exp) P H`,
  SUBGOAL_THEN `!s:(1)state. evaluate s env [Let (SOME vname) (Fun xv fexp) exp] =
                 evaluate s (ml_write vname (Closure env xv fexp) env) [exp]` ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`s:(1)state`; `env:v sem_env`; `SOME vname:mlstring option`;
      `Fun xv fexp`; `exp:exp`; `s:(1)state`; `Closure env xv fexp`]
      MON1AUX_evaluate_Let_Rval) THEN
    REWRITE_TAC[MON1AUX_evaluate_Fun; MON1AUX_nsOptBind_write];
    ASM_REWRITE_TAC[EvalSt_def]]);;

let nsAppend_build_rec_env_eq_lemma = prove
 (CASE_TERM `!(funs:(mlstring#mlstring#exp)list) (funs0:(mlstring#mlstring#exp)list) (cl_env:v sem_env)
    (v0:(mlstring,mlstring,v)namespace) v1.
     nsAppend (ITLIST (\fxe env'. match fxe with
                 (f,x,e) -> nsBind f (Recclosure cl_env funs0 f) env') funs v1) v0 =
     ITLIST (\fxe env'. match fxe with
               (f,x,e) -> nsBind f (Recclosure cl_env funs0 f) env') funs (nsAppend v1 v0)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ITLIST] THEN
  PAIR_CASES_ON `h:mlstring#mlstring#exp` THEN CAKE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[nsAppend_nsBind]);;

let nsAppend_build_rec_env_eq = prove
 (`!funs cl_env v0 (v1:(mlstring,mlstring,v)namespace).
     nsAppend (build_rec_env funs cl_env v1) v0 = build_rec_env funs cl_env (nsAppend v1 v0)`,
  REWRITE_TAC[build_rec_env_def; nsAppend_build_rec_env_eq_lemma]);;

let merge_build_rec_env = prove
 (`!funs env1 env0.
     merge_env (sem_env_REC (build_rec_env funs (merge_env env1 env0) (sem_env_v env1))
                            (sem_env_c env1)) env0 =
     sem_env_v_fupd (combin_K (build_rec_env funs (merge_env env1 env0)
                          (sem_env_v (merge_env env1 env0)))) (merge_env env1 env0)`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [merge_env_def] THEN
  REWRITE_TAC[sem_env_component_equality] THEN SIMP[] THEN
  REWRITE_TAC[nsAppend_build_rec_env_eq; merge_env_def] THEN SIMP[]);;

let EvalSt_Letrec_Fun = prove
 (CASE_TERM `!funs env exp (st:REFS) P H.
     ALL_DISTINCT (MAP (\fxe. match fxe with (f,x,e) -> f) funs) ==>
     EvalSt (sem_env_REC (build_rec_env funs env (sem_env_v env)) (sem_env_c env)) st exp P H ==>
     EvalSt env st (Letrec funs exp) P H`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `!s:(1)state. evaluate s env [Letrec funs exp] =
     evaluate s (sem_env_REC (build_rec_env funs env (sem_env_v env)) (sem_env_c env)) [exp]`
    ASSUME_TAC THENL
   [GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [evaluate_def] THEN ASM_REWRITE_TAC[] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[sem_env_component_equality] THEN SIMP[];
    ASM_REWRITE_TAC[EvalSt_def]]);;

let merge_env_bind_empty = prove
 (`merge_env (sem_env_REC (Bind [] []) (Bind [] [])) env = env`,
  REWRITE_TAC[merge_env_def; GSYM nsEmpty_def; nsAppend_nsEmpty] THEN
  REWRITE_TAC[sem_env_component_equality] THEN SIMP[]);;

let ml_monad_translator_Bind_list_to_write = prove
 (`merge_env (sem_env_REC (Bind (CONS (vname,v) binds) []) (Bind [] [])) env =
   ml_write vname v (merge_env (sem_env_REC (Bind binds []) (Bind [] [])) env)`,
  REWRITE_TAC[merge_env_def; ml_write_def; sem_env_component_equality] THEN SIMP[] THEN
  QCASES_ON "sem_env_v (env:v sem_env)" THEN
  REWRITE_TAC[nsAppend_def; nsBind_def; APPEND]);;

let evaluate_Var_IMP = prove
 (`evaluate (s1:(FFI)state) env [Var (Short name)] = (s2,Rval [v]) ==>
   nsLookup (sem_env_v env) (Short name) = SOME v`,
  REWRITE_TAC[evaluate_def] THEN TOP_CASE_TAC THEN
  REWRITE_TAC[PAIR_EQ; distinctness "result"; injectivity "result"; CONS_11;
    injectivity "option"] THEN MESON_TAC[]);;

let evaluate_Var_same_state = prove
 (`evaluate (s1:(FFI)state) env [Var (Short name)] = (s2,res) <=>
   evaluate s1 env [Var (Short name)] = (s2,res) /\ s2 = s1`,
  REWRITE_TAC[evaluate_def] THEN TOP_CASE_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  MESON_TAC[]);;

let MON1AUX_alloc_heap = prove
 (`!(G:hprop) (Hn:hprop) p (s:(FFI)state) junk newcells.
     G (st2heap p s) /\
     Hn (store2heap_aux (LENGTH (APPEND (state_refs s) junk)) newcells) ==>
     (Hn STAR G STAR cf_GC)
       (st2heap p (state_refs_fupd (combin_K (APPEND (APPEND (state_refs s) junk) newcells)) s))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(G STAR cf_GC)
      (st2heap p (state_refs_fupd (combin_K (APPEND (state_refs s) junk)) (s:(FFI)state)))`
    ASSUME_TAC THENL
   [MATCH_MP_TAC STATE_APPEND_JUNK THEN ASM_REWRITE_TAC[with_same_refs]; ALL_TAC] THEN
  REWRITE_TAC[GSYM STAR_ASSOC] THEN MATCH_MP_TAC MON1AUX_STAR_I THEN
  MAP_EVERY EXISTS_TAC
   [`store2heap_aux (LENGTH (APPEND (state_refs (s:(FFI)state)) junk)) newcells`;
    `st2heap p (state_refs_fupd (combin_K (APPEND (state_refs s) junk)) (s:(FFI)state))`] THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[SPLIT_SYM] THEN REWRITE_TAC[STATE_SPLIT_REFS]);;

let MON1AUX_EvalSt_alloc_gen = prove
 (`!env (st:REFS) exp1 exp loc_name (P:v->bool) (H:REFS->hprop)
    (p:(1->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)) (NH:v->REFS->hprop).
     (!s:(1)state. ?newcells junk lv.
        (!ck. ?ck1. evaluate (state_clock_fupd (combin_K ck1) s) env [exp1] =
                    (state_clock_fupd (combin_K ck)
                       (state_refs_fupd (combin_K (APPEND (APPEND (state_refs s) junk) newcells)) s),
                     Rval [lv])) /\
        NH lv st (store2heap_aux (LENGTH (APPEND (state_refs s) junk)) newcells)) /\
     (!loc. EvalSt (ml_write loc_name loc env) st exp P ((\st. NH loc st STAR H st),p)) ==>
     EvalSt env st (Let (SOME loc_name) exp1 exp) P (H,p)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "alloc") (LABEL_TAC "body")) THEN
  REWRITE_TAC[EvalSt_def] THEN X_GEN_TAC `s:(1)state` THEN
  REWRITE_TAC[REFS_PRED_def] THEN DISCH_TAC THEN
  REMOVE_THEN "alloc" (X_CHOOSE_THEN `newcells:(v store_v)list`
    (X_CHOOSE_THEN `junk:(v store_v)list`
      (X_CHOOSE_THEN `lv:v` (CONJUNCTS_THEN2 (LABEL_TAC "ev") ASSUME_TAC))) o
    SPEC `s:(1)state`) THEN
  REMOVE_THEN "body" (MP_TAC o SPEC `lv:v`) THEN REWRITE_TAC[EvalSt_def; REFS_PRED_def] THEN
  DISCH_THEN(MP_TAC o SPEC `state_refs_fupd (combin_K (APPEND (APPEND (state_refs s) junk) newcells))
                              (s:(1)state)`) THEN
  ANTS_TAC THENL
   [MP_TAC(ISPECL [`(H:REFS->hprop) st STAR cf_GC`; `(NH:v->REFS->hprop) lv st`;
      `p:(1->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)`; `s:(1)state`;
      `junk:(v store_v)list`; `newcells:(v store_v)list`] MON1AUX_alloc_heap) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM STAR_ASSOC; GC_STAR_GC] THEN MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s2:(1)state` (X_CHOOSE_THEN `res:v` (X_CHOOSE_THEN `st2:REFS`
    (X_CHOOSE_THEN `ck:num` STRIP_ASSUME_TAC)))) THEN
  REMOVE_THEN "ev" (X_CHOOSE_TAC `ck1:num` o SPEC `ck:num`) THEN
  MAP_EVERY EXISTS_TAC [`s2:(1)state`; `res:v`; `st2:REFS`; `ck1:num`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`state_clock_fupd (combin_K ck1) (s:(1)state)`; `env:v sem_env`;
      `SOME loc_name:mlstring option`; `exp1:exp`; `exp:exp`;
      `state_clock_fupd (combin_K ck) (state_refs_fupd (combin_K (APPEND (APPEND (state_refs s) junk)
         newcells)) (s:(1)state))`; `lv:v`] MON1AUX_evaluate_Let_Rval) THEN
    ASM_REWRITE_TAC[MON1AUX_nsOptBind_write];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (MON1AUX_head_is "REFS_PRED_FRAME" o concl)) THEN
  REWRITE_TAC[REFS_PRED_FRAME_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fr")))) THEN
  REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `refs2:(v store_v)list` SUBST_ALL_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[state_INFO.ri_accfupds; K_THM; MON1AUX_refs_fupd_fupd]) THEN
  REWRITE_TAC[state_INFO.ri_accfupds; K_THM; MON1AUX_refs_fupd_fupd] THEN
  CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `F':hprop` THEN DISCH_TAC THEN
  REMOVE_THEN "fr" (MP_TAC o SPEC `F' STAR cf_GC`) THEN ANTS_TAC THENL
   [MP_TAC(ISPECL [`(H:REFS->hprop) st STAR F'`; `(NH:v->REFS->hprop) lv st`;
      `p:(1->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)`; `s:(1)state`;
      `junk:(v store_v)list`; `newcells:(v store_v)list`] MON1AUX_alloc_heap) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN MON1AUX_HPROP_AC_TAC;
    DISCH_TAC THEN
    SUBGOAL_THEN
     `(((H:REFS->hprop) st2 STAR F') STAR
       ((NH:v->REFS->hprop) lv st2 STAR cf_GC STAR cf_GC))
        (st2heap p (state_refs_fupd (combin_K refs2) (s:(1)state)))`
      (ACCEPT_TAC o MATCH_MP (GEN_ALL HPROP_TO_GC_R)) THEN
    MON1AUX_HPROP_AC_TAC]);;

let MON1AUX_clock_refs_comm = prove
 (`!ck refs (s:(FFI)state).
     state_refs_fupd (combin_K refs) (state_clock_fupd (combin_K ck) s) =
     state_clock_fupd (combin_K ck) (state_refs_fupd (combin_K refs) s)`,
  REWRITE_TAC[state_component_equality; state_INFO.ri_accfupds; K_THM]);;

let EvalSt_Opref = prove
 (`!exp get_ref_exp (get_ref:REFS->A) loc_name (TYPE:A->v->bool) (st_name:mlstring) env
    (H:REFS->hprop) P (st:REFS).
     ml_Eval env get_ref_exp (TYPE (get_ref st)) ==>
     (!loc. EvalSt (ml_write loc_name loc env) st exp P
              ((\st. REF_REL TYPE loc (get_ref st) STAR H st),
               (p:(1->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)))) ==>
     EvalSt env st (Let (SOME loc_name) (App Opref [get_ref_exp]) exp) P (H,p)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`env:v sem_env`; `st:REFS`; `App Opref [get_ref_exp]`; `exp:exp`;
    `loc_name:mlstring`; `P:v->bool`; `H:REFS->hprop`;
    `p:(1->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)`;
    `\loc (st:REFS). REF_REL (TYPE:A->v->bool) loc ((get_ref:REFS->A) st)`]
    MON1AUX_EvalSt_alloc_gen) THEN
  BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `s:(1)state` THEN
  FIRST_ASSUM(MP_TAC o ISPEC `s:(1)state` o MATCH_MP MON1AUX_Eval_evaluate o
    check (MON1AUX_head_is "ml_Eval" o concl)) THEN
  DISCH_THEN(X_CHOOSE_THEN `xv:v` (X_CHOOSE_THEN `junk:(v store_v)list` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`[Refv (xv:v)]`; `junk:(v store_v)list`;
    `Loc T (LENGTH (APPEND (state_refs (s:(1)state)) junk))`] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `ck:num` THEN FIRST_X_ASSUM(X_CHOOSE_TAC `ck1:num` o SPEC `ck:num` o
      check (is_forall o concl)) THEN
    EXISTS_TAC `ck1:num` THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP MON1AUX_evaluate_Opref th]) THEN
    REWRITE_TAC[state_INFO.ri_accfupds; K_THM; MON1AUX_clock_refs_comm;
      MON1AUX_refs_fupd_fupd];
    REWRITE_TAC[REF_REL_def; SEP_CLAUSES; SEP_EXISTS_THM] THEN EXISTS_TAC `xv:v` THEN
    ASM_REWRITE_TAC[cf_HCOND_EXTRACT; MON1AUX_store2heap_REF_SAT]]);;

let ml_monad_translator_EQ_def = cake_def
  `ml_monad_translator_EQ (x:A) y <=> x = y`;;

let MON1AUX_evaluate_Con_NONE_nil = prove
 (`!(s:(FFI)state) env. evaluate s env [Con NONE []] = (s,Rval [Conv NONE []])`,
  REWRITE_TAC[evaluate_def; do_con_check_def; build_conv_def; REVERSE] THEN
  CAKE_REWRITE_TAC[] THEN REWRITE_TAC[evaluate_def; REVERSE] THEN CAKE_REWRITE_TAC[]);;

let EvalSt_AllocEmpty = prove
 (`!exp (get_ref:REFS->A list) loc_name (TYPE:A->v->bool) (st_name:mlstring) env
    (H:REFS->hprop) P (st:REFS).
     ml_monad_translator_EQ (get_ref st) [] ==>
     (!loc. EvalSt (ml_write loc_name loc env) st exp P
              ((\st. RARRAY_REL TYPE loc (get_ref st) STAR H st),
               (p:(1->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)))) ==>
     EvalSt env st
       (Let (SOME loc_name) (App Opref [App AallocEmpty [Con NONE []]]) exp) P (H,p)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ml_monad_translator_EQ_def] THEN DISCH_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`env:v sem_env`; `st:REFS`; `App Opref [App AallocEmpty [Con NONE []]]`;
    `exp:exp`; `loc_name:mlstring`; `P:v->bool`; `H:REFS->hprop`;
    `p:(1->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)`;
    `\loc (st:REFS). RARRAY_REL (TYPE:A->v->bool) loc ((get_ref:REFS->A list) st)`]
    MON1AUX_EvalSt_alloc_gen) THEN
  BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `s:(1)state` THEN
  MAP_EVERY EXISTS_TAC [`[Varray []; Refv (Loc T (LENGTH (state_refs (s:(1)state))))]`;
    `[]:(v store_v)list`; `Loc T (LENGTH (APPEND (state_refs (s:(1)state)) [Varray []]))`] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `ck:num` THEN EXISTS_TAC `ck:num` THEN
    SUBGOAL_THEN
     `evaluate (state_clock_fupd (combin_K ck) (s:(1)state)) env [App AallocEmpty [Con NONE []]] =
      (state_refs_fupd (combin_K (APPEND (state_refs s) [Varray []])) (state_clock_fupd (combin_K ck) s),
       Rval [Loc T (LENGTH (state_refs s))])` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`state_clock_fupd (combin_K ck) (s:(1)state)`; `env:v sem_env`; `AallocEmpty`;
        `[Con NONE []]`; `state_clock_fupd (combin_K ck) (s:(1)state)`; `[Conv NONE []]`;
        `APPEND (state_refs (s:(1)state)) [Varray []]`;
        `state_ffi (state_clock_fupd (combin_K ck) (s:(1)state))`;
        `Rval (Loc T (LENGTH (state_refs (s:(1)state)))):(v,v)result`]
        MON1AUX_evaluate_App_Simple) THEN
      REWRITE_TAC[REVERSE; APPEND; MON1AUX_evaluate_Con_NONE_nil] THEN
      ANTS_TAC THENL
       [REWRITE_TAC[getOpClass_def] THEN CAKE_REWRITE_TAC[] THEN
        REWRITE_TAC[do_app_def; store_alloc_def; state_INFO.ri_accfupds; K_THM] THEN
        CAKE_REWRITE_TAC[];
        DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[list_result_def; with_same_ffi]];
      ALL_TAC] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP MON1AUX_evaluate_Opref th]) THEN
    REWRITE_TAC[state_INFO.ri_accfupds; K_THM; MON1AUX_clock_refs_comm;
      MON1AUX_refs_fupd_fupd; APPEND_NIL; GSYM APPEND_ASSOC; APPEND];
    REWRITE_TAC[RARRAY_REL_def; SEP_CLAUSES; SEP_EXISTS_THM] THEN EXISTS_TAC `[]:v list` THEN
    ASM_REWRITE_TAC[cf_HCOND_EXTRACT; ALL2; RARRAY_HPROP_SAT_EQ] THEN
    EXISTS_TAC `LENGTH (state_refs (s:(1)state))` THEN
    REWRITE_TAC[APPEND_NIL; LENGTH_APPEND; LENGTH; store2heap_aux_def] THEN
    REWRITE_TAC[ARITH_RULE `a + SUC 0 = a + 1`; ADD_0]]);;

let MON1AUX_ck_Aalloc = prove
 (`!(s:(FFI)state) env nexp xexp n xv s1 s2.
     (!ck. ?ck1. evaluate (state_clock_fupd (combin_K ck1) s) env [xexp] =
                 (state_clock_fupd (combin_K ck) s1,Rval [xv])) /\
     (!ck. ?ck1. evaluate (state_clock_fupd (combin_K ck1) s1) env [nexp] =
                 (state_clock_fupd (combin_K ck) s2,Rval [Litv (IntLit (&n))])) ==>
     !ck. ?ck1. evaluate (state_clock_fupd (combin_K ck1) s) env [App Aalloc [nexp; xexp]] =
       (state_clock_fupd (combin_K ck)
          (state_refs_fupd (combin_K (APPEND (state_refs s2) [Varray (REPLICATE n xv)])) s2),
        Rval [Loc T (LENGTH (state_refs s2))])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:(FFI)state`; `env:v sem_env`; `Aalloc`; `[nexp; xexp]:exp list`;
    `s2:(FFI)state`; `[xv; Litv (IntLit (&n))]`;
    `APPEND (state_refs (s2:(FFI)state)) [Varray (REPLICATE n xv)]`;
    `Rval (Loc T (LENGTH (state_refs (s2:(FFI)state)))):(v,v)result`]
    MON1AUX_ck_App_Simple) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[REVERSE; APPEND; MON1AUX_getOpClass_Simple; MON1AUX_do_app_Aalloc] THEN
    MATCH_MP_TAC MON1AUX_ck_two THEN EXISTS_TAC `s1:(FFI)state` THEN
    CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC[list_result_def] THEN MESON_TAC[]]);;

let EvalSt_Alloc = prove
 (`!exp nexp n xexp (x:A) (get_farray:REFS->A list) loc_name (TYPE:A->v->bool) env
    (H:REFS->hprop) P (st:REFS).
     ml_monad_translator_EQ (get_farray st) (REPLICATE n x) ==>
     ml_Eval env nexp (\v. v = Litv (IntLit (&n))) ==>
     ml_Eval env xexp (TYPE x) ==>
     (!loc. EvalSt (ml_write loc_name loc env) st exp P
              ((\st. ARRAY_REL TYPE loc (get_farray st) STAR H st),
               (p:(1->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)))) ==>
     EvalSt env st (Let (SOME loc_name) (App Aalloc [nexp; xexp]) exp) P (H,p)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ml_monad_translator_EQ_def] THEN REPEAT DISCH_TAC THEN
  MP_TAC(ISPECL [`env:v sem_env`; `st:REFS`; `App Aalloc [nexp; xexp]`; `exp:exp`;
    `loc_name:mlstring`; `P:v->bool`; `H:REFS->hprop`;
    `p:(1->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)`;
    `\loc (st:REFS). ARRAY_REL (TYPE:A->v->bool) loc ((get_farray:REFS->A list) st)`]
    MON1AUX_EvalSt_alloc_gen) THEN
  BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `s:(1)state` THEN
  FIRST_ASSUM(MP_TAC o ISPEC `s:(1)state` o MATCH_MP MON1AUX_Eval_evaluate o
    check (fun th -> MON1AUX_head_is "ml_Eval" (concl th) && free_in `xexp:exp` (concl th))) THEN
  DISCH_THEN(X_CHOOSE_THEN `xv:v` (X_CHOOSE_THEN `junk1:(v store_v)list` STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(MP_TAC o ISPEC `state_refs_fupd (combin_K (APPEND (state_refs s) junk1)) (s:(1)state)` o
    MATCH_MP MON1AUX_Eval_evaluate o
    check (fun th -> MON1AUX_head_is "ml_Eval" (concl th) && free_in `nexp:exp` (concl th))) THEN
  DISCH_THEN(X_CHOOSE_THEN `nv:v` (X_CHOOSE_THEN `junk2:(v store_v)list`
    (STRIP_ASSUME_TAC o BETA_RULE))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `nv:v`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[state_INFO.ri_accfupds; K_THM; MON1AUX_refs_fupd_fupd;
    GSYM APPEND_ASSOC]) THEN
  MAP_EVERY EXISTS_TAC [`[Varray (REPLICATE n (xv:v))]`; `APPEND junk1 junk2:(v store_v)list`;
    `Loc T (LENGTH (APPEND (state_refs (s:(1)state)) (APPEND junk1 junk2)))`] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`s:(1)state`; `env:v sem_env`; `nexp:exp`; `xexp:exp`; `n:num`; `xv:v`;
      `state_refs_fupd (combin_K (APPEND (state_refs s) junk1)) (s:(1)state)`;
      `state_refs_fupd (combin_K (APPEND (state_refs s) (APPEND junk1 junk2))) (s:(1)state)`]
      MON1AUX_ck_Aalloc) THEN
    ASM_REWRITE_TAC[state_INFO.ri_accfupds; K_THM; MON1AUX_refs_fupd_fupd];
    REWRITE_TAC[ARRAY_REL_def; SEP_CLAUSES; SEP_EXISTS_THM] THEN
    EXISTS_TAC `REPLICATE n (xv:v)` THEN
    ASM_REWRITE_TAC[cf_HCOND_EXTRACT; MON1AUX_store2heap_ARRAY_SAT;
      LIST_REL_REPLICATE_same]]);;

let ml_monad_translator_Eval_lookup_var = prove
 (`!env vname xv (x:A) (TYPE:A->v->bool).
     nsLookup (sem_env_v env) (Short vname) = SOME xv ==>
     (ml_Eval env (Var (Short vname)) (TYPE x) <=> TYPE x xv)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[TR2AUX_Eval_Var_nsLookup] THEN ASM_REWRITE_TAC[] THEN
  CAKE_REWRITE_TAC[]);;

let nsBind_to_write = prove
 (`sem_env_REC (nsBind name v env1) env2 = ml_write name v (sem_env_REC env1 env2)`,
  REWRITE_TAC[ml_write_def; sem_env_component_equality] THEN SIMP[]);;

let nsLookup_write_simp = prove
 (`nsLookup (sem_env_v (ml_write name1 exp env)) (Short name2) =
   if name1 = name2 then SOME exp else nsLookup (sem_env_v env) (Short name2)`,
  REWRITE_TAC[ml_write_def] THEN SIMP[] THEN COND_CASES_TAC THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[nsLookup_nsBind];
    MATCH_MP_TAC(CONJUNCT2 nsLookup_nsBind) THEN
    REWRITE_TAC[injectivity "id"] THEN ASM_MESON_TAC[]]);;

let sem_env_same_components = prove
 (`sem_env_REC (sem_env_v env) (sem_env_c env) = (env:v sem_env)`,
  REWRITE_TAC[sem_env_component_equality] THEN SIMP[]);;

let lookup_cons_write_simp = prove
 (`ml_lookup_cons name2 (ml_write name1 exp env) = ml_lookup_cons name2 env`,
  REWRITE_TAC[ml_lookup_cons_def; ml_write_def] THEN SIMP[]);;

let lookup_cons_build_rec_env_simp = prove
 (`ml_lookup_cons name2
     (sem_env_REC (build_rec_env exp env (sem_env_v env)) (sem_env_c env)) =
   ml_lookup_cons name2 env`,
  REWRITE_TAC[ml_lookup_cons_def] THEN SIMP[]);;

let LOOKUP_ASSUM_SIMP = end_itlist CONJ
  [nsBind_to_write; Eval_Var_SIMP; ml_monad_translator_Eval_lookup_var;
   nsLookup_write_simp; sem_env_same_components; lookup_cons_write_simp;
   lookup_cons_build_rec_env_simp];;

let EVAL_T_F = prove
 (`(ml_CONTAINER TRUE <=> T) /\ (ml_CONTAINER FALSE <=> F)`,
  REWRITE_TAC[ml_CONTAINER_def; TRUE_def; FALSE_def]);;

let EVAL_PRECONDITION_T = prove
 (`ml_PRECONDITION T <=> T`,
  REWRITE_TAC[ml_PRECONDITION_def]);;

let H_STAR_emp = prove
 (`(H:(A->bool)->bool) STAR set_sep_emp = H`,
  REWRITE_TAC[SEP_CLAUSES]);;

let ml_monad_translator_H_STAR_TRUE = prove
 (`((H:(A->bool)->bool) STAR set_sep_cond T = H) /\ (set_sep_cond T STAR H = H)`,
  REWRITE_TAC[SEP_CLAUSES]);;

let PreImp_PRECONDITION_T_SIMP = prove
 (`ml_PreImp T a /\ ml_PRECONDITION T <=> a`,
  REWRITE_TAC[ml_PreImp_def; ml_PRECONDITION_def]);;

let ml_monad_translator_IF_T = prove
 (`(if T then x else y) = (x:A)`,
  REWRITE_TAC[]);;

let ml_monad_translator_IF_F = prove
 (`(if F then x else y) = (y:A)`,
  REWRITE_TAC[]);;

let ml_monad_translator_IMP_EQ_T = prove
 (`a ==> (a <=> T)`,
  REWRITE_TAC[]);;

let BETA_PAIR_THM = prove
 (`(\(x,y). (f:A->B->C) x y) (x,y) = (\x y. f x y) x y`,
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REFL_TAC);;
