(* ========================================================================= *)
(* pan_itreeEquivProof: port of HOL4                                         *)
(* pancake/proofs/pan_itreeEquivProofScript.sml (CakeML v3479).  Proof of    *)
(* the correspondence between the functional big-step semantics and the      *)
(* itree semantics for Pancake.                                              *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - HOL4's types ptree and fst are written out, as in pan_itreeProps.ml;    *)
(*   FUNPOW Tau n t is ITER n Tau t; HOL4 div is pan_itreeSem_div; HOL4's    *)
(*   overloaded eval, evaluate, empty_locals, ... are the panSem constants    *)
(*   on states (pan_eval, pan_evaluate, ...) and the pan_itreeSem ones on    *)
(*   bstates (pan_itreeSem_eval, ...).                                       *)
(* - Local helpers that are not HOL4 theorems are PITRAUX_.                  *)
(* ========================================================================= *)

needs "basis/pure/mlstring.ml";;
needs "hol4/llist.ml";;
needs "hol4/lprefix_lub.ml";;
needs "hol4/itreeTau.ml";;
needs "pancake/semantics/panSem.ml";;
needs "pancake/semantics/panProps.ml";;
needs "pancake/semantics/pan_itreeSem.ml";;
needs "pancake/semantics/pan_itreeProps.ml";;

prioritize_num();;
type_invention_error := true;;

let evaluate_invariant_oracle = prove
 (`!p (t:(A,B)pan_state) res st.
     pan_evaluate (p,t) = (res,st)
     ==> ffi_state_oracle (pan_state_ffi st) = ffi_state_oracle (pan_state_ffi t)`,
  MESON_TAC[evaluate_invariants]);;

let explode_eq_implode = prove
 (`!x y. explode x = y <=> x = implode y`,
  MESON_TAC[explode_implode; implode_explode]);;

let PITRAUX_ltree_bind_Ret = prove
 (`!(fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B)
    (X:((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
        (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree) n r.
     ltree fs X = ITER n Tau (itree_Ret r) ==>
     !k. ltree fs (itree_bind X k) =
         ITER n Tau (ltree (FST fs,SND (comp_ffi fs X)) (k r)) /\
         comp_ffi fs (itree_bind X k) = comp_ffi (FST fs,SND (comp_ffi fs X)) (k r) /\
         trace_prefix fs (itree_bind X k) =
         LAPPEND (trace_prefix fs X) (trace_prefix (FST fs,SND (comp_ffi fs X)) (k r))`,
  REPEAT STRIP_TAC THENL
   [ASM_REWRITE_TAC[ltree_bind; FUNPOW_Tau_bind; itree_bind_thm; o_THM];
    MATCH_MP_TAC comp_ffi_bind THEN ASM_MESON_TAC[];
    MATCH_MP_TAC trace_prefix_bind_append THEN ASM_MESON_TAC[]]);;
let PITRAUX_Tau_ITER = prove
 (`!n (x:(A,E,R)itree). Tau (ITER n Tau x) = ITER (SUC n) Tau x`,
  REWRITE_TAC[ITER]);;
(* rewrite with the bind facts of every assumption ltree fs X = ITER n Tau (Ret r) *)
let PITRAUX_BIND_TAC : tactic = fun (asl,w as g) ->
  let ths = mapfilter (fun (_,th) -> MATCH_MP PITRAUX_ltree_bind_Ret th) asl in
  REWRITE_TAC ths g;;
let PITRAUX_EVAL_SIMPS () =
  [PITRAUX_Tau_ITER; ITER_ADD; LAPPEND_NIL_2ND; FUNPOW_Tau_bind; o_THM;
   PITRAUX_Tau_FUNPOW_Ret; FUNPOW_Ret_simp2; LAPPEND_ASSOC;
   mrec_h_handle_call_ret_lemma; mrec_h_handle_deccall_ret_lemma;
   kvar_defs2; empty_locals_defs];;
let PITRAUX_EVAL_STEP_TAC =
  IMP_RES_TAC evaluate_invariant_oracle THEN FULL_RES_TAC THEN RFS[] THEN
  PITRAUX_BIND_TAC THEN SIMP(PITRAUX_EVAL_SIMPS()) THEN
  REPEAT(CASE_TAC THEN SIMP(PITRAUX_EVAL_SIMPS()));;
(* the forward simulation: a run that does not time out gives a          *)
(* terminating oracle run of the itree, with the same final ffi state and *)
(* the same I/O trace (nondiv_evaluate, evaluate_imp_nondiv and            *)
(* evaluate_nondiv_trace_eq below are its consequences)                   *)

let PITRAUX_evaluate_ltree = prove
 (`!p (s:(A,B)pan_state) res t.
     pan_evaluate (p,s) = (res,t) /\ ~(res = SOME pan_TimeOut)
     ==> (?n. ltree (ffi_state_oracle (pan_state_ffi s),ffi_state_ffi_state (pan_state_ffi s))
                    (mrec h_prog (h_prog (p,pan_itreeSem_bst s))) =
              ITER n Tau (itree_Ret (INR (res,pan_itreeSem_bst t)))) /\
         SND (comp_ffi (ffi_state_oracle (pan_state_ffi s),ffi_state_ffi_state (pan_state_ffi s))
                       (mrec h_prog (h_prog (p,pan_itreeSem_bst s)))) =
         ffi_state_ffi_state (pan_state_ffi t) /\
         llist_fromList (ffi_state_io_events (pan_state_ffi t)) =
         LAPPEND (llist_fromList (ffi_state_io_events (pan_state_ffi s)))
           (trace_prefix (ffi_state_oracle (pan_state_ffi s),ffi_state_ffi_state (pan_state_ffi s))
              (mrec h_prog (h_prog (p,pan_itreeSem_bst s))))`,
  REC_IND_TAC pan_evaluate_ind THEN REPEAT CONJ_TAC THEN
   REPEAT(GEN_TAC ORELSE DISCH_THEN STRIP_ASSUME_TAC) THEN
   QPAT_X_ASSUM "pan_evaluate _ = _" (MP_TAC o ONCE_REWRITE_RULE[pan_evaluate_def]) THEN
   REWRITE_TAC[mrec_prog_nonrec; mrec_If; mrec_ExtCall] THEN
   ONCE_REWRITE_TAC[mrec_While] THEN
   DISCH_TAC THEN GVS([COND_CASE_EQ; pan_sh_mem_load_def; pan_sh_mem_store_def;
                       call_FFI_def; explode_eq_implode; MULT_2] @ all_case_eqs()) THEN
   REPEAT(PAIRARG_TAC THEN GVS[]) THEN
   GVS[kvar_defs2; empty_locals_defs; pan_dec_clock_def; ITER; LAPPEND_NIL_2ND] THEN
   REPEAT(CASE_TAC THEN GVS[LAPPEND_NIL_2ND]) THEN
   TRY(QEXISTS_TAC "0" THEN SIMP[ITER] THEN NO_TAC) THEN
   PITRAUX_EVAL_STEP_TAC THEN PITRAUX_EVAL_STEP_TAC THEN PITRAUX_EVAL_STEP_TAC THEN
   TRY(SIMP[pan_itreeSem_bst_def; GSYM LAPPEND_fromList] THEN NO_TAC));;

(* HOL4 proves nondiv_evaluate by induction on n and on the program; here  *)
(* it follows from PITRAUX_evaluate_ltree for the state with clock k       *)

let nondiv_evaluate = prove
 (`!(s:(A,B)pan_state) p n r k res t.
     ltree (ffi_state_oracle (pan_state_ffi s),ffi_state_ffi_state (pan_state_ffi s))
           (mrec h_prog (h_prog (p,pan_itreeSem_bst s))) = ITER n Tau (itree_Ret (INR r)) /\
     pan_evaluate (p,pan_state_clock_fupd (K k) s) = (res,t) /\
     ~(res = SOME pan_TimeOut)
     ==> res = FST r /\ pan_itreeSem_bst t = SND r /\
         ffi_state_ffi_state (pan_state_ffi t) =
         SND (comp_ffi (ffi_state_oracle (pan_state_ffi s),
                        ffi_state_ffi_state (pan_state_ffi s))
                       (mrec h_prog (h_prog (p,pan_itreeSem_bst s))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`p:(A)panLang_prog`; `pan_state_clock_fupd (K k) (s:(A,B)pan_state)`;
                 `res:((A)pan_result)option`; `t:(A,B)pan_state`]
                PITRAUX_evaluate_ltree) THEN
  ASM_REWRITE_TAC[] THEN SIMP[] THEN STRIP_TAC THEN GVS[]);;

let nondiv_evaluate' = prove
 (`!(fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B) (s:(A,B)pan_state)
    p n r k res t.
     ltree fs (mrec h_prog (h_prog (p,pan_itreeSem_bst s))) = ITER n Tau (itree_Ret (INR r)) /\
     pan_evaluate (p,pan_state_clock_fupd (K k) s) = (res,t) /\
     ~(res = SOME pan_TimeOut) /\
     FST fs = ffi_state_oracle (pan_state_ffi s) /\
     SND fs = ffi_state_ffi_state (pan_state_ffi s)
     ==> res = FST r /\ pan_itreeSem_bst t = SND r /\
         ffi_state_ffi_state (pan_state_ffi t) =
         SND (comp_ffi (ffi_state_oracle (pan_state_ffi s),
                        ffi_state_ffi_state (pan_state_ffi s))
                       (mrec h_prog (h_prog (p,pan_itreeSem_bst s))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC nondiv_evaluate THEN
  MAP_EVERY EXISTS_TAC [`n:num`; `k:num`] THEN
  ASM_MESON_TAC[PAIR]);;

let evaluate_imp_nondiv = prove
 (`!p (s:(A,B)pan_state) res t.
     pan_evaluate (p,s) = (res,t) /\ ~(res = SOME pan_TimeOut)
     ==> ?n. ltree (ffi_state_oracle (pan_state_ffi s),ffi_state_ffi_state (pan_state_ffi s))
                   (mrec h_prog (h_prog (p,pan_itreeSem_bst s))) =
             ITER n Tau (itree_Ret (INR (res,pan_itreeSem_bst t)))`,
  MESON_TAC[PITRAUX_evaluate_ltree]);;

(* the remaining goals of an induction on n: the induction hypothesis      *)
(* !m. m <= b ==> .. at the count k of the assumption ltree _ _ = ITER k   *)
(* Tau (Ret ..) that mentions pat                                          *)

let PITRAUX_IH_AT_TAC (pat:term) : tactic = fun (asl,w as g) ->
  let is_target th =
    let c = concl th in
    is_eq c && can (find_term (fun t -> t = pat)) c &&
    (try fst(dest_const(fst(strip_comb(rhs c)))) = "ITER" with Failure _ -> false) in
  let th = snd(find (fun (_,th) -> is_target th) asl) in
  let k = hd(snd(strip_comb(rhs(concl th)))) in
  (FIRST_X_ASSUM(fun ih -> let c = concl ih in
     if is_forall c && type_of(fst(dest_forall c)) = `:num`
     then MP_TAC(SPEC k ih) else failwith "PITRAUX_IH_AT_TAC") THEN
   ANTS_TAC THENL [ARITH_TAC; ASM_MESON_TAC[]]) g;;

(* HOL4 proves nondiv_not_timeout by induction on n and on the program;    *)
(* here by induction on n with the rules of nondiv_INR (pan_itreeProps)    *)

let nondiv_not_timeout = prove
 (`!(fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B) p (s:(A)bstate) n res t.
     ltree fs (mrec h_prog (h_prog (p,s))) = ITER n Tau (itree_Ret (INR (res,t)))
     ==> ~(res = SOME pan_TimeOut)`,
  SUBGOAL_THEN
   `!n (fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B) p (s:(A)bstate) res t.
      ltree fs (mrec h_prog (h_prog (p,s))) = ITER n Tau (itree_Ret (INR (res,t)))
      ==> ~(res = SOME pan_TimeOut)`
   (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  GEN_TAC THEN GEN_TAC THEN QCASES_ON "p" THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[mrec_prog_nonrec; mrec_If; mrec_ExtCall] THEN
  TRY(GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV) [mrec_While]) THEN
  REPEAT(TOP_CASE_TAC THEN SIMP[]) THEN REPEAT STRIP_TAC THEN
  GVS_ASM (PITRAUX_NONDIV_RULES()) THEN
  REPEAT(FULL_CASE_TAC THEN GVS_ASM (PITRAUX_NONDIV_RULES())) THEN SIMP[] THEN
  PITRAUX_IH_AT_TAC `SOME (pan_TimeOut:(A)pan_result)`);;

(* a run that does not time out can be made to end with any clock *)

let PITRAUX_evaluate_any_clock = prove
 (`!c (s:(A,B)pan_state) r t k.
     pan_evaluate (c,s) = (r,t) /\ ~(r = SOME pan_TimeOut)
     ==> ?k'. pan_evaluate (c,pan_state_clock_fupd (K k') s) =
              (r,pan_state_clock_fupd (K k) t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(A)panLang_prog`; `s:(A,B)pan_state`; `r:((A)pan_result)option`;
                 `t:(A,B)pan_state`] (GEN_ALL evaluate_min_clock)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `k0:num`) THEN
  MP_TAC(ISPECL [`c:(A)panLang_prog`; `pan_state_clock_fupd (K k0) (s:(A,B)pan_state)`;
                 `r:((A)pan_result)option`;
                 `pan_state_clock_fupd (K 0) (t:(A,B)pan_state)`; `k:num`]
                pan_evaluate_add_clock_eq) THEN
  ASM_REWRITE_TAC[] THEN SIMP[] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* From a terminating oracle run back to a run of evaluate.                  *)
(* ------------------------------------------------------------------------- *)

(* Results of mrec h_prog under ltree are never INL (nondiv_INR) *)

let PITRAUX_nondiv_not_INL = prove
 (`!(fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B) p (s:(A)bstate) n x.
     ~(ltree fs (mrec h_prog (h_prog (p,s))) = ITER n Tau (itree_Ret (INL x)))`,
  MESON_TAC[nondiv_INR; distinctness "sum"]);;

let PITRAUX_IMP_RULES () =
  PITRAUX_nondiv_not_INL :: kvar_defs2 :: empty_locals_defs :: explode_eq_implode ::
  PITRAUX_NONDIV_RULES();;

(* the induction hypothesis !m. m (<|<=) b ==> !p s res t. ltree (oracle, *)
(* ffi state of s) (mrec h_prog (h_prog (p,pan_itreeSem_bst s))) = ITER m Tau (Ret     *)
(* (INR (res,t))) ==> C p s res t, applied to the assumption ltree _      *)
(* (mrec h_prog (h_prog (q,_))) = ITER k Tau (Ret (INR (r,y))) about the *)
(* program q, at the state x (by default the x of pan_itreeSem_bst x in the           *)
(* assumption; the other assumptions must turn the IH's premise into the *)
(* assumption): adds C q x r y                                           *)

let PITRAUX_SUBRUN_TAC (q:term) (xo:term option) : tactic = fun (asl,w as g) ->
  let is_run th =
    let c = concl th in
    is_eq c &&
    (try let l = lhs c in fst(dest_const(fst(strip_comb l))) = "ltree" &&
         fst(dest_pair(rand(rand(rand l)))) = q
     with Failure _ -> false) &&
    (try fst(dest_const(fst(strip_comb(rhs c)))) = "ITER" with Failure _ -> false) in
  let th = snd(find (fun (_,th) -> is_run th) asl) in
  let c = concl th in
  let k = hd(snd(strip_comb(rhs c))) in
  let qx = rand(rand(rand(lhs c))) in
  let x = match xo with Some x -> x | None -> rand(snd(dest_pair qx)) in
  let ry = rand(rand(rand(rhs c))) in
  let r,y = dest_pair ry in
  (FIRST_ASSUM(fun ih -> let c = concl ih in
     if is_forall c && type_of(fst(dest_forall c)) = `:num`
     then MP_TAC(SPEC k ih) else failwith "PITRAUX_SUBRUN_TAC") THEN
   ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
   DISCH_THEN(MP_TAC o SPECL [q; x; r; y]) THEN
   ANTS_TAC THENL
    [FIRST_X_ASSUM(MP_TAC o check (fun th' -> concl th' = c)) THEN
     ASM_REWRITE_TAC[] THEN SIMP[];
     ALL_TAC] THEN
   DISCH_TAC) g;;


(* a leaf step of PITRAUX_ltree_imp_evaluate: the run with clock 1 does   *)
(* not time out, and nondiv_evaluate identifies it with the itree run     *)

let PITRAUX_LEAF_IMP_TAC : tactic =
  DISCH_TAC THEN QEXISTS_TAC "SUC 0" THEN
  W(fun (_,w) -> let ev = lhs(fst(dest_conj(snd(dest_exists w)))) in
                 MP_TAC(ISPEC ev PAIR_SURJECTIVE)) THEN
  DISCH_THEN(X_CHOOSE_THEN `r0:((A)pan_result)option`
   (X_CHOOSE_THEN `t0:(A,B)pan_state` ASSUME_TAC)) THEN
  SUBGOAL_THEN `~(r0 = SOME (pan_TimeOut:(A)pan_result))` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o ONCE_REWRITE_RULE[pan_evaluate_def]) THEN DISCH_TAC THEN
    GVS(all_case_eqs() @ [ONELINE nb_op_def; pan_sh_mem_load_def; pan_sh_mem_store_def;
        pan_empty_locals_def; kvar_defs; pan_dec_clock_def; call_FFI_def; COND_CASE_EQ;
        pan_eval_upd_clock_eq; opt_mmap_eval_upd_clock_eq1]);
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> if is_eq(concl th) &&
                          (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "ltree"
                           with Failure _ -> false)
                       then MP_TAC th else failwith "") THEN
  DISCH_THEN(fun itr -> FIRST_ASSUM(fun eq ->
    if is_eq(concl eq) && (try fst(dest_const(fst(strip_comb(lhs(concl eq))))) =
                               "pan_evaluate" with Failure _ -> false)
    then MP_TAC(MATCH_MP nondiv_evaluate (CONJ itr (CONJ eq
           (ASSUME `~(r0 = SOME (pan_TimeOut:(A)pan_result))`))))
    else failwith "") THEN
    FIRST_ASSUM(fun eq -> if is_eq(concl eq) && (try fst(dest_const(fst(strip_comb(lhs(concl eq))))) =
                               "pan_evaluate" with Failure _ -> false)
                          then MP_TAC(MATCH_MP evaluate_invariant_oracle eq) else failwith "")) THEN
  SIMP[] THEN REPEAT STRIP_TAC THEN TRY(QEXISTS_TAC "t0") THEN ASM_MESON_TAC[];;

(* the itree assumption ltree _ (mrec h_prog (h_prog (C,pan_itreeSem_bst s))) = _ back *)
(* into the goal (for PITRAUX_LEAF_IMP_TAC after splits)                  *)

let PITRAUX_UNDISCH_ITREE_TAC : tactic =
  FIRST_X_ASSUM(fun th -> let c = concl th in
    if is_eq c && (try fst(dest_const(fst(strip_comb(lhs c)))) = "ltree" &&
                       fst(dest_const(fst(strip_comb(rand(lhs c))))) = "mrec"
                   with Failure _ -> false)
    then MP_TAC th else failwith "PITRAUX_UNDISCH_ITREE_TAC");;

(* the Dec step: the body runs in the state with the new local *)

let PITRAUX_IMP_DEC_TAC =
  DISCH_TAC THEN QCASES_ON "pan_eval (s:(A,B)pan_state) a2" THEN
  TRY(RENAME1 "pan_eval s a2 = SOME v0" THEN ASM_CASES_TAC `a1 = shape_of (v0:(A)pan_v)`) THEN
  TRY(PITRAUX_UNDISCH_ITREE_TAC THEN PITRAUX_LEAF_IMP_TAC THEN NO_TAC) THEN
  QPAT_X_ASSUM "ltree _ _ = _" (fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
  REWRITE_TAC[mrec_prog_nonrec] THEN ASM_SIMP_TAC[eval_bst] THEN SIMP[] THEN
  DISCH_TAC THEN GVS_ASM (PITRAUX_IMP_RULES()) THEN
  PITRAUX_SUBRUN_TAC `a3:(A)panLang_prog` None THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `k1:num` (X_CHOOSE_THEN `t1:(A,B)pan_state` STRIP_ASSUME_TAC)) THEN
  QEXISTS_TAC "k1" THEN ONCE_REWRITE_TAC[pan_evaluate_def] THEN
  PITRAUX_BIND_TAC THEN RFS[pan_eval_upd_clock_eq] THEN GVS[];;

(* the run fact pan_evaluate (q,_) = (r,t) of the assumptions, made to end *)
(* with clock k (PITRAUX_evaluate_any_clock): adds ?k'. pan_evaluate      *)
(* (q, clock k' state) = (r, t with clock k)                               *)

let PITRAUX_ANY_CLOCK_TAC (q:term) (k:term) : tactic =
  FIRST_ASSUM(fun eq ->
    let c = concl eq in
    if is_eq c && (try fst(dest_const(fst(strip_comb(lhs c)))) = "pan_evaluate" &&
                       fst(dest_pair(rand(lhs c))) = q with Failure _ -> false)
    then let r = fst(dest_pair(rhs c)) in
         MP_TAC(SPEC k (MATCH_MP PITRAUX_evaluate_any_clock
           (CONJ eq (EQT_ELIM(SIMP_CONV[option_DISTINCT; injectivity "option";
                                        distinctness "pan_result"]
                       (mk_neg(mk_eq(r,`SOME (pan_TimeOut:(A)pan_result)`))))))))
    else failwith "PITRAUX_ANY_CLOCK_TAC");;

(* the Seq step: c1, then c2 from the state c1 left *)

let PITRAUX_IMP_SEQ_TAC =
  DISCH_TAC THEN
  QPAT_X_ASSUM "ltree _ _ = _" (fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
  REWRITE_TAC[mrec_prog_nonrec] THEN SIMP[] THEN
  DISCH_TAC THEN GVS_ASM (PITRAUX_IMP_RULES()) THEN
  REPEAT(FULL_CASE_TAC THEN GVS_ASM (PITRAUX_IMP_RULES())) THEN
  PITRAUX_SUBRUN_TAC `a0:(A)panLang_prog` None THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `k1:num` (X_CHOOSE_THEN `t1:(A,B)pan_state` STRIP_ASSUME_TAC)) THEN
  FIRST
   [QEXISTS_TAC "k1" THEN ONCE_REWRITE_TAC[pan_evaluate_def] THEN
    PITRAUX_BIND_TAC THEN RFS[] THEN GVS[] THEN NO_TAC;
    PITRAUX_SUBRUN_TAC `a1:(A)panLang_prog` (Some `t1:(A,B)pan_state`) THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `k2:num` (X_CHOOSE_THEN `t2:(A,B)pan_state`
      STRIP_ASSUME_TAC)) THEN
    PITRAUX_ANY_CLOCK_TAC `a0:(A)panLang_prog` `k2:num` THEN SIMP[] THEN
    DISCH_THEN(X_CHOOSE_TAC `k3:num`) THEN
    QEXISTS_TAC "k3" THEN ONCE_REWRITE_TAC[pan_evaluate_def] THEN
    PITRAUX_BIND_TAC THEN RFS[] THEN PITRAUX_BIND_TAC THEN RFS[] THEN GVS[]];;

(* a step with one sub-run: unfold, decompose, the IH for the body q *)

let PITRAUX_IMP_ONE_TAC (qs:term list) =
  QPAT_X_ASSUM "ltree _ _ = _" (fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
  REWRITE_TAC[mrec_prog_nonrec; mrec_If] THEN ASM_SIMP_TAC[eval_bst] THEN SIMP[] THEN
  DISCH_TAC THEN GVS_ASM (PITRAUX_IMP_RULES()) THEN
  FIRST (map (fun q -> PITRAUX_SUBRUN_TAC q None) qs) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `k1:num` (X_CHOOSE_THEN `t1:(A,B)pan_state` STRIP_ASSUME_TAC)) THEN
  QEXISTS_TAC "k1" THEN ONCE_REWRITE_TAC[pan_evaluate_def] THEN
  PITRAUX_BIND_TAC THEN RFS[pan_eval_upd_clock_eq] THEN GVS[];;

(* the If step *)

let PITRAUX_IMP_IF_TAC =
  DISCH_TAC THEN QCASES_ON "pan_eval (s:(A,B)pan_state) a0" THEN
  TRY(RENAME1 "pan_eval s a0 = SOME v0" THEN QCASES_ON "v0" THEN
      TRY(RENAME1 "pan_eval s a0 = SOME (pan_Val w0)" THEN QCASES_ON "w0" THEN
          RENAME1 "pan_eval s a0 = SOME (pan_Val (Word w1))" THEN
          ASM_CASES_TAC `w1 = word 0:A word`)) THEN
  TRY(PITRAUX_UNDISCH_ITREE_TAC THEN PITRAUX_LEAF_IMP_TAC THEN NO_TAC) THEN
  PITRAUX_IMP_ONE_TAC [`a1:(A)panLang_prog`; `a2:(A)panLang_prog`];;

(* the While step: the body with clock k - 1, then the loop again *)

let PITRAUX_IMP_WHILE_TAC =
  DISCH_TAC THEN QCASES_ON "pan_eval (s:(A,B)pan_state) a0" THEN
  TRY(RENAME1 "pan_eval s a0 = SOME v0" THEN QCASES_ON "v0" THEN
      TRY(RENAME1 "pan_eval s a0 = SOME (pan_Val w0)" THEN QCASES_ON "w0" THEN
          RENAME1 "pan_eval s a0 = SOME (pan_Val (Word w1))" THEN
          ASM_CASES_TAC `w1 = word 0:A word`)) THEN
  TRY(PITRAUX_UNDISCH_ITREE_TAC THEN PITRAUX_LEAF_IMP_TAC THEN NO_TAC) THEN
  QPAT_X_ASSUM "ltree _ _ = _" (fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
  ONCE_REWRITE_TAC[mrec_While] THEN ASM_SIMP_TAC[eval_bst] THEN SIMP[] THEN
  DISCH_TAC THEN GVS_ASM (PITRAUX_IMP_RULES()) THEN
  REPEAT(FULL_CASE_TAC THEN GVS_ASM (PITRAUX_IMP_RULES())) THEN
  PITRAUX_SUBRUN_TAC `a1:(A)panLang_prog` None THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `k1:num` (X_CHOOSE_THEN `t1:(A,B)pan_state` STRIP_ASSUME_TAC)) THEN
  FIRST
   [QEXISTS_TAC "SUC k1" THEN ONCE_REWRITE_TAC[pan_evaluate_def] THEN
    PITRAUX_BIND_TAC THEN RFS[pan_eval_upd_clock_eq; pan_dec_clock_def; SUC_SUB1] THEN
    GVS[] THEN NO_TAC;
    PITRAUX_SUBRUN_TAC `While a0 a1:(A)panLang_prog` (Some `t1:(A,B)pan_state`) THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `k2:num` (X_CHOOSE_THEN `t2:(A,B)pan_state`
      STRIP_ASSUME_TAC)) THEN
    PITRAUX_ANY_CLOCK_TAC `a1:(A)panLang_prog` `k2:num` THEN SIMP[] THEN
    DISCH_THEN(X_CHOOSE_TAC `k3:num`) THEN
    QEXISTS_TAC "SUC k3" THEN ONCE_REWRITE_TAC[pan_evaluate_def] THEN
    PITRAUX_BIND_TAC THEN RFS[pan_eval_upd_clock_eq; pan_dec_clock_def; SUC_SUB1] THEN
    GVS[]];;

(* PITRAUX_SUBRUN_TAC for the sub-run on a program other than q0, at the  *)
(* state x of its pan_itreeSem_bst x                                       *)

let PITRAUX_SUBRUN_OTHER_TAC (q0:term) : tactic = fun (asl,w as g) ->
  let is_run th =
    let c = concl th in
    is_eq c &&
    (try let l = lhs c in fst(dest_const(fst(strip_comb l))) = "ltree" &&
         let q,st = dest_pair(rand(rand(rand l))) in
         is_var q && not (q = q0) && fst(dest_const(rator st)) = "pan_itreeSem_bst"
     with Failure _ -> false) &&
    (try fst(dest_const(fst(strip_comb(rhs c)))) = "ITER" with Failure _ -> false) in
  let th = snd(find (fun (_,th) -> is_run th) asl) in
  let q = fst(dest_pair(rand(rand(rand(lhs(concl th)))))) in
  PITRAUX_SUBRUN_TAC q None g;;

(* the Call and DecCall steps: the callee with clock k - 1, then possibly *)
(* the handler (Call) or the continuation program (DecCall)             *)

let PITRAUX_IMP_CALL_TAC (rw:thm) =
  DISCH_TAC THEN
  W(fun (asl,w) ->
     let c = rand(lhs(fst(dest_conj(snd(strip_exists w))))) in
     let p = fst(dest_pair c) in
     let args = snd(strip_comb p) in
     let argexps = el (length args - (if fst(dest_const(fst(strip_comb p))) = "DecCall"
                                       then 2 else 1)) args in
     let fname = el (length args - (if fst(dest_const(fst(strip_comb p))) = "DecCall"
                                     then 3 else 2)) args in
     QCASES_ON ("OPT_MMAP (pan_eval (s:(A,B)pan_state)) " ^ string_of_term argexps) THEN
     TRY(RENAME1 "OPT_MMAP (pan_eval s) _ = SOME args0" THEN
         QCASES_ON ("pan_lookup_code (pan_state_code (s:(A,B)pan_state)) " ^
                    string_of_term fname ^ " args0") THEN
         TRY(RENAME1 "pan_lookup_code _ _ _ = SOME x0" THEN
             PAIR_CASES_ON `x0:(A)panLang_prog#(mlstring,(A)pan_v)fmap#shape`))) THEN
  TRY(PITRAUX_UNDISCH_ITREE_TAC THEN PITRAUX_LEAF_IMP_TAC THEN NO_TAC) THEN
  QPAT_X_ASSUM "ltree _ _ = _" (fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
  REWRITE_TAC[rw] THEN ASM_SIMP_TAC[opt_mmap_eval_bst; bst_access] THEN SIMP[] THEN
  DISCH_TAC THEN GVS_ASM (PITRAUX_IMP_RULES()) THEN
  REPEAT(FULL_CASE_TAC THEN GVS_ASM (PITRAUX_IMP_RULES())) THEN
  PITRAUX_SUBRUN_TAC `x00:(A)panLang_prog` None THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `k1:num` (X_CHOOSE_THEN `t1:(A,B)pan_state` STRIP_ASSUME_TAC)) THEN
  FIRST
   [QEXISTS_TAC "SUC k1" THEN ONCE_REWRITE_TAC[pan_evaluate_def] THEN
    PITRAUX_BIND_TAC THEN RFS[pan_eval_upd_clock_eq; opt_mmap_eval_upd_clock_eq1;
                              pan_dec_clock_def; SUC_SUB1] THEN
    GVS[kvar_defs2; empty_locals_defs; mrec_h_handle_call_ret_lemma;
        mrec_h_handle_deccall_ret_lemma] THEN NO_TAC;
    GVS_ASM (PITRAUX_IMP_RULES()) THEN
    PITRAUX_SUBRUN_OTHER_TAC `x00:(A)panLang_prog` THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `k2:num` (X_CHOOSE_THEN `t2:(A,B)pan_state`
      STRIP_ASSUME_TAC)) THEN
    PITRAUX_ANY_CLOCK_TAC `x00:(A)panLang_prog` `k2:num` THEN SIMP[] THEN
    DISCH_THEN(X_CHOOSE_TAC `k3:num`) THEN
    QEXISTS_TAC "SUC k3" THEN ONCE_REWRITE_TAC[pan_evaluate_def] THEN
    PITRAUX_BIND_TAC THEN RFS[pan_eval_upd_clock_eq; opt_mmap_eval_upd_clock_eq1;
                              pan_dec_clock_def; SUC_SUB1] THEN
    PITRAUX_BIND_TAC THEN GVS[kvar_defs2; empty_locals_defs; mrec_h_handle_call_ret_lemma;
                              mrec_h_handle_deccall_ret_lemma] THEN
    PITRAUX_BIND_TAC THEN GVS[o_THM]];;

(* the backward simulation: an oracle run of the itree that terminates    *)
(* comes from a run of evaluate (with some clock) that does not time out, *)
(* with the same result, state, ffi state and oracle.  By induction on    *)
(* the number of Taus, the program cases one by one (HOL4 proves          *)
(* nondiv_imp_evaluate below so, in one long proof)                       *)

let PITRAUX_ltree_imp_evaluate = prove
 (`!n p (s:(A,B)pan_state) res t.
     ltree (ffi_state_oracle (pan_state_ffi s),ffi_state_ffi_state (pan_state_ffi s))
           (mrec h_prog (h_prog (p,pan_itreeSem_bst s))) = ITER n Tau (itree_Ret (INR (res,t)))
     ==> ?k t'. pan_evaluate (p,pan_state_clock_fupd (K k) s) = (res,t') /\
                pan_itreeSem_bst t' = t /\ ~(res = SOME pan_TimeOut) /\
                ffi_state_ffi_state (pan_state_ffi t') =
                SND (comp_ffi (ffi_state_oracle (pan_state_ffi s),
                               ffi_state_ffi_state (pan_state_ffi s))
                              (mrec h_prog (h_prog (p,pan_itreeSem_bst s)))) /\
                ffi_state_oracle (pan_state_ffi t') = ffi_state_oracle (pan_state_ffi s)`,
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  GEN_TAC THEN GEN_TAC THEN QCASES_ON "p" THEN REPEAT GEN_TAC THENL
   [PITRAUX_LEAF_IMP_TAC; PITRAUX_IMP_DEC_TAC; PITRAUX_LEAF_IMP_TAC;
    PITRAUX_LEAF_IMP_TAC; PITRAUX_LEAF_IMP_TAC; PITRAUX_LEAF_IMP_TAC;
    PITRAUX_LEAF_IMP_TAC; PITRAUX_IMP_SEQ_TAC; PITRAUX_IMP_IF_TAC;
    PITRAUX_IMP_WHILE_TAC; PITRAUX_LEAF_IMP_TAC; PITRAUX_LEAF_IMP_TAC;
    PITRAUX_IMP_CALL_TAC mrec_Call; PITRAUX_IMP_CALL_TAC mrec_DecCall;
    PITRAUX_LEAF_IMP_TAC; PITRAUX_LEAF_IMP_TAC; PITRAUX_LEAF_IMP_TAC;
    PITRAUX_LEAF_IMP_TAC; PITRAUX_LEAF_IMP_TAC; PITRAUX_LEAF_IMP_TAC;
    PITRAUX_LEAF_IMP_TAC]);;

let nondiv_imp_evaluate = prove
 (`!(s:(A,B)pan_state) p n res t.
     ltree (ffi_state_oracle (pan_state_ffi s),ffi_state_ffi_state (pan_state_ffi s))
           (mrec h_prog (h_prog (p,pan_itreeSem_bst s))) = ITER n Tau (itree_Ret (INR (res,t)))
     ==> ?k t'. pan_evaluate (p,pan_state_clock_fupd (K k) s) = (res,t') /\
                pan_itreeSem_bst t' = t /\ ~(res = SOME pan_TimeOut)`,
  MESON_TAC[PITRAUX_ltree_imp_evaluate]);;

let nondiv_imp_evaluate' = prove
 (`!(fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B) (s:(A,B)pan_state)
    p n res t.
     ltree fs (mrec h_prog (h_prog (p,pan_itreeSem_bst s))) = ITER n Tau (itree_Ret (INR (res,t))) /\
     FST fs = ffi_state_oracle (pan_state_ffi s) /\
     SND fs = ffi_state_ffi_state (pan_state_ffi s)
     ==> ?k t'. pan_evaluate (p,pan_state_clock_fupd (K k) s) = (res,t') /\
                pan_itreeSem_bst t' = t /\ ~(res = SOME pan_TimeOut)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC nondiv_imp_evaluate THEN
  QEXISTS_TAC "n" THEN ASM_MESON_TAC[PAIR]);;

let div_imp_timeout = prove
 (`!(fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B) (s:(A,B)pan_state) p.
     pan_itreeSem_div fs (mrec h_prog (h_prog (p,pan_itreeSem_bst s))) /\
     FST fs = ffi_state_oracle (pan_state_ffi s) /\
     SND fs = ffi_state_ffi_state (pan_state_ffi s)
     ==> !k. ?t. pan_evaluate (p,pan_state_clock_fupd (K k) s) = (SOME pan_TimeOut,t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `k:num` THEN
  MP_TAC(ISPEC `pan_evaluate (p,pan_state_clock_fupd (K k) (s:(A,B)pan_state))`
               PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:((A)pan_result)option` (X_CHOOSE_TAC `t:(A,B)pan_state`)) THEN
  ASM_REWRITE_TAC[PAIR_EQ] THEN ASM_CASES_TAC `r = SOME (pan_TimeOut:(A)pan_result)` THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `fs = (ffi_state_oracle (pan_state_ffi (s:(A,B)pan_state)),
                      ffi_state_ffi_state (pan_state_ffi s))` SUBST_ALL_TAC THENL
   [ASM_MESON_TAC[PAIR]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [pan_itreeSem_div_def]) THEN
  MP_TAC(MATCH_MP evaluate_imp_nondiv (CONJ
    (ASSUME `pan_evaluate (p,pan_state_clock_fupd (K k) (s:(A,B)pan_state)) = r,t`)
    (ASSUME `~(r = SOME (pan_TimeOut:(A)pan_result))`))) THEN
  SIMP[] THEN MESON_TAC[]);;

let evaluate_nondiv_trace_eq = prove
 (`!p (s:(A,B)pan_state) r t.
     pan_evaluate (p,s) = (r,t) /\ ~(r = SOME pan_TimeOut)
     ==> llist_fromList (ffi_state_io_events (pan_state_ffi t)) =
         LAPPEND (llist_fromList (ffi_state_io_events (pan_state_ffi s)))
           (trace_prefix (ffi_state_oracle (pan_state_ffi s),
                          ffi_state_ffi_state (pan_state_ffi s))
              (mrec h_prog (h_prog (p,pan_itreeSem_bst s))))`,
  MESON_TAC[PITRAUX_evaluate_ltree]);;

let nondiv_timeout_add_clock = prove
 (`!(fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B) (s:(A,B)pan_state)
    p t n r.
     pan_evaluate (p,s) = (SOME pan_TimeOut,t) /\
     ltree fs (mrec h_prog (h_prog (p,pan_itreeSem_bst s))) = ITER n Tau (itree_Ret r) /\
     FST fs = ffi_state_oracle (pan_state_ffi s) /\
     SND fs = ffi_state_ffi_state (pan_state_ffi s)
     ==> ?k q t'. pan_evaluate (p,pan_state_clock_fupd (K (pan_state_clock s + k)) s) =
                  (q,t') /\
                  r = INR (q,pan_itreeSem_bst t') /\ ~(q = SOME pan_TimeOut) /\
                  ?l. ffi_state_io_events (pan_state_ffi t') =
                      APPEND (ffi_state_io_events (pan_state_ffi t)) l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_TAC `x:((A)pan_result)option#(A)bstate` o MATCH_MP nondiv_INR) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  NAMED_CASES_ON "x" ["q x1"] THEN
  MP_TAC(ISPECL [`fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B`;
                 `s:(A,B)pan_state`; `p:(A)panLang_prog`; `n:num`;
                 `q:((A)pan_result)option`; `x1:(A)bstate`] nondiv_imp_evaluate') THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `t':(A,B)pan_state` STRIP_ASSUME_TAC)) THEN
  ASM_CASES_TAC `pan_state_clock (s:(A,B)pan_state) < k` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `d:num` SUBST_ALL_TAC o
      MATCH_MP (MESON[LE_EXISTS; LT_IMP_LE] `!c k. c < k ==> ?d. k = c + d`)) THEN
    MAP_EVERY QEXISTS_TAC ["d"; "q"; "t'"] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`p:(A)panLang_prog`; `s:(A,B)pan_state`; `d:num`]
                  pan_evaluate_add_clock_io_events_mono) THEN
    ASM_REWRITE_TAC[IS_PREFIX_APPEND];
    FIRST_X_ASSUM(X_CHOOSE_THEN `d:num` MP_TAC o
      MATCH_MP (MESON[LE_EXISTS; NOT_LT] `!c k. ~(c < k) ==> ?d. c = k + d`)) THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`p:(A)panLang_prog`; `pan_state_clock_fupd (K k) (s:(A,B)pan_state)`;
                   `q:((A)pan_result)option`; `t':(A,B)pan_state`; `d:num`]
                  pan_evaluate_add_clock_eq) THEN
    ASM_REWRITE_TAC[] THEN SIMP[] THEN
    SUBGOAL_THEN `pan_state_clock_fupd (K (k + d)) (s:(A,B)pan_state) = s`
      SUBST1_TAC THENL
     [ASM_REWRITE_TAC[pan_state_component_equality] THEN SIMP[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[]]);;

(* the trace of a bind starts with the trace of its first tree *)

let PITRAUX_trace_bind_LPREFIX = prove
 (`!(fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B)
    (X:((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
        (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree) k.
     LPREFIX (trace_prefix fs X) (trace_prefix fs (itree_bind X k))`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `pan_itreeSem_div (fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B)
      (X:((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
          (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree)` THEN
  ASM_SIMP_TAC[trace_prefix_bind_div; LPREFIX_REFL] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[nondiv_eq_Ret]) THEN
  MP_TAC(ISPECL [`fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B`;
     `X:((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
         (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree`;
     `k:(ffi_outcome+byte list)+((A)pan_result)option#(A)bstate->
        ((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
         (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree`;
     `r:(ffi_outcome+byte list)+((A)pan_result)option#(A)bstate`]
     trace_prefix_bind_append) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[LPREFIX_APPEND] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Runs that time out: their I/O is a prefix of the trace.                   *)
(* ------------------------------------------------------------------------- *)

let PITRAUX_LPREFIX_SELF = prove
 (`!(l:A list) x. LPREFIX (llist_fromList l) (LAPPEND (llist_fromList l) x)`,
  REWRITE_TAC[LPREFIX_APPEND] THEN MESON_TAC[]);;

let PITRAUX_LPREFIX_LAPPEND_MONO = prove
 (`!l (l1:A llist) l2. LPREFIX l1 l2 ==> LPREFIX (LAPPEND l l1) (LAPPEND l l2)`,
  REWRITE_TAC[LPREFIX_APPEND] THEN MESON_TAC[LAPPEND_ASSOC]);;

(* the facts of PITRAUX_evaluate_ltree for every run pan_evaluate (q,x) = *)
(* (r,y) of the assumptions that does not time out                       *)

let PITRAUX_FWD_TAC : tactic = fun (asl,w as g) ->
  let eqs = filter (fun (_,th) -> let c = concl th in
    is_eq c && (try fst(dest_const(fst(strip_comb(lhs c)))) = "pan_evaluate"
                with Failure _ -> false)) asl in
  let nt r =
    let tm = mk_neg(mk_eq(r,`SOME (pan_TimeOut:(A)pan_result)`)) in
    try snd(find (fun (_,th) -> concl th = tm) asl) with Failure _ ->
    EQT_ELIM(SIMP_CONV[option_DISTINCT; injectivity "option";
                       distinctness "pan_result"] tm) in
  let add (_,th) =
    try let r = fst(dest_pair(rhs(concl th))) in
        STRIP_ASSUME_TAC(MATCH_MP PITRAUX_evaluate_ltree (CONJ th (nt r)))
    with Failure _ -> ALL_TAC in
  MAP_EVERY add eqs g;;

(* a goal LPREFIX a c from an assumption LPREFIX a b, with tac for        *)
(* LPREFIX b c                                                            *)

let PITRAUX_LPREFIX_VIA_TAC (tac:tactic) : tactic = fun (asl,w as g) ->
  let a = lhand w in
  let ths = mapfilter (fun (_,th) -> let c = concl th in
     if (try fst(dest_const(fst(strip_comb c))) = "LPREFIX" && lhand c = a
         with Failure _ -> false) then th else failwith "") asl in
  FIRST (map (fun th -> let b = rand(concl th) in
    MATCH_MP_TAC (GEN_ALL LPREFIX_TRANS) THEN EXISTS_TAC b THEN CONJ_TAC THENL
    [ACCEPT_TAC th; tac]) ths) g;;

(* LPREFIX (LAPPEND l1 (.. (trace_prefix fs X))) (LAPPEND l1 (.. (trace_  *)
(* prefix fs (itree_bind X k)))) and the like                              *)

let PITRAUX_LPREFIX_END_TAC =
  REWRITE_TAC[LAPPEND_ASSOC] THEN
  REPEAT(MATCH_MP_TAC PITRAUX_LPREFIX_LAPPEND_MONO) THEN
  (MATCH_ACCEPT_TAC PITRAUX_trace_bind_LPREFIX ORELSE MATCH_ACCEPT_TAC LPREFIX_REFL);;

(* the I/O of every run is a prefix of the I/O before it followed by the *)
(* trace of the itree; by induction on evaluate: a run that does not     *)
(* time out is PITRAUX_evaluate_ltree, a time out in a first sub-run is  *)
(* its induction hypothesis, one in a second sub-run is the induction     *)
(* hypothesis after the forward simulation of the first                   *)

let PITRAUX_evaluate_LPREFIX = prove
 (`!p (s:(A,B)pan_state) res t.
     pan_evaluate (p,s) = (res,t)
     ==> LPREFIX (llist_fromList (ffi_state_io_events (pan_state_ffi t)))
           (LAPPEND (llist_fromList (ffi_state_io_events (pan_state_ffi s)))
              (trace_prefix (ffi_state_oracle (pan_state_ffi s),
                             ffi_state_ffi_state (pan_state_ffi s))
                 (mrec h_prog (h_prog (p,pan_itreeSem_bst s)))))`,
  REC_IND_TAC pan_evaluate_ind THEN REPEAT CONJ_TAC THEN
  REPEAT(GEN_TAC ORELSE DISCH_THEN STRIP_ASSUME_TAC) THEN
  (ASM_CASES_TAC `res = SOME (pan_TimeOut:(A)pan_result)` THENL
    [ALL_TAC;
     FIRST_X_ASSUM(fun eq -> if is_eq(concl eq) then
       MP_TAC(MATCH_MP PITRAUX_evaluate_ltree (CONJ eq
         (ASSUME `~(res = SOME (pan_TimeOut:(A)pan_result))`))) else failwith "") THEN
     SIMP[LPREFIX_REFL]]) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  QPAT_X_ASSUM "pan_evaluate _ = _" (MP_TAC o ONCE_REWRITE_RULE[pan_evaluate_def]) THEN
  REWRITE_TAC[mrec_prog_nonrec; mrec_If; mrec_ExtCall] THEN
  ONCE_REWRITE_TAC[mrec_While] THEN
  DISCH_TAC THEN GVS([COND_CASE_EQ; pan_sh_mem_load_def; pan_sh_mem_store_def;
                      call_FFI_def; explode_eq_implode; MULT_2] @ all_case_eqs()) THEN
  REPEAT(PAIRARG_TAC THEN GVS[]) THEN
  GVS[kvar_defs2; empty_locals_defs; pan_dec_clock_def] THEN
  TRY(MATCH_ACCEPT_TAC PITRAUX_LPREFIX_SELF THEN NO_TAC) THEN
  TRY(PITRAUX_LPREFIX_VIA_TAC PITRAUX_LPREFIX_END_TAC THEN NO_TAC) THEN
  PITRAUX_FWD_TAC THEN IMP_RES_TAC evaluate_invariant_oracle THEN RFS[] THEN
  PITRAUX_BIND_TAC THEN RFS[] THEN SIMP(PITRAUX_EVAL_SIMPS()) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LAPPEND_ASSOC]) THEN
  PITRAUX_LPREFIX_VIA_TAC PITRAUX_LPREFIX_END_TAC);;

(* HOL4 proves timeout_div_LPREFIX by induction on evaluate; here a       *)
(* consequence of PITRAUX_evaluate_LPREFIX (which needs no divergence)    *)

let timeout_div_LPREFIX = prove
 (`!p (s:(A,B)pan_state) t.
     pan_evaluate (p,s) = (SOME pan_TimeOut,t) /\
     pan_itreeSem_div (ffi_state_oracle (pan_state_ffi s),
                       ffi_state_ffi_state (pan_state_ffi s))
       (mrec h_prog (h_prog (p,pan_itreeSem_bst s)))
     ==> LPREFIX (llist_fromList (ffi_state_io_events (pan_state_ffi t)))
           (LAPPEND (llist_fromList (ffi_state_io_events (pan_state_ffi s)))
              (trace_prefix (ffi_state_oracle (pan_state_ffi s),
                             ffi_state_ffi_state (pan_state_ffi s))
                 (mrec h_prog (h_prog (p,pan_itreeSem_bst s)))))`,
  MESON_TAC[PITRAUX_evaluate_LPREFIX]);;

(* a monotone function on num that is bounded is eventually constant *)

let PITRAUX_MONO_BOUNDED_CONST = prove
 (`!f:num->num n.
     (!k. f k <= n) /\ (!k k'. k <= k' ==> f k <= f k')
     ==> ?k'. !k. k' <= k ==> f k = f k'`,
  REPEAT STRIP_TAC THEN
  MP_TAC(fst(EQ_IMP_RULE(SPEC `\x:num. ?k:num. x = (f:num->num) k` num_MAX))) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN EXISTS_TAC `n:num` THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` (CONJUNCTS_THEN2
    (X_CHOOSE_TAC `k0:num`) ASSUME_TAC)) THEN
  EXISTS_TAC `k0:num` THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM LE_ANTISYM] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `(f:num->num) k`) THEN ASM_REWRITE_TAC[] THEN
    MESON_TAC[];
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let not_less_opt_lemma = prove
 (`!n (prog:(A)panLang_prog) (s:(A,B)pan_state).
     (!k. ~less_opt n (SOME (LENGTH (ffi_state_io_events (pan_state_ffi
            (SND (pan_evaluate (prog,pan_state_clock_fupd (K k) s))))))))
     ==> ?k'. !k. k' <= k
              ==> LENGTH (ffi_state_io_events (pan_state_ffi
                    (SND (pan_evaluate (prog,pan_state_clock_fupd (K k) s))))) =
                  LENGTH (ffi_state_io_events (pan_state_ffi
                    (SND (pan_evaluate (prog,pan_state_clock_fupd (K k') s)))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[less_opt_def; NOT_LT] THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`\k. LENGTH (ffi_state_io_events (pan_state_ffi
           (SND (pan_evaluate (prog,pan_state_clock_fupd (K k) (s:(A,B)pan_state))))))`;
    `n:num`] PITRAUX_MONO_BOUNDED_CONST) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST1_TAC o REWRITE_RULE[LE_EXISTS]) THEN
  MATCH_MP_TAC IS_PREFIX_LENGTH THEN
  MP_TAC(ISPECL [`prog:(A)panLang_prog`; `pan_state_clock_fupd (K k) (s:(A,B)pan_state)`;
                 `d:num`] pan_evaluate_add_clock_io_events_mono) THEN
  SIMP[]);;

(* a run of mrec h_prog without events cannot end in FinalFFI *)

let PITRAUX_mrec_Ret_not_FinalFFI = prove
 (`!n p (s:(A)bstate) fe t.
     ~(mrec h_prog (h_prog (p,s)) =
       ITER n Tau (itree_Ret (INR (SOME (pan_FinalFFI fe),t))))`,
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  GEN_TAC THEN QCASES_ON "p" THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[mrec_prog_nonrec; mrec_If; mrec_ExtCall] THEN
  TRY(GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [mrec_While]) THEN
  REPEAT(TOP_CASE_TAC THEN SIMP[]) THEN REPEAT STRIP_TAC THEN
  GVS_ASM([PITRAUX_Tau_FUNPOW_Ret; PITRAUX_bind_FUNPOW_Ret; o_THM;
           mrec_h_handle_call_ret_lemma; mrec_h_handle_deccall_ret_lemma] @
          all_case_eqs()) THEN
  REPEAT(FULL_CASE_TAC THEN GVS_ASM([PITRAUX_Tau_FUNPOW_Ret; PITRAUX_bind_FUNPOW_Ret; o_THM;
           mrec_h_handle_call_ret_lemma; mrec_h_handle_deccall_ret_lemma] @
          all_case_eqs())) THEN
  PITRAUX_IH_AT_TAC `pan_FinalFFI:final_event->(A)pan_result`);;

(* ------------------------------------------------------------------------- *)
(* Runs without FFI events do not depend on the ffi state.                   *)
(* ------------------------------------------------------------------------- *)

let PITRAUX_eval_ffi_fupd = prove
 (`!(s:(A,B)pan_state) (ffi:(B)ffi_state) e es.
     pan_eval (pan_state_ffi_fupd (K ffi) s) e = pan_eval s e /\
     OPT_MMAP (pan_eval (pan_state_ffi_fupd (K ffi) s)) es = OPT_MMAP (pan_eval s) es`,
  REWRITE_TAC[GSYM eval_bst; GSYM opt_mmap_eval_bst] THEN
  SUBGOAL_THEN `!(s:(A,B)pan_state) (ffi:(B)ffi_state).
                  pan_itreeSem_bst (pan_state_ffi_fupd (K ffi) s) = pan_itreeSem_bst s`
    (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[pan_itreeSem_bst_def] THEN SIMP[]);;

let PITRAUX_call_FFI_empty = prove
 (`!(st:(B)ffi_state) conf bytes.
     call_FFI st (ExtCall (implode "")) conf bytes = FFI_return st bytes`,
  REWRITE_TAC[call_FFI_def]);;

(* the conclusion of PITRAUX_evaluate_ffi_indep as one predicate: as a   *)
(* rewrite rule (an induction hypothesis) it does not loop               *)

let PITRAUX_FFI_INDEP_def = cake_def
 `PITRAUX_FFI_INDEP (p:(A)panLang_prog) (s:(A,B)pan_state) r t <=>
    pan_state_ffi t = pan_state_ffi s /\
    !ffi. pan_evaluate (p,pan_state_ffi_fupd (K ffi) s) =
          (r,pan_state_ffi_fupd (K ffi) t)`;;

(* LENGTH x.io <= LENGTH y.io for every run pan_evaluate (q,x) = (r,y) *)

let PITRAUX_FI_MONO_TAC : tactic = fun (asl,w as g) ->
  let eqs = filter (fun (_,th) -> let c = concl th in
    is_eq c && (try fst(dest_const(fst(strip_comb(lhs c)))) = "pan_evaluate"
                with Failure _ -> false)) asl in
  MAP_EVERY (fun (_,th) -> ASSUME_TAC(MATCH_MP IS_PREFIX_LENGTH
                              (MATCH_MP pan_evaluate_io_events_mono th))) eqs g;;

(* the induction hypotheses LENGTH _ <= LENGTH _ /\ .. ==> .. : their    *)
(* antecedents by arithmetic on the lengths and simplification           *)

let PITRAUX_FI_DISCH_TAC : tactic =
  REPEAT(FIRST_X_ASSUM(fun th -> let c = concl th in
    if is_imp c && can (find_term (fun t -> try fst(dest_const(fst(strip_comb t))) = "<="
                                            with Failure _ -> false)) (lhand c)
    then MP_TAC th THEN ANTS_TAC THENL
          [REPEAT CONJ_TAC THEN
           (ASM_ARITH_TAC ORELSE
            ASM_SIMP_TAC[option_DISTINCT; injectivity "option"; distinctness "pan_result";
                         NOT_EXISTS_THM]);
           ALL_TAC] THEN DISCH_TAC
    else failwith "PITRAUX_FI_DISCH_TAC"));;

let PITRAUX_DROP_IMPS_TAC : tactic =
  REPEAT(FIRST_X_ASSUM(fun th -> let c = concl th in
    if is_forall c && is_imp(snd(strip_forall c)) then ALL_TAC
    else failwith "PITRAUX_DROP_IMPS_TAC"));;

(* a length assumption that is false (an FFI event was added) *)

let PITRAUX_FI_LEN_CONTR_TAC : tactic =
  FIRST_ASSUM(fun th -> let c = concl th in
    if (try fst(dest_const(fst(strip_comb c))) = "<=" with Failure _ -> false)
    then MP_TAC th THEN REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ARITH_TAC
    else failwith "PITRAUX_FI_LEN_CONTR_TAC");;

let PITRAUX_VK_CASES_TAC : tactic = fun (asl,w as g) ->
  let vs = filter (fun v -> type_of v = `:varkind`) (freesl (w :: map (concl o snd) asl)) in
  MAP_EVERY (fun v -> DISJ_CASES_THEN SUBST_ALL_TAC (SPEC v (cases "varkind"))) vs g;;

let PITRAUX_FI_SIMPS () =
  [PITRAUX_eval_ffi_fupd; pan_dec_clock_def; pan_sh_mem_load_def; pan_sh_mem_store_def;
   PITRAUX_call_FFI_empty; kvar_defs2; empty_locals_defs];;

(* by induction on evaluate: the case split of the run, the induction    *)
(* hypotheses for its sub-runs (whose I/O is also unchanged, by io       *)
(* monotonicity), then the run from the other ffi state, unfolded once   *)

let PITRAUX_evaluate_ffi_indep_lemma = prove
 (`!p (s:(A,B)pan_state) r t.
     pan_evaluate (p,s) = (r,t) /\
     LENGTH (ffi_state_io_events (pan_state_ffi t)) <=
     LENGTH (ffi_state_io_events (pan_state_ffi s)) /\
     ~(?fe. r = SOME (pan_FinalFFI fe))
     ==> PITRAUX_FFI_INDEP p s r t`,
  REC_IND_TAC pan_evaluate_ind THEN REPEAT CONJ_TAC THEN
  REPEAT(GEN_TAC ORELSE DISCH_THEN STRIP_ASSUME_TAC) THEN
  QPAT_X_ASSUM "pan_evaluate _ = _" (MP_TAC o ONCE_REWRITE_RULE[pan_evaluate_def]) THEN
  DISCH_TAC THEN GVS([COND_CASE_EQ; pan_sh_mem_load_def; pan_sh_mem_store_def;
                      call_FFI_def; explode_eq_implode; LENGTH_APPEND] @ all_case_eqs()) THEN
  REPEAT(PAIRARG_TAC THEN GVS[]) THEN
  GVS[kvar_defs2; empty_locals_defs; pan_dec_clock_def] THEN
  TRY(PITRAUX_FI_LEN_CONTR_TAC THEN NO_TAC) THEN PITRAUX_VK_CASES_TAC THEN
  PITRAUX_FI_MONO_TAC THEN FS[] THEN PITRAUX_FI_DISCH_TAC THEN
  PITRAUX_DROP_IMPS_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PITRAUX_FFI_INDEP_def]) THEN
  REWRITE_TAC[PITRAUX_FFI_INDEP_def] THEN FS[] THEN
  REPEAT CONJ_TAC THEN
  ((ASM_REWRITE_TAC[] THEN NO_TAC) ORELSE
   (REPEAT(CASE_TAC THEN SIMP[]) THEN NO_TAC) ORELSE
   (X_GEN_TAC `ffi:(B)ffi_state` THEN ONCE_REWRITE_TAC[pan_evaluate_def] THEN
    SIMP(PITRAUX_FI_SIMPS()) THEN REPEAT(CASE_TAC THEN SIMP(PITRAUX_FI_SIMPS())))));;

let PITRAUX_evaluate_ffi_indep = prove
 (`!p (s:(A,B)pan_state) r t.
     pan_evaluate (p,s) = (r,t) /\
     LENGTH (ffi_state_io_events (pan_state_ffi t)) <=
     LENGTH (ffi_state_io_events (pan_state_ffi s)) /\
     ~(?fe. r = SOME (pan_FinalFFI fe))
     ==> pan_state_ffi t = pan_state_ffi s /\
         !ffi. pan_evaluate (p,pan_state_ffi_fupd (K ffi) s) =
               (r,pan_state_ffi_fupd (K ffi) t)`,
  REWRITE_TAC[GSYM PITRAUX_FFI_INDEP_def; PITRAUX_evaluate_ffi_indep_lemma]);;

(* ------------------------------------------------------------------------- *)
(* Itrees without FFI calls: runs of evaluate for every ffi state.           *)
(* ------------------------------------------------------------------------- *)

let PITRAUX_ltree_FUNPOW_Ret = prove
 (`!n (fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B)
      (r:(ffi_outcome+byte list)+((A)pan_result)option#(A)bstate).
     ltree fs (ITER n Tau (itree_Ret r)) =
     (ITER n Tau (itree_Ret r):((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
                                (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree)`,
  SIMP[ltree_FUNPOW_Tau; ltree_simps]);;

(* a state with another ffi state, as a pan_itreeSem_ext *)

let PITRAUX_ffi_fupd_ext = prove
 (`!(t:(A,B)pan_state) (ffi:(B)ffi_state).
     pan_state_ffi_fupd (K ffi) t = pan_itreeSem_ext (pan_itreeSem_bst t) (pan_state_clock t) ffi`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM(CONJUNCT1(SPEC_ALL ext_bst_id))] THEN
  REWRITE_TAC[ext_normalise]);;

(* f applied to the first assumption pan_evaluate _ = _ *)

let PITRAUX_ON_EVAL_TAC (f:thm->tactic) : tactic =
  FIRST_ASSUM(fun eq -> let c = concl eq in
    if is_eq c && (try fst(dest_const(fst(strip_comb(lhs c)))) = "pan_evaluate"
                   with Failure _ -> false)
    then f eq else failwith "PITRAUX_ON_EVAL_TAC");;

(* HOL4 proves mrec_Ret_evaluate and mrec_FUNPOW_Ret_evaluate by          *)
(* induction on n and on the program; here: the backward simulation for   *)
(* one ffi state, the trace (empty) for its I/O, and                       *)
(* PITRAUX_evaluate_ffi_indep for the other ffi states                     *)

let PITRAUX_mrec_FUNPOW_Ret_evaluate = prove
 (`!n p (s:(A)bstate) res t.
     mrec h_prog (h_prog (p,s)) = ITER n Tau (itree_Ret (INR (res,t)))
     ==> ?k k'. (!ffi:(B)ffi_state. pan_evaluate (p,pan_itreeSem_ext s k ffi) = (res,pan_itreeSem_ext t k' ffi)) /\
                k' <= k /\ ~(res = SOME pan_TimeOut) /\
                (!fe. ~(res = SOME (pan_FinalFFI fe)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `!fe. ~(res = SOME (pan_FinalFFI fe:(A)pan_result))` ASSUME_TAC THENL
   [ASM_MESON_TAC[PITRAUX_mrec_Ret_not_FinalFFI]; ALL_TAC] THEN
  MP_TAC(ISPECL [`n:num`; `p:(A)panLang_prog`; `pan_itreeSem_ext (s:(A)bstate) 0 (ARB:(B)ffi_state)`;
                 `res:((A)pan_result)option`; `t:(A)bstate`] PITRAUX_ltree_imp_evaluate) THEN
  ASM_REWRITE_TAC[bst_ext_id; PITRAUX_ltree_FUNPOW_Ret] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `t':(A,B)pan_state` STRIP_ASSUME_TAC)) THEN
  PITRAUX_ON_EVAL_TAC (fun eq -> FIRST_ASSUM(MP_TAC o MATCH_MP evaluate_nondiv_trace_eq o
                                              CONJ eq)) THEN
  SIMP[bst_ext_id; ext_normalise; ext_access; trace_prefix_FUNPOW_Tau; trace_prefix_simps;
           LAPPEND_NIL_2ND; fromList_11] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`p:(A)panLang_prog`;
                 `pan_state_clock_fupd (K k) (pan_itreeSem_ext (s:(A)bstate) 0 (ARB:(B)ffi_state))`;
                 `res:((A)pan_result)option`; `t':(A,B)pan_state`] PITRAUX_evaluate_ffi_indep) THEN
  SIMP[ext_normalise; ext_access; LE_REFL] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`k:num`; `pan_state_clock (t':(A,B)pan_state)`] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[PITRAUX_ffi_fupd_ext]; ALL_TAC] THEN
  PITRAUX_ON_EVAL_TAC (MP_TAC o MATCH_MP pan_evaluate_clock) THEN
  SIMP[ext_normalise; ext_access]);;

let mrec_Ret_evaluate = prove
 (`!p (s:(A)bstate) res t.
     mrec h_prog (h_prog (p,s)) = itree_Ret (INR (res,t))
     ==> ?k k'. !ffi:(B)ffi_state.
           pan_evaluate (p,pan_itreeSem_ext s k ffi) = (res,pan_itreeSem_ext t k' ffi) /\
           ~(res = SOME pan_TimeOut) /\ (!fe. ~(res = SOME (pan_FinalFFI fe))) /\
           k' <= k`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`0`; `p:(A)panLang_prog`; `s:(A)bstate`; `res:((A)pan_result)option`;
                 `t:(A)bstate`] PITRAUX_mrec_FUNPOW_Ret_evaluate) THEN
  ASM_REWRITE_TAC[ITER] THEN MESON_TAC[]);;

(* HOL4: move to HOL - llistTheory *)

let LFINITE_LAPPEND_EQ_NIL = prove
 (`!(ll:A llist) l1. LFINITE ll ==> (LAPPEND ll l1 = ll <=> l1 = LNIL)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [ASM_MESON_TAC[LFINITE_LAPPEND_IMP_NIL]; SIMP_TAC[LAPPEND_NIL_2ND]]);;

let mrec_FUNPOW_Ret_evaluate = prove
 (`!n p (s:(A)bstate) res t.
     mrec h_prog (h_prog (p,s)) = ITER n Tau (itree_Ret (INR (res,t)))
     ==> ?k k'. (!ffi:(B)ffi_state. pan_evaluate (p,pan_itreeSem_ext s k ffi) = (res,pan_itreeSem_ext t k' ffi)) /\
                k' <= k /\ ~(res = SOME pan_TimeOut) /\
                (!fe. ~(res = SOME (pan_FinalFFI fe)))`,
  REWRITE_TAC[PITRAUX_mrec_FUNPOW_Ret_evaluate]);;

(* ------------------------------------------------------------------------- *)
(* After a failed FFI call the itree of a program ends in FinalFFI.          *)
(* ------------------------------------------------------------------------- *)

let PITRAUX_Tau_FUNPOW_Vis = prove
 (`!(t:(A,E,R)itree) n e k.
     Tau t = ITER n Tau (Vis e k) <=> ?m. n = SUC m /\ t = ITER m Tau (Vis e k)`,
  GEN_TAC THEN INDUCT_TAC THEN SIMP[ITER; NOT_SUC; SUC_INJ]);;

let PITRAUX_Vis_FUNPOW_Vis = prove
 (`!(e':E) (k':A->(A,E,R)itree) (r:R) n e k.
     (Vis e' k' = ITER n Tau (Vis e k) <=> n = 0 /\ e' = e /\ k' = k) /\
     ~(itree_Ret r = ITER n Tau (Vis e k))`,
  REPEAT GEN_TAC THEN QCASES_ON "n" THEN SIMP[ITER] THEN MESON_TAC[]);;

let PITRAUX_bind_FUNPOW_Vis = prove
 (`!n (ht:(A,E,R)itree) (t:R->(A,E,B)itree) e k.
     itree_bind ht t = ITER n Tau (Vis e k) <=>
     (?g. ht = ITER n Tau (Vis e g) /\ k = (\x. itree_bind (g x) t)) \/
     (?x m. ht = ITER m Tau (itree_Ret x) /\
            t x = ITER (n - m) Tau (Vis e k) /\ m <= n)`,
  REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[bind_FUNPOW_Vis] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[FUNPOW_Tau_bind; itree_bind_thm] THEN
  FIRST_X_ASSUM(CHOOSE_THEN SUBST1_TAC o REWRITE_RULE[LE_EXISTS]) THEN
  REWRITE_TAC[ADD_SUB2; ITER_ADD] THEN REWRITE_TAC[ADD_SYM]);;

let PITRAUX_VIS_RULES () =
  [PITRAUX_Tau_FUNPOW_Vis; PITRAUX_Vis_FUNPOW_Vis; PITRAUX_bind_FUNPOW_Vis; o_THM;
   mrec_h_handle_call_ret_lemma; mrec_h_handle_deccall_ret_lemma; COND_CASE_EQ] @
  all_case_eqs();;

(* the induction hypothesis at the count of the assumption mrec h_prog _ = *)
(* ITER k Tau (Vis _ _), applied to it                                      *)

let PITRAUX_VIS_IH_TAC : tactic = fun (asl,w as g) ->
  let is_target th = let c = concl th in is_eq c &&
     (try fst(dest_const(fst(strip_comb(lhs c)))) = "mrec" with Failure _ -> false) &&
     (try fst(dest_const(fst(strip_comb(rhs c)))) = "ITER" &&
          fst(dest_const(fst(strip_comb(rand(rhs c))))) = "Vis" with Failure _ -> false) in
  let th = snd(find (fun (_,th) -> is_target th) asl) in
  let k = hd(snd(strip_comb(rhs(concl th)))) in
  (FIRST_X_ASSUM(fun ih -> let c = concl ih in
     if is_forall c && type_of(fst(dest_forall c)) = `:num`
     then MP_TAC(SPEC k ih) else failwith "PITRAUX_VIS_IH_TAC") THEN
   ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   DISCH_THEN(fun ih -> ASSUME_TAC(MATCH_MP ih th))) g;;

(* by induction on the number of Taus before the call: the call itself   *)
(* (ExtCall, ShMemLoad, ShMemStore) ends in FinalFFI after one Tau; in    *)
(* a sub-run, the continuations pass FinalFFI on                          *)

let PITRAUX_mrec_Vis_fail = prove
 (`!n p (s:(A)bstate) a g.
     mrec h_prog (h_prog (p,s)) = ITER n Tau (Vis a g)
     ==> !outcome. ?m fe st. g (INL (INL outcome)) =
                             ITER m Tau (itree_Ret (INR (SOME (pan_FinalFFI fe),st)))`,
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  GEN_TAC THEN QCASES_ON "p" THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[mrec_prog_nonrec; mrec_If; mrec_ExtCall] THEN
  TRY(GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [mrec_While]) THEN
  REPEAT(TOP_CASE_TAC THEN SIMP[]) THEN REPEAT STRIP_TAC THEN
  GVS_ASM (PITRAUX_VIS_RULES()) THEN
  REPEAT(FULL_CASE_TAC THEN GVS_ASM (PITRAUX_VIS_RULES())) THEN SIMP[] THEN
  FIRST
   [EXISTS_TAC `SUC 0` THEN SIMP[ITER] THEN NO_TAC;
    PITRAUX_VIS_IH_TAC THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o SPEC `outcome:ffi_outcome`) THEN
    ASM_REWRITE_TAC[FUNPOW_Tau_bind; itree_bind_thm] THEN
    SIMP[o_THM; mrec_h_handle_call_ret_lemma; mrec_h_handle_deccall_ret_lemma;
         empty_locals_defs] THEN
    MESON_TAC[]]);;

(* every itree spins or reaches a Ret or a Vis after some Taus *)

let PITRAUX_itree_cases3 = prove
 (`!t:(A,E,R)itree.
     t = itree_spin \/ (?n r. t = ITER n Tau (itree_Ret r)) \/ (?n e k. t = ITER n Tau (Vis e k))`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`t:(A,E,R)itree`; `itree_Ret:R->(A,E,R)itree`; `t:(A,E,R)itree`]
                itree_bind_cases) THEN
  REWRITE_TAC[itree_bind_right_identity] THEN MESON_TAC[]);;

(* the instance at the outcome x of the assumption !outcome. .. about     *)
(* k (INL (INL outcome)), x from the term k (INL (INL x)) of the ltree     *)
(* assumption                                                               *)

let PITRAUX_FAIL_INST_TAC : tactic = fun (asl,w as g) ->
  let is_ltree_eq th = is_eq (concl th) &&
    can (find_term (fun t -> try fst(dest_const(fst(strip_comb t))) = "ltree"
                             with Failure _ -> false)) (concl th) in
  let th = snd(find (fun (_,th) -> is_ltree_eq th) asl) in
  let t = find_term (fun t -> try fst(dest_const(rator t)) = "INL" &&
                                  fst(dest_const(rator(rand t))) = "INL"
                              with Failure _ -> false) (concl th) in
  let x = rand(rand t) in
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o SPEC x o
    check (fun th -> is_forall (concl th) &&
                     type_of (fst (dest_forall (concl th))) = `:ffi_outcome`)) g;;

(* an itree of a program whose oracle run ends without I/O and not in     *)
(* FinalFFI has no FFI call: it is that run                               *)

let PITRAUX_mrec_nil_trace_Ret = prove
 (`!(fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B) p (s:(A)bstate) n r.
     ltree fs (mrec h_prog (h_prog (p,s))) = ITER n Tau (itree_Ret r) /\
     trace_prefix fs (mrec h_prog (h_prog (p,s))) = LNIL /\
     (!fe st. ~(r = INR (SOME (pan_FinalFFI fe),st)))
     ==> mrec h_prog (h_prog (p,s)) = ITER n Tau (itree_Ret r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `mrec h_prog (h_prog (p,s:(A)bstate)):
                  ((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
                   (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree`
               PITRAUX_itree_cases3) THEN
  STRIP_TAC THENL
   [UNDISCH_TAC `ltree (fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B)
                   (mrec h_prog (h_prog (p,s:(A)bstate))) = ITER n Tau (itree_Ret r)` THEN
    ASM_REWRITE_TAC[ltree_spin] THEN MESON_TAC[FUNPOW_Ret_spin_F];
    UNDISCH_TAC `ltree (fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B)
                   (mrec h_prog (h_prog (p,s:(A)bstate))) = ITER n Tau (itree_Ret r)` THEN
    ASM_REWRITE_TAC[PITRAUX_ltree_FUNPOW_Ret] THEN SIMP[];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PITRAUX_mrec_Vis_fail) THEN
  FIRST_X_ASSUM(fun th -> if is_eq(concl th) && is_comb(lhs(concl th)) &&
                             (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "mrec"
                              with Failure _ -> false) &&
                             (try fst(dest_const(fst(strip_comb(rand(rhs(concl th)))))) = "Vis"
                              with Failure _ -> false)
                          then SUBST_ALL_TAC th else failwith "") THEN
  PAIR_CASES_ON `e:ev` THEN FS[] THEN
  FULL_CASE_TAC THEN FS[] THEN TRY(FULL_CASE_TAC THEN FS[]) THEN
  PITRAUX_FAIL_INST_TAC THEN RFS[PITRAUX_ltree_FUNPOW_Ret; PITRAUX_Tau_ITER; ITER_ADD]);;

(* ------------------------------------------------------------------------- *)
(* The I/O of the first n steps of an oracle run (local helpers): every     *)
(* finite part of the trace is reached in finitely many steps.               *)
(* ------------------------------------------------------------------------- *)

let PITRAUX_ttrace_def = cake_def
 `(PITRAUX_ttrace (fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B) 0
     (t:((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
         (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree) = []) /\
  (PITRAUX_ttrace fs (SUC n) t =
     match t with
       itree_Ret r -> []
     | Tau u -> PITRAUX_ttrace fs n u
     | Vis (s,c,ws) g ->
         (match FST fs s (SND fs) c ws with
            Oracle_return fs' ws' ->
              if LENGTH ws = LENGTH ws'
              then CONS (IO_event s c (ZIP ws ws'))
                     (PITRAUX_ttrace (FST fs,fs') n (g (INL (INR ws'))))
              else PITRAUX_ttrace fs n (g (INL (INL FFI_failed)))
          | Oracle_final outcome -> PITRAUX_ttrace fs n (g (INL (INL outcome)))))`;;

let PITRAUX_ttrace_simps = prove(CASE_TERM
 `!(fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B) n
    (t:((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
        (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree)
    (r:(ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)
    (u:((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
        (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree)
    s c ws
    (g:(ffi_outcome+byte list)+((A)pan_result)option#(A)bstate->
       ((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
        (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree).
   PITRAUX_ttrace fs 0 t = [] /\
   PITRAUX_ttrace fs (SUC n) (itree_Ret r) = [] /\
   PITRAUX_ttrace fs (SUC n) (Tau u) = PITRAUX_ttrace fs n u /\
   PITRAUX_ttrace fs (SUC n) (Vis (s,c,ws) g) =
     match FST fs s (SND fs) c ws with
       Oracle_return fs' ws' ->
         if LENGTH ws = LENGTH ws'
         then CONS (IO_event s c (ZIP ws ws'))
                (PITRAUX_ttrace (FST fs,fs') n (g (INL (INR ws'))))
         else PITRAUX_ttrace fs n (g (INL (INL FFI_failed)))
     | Oracle_final outcome -> PITRAUX_ttrace fs n (g (INL (INL outcome)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[PITRAUX_ttrace_def] THEN SIMP[]);;
let _ = cake_add_simps [PITRAUX_ttrace_simps];;

let PITRAUX_ttrace_FUNPOW_Ret = prove
 (`!m n (fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B)
      (r:(ffi_outcome+byte list)+((A)pan_result)option#(A)bstate).
     PITRAUX_ttrace fs n
       (ITER m Tau (itree_Ret r):((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
                                  (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree) =
     []`,
  INDUCT_TAC THEN INDUCT_TAC THEN SIMP[ITER]);;

let PITRAUX_ttrace_LPREFIX = prove
 (`!n (fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B)
      (t:((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
          (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree).
     LPREFIX (llist_fromList (PITRAUX_ttrace fs n t)) (trace_prefix fs t)`,
  INDUCT_TAC THEN REPEAT GEN_TAC THEN SIMP[llist_fromList_def; LPREFIX_LNIL] THEN
  QCASES_ON "t" THEN TRY(RENAME1 "Vis e0 g0" THEN PAIR_CASES_ON `e0:ev`) THEN
  SIMP[llist_fromList_def; LPREFIX_LNIL] THEN
  REPEAT(CASE_TAC THEN SIMP[llist_fromList_def; LPREFIX_LNIL]) THEN
  REWRITE_TAC[LPREFIX_LCONS] THEN ASM_MESON_TAC[]);;

(* one step of the oracle run at a Vis: the next oracle state fs1, the   *)
(* answer x1 and the I/O l1 of the step                                   *)

let PITRAUX_Vis_step = prove
 (`!(fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B) e
    (g:(ffi_outcome+byte list)+((A)pan_result)option#(A)bstate->
       ((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
        (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree)
    (k:(ffi_outcome+byte list)+((A)pan_result)option#(A)bstate->
       ((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
        (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree).
     ?(fs1:(ffiname->B->byte list->byte list->(B)oracle_result)#B) x1 l1.
       FST fs1 = FST fs /\
       ltree fs (Vis e g) = Tau (ltree fs1 (g x1)) /\
       comp_ffi fs (Vis e g) = comp_ffi fs1 (g x1) /\
       trace_prefix fs (Vis e g) = LAPPEND (llist_fromList l1) (trace_prefix fs1 (g x1)) /\
       !n. PITRAUX_ttrace fs (SUC n) (Vis e g) = APPEND l1 (PITRAUX_ttrace fs1 n (g x1)) /\
           PITRAUX_ttrace fs (SUC n) (Vis e (\x. itree_bind (g x) k)) =
           APPEND l1 (PITRAUX_ttrace fs1 n (itree_bind (g x1) k))`,
  REPEAT GEN_TAC THEN PAIR_CASES_ON `e:ev` THEN
  REWRITE_TAC[ltree_simps; comp_ffi_simps; trace_prefix_simps; PITRAUX_ttrace_simps] THEN
  REPEAT(CASE_TAC ORELSE COND_CASES_TAC) THEN CONV_TAC(DEPTH_CONV BETA_CONV) THENL
   [MAP_EVERY EXISTS_TAC
     [`(FST (fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B),a0:B)`;
      `INL (INR a1):(ffi_outcome+byte list)+((A)pan_result)option#(A)bstate`;
      `[IO_event e0 e1 (ZIP e2 a1)]`];
    MAP_EVERY EXISTS_TAC
     [`fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B`;
      `INL (INL FFI_failed):(ffi_outcome+byte list)+((A)pan_result)option#(A)bstate`;
      `[]:io_event list`];
    MAP_EVERY EXISTS_TAC
     [`fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B`;
      `INL (INL a):(ffi_outcome+byte list)+((A)pan_result)option#(A)bstate`;
      `[]:io_event list`]] THEN
  REWRITE_TAC[APPEND; llist_fromList_def; LAPPEND; FST]);;

(* the n-step I/O of a run that ends after m <= n steps is its trace *)

let PITRAUX_ttrace_Ret = prove
 (`!m (fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B)
      (X:((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
          (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree) r.
     ltree fs X = ITER m Tau (itree_Ret r)
     ==> trace_prefix fs X = llist_fromList (PITRAUX_ttrace fs m X) /\
         !n. m <= n ==> PITRAUX_ttrace fs n X = PITRAUX_ttrace fs m X`,
  INDUCT_TAC THEN REPEAT GEN_TAC THEN QCASES_ON "X" THENL
   [REWRITE_TAC[ITER; ltree_simps; trace_prefix_simps; PITRAUX_ttrace_simps;
                llist_fromList_def] THEN
    DISCH_TAC THEN INDUCT_TAC THEN REWRITE_TAC[PITRAUX_ttrace_simps];
    REWRITE_TAC[ITER; ltree_simps; itree_distinct];
    MP_TAC(ISPECL [`fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B`; `a:ev`;
       `g:(ffi_outcome+byte list)+((A)pan_result)option#(A)bstate->
          ((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
           (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree`;
       `g:(ffi_outcome+byte list)+((A)pan_result)option#(A)bstate->
          ((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
           (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree`]
       PITRAUX_Vis_step) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[ITER; itree_distinct];
    REWRITE_TAC[ITER; ltree_simps; itree_distinct];
    REWRITE_TAC[ITER; ltree_simps; trace_prefix_simps; PITRAUX_ttrace_simps; itree_11] THEN
    DISCH_THEN(fun th -> FIRST_X_ASSUM(STRIP_ASSUME_TAC o C MATCH_MP th)) THEN
    ASM_REWRITE_TAC[] THEN INDUCT_TAC THEN
    REWRITE_TAC[LE_SUC; PITRAUX_ttrace_simps; ARITH_RULE `~(SUC m <= 0)`] THEN
    ASM_SIMP_TAC[];
    MP_TAC(ISPECL [`fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B`; `a:ev`;
       `g:(ffi_outcome+byte list)+((A)pan_result)option#(A)bstate->
          ((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
           (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree`;
       `g:(ffi_outcome+byte list)+((A)pan_result)option#(A)bstate->
          ((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
           (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree`]
       PITRAUX_Vis_step) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[ITER; itree_11] THEN
    DISCH_THEN(fun th -> FIRST_X_ASSUM(STRIP_ASSUME_TAC o C MATCH_MP th)) THEN
    ASM_REWRITE_TAC[LAPPEND_fromList] THEN INDUCT_TAC THEN
    REWRITE_TAC[LE_SUC; ARITH_RULE `~(SUC m <= 0)`] THEN
    ASM_SIMP_TAC[]]);;

(* the n-step I/O of a bind: that of its first tree, or, when that one   *)
(* ends after m <= n steps, its trace followed by the (n - m)-step I/O   *)
(* of the continuation                                                    *)

let PITRAUX_ttrace_bind = prove
 (`!n (fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B)
      (X:((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
          (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree) k.
     (?m r. m <= n /\ ltree fs X = ITER m Tau (itree_Ret r) /\
            PITRAUX_ttrace fs n (itree_bind X k) =
            APPEND (PITRAUX_ttrace fs m X)
                   (PITRAUX_ttrace (FST fs,SND (comp_ffi fs X)) (n - m) (k r))) \/
     PITRAUX_ttrace fs n (itree_bind X k) = PITRAUX_ttrace fs n X`,
  INDUCT_TAC THEN REPEAT GEN_TAC THENL
   [DISJ2_TAC THEN REWRITE_TAC[PITRAUX_ttrace_simps]; ALL_TAC] THEN
  QCASES_ON "X" THENL
   [DISJ1_TAC THEN MAP_EVERY QEXISTS_TAC ["0"; "x"] THEN
    REWRITE_TAC[LE_0; ITER; ltree_simps; itree_bind_thm; comp_ffi_simps; SUB_0;
                PITRAUX_ttrace_simps; APPEND; PAIR];
    REWRITE_TAC[itree_bind_thm; PITRAUX_ttrace_simps; ltree_simps; comp_ffi_simps] THEN
    FIRST_X_ASSUM(DISJ_CASES_TAC o SPECL
      [`fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B`;
       `u:((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
           (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree`;
       `k:(ffi_outcome+byte list)+((A)pan_result)option#(A)bstate->
          ((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
           (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree`]) THENL
     [DISJ1_TAC THEN FIRST_X_ASSUM(X_CHOOSE_THEN `m:num` (X_CHOOSE_THEN
        `r:(ffi_outcome+byte list)+((A)pan_result)option#(A)bstate` STRIP_ASSUME_TAC)) THEN
      MAP_EVERY QEXISTS_TAC ["SUC m"; "r"] THEN
      ASM_REWRITE_TAC[LE_SUC; ITER; PITRAUX_ttrace_simps; SUB_SUC];
      DISJ2_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B`; `a:ev`;
     `g:(ffi_outcome+byte list)+((A)pan_result)option#(A)bstate->
        ((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
         (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree`;
     `k:(ffi_outcome+byte list)+((A)pan_result)option#(A)bstate->
        ((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
         (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree`]
     PITRAUX_Vis_step) THEN
  DISCH_THEN(X_CHOOSE_THEN `fs1:(ffiname->B->byte list->byte list->(B)oracle_result)#B`
    (X_CHOOSE_THEN `x1:(ffi_outcome+byte list)+((A)pan_result)option#(A)bstate`
      (X_CHOOSE_THEN `l1:io_event list` STRIP_ASSUME_TAC))) THEN
  ASM_REWRITE_TAC[itree_bind_thm] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o SPECL
    [`fs1:(ffiname->B->byte list->byte list->(B)oracle_result)#B`;
     `(g:(ffi_outcome+byte list)+((A)pan_result)option#(A)bstate->
         ((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
          (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree) x1`;
     `k:(ffi_outcome+byte list)+((A)pan_result)option#(A)bstate->
        ((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
         (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree`]) THENL
   [DISJ1_TAC THEN FIRST_X_ASSUM(X_CHOOSE_THEN `m:num` (X_CHOOSE_THEN
      `r:(ffi_outcome+byte list)+((A)pan_result)option#(A)bstate` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY QEXISTS_TAC ["SUC m"; "r"] THEN
    ASM_REWRITE_TAC[LE_SUC; ITER; SUB_SUC; APPEND_ASSOC];
    DISJ2_TAC THEN ASM_REWRITE_TAC[]]);;


(* a run whose every n-step I/O is empty has an empty trace (coinduction *)
(* on the unfolded trace)                                                 *)

let PITRAUX_NIL_STEP_TAC : tactic =
  let is_step th = is_forall (concl th) &&
    (try let t = find_term (fun t -> try fst(dest_const(fst(strip_comb t))) = "PITRAUX_ttrace" &&
                                         length(snd(strip_comb t)) = 3
                                     with Failure _ -> false) (concl th) in
         is_comb (last(snd(strip_comb t)))
     with Failure _ -> false) in
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
  FIRST
   [FIRST_X_ASSUM(MP_TAC o SPEC `SUC 0` o check is_step) THEN
    SIMP[NOT_CONS_NIL] THEN NO_TAC;
    STRIP_TAC THEN
    W(fun (_,w) -> let (_,b) = strip_exists w in let eq = fst(dest_conj b) in
                   let st,y = dest_pair(rand(lhs eq)) in MAP_EVERY EXISTS_TAC [st; y]) THEN
    REWRITE_TAC[] THEN GEN_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `SUC n` o check is_step) THEN SIMP[]];;

let PITRAUX_ttrace_nil = prove
 (`!(fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B)
    (X:((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
        (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree).
     (!n. PITRAUX_ttrace fs n X = []) ==> trace_prefix fs X = LNIL`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[trace_prefix_def; LFLATTEN_EQ_NIL] THEN
  MATCH_GOALSUB_ABBREV_TAC "LUNFOLD ff (SND fs,X)" THEN
  SUBGOAL_THEN `!ll:(io_event llist)llist.
      (?st Y. ll = LUNFOLD ff (st,Y) /\
              !n. PITRAUX_ttrace (FST (fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B),st) n
                    (Y:((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
                        (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree) = [])
      ==> llist_every ((=) LNIL) ll` MATCH_MP_TAC THENL
   [ALL_TAC;
    MAP_EVERY EXISTS_TAC [`SND (fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B)`;
      `X:((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
          (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree`] THEN
    ASM_REWRITE_TAC[PAIR]] THEN
  MATCH_MP_TAC llist_every_coind THEN REPEAT GEN_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `st:B` (X_CHOOSE_THEN
    `Y:((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
        (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o ONCE_REWRITE_RULE[LUNFOLD] o check (fun th -> is_eq (concl th) &&
    (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "LCONS" with Failure _ -> false))) THEN
  EXPAND_TAC "ff" THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[pair_CASE] THEN
  QCASES_ON "Y" THEN TRY(RENAME1 "Vis e0 g0" THEN PAIR_CASES_ON `e0:ev`) THEN SIMP[] THEN
  REPEAT(CASE_TAC ORELSE COND_CASES_TAC) THEN SIMP[] THEN
  PITRAUX_NIL_STEP_TAC);;

(* the trace after the first n steps: the run continues from some oracle *)
(* state fs' and tree Y                                                  *)

let PITRAUX_ttrace_split = prove
 (`!n (fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B)
      (X:((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
          (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree).
     ?(fs':(ffiname->B->byte list->byte list->(B)oracle_result)#B)
      (Y:((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
          (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree).
       trace_prefix fs X =
       LAPPEND (llist_fromList (PITRAUX_ttrace fs n X)) (trace_prefix fs' Y) /\
       !m. PITRAUX_ttrace fs (n + m) X =
           APPEND (PITRAUX_ttrace fs n X) (PITRAUX_ttrace fs' m Y)`,
  INDUCT_TAC THEN REPEAT GEN_TAC THENL
   [MAP_EVERY EXISTS_TAC [`fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B`;
      `X:((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
          (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree`] THEN
    REWRITE_TAC[PITRAUX_ttrace_simps; llist_fromList_def; LAPPEND; APPEND; ADD_CLAUSES];
    ALL_TAC] THEN
  QCASES_ON "X" THENL
   [MAP_EVERY EXISTS_TAC [`fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B`;
      `itree_Ret x:((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
                    (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree`] THEN
    REWRITE_TAC[ADD_CLAUSES; PITRAUX_ttrace_simps; trace_prefix_simps; llist_fromList_def;
                LAPPEND; APPEND] THEN
    REWRITE_TAC[REWRITE_RULE[ITER] (ISPEC `0` PITRAUX_ttrace_FUNPOW_Ret)];
    FIRST_X_ASSUM(X_CHOOSE_THEN `fs':(ffiname->B->byte list->byte list->(B)oracle_result)#B`
      (X_CHOOSE_THEN `Y:((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
          (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree` STRIP_ASSUME_TAC) o
      SPECL [`fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B`;
             `u:((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
                 (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree`]) THEN
    MAP_EVERY EXISTS_TAC [`fs':(ffiname->B->byte list->byte list->(B)oracle_result)#B`;
      `Y:((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
          (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree`] THEN
    ASM_REWRITE_TAC[PITRAUX_ttrace_simps; trace_prefix_simps; ADD_CLAUSES];
    MP_TAC(ISPECL [`fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B`; `a:ev`;
       `g:(ffi_outcome+byte list)+((A)pan_result)option#(A)bstate->
          ((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
           (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree`;
       `g:(ffi_outcome+byte list)+((A)pan_result)option#(A)bstate->
          ((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
           (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree`]
       PITRAUX_Vis_step) THEN
    DISCH_THEN(X_CHOOSE_THEN `fs1:(ffiname->B->byte list->byte list->(B)oracle_result)#B`
      (X_CHOOSE_THEN `x1:(ffi_outcome+byte list)+((A)pan_result)option#(A)bstate`
        (X_CHOOSE_THEN `l1:io_event list` STRIP_ASSUME_TAC))) THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `fs':(ffiname->B->byte list->byte list->(B)oracle_result)#B`
      (X_CHOOSE_THEN `Y:((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
          (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree` STRIP_ASSUME_TAC) o
      SPECL [`fs1:(ffiname->B->byte list->byte list->(B)oracle_result)#B`;
             `(g:(ffi_outcome+byte list)+((A)pan_result)option#(A)bstate->
                 ((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
                  (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree) x1`]) THEN
    MAP_EVERY EXISTS_TAC [`fs':(ffiname->B->byte list->byte list->(B)oracle_result)#B`;
      `Y:((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
          (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree`] THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; APPEND_ASSOC] THEN
    REWRITE_TAC[GSYM LAPPEND_fromList; LAPPEND_ASSOC]]);;

let PITRAUX_ttrace_mono = prove
 (`!n m (fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B)
      (X:((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
          (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree).
     PITRAUX_ttrace fs n X <<= PITRAUX_ttrace fs (n + m) X`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`n:num`; `fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B`;
                 `X:((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
                     (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree`]
                PITRAUX_ttrace_split) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[IS_PREFIX_APPEND3]);;

(* ------------------------------------------------------------------------- *)
(* Every n-step I/O of the itree is covered by a run of evaluate.            *)
(* ------------------------------------------------------------------------- *)

let PITRAUX_LPREFIX_fromList_fromList = prove
 (`!l1 l2:A list. LPREFIX (llist_fromList l1) (llist_fromList l2) <=> l1 <<= l2`,
  REWRITE_TAC[LPREFIX_fromList; from_toList] THEN SIMP[]);;

(* a run that does not time out covers every n-step I/O *)

let PITRAUX_ttrace_nonto = prove
 (`!p (s:(A,B)pan_state) r t.
     pan_evaluate (p,s) = (r,t) /\ ~(r = SOME pan_TimeOut)
     ==> !n. APPEND (ffi_state_io_events (pan_state_ffi s))
               (PITRAUX_ttrace (ffi_state_oracle (pan_state_ffi s),
                                ffi_state_ffi_state (pan_state_ffi s)) n
                  (mrec h_prog (h_prog (p,pan_itreeSem_bst s))))
             <<= ffi_state_io_events (pan_state_ffi t)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP evaluate_nondiv_trace_eq) THEN
  REWRITE_TAC[GSYM PITRAUX_LPREFIX_fromList_fromList; GSYM LAPPEND_fromList] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[LPREFIX_LAPPEND_fromList; PITRAUX_ttrace_LPREFIX]);;

let PITRAUX_ttrace_Tau = prove
 (`!n (fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B)
      (u:((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
          (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree).
     PITRAUX_ttrace fs n (Tau u) = PITRAUX_ttrace fs (n - 1) u`,
  INDUCT_TAC THEN REWRITE_TAC[PITRAUX_ttrace_simps; SUC_SUB1; SUB_0]);;

(* a bind whose continuation always returns has the n-step I/O of its    *)
(* first tree                                                             *)

let PITRAUX_ttrace_bind_ret = prove
 (`!n (fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B)
      (X:((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
          (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree) k.
     (!a. ?x. k a = itree_Ret x)
     ==> PITRAUX_ttrace fs n (itree_bind X k) = PITRAUX_ttrace fs n X`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B`;
                `X:((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
                    (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree`;
                `k:(ffi_outcome+byte list)+((A)pan_result)option#(A)bstate->
                   ((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
                    (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree`]
                PITRAUX_ttrace_bind) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `x:(ffi_outcome+byte list)+((A)pan_result)option#(A)bstate` o
    SPEC `r:(ffi_outcome+byte list)+((A)pan_result)option#(A)bstate`) THEN
  ASM_REWRITE_TAC[REWRITE_RULE[ITER] (ISPEC `0` PITRAUX_ttrace_FUNPOW_Ret); APPEND_NIL] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP PITRAUX_ttrace_Ret) THEN ASM_MESON_TAC[]);;

let PITRAUX_EXISTS_PAIR_SND = prove
 (`!(E:A#B) (Q:B->bool). (?r t. E = (r,t) /\ Q t) <=> Q (SND E)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [STRIP_TAC THEN ASM_REWRITE_TAC[SND];
    DISCH_TAC THEN MAP_EVERY EXISTS_TAC [`FST (E:A#B)`; `SND (E:A#B)`] THEN
    ASM_REWRITE_TAC[PAIR]]);;

let PITRAUX_io_mono_SND2 = prove
 (`!q (x:(A,B)pan_state) (y:(A,B)pan_state).
     ffi_state_io_events (pan_state_ffi y) = ffi_state_io_events (pan_state_ffi x)
     ==> ffi_state_io_events (pan_state_ffi y) <<=
         ffi_state_io_events (pan_state_ffi (SND (pan_evaluate (q,x))))`,
  MESON_TAC[PSEMAUX_io_events_mono_SND]);;

(* the case split of PITRAUX_ttrace_bind for the n-step I/O of a bind in *)
(* the goal                                                               *)

let PITRAUX_TTRACE_BIND_TAC : tactic = fun (asl,w as g) ->
  let t = find_term (fun t -> try let h,args = strip_comb t in
            fst(dest_const h) = "PITRAUX_ttrace" && length args = 3 &&
            fst(dest_const(fst(strip_comb(el 2 args)))) = "itree_bind"
          with Failure _ -> false) w in
  let _,args = strip_comb t in
  let fs = el 0 args and m = el 1 args and b = el 2 args in
  let _,bargs = strip_comb b in
  (MP_TAC(ISPECL [m; fs; el 0 bargs; el 1 bargs] PITRAUX_ttrace_bind) THEN
   DISCH_THEN(DISJ_CASES_THEN2
     (X_CHOOSE_THEN `m1:num` (X_CHOOSE_THEN
        `rr:(ffi_outcome+byte list)+((A)pan_result)option#(A)bstate` STRIP_ASSUME_TAC))
     ASSUME_TAC) THEN
   ASM_REWRITE_TAC[]) g;;

(* n = 0: any run covers the empty I/O *)

let PITRAUX_C_ZERO_TAC : tactic =
  REWRITE_TAC[PITRAUX_ttrace_simps; APPEND_NIL] THEN QEXISTS_TAC "0" THEN
  W(fun (_,w) -> let ev = lhs(fst(dest_conj(snd(strip_exists w)))) in
                 MP_TAC(ISPEC ev PAIR_SURJECTIVE)) THEN
  DISCH_THEN(X_CHOOSE_THEN `r0:((A)pan_result)option`
   (X_CHOOSE_THEN `t0:(A,B)pan_state` ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`r0:((A)pan_result)option`; `t0:(A,B)pan_state`] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP pan_evaluate_io_events_mono) THEN SIMP[];;

(* a leaf: the run with clock 1 does not time out *)

let PITRAUX_C_LEAF_TAC : tactic =
  QEXISTS_TAC "SUC 0" THEN
  W(fun (_,w) -> let ev = lhs(fst(dest_conj(snd(strip_exists w)))) in
                 MP_TAC(ISPEC ev PAIR_SURJECTIVE)) THEN
  DISCH_THEN(X_CHOOSE_THEN `r0:((A)pan_result)option`
   (X_CHOOSE_THEN `t0:(A,B)pan_state` ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`r0:((A)pan_result)option`; `t0:(A,B)pan_state`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(r0 = SOME (pan_TimeOut:(A)pan_result))` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o ONCE_REWRITE_RULE[pan_evaluate_def]) THEN DISCH_TAC THEN
    GVS(all_case_eqs() @ [ONELINE nb_op_def; pan_sh_mem_load_def; pan_sh_mem_store_def;
        pan_empty_locals_def; kvar_defs; pan_dec_clock_def; call_FFI_def; COND_CASE_EQ;
        pan_eval_upd_clock_eq; opt_mmap_eval_upd_clock_eq1]);
    ALL_TAC] THEN
  FIRST_ASSUM(fun eq -> if is_eq(concl eq) && (try fst(dest_const(fst(strip_comb(lhs(concl eq))))) =
                               "pan_evaluate" with Failure _ -> false)
    then MP_TAC(SPEC `n:num` (MATCH_MP PITRAUX_ttrace_nonto (CONJ eq
           (ASSUME `~(r0 = SOME (pan_TimeOut:(A)pan_result))`))))
    else failwith "") THEN
  SIMP[];;

(* the backward simulation for the sub-run of the assumption ltree _      *)
(* (mrec h_prog (h_prog (q0,pan_itreeSem_bst s0))) = ITER m1 Tau (Ret rr): rr becomes  *)
(* INR (q1,pan_itreeSem_bst t1) for a run pan_evaluate (q0,clock k1 s0) = (q1,t1) that *)
(* does not time out, whose I/O is that of s0 and the m1-step I/O         *)

let PITRAUX_C_BACK_TAC : tactic = fun (asl,w as g) ->
  let is_ltree th = let c = concl th in is_eq c &&
     (try fst(dest_const(fst(strip_comb(lhs c)))) = "ltree" with Failure _ -> false) in
  let th = snd(find (fun (_,th) -> is_ltree th) asl) in
  let c = concl th in
  let mr = rand(lhs c) in
  let q0, b0 = dest_pair(rand(rand mr)) in
  let s0 = rand b0 in
  let m1 = hd(snd(strip_comb(rhs c))) in
  (MP_TAC(MATCH_MP nondiv_INR th) THEN
   DISCH_THEN(X_CHOOSE_THEN `xx:((A)pan_result)option#(A)bstate` SUBST_ALL_TAC) THEN
   PAIR_CASES_ON `xx:((A)pan_result)option#(A)bstate` THEN
   RENAME1 "INR (q1,st1)" THEN
   MP_TAC(ISPECL [m1; q0; s0; `q1:((A)pan_result)option`; `st1:(A)bstate`]
                 PITRAUX_ltree_imp_evaluate) THEN
   ANTS_TAC THENL [FIRST_ASSUM(MP_TAC o check is_ltree) THEN SIMP[]; ALL_TAC] THEN
   DISCH_THEN(X_CHOOSE_THEN `k1:num` (X_CHOOSE_THEN `t1:(A,B)pan_state`
     (STRIP_ASSUME_TAC o CAKE_SIMP_RULE []))) THEN
   FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th' ->
     try fst(dest_const(fst(strip_comb(lhs(concl th'))))) = "pan_itreeSem_bst" with Failure _ -> false)) THEN
   PITRAUX_ON_EVAL_TAC (fun eq -> FIRST_ASSUM(MP_TAC o MATCH_MP evaluate_nondiv_trace_eq o
                                               CONJ eq)) THEN
   SIMP[] THEN
   FIRST_ASSUM(fun th' -> if is_ltree th'
                          then REWRITE_TAC[CONJUNCT1(MATCH_MP PITRAUX_ttrace_Ret th')]
                          else failwith "") THEN
   REWRITE_TAC[LAPPEND_fromList; fromList_11] THEN DISCH_TAC THEN SIMP[] THEN
   FIRST_X_ASSUM(fun th' -> let c = concl th' in
     if is_eq c && (try fst(dest_const(fst(strip_comb(rhs c)))) = "SND" with Failure _ -> false)
     then REWRITE_TAC[GSYM th'] else failwith "")) g;;

(* the induction hypothesis for the sub-run of the n-step I/O term of the *)
(* goal chosen by pick (among those with an mrec tree): adds the run      *)
(* pan_evaluate (q,clock k2 x) = (r2,t2) and its I/O fact                  *)

let PITRAUX_C_IH_AT_TAC (pick:term list->term) : tactic = fun (asl,w as g) ->
  let tts = find_terms (fun t -> try let h,args = strip_comb t in
       fst(dest_const h) = "PITRAUX_ttrace" && length args = 3 &&
       fst(dest_const(fst(strip_comb(el 2 args)))) = "mrec" with Failure _ -> false) w in
  let t = pick tts in
  let _,args = strip_comb t in
  let cnt = el 1 args and tr = el 2 args in
  let q, b = dest_pair(rand(rand tr)) in
  let x = rand b in
  (FIRST_ASSUM(MP_TAC o SPEC cnt) THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   DISCH_THEN(MP_TAC o SPECL [q; x]) THEN SIMP[] THEN
   DISCH_THEN(X_CHOOSE_THEN `k2:num` (X_CHOOSE_THEN `r2:((A)pan_result)option`
     (X_CHOOSE_THEN `t2:(A,B)pan_state` STRIP_ASSUME_TAC)))) g;;

(* the ttrace term whose count is not m1 *)

let PITRAUX_PICK_OTHER tts =
  find (fun t -> not (el 1 (snd(strip_comb t)) = `m1:num`)) tts;;

let PITRAUX_C_SIMPS () =
  [pan_eval_upd_clock_eq; opt_mmap_eval_upd_clock_eq1; pan_dec_clock_def; SUC_SUB1;
   kvar_defs2; empty_locals_defs; IS_PREFIX_REFL];;

(* the second sub-run, after the first (q0) made to end with clock k2 *)

let PITRAUX_C_CONT_TAC (q0:term) (kf:term->term) : tactic =
  SIMP[PITRAUX_ttrace_Tau; PITRAUX_ttrace_bind_ret; kvar_defs2; empty_locals_defs] THEN
  PITRAUX_C_IH_AT_TAC PITRAUX_PICK_OTHER THEN
  PITRAUX_ANY_CLOCK_TAC q0 `k2:num` THEN SIMP[] THEN
  DISCH_THEN(X_CHOOSE_TAC `k3:num`) THEN
  EXISTS_TAC (kf `k3:num`) THEN ONCE_REWRITE_TAC[pan_evaluate_def] THEN
  ASM_REWRITE_TAC[] THEN SIMP(PITRAUX_C_SIMPS());;

(* the construct ends with the first sub-run *)

let PITRAUX_C_FIN_TAC (kf:term->term) : tactic =
  SIMP[REWRITE_RULE[ITER] (ISPEC `0` PITRAUX_ttrace_FUNPOW_Ret); APPEND_NIL] THEN
  EXISTS_TAC (kf `k1:num`) THEN ONCE_REWRITE_TAC[pan_evaluate_def] THEN
  ASM_REWRITE_TAC[] THEN SIMP(PITRAUX_C_SIMPS());;

(* the goal from the io monotonicity of some run of the assumptions *)

let PITRAUX_IO_MONO_TAC : tactic = fun (asl,w as g) ->
  let eqs = filter (fun (_,th) -> let c = concl th in
    is_eq c && (try fst(dest_const(fst(strip_comb(lhs c)))) = "pan_evaluate"
                with Failure _ -> false)) asl in
  FIRST (map (fun (_,th) -> MP_TAC(MATCH_MP pan_evaluate_io_events_mono th) THEN
                             SIMP[kvar_defs2; empty_locals_defs] THEN NO_TAC) eqs) g;;

let PITRAUX_C_FIRST_TAC (q:term) (st:term) (kf:term->term) : tactic =
  FIRST_ASSUM(MP_TAC o SPEC `n - 1`) THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [q; st]) THEN SIMP[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k1:num` (X_CHOOSE_THEN `r1:((A)pan_result)option`
    (X_CHOOSE_THEN `t1:(A,B)pan_state` STRIP_ASSUME_TAC))) THEN
  EXISTS_TAC (kf `k1:num`) THEN REWRITE_TAC[PITRAUX_EXISTS_PAIR_SND] THEN
  MATCH_MP_TAC IS_PREFIX_TRANS THEN
  EXISTS_TAC `ffi_state_io_events (pan_state_ffi (t1:(A,B)pan_state))` THEN
  CONJ_TAC THENL [ALL_TAC; FIRST_X_ASSUM(MP_TAC o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "isPREFIX" with Failure _ -> false)) THEN
    SIMP[]] THEN
  ONCE_REWRITE_TAC[pan_evaluate_def] THEN
  SIMP[pan_eval_upd_clock_eq; opt_mmap_eval_upd_clock_eq1; pan_dec_clock_def; SUC_SUB1] THEN
  REPEAT((COND_CASES_TAC ORELSE CASE_TAC) THEN SIMP[]) THEN PITRAUX_VK_CASES_TAC THEN
  SIMP[IS_PREFIX_REFL; PITRAUX_io_mono_SND2; empty_locals_defs; kvar_defs2] THEN
  TRY PITRAUX_IO_MONO_TAC;;

(* the first sub-run (q,st) of the construct has not ended within the    *)
(* steps above: PITRAUX_C_FIRST_TAC; it has ended: PITRAUX_C_BACK_TAC,   *)
(* then the construct ends (PITRAUX_C_FIN_TAC) or runs a second program  *)
(* (PITRAUX_C_CONT_TAC)                                                   *)

let PITRAUX_C_SEQ_TAC =
  REWRITE_TAC[mrec_prog_nonrec] THEN SIMP[PITRAUX_ttrace_Tau] THEN PITRAUX_TTRACE_BIND_TAC THENL
   [PITRAUX_C_BACK_TAC THEN QCASES_ON "q1" THENL
     [PITRAUX_C_CONT_TAC `a0:(A)panLang_prog` I; PITRAUX_C_FIN_TAC I];
    PITRAUX_C_FIRST_TAC `a0:(A)panLang_prog` `s:(A,B)pan_state` I];;

let PITRAUX_C_COND_CASES_TAC =
  QCASES_ON "pan_eval (s:(A,B)pan_state) a0" THEN
  TRY(RENAME1 "pan_eval s a0 = SOME v0" THEN QCASES_ON "v0" THEN
      TRY(RENAME1 "pan_eval s a0 = SOME (pan_Val w0)" THEN QCASES_ON "w0" THEN
          RENAME1 "pan_eval s a0 = SOME (pan_Val (Word w1))" THEN
          ASM_CASES_TAC `w1 = word 0:A word`)) THEN
  TRY(PITRAUX_C_LEAF_TAC THEN NO_TAC);;

let PITRAUX_C_WHILE_TAC =
  PITRAUX_C_COND_CASES_TAC THEN
  ONCE_REWRITE_TAC[mrec_While] THEN ASM_SIMP_TAC[eval_bst] THEN SIMP[PITRAUX_ttrace_Tau] THEN
  PITRAUX_TTRACE_BIND_TAC THENL
   [PITRAUX_C_BACK_TAC THEN QCASES_ON "q1" THEN
    TRY(RENAME1 "SOME r0" THEN QCASES_ON "r0") THEN
    FIRST [PITRAUX_C_CONT_TAC `a1:(A)panLang_prog` (curry mk_comb `SUC`) THEN NO_TAC;
           PITRAUX_C_FIN_TAC (curry mk_comb `SUC`) THEN NO_TAC];
    PITRAUX_C_FIRST_TAC `a1:(A)panLang_prog` `s:(A,B)pan_state` (curry mk_comb `SUC`)];;

let PITRAUX_C_IF_TAC =
  PITRAUX_C_COND_CASES_TAC THEN
  REWRITE_TAC[mrec_If] THEN ASM_SIMP_TAC[eval_bst] THEN
  SIMP[PITRAUX_ttrace_Tau; PITRAUX_ttrace_bind_ret] THEN
  PITRAUX_C_IH_AT_TAC hd THEN
  EXISTS_TAC `k2:num` THEN ONCE_REWRITE_TAC[pan_evaluate_def] THEN
  ASM_REWRITE_TAC[] THEN SIMP(PITRAUX_C_SIMPS());;

let PITRAUX_C_DEC_TAC =
  QCASES_ON "pan_eval (s:(A,B)pan_state) a2" THEN
  TRY(RENAME1 "pan_eval s a2 = SOME v0" THEN ASM_CASES_TAC `a1 = shape_of (v0:(A)pan_v)`) THEN
  TRY(PITRAUX_C_LEAF_TAC THEN NO_TAC) THEN
  REWRITE_TAC[mrec_prog_nonrec] THEN ASM_SIMP_TAC[eval_bst] THEN
  SIMP[PITRAUX_ttrace_Tau; PITRAUX_ttrace_bind_ret] THEN
  PITRAUX_C_IH_AT_TAC hd THEN
  EXISTS_TAC `k2:num` THEN ONCE_REWRITE_TAC[pan_evaluate_def] THEN
  ASM_REWRITE_TAC[] THEN SIMP(PITRAUX_C_SIMPS());;

let PITRAUX_C_CALL_TAC (rw:thm) =
  W(fun (asl,w) ->
     let c = rand(lhs(fst(dest_conj(snd(strip_exists w))))) in
     let p = fst(dest_pair c) in
     let args = snd(strip_comb p) in
     let isdc = fst(dest_const(fst(strip_comb p))) = "DecCall" in
     let argexps = el (length args - (if isdc then 2 else 1)) args in
     let fname = el (length args - (if isdc then 3 else 2)) args in
     QCASES_ON ("OPT_MMAP (pan_eval (s:(A,B)pan_state)) " ^ string_of_term argexps) THEN
     TRY(RENAME1 "OPT_MMAP (pan_eval s) _ = SOME args0" THEN
         QCASES_ON ("pan_lookup_code (pan_state_code (s:(A,B)pan_state)) " ^
                    string_of_term fname ^ " args0") THEN
         TRY(RENAME1 "pan_lookup_code _ _ _ = SOME x0" THEN
             PAIR_CASES_ON `x0:(A)panLang_prog#(mlstring,(A)pan_v)fmap#shape`))) THEN
  TRY(PITRAUX_C_LEAF_TAC THEN NO_TAC) THEN
  REWRITE_TAC[rw] THEN ASM_SIMP_TAC[opt_mmap_eval_bst; bst_access] THEN
  SIMP[PITRAUX_ttrace_Tau] THEN PITRAUX_TTRACE_BIND_TAC THENL
   [PITRAUX_C_BACK_TAC THEN
    SIMP[o_THM; mrec_h_handle_call_ret_lemma; mrec_h_handle_deccall_ret_lemma] THEN
    REPEAT((CASE_TAC ORELSE COND_CASES_TAC) THEN SIMP[]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
    TRY(FIRST_ASSUM(CONTR_TAC o check (fun th -> concl th = `F`)) THEN NO_TAC) THEN
    PITRAUX_VK_CASES_TAC THEN RULE_ASSUM_TAC(CAKE_SIMP_RULE [kvar_defs2; bst_access]) THEN
    FIRST [PITRAUX_C_FIN_TAC (curry mk_comb `SUC`) THEN NO_TAC;
           PITRAUX_C_CONT_TAC `x00:(A)panLang_prog` (curry mk_comb `SUC`) THEN NO_TAC];
    PITRAUX_C_FIRST_TAC `x00:(A)panLang_prog` `pan_state_locals_fupd (K x01) (s:(A,B)pan_state)`
                        (curry mk_comb `SUC`)];;

(* every n-step I/O of the itree of a program is covered by a run of     *)
(* evaluate with some clock; by induction on n, the program cases one by *)
(* one                                                                    *)

let PITRAUX_ttrace_evaluate = prove
 (`!n p (s:(A,B)pan_state).
     ?k r t. pan_evaluate (p,pan_state_clock_fupd (K k) s) = (r,t) /\
             APPEND (ffi_state_io_events (pan_state_ffi s))
               (PITRAUX_ttrace (ffi_state_oracle (pan_state_ffi s),
                                ffi_state_ffi_state (pan_state_ffi s)) n
                  (mrec h_prog (h_prog (p,pan_itreeSem_bst s))))
             <<= ffi_state_io_events (pan_state_ffi t)`,
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  GEN_TAC THEN GEN_TAC THEN ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[] THEN PITRAUX_C_ZERO_TAC; ALL_TAC] THEN
  QCASES_ON "p" THEN REPEAT GEN_TAC THENL
   [PITRAUX_C_LEAF_TAC; PITRAUX_C_DEC_TAC; PITRAUX_C_LEAF_TAC; PITRAUX_C_LEAF_TAC;
    PITRAUX_C_LEAF_TAC; PITRAUX_C_LEAF_TAC; PITRAUX_C_LEAF_TAC; PITRAUX_C_SEQ_TAC;
    PITRAUX_C_IF_TAC; PITRAUX_C_WHILE_TAC; PITRAUX_C_LEAF_TAC; PITRAUX_C_LEAF_TAC;
    PITRAUX_C_CALL_TAC mrec_Call; PITRAUX_C_CALL_TAC mrec_DecCall;
    PITRAUX_C_LEAF_TAC; PITRAUX_C_LEAF_TAC; PITRAUX_C_LEAF_TAC; PITRAUX_C_LEAF_TAC;
    PITRAUX_C_LEAF_TAC; PITRAUX_C_LEAF_TAC; PITRAUX_C_LEAF_TAC]);;

let PITRAUX_ttrace_FUNPOW_Tau = prove
 (`!n m (fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B)
      (Y:((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
          (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree).
     PITRAUX_ttrace fs (n + m) (ITER n Tau Y) = PITRAUX_ttrace fs m Y`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[ITER; ADD_CLAUSES; PITRAUX_ttrace_simps]);;

(* a program with no I/O at any clock (from clock 0) has an empty n-step *)
(* I/O for every n                                                        *)

let PITRAUX_no_io_ttrace_nil = prove
 (`!p (s:(A,B)pan_state).
     (!k. ffi_state_io_events (pan_state_ffi s) =
          ffi_state_io_events (pan_state_ffi (SND (pan_evaluate
            (p,pan_state_clock_fupd (K (k + pan_state_clock s)) s))))) /\
     pan_state_clock s = 0
     ==> !n. PITRAUX_ttrace (ffi_state_oracle (pan_state_ffi s),
                             ffi_state_ffi_state (pan_state_ffi s)) n
               (mrec h_prog (h_prog (p,pan_itreeSem_bst s))) = []`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `n:num` THEN
  MP_TAC(ISPECL [`n:num`; `p:(A)panLang_prog`; `s:(A,B)pan_state`] PITRAUX_ttrace_evaluate) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `r:((A)pan_result)option`
    (X_CHOOSE_THEN `t:(A,B)pan_state` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN
  DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o MATCH_MP IS_PREFIX_LENGTH o
    REWRITE_RULE[GSYM th] o check (fun th' ->
      try fst(dest_const(fst(strip_comb(concl th')))) = "isPREFIX" with Failure _ -> false))) THEN
  REWRITE_TAC[LENGTH_APPEND; GSYM LENGTH_EQ_NIL] THEN ARITH_TAC);;

(* a run of a program from clock 0 with no I/O at any clock: the first   *)
(* call of its itree cannot succeed (HOL4 proves it by induction on n and *)
(* the program; here a successful call would be an event of the n-step   *)
(* I/O, which PITRAUX_ttrace_evaluate puts into a run)                     *)

let mrec_Vis_no_trace_lemma = prove
 (`!p (s:(A,B)pan_state) n a g (fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B) X.
     mrec h_prog (h_prog (p,pan_itreeSem_bst s)) = ITER n Tau (Vis a g) /\
     (!k. ffi_state_io_events (pan_state_ffi s) =
          ffi_state_io_events (pan_state_ffi (SND (pan_evaluate
            (p,pan_state_clock_fupd (K (k + pan_state_clock s)) s))))) /\
     FST fs = ffi_state_oracle (pan_state_ffi s) /\
     SND fs = ffi_state_ffi_state (pan_state_ffi s) /\
     pan_state_clock s = 0 /\
     FST fs (FST a) (SND fs) (FST (SND a)) (SND (SND a)) = X
     ==> (?f l. X = Oracle_return f l /\ ~(LENGTH (SND (SND a)) = LENGTH l)) \/
         (?f. X = Oracle_final f)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  SUBGOAL_THEN `(fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B) =
                (ffi_state_oracle (pan_state_ffi (s:(A,B)pan_state)),
                 ffi_state_ffi_state (pan_state_ffi s))` SUBST_ALL_TAC THENL
   [ASM_MESON_TAC[PAIR]; ALL_TAC] THEN
  MP_TAC(ISPECL [`p:(A)panLang_prog`; `s:(A,B)pan_state`] PITRAUX_no_io_ttrace_nil) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `n + 1`) THEN
  PAIR_CASES_ON `a:ev` THEN REWRITE_TAC[FST; SND; PITRAUX_ttrace_FUNPOW_Tau; ONE;
                                        PITRAUX_ttrace_simps] THEN
  QCASES_ON "ffi_state_oracle (pan_state_ffi (s:(A,B)pan_state)) a0 (ffi_state_ffi_state (pan_state_ffi s)) a1 a2" THEN
  REWRITE_TAC[injectivity "oracle_result"; distinctness "oracle_result"] THEN
  SIMP[NOT_CONS_NIL] THEN TRY(COND_CASES_TAC THEN REWRITE_TAC[NOT_CONS_NIL]));;

(* HOL4 proves evaluate_mrec_FUNPOW_Ret_io_events by induction on        *)
(* evaluate; here: the forward simulation gives a terminating oracle run *)
(* with an empty trace, so the itree has no FFI call                     *)

let evaluate_mrec_FUNPOW_Ret_io_events = prove
 (`!p (s0:(A,B)pan_state) res t s k ffi.
     pan_evaluate (p,s0) = (res,t) /\ s0 = pan_itreeSem_ext s k ffi /\
     ffi_state_io_events (pan_state_ffi t) = ffi_state_io_events ffi /\
     (!fe. ~(res = SOME (pan_FinalFFI fe))) /\ ~(res = SOME pan_TimeOut)
     ==> ?n. mrec h_prog (h_prog (p,s)) = ITER n Tau (itree_Ret (INR (res,pan_itreeSem_bst t)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC)) THEN
  PITRAUX_ON_EVAL_TAC (fun eq -> FIRST_ASSUM(MP_TAC o MATCH_MP PITRAUX_evaluate_ltree o
                                              CONJ eq)) THEN
  REWRITE_TAC[bst_ext_id; ext_access] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `n:num`) (ASSUME_TAC o CONJUNCT2)) THEN
  EXISTS_TAC `n:num` THEN MATCH_MP_TAC PITRAUX_mrec_nil_trace_Ret THEN
  EXISTS_TAC `(ffi_state_oracle (ffi:(B)ffi_state),ffi_state_ffi_state ffi)` THEN
  ASM_REWRITE_TAC[injectivity "sum"; PAIR_EQ] THEN
  FIRST_X_ASSUM(MP_TAC o SYM o check (fun th ->
    can (find_term (fun t -> try fst(dest_const t) = "LAPPEND" with Failure _ -> false))
        (concl th))) THEN
  SIMP[LFINITE_LAPPEND_EQ_NIL; LFINITE_fromList]);;

let evaluate_mrec_FUNPOW_Ret = prove
 (`!p (s:(A,B)pan_state) res t.
     pan_evaluate (p,s) = (res,t) /\ pan_state_ffi t = pan_state_ffi s /\
     (!fe. ~(res = SOME (pan_FinalFFI fe))) /\ ~(res = SOME pan_TimeOut)
     ==> ?n. mrec h_prog (h_prog (p,pan_itreeSem_bst s)) =
             ITER n Tau (itree_Ret (INR (res,pan_itreeSem_bst t)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC evaluate_mrec_FUNPOW_Ret_io_events THEN
  MAP_EVERY EXISTS_TAC [`s:(A,B)pan_state`; `pan_state_clock (s:(A,B)pan_state)`;
                        `pan_state_ffi (s:(A,B)pan_state)`] THEN
  ASM_REWRITE_TAC[ext_bst_id]);;

(* the n-th call after n Taus fails (mrec_Vis_no_trace_lemma), so the     *)
(* itree ends in FinalFFI after it (PITRAUX_mrec_Vis_fail)                *)

let PITRAUX_FAIL_INST_GOAL_TAC : tactic = fun (asl,w as g) ->
  let t = find_term (fun t -> try fst(dest_const(rator t)) = "INL" &&
                                  fst(dest_const(rator(rand t))) = "INL"
                              with Failure _ -> false) w in
  let x = rand(rand t) in
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o SPEC x o
    check (fun th -> is_forall (concl th) &&
                     type_of (fst (dest_forall (concl th))) = `:ffi_outcome`)) g;;

let mrec_Vis_nondiv_lemma = prove
 (`!p (s:(A,B)pan_state) n a g (fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B).
     mrec h_prog (h_prog (p,pan_itreeSem_bst s)) = ITER n Tau (Vis a g) /\
     (!k. ffi_state_io_events (pan_state_ffi s) =
          ffi_state_io_events (pan_state_ffi (SND (pan_evaluate
            (p,pan_state_clock_fupd (K (k + pan_state_clock s)) s))))) /\
     FST fs = ffi_state_oracle (pan_state_ffi s) /\
     SND fs = ffi_state_ffi_state (pan_state_ffi s) /\
     pan_state_clock s = 0
     ==> ~pan_itreeSem_div fs (mrec h_prog (h_prog (p,pan_itreeSem_bst s)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`p:(A)panLang_prog`; `s:(A,B)pan_state`; `n:num`; `a:ev`;
                 `g:(ffi_outcome+byte list)+((A)pan_result)option#(A)bstate->
                    ((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
                     (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree`;
                 `fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B`;
                 `FST (fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B)
                    (FST (a:ev)) (SND fs) (FST (SND a)) (SND (SND a))`]
                mrec_Vis_no_trace_lemma) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PITRAUX_mrec_Vis_fail) THEN
  ASM_REWRITE_TAC[nondiv_eq_Ret; ltree_FUNPOW_Tau] THEN
  PAIR_CASES_ON `a:ev` THEN REWRITE_TAC[FST; SND; ltree_simps] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN SIMP[] THEN PITRAUX_FAIL_INST_GOAL_TAC THEN
  ASM_REWRITE_TAC[PITRAUX_ltree_FUNPOW_Ret; PITRAUX_Tau_ITER; ITER_ADD] THEN MESON_TAC[]);;

(* HOL4 proves div_no_trace_LNIL with mrec_Vis_nondiv_lemma; here the     *)
(* n-step I/O is empty for every n (PITRAUX_no_io_ttrace_nil)             *)

let div_no_trace_LNIL = prove
 (`!p (s:(A,B)pan_state) (fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B).
     pan_itreeSem_div fs (mrec h_prog (h_prog (p,pan_itreeSem_bst s))) /\
     (!k. ffi_state_io_events (pan_state_ffi s) =
          ffi_state_io_events (pan_state_ffi (SND (pan_evaluate
            (p,pan_state_clock_fupd (K (k + pan_state_clock s)) s))))) /\
     FST fs = ffi_state_oracle (pan_state_ffi s) /\
     SND fs = ffi_state_ffi_state (pan_state_ffi s) /\
     pan_state_clock s = 0
     ==> trace_prefix fs (mrec h_prog (h_prog (p,pan_itreeSem_bst s))) = LNIL`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B) =
                (ffi_state_oracle (pan_state_ffi (s:(A,B)pan_state)),
                 ffi_state_ffi_state (pan_state_ffi s))` SUBST_ALL_TAC THENL
   [ASM_MESON_TAC[PAIR]; ALL_TAC] THEN
  MATCH_MP_TAC PITRAUX_ttrace_nil THEN MATCH_MP_TAC PITRAUX_no_io_ttrace_nil THEN
  ASM_REWRITE_TAC[]);;

(* HOL4 proves bounded_trace_eq by induction on evaluate; here: every    *)
(* n-step I/O is covered by a run (PITRAUX_ttrace_evaluate), so within  *)
(* the stable I/O; the n-step I/O then stops growing, the rest of the   *)
(* trace is empty (PITRAUX_ttrace_split, PITRAUX_ttrace_nil), and the    *)
(* run's I/O is a prefix of the trace (PITRAUX_evaluate_LPREFIX)         *)

let bounded_trace_eq = prove
 (`!p (s:(A,B)pan_state).
     (!k'. ffi_state_io_events (pan_state_ffi (SND (pan_evaluate (p,s)))) =
           ffi_state_io_events (pan_state_ffi (SND (pan_evaluate
             (p,pan_state_clock_fupd (K (k' + pan_state_clock s)) s))))) /\
     pan_itreeSem_div (ffi_state_oracle (pan_state_ffi s),ffi_state_ffi_state (pan_state_ffi s))
       (mrec h_prog (h_prog (p,pan_itreeSem_bst s)))
     ==> LAPPEND (llist_fromList (ffi_state_io_events (pan_state_ffi s)))
           (trace_prefix (ffi_state_oracle (pan_state_ffi s),
                          ffi_state_ffi_state (pan_state_ffi s))
              (mrec h_prog (h_prog (p,pan_itreeSem_bst s)))) =
         llist_fromList (ffi_state_io_events (pan_state_ffi (SND (pan_evaluate (p,s)))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `L = ffi_state_io_events (pan_state_ffi (SND (pan_evaluate (p,s:(A,B)pan_state))))` THEN
  ABBREV_TAC `fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B =
                (ffi_state_oracle (pan_state_ffi (s:(A,B)pan_state)),
                 ffi_state_ffi_state (pan_state_ffi s))` THEN
  FIRST_X_ASSUM(ASSUME_TAC o GSYM o check (fun th -> is_forall (concl th))) THEN
  SUBGOAL_THEN
   `!n. APPEND (ffi_state_io_events (pan_state_ffi (s:(A,B)pan_state)))
               (PITRAUX_ttrace (fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B) n
                  (mrec h_prog (h_prog (p,pan_itreeSem_bst s)))) <<= L`
   ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN
    MP_TAC(ISPECL [`n:num`; `p:(A)panLang_prog`; `s:(A,B)pan_state`] PITRAUX_ttrace_evaluate) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `r:((A)pan_result)option`
      (X_CHOOSE_THEN `t:(A,B)pan_state` STRIP_ASSUME_TAC))) THEN
    MATCH_MP_TAC IS_PREFIX_TRANS THEN
    EXISTS_TAC `ffi_state_io_events (pan_state_ffi (t:(A,B)pan_state))` THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `k <= pan_state_clock (s:(A,B)pan_state)` THENL
     [MP_TAC(ISPECL [`p:(A)panLang_prog`; `pan_state_clock_fupd (K k) (s:(A,B)pan_state)`;
                     `pan_state_clock (s:(A,B)pan_state) - k`]
                    pan_evaluate_add_clock_io_events_mono) THEN
      SIMP[] THEN ASM_SIMP_TAC[ARITH_RULE `k <= c ==> k + (c - k) = c`] THEN
      SUBGOAL_THEN `pan_state_clock_fupd (K (pan_state_clock s)) (s:(A,B)pan_state) = s`
        (fun th -> REWRITE_TAC[th]) THENL
       [REWRITE_TAC[pan_state_component_equality] THEN SIMP[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPEC `k - pan_state_clock (s:(A,B)pan_state)` o
        check (fun th -> is_forall (concl th) &&
          can (find_term (fun t -> t = `L:io_event list`)) (concl th))) THEN
      ASM_SIMP_TAC[ARITH_RULE `~(k <= c) ==> k - c + c = k`] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IS_PREFIX_REFL]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\n. LENGTH (PITRAUX_ttrace (fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B) n
                          (mrec h_prog (h_prog (p,pan_itreeSem_bst (s:(A,B)pan_state)))))`;
                 `LENGTH (L:io_event list)`] PITRAUX_MONO_BOUNDED_CONST) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [X_GEN_TAC `n:num` THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP IS_PREFIX_LENGTH o SPEC `n:num`) THEN
      REWRITE_TAC[LENGTH_APPEND] THEN ARITH_TAC;
      REPEAT GEN_TAC THEN
      DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST1_TAC o REWRITE_RULE[LE_EXISTS]) THEN
      MATCH_MP_TAC IS_PREFIX_LENGTH THEN REWRITE_TAC[PITRAUX_ttrace_mono]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `n0:num`) THEN
  MP_TAC(ISPECL [`n0:num`; `fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B`;
                 `mrec h_prog (h_prog (p,pan_itreeSem_bst (s:(A,B)pan_state)))`] PITRAUX_ttrace_split) THEN
  DISCH_THEN(X_CHOOSE_THEN `fs':(ffiname->B->byte list->byte list->(B)oracle_result)#B`
    (X_CHOOSE_THEN `Y:((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
          (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `trace_prefix (fs':(ffiname->B->byte list->byte list->(B)oracle_result)#B)
                  (Y:((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
                      (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree) = LNIL`
    ASSUME_TAC THENL
   [MATCH_MP_TAC PITRAUX_ttrace_nil THEN X_GEN_TAC `m:num` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `m:num` o check (fun th -> is_forall (concl th) &&
      can (find_term (fun t -> t = `fs':(ffiname->B->byte list->byte list->(B)oracle_result)#B`))
          (concl th))) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n0 + m:num` o check (fun th -> is_forall (concl th) &&
      can (find_term (fun t -> t = `n0:num`)) (concl th))) THEN
    REWRITE_TAC[LE_ADD] THEN
    DISCH_THEN(fun th -> DISCH_THEN(MP_TAC o AP_TERM `LENGTH:io_event list->num`) THEN
                         REWRITE_TAC[th]) THEN
    REWRITE_TAC[LENGTH_APPEND; ARITH_RULE `a = a + b <=> b = 0`; LENGTH_EQ_NIL];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[LAPPEND_NIL_2ND; LAPPEND_fromList; fromList_11] THEN
  MATCH_MP_TAC IS_PREFIX_ANTISYM THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `n0:num` o check (fun th -> is_forall (concl th) &&
      try fst(dest_const(fst(strip_comb(snd(dest_forall(concl th)))))) = "isPREFIX"
      with Failure _ -> false)) THEN REWRITE_TAC[];
    MP_TAC(ISPECL [`p:(A)panLang_prog`; `s:(A,B)pan_state`;
                   `FST (pan_evaluate (p,s:(A,B)pan_state))`;
                   `SND (pan_evaluate (p,s:(A,B)pan_state))`] PITRAUX_evaluate_LPREFIX) THEN
    ASM_REWRITE_TAC[PAIR; LAPPEND_NIL_2ND; LAPPEND_fromList;
                    PITRAUX_LPREFIX_fromList_fromList]]);;

(* ------------------------------------------------------------------------- *)
(* The behaviours of the two semantics agree.                                *)
(* ------------------------------------------------------------------------- *)

let evaluate_behaviour_def = cake_def
 `evaluate_behaviour ((prog:(A)panLang_prog),(s:(A,B)pan_state)) =
    if ?k. match FST (pan_evaluate (prog,pan_state_clock_fupd (K k) s)) with
             SOME pan_TimeOut -> F
           | SOME (pan_FinalFFI _) -> F
           | SOME (pan_Return _) -> F
           | _ -> T
    then Fail
    else
      match (some res. ?k t r outcome.
               pan_evaluate (prog,pan_state_clock_fupd (K k) s) = (r,t) /\
               (match r with
                  SOME (pan_FinalFFI e) -> outcome = FFI_outcome e
                | SOME (pan_Return _) -> outcome = Success
                | _ -> F) /\
               res = Terminate outcome (ffi_state_io_events (pan_state_ffi t))) with
        SOME res -> res
      | NONE ->
          Diverge (build_lprefix_lub
            (IMAGE (\k. llist_fromList (ffi_state_io_events (pan_state_ffi
                          (SND (pan_evaluate (prog,pan_state_clock_fupd (K k) s))))))
                   (:num)))`;;

let itree_behaviour_def = cake_def
 `itree_behaviour pre (fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B)
                  ((prog:(A)panLang_prog),(s:(A)bstate)) =
    let trace = trace_prefix0 fs (itree_evaluate (prog,s)) in
    match (some r. ?n s'. ltree fs (mrec h_prog (h_prog (prog,s))) =
                          ITER n Tau (itree_Ret (INR (r,s')))) with
      SOME r ->
        (match r with
           SOME (pan_FinalFFI e) ->
             (match llist_toList trace with
                NONE -> Fail
              | SOME io -> Terminate (FFI_outcome e) (APPEND pre io))
         | SOME (pan_Return _) ->
             (match llist_toList trace with
                NONE -> Fail
              | SOME io -> Terminate Success (APPEND pre io))
         | _ -> Fail)
    | NONE -> Diverge (LAPPEND (llist_fromList pre) trace)`;;

(* helpers for evaluate_to_itree *)

let PITRAUX_some_none = prove
 (`!P:A->bool. (!x. ~P x) ==> (some) P = NONE`,
  REWRITE_TAC[some_DEF] THEN MESON_TAC[]);;

(* the forward simulation for a run with any clock *)

let PITRAUX_fwd_clock = prove
 (`!prog (s:(A,B)pan_state) k r t.
     pan_evaluate (prog,pan_state_clock_fupd (K k) s) = (r,t) /\ ~(r = SOME pan_TimeOut)
     ==> (?n. ltree (ffi_state_oracle (pan_state_ffi s),ffi_state_ffi_state (pan_state_ffi s))
                    (mrec h_prog (h_prog (prog,pan_itreeSem_bst s))) =
              ITER n Tau (itree_Ret (INR (r,pan_itreeSem_bst t)))) /\
         llist_fromList (ffi_state_io_events (pan_state_ffi t)) =
         LAPPEND (llist_fromList (ffi_state_io_events (pan_state_ffi s)))
           (trace_prefix (ffi_state_oracle (pan_state_ffi s),ffi_state_ffi_state (pan_state_ffi s))
              (mrec h_prog (h_prog (prog,pan_itreeSem_bst s))))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP PITRAUX_evaluate_ltree) THEN SIMP[]);;

(* the n-th element of a list prefix of two llists *)

let PITRAUX_LPREFIX_LNTH = prove
 (`!(l:A list) ll ub i v.
     LPREFIX (llist_fromList l) ll /\ LPREFIX (llist_fromList l) ub /\
     LNTH i ll = SOME v /\ i < LENGTH l
     ==> LNTH i ub = SOME v`,
  REWRITE_TAC[LPREFIX_NTH] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `LNTH i (llist_fromList (l:A list)) = SOME (EL i l)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[LNTH_fromList]; ALL_TAC] THEN
  ASM_MESON_TAC[option_INJ]);;

(* a run that always times out: the least upper bound of its I/O is the  *)
(* I/O before followed by the trace (the last part of HOL4's proof of    *)
(* evaluate_to_itree, with not_less_opt_lemma and bounded_trace_eq)       *)

let PITRAUX_lub_trace = prove
 (`!prog (s:(A,B)pan_state).
     (!k. FST (pan_evaluate (prog,pan_state_clock_fupd (K k) s)) = SOME pan_TimeOut)
     ==> build_lprefix_lub
           (IMAGE (\k. llist_fromList (ffi_state_io_events (pan_state_ffi
                         (SND (pan_evaluate (prog,pan_state_clock_fupd (K k) s)))))) (:num)) =
         LAPPEND (llist_fromList (ffi_state_io_events (pan_state_ffi s)))
           (trace_prefix (ffi_state_oracle (pan_state_ffi s),ffi_state_ffi_state (pan_state_ffi s))
              (mrec h_prog (h_prog (prog,pan_itreeSem_bst s))))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_SYM THEN
  MP_TAC(ISPECL [`prog:(A)panLang_prog`; `s:(A,B)pan_state`]
                evaluate_io_events_lprefix_chain) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM(MATCH_MP build_prefix_lub_intro th)]) THEN
  REWRITE_TAC[lprefix_lub_def; FORALL_IN_IMAGE; IN_UNIV] THEN
  SUBGOAL_THEN
   `!k. LPREFIX (llist_fromList (ffi_state_io_events (pan_state_ffi
                  (SND (pan_evaluate (prog,pan_state_clock_fupd (K k) (s:(A,B)pan_state)))))))
          (LAPPEND (llist_fromList (ffi_state_io_events (pan_state_ffi s)))
             (trace_prefix (ffi_state_oracle (pan_state_ffi s),ffi_state_ffi_state (pan_state_ffi s))
                (mrec h_prog (h_prog (prog,pan_itreeSem_bst s)))))`
   ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN
    MP_TAC(ISPECL [`prog:(A)panLang_prog`; `pan_state_clock_fupd (K k) (s:(A,B)pan_state)`;
                   `FST (pan_evaluate (prog,pan_state_clock_fupd (K k) (s:(A,B)pan_state)))`;
                   `SND (pan_evaluate (prog,pan_state_clock_fupd (K k) (s:(A,B)pan_state)))`]
                  PITRAUX_evaluate_LPREFIX) THEN
    SIMP[PAIR];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `ub:io_event llist` THEN DISCH_TAC THEN
  ASM_CASES_TAC
   `!n. ?k. n < LENGTH (ffi_state_io_events (pan_state_ffi
                (SND (pan_evaluate (prog,pan_state_clock_fupd (K k) (s:(A,B)pan_state))))))` THENL
   [REWRITE_TAC[LPREFIX_NTH] THEN MAP_EVERY X_GEN_TAC [`i:num`; `v:io_event`] THEN
    DISCH_TAC THEN FIRST_X_ASSUM(X_CHOOSE_TAC `k:num` o SPEC `i:num`) THEN
    MATCH_MP_TAC PITRAUX_LPREFIX_LNTH THEN
    EXISTS_TAC `ffi_state_io_events (pan_state_ffi
                  (SND (pan_evaluate (prog,pan_state_clock_fupd (K k) (s:(A,B)pan_state)))))` THEN
    EXISTS_TAC `LAPPEND (llist_fromList (ffi_state_io_events (pan_state_ffi (s:(A,B)pan_state))))
           (trace_prefix (ffi_state_oracle (pan_state_ffi s),ffi_state_ffi_state (pan_state_ffi s))
              (mrec h_prog (h_prog (prog,pan_itreeSem_bst s))))` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `n:num` o REWRITE_RULE[NOT_FORALL_THM; NOT_EXISTS_THM]) THEN
  MP_TAC(ISPECL [`n:num`; `prog:(A)panLang_prog`; `s:(A,B)pan_state`] not_less_opt_lemma) THEN
  ASM_REWRITE_TAC[less_opt_def] THEN
  DISCH_THEN(X_CHOOSE_TAC `k0:num`) THEN
  MP_TAC(ISPECL [`prog:(A)panLang_prog`; `pan_state_clock_fupd (K k0) (s:(A,B)pan_state)`]
                bounded_trace_eq) THEN
  ANTS_TAC THENL
   [SIMP[] THEN CONJ_TAC THENL
     [X_GEN_TAC `d:num` THEN
      REWRITE_TAC[GSYM IS_PREFIX_LENGTH_ANTI] THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`prog:(A)panLang_prog`; `pan_state_clock_fupd (K k0) (s:(A,B)pan_state)`;
                       `d:num`] pan_evaluate_add_clock_io_events_mono) THEN
        SIMP[ADD_SYM];
        FIRST_X_ASSUM(MP_TAC o SPEC `d + k0:num`) THEN REWRITE_TAC[LE_ADD] THEN
        SIMP[]];
      REWRITE_TAC[pan_itreeSem_div_def] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP nondiv_INR) THEN
      DISCH_THEN(X_CHOOSE_THEN `x:((A)pan_result)option#(A)bstate` SUBST_ALL_TAC) THEN
      PAIR_CASES_ON `x:((A)pan_result)option#(A)bstate` THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP nondiv_imp_evaluate) THEN
      DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `t:(A,B)pan_state` STRIP_ASSUME_TAC)) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th -> is_forall (concl th) &&
        can (find_term (fun t -> t = `pan_TimeOut:(A)pan_result`)) (concl th))) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[CAKE_SIMP_RULE [] th]) THEN ASM_REWRITE_TAC[]);;

(* a finite trace after a finite I/O *)

let PITRAUX_toList_LAPPEND = prove
 (`!(l1:A list) l2 (tr:A llist).
     llist_fromList l2 = LAPPEND (llist_fromList l1) tr
     ==> ?l. llist_toList tr = SOME l /\ l2 = APPEND l1 l`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `LFINITE (tr:A llist)` ASSUME_TAC THENL
   [MP_TAC(ISPEC `l2:A list` LFINITE_fromList) THEN ASM_REWRITE_TAC[LFINITE_APPEND] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `l:A list` SUBST_ALL_TAC o MATCH_MP LFINITE_IMP_fromList) THEN
  EXISTS_TAC `l:A list` THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[LAPPEND_fromList; fromList_11]) THEN
  SIMP[from_toList]);;

(* the some term of the goal (chosen by pick) equals v: a subgoal *)

let PITRAUX_SOME_SUBGOAL_TAC (v:term) (pick:term->bool) : tactic = fun (asl,w as g) ->
  let t = find_term (fun t -> try fst(dest_const(rator t)) = "some" && pick t
                              with Failure _ -> false) w in
  SUBGOAL_THEN (mk_eq(t, v)) SUBST1_TAC g;;

(* the cases of a result *)

let PITRAUX_result_cases = prove
 (`!r:((A)pan_result)option.
     r = NONE \/ r = SOME pan_Error \/ r = SOME pan_TimeOut \/ r = SOME pan_Break \/
     r = SOME pan_Continue \/ (?v. r = SOME (pan_Return v)) \/
     (?e v. r = SOME (pan_Exception e v)) \/ (?f. r = SOME (pan_FinalFFI f))`,
  GEN_TAC THEN QCASES_ON "r" THEN TRY(RENAME1 "SOME x0" THEN QCASES_ON "x0") THEN
  SIMP[]);;

(* HOL4's proof splits on the results of the runs with the some intro    *)
(* rule; here: either some run does not time out (then every such run    *)
(* agrees with the itree's result, PITRAUX_fwd_clock), or all time out    *)
(* (then the itree diverges and PITRAUX_lub_trace gives the trace)        *)

let evaluate_to_itree = prove
 (`!prog (s:(A,B)pan_state).
     evaluate_behaviour (prog,s) =
     itree_behaviour (ffi_state_io_events (pan_state_ffi s))
       (ffi_state_oracle (pan_state_ffi s),ffi_state_ffi_state (pan_state_ffi s)) (prog,pan_itreeSem_bst s)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[evaluate_behaviour_def; itree_behaviour_def; trace_prefix0_eq_trace_prefix;
              LET_DEF; LET_END_DEF] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  ASM_CASES_TAC `?k. ~(FST (pan_evaluate (prog,pan_state_clock_fupd (K k) (s:(A,B)pan_state))) =
                       SOME pan_TimeOut)` THENL
   [ALL_TAC;
    FIRST_X_ASSUM(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM]) THEN
    ASM_REWRITE_TAC[] THEN SIMP[] THEN
    PITRAUX_SOME_SUBGOAL_TAC `NONE:behaviour option` (fun t -> type_of t = `:behaviour option`) THENL
     [MATCH_MP_TAC PITRAUX_some_none THEN BETA_TAC THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th -> is_forall (concl th))) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> not (is_eq (concl th)))) THEN SIMP[];
      ALL_TAC] THEN
    PITRAUX_SOME_SUBGOAL_TAC `NONE:(((A)pan_result)option)option` (fun t -> true) THENL
     [MATCH_MP_TAC PITRAUX_some_none THEN BETA_TAC THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP nondiv_imp_evaluate) THEN
      DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `t:(A,B)pan_state` STRIP_ASSUME_TAC)) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SIMP[] THEN MATCH_MP_TAC PITRAUX_lub_trace THEN ASM_REWRITE_TAC[]] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `k:num`) THEN
  MP_TAC(ISPEC `pan_evaluate (prog,pan_state_clock_fupd (K k) (s:(A,B)pan_state))` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:((A)pan_result)option` (X_CHOOSE_THEN `t:(A,B)pan_state` ASSUME_TAC)) THEN
  SUBGOAL_THEN `~(r = SOME (pan_TimeOut:(A)pan_result))` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg (concl th))) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`prog:(A)panLang_prog`; `s:(A,B)pan_state`; `k:num`; `r:((A)pan_result)option`;
                `t:(A,B)pan_state`] PITRAUX_fwd_clock) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `n:num`) ASSUME_TAC) THEN
  SUBGOAL_THEN `!k' r' t'. pan_evaluate (prog,pan_state_clock_fupd (K k') (s:(A,B)pan_state)) = (r',t') /\
                           ~(r' = SOME pan_TimeOut)
                           ==> r' = r /\
                               ffi_state_io_events (pan_state_ffi t') =
                               ffi_state_io_events (pan_state_ffi (t:(A,B)pan_state))`
    ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(SPECL [`prog:(A)panLang_prog`; `s:(A,B)pan_state`; `k':num`; `r':((A)pan_result)option`;
                  `t':(A,B)pan_state`] PITRAUX_fwd_clock) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `n':num`) ASSUME_TAC) THEN CONJ_TAC THENL
     [REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
        (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "ltree" with Failure _ -> false)))) THEN
      DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[FUNPOW_Tau_Ret_eq_simp; injectivity "sum"; PAIR_EQ] THEN MESON_TAC[];
      ONCE_REWRITE_TAC[GSYM fromList_11] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  PITRAUX_SOME_SUBGOAL_TAC `SOME (r:((A)pan_result)option)`
    (fun t -> type_of t = `:(((A)pan_result)option)option`) THENL
   [MATCH_MP_TAC BASICAUX_some_unique THEN BETA_TAC THEN CONJ_TAC THENL
     [ASM_MESON_TAC[];
      REPEAT STRIP_TAC THEN
      UNDISCH_TAC `ltree (ffi_state_oracle (pan_state_ffi (s:(A,B)pan_state)),ffi_state_ffi_state (pan_state_ffi s))
                    (mrec h_prog (h_prog (prog,pan_itreeSem_bst s))) =
                  ITER n Tau (itree_Ret (INR (r,pan_itreeSem_bst (t:(A,B)pan_state))))` THEN
      ASM_REWRITE_TAC[FUNPOW_Tau_Ret_eq_simp; injectivity "sum"; PAIR_EQ] THEN MESON_TAC[]];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP PITRAUX_toList_LAPPEND o check (fun th ->
    try fst(dest_const(fst(strip_comb(rhs(concl th))))) = "LAPPEND" with Failure _ -> false)) THEN
  DISCH_THEN(X_CHOOSE_THEN `l:io_event list` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `r:((A)pan_result)option` PITRAUX_result_cases) THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
  TRY(FIRST_ASSUM(CONTR_TAC o check (fun th -> concl th = `F`)) THEN NO_TAC) THEN
  ASM_REWRITE_TAC[] THEN SIMP[] THEN
  FIRST
   [COND_CASES_TAC THENL
     [REWRITE_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o REWRITE_RULE[NOT_EXISTS_THM] o
        check (fun th -> is_neg (concl th) &&
                         is_exists (dest_neg (concl th)))) THEN SIMP[]] THEN NO_TAC;
    COND_CASES_TAC THENL
     [FIRST_X_ASSUM(X_CHOOSE_TAC `k2:num` o check (fun th -> is_exists (concl th))) THEN
      MP_TAC(ISPEC `pan_evaluate (prog,pan_state_clock_fupd (K k2) (s:(A,B)pan_state))`
                   PAIR_SURJECTIVE) THEN
      DISCH_THEN(X_CHOOSE_THEN `r2:((A)pan_result)option` (X_CHOOSE_THEN `t2:(A,B)pan_state`
        ASSUME_TAC)) THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`k2:num`; `r2:((A)pan_result)option`; `t2:(A,B)pan_state`] o
        check (fun th -> is_forall (concl th) &&
          can (find_term (fun t -> t = `pan_TimeOut:(A)pan_result`)) (concl th))) THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t -> t = `k2:num`)) (concl th) &&
                                              not (is_eq (concl th)))) THEN
      ASM_REWRITE_TAC[] THEN QCASES_ON "r2" THEN TRY(RENAME1 "SOME r3" THEN QCASES_ON "r3") THEN
      SIMP[];
      W(fun (_,w) -> let out = rand(rator(rhs w)) in
        PITRAUX_SOME_SUBGOAL_TAC (mk_comb(`SOME:behaviour->behaviour option`,
          mk_comb(mk_comb(`Terminate`,out),
                  `ffi_state_io_events (pan_state_ffi (t:(A,B)pan_state))`)))
          (fun t -> type_of t = `:behaviour option`)) THENL
       [MATCH_MP_TAC BASICAUX_some_unique THEN BETA_TAC THEN CONJ_TAC THENL
         [MAP_EVERY EXISTS_TAC [`k:num`; `t:(A,B)pan_state`] THEN ASM_REWRITE_TAC[] THEN SIMP[];
          REPEAT STRIP_TAC THEN
          FIRST_X_ASSUM(MP_TAC o SPECL [`k':num`; `r':((A)pan_result)option`; `t':(A,B)pan_state`] o
            check (fun th -> is_forall (concl th) &&
              can (find_term (fun t -> t = `pan_TimeOut:(A)pan_result`)) (concl th))) THEN
          ASM_REWRITE_TAC[] THEN
          FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t -> t = `outcome:outcome`))
                                                    (concl th) && not (is_eq (concl th)))) THEN
          QCASES_ON "r'" THEN TRY(RENAME1 "SOME r4" THEN QCASES_ON "r4") THEN SIMP[]];
        SIMP[]]]]);;
