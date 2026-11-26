(* ========================================================================= *)
(* bvi_inline: port of HOL4 compiler/backend/bvi_inlineScript.sml (CakeML    *)
(* v3479).                                                                   *)
(* A deliberately small BVI inliner for CPR worker-wrapper functions.        *)
(* This pass is name preserving.  It only substitutes wrappers satisfying    *)
(* wrapper_ok; extending that predicate is the intended way to support a     *)
(* new worker-wrapper protocol.                                              *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - HOL4 FUNPOW f n x is ITER n f x, GENLIST f n is list_of_seq f n.        *)
(* - The clauses of a HOL Light definition share their variables, so the     *)
(*   target of LetCall (HOL4 dest, also the name of the num option of        *)
(*   bvi_Call) is dest'.                                                     *)
(* - HOL4's paired lambdas are written (\p. match p with (a,b,c) -> t).      *)
(* - canonical_wrapper (a catch-all clause) is made with sem1aux_def; its    *)
(*   HOL4 induction theorem (a case analysis) by BVIPAUX_INL_case_ind.       *)
(* - The four example theorems (EVAL_TAC in HOL4) are proved by rewriting.   *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/bvi.ml";;
needs "compiler/backend/backend_common.ml";;
needs "semantics/sem1aux_tfl.ml";;

type_invention_error := true;;

let bvi_mk_tick_def = cake_def
  `bvi_mk_tick n (e:bvi_exp) = ITER n bvi_Tick e`;;

(* First-order form for cv_compute, which has no FUNPOW. *)

let bvi_mk_tick_eq = prove
 (`!n e. bvi_mk_tick n e =
         if n = 0 then e else bvi_Tick (bvi_mk_tick (n - 1) e)`,
  INDUCT_TAC THEN SIMP[bvi_mk_tick_def; ITER; NOT_SUC; SUC_SUB1]);;

(* Op reverses its argument list, so a wrapper that boxes the worker's rets *)
(* results in order lists them reversed under the Cons.                      *)

let canonical_wrapper_def = sem1aux_def
  `(canonical_wrapper name arity
      (LetCall rets ticks worker args (bvi_Op (BlockOp (clos_Cons tag)) rvs)) <=>
      ~(worker = name) /\
      args = list_of_seq bvi_Var arity /\
      rvs = REVERSE (list_of_seq bvi_Var rets)) /\
   (canonical_wrapper name arity _ <=> F)`;;

(* the induction theorem (a case analysis) that HOL4 makes for a            *)
(* non-recursive definition by patterns: one case per clause of the         *)
(* definition theorem def (the completed clauses)                          *)

let BVIPAUX_INL_case_ind (def:thm) : thm =
  let cls = map (fun cl -> let vs,eq = strip_forall cl in
                           let c,args = strip_comb(lhs eq) in vs,c,args)
                (conjuncts(concl def)) in
  let _,c,args0 = hd cls in
  let tty = mk_tuple_ty (map type_of args0) in
  let wfth = ISPEC (mk_abs(mk_var("x",tty),`0`)) WF_MEASURE in
  derive_induction c (map (fun (vs,_,args) -> vs,args) cls) [] wfth;;

let canonical_wrapper_ind = BVIPAUX_INL_case_ind canonical_wrapper_def;;

let wrapper_ok_def = cake_def
  `wrapper_ok name arity body <=> canonical_wrapper name arity body`;;

(* cs is a cache of code-table entries.  The correctness invariant needed  *)
(* for a hit is that the cached label, arity, and body correspond to the    *)
(* code table (up to the expression relation used by the pass).             *)

let inline_exp_def = sem1aux_def_wf
  `MEASURE (\x:((num # bvi_exp) spt # bvi_exp) + ((num # bvi_exp) spt # bvi_exp list).
              sum_CASE x (\p. bvi_exp_size (SND p))
                         (\p. list_size bvi_exp_size (SND p)))`
  SEM1AUX_TC_TAC
  `(inline_exp cs (bvi_Var n) = bvi_Var n) /\
   (inline_exp cs (bvi_If x y z) =
      bvi_If (inline_exp cs x) (inline_exp cs y) (inline_exp cs z)) /\
   (inline_exp cs (bvi_Let xs y) =
      bvi_Let (inline_exps cs xs) (inline_exp cs y)) /\
   (inline_exp cs (bvi_Raise x) = bvi_Raise (inline_exp cs x)) /\
   (inline_exp cs (bvi_Tick x) = bvi_Tick (inline_exp cs x)) /\
   (inline_exp cs (bvi_Call ticks dest xs handler) =
      let xs = inline_exps cs xs in
        match handler with
          SOME h -> bvi_Call ticks dest xs (SOME (inline_exp cs h))
        | NONE ->
            match dest with
              NONE -> bvi_Call ticks NONE xs NONE
            | SOME name ->
                match lookup name cs with
                  NONE -> bvi_Call ticks (SOME name) xs NONE
                | SOME (arity,body) ->
                    if LENGTH xs = arity then
                      bvi_Let xs (bvi_mk_tick (SUC ticks) body)
                    else bvi_Call ticks (SOME name) xs NONE) /\
   (inline_exp cs (bvi_Force loc n) = bvi_Force loc n) /\
   (inline_exp cs (bvi_Op op xs) = bvi_Op op (inline_exps cs xs)) /\
   (inline_exp cs (LetCall rets ticks dest' xs y) =
      LetCall rets ticks dest' (inline_exps cs xs) (inline_exp cs y)) /\
   (inline_exp cs (bvi_Return xs) = bvi_Return (inline_exps cs xs)) /\
   (inline_exps cs [] = []) /\
   (inline_exps cs (CONS x xs) = CONS (inline_exp cs x) (inline_exps cs xs))`;;

let inline_exp_ind = cake_ind "inline_exp";;

let inline_all_def = cake_def
  `(inline_all cs [] = (cs,[])) /\
   (inline_all cs (CONS (name,arity,body) prog) =
      let body = inline_exp cs body in
      let cs1 = if wrapper_ok name arity body then
                  insert name (arity,body) cs
                else cs in
      let (cs2,prog2) = inline_all cs1 prog in
        (cs2,CONS (name,arity,body) prog2))`;;

(* sem1aux_def_wf finds no context for the call under OPTION_MAP and warns  *)
(* that it makes no induction theorem: it is proved below                  *)

let remove_ticks_exp_def = sem1aux_def_wf
  `MEASURE (\x:bvi_exp + bvi_exp list.
              sum_CASE x (\e. bvi_exp_size e) (\es. list_size bvi_exp_size es))`
  SEM1AUX_TC_TAC
  `(remove_ticks_exp (bvi_Var n) = bvi_Var n) /\
   (remove_ticks_exp (bvi_If x y z) =
      bvi_If (remove_ticks_exp x) (remove_ticks_exp y) (remove_ticks_exp z)) /\
   (remove_ticks_exp (bvi_Let xs y) =
      bvi_Let (remove_ticks_exps xs) (remove_ticks_exp y)) /\
   (remove_ticks_exp (bvi_Raise x) = bvi_Raise (remove_ticks_exp x)) /\
   (remove_ticks_exp (bvi_Tick x) = remove_ticks_exp x) /\
   (remove_ticks_exp (bvi_Call ticks dest xs handler) =
      bvi_Call 0 dest (remove_ticks_exps xs)
        (OPTION_MAP remove_ticks_exp handler)) /\
   (remove_ticks_exp (bvi_Force loc n) = bvi_Force loc n) /\
   (remove_ticks_exp (bvi_Op op xs) = bvi_Op op (remove_ticks_exps xs)) /\
   (remove_ticks_exp (LetCall rets ticks dest' xs y) =
      LetCall rets 0 dest' (remove_ticks_exps xs) (remove_ticks_exp y)) /\
   (remove_ticks_exp (bvi_Return xs) = bvi_Return (remove_ticks_exps xs)) /\
   (remove_ticks_exps [] = []) /\
   (remove_ticks_exps (CONS x xs) =
      CONS (remove_ticks_exp x) (remove_ticks_exps xs))`;;

(* the recursive call under OPTION_MAP gets the context handler = SOME h     *)
(* (HOL4's OPTION_MAP_CONG); the induction theorem is proved from the       *)
(* structural induction of bvi_exp                                           *)

let remove_ticks_exp_ind = prove
 (`!P0 P1.
     (!n. P0 (bvi_Var n)) /\
     (!x y z. P0 x /\ P0 y /\ P0 z ==> P0 (bvi_If x y z)) /\
     (!xs y. P0 y /\ P1 xs ==> P0 (bvi_Let xs y)) /\
     (!x. P0 x ==> P0 (bvi_Raise x)) /\
     (!x. P0 x ==> P0 (bvi_Tick x)) /\
     (!ticks dest xs handler.
        (!h. handler = SOME h ==> P0 h) /\ P1 xs
        ==> P0 (bvi_Call ticks dest xs handler)) /\
     (!loc n. P0 (bvi_Force loc n)) /\
     (!op xs. P1 xs ==> P0 (bvi_Op op xs)) /\
     (!rets ticks dest' xs y.
        P0 y /\ P1 xs ==> P0 (LetCall rets ticks dest' xs y)) /\
     (!xs. P1 xs ==> P0 (bvi_Return xs)) /\
     P1 [] /\
     (!x xs. P0 x /\ P1 xs ==> P1 (CONS x xs))
     ==> (!x. P0 x) /\ (!xs. P1 xs)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`P0:bvi_exp->bool`; `P1:bvi_exp list->bool`;
                 `\opt:bvi_exp option. !h. opt = SOME h ==> P0 h`]
                bvi_exp_INDUCT) THEN
  REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
    TRY(ASM_SIMP_TAC[] THEN NO_TAC) THEN ASM_MESON_TAC[];
    SIMP_TAC[]]);;

let bvi_inline_compile_inc_def = cake_def
  `bvi_inline_compile_inc cs prog =
     let (cs1,prog1) = inline_all cs prog in
       (cs1,MAP (\p. match p with
                       (name,arity,body) -> (name,arity,remove_ticks_exp body))
                prog1)`;;

let bvi_inline_compile_prog_def = cake_def
  `bvi_inline_compile_prog prog = bvi_inline_compile_inc LN prog`;;

let canonical_four_result_wrapper = prove
 (`wrapper_ok 10 3
     (LetCall 4 0 11 (list_of_seq bvi_Var 3)
       (bvi_Op (BlockOp (clos_Cons 7)) (REVERSE (list_of_seq bvi_Var 4))))`,
  REWRITE_TAC[wrapper_ok_def; canonical_wrapper_def] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let malformed_wrappers_rejected = prove
 (`~wrapper_ok 10 3
      (LetCall 4 0 10 (list_of_seq bvi_Var 3)
        (bvi_Op (BlockOp (clos_Cons 7)) (list_of_seq bvi_Var 4))) /\
   ~wrapper_ok 10 3
      (LetCall 4 0 11 [bvi_Var 0; bvi_Var 2; bvi_Var 1]
        (bvi_Op (BlockOp (clos_Cons 7)) (list_of_seq bvi_Var 4))) /\
   ~wrapper_ok 10 3
      (LetCall 4 0 11 (list_of_seq bvi_Var 3)
        (bvi_Op (BlockOp (clos_Cons 7)) [bvi_Var 0; bvi_Var 1; bvi_Var 2])) /\
   ~wrapper_ok 10 3 (bvi_Return (list_of_seq bvi_Var 3))`,
  REWRITE_TAC[wrapper_ok_def; canonical_wrapper_def] THEN
  CONV_TAC(TOP_DEPTH_CONV LIST_OF_SEQ_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV REVERSE_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[CONS_11; NOT_CONS_NIL; injectivity "bvi_exp"] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let inline_boundary_examples = prove
 (`inline_exp (insert 10 (3,
      LetCall 4 0 11 (list_of_seq bvi_Var 3)
        (bvi_Op (BlockOp (clos_Cons 7)) (list_of_seq bvi_Var 4))) LN)
    (bvi_Call 2 (SOME 10) [bvi_Var 4; bvi_Var 5; bvi_Var 6] NONE) =
      bvi_Let [bvi_Var 4; bvi_Var 5; bvi_Var 6]
        (bvi_mk_tick 3
          (LetCall 4 0 11 (list_of_seq bvi_Var 3)
            (bvi_Op (BlockOp (clos_Cons 7)) (list_of_seq bvi_Var 4)))) /\
   inline_exp (insert 10 (3,
      LetCall 4 0 11 (list_of_seq bvi_Var 3)
        (bvi_Op (BlockOp (clos_Cons 7)) (list_of_seq bvi_Var 4))) LN)
    (bvi_Call 2 (SOME 10) [bvi_Var 4; bvi_Var 5; bvi_Var 6] (SOME (bvi_Var 0))) =
      bvi_Call 2 (SOME 10) [bvi_Var 4; bvi_Var 5; bvi_Var 6] (SOME (bvi_Var 0)) /\
   inline_exp (insert 10 (3,
      LetCall 4 0 11 (list_of_seq bvi_Var 3)
        (bvi_Op (BlockOp (clos_Cons 7)) (list_of_seq bvi_Var 4))) LN)
    (LetCall 1 2 10 [bvi_Var 4; bvi_Var 5; bvi_Var 6] (bvi_Return [bvi_Var 0])) =
      LetCall 1 2 10 [bvi_Var 4; bvi_Var 5; bvi_Var 6] (bvi_Return [bvi_Var 0])`,
  CAKE_REWRITE_TAC[inline_exp_def; LET_DEF; LET_END_DEF; lookup_insert1;
                   LENGTH] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CAKE_REWRITE_TAC[]);;

let final_tick_cleanup_example = prove
 (`remove_ticks_exp
     (bvi_Tick (bvi_Call 2 (SOME 10) [bvi_Tick (bvi_Var 0)]
       (SOME (LetCall 1 3 11 [bvi_Tick (bvi_Var 1)] (bvi_Return [bvi_Var 0]))))) =
   bvi_Call 0 (SOME 10) [bvi_Var 0]
     (SOME (LetCall 1 0 11 [bvi_Var 1] (bvi_Return [bvi_Var 0])))`,
  REWRITE_TAC[remove_ticks_exp_def; OPTION_MAP_DEF]);;
