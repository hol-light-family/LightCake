(* ========================================================================= *)
(* clos_known: port of HOL4 compiler/backend/clos_knownScript.sml (CakeML    *)
(* v3479).                                                                   *)
(* This complicated compiler phase tracks where closure values flow in a    *)
(* program.  It attempts to annotate function applications with the         *)
(* (numeric) names of the called closures (annotations lead to better code  *)
(* in clos_to_bvl).  If the code for the applied closure is statically      *)
(* known and small enough, then this compiler phase can inline the body of  *)
(* the called closure.  The function inlining is recursive and controlled   *)
(* using configurable parameters.                                           *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - HOL4 ++ is APPEND, HOL4's paired lambdas are pair cases                 *)
(*   (\p. match p with ..), HOL4 isEmpty t is t = LN, t ss k (the trace    *)
(*   overload of backend_common) is mk_cons t k.                             *)
(* - The names of Fn and clos_Letrec (HOL4 t) are nm and nms.                *)
(* - The many-clause definitions are made with sem1aux_def(_wf)              *)
(*   (semantics/sem1aux_tfl.ml); HOL4 exp3_size is list_size clos_exp_size. *)
(* - CLOS2AUX_ names are local proof helpers.                                *)
(* - HOL4 known is clos_known_known (a short or common word), with the       *)
(*   theorems renamed alike (known_def is clos_known_known_def, ...).        *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/db_vars.ml";;
needs "compiler/backend/clos_ticks.ml";;
needs "compiler/backend/clos_letop.ml";;
needs "compiler/backend/clos_fvs.ml";;
needs "compiler/backend/clos_op.ml";;
needs "semantics/sem1aux_tfl.ml";;

type_invention_error := true;;


(* proof helpers of this file *)

(* does the constant named s occur in tm *)

let CLOS2AUX_CONST_IN s tm =
  can (find_term (fun t -> is_const t && fst(dest_const t) = s)) tm;;

(* termination of the compile functions: HOL4's exp3_size is              *)
(* list_size clos_exp_size, its exp1_size (on (num # exp) list) is        *)
(* list_size (pair_size (\x. x) clos_exp_size)                             *)

let CLOS2AUX_MAP_SND_LE = prove
 (`!fns:(num#clos_exp) list.
     list_size clos_exp_size (MAP SND fns) <=
     list_size (pair_size (\x. x) clos_exp_size) fns`,
  REWRITE_TAC[list_size_pair_size_MAP_FST_SND] THEN ARITH_TAC);;

(* for every MAP SND fns of the goal, the fact CLOS2AUX_MAP_SND_LE fns   *)

let CLOS2AUX_ADD_MAP_SND_TAC : tactic = fun (asl,w as g) ->
  let ty = `:(num#clos_exp)list` in
  let ts = find_terms (fun t ->
      try let f,args = strip_comb t in
          fst(dest_const f) = "MAP" && length args = 2 &&
          is_const (hd args) && fst(dest_const (hd args)) = "SND" &&
          type_of (el 1 args) = ty
      with Failure _ -> false) w in
  MAP_EVERY (fun t -> ASSUME_TAC (SPEC (rand t) CLOS2AUX_MAP_SND_LE))
            (setify ts) g;;

let CLOS2AUX_SIZE_TC_TAC : tactic =
  REWRITE_TAC[IMP_CONJ] THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  CLOS2AUX_ADD_MAP_SND_TAC THEN RVEQ_TAC THEN TERM_TAC;;

(* the kit's PAIRARG_TAC, innermost first: split a pair_CASE e f whose      *)
(* scrutinee e has no pair_CASE in it (a call), looked for in the goal      *)
(* first, then in the assumptions                                          *)

let CLOS2AUX_SPLIT_PAIR_TAC : tactic =
  fun (asl,w as gl) ->
    let whole = list_mk_conj(w :: map (concl o snd) asl) in
    let is_cand t =
      is_case_app t &&
      (let c,x,fs = dest_case_app t in
       fst(dest_const c) = "pair_CASE" && not (is_pair x) &&
       not (CLOS2AUX_CONST_IN "pair_CASE" x) && free_in x whole) in
    let t = try find_term is_cand w with Failure _ -> find_term is_cand whole in
    let _,x,fs = dest_case_app t in
    let f = hd fs in
    let tya,tyb = match dest_type(type_of x) with
        "prod",[a;b] -> a,b | _ -> failwith "CLOS2AUX_SPLIT_PAIR_TAC" in
    let n1,n2 =
      try let a,b = dest_abs f in let b1,_ = dest_abs b in
          fst(dest_var a),fst(dest_var b1)
      with Failure _ -> "p1","p2" in
    let avoid = frees whole in
    let v1 = variant avoid (mk_var(n1,tya)) in
    let v2 = variant (v1::avoid) (mk_var(n2,tyb)) in
    let nch = ISPEC x (nchotomy_of_type (type_of x)) in
    (MP_TAC nch THEN
     DISCH_THEN(X_CHOOSE_THEN v1 (X_CHOOSE_THEN v2
       (fun th -> if is_var x then SUBST_ALL_TAC th
                  else SUBST_ALL_TAC th THEN ASSUME_TAC th))) THEN
     CASE_ASM_TIDY_TAC THEN CASE_REWRITE_TAC[]) gl;;

(* This definition is written to short-circuit, i.e. exit as soon as       *)
(* possible.  The names of Fn and clos_Letrec (HOL4 t) are nm and nms.      *)

let get_size_sc_aux_def = sem1aux_def_wf
  `MEASURE (\p:num#clos_exp list. list_size clos_exp_size (SND p))`
  CLOS2AUX_SIZE_TC_TAC
  `(get_size_sc_aux n [] = n) /\
   (get_size_sc_aux n (CONS (x:clos_exp) (CONS y xs)) =
      if n = 0 then n else
        let n = get_size_sc_aux n [x] in if n = 0 then n else
          get_size_sc_aux n (CONS y xs)) /\
   (get_size_sc_aux n [clos_Var t v] = n - 1) /\
   (get_size_sc_aux n [clos_If t x1 x2 x3] =
      let n = n - 1 in if n = 0 then 0 else
      let n = get_size_sc_aux n [x1] in if n = 0 then 0 else
      let n = get_size_sc_aux n [x2] in if n = 0 then 0 else
        get_size_sc_aux n [x3]) /\
   (get_size_sc_aux n [clos_Let t xs x2] =
      let n = n - 1 in if n = 0 then 0 else
      let n = get_size_sc_aux n xs in if n = 0 then 0 else
        get_size_sc_aux n [x2]) /\
   (get_size_sc_aux n [clos_Raise t x1] =
      let n = n - 1 in if n = 0 then 0 else
        get_size_sc_aux n [x1]) /\
   (get_size_sc_aux n [clos_Handle t x1 x2] =
      let n = n - 1 in if n = 0 then 0 else
      let n = get_size_sc_aux n [x1] in if n = 0 then 0 else
        get_size_sc_aux n [x2]) /\
   (get_size_sc_aux n [clos_Op t op xs] =
      let n = n - 1 in if n = 0 then 0 else
        get_size_sc_aux n xs) /\
   (get_size_sc_aux n [clos_Tick t x] = get_size_sc_aux n [x]) /\
   (get_size_sc_aux n [clos_Call t ticks dest xs] =
      let n = n - 1 in if n = 0 then 0 else
        get_size_sc_aux n xs) /\
   (get_size_sc_aux n [Fn nm loc_opt ws_opt num_args x1] =
      let n = n - 1 in if n = 0 then 0 else
        get_size_sc_aux n [x1]) /\
   (get_size_sc_aux n [clos_Letrec nms loc_opt ws_opt fns x1] =
      let n = n - 1 in if n = 0 then 0 else
      let n = get_size_sc_aux n (MAP SND fns) in if n = 0 then 0 else
        get_size_sc_aux n [x1]) /\
   (get_size_sc_aux n [clos_App t loc_opt x1 xs] =
      let n = n - 1 in if n = 0 then 0 else
      let n = get_size_sc_aux n [x1] in if n = 0 then 0 else
        get_size_sc_aux n xs)`;;

let get_size_sc_aux_ind = cake_ind "get_size_sc_aux";;

let get_size_sc_def = cake_def
  `get_size_sc limit e =
     let n = get_size_sc_aux (limit + 1) [e] in
       if n = 0 then NONE else SOME ((limit + 1) - n)`;;

let get_size_aux_def = sem1aux_def_wf
  `MEASURE (\xs:clos_exp list. list_size clos_exp_size xs)`
  CLOS2AUX_SIZE_TC_TAC
  `(get_size_aux [] = 0) /\
   (get_size_aux (CONS (x:clos_exp) (CONS y xs)) =
      get_size_aux [x] + get_size_aux (CONS y xs)) /\
   (get_size_aux [clos_Var t v] = 1) /\
   (get_size_aux [clos_If t x1 x2 x3] =
      1 + get_size_aux [x1] + get_size_aux [x2] + get_size_aux [x3]) /\
   (get_size_aux [clos_Let t xs x2] =
      1 + get_size_aux xs + get_size_aux [x2]) /\
   (get_size_aux [clos_Raise t x1] = 1 + get_size_aux [x1]) /\
   (get_size_aux [clos_Handle t x1 x2] =
      1 + get_size_aux [x1] + get_size_aux [x2]) /\
   (get_size_aux [clos_Op t op xs] = 1 + get_size_aux xs) /\
   (get_size_aux [clos_Tick t x] = get_size_aux [x]) /\
   (get_size_aux [clos_Call t ticks dest xs] = 1 + get_size_aux xs) /\
   (get_size_aux [Fn nm loc_opt ws_opt num_args x1] = 1 + get_size_aux [x1]) /\
   (get_size_aux [clos_Letrec nms loc_opt ws_opt fns x1] =
      1 + get_size_aux (MAP SND fns) + get_size_aux [x1]) /\
   (get_size_aux [clos_App t loc_opt x1 xs] =
      1 + get_size_aux [x1] + get_size_aux xs)`;;

let get_size_aux_ind = cake_ind "get_size_aux";;

(* HOL4: get_size *)

let clos_known_get_size_def = cake_def
  `clos_known_get_size e = get_size_aux [e]`;;

let get_size_sc_aux_correct = prove
 (`!xs limit (n:num). get_size_sc_aux limit xs = limit - get_size_aux xs`,
  SUBGOAL_THEN `!xs limit. get_size_sc_aux limit xs = limit - get_size_aux xs`
    (fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC get_size_aux_ind THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[get_size_sc_aux_def; get_size_aux_def] THEN
  ASM_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REPEAT COND_CASES_TAC THEN ASM_ARITH_TAC);;

let get_size_sc_SOME = prove
 (`!exp limit n. get_size_sc limit exp = SOME n ==> clos_known_get_size exp = n`,
  REWRITE_TAC[get_size_sc_def; clos_known_get_size_def; get_size_sc_aux_correct;
              LET_DEF; LET_END_DEF] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[option_DISTINCT; option_INJ] THEN ASM_ARITH_TAC);;

(* HOL4: free; the names of Fn and clos_Letrec (HOL4 t) are nm and nms,    *)
(* HOL4's paired lambda \(n,x). .. is a pair case                           *)

let clos_known_free_def = sem1aux_def_wf
  `MEASURE (\xs:clos_exp list. list_size clos_exp_size xs)`
  CLOS2AUX_SIZE_TC_TAC
  `(clos_known_free [] = ([],db_vars_Empty)) /\
   (clos_known_free (CONS (x:clos_exp) (CONS y xs)) =
      let (c1,l1) = clos_known_free [x] in
      let (c2,l2) = clos_known_free (CONS y xs) in
        (APPEND c1 c2,mk_Union l1 l2)) /\
   (clos_known_free [clos_Var t v] = ([clos_Var t v],db_vars_Var v)) /\
   (clos_known_free [clos_If t x1 x2 x3] =
      let (c1,l1) = clos_known_free [x1] in
      let (c2,l2) = clos_known_free [x2] in
      let (c3,l3) = clos_known_free [x3] in
        ([clos_If t (HD c1) (HD c2) (HD c3)],mk_Union l1 (mk_Union l2 l3))) /\
   (clos_known_free [clos_Let t xs x2] =
      let (c1,l1) = clos_known_free xs in
      let (c2,l2) = clos_known_free [x2] in
        ([clos_Let t c1 (HD c2)],mk_Union l1 (db_vars_Shift (LENGTH xs) l2))) /\
   (clos_known_free [clos_Raise t x1] =
      let (c1,l1) = clos_known_free [x1] in
        ([clos_Raise t (HD c1)],l1)) /\
   (clos_known_free [clos_Tick t x1] =
      let (c1,l1) = clos_known_free [x1] in
        ([clos_Tick t (HD c1)],l1)) /\
   (clos_known_free [clos_Op t op xs] =
      let (c1,l1) = clos_known_free xs in
        ([clos_Op t op c1],l1)) /\
   (clos_known_free [clos_App t loc_opt x1 xs2] =
      let (c1,l1) = clos_known_free [x1] in
      let (c2,l2) = clos_known_free xs2 in
        ([clos_App t loc_opt (HD c1) c2],mk_Union l1 l2)) /\
   (clos_known_free [Fn nm loc _ num_args x1] =
      let (c1,l1) = clos_known_free [x1] in
      let l2 = db_vars_Shift num_args l1 in
        ([Fn nm loc (SOME (vars_to_list l2)) num_args (HD c1)],l2)) /\
   (clos_known_free [clos_Letrec nms loc _ fns x1] =
      let m = LENGTH fns in
      let res = MAP (\p. match p with
                         (n,x) -> let (c,l) = clos_known_free [x] in
                                    ((n,HD c),db_vars_Shift (n + m) l)) fns in
      let c1 = MAP FST res in
      let l1 = list_mk_Union (MAP SND res) in
      let (c2,l2) = clos_known_free [x1] in
        ([clos_Letrec nms loc (SOME (vars_to_list l1)) c1 (HD c2)],
         mk_Union l1 (db_vars_Shift (LENGTH fns) l2))) /\
   (clos_known_free [clos_Handle t x1 x2] =
      let (c1,l1) = clos_known_free [x1] in
      let (c2,l2) = clos_known_free [x2] in
        ([clos_Handle t (HD c1) (HD c2)],mk_Union l1 (db_vars_Shift 1 l2))) /\
   (clos_known_free [clos_Call t ticks dest xs] =
      let (c1,l1) = clos_known_free xs in
        ([clos_Call t ticks dest c1],l1))`;;

(* HOL4 leaves free_LENGTH, free_SING, LENGTH_FST_free, HD_FST_free and   *)
(* free_CONS in a comment                                                   *)

(* HOL4: closed; HOL4 isEmpty t is t = LN *)

let clos_known_closed_def = cake_def
  `clos_known_closed x <=> db_to_set (SND (clos_known_free [x])) = LN`;;

let contains_closures_def = sem1aux_def_wf
  `MEASURE (\xs:clos_exp list. list_size clos_exp_size xs)`
  CLOS2AUX_SIZE_TC_TAC
  `(contains_closures [] <=> F) /\
   (contains_closures (CONS (x:clos_exp) (CONS y xs)) <=>
      if contains_closures [x] then T else contains_closures (CONS y xs)) /\
   (contains_closures [clos_Var t v] <=> F) /\
   (contains_closures [clos_If t x1 x2 x3] <=>
      if contains_closures [x1] then T else
      if contains_closures [x2] then T else
        contains_closures [x3]) /\
   (contains_closures [clos_Let t xs x2] <=>
      if contains_closures xs then T else contains_closures [x2]) /\
   (contains_closures [clos_Raise t x1] <=> contains_closures [x1]) /\
   (contains_closures [clos_Handle t x1 x2] <=>
      if contains_closures [x1] then T else contains_closures [x2]) /\
   (contains_closures [clos_Op t op xs] <=> contains_closures xs) /\
   (contains_closures [clos_Tick t x] <=> contains_closures [x]) /\
   (contains_closures [clos_Call t ticks dest xs] <=> contains_closures xs) /\
   (contains_closures [Fn nm loc_opt ws_opt num_args x1] <=> T) /\
   (contains_closures [clos_Letrec nms loc_opt ws_opt fns x1] <=> T) /\
   (contains_closures [clos_App t loc_opt x1 xs] <=>
      if contains_closures [x1] then T else contains_closures xs)`;;

let contains_closures_ind = cake_ind "contains_closures";;

(* -----------------------------------------------------------------        *)
(* This compiler transformation turns App NONEs into App SOMEs.  An App    *)
(* can carry a SOME loc if: 1) the closure value that is used there was     *)
(* created with location loc; 2) the closure value expects the number of    *)
(* arguments it gets here.  This part of the compiler makes two passes.     *)
(* The first pass tracks which closure values flow into which globals.      *)
(* The second pass tracks closure values (with help of the result of the    *)
(* first pass) and switches App NONEs into App SOMEs wherever possible.     *)
(* -----------------------------------------------------------------        *)

(* ClosNoInline: location in code table, arity; Clos: loc, arity, body,     *)
(* body size; Tuple: conses or tuples; Int: used to index tuples; Other:    *)
(* unknown; Impossible: value returned by Raise                             *)

let val_approx_INDUCT,val_approx_RECURSION = cake_type
  "val_approx = ClosNoInline num num
              | clos_known_Clos num num clos_exp num
              | clos_known_Tuple num (val_approx list)
              | clos_known_Int int
              | clos_known_Other
              | Impossible";;

(* HOL4: val val_approx_size_def = definition ..: type_size_def            *)
(* "val_approx" (and size_aux_eqs "val_approx")                             *)

(* merge recurses through MAP2.  The definition (sem1aux_def_wf) uses the   *)
(* admissibility rule CLOS2AUX_ADMISSIBLE_MAP2 for MAP2 (a recursive call   *)
(* under MAP2 f l1 l2 gets the context MEM y l1, as with HOL4's MAP2_CONG;  *)
(* HOL Light's MAP2 takes HD and TL of the second list, so its element is   *)
(* not constrained), registered for this definition only.  sem1aux_def_wf   *)
(* finds no context for MAP2 when it derives the induction theorem, so      *)
(* merge_ind is derived below with the kit's derive_induction from the one  *)
(* termination condition of the clauses (HOL4's merge_ind).                 *)

let CLOS2AUX_MAP2_CONG = prove
 (`!(f:C->D->E) g l1 l2.
     (!y z. MEM y l1 ==> f y z = g y z) ==> MAP2 f l1 l2 = MAP2 g l1 l2`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP2_DEF; MEM; CONS_11] THEN REPEAT STRIP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]]);;

let CLOS2AUX_ADMISSIBLE_MAP2 = prove
 (`!(<<) (p:(A->B)->P->bool) (s:P->A) (h:(A->B)->P->C->D->E) l1 l2.
        admissible(<<) p s l1 /\ admissible(<<) p s l2 /\
        admissible (<<) (\f (y,z,x). p f x /\ MEM y (l1 f x))
                        (\(y,z,x). s x) (\f (y,z,x). h f x y z)
        ==> admissible (<<) p s (\f x. MAP2 (h f x) (l1 f x) (l2 f x))`,
  REWRITE_TAC[admissible; FORALL_PAIR_THM] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(l1:(A->B)->P->C list) g a = l1 f a /\
                (l2:(A->B)->P->D list) g a = l2 f a`
    (fun th -> REWRITE_TAC[th]) THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC CLOS2AUX_MAP2_CONG THEN ASM_MESON_TAC[]);;

let merge_def =
  let saved = !cake_admissible_rules in
  cake_register_admissible "MAP2" CLOS2AUX_ADMISSIBLE_MAP2;
  let th = try sem1aux_def_wf
    `MEASURE (\p:val_approx#val_approx. val_approx_size (FST p))`
    SEM1AUX_TC_TAC
    `(merge Impossible y = y) /\
     (merge x Impossible = x) /\
     (merge (clos_known_Tuple tg1 xs) (clos_known_Tuple tg2 ys) =
        if LENGTH xs = LENGTH ys /\ tg1 = tg2
        then clos_known_Tuple tg1 (MAP2 merge xs ys)
        else clos_known_Other) /\
     (merge (ClosNoInline m1 n1) (ClosNoInline m2 n2) =
        if m1 = m2 /\ n1 = n2 then ClosNoInline m1 n1 else clos_known_Other) /\
     (merge (clos_known_Clos m1 n1 e1 s1) (clos_known_Clos m2 n2 e2 s2) =
        if m1 = m2 /\ n1 = n2 /\ e1 = e2 /\ s1 = s2
        then clos_known_Clos m1 n1 e1 s1 else clos_known_Other) /\
     (merge (clos_known_Int i) (clos_known_Int j) =
        if i = j then clos_known_Int i else clos_known_Other) /\
     (merge _ _ = clos_known_Other)`
    with e -> (cake_admissible_rules := saved; raise e) in
  cake_admissible_rules := saved; th;;

let merge_ind =
  let r = `MEASURE (\p:val_approx#val_approx. val_approx_size (FST p))` in
  let tc = prove
   (`!tg1 xs tg2 ys x (y:val_approx).
       (LENGTH xs = LENGTH ys /\ tg1 = tg2) /\ MEM x xs
       ==> MEASURE (\p:val_approx#val_approx. val_approx_size (FST p))
             (x,y) (clos_known_Tuple tg1 xs,clos_known_Tuple tg2 ys)`,
    SEM1AUX_TC_TAC) in
  let wfth = prove(mk_comb(`WF:(val_approx#val_approx->val_approx#val_approx->bool)->bool`,r),
                   WF_TAC) in
  let cls = map (fun c -> let vs,eq = strip_forall c in
                          vs,snd(strip_comb(lhs eq)))
                (conjuncts (concl merge_def)) in
  derive_induction `merge` cls [tc] wfth;;

let _ = cake_add_simps [merge_def];;

(* Avoid MAP2 *)

let CLOS2AUX_MEM_ZIP_FST = prove
 (`!(xs:A list) (ys:B list) p.
     LENGTH xs = LENGTH ys /\ MEM p (ZIP xs ys) ==> MEM (FST p) xs`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`xs:A list`; `ys:B list`; `p:A#B`] MEM_ZIP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[FST] THEN
  ASM_MESON_TAC[MEM_EL]);;

let CLOS2AUX_MERGE_TUP_TC_TAC : tactic =
  REWRITE_TAC[IMP_CONJ] THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  RVEQ_TAC THEN
  REPEAT (FIRST_X_ASSUM (fun th -> if is_conj (concl th)
                                   then STRIP_ASSUME_TAC th else NO_TAC)) THEN
  IMP_RES_TAC CLOS2AUX_MEM_ZIP_FST THEN TERM_TAC;;

let merge_tup_def = sem1aux_def_wf
  `MEASURE (\p:val_approx#val_approx. val_approx_size (FST p))`
  CLOS2AUX_MERGE_TUP_TC_TAC
  `(merge_tup (Impossible,y) = y) /\
   (merge_tup (x,Impossible) = x) /\
   (merge_tup (clos_known_Tuple tg1 xs,clos_known_Tuple tg2 ys) =
      if LENGTH xs = LENGTH ys /\ tg1 = tg2
      then clos_known_Tuple tg1 (MAP merge_tup (ZIP xs ys))
      else clos_known_Other) /\
   (merge_tup (ClosNoInline m1 n1,ClosNoInline m2 n2) =
      if m1 = m2 /\ n1 = n2 then ClosNoInline m1 n1 else clos_known_Other) /\
   (merge_tup (clos_known_Clos m1 n1 e1 s1,clos_known_Clos m2 n2 e2 s2) =
      if m1 = m2 /\ n1 = n2 /\ e1 = e2 /\ s1 = s2
      then clos_known_Clos m1 n1 e1 s1 else clos_known_Other) /\
   (merge_tup (clos_known_Int i,clos_known_Int j) =
      if i = j then clos_known_Int i else clos_known_Other) /\
   (merge_tup (_,_) = clos_known_Other)`;;

let merge_tup_ind = cake_ind "merge_tup";;

(* HOL4 leaves merge_tup_pmatch in a comment *)

let merge_alt = prove
 (`!x y. merge x y = merge_tup (x,y)`,
  MATCH_MP_TAC merge_ind THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[merge_def; merge_tup_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
  ASM_SIMP_TAC[MAP2_MAP; injectivity "val_approx"] THEN
  MATCH_MP_TAC MAP_EQ THEN REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[UNCURRY_DEF] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`xs:val_approx list`; `ys:val_approx list`;
                 `(p1:val_approx,p2:val_approx)`] CLOS2AUX_MEM_ZIP_FST) THEN
  ASM_REWRITE_TAC[FST]);;

(* the NAME_pmatch theorems: the definition by cases (the match form is     *)
(* compiled into case constants, a case split proves it)                    *)

let known_op_def = sem1aux_def
  `(known_op (GlobOp (clos_Global n)) as g =
      if NULL as then
        match lookup n g with
          NONE -> (clos_known_Other,g)
        | SOME x -> (x,g)
      else (clos_known_Other,g)) /\
   (known_op (GlobOp (SetGlobal n)) as g =
      match as with
        [] -> (clos_known_Other,g)
      | CONS a xs ->
          match lookup n g with
            NONE -> (clos_known_Other,insert n a g)
          | SOME other -> (clos_known_Other,insert n (merge other a) g)) /\
   (known_op (BlockOp (clos_Cons tg)) as g = (clos_known_Tuple tg as,g)) /\
   (known_op (IntOp (clos_Const i)) as g = (clos_known_Int i,g)) /\
   (known_op (MemOp clos_El) as g =
      match as with
        [clos_known_Tuple _ xs; clos_known_Int i] ->
          if &0 <= i /\ i < &(LENGTH xs)
          then (EL (num_of_int i) xs,g)
          else (clos_known_Other,g)
      | CONS Impossible xs -> (Impossible,g)
      | CONS _ (CONS Impossible xs) -> (Impossible,g)
      | _ -> (clos_known_Other,g)) /\
   (known_op op (as:val_approx list) (g:val_approx spt) = (clos_known_Other,g))`;;

let known_op_pmatch = prove
 (CASE_TERM
  `!op (as:val_approx list) (g:val_approx spt).
     known_op op as g =
     match op with
       GlobOp (clos_Global n) ->
         if NULL as then
           match lookup n g with
             NONE -> (clos_known_Other,g)
           | SOME x -> (x,g)
         else (clos_known_Other,g)
     | GlobOp (SetGlobal n) ->
         (match as with
            [] -> (clos_known_Other,g)
          | CONS a xs ->
              match lookup n g with
                NONE -> (clos_known_Other,insert n a g)
              | SOME other -> (clos_known_Other,insert n (merge other a) g))
     | BlockOp (clos_Cons tg) -> (clos_known_Tuple tg as,g)
     | IntOp (clos_Const i) -> (clos_known_Int i,g)
     | MemOp clos_El ->
         (match as with
            [clos_known_Tuple _ xs; clos_known_Int i] ->
              if &0 <= i /\ i < &(LENGTH xs)
              then (EL (num_of_int i) xs,g)
              else (clos_known_Other,g)
          | CONS Impossible xs -> (Impossible,g)
          | CONS _ (CONS Impossible xs) -> (Impossible,g)
          | _ -> (clos_known_Other,g))
     | _ -> (clos_known_Other,g)`,
  IL1AUX_PMATCH_TAC[known_op_def]);;

(* HOL4: EL_MEM_LEMMA [local] *)

let clos_known_EL_MEM_LEMMA = prove
 (`!xs i (x:A). i < LENGTH xs /\ x = EL i xs ==> MEM x xs`,
  MESON_TAC[MEM_EL]);;

let clos_approx_def = cake_def
  `clos_approx max_size loc num_args body =
     match get_size_sc max_size body with
       NONE -> ClosNoInline loc num_args
     | SOME body_size -> clos_known_Clos loc num_args body body_size`;;

let clos_gen_noinline_def = cake_def
  `(clos_gen_noinline n i [] = []) /\
   (clos_gen_noinline n i (CONS (a,e:clos_exp) xs) =
      CONS (ClosNoInline (n + 2 * i) a) (clos_gen_noinline n (i + 1) xs))`;;

let clos_gen_noinline_ind = cake_ind "clos_gen_noinline";;

let globalOpt_INDUCT,globalOpt_RECURSION = cake_type
  "globalOpt = gO_Int int | gO_NullTuple num | gO_None";;

let isGlobal_def = sem1aux_def
  `(isGlobal (GlobOp (clos_Global _)) <=> T) /\
   (isGlobal _ <=> F)`;;

let isGlobal_pmatch = prove
 (CASE_TERM
  `!op. isGlobal op <=> match op with GlobOp (clos_Global _) -> T | _ -> F`,
  IL1AUX_PMATCH_TAC[isGlobal_def]);;

let gO_destApx_def = sem1aux_def
  `(gO_destApx (clos_known_Int i) = gO_Int i) /\
   (gO_destApx (clos_known_Tuple tag args) =
      if NULL args then gO_NullTuple tag else gO_None) /\
   (gO_destApx _ = gO_None)`;;

(* HOL4: mk_Ticks; t ss tc is mk_cons t tc *)

let clos_known_mk_Ticks_def = cake_def_wf
  `MEASURE (\p:tra#num#num#clos_exp. FST (SND (SND p)))`
  TERM_TAC
  `clos_known_mk_Ticks t tc n e =
     if n = 0 then e
     else clos_known_mk_Ticks t (tc + 1) (n - 1) (clos_Tick (mk_cons t tc) e)`;;

let clos_known_mk_Ticks_ind = cake_ind "clos_known_mk_Ticks";;

let inliningDecision_INDUCT,inliningDecision_RECURSION = cake_type
  "inliningDecision = inlD_Nothing
                    | inlD_Annotate num
                    | inlD_LetInline clos_exp";;

(* inline_factor: as in Inline expansion: when and how? by Manuel Serrano;  *)
(* val_approx_spt could replace the explicit g argument of known            *)

let clos_known_config_INFO = cake_record "clos_known_config"
  ["inline_max_body_size","num";
   "inline_factor","num";
   "initial_inline_factor","num";
   "val_approx_spt","val_approx spt"];;

let default_inline_factor_def = cake_def
  `default_inline_factor = 8`;;

let default_max_body_size_def = cake_def
  `default_max_body_size max_app inline_factor = (max_app + 1) * inline_factor`;;

let mk_config_def = cake_def
  `mk_config max_body_size inline_factor =
     clos_known_config_REC max_body_size inline_factor inline_factor LN`;;

let clos_known_default_config_def = cake_def
  `clos_known_default_config max_app =
     mk_config (default_max_body_size max_app default_inline_factor)
               default_inline_factor`;;

let dec_inline_factor_def = cake_def
  `dec_inline_factor c =
     clos_known_config_inline_factor_fupd
       (K (clos_known_config_inline_factor c DIV 2)) c`;;

let reset_inline_factor_def = cake_def
  `reset_inline_factor c =
     clos_known_config_inline_factor_fupd
       (K (clos_known_config_initial_inline_factor c)) c`;;

let decide_inline_def = cake_def
  `decide_inline c fapx (app_lopt:num option) app_arity =
     match fapx with
       ClosNoInline loc arity ->
         if app_lopt = NONE /\ app_arity = arity
         then inlD_Annotate loc else inlD_Nothing
     | clos_known_Clos loc arity body body_size ->
         if app_lopt = NONE /\ app_arity = arity then
           (if body_size < clos_known_config_inline_factor c * (1 + app_arity) /\
               ~contains_closures [body] /\
               clos_known_closed (Fn (implode "") NONE NONE app_arity body)
            then inlD_LetInline body
            else inlD_Annotate loc)
         else inlD_Nothing
     | _ -> inlD_Nothing`;;

let CLOS2AUX_LT_MULT_POS = prove
 (`!a b c. a < b * c ==> 0 < b`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `b = 0` THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT] THEN ASM_ARITH_TAC);;

let decide_inline_LetInline = prove
 (`!c fapx lopt arity body.
     decide_inline c fapx lopt arity = inlD_LetInline body
     ==> 0 < clos_known_config_inline_factor c`,
  REPEAT GEN_TAC THEN CASES_ON `fapx:val_approx` THEN
  REWRITE_TAC[decide_inline_def] THEN CASE_REWRITE_TAC[] THEN
  REPEAT COND_CASES_TAC THEN CASE_REWRITE_TAC[] THEN
  ASM_MESON_TAC[CLOS2AUX_LT_MULT_POS]);;

(* HOL4: known; t ss k is mk_cons t k; the names of Fn and clos_Letrec    *)
(* (HOL4 t) are nm and nms; HOL4's paired lambda \(num_args,x). .. is a    *)
(* pair case.  Termination: the inline factor decreases at an inlined call *)
(* (decide_inline_LetInline), the size of the expressions elsewhere.        *)

let CLOS2AUX_DIV2_LT = prove
 (`!x. 0 < x ==> x DIV 2 < x`,
  GEN_TAC THEN DISCH_TAC THEN MP_TAC(SPECL [`x:num`; `2`] DIVISION) THEN
  ASM_ARITH_TAC);;

let CLOS2AUX_KNOWN_TC_TAC : tactic =
  REWRITE_TAC[IMP_CONJ] THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  TRY (FIRST_ASSUM (fun th ->
         ASSUME_TAC (MATCH_MP CLOS2AUX_DIV2_LT
                       (MATCH_MP decide_inline_LetInline th)))) THEN
  CLOS2AUX_ADD_MAP_SND_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC(WF_REL_THMS @ [FST; SND; I_THM; dec_inline_factor_def; K_THM;
                             clos_known_config_INFO.ri_accfupds]) THEN
  TERM_TAC;;

let clos_known_known_def = sem1aux_def_wf
  `inv_image ((MEASURE (I:num->num)) LEX (MEASURE (I:num->num)))
     (\p:clos_known_config # clos_exp list # val_approx list # val_approx spt.
        (clos_known_config_inline_factor (FST p),
         list_size clos_exp_size (FST (SND p))))`
  CLOS2AUX_KNOWN_TC_TAC
  `(clos_known_known c [] vs (g:val_approx spt) = ([],g)) /\
   (clos_known_known c (CONS (x:clos_exp) (CONS y xs)) vs g =
      let (eas1,g) = clos_known_known c [x] vs g in
      let (eas2,g) = clos_known_known c (CONS y xs) vs g in
        (APPEND eas1 eas2,g)) /\
   (clos_known_known c [clos_Var t v] vs g =
      ([(clos_Var t v,any_el v vs clos_known_Other)],g)) /\
   (clos_known_known c [clos_If t x1 x2 x3] vs g =
      let (ea1,g) = clos_known_known c [x1] vs g in
      let (ea2,g) = clos_known_known c [x2] vs g in
      let (ea3,g) = clos_known_known c [x3] vs g in
      let (e1,a1) = HD ea1 in
      let (e2,a2) = HD ea2 in
      let (e3,a3) = HD ea3 in
        ([(clos_If t e1 e2 e3,merge a2 a3)],g)) /\
   (clos_known_known c [clos_Let t xs x2] vs g =
      let (ea1,g) = clos_known_known c xs vs g in
      let (ea2,g) = clos_known_known c [x2] (APPEND (MAP SND ea1) vs) g in
      let (e2,a2) = HD ea2 in
        ([(clos_Let t (MAP FST ea1) e2,a2)],g)) /\
   (clos_known_known c [clos_Raise t x1] vs g =
      let (ea1,g) = clos_known_known c [x1] vs g in
      let (e1,a1) = HD ea1 in
        ([(clos_Raise t e1,Impossible)],g)) /\
   (clos_known_known c [clos_Tick t x1] vs g =
      let (ea1,g) = clos_known_known c [x1] vs g in
      let (e1,a1) = HD ea1 in
        ([(clos_Tick t e1,a1)],g)) /\
   (clos_known_known c [clos_Handle t x1 x2] vs g =
      let (ea1,g) = clos_known_known c [x1] vs g in
      let (ea2,g) = clos_known_known c [x2] (CONS clos_known_Other vs) g in
      let (e1,a1) = HD ea1 in
      let (e2,a2) = HD ea2 in
        ([(clos_Handle t e1 e2,merge a1 a2)],g)) /\
   (clos_known_known c [clos_Call t ticks dest xs] vs g =
      let (ea1,g) = clos_known_known c xs vs g in
        ([(clos_Call t ticks dest (MAP FST ea1),clos_known_Other)],g)) /\
   (clos_known_known c [clos_Op t op xs] vs g =
      let (ea1,g) = clos_known_known c xs vs g in
      let (a,g) = known_op op (REVERSE (MAP SND ea1)) g in
      let e =
        (if isGlobal op then
           match gO_destApx a with
             gO_None -> clos_op_SmartOp t op
           | gO_Int i -> clos_Op t (IntOp (clos_Const i))
           | gO_NullTuple tag -> clos_Op t (BlockOp (clos_Cons tag))
         else clos_op_SmartOp t op) (MAP FST ea1) in
        ([(e,a)],g)) /\
   (clos_known_known c [clos_App t loc_opt x xs] vs g =
      let (ea2,g) = clos_known_known c xs vs g in
      let (ea1,g) = clos_known_known c [x] vs g in
      let (e1,a1) = HD ea1 in
        match decide_inline c a1 loc_opt (LENGTH xs) with
          inlD_Nothing ->
            ([(clos_App t loc_opt e1 (MAP FST ea2),clos_known_Other)],g)
        | inlD_Annotate new_loc ->
            ([(clos_App t (SOME new_loc) e1 (MAP FST ea2),clos_known_Other)],g)
        | inlD_LetInline body ->
            let (eabody,_) =
              clos_known_known (dec_inline_factor c) [body] (MAP SND ea2) g in
            let (ebody,abody) = HD eabody in
              if pure x then
                ([(clos_Let (mk_cons t 0) (MAP FST ea2)
                     (clos_known_mk_Ticks t 1 (LENGTH xs) ebody),abody)],g)
              else
                ([(clos_Let (mk_cons t 0) (SNOC e1 (MAP FST ea2))
                     (clos_known_mk_Ticks t 1 (LENGTH xs) ebody),abody)],g)) /\
   (clos_known_known c [Fn nm loc_opt ws_opt num_args x1] vs g =
      let (ea1,g) =
        clos_known_known c [x1] (APPEND (REPLICATE num_args clos_known_Other) vs) g in
      let (body,a1) = HD ea1 in
        ([(Fn nm loc_opt NONE num_args body,
           match loc_opt with
             SOME loc ->
               clos_approx (clos_known_config_inline_max_body_size c)
                 loc num_args x1
           | NONE -> clos_known_Other)],g)) /\
   (clos_known_known c [clos_Letrec nms loc_opt _ fns x1] vs g =
      let clos = (match loc_opt with
                    NONE -> REPLICATE (LENGTH fns) clos_known_Other
                  | SOME loc -> clos_gen_noinline loc 0 fns) in
      let new_fns =
        MAP (\p. match p with
                   (num_args,x) ->
                     let new_vs =
                       APPEND (APPEND (REPLICATE num_args clos_known_Other) clos)
                              vs in
                     let res = clos_known_known c [x] new_vs g in
                       (num_args,FST (HD (FST res)))) fns in
      let (ea1,g) = clos_known_known c [x1] (APPEND clos vs) g in
      let (e1,a1) = HD ea1 in
        ([(clos_Letrec nms loc_opt NONE new_fns e1,a1)],g))`;;

let clos_known_known_ind = cake_ind "clos_known_known";;

let known_LENGTH = prove
 (`!limit es vs (g:val_approx spt).
     LENGTH (FST (clos_known_known limit es vs g)) = LENGTH es`,
  MATCH_MP_TAC clos_known_known_ind THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[clos_known_known_def; LET_DEF; LET_END_DEF] THEN
  REPEAT (CLOS2AUX_SPLIT_PAIR_TAC THEN FS[]) THEN FS[LENGTH] THEN
  REPEAT (TOP_CASE_TAC THEN FS[LENGTH]) THEN
  REPEAT (CLOS2AUX_SPLIT_PAIR_TAC THEN FS[]) THEN FS[LENGTH] THEN
  ARITH_TAC);;

let known_LENGTH_EQ_E = prove
 (`!limit es vs (g0:val_approx spt) alist g.
     clos_known_known limit es vs g0 = (alist,g) ==> LENGTH alist = LENGTH es`,
  MESON_TAC[FST; known_LENGTH]);;

let known_sing = prove
 (`!limit e vs (g:val_approx spt).
     ?e' a g'. clos_known_known limit [e] vs g = ([(e',a)],g')`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`limit:clos_known_config`; `[e:clos_exp]`;
                `vs:val_approx list`; `g:val_approx spt`] known_LENGTH) THEN
  SPEC_TAC(`clos_known_known limit [e] vs (g:val_approx spt)`,
           `r:(clos_exp#val_approx) list # val_approx spt`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST; PAIR_EQ; LENGTH] THEN
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `p1:(clos_exp#val_approx) list` list_CASES) THEN
  REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ; LENGTH_EQ_NIL; CONS_11] THEN
  MESON_TAC[PAIR]);;

let known_sing_EQ_E = prove
 (`!limit e vs (g0:val_approx spt) all g.
     clos_known_known limit [e] vs g0 = (all,g) ==> ?e' apx. all = [(e',apx)]`,
  MESON_TAC[PAIR_EQ; known_sing]);;

(* HOL4: compile *)

let clos_known_compile_def = cake_def
  `(clos_known_compile NONE exps = (NONE,exps)) /\
   (clos_known_compile (SOME c) exps =
      let exps = clos_fvs_compile exps in
      let (es,g) = clos_known_known c exps [] LN in
      let es1 = clos_ticks_remove_ticks (MAP FST es) in
      let es2 = clos_letop_let_op es1 in
        (SOME (clos_known_config_val_approx_spt_fupd (K g) c),es2))`;;

(* HOL4: compile_inc *)

let clos_known_compile_inc_def = cake_def
  `clos_known_compile_inc c g (es,xs:A) =
     let (eas,g') = clos_known_known (reset_inline_factor c) es [] g in
       (g',MAP FST eas,xs)`;;

let known_static_conf_def = cake_def
  `known_static_conf kc =
     match kc with
       NONE -> NONE
     | SOME kc ->
         SOME (clos_known_config_val_approx_spt_fupd (K LN)
                 (reset_inline_factor kc))`;;

let known_compile_inc_def = cake_def
  `(known_compile_inc NONE (spt:val_approx spt) (p:clos_prog) = (spt,p)) /\
   (known_compile_inc (SOME c) spt p =
      let p = (clos_fvs_compile_inc p:clos_prog) in
      let (spt,p) = clos_known_compile_inc c spt p in
      let p = (clos_ticks_compile_inc p:clos_prog) in
      let p = (clos_letop_compile_inc p:clos_prog) in
        (spt,p))`;;

let option_val_approx_spt_def = cake_def
  `option_val_approx_spt kc =
     match kc with
       NONE -> LN
     | SOME kcfg -> clos_known_config_val_approx_spt kcfg`;;

let option_upd_val_spt_def = cake_def
  `(option_upd_val_spt (spt:val_approx spt) NONE = NONE) /\
   (option_upd_val_spt spt (SOME kc) =
      SOME (clos_known_config_val_approx_spt_fupd (K spt) kc))`;;
