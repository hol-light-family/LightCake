(* ========================================================================= *)
(* bvl_handle: port of HOL4 compiler/backend/bvl_handleScript.sml (CakeML    *)
(* v3479).  A BVL transformation that introduces a Let into each Handle      *)
(* body.  This is preparation for BVL --> BVI compilation.  This phase also  *)
(* removes Handles in case the body cannot raise an exception.               *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/bvl.ml";;
needs "compiler/backend/db_vars.ml";;
needs "compiler/backend/bvl_const.ml";;
needs "semantics/sem1aux_tfl.ml";;

type_invention_error := true;;

let can_raise_def = sem1aux_def_wf
  `MEASURE (\x:bvl_exp + bvl_exp list.
              sum_CASE x (\e. bvl_exp_size e) (\es. list_size bvl_exp_size es))`
  SEM1AUX_TC_TAC
  `(can_raise (bvl_Var v) <=> F) /\
   (can_raise (bvl_If x1 x2 x3) <=> can_raise x1 \/ can_raise x2 \/ can_raise x3) /\
   (can_raise (bvl_Let xs x2) <=> can_raise x2 \/ can_raise1 xs) /\
   (can_raise (bvl_Handle x1 x2) <=> can_raise x2) /\
   (can_raise (bvl_Raise x1) <=> T) /\
   (can_raise (bvl_Op op xs) <=> op = clos_ThunkOp ForceThunk \/ can_raise1 xs) /\
   (can_raise (bvl_Tick x) <=> can_raise x) /\
   (can_raise (bvl_Force m n) <=> T) /\
   (can_raise (bvl_Call t dest xs) <=> T) /\
   (can_raise1 [] <=> F) /\
   (can_raise1 (CONS x xs) <=> can_raise x \/ can_raise1 xs)`;;

let dest_handle_Raise_def = sem1aux_def
  `(dest_handle_Raise (bvl_Raise x) = if can_raise x then NONE else SOME x) /\
   (dest_handle_Raise _ = NONE)`;;

let dest_handle_Raise_ind = BVLPAUX_case_ind dest_handle_Raise_def;;

let dest_handle_Let_def = sem1aux_def
  `(dest_handle_Let (bvl_Let xs x) =
      if can_raise1 xs then NONE else SOME (xs,x)) /\
   (dest_handle_Let _ = NONE)`;;

let dest_handle_If_def = sem1aux_def
  `(dest_handle_If (bvl_If x1 x2 x3) =
      if can_raise x1 then NONE else
      if can_raise x2 then
        (if can_raise x3 then NONE else SOME (INL (x1,x2,x3))) else
      if can_raise x3 then
        (if can_raise x2 then NONE else SOME (INR (x1,x2,x3))) else
        NONE) /\
   (dest_handle_If _ = NONE)`;;

let handle_adj_vars_def = sem1aux_def_wf
  `MEASURE (\x:num#num#bvl_exp + num#num#bvl_exp list.
              sum_CASE x (\p. bvl_exp_size (SND (SND p)))
                         (\p. list_size bvl_exp_size (SND (SND p))))`
  SEM1AUX_TC_TAC
  `(handle_adj_vars l d (bvl_Var v) = bvl_Var (if v < l then v else v + d)) /\
   (handle_adj_vars l d (bvl_If x1 x2 x3) =
      bvl_If (handle_adj_vars l d x1) (handle_adj_vars l d x2)
             (handle_adj_vars l d x3)) /\
   (handle_adj_vars l d (bvl_Let xs x2) =
      bvl_Let (handle_adj_vars1 l d xs) (handle_adj_vars (l + LENGTH xs) d x2)) /\
   (handle_adj_vars l d (bvl_Handle x1 x2) =
      bvl_Handle (handle_adj_vars l d x1) (handle_adj_vars (l + 1) d x2)) /\
   (handle_adj_vars l d (bvl_Raise x1) = bvl_Raise (handle_adj_vars l d x1)) /\
   (handle_adj_vars l d (bvl_Op op xs) = bvl_Op op (handle_adj_vars1 l d xs)) /\
   (handle_adj_vars l d (bvl_Tick x) = bvl_Tick (handle_adj_vars l d x)) /\
   (handle_adj_vars l d (bvl_Force m v) =
      bvl_Force m (if v < l then v else v + d)) /\
   (handle_adj_vars l d (bvl_Call t dest xs) =
      bvl_Call t dest (handle_adj_vars1 l d xs)) /\
   (handle_adj_vars1 l d [] = []) /\
   (handle_adj_vars1 l d (CONS x xs) =
      CONS (handle_adj_vars l d x) (handle_adj_vars1 l d xs))`;;

let handle_size_def = sem1aux_def_wf
  `MEASURE (\x:bvl_exp + bvl_exp list.
              sum_CASE x (\e. bvl_exp_size e) (\es. list_size bvl_exp_size es))`
  SEM1AUX_TC_TAC
  `(handle_size (bvl_Var v) = 1) /\
   (handle_size (bvl_If x1 x2 x3) =
      1 + handle_size x1 + handle_size x2 + handle_size x3) /\
   (handle_size (bvl_Let xs x2) = 1 + handle_size x2 + handle_size1 xs) /\
   (handle_size (bvl_Handle x1 x2) = 1 + 5 * (handle_size x1 + handle_size x2)) /\
   (handle_size (bvl_Raise x1) = 1 + handle_size x1) /\
   (handle_size (bvl_Op op xs) = 1 + handle_size1 xs) /\
   (handle_size (bvl_Tick x) = 1 + handle_size x) /\
   (handle_size (bvl_Force m n) = 1) /\
   (handle_size (bvl_Call t dest xs) = 1 + handle_size1 xs) /\
   (handle_size1 [] = 1) /\
   (handle_size1 (CONS x xs) = 1 + handle_size x + handle_size1 xs)`;;

let handle_size_non_zero = prove
 (`!x. 0 < handle_size x`,
  GEN_TAC THEN CASES_ON `x:bvl_exp` THEN FS[handle_size_def] THEN ARITH_TAC);;

(* inversion of the three dest_handle functions, for the termination      *)
(* conditions of handle_simp (HOL4 uses gvs with one_line_ify and          *)
(* AllCaseEqs there); the bound names are unusual on purpose: FS strips the *)
(* existentials under these names                                          *)

let BVLPAUX_dest_handle_Raise_eq = prove
 (`!x r. dest_handle_Raise x = SOME r <=> x = bvl_Raise r /\ ~can_raise r`,
  MATCH_MP_TAC dest_handle_Raise_ind THEN
  REWRITE_TAC[dest_handle_Raise_def] THEN CASE_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN CASE_REWRITE_TAC[] THEN
  ASM_MESON_TAC[]);;

let BVLPAUX_dest_handle_Let_eq = prove
 (`!x p. dest_handle_Let x = SOME p <=>
         ?dhl1 dhl2. x = bvl_Let dhl1 dhl2 /\ p = (dhl1,dhl2) /\ ~can_raise1 dhl1`,
  MATCH_MP_TAC (BVLPAUX_case_ind dest_handle_Let_def) THEN
  REWRITE_TAC[dest_handle_Let_def] THEN CASE_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN CASE_REWRITE_TAC[] THEN
  ASM_MESON_TAC[]);;

let BVLPAUX_dest_handle_If_eq = prove
 (`!x p. dest_handle_If x = SOME p <=>
         ?dhi1 dhi2 dhi3.
           x = bvl_If dhi1 dhi2 dhi3 /\ ~can_raise dhi1 /\
           ((can_raise dhi2 /\ ~can_raise dhi3 /\ p = INL (dhi1,dhi2,dhi3)) \/
            (~can_raise dhi2 /\ can_raise dhi3 /\ p = INR (dhi1,dhi2,dhi3)))`,
  MATCH_MP_TAC (BVLPAUX_case_ind dest_handle_If_def) THEN
  REWRITE_TAC[dest_handle_If_def] THEN CASE_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN REPEAT COND_CASES_TAC THEN CASE_REWRITE_TAC[] THEN
  ASM_MESON_TAC[]);;

(* the termination tactic of handle_simp: invert the contexts, then the     *)
(* sizes (handle_size is positive)                                          *)

let BVLPAUX_HS_POS_TAC : tactic = fun (asl,w as g) ->
  let tms = find_terms (fun t -> is_comb t && rator t = `handle_size`) w in
  MAP_EVERY (fun t -> MP_TAC (SPEC (rand t) handle_size_non_zero)) tms g;;

let BVLPAUX_HANDLE_TC_TAC : tactic =
  REWRITE_TAC[IMP_CONJ] THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  RVEQ_TAC THEN
  FS[BVLPAUX_dest_handle_Raise_eq; BVLPAUX_dest_handle_Let_eq;
     BVLPAUX_dest_handle_If_eq] THEN
  RVEQ_TAC THEN
  REWRITE_TAC[measure_THM; sum_CASE; FST; SND; handle_size_def] THEN
  BVLPAUX_HS_POS_TAC THEN ARITH_TAC;;

let handle_simp_def = sem1aux_def_wf
  `MEASURE (\x:bvl_exp + bvl_exp list + bvl_exp # bvl_exp # num.
              sum_CASE x (\a. handle_size a)
                (\y. sum_CASE y (\a. handle_size1 a)
                       (\p. handle_size (FST p) + handle_size (FST (SND p)))))`
  BVLPAUX_HANDLE_TC_TAC
  `(handle_simp (bvl_Handle x1 x2) = make_handle x1 x2 0) /\
   (handle_simp (bvl_Var v) = bvl_Var v) /\
   (handle_simp (bvl_If x1 x2 x3) =
      bvl_If (handle_simp x1) (handle_simp x2) (handle_simp x3)) /\
   (handle_simp (bvl_Let xs x2) = bvl_Let (handle_simp_list xs) (handle_simp x2)) /\
   (handle_simp (bvl_Raise x1) = bvl_Raise (handle_simp x1)) /\
   (handle_simp (bvl_Op op xs) = bvl_Op op (handle_simp_list xs)) /\
   (handle_simp (bvl_Tick x) = bvl_Tick (handle_simp x)) /\
   (handle_simp (bvl_Force m n) = bvl_Force m n) /\
   (handle_simp (bvl_Call t dest xs) = bvl_Call t dest (handle_simp_list xs)) /\
   (handle_simp_list [] = []:bvl_exp list) /\
   (handle_simp_list (CONS x xs) = CONS (handle_simp x) (handle_simp_list xs)) /\
   (make_handle x1 x2 l =
      match dest_handle_Raise x1 with
        SOME r -> bvl_Let [r] (handle_adj_vars 1 l (handle_simp x2))
      | NONE ->
      match dest_handle_Let x1 with
        SOME (xs,x) ->
          bvl_Let (handle_simp_list xs) (make_handle x x2 (l + LENGTH xs))
      | NONE ->
      match dest_handle_If x1 with
        SOME (INR (b1,b2,b3)) ->
          bvl_If (handle_simp b1) (handle_simp b2) (make_handle b3 x2 l)
      | SOME (INL (b1,b2,b3)) ->
          bvl_If (handle_simp b1) (make_handle b2 x2 l) (handle_simp b3)
      | NONE ->
          bvl_Handle (handle_simp x1) (handle_adj_vars 1 l (handle_simp x2)))`;;

let handle_simp_ind = cake_ind "handle_simp";;

(* HOL4 GENLIST is list_of_seq; fvs : 'a spt in HOL4 (num_set where used) *)

let SmartLet_def = cake_def
  `SmartLet xs (x:bvl_exp) = if NULL xs then x else bvl_Let xs x`;;

let LetLet_def = cake_def
  `LetLet env_length (fvs:A spt) (body:bvl_exp) =
     let xs = list_of_seq I env_length in
     let zs = FILTER (\n. IS_SOME (lookup n fvs)) xs in
     let ys = MAPi (\i x. (x,i)) zs in
     let long_list =
       list_of_seq (\n. match ALOOKUP ys n with
                          NONE -> bvl_Op (IntOp (clos_Const (&0))) []
                        | SOME k -> bvl_Var k) env_length in
       bvl_Let (MAP bvl_Var zs) (SmartLet long_list body)`;;

let OptionalLetLet_def = cake_def
  `OptionalLetLet (e:bvl_exp) env_size live s (limit:num) (nr:bool) =
     if s < limit then ([e],live,s,nr) else
       let fvs = db_to_set live in
       let flat_live = vars_from_list (MAP FST (toAList fvs)) in
         ([bvl_Let [] (LetLet env_size fvs e)],flat_live,0,nr)`;;

let OptionalLetLet_sing_def = cake_def
  `OptionalLetLet_sing (e:bvl_exp) env_size live s (limit:num) (nr:bool) =
     if s < limit then (e,live,s,nr) else
       let fvs = db_to_set live in
       let flat_live = vars_from_list (MAP FST (toAList fvs)) in
         (bvl_Let [] (LetLet env_size fvs e),flat_live,0,nr)`;;

(* HOL4: the paired lambda \(d,l,s,nr). ([d],l,s,nr) is written as a match *)

let OptionalLetLet_sing_eq = prove
 (CASE_TERM
  `OptionalLetLet e sz lv s lim nr =
     (\p. match p with (d,l,s,nr) -> ([d],l,s,nr))
       (OptionalLetLet_sing e sz lv s lim nr)`,
  REWRITE_TAC[OptionalLetLet_def; OptionalLetLet_sing_def] THEN
  COND_CASES_TAC THEN CASE_REWRITE_TAC[LET_DEF; LET_END_DEF]);;

(* HOL4 Empty, Var, Shift of db_vars are db_vars_Empty, db_vars_Var,      *)
(* db_vars_Shift; termination (automatic in HOL4) by the size of the       *)
(* expression list                                                          *)

let bvl_handle_compile_def = sem1aux_def_wf
  `MEASURE (\p:num#num#bvl_exp list. list_size bvl_exp_size (SND (SND p)))`
  SEM1AUX_TC_TAC
  `(bvl_handle_compile l n [] = ([]:bvl_exp list,db_vars_Empty,0,T)) /\
   (bvl_handle_compile l n (CONS x (CONS y xs)) =
      let (dx,lx,s1,nr1) = bvl_handle_compile l n [x] in
      let (dy,ly,s2,nr2) = bvl_handle_compile l n (CONS y xs) in
        (APPEND dx dy,mk_Union lx ly,s1 + s2,(nr1 /\ nr2))) /\
   (bvl_handle_compile l n [bvl_Var v] =
      if v < n then ([bvl_Var v],db_vars_Var v,1,T)
      else ([bvl_Op (IntOp (clos_Const (&0))) []],db_vars_Empty,1,T)) /\
   (bvl_handle_compile l n [bvl_If x1 x2 x3] =
      let (x1,l1,s1,nr1) = bvl_handle_compile l n [x1] in
      let (x2,l2,s2,nr2) = bvl_handle_compile l n [x2] in
      let (x3,l3,s3,nr3) = bvl_handle_compile l n [x3] in
        OptionalLetLet (bvl_If (HD x1) (HD x2) (HD x3)) n
          (mk_Union l1 (mk_Union l2 l3)) (s1 + s2 + s3 + 1) l
          (nr1 /\ nr2 /\ nr3)) /\
   (bvl_handle_compile l n [bvl_Let xs x2] =
      if NULL xs then
        bvl_handle_compile l n [x2]
      else
        let k = LENGTH xs in
        let (xs,l1,s1,nr1) = bvl_handle_compile l n xs in
        let (x2,l2,s2,nr2) = bvl_handle_compile l (n + k) [x2] in
          OptionalLetLet (bvl_Let xs (HD x2)) n
            (mk_Union l1 (db_vars_Shift k l2)) (s1 + s2 + 1) l (nr1 /\ nr2)) /\
   (bvl_handle_compile l n [bvl_Handle x1 x2] =
      let (y1,l1,s1,nr1) = bvl_handle_compile l n [x1] in
        if nr1 then (y1,l1,s1,T) else
          let (y2,l2,s2,nr2) = bvl_handle_compile l (n + 1) [x2] in
            ([bvl_Handle (LetLet n (db_to_set l1) (HD y1)) (HD y2)],
             mk_Union l1 (db_vars_Shift 1 l2),
             s2,nr2)) /\
   (bvl_handle_compile l n [bvl_Raise x1] =
      let (dx,lx,s1,nr1) = bvl_handle_compile l n [x1] in
        OptionalLetLet (bvl_Raise (HD dx)) n lx (s1 + 1) l F) /\
   (bvl_handle_compile l n [bvl_Op op xs] =
      let (ys,lx,s1,nr1) = bvl_handle_compile l n xs in
        if op = clos_ThunkOp ForceThunk then
          ([bvl_Op op ys],lx,s1 + 1,F)
        else
          OptionalLetLet (bvl_Op op ys) n lx (s1 + 1) l nr1) /\
   (bvl_handle_compile l n [bvl_Tick x] =
      let (y,lx,s1,nr1) = bvl_handle_compile l n [x] in
        ([bvl_Tick (HD y)],lx,s1,nr1)) /\
   (bvl_handle_compile l n [bvl_Force m v] =
      if v < n then ([bvl_Force m v],db_vars_Var v,1,F)
      else ([bvl_Op (IntOp (clos_Const (&0))) []],db_vars_Empty,1,T)) /\
   (bvl_handle_compile l n [bvl_Call t dest xs] =
      let (ys,lx,s1,nr1) = bvl_handle_compile l n xs in
        OptionalLetLet (bvl_Call t dest ys) n lx (s1 + 1) l F)`;;

let bvl_handle_compile_ind = cake_ind "bvl_handle_compile";;

let bvl_handle_compile_sing_def = sem1aux_def_wf
  `MEASURE (\x:num#num#bvl_exp + num#num#bvl_exp list.
              sum_CASE x (\p. bvl_exp_size (SND (SND p)))
                         (\p. list_size bvl_exp_size (SND (SND p))))`
  SEM1AUX_TC_TAC
  `(bvl_handle_compile_sing l n (bvl_Var v) =
      if v < n then (bvl_Var v,db_vars_Var v,1,T)
      else (bvl_Op (IntOp (clos_Const (&0))) [],db_vars_Empty,1,T)) /\
   (bvl_handle_compile_sing l n (bvl_If x1 x2 x3) =
      let (x1,l1,s1,nr1) = bvl_handle_compile_sing l n x1 in
      let (x2,l2,s2,nr2) = bvl_handle_compile_sing l n x2 in
      let (x3,l3,s3,nr3) = bvl_handle_compile_sing l n x3 in
        OptionalLetLet_sing (bvl_If x1 x2 x3) n
          (mk_Union l1 (mk_Union l2 l3)) (s1 + s2 + s3 + 1) l
          (nr1 /\ nr2 /\ nr3)) /\
   (bvl_handle_compile_sing l n (bvl_Let xs x2) =
      if NULL xs then
        bvl_handle_compile_sing l n x2
      else
        let k = LENGTH xs in
        let (xs,l1,s1,nr1) = bvl_handle_compile_list l n xs in
        let (x2,l2,s2,nr2) = bvl_handle_compile_sing l (n + k) x2 in
          OptionalLetLet_sing (bvl_Let xs x2) n
            (mk_Union l1 (db_vars_Shift k l2)) (s1 + s2 + 1) l (nr1 /\ nr2)) /\
   (bvl_handle_compile_sing l n (bvl_Handle x1 x2) =
      let (y1,l1,s1,nr1) = bvl_handle_compile_sing l n x1 in
        if nr1 then (y1,l1,s1,T) else
          let (y2,l2,s2,nr2) = bvl_handle_compile_sing l (n + 1) x2 in
            (bvl_Handle (LetLet n (db_to_set l1) y1) y2,
             mk_Union l1 (db_vars_Shift 1 l2),
             s2,nr2)) /\
   (bvl_handle_compile_sing l n (bvl_Raise x1) =
      let (dx,lx,s1,nr1) = bvl_handle_compile_sing l n x1 in
        OptionalLetLet_sing (bvl_Raise dx) n lx (s1 + 1) l F) /\
   (bvl_handle_compile_sing l n (bvl_Op op xs) =
      let (ys,lx,s1,nr1) = bvl_handle_compile_list l n xs in
        if op = clos_ThunkOp ForceThunk then
          (bvl_Op op ys,lx,s1 + 1,F)
        else
          OptionalLetLet_sing (bvl_Op op ys) n lx (s1 + 1) l nr1) /\
   (bvl_handle_compile_sing l n (bvl_Tick x) =
      let (y,lx,s1,nr1) = bvl_handle_compile_sing l n x in
        (bvl_Tick y,lx,s1,nr1)) /\
   (bvl_handle_compile_sing l n (bvl_Force m v) =
      if v < n then (bvl_Force m v,db_vars_Var v,1,F)
      else (bvl_Op (IntOp (clos_Const (&0))) [],db_vars_Empty,1,T)) /\
   (bvl_handle_compile_sing l n (bvl_Call t dest xs) =
      let (ys,lx,s1,nr1) = bvl_handle_compile_list l n xs in
        OptionalLetLet_sing (bvl_Call t dest ys) n lx (s1 + 1) l F) /\
   (bvl_handle_compile_list l n [] = ([]:bvl_exp list,db_vars_Empty,0,T)) /\
   (bvl_handle_compile_list l n (CONS x xs) =
      let (dx,lx,s1,nr1) = bvl_handle_compile_sing l n x in
      let (dy,ly,s2,nr2) = bvl_handle_compile_list l n xs in
        (CONS dx dy,mk_Union lx ly,s1 + s2,(nr1 /\ nr2)))`;;

(* HOL4 proves compile_sing_eq with pairarg_tac; here BVLPAUX_PAIRARG_TAC   *)
(* splits the innermost pair_CASE e f of the goal whose scrutinee e is free *)
(* (no bound variable, no case or conditional inside), keeping e = (a,b) as *)
(* an assumption (the kit's PAIRARG_TAC picks outer nested scrutinees first *)
(* and can pick an occurrence under a binder of a free variable of the same *)
(* name, which made it loop on these goals)                                 *)

let BVLPAUX_PAIRARG_TAC : tactic =
  fun (asl,w as gl) ->
    let rec go bvs t =
      let here =
        is_case_app t &&
        (let c,x,_ = dest_case_app t in
         fst(dest_const c) = "pair_CASE" && not (is_pair x) &&
         not (can (find_term is_case_app) x) &&
         not (can (find_term is_cond) x) &&
         intersect (frees x) bvs = []) in
      if here then t else
      match t with
        Comb(f,a) -> (try go bvs f with Failure _ -> go bvs a)
      | Abs(v,b) -> go (v::bvs) b
      | _ -> failwith "BVLPAUX_PAIRARG_TAC" in
    let _,x,_ = dest_case_app (go [] w) in
    let v = genvar (type_of x) in
    let lemma = mk_forall(v,mk_imp(mk_eq(x,v),subst [v,x] w)) in
    (SUBGOAL_THEN lemma (fun th -> ACCEPT_TAC (MP (SPEC x th) (REFL x))) THEN
     REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
     CASE_REWRITE_TAC[HD; APPEND]) gl;;

(* split every pair and every conditional of the goal *)

let BVLPAUX_SPLIT_ALL_TAC : tactic =
  REPEAT (BVLPAUX_PAIRARG_TAC ORELSE
          (COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
           CASE_REWRITE_TAC[HD; APPEND])) THEN
  REWRITE_TAC[mk_Union_Empty; ADD_CLAUSES; AND_CLAUSES; HD; APPEND];;

let bvl_handle_compile_sing_eq = prove
 (CASE_TERM
  `(!e l n. bvl_handle_compile l n [e] =
            (\p. match p with (d,l,s,nr) -> ([d],l,s,nr))
              (bvl_handle_compile_sing l n e)) /\
   (!es l n. bvl_handle_compile l n es = bvl_handle_compile_list l n es)`,
  MATCH_MP_TAC bvl_exp_INDUCT THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REPEAT DISCH_TAC THEN REPEAT GEN_TAC THENL
   [ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC;
    ALL_TAC; ALL_TAC; CASES_ON `a1:bvl_exp list`] THEN
  ASM_REWRITE_TAC[bvl_handle_compile_def; bvl_handle_compile_sing_def;
                  OptionalLetLet_sing_eq; LET_DEF; LET_END_DEF] THEN
  BVLPAUX_SPLIT_ALL_TAC);;

(* HOL4: bvl_const$compile_exp is bvl_const_compile_exp *)

let bvl_handle_compile_exp_def = cake_def
  `bvl_handle_compile_exp cut_size arity e =
     HD (FST (bvl_handle_compile cut_size arity
                [handle_simp (bvl_const_compile_exp e)]))`;;

let bvl_handle_compile_exp_eq = prove
 (`bvl_handle_compile_exp cut_size arity e =
     FST (bvl_handle_compile_sing cut_size arity
            (handle_simp (bvl_const_compile_exp e)))`,
  REWRITE_TAC[bvl_handle_compile_exp_def; bvl_handle_compile_sing_eq] THEN
  BVLPAUX_SPLIT_ALL_TAC THEN REWRITE_TAC[FST]);;

(* HOL4 defines dest_Seq with the literal pattern Let [e1;e2] (Var 1) and a *)
(* catch-all clause; the kit does not complete clauses with literals, so   *)
(* the literal is the condition n = 1 (the other clauses are the completed *)
(* catch-all, as in HOL4)                                                   *)

let bvl_handle_dest_Seq_def = sem1aux_def
  `(bvl_handle_dest_Seq (bvl_Let [e1; e2] (bvl_Var n)) =
      if n = 1 then SOME (e1,e2) else NONE) /\
   (bvl_handle_dest_Seq _ = NONE)`;;

let bvl_handle_dest_Seq_ind = BVLPAUX_case_ind bvl_handle_dest_Seq_def;;

let bvl_handle_dest_Seq_pmatch = prove
 (CASE_TERM
  `!exp. bvl_handle_dest_Seq exp =
         match exp with
           bvl_Let [e1; e2] (bvl_Var 1) -> SOME (e1,e2)
         | _ -> NONE`,
  MATCH_MP_TAC bvl_handle_dest_Seq_ind THEN
  REWRITE_TAC[bvl_handle_dest_Seq_def] THEN CASE_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

(* for the termination of compile_seqs (HOL4 uses dest_Seq_ind there) *)

let BVLPAUX_dest_Seq_eq = prove
 (`!e p. bvl_handle_dest_Seq e = SOME p <=>
         ?ds1 ds2. e = bvl_Let [ds1; ds2] (bvl_Var 1) /\ p = (ds1,ds2)`,
  MATCH_MP_TAC bvl_handle_dest_Seq_ind THEN
  REWRITE_TAC[bvl_handle_dest_Seq_def] THEN CASE_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN CASE_REWRITE_TAC[] THEN
  ASM_MESON_TAC[]);;

(* HOL4: Termination WF_REL_TAC `measure (\(c,e,a). exp_size e)` *)

let compile_seqs_def = cake_def_wf
  `MEASURE (\p:num#bvl_exp#bvl_exp option. bvl_exp_size (FST (SND p)))`
  (REWRITE_TAC[IMP_CONJ] THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
   RVEQ_TAC THEN FS[BVLPAUX_dest_Seq_eq] THEN RVEQ_TAC THEN TERM_TAC)
  `compile_seqs cut_size e acc =
     match bvl_handle_dest_Seq e with
       NONE -> (let new_e = bvl_handle_compile_exp cut_size 0 e in
                match acc with
                  NONE -> new_e
                | SOME rest -> bvl_Let [new_e] (bvl_Let [] (bvl_Let [] rest)))
     | SOME (e1,e2) ->
         compile_seqs cut_size e1 (SOME (compile_seqs cut_size e2 acc))`;;

let compile_seqs_ind = cake_ind "compile_seqs";;

let compile_any_def = cake_def
  `compile_any split_seq cut_size arity e =
     if arity = 0 /\ split_seq then compile_seqs cut_size e NONE
     else bvl_handle_compile_exp cut_size arity e`;;

let bvl_handle_compile_length = prove
 (`!l n xs. LENGTH (FST (bvl_handle_compile l n xs)) = LENGTH xs`,
  MATCH_MP_TAC bvl_handle_compile_ind THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[bvl_handle_compile_def; LET_DEF; LET_END_DEF] THEN
  REPEAT (BVLPAUX_PAIRARG_TAC ORELSE COND_CASES_TAC) THEN
  GVS[OptionalLetLet_def; LENGTH_APPEND] THEN RW[] THEN ARITH_TAC);;

let _ = cake_add_simps [bvl_handle_compile_length];;

(* HOL4: s is the pair of the last two components *)

let bvl_handle_compile_sing = prove
 (`bvl_handle_compile l n [x] = (dx,lx,s:num#bool) ==> ?y. dx = [y]`,
  DISCH_TAC THEN
  MP_TAC (SPECL [`l:num`; `n:num`; `[x:bvl_exp]`] bvl_handle_compile_length) THEN
  ASM_REWRITE_TAC[FST] THEN
  CASES_ON `dx:bvl_exp list` THEN RW[LENGTH; LENGTH_EQ_NIL]);;

(* HOL4: compile_seqs_def specialised to NONE and SOME y, lets unfolded *)

let compile_seqs_compute = prove
 (CASE_TERM
  `(compile_seqs e c NONE =
      match bvl_handle_dest_Seq c with
        NONE -> bvl_handle_compile_exp e 0 c
      | SOME (e1,e2) -> compile_seqs e e1 (SOME (compile_seqs e e2 NONE))) /\
   (compile_seqs e c (SOME y) =
      match bvl_handle_dest_Seq c with
        NONE ->
          bvl_Let [bvl_handle_compile_exp e 0 c] (bvl_Let [] (bvl_Let [] y))
      | SOME (e1,e2) ->
          compile_seqs e e1 (SOME (compile_seqs e e2 (SOME y))))`,
  CONJ_TAC THEN GEN_REWRITE_TAC LAND_CONV [compile_seqs_def] THEN
  CASE_REWRITE_TAC[LET_DEF; LET_END_DEF]);;
