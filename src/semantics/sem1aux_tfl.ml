(* ========================================================================= *)
(* sem1aux_tfl: definitions with many clauses, compiled as HOL4's TFL does   *)
(* (an extension of the kit's definition tools).                             *)
(*                                                                           *)
(*   sem1aux_def `clauses`              like cake_def                        *)
(*   sem1aux_def_wf `R` tac `clauses`   like cake_def_wf                     *)
(*                                                                           *)
(* HOL Light's recursion package checks a casewise definition with one       *)
(* condition per pair of clauses, so a definition with tens of clauses (a    *)
(* catch-all clause completed into many) takes hours.  These functions do    *)
(* what HOL4's TFL does:                                                     *)
(* 1. complete overlapping clauses (the kit's complete_all_clauses);         *)
(* 2. compile the clauses of each function into one case tree on its         *)
(*    arguments (the kit's compile_rows: first match wins, unmatched is ARB);*)
(* 3. define each function by that single clause (new_definition when       *)
(*    nothing is recursive, else the steps of the kit's cake_def_gen and     *)
(*    cake_def_mutual with the relation, without their induction theorem);   *)
(* 4. prove the completed clauses from it by rewriting: the theorem          *)
(*    returned (HOL4's NAME_def, quantified as cake_def does);               *)
(* 5. for a recursive definition, derive the induction theorem with one      *)
(*    case per completed clause (HOL4's NAME_ind) with the kit's             *)
(*    derive_induction, from the termination conditions of the clauses: the *)
(*    recursive calls with their contexts (the condition of an if, the       *)
(*    equation scrutinee = pattern of a case arm, MEM y l for ALL, EX and    *)
(*    MAP, the antecedent of ==>), each proved by the tactic; cake_ind       *)
(*    "NAME" then returns it.                                                *)
(* The relation and the tactic are those of cake_def_wf (on the tupled       *)
(* arguments, on their sum for mutual recursion); the tactic must prove the  *)
(* termination conditions of step 3 (single clause) and of step 5.           *)
(* sem1aux_def without a relation tries the kit's size measures with         *)
(* SEM1AUX_TC_TAC.  sem1aux_verbose := true prints the time of each step.     *)
(* ========================================================================= *)

needs "hol4/vocab.ml";;

type_invention_error := true;;

(* a termination tactic for both kinds of termination conditions: split the *)
(* context without STRIP_TAC (its existentials may bind the names of free    *)
(* variables), eliminate the variable equations, then the kit's TERM_TAC     *)

let SEM1AUX_TC_TAC : tactic =
  REWRITE_TAC[IMP_CONJ] THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  RVEQ_TAC THEN TERM_TAC;;

(* sem1aux_verbose := true prints the time of each phase *)

let sem1aux_verbose = ref false;;

let sem1aux_time name f x =
  if not !sem1aux_verbose then f x else
  let t0 = Sys.time() in
  let r = f x in
  Format.print_string (Printf.sprintf "sem1aux: %s %.1f s\n"
                         name (Sys.time() -. t0));
  Format.print_flush(); r;;

let sem1aux_list_consts = ["ALL"; "EX"; "MAP"];;

(* the calls of the functions fns in t with their contexts, innermost      *)
(* context first; bound variables are renamed apart from avoid0            *)

let sem1aux_calls (fns:term list) (avoid0:term list) (t:term) =
  let avoid = ref avoid0 in
  let open_abs t = let v,b = dest_abs t in
                   let v' = pm_fresh avoid v in v',vsubst [v',v] b in
  let rec go ctx t =
    let h,args = strip_comb t in
    if mem h fns then
      (ctx,t) :: flat (map (go ctx) args)
    else if is_cond t then
      let b,(x,y) = dest_cond t in
      go ctx b @ go (b::ctx) x @ go (mk_neg b::ctx) y
    else if is_imp t then
      let a,b = dest_imp t in
      go ctx a @ go (a::ctx) b
    else if is_case_app t then
      let c,s,fs = dest_case_app t in
      let ci = case_info_of_const c in
      go ctx s @
      flat (map2 (fun (vs,pat) f ->
        let tyi = type_match (type_of pat) (type_of s) [] in
        let rec take n t acc =
          if n = 0 then Some(rev acc,t)
          else if is_abs t then let v,b = open_abs t in take (n-1) b (v::acc)
          else None in
        match take (length vs) f [] with
          Some(avs,body) ->
            let pat' = vsubst (zip avs (map (inst tyi) vs)) (inst tyi pat) in
            go (mk_eq(s,pat')::ctx) body
        | None -> go ctx f) ci.ci_pats fs)
    else if is_const h && mem (fst(dest_const h)) sem1aux_list_consts &&
            length args = 2 && is_abs (hd args) then
      let l = el 1 args in
      let y,body = open_abs (hd args) in
      let mem_tm = mk_comb(mk_comb(mk_const("MEM",[type_of y,aty]),y),l) in
      go ctx l @ go (mem_tm::ctx) body
    else match t with
      Comb(a,b) -> go ctx a @ go ctx b
    | Abs(_,_) -> let _,b = open_abs t in go ctx b
    | _ -> [] in
  go [] t;;

(* the mutual induction theorem of f1 .. fk from the induction theorem ind *)
(* of their encoding on the sum of the argument tuples (as cake_def_mutual) *)

let sem1aux_mutual_ind (fns:term list) (ns:int list) (argtups:hol_type list)
                       (ind:thm) =
  let k = length fns in
  let ps = map2 (fun f ty ->
                   let atys = fst(chop_list (el (index f fns) ns)
                                    (fst(splitlist dest_fun_ty (type_of f)))) in
                   mk_var("P"^fst(dest_var f),itlist mk_fun_ty atys bool_ty))
                fns argtups in
  let pfun i =
    let n = el i ns in
    let t = mk_var("t_mr",el i argtups) in
    mk_abs(t,list_mk_comb(el i ps,if n = 1 then [t] else tuple_selectors n t)) in
  let rec qterm l i = match l with
      [_] -> pfun i
    | _::rest ->
        let s = mk_var("s_mr",mk_sum_ty l) in
        let a = pfun i and b = qterm rest (i+1) in
        mk_abs(s,list_mk_icomb "sum_CASE" [s;a;b])
    | [] -> failwith "sem1aux_mutual_ind" in
  let q = qterm argtups 0 in
  let th1 = ISPEC q ind in
  (* with three or more functions a sum_CASE reduces to a beta-redex whose *)
  (* reduct is a sum_CASE again: reduce until nothing changes (the fix of   *)
  (* compiler/backend/il1aux_mutual.ml)                                     *)
  let step = PURE_REWRITE_CONV[sum_CASE; FST; SND] THENC
             TOP_DEPTH_CONV BETA_CONV in
  let th2 = CONV_RULE (TOP_DEPTH_CONV BETA_CONV THENC
                       REPEATC (CHANGED_CONV step) THENC
                       PURE_REWRITE_CONV[FST; SND]) th1 in
  let rec split_conv l = match l with
      [] | [_] -> ALL_CONV
    | _::rest -> GEN_REWRITE_CONV I [SUM_CASE_FORALL] THENC
                 RAND_CONV (BINDER_CONV BETA_CONV THENC split_conv rest) in
  let th3 = CONV_RULE (RAND_CONV (split_conv argtups THENC
                                  TOP_DEPTH_CONV BETA_CONV)) th2 in
  let concl_conv =
    let rec go i tm =
      if i = k - 1 then FORALL_TUPLE_CONV (el i ns) tm
      else let l,r = dest_conj tm in
           MK_CONJ (FORALL_TUPLE_CONV (el i ns) l) (go (i+1) r) in
    go 0 in
  let th4 = CONV_RULE (RAND_CONV (concl_conv THENC
                                  PURE_REWRITE_CONV[FST; SND])) th3 in
  (* the variables of each conjunct of the conclusion are x1, x2, ... *)
  let rename_binders tm =
    let rec go i tm =
      if is_forall tm then
        let v = fst(dest_forall tm) in
        (GEN_ALPHA_CONV (mk_var("x"^string_of_int i,type_of v)) THENC
         BINDER_CONV (go (i+1))) tm
      else REFL tm in
    go 1 tm in
  let th5 = CONV_RULE (RAND_CONV (DEPTH_BINOP_CONV `(/\)` rename_binders)) th4 in
  GENL ps th5;;

(* the kit's cake_def_gen for recursive clauses of ONE function, without    *)
(* its induction theorem (sem1aux_def_gen derives the clause-shaped one)    *)

let sem1aux_core_single (r,tac) (tm:term) : thm =
  let cls = dest_clauses tm in
  let f = match cls with (_,f,_,_)::_ -> f | [] -> failwith "sem1aux_core" in
  let name = fst(dest_var f) in
  let tm0 = close_clauses [f] tm in
  let attempt () =
    let cth = if !cake_case_to_match then CASE_TO_MATCH_CONV tm0 else REFL tm0 in
    let etm = mk_exists(f,rand(concl cth)) in
    let eth0 = sem1aux_time "recursion" cake_pure_prove_recursive_function_exists etm in
    let eth,_ = sem1aux_time "termination" (discharge_hyps name (Some(r,tac))) eth0 in
    if not (aconv (concl eth) etm) then
      failwith "sem1aux_core: the existence theorem is not about the clauses" else
    let eth' = EQ_MP (SYM (MK_EXISTS f cth)) eth in
    CONV_RULE (DEPTH_CONV ETA_MARKED_CONV) (new_specification [name] eth') in
  if !cake_case_to_match then attempt () else
  (* the recursion package may leave an admissibility claim of a case tree  *)
  (* unproved (it then fails as a termination condition): retry through     *)
  (* match terms                                                            *)
  try attempt () with Failure _ ->
    let saved = !cake_case_to_match in
    Format.print_string ("sem1aux: "^name^": retrying with cake_case_to_match\n");
    Format.print_flush();
    cake_case_to_match := true;
    try let th = attempt () in cake_case_to_match := saved; th
    with e -> (cake_case_to_match := saved; raise e);;

(* the kit's cake_def_mutual (the same encoding on the sum of the argument  *)
(* tuples), with sem1aux_core_single for the encoded function               *)

let sem1aux_core_mutual (r,tac) (tm:term) : thm =
  let cls = dest_clauses tm in
  let rec order acc l = match l with
      [] -> rev acc
    | (_,f,_,_)::t -> if mem f acc then order acc t else order (f::acc) t in
  let fns = order [] cls in
  let k = length fns in
  let arity f = let (_,_,args,_) = find (fun (_,g,_,_) -> g = f) cls in
                length args in
  let ns = map arity fns in
  let split_ty f n = let tys,r = splitlist dest_fun_ty (type_of f) in
                     let a,b = chop_list n tys in
                     a, itlist mk_fun_ty b r in
  let sigs = map2 split_ty fns ns in
  let argtups = map (fun (a,_) -> mk_tuple_ty a) sigs in
  let restys = map snd sigs in
  let sty = mk_sum_ty argtups and rty = mk_sum_ty restys in
  let names = map (fst o dest_var) fns in
  let fname = end_itlist (fun a b -> a^"_"^b) names ^ "_MUTREC" in
  let ff = mk_var(fname,mk_fun_ty sty rty) in
  let encode i f =
    let n = el i ns and (atys,_) = el i sigs in
    let xs = map2 (fun ty j -> mk_var("x_mr"^string_of_int j,ty)) atys (1--n) in
    list_mk_abs(xs,mk_sum_proj restys i
                     (mk_comb(ff,mk_sum_inj argtups i (mk_tuple_term xs)))) in
  let substs = map2 (fun f i -> encode i f,f) fns (0--(k-1)) in
  let beta_new t = rhs(concl(TOP_DEPTH_CONV BETA_CONV t)) in
  let fclause (vs,f,args,r) =
    let i = index f fns in
    let lhs_ = mk_comb(ff,mk_sum_inj argtups i (mk_tuple_term args)) in
    let r' = mk_sum_inj restys i (beta_new (vsubst substs r)) in
    list_mk_forall(vs,mk_eq(lhs_,r')) in
  let ftm = list_mk_conj(map fclause cls) in
  let fdef = sem1aux_core_single (r,tac) ftm in
  let fconst = mk_const(fname,[]) in
  let fconst = inst (type_match (type_of fconst) (type_of ff) []) fconst in
  let fdefs = map2 (fun f i ->
      let n = el i ns and (atys,_) = el i sigs in
      let xs = map2 (fun ty j -> mk_var("x"^string_of_int j,ty)) atys (1--n) in
      let r = mk_sum_proj restys i
                (mk_comb(fconst,mk_sum_inj argtups i (mk_tuple_term xs))) in
      new_definition (mk_eq(list_mk_comb(f,xs),r)))
    fns (0--(k-1)) in
  let consts = map (fun f -> let c = mk_const(fst(dest_var f),[]) in
                             inst (type_match (type_of c) (type_of f) []) c)
                   fns in
  let csubst = zip consts fns in
  let fold_conv = PURE_REWRITE_CONV (map GSYM fdefs) in
  let clause_thm (vs,f,args,r) =
    let i = index f fns in
    let tm = vsubst csubst (list_mk_forall(vs,mk_eq(list_mk_comb(f,args),r))) in
    CONV_RULE (DEPTH_CONV ETA_MARKED_CONV) (prove(tm,
      REPEAT GEN_TAC THEN
      CONV_TAC(LAND_CONV(REWR_CONV (SPEC_ALL (el i fdefs)) THENC
                         RAND_CONV(PURE_ONCE_REWRITE_CONV[fdef]) THENC
                         PURE_REWRITE_CONV[OUTL; OUTR] THENC fold_conv)) THEN
      REFL_TAC)) in
  end_itlist CONJ (map clause_thm cls);;

(* bound variables with a marked name (eta%1, x%pm2) get plain names *)

let sem1aux_rename_marked_conv : conv =
  let rec conv avoid tm =
    match tm with
      Comb(a,b) -> MK_COMB(conv avoid a,conv avoid b)
    | Abs(v,b) ->
        let n,ty = dest_var v in
        if String.contains n '%' then
          let base = String.sub n 0 (String.index n '%') in
          let base = if base = "eta" || base = "" then "x" else base in
          let v' = variant (avoid @ frees tm) (mk_var(base,ty)) in
          let th1 = ALPHA_CONV v' tm in
          let v'',b' = dest_abs(rand(concl th1)) in
          TRANS th1 (ABS v'' (conv (v''::avoid) b'))
        else ABS v (conv (v::avoid) b)
    | _ -> REFL tm in
  fun tm -> conv [] tm;;

let sem1aux_def_gen (rel_tac : (term * tactic) option) (tm:term) : thm =
  let tm1 = complete_all_clauses (rename_wildcards (cases_of_matches tm)) in
  let cls1 = dest_clauses tm1 in
  let rec order acc l = match l with
      [] -> rev acc
    | (_,f,_,_)::t -> if mem f acc then order acc t else order (f::acc) t in
  let fns = order [] cls1 in
  if exists (fun f -> not (is_var f)) fns then
    failwith "sem1aux_def: a defined function is a constant" else
  let arity f = match find (fun (_,g,_,_) -> g = f) cls1 with
                  (_,_,args,_) -> length args in
  let ns = map arity fns in
  if exists (fun (_,f,args,_) -> length args <> arity f) cls1 then
    failwith "sem1aux_def: clauses with different numbers of arguments" else
  let tm2 = itlist2 (fun f k t -> eta_expand_bare k f t) fns ns tm1 in
  let tm0 = close_clauses fns tm2 in
  let cls = dest_clauses tm0 in
  let recursive =
    exists (fun (_,_,_,r) -> exists (fun f -> free_in f r) fns) cls in
  let names = map (fst o dest_var) fns in
  let sigs = map2 (fun f n -> let tys,r = splitlist dest_fun_ty (type_of f) in
                              let a,b = chop_list n tys in
                              a, itlist mk_fun_ty b r) fns ns in
  (* 2. the case tree of each function; the argument variables of all the  *)
  (* functions get distinct names (the recursion package mixes the         *)
  (* variables of the clauses of a mutual definition)                      *)
  let avoid = ref (fns @ frees tm0) in
  let tree f =
    let n = arity f and (atys,rty) = el (index f fns) sigs in
    let fcls = filter (fun (_,g,_,_) -> g = f) cls in
    let xs = map2 (fun ty j ->
        let base = match fcls with
            (_,_,args,_)::_ when is_var (el j args) -> fst(dest_var (el j args))
          | _ -> "x"^string_of_int (j + 1) in
        pm_fresh avoid (mk_var(base,ty))) atys (0--(n-1)) in
    let counter = ref 0 in
    let rows = map (fun (_,_,args,r) ->
        let pvs = filter (fun v -> not (is_wildcard v)) (freesl args) in
        let ren = map (fun v -> incr counter;
                         mk_var(fst(dest_var v)^"%pm"^string_of_int !counter,
                                type_of v),v) pvs in
        {pm_pats = map (vsubst ren) args; pm_guard = None;
         pm_rhs = vsubst ren r}) fcls in
    let avoid0 = !avoid @ flat (map (fun r -> freesl r.pm_pats) rows) in
    let body = compile_rows avoid0 xs rows (mk_const("ARB",[rty,aty])) in
    list_mk_forall(xs,mk_eq(list_mk_comb(f,xs),body)) in
  let deftm = list_mk_conj (map tree fns) in
  (* 3. the definition by one clause per function *)
  let def1,rel_tac_used =
    if not recursive then
      end_itlist CONJ
        (map (fun c -> new_definition (snd(strip_forall c))) (conjuncts deftm)),
      None
    else
    let core rt = if length fns = 1 then sem1aux_core_single rt deftm
                  else sem1aux_core_mutual rt deftm in
    match rel_tac with
      Some(r,tac) -> core (r,tac),Some(r,tac)
    | None ->
        let argtups = map (fun (a,_) -> mk_tuple_ty a) sigs in
        let cands = if length fns = 1 then measure_candidates (hd argtups)
                    else sum_measure_candidates argtups in
        let saved = !cake_quiet in
        let rec go l = match l with
            [] -> failwith "sem1aux_def: termination not proved; use sem1aux_def_wf"
          | r::rest ->
              (try cake_quiet := true;
                   let th = core (r,SEM1AUX_TC_TAC) in
                   cake_quiet := saved; th,Some(r,SEM1AUX_TC_TAC)
               with Failure _ -> (cake_quiet := saved; go rest)) in
        go cands in
  let consts = map (fun f -> let c = mk_const(fst(dest_var f),[]) in
                             inst (type_match (type_of c) (type_of f) []) c) fns in
  let csubst = zip consts fns in
  let fdefs = CONJUNCTS def1 in
  (* 4. the completed clauses *)
  let clause_thm (vs,f,args,r) =
    let i = index f fns in
    let stmt = vsubst csubst (list_mk_forall(vs,mk_eq(list_mk_comb(f,args),r))) in
    let stmt = rhs(concl(DEPTH_CONV ETA_MARKED_CONV stmt)) in
    try prove(stmt,
              REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [el i fdefs] THEN
              CAKE_REWRITE_TAC[] THEN TRY REFL_TAC THEN NO_TAC)
    with Failure _ ->
      failwith ("sem1aux_def: could not prove the clause "^string_of_term stmt) in
  let def = sem1aux_time "clauses" (fun () -> end_itlist CONJ (map clause_thm cls)) () in
  (* 5. the induction theorem *)
  (if recursive then
     match rel_tac_used with
       None -> ()
     | Some(r,tac) ->
     try
       let argtups = map (fun (a,_) -> mk_tuple_ty a) sigs in
       let sty = mk_sum_ty argtups in
       let r = inst (type_match (fst(dest_fun_ty(type_of r))) sty []) r in
       let enc i args = mk_sum_inj argtups i (mk_tuple_term args) in
       let tcs = flat (map (fun (vs,f,args,rhs_) ->
           let i = index f fns in
           let calls = sem1aux_calls fns (vs @ fns) rhs_ in
           map (fun (ctx,call) ->
                  let g,cargs = strip_comb call in
                  let j = index g fns in
                  let rr = mk_comb(mk_comb(r,enc j cargs),enc i args) in
                  let body = if ctx = [] then rr
                             else mk_imp(list_mk_conj(rev ctx),rr) in
                  (* a context may mention the functions (HOL4's TFL     *)
                  (* contexts do): they are the defined constants         *)
                  let body = vsubst csubst body in
                  list_mk_forall(frees_in_order body,body)) calls) cls) in
       let tcs = setify tcs in
       let prove_tc tc =
         try prove(tc,tac) with Failure _ ->
           failwith ("sem1aux_def: could not prove the termination condition "^
                     string_of_term tc) in
       let tc_thms = sem1aux_time "clause termination" (map prove_tc) tcs in
       let wfth = prove(mk_comb(mk_const("WF",[sty,aty]),r),WF_TAC) in
       if length fns = 1 then
         let ind = sem1aux_time "induction" (derive_induction (hd consts)
                     (map (fun (vs,_,args,_) -> vs,args) cls) tc_thms) wfth in
         let ind = CONV_RULE sem1aux_rename_marked_conv ind in
         cake_ind_store := (hd names,ind) :: !cake_ind_store
       else
         let c = mk_var("sem1aux_enc",mk_fun_ty sty bool_ty) in
         let ecls = map (fun (vs,f,args,_) -> vs,[enc (index f fns) args]) cls in
         let ind0 = sem1aux_time "induction" (derive_induction c ecls tc_thms) wfth in
         let ind = CONV_RULE sem1aux_rename_marked_conv
                     (sem1aux_mutual_ind fns ns argtups ind0) in
         do_list (fun n -> cake_ind_store := (n,ind) :: !cake_ind_store) names
     with Failure msg ->
       Format.print_string("Warning: sem1aux_def "^hd names^
                           ": no clause induction theorem ("^msg^")\n"));
  def;;

let sem1aux_def tm = sem1aux_def_gen None tm;;

let sem1aux_def_wf r tac tm = sem1aux_def_gen (Some(r,tac)) tm;;
