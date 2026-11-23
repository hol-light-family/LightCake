(* ========================================================================= *)
(* il1aux_mutual: induction theorems of definitions of three or more        *)
(* mutually recursive functions (an extension of the kit's definition        *)
(* tools).                                                                   *)
(*                                                                           *)
(* The kit's cake_def_mutual and sem1aux_def_gen (semantics/sem1aux_tfl.ml) *)
(* turn the induction theorem of the encoded function (on the sum of the    *)
(* argument tuples) into the mutual one.  For three or more functions both  *)
(* conversions stop early: a nested sum_CASE (INR ..) of a hypothesis is    *)
(* left unreduced, and the conclusion !x. sum_CASE x f (\s. sum_CASE s g h) *)
(* is split only once (the second split meets a beta-redex), so they fail   *)
(* with REWRITES_CONV and no induction theorem is stored.                   *)
(*                                                                           *)
(*   il1aux_def_wf `R` tac `clauses`                                         *)
(*                                                                           *)
(* is sem1aux_def_wf `R` tac `clauses` followed, when that leaves no         *)
(* induction theorem, by the same derivation (the termination conditions of *)
(* the clauses, the kit's derive_induction) with both conversions repeated  *)
(* until they are done; cake_ind "f" then returns the theorem for each      *)
(* function f of the definition.                                             *)
(*                                                                           *)
(*   IL1AUX_PAIRARG_TAC                                                      *)
(*                                                                           *)
(* is the kit's PAIRARG_TAC with names new for every variable of the goal:  *)
(* the kit's names are only new among the variables of the same type, so a *)
(* split of calls_sing x g = (e1,g') can make a variable e1 : clos_exp next  *)
(* to an e1 : clos_exp list, which confuses the elimination of equations.   *)
(* ========================================================================= *)

needs "semantics/sem1aux_tfl.ml";;

(* lib.ml's find, under a name of its own *)

let rec il1aux_find p l =
  match l with
    [] -> failwith "il1aux_find"
  | h::t -> if p h then h else il1aux_find p t;;

(* sem1aux_mutual_ind with the two conversions repeated *)

let il1aux_mutual_ind (fns:term list) (ns:int list) (argtups:hol_type list)
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
    | [] -> failwith "il1aux_mutual_ind" in
  let q = qterm argtups 0 in
  let th1 = ISPEC q ind in
  let step = PURE_REWRITE_CONV[sum_CASE; FST; SND] THENC
             TOP_DEPTH_CONV BETA_CONV in
  let th2 = CONV_RULE (TOP_DEPTH_CONV BETA_CONV THENC
                       REPEATC (CHANGED_CONV step)) th1 in
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

(* the induction theorem of a mutual definition made by sem1aux_def_wf r0  *)
(* tac tm: the steps of sem1aux_def_gen (clauses, termination conditions,  *)
(* derive_induction) with il1aux_mutual_ind                                 *)

let il1aux_mutual_def_ind (r0:term) (tac:tactic) (tm:term) =
  let tm1 = complete_all_clauses (rename_wildcards (cases_of_matches tm)) in
  let cls1 = dest_clauses tm1 in
  let rec order acc l = match l with
      [] -> rev acc
    | (_,f,_,_)::t -> if mem f acc then order acc t else order (f::acc) t in
  let fns = order [] cls1 in
  let arity f = match il1aux_find (fun (_,g,_,_) -> g = f) cls1 with
                  (_,_,args,_) -> length args in
  let ns = map arity fns in
  let tm2 = itlist2 (fun f k t -> eta_expand_bare k f t) fns ns tm1 in
  let tm0 = close_clauses fns tm2 in
  let cls = dest_clauses tm0 in
  let sigs = map2 (fun f n -> let tys,r = splitlist dest_fun_ty (type_of f) in
                              let a,b = chop_list n tys in
                              a, itlist mk_fun_ty b r) fns ns in
  let consts = map (fun f -> let c = mk_const(fst(dest_var f),[]) in
                             inst (type_match (type_of c) (type_of f) []) c) fns in
  let csubst = zip consts fns in
  let argtups = map (fun (a,_) -> mk_tuple_ty a) sigs in
  let sty = mk_sum_ty argtups in
  let r = inst (type_match (fst(dest_fun_ty(type_of r0))) sty []) r0 in
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
             let body = vsubst csubst body in
             list_mk_forall(frees_in_order body,body)) calls) cls) in
  let tc_thms = map (fun tc -> prove(tc,tac)) (setify tcs) in
  let wfth = prove(mk_comb(mk_const("WF",[sty,aty]),r),WF_TAC) in
  let c = mk_var("sem1aux_enc",mk_fun_ty sty bool_ty) in
  let ecls = map (fun (vs,f,args,_) -> vs,[enc (index f fns) args]) cls in
  let ind0 = derive_induction c ecls tc_thms wfth in
  let ind = CONV_RULE sem1aux_rename_marked_conv
              (il1aux_mutual_ind fns ns argtups ind0) in
  map (fst o dest_var) fns,ind;;

let il1aux_def_wf (r0:term) (tac:tactic) (tm:term) : thm =
  let def = sem1aux_def_wf r0 tac tm in
  let f = hd(conjuncts(concl def)) in
  let name = fst(dest_const(fst(strip_comb(lhs(snd(strip_forall f)))))) in
  if can cake_ind name then def else
  let names,ind = il1aux_mutual_def_ind r0 tac tm in
  do_list (fun n -> cake_ind_store := (n,ind) :: !cake_ind_store) names;
  def;;

(* the kit's PAIRARG_TAC with names new for every variable of the goal *)

let IL1AUX_PAIRARG_TAC : tactic =
  fun (asl,w as gl) ->
    let whole = list_mk_conj(w :: map (concl o snd) asl) in
    let is_cand t =
      is_case_app t &&
      (let c,x,fs = dest_case_app t in
       fst(dest_const c) = "pair_CASE" && not (is_pair x) &&
       free_in x whole) in
    let t = find_term is_cand whole in
    let _,x,fs = dest_case_app t in
    let f = hd fs in
    let tya,tyb = match dest_type(type_of x) with
        "prod",[a;b] -> a,b | _ -> failwith "IL1AUX_PAIRARG_TAC" in
    let n1,n2 =
      try let a,b = dest_abs f in let b1,_ = dest_abs b in
          fst(dest_var a),fst(dest_var b1)
      with Failure _ -> "p1","p2" in
    let names = map (fst o dest_var) (variables whole) in
    let rec fresh avoid n = if mem n avoid then fresh avoid (n ^ "'") else n in
    let m1 = fresh names n1 in
    let m2 = fresh (m1::names) n2 in
    let v1 = mk_var(m1,tya) and v2 = mk_var(m2,tyb) in
    let nch = ISPEC x (nchotomy_of_type (type_of x)) in
    (MP_TAC nch THEN
     DISCH_THEN(X_CHOOSE_THEN v1 (X_CHOOSE_THEN v2
       (fun th -> if is_var x then SUBST_ALL_TAC th
                  else SUBST_ALL_TAC th THEN ASSUME_TAC th))) THEN
     CASE_ASM_TIDY_TAC THEN CASE_REWRITE_TAC[]) gl;;
