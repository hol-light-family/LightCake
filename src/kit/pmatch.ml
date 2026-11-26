(* ========================================================================= *)
(* CakeML kit: compiling match terms into case constants (HOL4's case        *)
(* pattern compilation).                                                     *)
(*                                                                           *)
(* The port never keeps HOL Light match terms: a definition or statement may *)
(* be WRITTEN with match (nested patterns, wildcards, first match wins, as   *)
(* HOL4's case), and the kit turns every match into nested case constants    *)
(* (ty_CASE) and conditionals before anything is defined or proved:          *)
(*   cases_of_matches tm      the term with every match compiled             *)
(*   CASE_TERM tm             the same (for statements: prove(CASE_TERM `..`,*)
(*                            tac))                                          *)
(* cake_def and cake_def_wf apply it to their clauses.                       *)
(* Semantics: HOL4's.  Each occurrence of the wildcard _ is independent      *)
(* (the kit's parse_term names each _ apart: parse.ml); a numeral other     *)
(* than 0, a T/F or another literal pattern is a test x = lit; an            *)
(* unmatched value gives ARB.                                                *)
(* ========================================================================= *)

type pm_row = { pm_pats : term list; pm_guard : term option; pm_rhs : term };;

let dest_match_term tm =
  let m,arms = dest_comb tm in
  let mc,e = dest_comb m in
  if not (is_const mc && fst(dest_const mc) = "_MATCH")
  then failwith "dest_match_term" else
  let rec arms_list t =
    if is_comb t && is_comb(rator t) && is_const(rator(rator t)) &&
       fst(dest_const(rator(rator t))) = "_SEQPATTERN"
    then rand(rator t) :: arms_list (rand t) else [t] in
  let dest_arm arm =
    let y,b1 = dest_abs arm in
    let z,b2 = dest_abs b1 in
    let _,core = strip_exists b2 in
    let h,args = strip_comb core in
    match fst(dest_const h),args with
      "_UNGUARDED_PATTERN",[p;r] -> lhand p,None,lhand r
    | "_GUARDED_PATTERN",[p;g;r] -> lhand p,Some g,lhand r
    | _ -> failwith "dest_match_term: arm" in
  e,map dest_arm (arms_list arms);;

let is_match_term tm =
  try fst(dest_const(rator(rator tm))) = "_MATCH" with Failure _ -> false;;

let is_wildcard v =
  is_var v &&
  (let n = fst(dest_var v) in
   n = "_" || String.length n > 2 && String.sub n 0 3 = "_%w");;

let pm_base_name v =
  let n = fst(dest_var v) in
  try let k = String.index n '%' in String.sub n 0 k with Not_found -> n;;

(* the pattern one (HOL4's (), the only value of type :1) matches every    *)
(* value, as HOL4's one constructor does: no test, nothing bound (before    *)
(* 2026-11-25 it was a literal, a test x = one, so ONELINE and the compiled *)
(* matches had if x = one then .. else ARB)                                  *)
let kit_one_tm = mk_const("one",[]);;

let is_literal_pat p =
  (is_numeral p && dest_numeral p <> num_0) ||
  p = `T` || p = `F` ||
  (frees p = [] && not (is_numeral p) && not (is_constructor_app p) &&
   p <> kit_one_tm);;

(* a variant of v whose NAME differs from every name in avoid (HOL Light's  *)
(* variant only avoids variables of the same name and type)                 *)

let pm_fresh avoid v =
  let n0,ty = dest_var v in
  let names = map (fst o dest_var) (!avoid) in
  let rec go n = if mem n names then go (n^"'") else n in
  let v' = mk_var(go n0,ty) in
  avoid := v' :: !avoid; v';;

(* the constructor patterns of the type of s: (vars, pattern, head name) *)

let pm_constructors ty =
  let n = fst(dest_type ty) in
  let ci = case_info_of_tyname n in
  let pats = map (fun (vs,p) ->
                    let tyi = type_match (type_of p) ty [] in
                    map (inst tyi) vs, inst tyi p) ci.ci_pats in
  ci,pats;;

let pat_head p =
  if is_numeral p then "NUMERAL" else
  let h = fst(strip_comb p) in
  if is_const h then fst(dest_const h) else "";;

(* opt-in (since 2026-11-22): match (f x, f y) with .. compiles to           *)
(* pair_CASE (f x,f y) (\a b. ..) as in HOL4, so the recursion package sees  *)
(* both calls outside the arms (unconditional induction hypotheses for f x   *)
(* and f y, as HOL4's TFL gives).  By default a tuple scrutinee is split     *)
(* into its components (case on f x, then case on f y inside its arms, so    *)
(* the call f y gets the context f x = ..), as before                        *)
let cake_match_tuple_case = ref false;;

let rec pm_tuple_comps t =
  if is_pair t then let a,b = dest_pair t in pm_tuple_comps a @ pm_tuple_comps b else [t];;

let rec compile_rows (avoid0:term list) (scruts:term list)
                     (rows:pm_row list) (dflt:term) : term =
  match rows with
    [] -> dflt
  | r::rest ->
    let nonvar = filter (fun (p,_) -> not (is_var p) && p <> kit_one_tm)
                        (zip r.pm_pats scruts) in
    if nonvar = [] then
      let s = mapfilter (fun (p,s) -> if is_wildcard p || p = kit_one_tm then failwith ""
                                      else (s,p)) (zip r.pm_pats scruts) in
      let rhs_ = vsubst s r.pm_rhs in
      (match r.pm_guard with
         None -> rhs_
       | Some g -> mk_cond(vsubst s g,rhs_,compile_rows avoid0 scruts rest dflt))
    else
      let i = index (fst(hd nonvar)) r.pm_pats in
      let p0 = el i r.pm_pats and s = el i scruts in
      let replace_col l k xs = let a,b = chop_list k l in a @ xs @ tl b in
      let col = map (fun r' -> el i r'.pm_pats) rows in
      let has_suc = exists (fun p -> pat_head p = "SUC") col in
      let num_lit p = is_numeral p && not has_suc in
      if has_suc && exists (fun p -> is_numeral p && dest_numeral p <> num_0) col
      then failwith "compile_match_term: numerals other than 0 mixed with SUC"
      else if is_literal_pat p0 || num_lit p0 then
        (* rows with this literal (or a variable) at column i vs the others *)
        let yes = mapfilter (fun r' ->
            let p = el i r'.pm_pats in
            if p = p0 then {r' with pm_pats = replace_col r'.pm_pats i
                                      [mk_var("_",type_of p)]}
            else if is_var p then r'
            else failwith "") rows in
        let no = filter (fun r' -> let p = el i r'.pm_pats in
                                   is_var p || p <> p0) rows in
        let eq = if p0 = `T` then s else if p0 = `F` then mk_neg s
                 else mk_eq(s,p0) in
        mk_cond(eq,compile_rows avoid0 scruts yes dflt,
                   compile_rows avoid0 scruts no dflt)
      else if is_pair p0 && is_pair s &&
              not (!cake_match_tuple_case &&
                   exists (fun t -> not (is_var t)) (pm_tuple_comps s)) then
        (* an explicit tuple scrutinee: split the column without pair_CASE *)
        let a,b = dest_pair s in
        let rows' = map (fun r' ->
            let p = el i r'.pm_pats in
            if is_pair p then
              let pa,pb = dest_pair p in
              {r' with pm_pats = replace_col r'.pm_pats i [pa;pb]}
            else
              let w1 = mk_var("_",type_of a) and w2 = mk_var("_",type_of b) in
              let rhs_ = if is_wildcard p then r'.pm_rhs
                         else vsubst [s,p] r'.pm_rhs in
              let g = match r'.pm_guard with
                  None -> None
                | Some g -> Some(if is_wildcard p then g else vsubst [s,p] g) in
              {pm_pats = replace_col r'.pm_pats i [w1;w2];
               pm_guard = g; pm_rhs = rhs_}) rows in
        compile_rows avoid0 (replace_col scruts i [a;b]) rows' dflt
      else
        let ci,cons = pm_constructors (type_of s) in
        let branch (cvs,cpat) =
          let avoid = ref avoid0 in
          let chead = pat_head cpat in
          (* preferred names: from the first row with this constructor *)
          let pref = try let r1 = find (fun r' ->
                                          pat_head (el i r'.pm_pats) = chead &&
                                          not (is_var (el i r'.pm_pats))) rows in
                         let p = el i r1.pm_pats in
                         let args = if is_numeral p then [] else snd(strip_comb p) in
                         map2 (fun a cv -> if is_var a && not (is_wildcard a)
                                           then a else cv) args cvs
                     with Failure _ -> cvs in
          let pref = if length pref = length cvs then pref else cvs in
          let xs = map2 (fun v p -> pm_fresh avoid (mk_var(pm_base_name p,
                                                            type_of v)))
                        cvs pref in
          let cval = vsubst (zip xs cvs) cpat in
          let rows_c = mapfilter (fun r' ->
              let p = el i r'.pm_pats in
              if is_var p then
                let ws = map (fun x -> mk_var("_",type_of x)) xs in
                let sub t = if is_wildcard p then t else vsubst [cval,p] t in
                {pm_pats = replace_col r'.pm_pats i ws;
                 pm_guard = (match r'.pm_guard with None -> None
                                                  | Some g -> Some(sub g));
                 pm_rhs = sub r'.pm_rhs}
              else if pat_head p = chead &&
                      (not (is_numeral p) || p = cpat) then
                let args = if is_numeral p then [] else snd(strip_comb p) in
                {r' with pm_pats = replace_col r'.pm_pats i args}
              else failwith "") rows in
          let body = compile_rows (!avoid) (replace_col scruts i xs) rows_c dflt in
          list_mk_abs(xs,body) in
        let branches = map branch cons in
        let rty = type_of dflt in
        let c = ci.ci_case in
        let c' = inst (type_match (type_of c)
                         (itlist (mk_fun_ty o type_of) (s::branches) rty) []) c in
        list_mk_comb(c',s::branches);;

let compile_match_term tm =
  let e,arms = dest_match_term tm in
  let counter = ref 0 in
  let arms = map (fun (p,g,r) ->
      let vs = filter (fun v -> not (is_wildcard v)) (frees p) in
      let ren = map (fun v -> incr counter;
                      mk_var(fst(dest_var v)^"%pm"^string_of_int !counter,
                             type_of v),v) vs in
      vsubst ren p,
      (match g with None -> None | Some g -> Some(vsubst ren g)),
      vsubst ren r) arms in
  let avoid = frees tm @ flat (map (fun (p,_,_) -> frees p) arms) in
  let rows = map (fun (p,g,r) ->
      (* check linearity: a named variable may occur once *)
      let vs = filter (fun v -> not (is_wildcard v)) (frees p) in
      let rec count v t = match t with
          Comb(f,x) -> count v f + count v x
        | Var _ -> if t = v then 1 else 0
        | _ -> 0 in
      if exists (fun v -> count v p > 1) vs
      then failwith "compile_match_term: a variable occurs twice in a pattern"
      else {pm_pats = [p]; pm_guard = g; pm_rhs = r}) arms in
  let rty = type_of(let _,_,r = hd arms in r) in
  let dflt = mk_const("ARB",[rty,aty]) in
  compile_rows avoid [e] rows dflt;;

(* HOL Light's paired lets (let (x,y) = e in t, a LET of a GABS) become      *)
(* pair_CASE e (\x y. t), the kit's form, with nested tuples nested.  Paired *)
(* lambdas \(x,y). t elsewhere stay as they are (write \p. match p with     *)
(* (x,y) -> t to get pair_CASE)                                              *)

let mk_pair_case_term e f =
  let c0 = mk_const("pair_CASE",[]) in
  let rty = snd(dest_fun_ty(snd(dest_fun_ty(type_of f)))) in
  let cty = mk_fun_ty (type_of e) (mk_fun_ty (type_of f) rty) in
  mk_comb(mk_comb(inst (type_match (type_of c0) cty []) c0,e),f);;

let elim_gabs tm0 =
  let avoid = ref (variables tm0) in
  let fresh ty = pm_fresh avoid (mk_var("p",ty)) in
  (* a term equal to (\pat. body) e, for a tuple pattern pat *)
  let rec pc e pat body =
    if is_var pat then vsubst [e,pat] body else
    let p1,p2 = dest_pair pat in
    let a = if is_var p1 then p1 else fresh (type_of p1) in
    let b = if is_var p2 then p2 else fresh (type_of p2) in
    let body2 = if is_var p2 then body else pc b p2 body in
    let body1 = if is_var p1 then body2 else pc a p1 body2 in
    mk_pair_case_term e (mk_abs(a,mk_abs(b,body1))) in
  let strip_let_end t =
    try if fst(dest_const(rator t)) = "LET_END" then rand t else t
    with Failure _ -> t in
  let rec tuple_vars p =
    is_var p || (is_pair p && tuple_vars (fst(dest_pair p)) &&
                 tuple_vars (snd(dest_pair p))) in
  let tuple_pat p = is_pair p && tuple_vars p in
  let rec go tm =
    match tm with
      Comb(Comb(Const("LET",_),g),e) when is_gabs g &&
                                          tuple_pat (fst(dest_gabs g)) ->
        let pat,body = dest_gabs g in
        pc (go e) pat (go (strip_let_end body))
    | Comb(f,x) -> mk_comb(go f,go x)
    | Abs(v,b) -> mk_abs(v,go b)
    | _ -> tm in
  go tm0;;

(* every match of a term, innermost first *)

let rec cases_of_matches_rec tm =
  match tm with
    Comb(f,x) ->
      let tm' = mk_comb(cases_of_matches_rec f,cases_of_matches_rec x) in
      if is_match_term tm' then cases_of_matches_rec (compile_match_term tm')
      else tm'
  | Abs(v,b) -> mk_abs(v,cases_of_matches_rec b)
  | _ -> tm;;

let cases_of_matches tm = cases_of_matches_rec (elim_gabs tm);;

let CASE_TERM tm = cases_of_matches tm;;

(* the q-tactics compile the matches of their strings (since 2026-11-22),    *)
(* and so does g (HOL Light's g sets the goal as parsed)                     *)
kit_q_compile_matches := cases_of_matches;;

(* Replaces HOL Light's g: a goal written with match gets the kit's case     *)
(* constants, as the clauses of cake_def and the strings of the q-tactics   *)
let g tm = g (if kit_has_match tm then cases_of_matches tm else tm);;

(* ------------------------------------------------------------------------- *)
(* HOL4 oneline (DefnBase.one_line_ify): the clauses of a definition by      *)
(* patterns, |- f p11 .. p1n = e1 /\ .. /\ f pk1 .. pkn = ek (constructor    *)
(* patterns, as cake_def stores them), as one equation                       *)
(*   |- !v1 .. vn. f v1 .. vn = case .. (the patterns of the columns that    *)
(*   have one compiled into case constants, first match wins)                *)
(* proved by splitting the case tree and rewriting with the clauses.  As in  *)
(* HOL4 the arguments split on are named v, v' ..; the others keep the      *)
(* names of the first clause.  A clause with only variables is returned as  *)
(* it is.  Since 2026-11-20.                                                 *)
(* ------------------------------------------------------------------------- *)

let ONELINE_TAC (th:thm) : tactic =
  (* a variable of type :1 is one (a clause with the pattern one): before  *)
  (* the clauses are tried, it is replaced by one                          *)
  let unit_ty = type_of kit_one_tm in
  let ones : tactic = fun (asl,w as g) ->
    match filter (fun v -> type_of v = unit_ty) (frees w) with
      [] -> ALL_TAC g
    | vs -> MAP_EVERY (fun v -> SUBST1_TAC (SPEC v one)) vs g in
  let rec go g =
    ((ones THEN REWRITE_TAC[th] THEN CAKE_REWRITE_TAC[] THEN NO_TAC) ORELSE
     (TOP_CASE_TAC THEN go)) g in
  REPEAT GEN_TAC THEN go;;

let ONELINE (th:thm) : thm =
  let conjs = CONJUNCTS (SPEC_ALL th) in
  let rows = map (fun c -> let l,r = dest_eq (snd (strip_forall (concl c))) in
                           let f,args = strip_comb l in f,args,r,c) conjs in
  let f,args1,_,_ = hd rows in
  if not (forall (fun (g,a,_,_) -> g = f && length a = length args1) rows)
  then failwith "ONELINE: clauses of more than one function" else
  match (try Some (find (fun (_,a,_,_) -> forall is_var a) rows) with Failure _ -> None) with
    Some (_,_,_,c) -> GEN_ALL c
  | None ->
  let n = length args1 in
  let patcols = filter (fun i -> exists (fun (_,a,_,_) -> not (is_var (el i a))) rows)
                       (0--(n-1)) in
  let patfvs = itlist (fun (_,a,_,_) acc ->
                         union (freesl (map (fun i -> el i a) patcols)) acc) rows [] in
  let avoid = ref patfvs in
  let actual = map (fun i -> let a = el i args1 in
                       if mem i patcols then pm_fresh avoid (mk_var("v",type_of a))
                       else pm_fresh avoid a) (0--(n-1)) in
  let counter = ref 0 in
  let pmrows = map (fun (_,a,r,_) ->
      let theta = mapfilter (fun i -> if mem i patcols then fail() else el i actual,el i a)
                            (0--(n-1)) in
      let pats = map (fun i -> el i a) patcols in
      let vs = filter (fun v -> not (is_wildcard v)) (freesl pats) in
      let ren = map (fun v -> incr counter;
                       mk_var(fst(dest_var v)^"%pm"^string_of_int !counter,type_of v),v) vs in
      {pm_pats = map (vsubst ren) pats; pm_guard = None;
       pm_rhs = vsubst ren (vsubst theta r)}) rows in
  let rty = type_of (let _,_,r,_ = hd rows in r) in
  let dflt = mk_const("ARB",[rty,aty]) in
  let scruts = map (fun i -> el i actual) patcols in
  (* the binders of the branches avoid the arguments only (the pattern     *)
  (* variables were renamed apart, so their own names are free to reuse)   *)
  let body = compile_rows actual scruts pmrows dflt in
  let goal = list_mk_forall(actual,mk_eq(list_mk_comb(f,actual),body)) in
  prove(goal,ONELINE_TAC th);;
