(* ========================================================================= *)
(* CakeML kit: datatypes with case constants.                                *)
(*                                                                           *)
(* HOL4 writes   case x of C1 a => e1 | C2 b c => e2   for the constant      *)
(* ty_CASE x (\a. e1) (\b c. e2), with rewrite equations                     *)
(*   ty_CASE (C1 a) f1 f2 = f1 a    ty_CASE (C2 b c) f1 f2 = f2 b c.         *)
(* The port does the same: every datatype gets such a case constant, so a   *)
(* case split is a cases theorem plus rewriting (never MATCH_CONV).  Nested  *)
(* patterns are nested case constants.  For each type the kit also proves    *)
(*   ty_case_eq    (ty_CASE x f1 .. fn = v) <=> (?a. x = C1 a /\ f1 a = v)   *)
(*                                              \/ ...                       *)
(*   ty_case_match ty_CASE x f1 .. fn = match x with C1 a -> f1 a | ...      *)
(* (the second is used internally by the definition package).               *)
(* ========================================================================= *)

type case_info =
  { ci_tyname : string;          (* HOL Light type name *)
    ci_case : term;              (* the case constant, generic type *)
    ci_def : thm;                (* the defining equations *)
    ci_pats : (term list * term) list;  (* pattern variables, pattern *)
    ci_nchotomy : thm;           (* !x. x = C1 \/ (?a. x = C2 a) \/ ... *)
    ci_case_eq : thm;
    ci_match : thm option ref;    (* computed on first use *)
    ci_distinct : thm list;      (* both orientations *)
    ci_inject : thm list };;

let the_case_infos = ref ([] : (string * case_info) list);;

let case_info_of_tyname s = assoc s (!the_case_infos);;

let case_info_of_const c =
  let n = fst(dest_const c) in
  snd(find (fun (_,ci) -> fst(dest_const ci.ci_case) = n) (!the_case_infos));;

let is_case_const tm =
  is_const tm &&
  let n = fst(dest_const tm) in
  exists (fun (_,ci) -> fst(dest_const ci.ci_case) = n) (!the_case_infos);;

(* a fully applied case expression: CASE x f1 .. fn *)

let is_case_app tm =
  let h,args = strip_comb tm in
  is_case_const h &&
  length args = 1 + length (case_info_of_const h).ci_pats;;

let dest_case_app tm =
  let h,args = strip_comb tm in
  if not (is_case_app tm) then failwith "dest_case_app" else
  h,hd args,tl args;;

(* ------------------------------------------------------------------------- *)
(* Helpers.                                                                  *)
(* ------------------------------------------------------------------------- *)

let fresh_tyvar avoid =
  let names = map dest_vartype avoid in
  let rec pick l = match l with
      [] -> failwith "fresh_tyvar"
    | n::t -> if mem n names then pick t else mk_vartype n in
  pick ["R"; "R1"; "R2"; "Z"; "Z1"; "Z2"; "Q"; "Q1"];;

let sym_neg th =
  GEN_ALL(CONV_RULE (RAND_CONV SYM_CONV) (SPEC_ALL th));;

let tyname_of_type ty = fst(dest_type ty);;

(* the patterns of a type, from its cases theorem *)

let patterns_of_nchotomy nch =
  let x,bod = dest_forall(concl nch) in
  map (fun d -> let vs,eq = strip_exists d in vs,rand eq) (disjuncts bod);;

(* ------------------------------------------------------------------------- *)
(* Building match terms (used for the ty_case_match theorems).              *)
(* ------------------------------------------------------------------------- *)

let mk_match_term =
  fun x arms ->
    let rty = let (_,_,r) = hd arms in type_of r in
    let xty = type_of x in
    let geq_x = mk_const("GEQ",[xty,aty])
    and geq_r = mk_const("GEQ",[rty,aty]) in
    let ung = `_UNGUARDED_PATTERN` in
    let mk_arm (vs,pat,rhs) =
      let y = mk_var("y_pm",xty) and z = mk_var("z_pm",rty) in
      let body = mk_comb(mk_comb(ung,mk_comb(mk_comb(geq_x,pat),y)),
                         mk_comb(mk_comb(geq_r,rhs),z)) in
      mk_abs(y,mk_abs(z,list_mk_exists(vs,body))) in
    let arms' = map mk_arm arms in
    let armty = type_of(hd arms') in
    let seq = mk_const("_SEQPATTERN",[xty,aty; rty,bty]) in
    let rec chain l = match l with
        [a] -> a
      | a::t -> mk_comb(mk_comb(seq,a),chain t)
      | [] -> failwith "mk_match_term" in
    ignore armty;
    mk_comb(mk_comb(mk_const("_MATCH",[xty,aty; rty,bty]),x),chain arms');;

(* In the proof of ty_case_eq, after the case split, the goal is a
   disjunction one of whose disjuncts is ?bs. C as = C bs /\ f bs = v
   (or C = C /\ f = v): pick it and instantiate it with as. *)

let CASE_EQ_PICK_TAC (asl,w as gl) =
  let ds = disjuncts w in
  let n = length ds in
  let same_head d =
    let _,bod = strip_exists d in
    let eq = fst(dest_conj bod) in
    let l,r = dest_eq eq in
    fst(strip_comb l) = fst(strip_comb r) in
  let k = index true (map same_head ds) in
  let d = el k ds in
  let vs,bod = strip_exists d in
  let l,_ = dest_eq(fst(dest_conj bod)) in
  let args = snd(strip_comb l) in
  let args = if length args = length vs then args
             else (* a pair pattern x,y or a numeral: match it *)
               let pat = rand(fst(dest_conj bod)) in
               let _,tmi,_ = term_match [] pat l in
               map (fun v -> rev_assoc v tmi) vs in
  let select = funpow k (fun t -> DISJ2_TAC THEN t)
                        (if k < n - 1 then DISJ1_TAC else ALL_TAC) in
  (select THEN MAP_EVERY EXISTS_TAC args THEN ASM_REWRITE_TAC[]) gl;;

(* the match theorem of a case constant, proved on first use *)

let case_match_thm ci =
  match !(ci.ci_match) with
    Some th -> th
  | None ->
      let c = ci.ci_case in
      let ty = hd(snd(dest_type(type_of c))) in
      let rty = funpow (length ci.ci_pats + 1)
                  (fun t -> hd(tl(snd(dest_type t)))) (type_of c) in
      let fs = map2 (fun (vs,_) i ->
                       mk_var("f"^string_of_int i,
                              itlist (mk_fun_ty o type_of) vs rty))
                    ci.ci_pats (1--length ci.ci_pats) in
      let x = mk_var("x",ty) in
      let arms = map2 (fun (vs,pat) f -> vs,pat,list_mk_comb(f,vs))
                      ci.ci_pats fs in
      let mtm = list_mk_forall(x::fs,
                  mk_eq(list_mk_comb(c,x::fs),mk_match_term x arms)) in
      let th = prove(mtm,
        GEN_TAC THEN REPEAT GEN_TAC THEN
        STRUCT_CASES_TAC (SPEC x ci.ci_nchotomy) THEN
        REWRITE_TAC[ci.ci_def] THEN CONV_TAC(TOP_DEPTH_CONV MATCH_CONV) THEN
        REWRITE_TAC[]) in
      ci.ci_match := Some th; th;;

(* ------------------------------------------------------------------------- *)
(* Defining the case constant of an existing inductive type.                 *)
(* ------------------------------------------------------------------------- *)

(* for a nested type, cases/distinctness/injectivity also return the
   theorems of the auxiliary types; keep only those about tyname *)

let about_type tyname th =
  let tm = snd(strip_forall(concl th)) in
  let eq = if is_neg tm then dest_neg tm
           else if is_eq tm && is_eq(lhs tm) then lhs tm
           else if is_eq tm then tm else fst(dest_forall tm) in
  try tyname_of_type(type_of(lhs eq)) = tyname with Failure _ -> false;;

let define_case_constant tyname casename =
  let nch =
    let th = cases tyname in
    find (fun c -> tyname_of_type(type_of(fst(dest_forall(concl c)))) = tyname)
         (CONJUNCTS th) in
  let _,_,rth = assoc tyname (!inductive_type_store) in
  let pats = patterns_of_nchotomy nch in
  let ty = type_of(fst(dest_forall(concl nch))) in
  let r = fresh_tyvar (tyvars ty) in
  let fs = map2 (fun (vs,_) i ->
                   mk_var("f"^string_of_int i,
                          itlist (mk_fun_ty o type_of) vs r))
                pats (1--length pats) in
  let cty = itlist (mk_fun_ty o type_of) fs r in
  let cv = mk_var(casename,mk_fun_ty ty cty) in
  let clause (vs,pat) f =
    list_mk_forall(vs @ fs,
      mk_eq(list_mk_comb(cv,pat::fs),list_mk_comb(f,vs))) in
  let def = new_recursive_definition rth
              (list_mk_conj(map2 clause pats fs)) in
  let c = fst(strip_comb(lhs(snd(strip_forall(hd(conjuncts(concl def))))))) in
  let distinct =
    try let th = distinctness tyname in
        let ths = filter (about_type tyname) (CONJUNCTS th) in
        ths @ map sym_neg ths
    with Failure _ -> [] in
  let inject =
    try filter (about_type tyname) (CONJUNCTS(injectivity tyname))
    with Failure _ -> [] in
  let x = mk_var("x",ty) and v = mk_var("v",r) in
  let ceq =
    let lhs = mk_eq(list_mk_comb(c,x::fs),v) in
    let rhs = list_mk_disj
      (map2 (fun (vs,pat) f ->
               list_mk_exists(vs,mk_conj(mk_eq(x,pat),
                                         mk_eq(list_mk_comb(f,vs),v))))
            pats fs) in
    list_mk_forall(x::(fs @ [v]),mk_eq(lhs,rhs)) in
  let case_eq = prove(ceq,
    GEN_TAC THEN REPEAT GEN_TAC THEN EQ_TAC THENL
     [STRUCT_CASES_TAC (SPEC x nch) THEN
      GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [def] THEN DISCH_TAC THEN
      CASE_EQ_PICK_TAC;
      DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN
        (REPEAT_TCL CHOOSE_THEN (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC))) THEN
      REWRITE_TAC[def] THEN ASM_REWRITE_TAC[]]) in
  let mth = ref None in
  let ci = { ci_tyname = tyname; ci_case = c; ci_def = def; ci_pats = pats;
             ci_nchotomy = nch; ci_case_eq = case_eq; ci_match = mth;
             ci_distinct = distinct; ci_inject = inject } in
  the_case_infos := (tyname,ci) :: (!the_case_infos);
  ci;;

(* constructors: the heads of the patterns of every registered type *)

let is_constructor_app tm =
  is_numeral tm ||
  let h = fst(strip_comb tm) in
  is_const h &&
  let n = fst(dest_const h) in
  exists (fun (_,ci) ->
            exists (fun (_,p) -> let h' = fst(strip_comb p) in
                                 is_const h' && fst(dest_const h') = n)
                   ci.ci_pats)
         (!the_case_infos);;

(* ------------------------------------------------------------------------- *)
(* Size functions (HOL4's ty_size): for a constructor with arguments,       *)
(* 1 + the sizes of the arguments; 0 for a constructor without; a number is *)
(* its own size; type variables get size parameters (size functions come   *)
(* first: ty_size f_A f_B x); bool, char, int, words, functions count 0.    *)
(* An auxiliary type of a nested definition (e.g. exp list inside exp) gets *)
(* its own function TY_size_auxN; ty_size_aux_eqs relates it to list_size  *)
(* etc. where that is proved.                                               *)
(* ------------------------------------------------------------------------- *)

let list_size = new_recursive_definition list_RECURSION
  `(list_size (f:A->num) [] = 0) /\
   (list_size f (CONS h t) = 1 + f h + list_size f t)`;;

let option_size = new_recursive_definition option_RECURSION
  `(option_size (f:A->num) NONE = 0) /\
   (option_size f (SOME x) = 1 + f x)`;;

(* HOL4's pair_size counts the pair constructor (1 +), as HOL4's generated  *)
(* size functions do for a component of product type; min_pair_size does   *)
(* not                                                                       *)

let pair_size = new_definition
  `pair_size (f:A->num) (g:B->num) p = 1 + f (FST p) + g (SND p)`;;

let pair_size_THM = prove
 (`!(f:A->num) (g:B->num) a b. pair_size f g (a,b) = 1 + f a + g b`,
  REWRITE_TAC[pair_size]);;

let min_pair_size = new_definition
  `min_pair_size (f:A->num) (g:B->num) p = f (FST p) + g (SND p)`;;

let min_pair_size_THM = prove
 (`!(f:A->num) (g:B->num) a b. min_pair_size f g (a,b) = f a + g b`,
  REWRITE_TAC[min_pair_size]);;

let sum_size = new_recursive_definition sum_RECURSION
  `(sum_size (f:A->num) (g:B->num) (INL a) = f a) /\
   (sum_size f g (INR b) = g b)`;;

(* type name -> (size constant, its type variables in parameter order) *)

let the_size_fns = ref
  [ "list",(`list_size:(A->num)->A list->num`,[`:A`]);
    "option",(`option_size:(A->num)->A option->num`,[`:A`]);
    "prod",(`pair_size:(A->num)->(B->num)->A#B->num`,[`:A`;`:B`]);
    "sum",(`sum_size:(A->num)->(B->num)->A+B->num`,[`:A`;`:B`]) ];;

let the_size_defs = ref [list_size; option_size; pair_size_THM; sum_size];;

let the_size_aux_eqs = ref ([] : (string * thm list) list);;

let size_aux_eqs tyname = assoc tyname (!the_size_aux_eqs);;

let zero_size ty = mk_abs(mk_var("x",ty),`0:num`);;

let rec size_of_type (tvsizes:(hol_type*term) list) ty =
  if is_vartype ty then
    (try assoc ty tvsizes with Failure _ -> zero_size ty)
  else
    let n,args = dest_type ty in
    if n = "num" then mk_abs(mk_var("x",ty),mk_var("x",ty))
    else
      try let c,tvs = assoc n (!the_size_fns) in
          let k = length tvs in
          let dom = fst(dest_fun_ty(funpow k (fun t -> snd(dest_fun_ty t))
                                           (type_of c))) in
          let tyi = type_match dom ty [] in
          list_mk_comb(inst tyi c,
                       map (fun tv -> size_of_type tvsizes (type_subst tyi tv))
                           tvs)
      with Failure _ -> zero_size ty;;

let define_size_functions (names:string list) =
  let main = hd names in
  let _,_,rth = assoc main (!inductive_type_store) in
  let fvs,bod = strip_forall(concl rth) in
  let fns,cls = strip_exists bod in
  let clauses = conjuncts cls in
  let dom fn = fst(dest_fun_ty(type_of fn)) in
  let mainty = dom (find (fun fn -> fst(dest_type(dom fn)) = main) fns) in
  let tvs = tyvars mainty in
  let params = map (fun tv -> mk_var("f_"^dest_vartype tv,mk_fun_ty tv `:num`))
                   tvs in
  let tvsizes = zip tvs params in
  let naux = ref 0 in
  let fname fn =
    let n = fst(dest_type(dom fn)) in
    if mem n names then n^"_size"
    else (incr naux; main^"_size_aux"^string_of_int !naux) in
  let fnames = map fname fns in
  let svars = map2 (fun fn nm ->
                      mk_var(nm,itlist (mk_fun_ty o type_of) params
                                         (mk_fun_ty (dom fn) `:num`)))
                   fns fnames in
  let sz_of fn = list_mk_comb(assoc fn (zip fns svars),params) in
  let one_clause cl =
    let vs,eq = strip_forall cl in
    let l = lhs eq in
    let fn,pat = dest_comb l in
    let _,args = strip_comb pat in
    let args = if is_pair pat then [fst(dest_pair pat);snd(dest_pair pat)]
               else args in
    let comp a =
      let ty = type_of a in
      try let fn' = find (fun f -> dom f = ty) fns in mk_comb(sz_of fn',a)
      with Failure _ ->
        let t = mk_comb(size_of_type tvsizes ty,a) in
        try rhs(concl(BETA_CONV t)) with Failure _ -> t in
    (* a pair counts 1, as HOL4's pair_size does *)
    let r = if args = [] then `0:num`
            else list_mk_binop `(+):num->num->num` (`1` :: map comp args) in
    list_mk_forall(vs @ params,mk_eq(mk_comb(sz_of fn,pat),r)) in
  let def = new_recursive_definition rth (list_mk_conj(map one_clause clauses)) in
  let consts = map (fun v -> mk_const(fst(dest_var v),[])) svars in
  List.iter2 (fun nm c ->
      let base = String.sub nm 0 (String.length nm - 5) in
      if mem base names then
        the_size_fns := (base,(c,tvs)) :: !the_size_fns) fnames consts;
  the_size_defs := def :: !the_size_defs;
  (* the auxiliary functions as list_size / option_size / pair_size forms *)
  let cmap = zip svars consts in
  let csz fn = list_mk_comb(inst (type_match (type_of(assoc (assoc fn (zip fns svars)) cmap))
                                              (type_of(assoc fn (zip fns svars))) [])
                                 (assoc (assoc fn (zip fns svars)) cmap),params) in
  let aux_eq fn =
    let d = dom fn in
    let k,targs = dest_type d in
    if mem k names || not (mem k ["list";"option";"prod"]) then failwith "" else
    let arg_size ty =
      try csz (find (fun f -> dom f = ty) fns)
      with Failure _ -> size_of_type tvsizes ty in
    let gc,gtvs = assoc k (!the_size_fns) in
    let gdom = fst(dest_fun_ty(funpow (length gtvs)
                                 (fun t -> snd(dest_fun_ty t)) (type_of gc))) in
    let tyi = type_match gdom d [] in
    let rhs_ = list_mk_comb(inst tyi gc,map arg_size targs) in
    let lhs_ = csz fn in
    let x = mk_var("x",d) in
    let tm = list_mk_forall(params,mk_eq(lhs_,rhs_)) in
    prove(tm,
      REPEAT GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
      (if k = "list" then LIST_INDUCT_TAC
       else X_GEN_TAC x THEN
            STRUCT_CASES_TAC (ISPEC x (case_info_of_tyname
                                         (if k = "prod" then "prod" else k)).ci_nchotomy)) THEN
      ASM_REWRITE_TAC[def; list_size; option_size; pair_size_THM]) in
  let eqs = mapfilter aux_eq fns in
  if eqs <> [] then
    the_size_aux_eqs := (main,eqs) :: !the_size_aux_eqs;
  def;;

(* ------------------------------------------------------------------------- *)
(* New datatypes.  cake_type "spec" is define_type "spec" followed by the    *)
(* case constant of each new type; it returns define_type's pair.            *)
(* ------------------------------------------------------------------------- *)

let cake_last_types = ref ([] : string list);;

let cake_type s =
  let spec = parse_inductive_type_specification s in
  let names = map (fun (ty,_) -> try dest_vartype ty
                                 with Failure _ -> fst(dest_type ty)) spec in
  let res = define_type s in
  cake_last_types := names;
  do_list (fun n -> ignore(define_case_constant n (n^"_CASE"))) names;
  (try ignore(define_size_functions names)
   with Failure msg -> Format.print_string
     ("Warning: cake_type: no size functions for "^hd names^" ("^msg^")\n"));
  res;;

let type_size_def tyname =
  find (fun th -> exists (fun cl ->
          try let f = fst(strip_comb(lhs(snd(strip_forall cl)))) in
              fst(dest_const f) = tyname^"_size"
          with Failure _ -> false) (conjuncts(concl th)))
       (!the_size_defs);;

(* old name, kept for files written before the rename (prefer type_size_def: a   *)
(* theorem bound as size_def would shadow it)                                  *)
let size_def = type_size_def;;

(* the theorems of a case constant, by type name *)

let case_def tyname = (case_info_of_tyname tyname).ci_def;;
let case_eq tyname = (case_info_of_tyname tyname).ci_case_eq;;

(* every case equation, distinctness and injectivity theorem known *)

let all_case_rewrites () =
  itlist (fun (_,ci) l -> ci.ci_def :: ci.ci_distinct @ ci.ci_inject @ l)
         (!the_case_infos) [];;

(* HOL4's bool_case_eq: the case_eq of a conditional *)

let COND_CASE_EQ = prove
 (`!b (x:A) y v. (if b then x else y) = v <=> b /\ x = v \/ ~b /\ y = v`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[]);;

let all_case_eqs () =
  COND_CASE_EQ :: map (fun (_,ci) -> ci.ci_case_eq) (!the_case_infos);;

(* ------------------------------------------------------------------------- *)
(* The types HOL Light already has.  HOL4's names: pair_CASE, list_CASE,     *)
(* option_CASE, sum_CASE, num_CASE.                                          *)
(* ------------------------------------------------------------------------- *)

let list_case_info = define_case_constant "list" "list_CASE";;
let option_case_info = define_case_constant "option" "option_CASE";;
let sum_case_info = define_case_constant "sum" "sum_CASE";;
let num_case_info = define_case_constant "num" "num_CASE";;
let pair_case_info = define_case_constant "prod" "pair_CASE";;

let list_CASE = list_case_info.ci_def;;
let option_CASE = option_case_info.ci_def;;
let sum_CASE = sum_case_info.ci_def;;
let num_CASE = num_case_info.ci_def;;
let pair_CASE = pair_case_info.ci_def;;
let list_case_eq = list_case_info.ci_case_eq;;
let option_case_eq = option_case_info.ci_case_eq;;
let sum_case_eq = sum_case_info.ci_case_eq;;
let num_case_eq = num_case_info.ci_case_eq;;
let pair_case_eq = pair_case_info.ci_case_eq;;
