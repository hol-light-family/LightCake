(* ========================================================================= *)
(* CakeML kit: independent wildcards in quotations, and a faster typechecker *)
(* for parse_term.                                                           *)
(*                                                                           *)
(* HOL Light reads every _ of a quotation as the same variable "_": the two  *)
(* wildcards of CONS _ (CONS _ t), or the wildcards of two clauses of a      *)
(* definition, are one variable with one type.  HOL4 reads each _ as a new   *)
(* variable.  The parse_term below (which the quotation expander calls)      *)
(* gives each _ token its own name _%wN before parsing, so wildcards are     *)
(* independent variables of independent types.  is_wildcard (pmatch.ml)     *)
(* recognises these names; the definition package and the match compiler   *)
(* never let them reach a theorem.                                           *)
(* ========================================================================= *)

let cake_wild_counter = ref 0;;

(* the lexer glues _ to symbol characters after it (_:num lexes as the     *)
(* identifier "_:" followed by num); such a token is split, so (_:num) is  *)
(* a wildcard of type num                                                   *)

let cake_wild_tokens t =
  let fresh() = incr cake_wild_counter;
                Ident("_%w" ^ string_of_int !cake_wild_counter) in
  match t with
    Ident "_" -> [fresh()]
  | Ident s when String.length s > 1 && String.sub s 0 1 = "_" &&
                 forall issymb (tl(explode s)) ->
      fresh() :: lex(tl(explode s))
  | _ -> [t];;

(* ------------------------------------------------------------------------- *)
(* Tables of the parser state.  HOL Light's typechecker (retypecheck in      *)
(* preterm.ml) tests every identifier of a quotation with get_const_type, a *)
(* search of the kernel's list of constants (thousands of them here, so     *)
(* about 1 ms for a variable or an old constant), and filters the whole     *)
(* interface list for every identifier and constant.  The copy below looks  *)
(* them up in hash tables instead.  Each table mirrors one list of HOL      *)
(* Light's state and is brought up to date at the start of every parse, by *)
(* a physical-equality test of the list against the one it was built from  *)
(* (every change of these lists makes a new list): the constants (which     *)
(* only grow at the front, so only the new ones are added), the interface   *)
(* and the overload skeletons (rebuilt when they change).  Hidden constants *)
(* (is_hidden) and implicit types (the_implicit_types) are short lists and  *)
(* are read directly, as by HOL Light.                                       *)
(* ------------------------------------------------------------------------- *)

let cake_ptab_consts = (Hashtbl.create 20000 : (string,hol_type) Hashtbl.t)
and cake_ptab_consts_of = ref ([]:(string*hol_type)list)
and cake_ptab_iface =
  (Hashtbl.create 1000 : (string,(string*(string*hol_type))list) Hashtbl.t)
and cake_ptab_iface_of = ref ([]:(string*(string*hol_type))list)
and cake_ptab_skels = (Hashtbl.create 100 : (string,hol_type) Hashtbl.t)
and cake_ptab_skels_of = ref ([]:(string*hol_type)list)
and cake_ptab_rebuilds = Array.make 4 0;;

let cake_ptab_sync () =
  let cl = constants() in
  (if not (cl == !cake_ptab_consts_of) then
     let old = !cake_ptab_consts_of in
     let rec news l acc =
       if l == old then Some acc else
       match l with [] -> None | h::t -> news t (h::acc) in
     (match news cl [] with
        Some l -> cake_ptab_rebuilds.(0) <- cake_ptab_rebuilds.(0) + 1;
                  List.iter (fun (c,ty) -> Hashtbl.replace cake_ptab_consts c ty) l
      | None -> cake_ptab_rebuilds.(1) <- cake_ptab_rebuilds.(1) + 1;
                Hashtbl.reset cake_ptab_consts;
                List.iter (fun (c,ty) -> Hashtbl.replace cake_ptab_consts c ty)
                  (List.rev cl));
     cake_ptab_consts_of := cl);
  let il = !the_interface in
  (if not (il == !cake_ptab_iface_of) then
     (cake_ptab_rebuilds.(2) <- cake_ptab_rebuilds.(2) + 1;
      Hashtbl.reset cake_ptab_iface;
      List.iter (fun ((s,_) as e) ->
          let l = try Hashtbl.find cake_ptab_iface s with Not_found -> [] in
          Hashtbl.replace cake_ptab_iface s (e::l)) (List.rev il);
      cake_ptab_iface_of := il));
  let sl = !the_overload_skeletons in
  if not (sl == !cake_ptab_skels_of) then
    (cake_ptab_rebuilds.(3) <- cake_ptab_rebuilds.(3) + 1;
     Hashtbl.reset cake_ptab_skels;
     List.iter (fun (s,ty) -> Hashtbl.replace cake_ptab_skels s ty) (List.rev sl);
     cake_ptab_skels_of := sl);;

(* get_const_type s, assoc s (!the_overload_skeletons), and the filter of   *)
(* the interface entries of s (in the order of the_interface); the failures *)
(* are those of assoc                                                       *)

let cake_ptab_const_type s =
  try Hashtbl.find cake_ptab_consts s with Not_found -> failwith "find";;

let cake_ptab_skeleton s =
  try Hashtbl.find cake_ptab_skels s with Not_found -> failwith "find";;

let cake_ptab_interface s =
  try Hashtbl.find cake_ptab_iface s with Not_found -> [];;

(* ------------------------------------------------------------------------- *)
(* HOL Light's counter of system type variables (Stv n), in preterm.ml, is   *)
(* not accessible, but it decides the names ?n of invented type variables   *)
(* and the numbers in some error messages.  So that the copy gives exactly  *)
(* the terms and failures of HOL Light's typechecker, every parse of the    *)
(* copy takes its numbers from HOL Light's counter: cake_hol_tyvar_probe () *)
(* typechecks a variable of a given type Stv(-1) with HOL Light's           *)
(* retypecheck (no lookups), which returns the number n HOL Light's counter *)
(* gives (and counts it); the copy then counts from n with its own counter, *)
(* and at the end cake_hol_tyvar_advance j makes HOL Light count the j      *)
(* numbers the copy used after n (a retypecheck of f x .. x, with f and x   *)
(* given types, uses one number for itself and one per application).  So   *)
(* HOL Light's counter is where its own parser would have left it.          *)
(* ------------------------------------------------------------------------- *)

let cake_hol_tyvar_probe =
  let venv = ["x",Stv(-1)] and ptm = Varp("x",dpty) in
  fun () -> match retypecheck venv ptm with
              Varp(_,Stv n) -> n
            | _ -> failwith "cake_hol_tyvar_probe";;

let cake_hol_tyvar_advance =
  let venv = ["f",Stv(-1); "x",Utv "A"] and x = Varp("x",dpty) in
  let rec chain m acc = if m <= 0 then acc else chain (m - 1) (Combp(acc,x)) in
  let rec advance j =
    if j > 0 then
      let c = min j 4096 in
      (ignore (retypecheck venv (chain (c - 1) (Varp("f",dpty)))); advance (j - c)) in
  advance;;

(* HOL Light 233b83c (#184, 2026) made a binder shadow a constant of the     *)
(* same name also inside a tuple or under a type annotation; 924faf0 and    *)
(* other earlier versions read such a name as the constant.  The copy does *)
(* what the running HOL Light does, found by typechecking \(T,y). y with    *)
(* HOL Light's own retypecheck.                                             *)

let cake_binders_shadow_constants =
  let old = !ignore_constant_varstruct in
  ignore_constant_varstruct := true;
  let ptm = Absp(Combp(Combp(Varp(",",dpty),Varp("T",dpty)),Varp("y",dpty)),
                 Varp("y",dpty)) in
  let r = try (match retypecheck [] ptm with
                 Absp(Combp(Combp(_,Varp("T",_)),_),_) -> Some true
               | Absp(Combp(Combp(_,Constp("T",_)),_),_) -> Some false
               | _ -> None)
          with Failure _ -> None in
  ignore_constant_varstruct := old;
  match r with
    Some b -> b
  | None -> failwith "kit/parse.ml: unknown behaviour of HOL Light's retypecheck";;

(* ------------------------------------------------------------------------- *)
(* Constants and types for term_of_preterm: HOL Light's                   *)
(* term_of_preterm builds every constant with mk_mconst, which looks the    *)
(* name up twice in the kernel's list of constants, and every type with     *)
(* mk_type, which looks the operator up in the list of types.  Here the     *)
(* generic constant of each name and the generic type of each operator are  *)
(* kept in tables (both lists only grow, and an entry never changes) and    *)
(* instantiated with the kernel's inst and type_subst, which give the same  *)
(* terms.                                                                    *)
(* ------------------------------------------------------------------------- *)

let cake_const_cache = (Hashtbl.create 20000 : (string,term) Hashtbl.t);;
let cake_tyop_cache = (Hashtbl.create 1000 : (string,hol_type * hol_type list) Hashtbl.t);;

let cake_mk_mconst (c,ty) =
  try let gc = try Hashtbl.find cake_const_cache c with Not_found ->
                 let gc = mk_const(c,[]) in Hashtbl.add cake_const_cache c gc; gc in
      let con = inst (type_match (type_of gc) ty []) gc in
      if type_of con = ty then con else fail()
  with Failure _ -> failwith "mk_const: generic type cannot be instantiated";;

let cake_mk_type (con,args) =
  let gty,vs =
    try Hashtbl.find cake_tyop_cache con with Not_found ->
      let n = try get_type_arity con with Failure _ ->
                failwith ("mk_type: type "^con^" has not been defined") in
      let vs = map (fun i -> mk_vartype ("?cake_tyarg" ^ string_of_int i)) (1--n) in
      let e = mk_type(con,vs),vs in Hashtbl.add cake_tyop_cache con e; e in
  if length args <> length vs then failwith ("mk_type: wrong number of arguments to "^con)
  else type_subst (zip args vs) gty;;

(* ------------------------------------------------------------------------- *)
(* A copy of HOL Light's typechecker and translation to terms: the section  *)
(* "Main pretype->type, preterm->term and retypechecking functions" of      *)
(* preterm.ml, HOL Light commit 9cb19cc (preterm.ml as of 233b83c; the same *)
(* in upstream master 6dbb775), with the Absp case of typify of 924faf0 as  *)
(* well (see cake_binders_shadow_constants).  The differences, each marked *)
(* KIT: the counter tyv_num is outside (cake_tyv_num, see above);          *)
(* pmk_cv, get_generic_type, resolve_interface and solve_preterm use the    *)
(* tables above instead of get_const_type, assoc and filter or find over    *)
(* the interface; type_of_pretype_base and term_of_preterm use              *)
(* cake_mk_type and cake_mk_mconst.  Keep it in step with preterm.ml: the   *)
(* check mode below (cake_parse_check) compares the two on every parse.     *)
(* ------------------------------------------------------------------------- *)

let cake_tyv_num = ref 0;;

let cake_type_of_pretype,cake_term_of_preterm,cake_retypecheck_raw =
  let tyv_num = cake_tyv_num in (* KIT *)
  let new_type_var() = let n = !tyv_num in (tyv_num := n + 1; Stv(n)) in

  let pmk_cv(s,pty) =
    if can cake_ptab_const_type s then Constp(s,pty) (* KIT *)
    else Varp(s,pty) in

  let pmk_numeral =
    let num_pty = Ptycon("num",[]) in
    let NUMERAL = Constp("NUMERAL",Ptycon("fun",[num_pty; num_pty]))
    and BIT0 = Constp("BIT0",Ptycon("fun",[num_pty; num_pty]))
    and BIT1 = Constp("BIT1",Ptycon("fun",[num_pty; num_pty]))
    and t_0 = Constp("_0",num_pty) in
    let rec pmk_numeral(n) =
      if n =/ num_0 then t_0 else
      let m = quo_num n (num_2) and b = mod_num n (num_2) in
      let op = if b =/ num_0 then BIT0 else BIT1 in
      Combp(op,pmk_numeral(m)) in
    fun n -> Combp(NUMERAL,pmk_numeral n) in

  (* ----------------------------------------------------------------------- *)
  (* Pretype substitution for a pretype resulting from translation of type.  *)
  (* ----------------------------------------------------------------------- *)

  let rec pretype_subst th ty =
    match ty with
      Ptycon(tycon,args) -> Ptycon(tycon,map (pretype_subst th) args)
    | Utv v -> rev_assocd ty th ty
    | _ -> failwith "pretype_subst: Unexpected form of pretype" in

  (* ----------------------------------------------------------------------- *)
  (* Convert type to pretype with new Stvs for all type variables.           *)
  (* ----------------------------------------------------------------------- *)

  let pretype_instance ty =
    let gty = pretype_of_type ty
    and tyvs = map pretype_of_type (tyvars ty) in
    let subs = map (fun tv -> new_type_var(),tv) tyvs in
    pretype_subst subs gty in

  (* ----------------------------------------------------------------------- *)
  (* Get a new instance of a constant's generic type modulo interface.       *)
  (* ----------------------------------------------------------------------- *)

  let get_generic_type cname =
    match cake_ptab_interface cname with (* KIT *)
      [_,(c,ty)] -> ty
    | _::_::_ -> cake_ptab_skeleton cname (* KIT *)
    | [] -> cake_ptab_const_type cname in (* KIT *)

  (* ----------------------------------------------------------------------- *)
  (* Get the implicit generic type of a variable.                            *)
  (* ----------------------------------------------------------------------- *)

  let get_var_type vname =
    assoc vname !the_implicit_types in

  (* ----------------------------------------------------------------------- *)
  (* Unravel unifications and apply them to a type.                          *)
  (* ----------------------------------------------------------------------- *)

  let rec solve env pty =
    match pty with
      Ptycon(f,args) -> Ptycon(f,map (solve env) args)
    | Stv(i) -> if defined env i then solve env (apply env i) else pty
    | _ -> pty in

  (* ----------------------------------------------------------------------- *)
  (* Functions for display of preterms and pretypes, by converting them      *)
  (* to terms and types then re-using standard printing functions.           *)
  (* ----------------------------------------------------------------------- *)

  let free_stvs =
    let rec free_stvs = function
    |Stv n -> [n]
    |Utv _ -> []
    |Ptycon(_,args) -> flat (map free_stvs args)
    in
    setify o free_stvs
  in

  let string_of_pretype stvs =
    let rec type_of_pretype' ns = function
      |Stv n -> mk_vartype (if mem n ns then "?" ^ string_of_int n else "_")
      |Utv v -> mk_vartype v
      |Ptycon(con,args) -> mk_type(con,map (type_of_pretype' ns) args)
    in
    string_of_type o type_of_pretype' stvs
  in

  let string_of_preterm =
    let rec untyped_t_of_pt = function
      |Varp(s,pty) -> mk_var(s,aty)
      |Constp(s,pty) -> mk_mconst(s,get_const_type s)
      |Combp(l,r) -> mk_comb(untyped_t_of_pt l,untyped_t_of_pt r)
      |Absp(v,bod) -> mk_gabs(untyped_t_of_pt v,untyped_t_of_pt bod)
      |Typing(ptm,pty) -> untyped_t_of_pt ptm
    in
    string_of_term o untyped_t_of_pt
  in

  let string_of_ty_error env = function
    |None ->
        "unify: types cannot be unified "
        ^ "(you should not see this message, please report)"
    |Some(t,ty1,ty2) ->
        let ty1 = solve env ty1 and ty2 = solve env ty2 in
        let sty1 = string_of_pretype (free_stvs ty2) ty1 in
        let sty2 = string_of_pretype (free_stvs ty1) ty2 in
        let default_msg s =
          " " ^ s ^ " cannot have type " ^ sty1 ^ " and " ^ sty2
          ^ " simultaneously"
        in
        match t with
        |Constp(s,_) ->
            " " ^ s ^ " has type " ^ string_of_type (get_const_type s) ^ ", "
            ^ "it cannot be used with type " ^ sty2
        |Varp(s,_) -> default_msg s
        |t -> default_msg (string_of_preterm t)
  in

  (* ----------------------------------------------------------------------- *)
  (* Unification of types                                                    *)
  (* ----------------------------------------------------------------------- *)

  let rec istrivial ptm env x = function
    |Stv y ->
        y = x || defined env y && istrivial ptm env x (apply env y)
    |Ptycon(f,args) when exists (istrivial ptm env x) args ->
        failwith (string_of_ty_error env ptm)
    |(Ptycon _ | Utv _) -> false
  in

  let unify ptm env ty1 ty2 =
    let rec unify env = function
    |[] -> env
    |(ty1,ty2,_)::oth when ty1 = ty2 -> unify env oth
    |(Ptycon(f,fargs),Ptycon(g,gargs),ptm)::oth ->
        if f = g && length fargs = length gargs
        then unify env (map2 (fun x y -> x,y,ptm) fargs gargs @ oth)
        else failwith (string_of_ty_error env ptm)
    |(Stv x,t,ptm)::oth ->
        if defined env x then unify env ((apply env x,t,ptm)::oth)
        else unify (if istrivial ptm env x t then env else (x|->t) env) oth
    |(t,Stv x,ptm)::oth -> unify env ((Stv x,t,ptm)::oth)
    |(_,_,ptm)::oth -> failwith (string_of_ty_error env ptm)
    in
    unify env [ty1,ty2,match ptm with None -> None | Some t -> Some(t,ty1,ty2)]
  in

  (* ----------------------------------------------------------------------- *)
  (* Names in a varstruct that "typify" would otherwise read as constants.   *)
  (* A binder may legitimately shadow a constant of that name, so these are  *)
  (* forced to be treated as bound variables when typing it (see Absp).      *)
  (* ----------------------------------------------------------------------- *)

  let rec varstruct_consts (ptm:preterm) : string list =
    match ptm with
    | Varp(s,_) ->                       (* same test as "typify" uses below *)
        if not(is_hidden s) && can get_generic_type s then [s] else []
    | Typing(t,_) -> varstruct_consts t  (* annotated binder "(c:ty)"        *)
    | Combp(Combp(Varp(",",_),l),r) ->   (* tuple varstruct "(c,y)"          *)
        union (varstruct_consts l) (varstruct_consts r)
    | _ -> [] in

  (* ----------------------------------------------------------------------- *)
  (* Attempt to attach a given type to a term, performing unifications.      *)
  (* Here "venv" maps the names of the bound variables in scope to their     *)
  (* pretypes, and "uenv" holds the unifications of system type variables    *)
  (* accumulated so far. The returned "venv" holds only the new bindings.    *)
  (* ----------------------------------------------------------------------- *)

  let rec typify (ty:pretype)
                 ((ptm:preterm),(venv:(string*pretype)list),
                  (uenv:(int,pretype)func)) =
    match ptm with
    |Varp(s,_) when can (assoc s) venv ->
        let ty' = assoc s venv in
        Varp(s,ty'),[],unify (Some ptm) uenv ty' ty
    |Varp(s,_) when can num_of_string s ->
        let t = pmk_numeral(num_of_string s) in
        let ty' = Ptycon("num",[]) in
        t,[],unify (Some ptm) uenv ty' ty
    |Varp(s,_) ->
        warn (s <> "" && isnum s) "Non-numeral begins with a digit";
          if not(is_hidden s) && can get_generic_type s then
            let pty = pretype_instance(get_generic_type s) in
            let ptm = Constp(s,pty) in
            ptm,[],unify (Some ptm) uenv pty ty
          else
            let ptm = Varp(s,ty) in
            if not(can get_var_type s) then ptm,[s,ty],uenv
            else
              let pty = pretype_instance(get_var_type s) in
              ptm,[s,ty],unify (Some ptm) uenv pty ty
    |Combp(f,x) ->
        let ty'' = new_type_var() in
        let ty' = Ptycon("fun",[ty'';ty]) in
        let f',venv1,uenv1 = typify ty' (f,venv,uenv) in
        let x',venv2,uenv2 = typify ty'' (x,venv1@venv,uenv1) in
        Combp(f',x'),(venv1@venv2),uenv2
    |Typing(tm,pty) -> typify ty (tm,venv,unify (Some tm) uenv ty pty)
    |Absp(v,bod) ->
        let ty',ty'' =
          match ty with
          |Ptycon("fun",[ty';ty'']) -> ty',ty''
          |_ -> new_type_var(),new_type_var()
        in
        let ty''' = Ptycon("fun",[ty';ty'']) in
        let uenv0 = unify (Some ptm) uenv ty''' ty in
        let v',venv1,uenv1 =
          if cake_binders_shadow_constants then (* KIT: 233b83c and later *)
          (* Pre-bind the constant-named binders, so that typing the         *)
          (* varstruct sees them as variables rather than constants.         *)
          let cseed:(string*pretype)list =
            if !ignore_constant_varstruct
            then map (fun s -> s,new_type_var()) (varstruct_consts v)
            else [] in
          let v',venv1,uenv1 = typify ty' (v,cseed,uenv0) in
          (* Re-add cseed: typify omits names already in its venv, but the   *)
          (* body below must still see them as bound variables.              *)
          v',cseed@venv1,uenv1
          else (* KIT: before 233b83c (924faf0) *)
          let v',venv1,uenv1 = typify ty' (v,[],uenv0) in
          match v' with
          |Constp(s,_) when !ignore_constant_varstruct ->
              Varp(s,ty'),[s,ty'],uenv0
          |_ -> v',venv1,uenv1
        in
        let bod',venv2,uenv2 = typify ty'' (bod,venv1@venv,uenv1) in
        Absp(v',bod'),venv2,uenv2
    |_ -> failwith "typify: unexpected constant at this stage"
  in

  (* ----------------------------------------------------------------------- *)
  (* Further specialize type constraints by resolving overloadings.          *)
  (* ----------------------------------------------------------------------- *)

  let rec resolve_interface ptm cont env =
    match ptm with
      Combp(f,x) -> resolve_interface f (resolve_interface x cont) env
    | Absp(v,bod) -> resolve_interface v (resolve_interface bod cont) env
    | Varp(_,_) -> cont env
    | Constp(s,ty) ->
          let maps = cake_ptab_interface s in (* KIT *)
          if maps = [] then cont env else
          tryfind (fun (_,(_,ty')) ->
            let ty' = pretype_instance ty' in
            cont(unify (Some ptm) env ty' ty)) maps
  in

  (* ----------------------------------------------------------------------- *)
  (* Hence apply throughout a preterm.                                       *)
  (* ----------------------------------------------------------------------- *)

  let rec solve_preterm env ptm =
    match ptm with
      Varp(s,ty) -> Varp(s,solve env ty)
    | Combp(f,x) -> Combp(solve_preterm env f,solve_preterm env x)
    | Absp(v,bod) -> Absp(solve_preterm env v,solve_preterm env bod)
    | Constp(s,ty) -> let tys = solve env ty in
          try let _,(c',_) = find
                (fun (s',(c',ty')) ->
                   s = s' && can (unify None env (pretype_instance ty')) ty)
                (cake_ptab_interface s) in (* KIT *)
              pmk_cv(c',tys)
          with Failure _ -> Constp(s,tys)
  in

  (* ----------------------------------------------------------------------- *)
  (* Pretype -> type conversion. The base function returns a flag if a       *)
  (* system type variable was translated to real type variable.              *)
  (* ----------------------------------------------------------------------- *)

  let rec type_of_pretype_base (ty:pretype): hol_type * bool =
    match ty with
      Stv n -> let s = "?"^(string_of_int n) in
               (mk_vartype(s), true)
    | Utv(v) -> (mk_vartype(v), false)
    | Ptycon(con,args) ->
      let args',translated = unzip (map type_of_pretype_base args) in
      let translated = List.fold_left (||) false translated in
      (cake_mk_type(con,args'), translated) in (* KIT *)

  let type_of_pretype (ty:pretype): hol_type =
    fst (type_of_pretype_base ty) in

  (* ----------------------------------------------------------------------- *)
  (* Maps preterms to terms.                                                 *)
  (* ----------------------------------------------------------------------- *)

  let term_of_preterm =
    let stvs_translated_terms:string list ref = ref [] in
    let rec term_of_preterm (ptm:preterm): term =
      match ptm with
        Varp(s,pty) ->
          let ty, translated = type_of_pretype_base pty in
          let v = mk_var(s,ty) in
          let _ =
            if translated && not (exists (fun s' -> s = s')
                             !stvs_translated_terms)
            then stvs_translated_terms := s::!stvs_translated_terms
            else () in v
      | Constp(s,pty) ->
          let ty, translated = type_of_pretype_base pty in
          let c = cake_mk_mconst(s,ty) in (* KIT *)
          let _ =
            if translated && not (exists (fun s' -> s = s')
                             !stvs_translated_terms)
            then stvs_translated_terms := s::!stvs_translated_terms
            else () in c
      | Combp(l,r) -> mk_comb(term_of_preterm l,term_of_preterm r)
      | Absp(v,bod) -> mk_gabs(term_of_preterm v,term_of_preterm bod)
      | Typing(ptm,pty) -> term_of_preterm ptm in
    let report_type_invention () =
      if !stvs_translated_terms <> [] then
        if !type_invention_error
        then failwith
            ("typechecking error (cannot infer type of variables): " ^
             String.concat ", " !stvs_translated_terms)
        else warn !type_invention_warning "inventing type variables" in
    fun ptm -> stvs_translated_terms := [];
               let tm = term_of_preterm ptm in
               report_type_invention (); tm in

  (* ----------------------------------------------------------------------- *)
  (* Overall typechecker: initial typecheck plus overload resolution pass.   *)
  (* ----------------------------------------------------------------------- *)

  let retypecheck venv ptm =
    let ty = new_type_var() in
    let ptm',_,env =
      try typify ty (ptm,venv,undefined)
      with Failure e -> failwith
       ("typechecking error (initial type assignment):" ^ e) in
    let env' =
      try resolve_interface ptm' (fun e -> e) env
      with Failure _ -> failwith "typechecking error (overload resolution)" in
    let ptm'' = solve_preterm env' ptm' in
    ptm'' in

  type_of_pretype,term_of_preterm,retypecheck;;

(* ------------------------------------------------------------------------- *)
(* cake_retypecheck venv ptm: HOL Light's retypecheck venv ptm, the same     *)
(* preterm or the same failure, with the tables brought up to date and the  *)
(* numbers taken from HOL Light's counter.                                  *)
(* ------------------------------------------------------------------------- *)

let cake_retypecheck venv ptm =
  cake_ptab_sync();
  let n = cake_hol_tyvar_probe() in
  cake_tyv_num := n;
  let r = try cake_retypecheck_raw venv ptm
          with e -> (cake_hol_tyvar_advance (!cake_tyv_num - n - 1); raise e) in
  cake_hol_tyvar_advance (!cake_tyv_num - n - 1); r;;

(* ------------------------------------------------------------------------- *)
(* Check mode (cake_parse_check := true): every parse is made both ways,     *)
(* with HOL Light's term_of_preterm o retypecheck venv and with the copy,   *)
(* from the same state (the copy's counter starts where HOL Light's did);   *)
(* the result (a term, or a failure with its message) must be the same,     *)
(* structurally; a difference is printed as a CAKEPARSEDIFF line; HOL       *)
(* Light's result is returned.  cake_parse_check_report () prints the       *)
(* number of parses, differences and the CPU time of each way.              *)
(* ------------------------------------------------------------------------- *)

let cake_parse_check = ref false;;
let cake_parse_check_stats = Array.make 4 0 and cake_parse_check_times = Array.make 2 0.0;;

let cake_parse_check_both (src:string) venv ptm =
  cake_ptab_sync();
  let n = cake_hol_tyvar_probe() in
  let t0 = Sys.time() in
  let r1 = try Ok (term_of_preterm (retypecheck venv ptm)) with e -> Error e in
  let t1 = Sys.time() in
  cake_tyv_num := n + 1;
  let r2 = try Ok (cake_term_of_preterm (cake_retypecheck_raw venv ptm)) with e -> Error e in
  let t2 = Sys.time() in
  cake_parse_check_times.(0) <- cake_parse_check_times.(0) +. (t1 -. t0);
  cake_parse_check_times.(1) <- cake_parse_check_times.(1) +. (t2 -. t1);
  cake_parse_check_stats.(0) <- cake_parse_check_stats.(0) + 1;
  let show r = match r with
      Ok tm -> let s = string_of_term tm in
               "term " ^ (if String.length s > 300 then String.sub s 0 300 else s)
    | Error e -> Printexc.to_string e in
  let same = match r1,r2 with
      Ok t1,Ok t2 -> t1 = t2
    | Error e1,Error e2 -> Printexc.to_string e1 = Printexc.to_string e2
    | _ -> false in
  (match r1 with Error _ ->
     cake_parse_check_stats.(2) <- cake_parse_check_stats.(2) + 1 | _ -> ());
  (if not same then
     (cake_parse_check_stats.(1) <- cake_parse_check_stats.(1) + 1;
      Printf.printf "CAKEPARSEDIFF\t%s\t%s\t%s\n%!" (String.escaped src)
        (String.escaped (show r1)) (String.escaped (show r2))));
  match r1 with
    Ok tm -> tm
  | Error e -> raise e;;

let cake_parse_check_report () =
  Printf.printf "CAKEPARSECHECK\tparses %d\tdifferences %d\tfailures %d\tHOL Light %.3f s\tkit %.3f s\ttables %d %d %d %d\n%!"
    cake_parse_check_stats.(0) cake_parse_check_stats.(1) cake_parse_check_stats.(2)
    cake_parse_check_times.(0) cake_parse_check_times.(1)
    cake_ptab_rebuilds.(0) cake_ptab_rebuilds.(1) cake_ptab_rebuilds.(2)
    cake_ptab_rebuilds.(3);;

(* the term of a preterm, as term_of_preterm (retypecheck venv ptm) *)

let cake_preterm_to_term (src:string) venv ptm =
  if !cake_parse_check then cake_parse_check_both src venv ptm
  else cake_term_of_preterm (cake_retypecheck venv ptm);;

(* Replaces HOL Light's parse_term (parser.ml), which every quotation calls: *)
(* the same terms, made with the kit's typechecker and constant tables       *)
(* (cake_retypecheck, cake_term_of_preterm), each wildcard _ its own variable *)
let parse_term s =
  let ptm,l = (parse_preterm o flat o map cake_wild_tokens o lex o explode) s in
  if l = [] then cake_preterm_to_term s [] ptm
  else failwith "Unparsed input following term";;

(* T and F, the commonest quotations in tactic code that runs once per       *)
(* subterm or per assumption, like concl th = F: made once (a parse costs   *)
(* milliseconds in a session with thousands of constants)                   *)

let parse_term =
  let t_tm = parse_term "T" and f_tm = parse_term "F" in
  fun s -> if s = "T" then t_tm else if s = "F" then f_tm else parse_term s;;
