(* ========================================================================= *)
(* ml_parseLib: the program parser of the basis scripts (CakeML v3479):     *)
(* HOL4's characteristic/cfTacticsBaseLib.sml parse, parse_topdecs,          *)
(* cfTacticsLib.sml process_topdecs, cfNormaliseLib.sml and the Quote        *)
(* cakeml: and Quote add_cakeml: syntax of basis/basisFunctionsLib.sml.      *)
(*                                                                           *)
(* As in HOL4, a CakeML program text is parsed by evaluation of the verified *)
(* lexer lexer_fun, PEG interpreter peg_exec on cmlPEG and parse-tree        *)
(* conversion of cmlPtreeConversion (here by Compute, HOL4: EVAL):           *)
(*   parse_prog_thm s : |- parse_prog (lexer_fun s) = peg_Success [] decs NONE *)
(*   parse_topdecs s  : decs (constructors and literals only)                *)
(*   process_topdecs s: normalise_prog decs (HOL4's unverified A-normal form,  *)
(*                      ported step by step), also cakeml;                   *)
(*   add_cakeml s     : appends process_topdecs s to ml_progLib's program.   *)
(* The basis scripts give add_cakeml HOL4's program text verbatim.           *)
(*                                                                           *)
(* The compute set is the dependency closure of parse_prog and lexer_fun     *)
(* (mlp_closure): every constant met by the evaluation gets its equations    *)
(* (a missing one fails at load time), with HOL4's [compute] choices        *)
(* (peg_exec_thm, applykont_thm, cmlPEG_exec_thm, get_token_eqn,            *)
(* ptree_Expr_pevaled; cmlPEG and coreloop opaque) and conversions for       *)
(* arithmetic, ORD, CHR and the equality of values.  Speed: see the notes    *)
(* MLP in Mlp_compute and the comments at mlp_parse_cs.                      *)
(* ========================================================================= *)

needs "compiler/parsing/cmlParse.ml";;
needs "compiler/parsing/lexer_impl.ml";;
needs "translator/ml_progLib.ml";;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Mlp_compute: HOL Light's Compute (compute.ml, Alexey Solovyev's port of   *)
(* HOL4's computeLib by Bruno Barras), copied with three changes, marked    *)
(* MLP (the theorems are the same, only the inferences that make them        *)
(* differ):                                                                  *)
(* - a rule is instantiated by INST of its pattern variables, where          *)
(*   compute.ml applies SPEC to the generalised rule once per variable.      *)
(*   Each SPEC substitutes under the remaining binders, and the capture      *)
(*   checks there traverse the instantiated values (vfree_in); for values    *)
(*   with much sharing, such as the continuations of the PEG interpreter,    *)
(*   whose tree size grows exponentially with the depth of the parse, that   *)
(*   took 9 s to parse a one-token expression (0.2 s with INST);            *)
(* - the INST is made in two rounds, the variables that occur under an      *)
(*   abstraction of the rule first (their values are traversed by the       *)
(*   capture checks at abstractions whose body changes), then the others     *)
(*   (the rest of the input of the lexer: the lexer became 3 times faster);  *)
(*   the pattern variables are renamed to genvars, so that the rounds and     *)
(*   type instantiation cannot identify two variables;                       *)
(* - MK_comb's combination of an unchanged rator and rand keeps the theorem  *)
(*   it started from (no MK_COMB and TRANS; 15% faster).                     *)
(* The global compset of compute.ml is left out; comments removed (see       *)
(* compute.ml).                                                              *)
(* ------------------------------------------------------------------------- *)

module type Mlp_compute_sig = sig
  type compset

  val monitoring : (term -> bool) option ref
  val stoppers : (term -> bool) option ref

  val new_compset : thm list -> compset
  val bool_compset : unit -> compset

  val add_thms : thm list -> compset -> unit
  val add_conv : term * int * conv -> compset -> unit
  val set_skip : compset -> term -> int option -> unit

  val scrub_const : compset -> term -> unit
  val scrub_thms : thm list -> compset -> unit

  val lazyfy_thm : thm -> thm
  val strictify_thm : thm -> thm

  val CBV_CONV : compset -> term -> thm
  val WEAK_CBV_CONV : compset -> term -> thm

  type 'a fterm
  type db
  type transform = private Conversion of (term -> thm * db fterm) | Rrules of thm list

  val listItems : compset -> (string * transform list) list
end;;

module Mlp_compute : Mlp_compute_sig = struct

let RIGHT_BETA th =
  try TRANS th (BETA_CONV (rhs (concl th)))
  with _ -> failwith "RIGHT_BETA";;

let RIGHT_ETA thm =
  try TRANS thm (ETA_CONV (rhs (concl thm)))
  with _ -> failwith "RIGHT_ETA";;

(* MLP: an application whose rator and rand are unchanged keeps th *)

let MK_comb th =
  let rator, rand = dest_comb (rhs (concl th)) in
  let mka th1 th2 =
    if rhs (concl th1) == rator && rhs (concl th2) == rand then th
    else TRANS th (MK_COMB (th1, th2)) in
  (REFL rator, REFL rand, mka);;

let MK_abs th =
  let bvar, body = dest_abs (rhs (concl th)) in
  (bvar, REFL body, fun th1 -> TRANS th (ABS bvar th1));;

let rec BODY_CONJUNCTS th =
  if is_forall (concl th) then
    BODY_CONJUNCTS (SPEC_ALL th)
  else if is_conj (concl th) then
    BODY_CONJUNCTS (CONJUNCT1 th) @ BODY_CONJUNCTS (CONJUNCT2 th)
  else [th];;

type ('a, 'b, 'c) stack =
    Ztop
  | Zrator of 'a * ('a, 'b, 'c) stack
  | Zrand of 'b * ('a, 'b, 'c) stack
  | Zabs of 'c * ('a, 'b, 'c) stack;;

exception Dead_code of string;;

let rhs_concl = rand o concl;;
let refl_thm = REFL;;
let trans_thm = TRANS;;
let beta_thm = RIGHT_BETA;;
let evaluate th = th;;

let try_eta thm = try RIGHT_ETA thm with _ -> thm;;

let push_in_stk f arg (th, stk) =
  let (tha, thb, mka) = MK_comb th in
  (tha, Zrator ((mka, (thb, f arg)), stk));;

let push_skip_stk f arg (th, stk) =
  let (tha, thb, mka) = MK_comb th in
  (tha, Zrand ((C mka, true, (thb, f arg)), stk));;

let push_lam_in_stk (th, stk) =
  let (_, thb, mkl) = MK_abs th in
  (thb, Zabs (try_eta o mkl, stk));;

let FUNIFY thm =
  try
    let x = rand (lhs (concl thm)) in
    CONV_RULE (RATOR_CONV (RAND_CONV (CHANGED_CONV (PURE_REWRITE_CONV[ETA_AX])))) (ABS x thm)
  with _ -> failwith "FUNIFY";;

let UNFUNIFY thm =
  try
    let lhs, rhs = dest_eq (concl thm) in
    let x = variant (frees lhs) (fst (dest_abs rhs)) in
    CONV_RULE (RAND_CONV BETA_CONV) (AP_THM thm x)
  with _ -> failwith "UNFUNIFY";;

let repeat_on_conj f thm =
  let rec iter th = try iter (f th) with _ -> th in
  end_itlist CONJ (List.map iter (BODY_CONJUNCTS thm));;

let lazyfy_thm = repeat_on_conj FUNIFY;;
let strictify_thm = repeat_on_conj UNFUNIFY;;

let eq_intro thm =
  if is_eq (concl thm) then thm else
  if is_neg (concl thm) then EQF_INTRO thm
  else EQT_INTRO thm;;

type pattern =
    Pvar of int
  | Papp of term * pattern list;;

let check_arg_form trm =
  let rec chk t stk free =
    if is_comb t then
      let rator, rand = dest_comb t in
      let free', pat1 = chk rand [] free in
      chk rator (pat1 :: stk) free'
    else if is_var t then
      if stk = [] then
        let newi = List.length free in
        try (free, Pvar (newi - index t free - 1))
        with _ -> (t :: free, Pvar newi)
      else
        failwith ("check_arg_form: " ^ fst (dest_var t) ^ " occurs as a variable on lhs")
    else if is_const t then
      (free, Papp (t, List.rev stk))
    else
      failwith ("check_arg_form: lambda abstraction not allowed on lhs: `"
        ^ (string_of_term trm) ^ "`")
  in
  match chk trm [] [] with
    | (fv, Papp (head, args)) -> (List.rev fv, head, args)
    | _ -> failwith "check_arg_form: ill-formed lhs";;

type 'a cst_rec = {
  head: term;
  args: (term * 'a fterm) list;
  rws: 'a;
  skip: int option
}
and 'a clos_rec = {
  env: 'a fterm list;
  term: 'a dterm
}
and 'a fterm =
    Const of 'a cst_rec
  | Neutr
  | Clos of 'a clos_rec

and 'a dterm =
    Bv of int
  | Fv
  | Cst of term * ('a * int option) ref
  | App of 'a dterm * 'a dterm list
  | Abs of 'a dterm;;

let appl = function
  | App (a, l1), arg -> App (a, arg :: l1)
  | t, arg -> App (t, [arg]);;

let inst_type_dterm = function
  | [], v -> v
  | tysub, v ->
    let rec tyi_dt = function
      | Cst (c, dbsk) -> Cst (inst tysub c, dbsk)
      | App (h, l) -> App (tyi_dt h, map tyi_dt l)
      | Abs v -> Abs (tyi_dt v)
      | v -> v in
    tyi_dt v;;

type action =
    Rewrite of rewrite list
  | Conv of (term -> thm * db fterm)

and try_rec = {
  hcst: term;
  rws: action;
  tail: db
}

and db =
    End_db
  | Try of try_rec
  | Need_arg of db

and rewrite_rec = {
  cst: term;
  lhs: pattern list;
  npv: int;
  rhs: db dterm;
  thm: thm;
  fva: term array;
  lama: bool array
}

and rewrite =
    Rw of rewrite_rec;;

let rec add_in_db = function
  | (n, cst, act, End_db) ->
      funpow n (fun a -> Need_arg a) (Try { hcst = cst; rws = act; tail = End_db })
  | (0, cst, (Rewrite nrws as act), Try { hcst = hcst; rws = Rewrite rws as rw; tail = tail }) ->
    if cst = hcst then Try { hcst = hcst; rws = Rewrite (nrws @ rws); tail = tail }
    else Try { hcst = hcst; rws = rw; tail = add_in_db (0, cst, act, tail) }
  | (n, cst, act, Try { hcst = hcst; rws = rws; tail = tail }) ->
    Try { hcst = hcst; rws = rws; tail = add_in_db(n, cst, act, tail) }
  | (0, cst, act, db) ->
    Try { hcst = cst; rws = act; tail = db }
  | (n, cst, act, Need_arg tail) ->
    Need_arg (add_in_db(n - 1, cst, act, tail));;

let key_of (Rw {cst = cst; lhs = lhs}) =
  let name, _ = dest_const cst in
  (name, length lhs, cst);;

let is_skip = function
  | (_, Const {skip = Some n; args = args}) -> n <= List.length args
  | _ -> false;;

let partition_skip skip args =
  match skip with
  | Some n ->
    let len = List.length args in
    if n <= len then
      chop_list (len - n) args
    else
      ([], args)
  | None -> ([], args);;

type compset =
    Rws of (string, (db * int option) ref) Hashtbl.t;;

let empty_rws () = Rws (Hashtbl.create 100);;

let assoc_clause (Rws rws) cst =
  try Hashtbl.find rws cst
  with Not_found ->
    let mt = ref (End_db, None) in
    Hashtbl.add rws cst mt;
    mt;;

let add_in_db_upd rws (name, arity, hcst) act =
  let { contents = db, sk } as rl = assoc_clause rws name in
  rl := add_in_db (arity, hcst, act, db), sk;;

let set_skip_name (Rws htbl as rws) p sk =
  let { contents = db, _ } as rl = assoc_clause rws p in
  rl := db, sk;;

let scrub_const (Rws htbl) c =
  let name, _ = dest_const c in
  Hashtbl.remove htbl name;;

let from_term (rws, env, t) =
  let rec down (env, t, c) =
    match t with
    | Var _ -> up ((try Bv (index t env) with _ -> Fv), c)
    | Const (name, _) -> up (Cst (t, assoc_clause rws name), c)
    | Comb (rator, rand) -> down (env, rator, Zrator ((env, rand), c))
    | Abs (bvar, body) -> down (bvar :: env, body, Zabs ((), c))

  and up = function
    | dt, Ztop -> dt
    | dt, Zrator ((env, arg), c) -> down (env, arg, Zrand(dt, c))
    | dt, Zrand (dr, c) -> up (appl (dr, dt), c)
    | dt, Zabs (_, c) -> up (Abs dt, c)
  in
  down (env, t, Ztop);;

let mk_rewrite rws eq_thm =
  let lhs, rhs = dest_eq (concl eq_thm) in
  let fv, cst, pats = check_arg_form lhs in
  (* MLP: the pattern variables are renamed to genvars, and those that occur *)
  (* under an abstraction are recorded (see inst_rw)                          *)
  let fv' = map (fun v -> genvar (type_of v)) fv in
  let eq_thm = INST (zip fv' fv) eq_thm in
  let fv = fv' in
  let rhs = snd (dest_eq (concl eq_thm)) in
  let rec under_abs acc tm =
    if is_abs tm then union (frees tm) acc
    else if is_comb tm then
      let f,x = dest_comb tm in under_abs (under_abs acc f) x
    else acc in
  let lv = under_abs [] (concl eq_thm) in
  let rhsc = from_term (rws, rev fv, rhs) in
  Rw {
    cst = cst;
    lhs = pats;
    rhs = rhsc;
    npv = length fv;
    thm = eq_thm;
    fva = Array.of_list fv;
    lama = Array.of_list (map (fun v -> mem v lv) fv)
  };;

let unsuitable th =
  let l, r = dest_eq (concl th) in
  can (term_match [] l) r;;

let enter_thm rws thm0 =
  let thm = eq_intro thm0 in
  if unsuitable thm then ()
  else
    let rw = mk_rewrite rws thm in
    add_in_db_upd rws (key_of rw) (Rewrite [rw]);;

let add_thms lthm rws =
  List.iter (List.iter (enter_thm rws) o BODY_CONJUNCTS) lthm;;

let add_extern (cst, arity, fconv) rws =
  let name, _ = dest_const cst in
  add_in_db_upd rws (name, arity, cst) (Conv fconv);;

let new_rws () =
  let rws = empty_rws () in
  add_thms [REFL_CLAUSE] rws;
  rws;;

let from_list lthm =
  let rws = new_rws() in
  add_thms lthm rws;
  rws;;

let scrub_thms lthm rws =
  let tmlist = map (concl o hd o BODY_CONJUNCTS) lthm in
  let clist = map (fst o strip_comb o lhs o snd o strip_forall) tmlist in
  List.iter (scrub_const rws) clist;;

let rws_of (Rws htbl) =
  let dblist = Hashtbl.fold (fun _ {contents = (db, _)} r -> db :: r) htbl [] in
  let rec get_actions db =
    match db with
    | End_db -> []
    | Need_arg db' -> get_actions db'
    | Try {hcst = hcst; rws = rws; tail = tail} ->
      (hcst, rws) :: get_actions tail in
  let actionlist = List.concat (List.map get_actions dblist) in
  let dest (Rw {thm = thm}) = thm in
  let dest_action = function
    | hcst, Rewrite rws -> (hcst, map dest rws)
    | hcst, Conv _ -> (hcst, []) in
  let rwlist = List.map dest_action actionlist in
  rwlist;;

type transform =
    Conversion of (term -> thm * db fterm)
  | Rrules of thm list;;

let deplist (Rws htbl) =
  let dblist = Hashtbl.fold (fun s {contents = (db, _)} r -> (s, db) :: r) htbl [] in
  let rec get_actions db =
    match db with
    | End_db -> []
    | Need_arg db' -> get_actions db'
    | Try {hcst = hcst; rws = rws; tail = tail} ->
      rws :: get_actions tail in
  let actionlist = List.map (fun (s, db) -> s, get_actions db) dblist in
  let dest (Rw {thm = thm}) = thm in
  let dest_action = function
    | Rewrite rws -> Rrules (map dest rws)
    | Conv ecnv -> Conversion ecnv in
  let rwlist = List.map (fun (s, act) -> s, map dest_action act) actionlist in
  rwlist;;

exception No_match;;

let match_const (bds, tbds) pc c =
  let name, ty = dest_const pc in
  let name', ty' = dest_const c in
  if name = name' then
    try bds, type_match ty ty' tbds with _ -> raise No_match
  else raise No_match;;

let match_var (bds, tbds) var arg =
  let _ = match bds.(var) with
  | Some (tm, _) -> if aconv tm (fst arg) then () else raise No_match
  | None -> bds.(var) <- Some arg in
  (bds, tbds);;

let rec match_list bds pats args =
  match (pats, args) with
    | pat :: pats, arg :: args ->
      match_list (match_solve bds pat arg) pats args
    | [], [] -> bds
    | _ -> raise (Dead_code "match_list")

and match_solve bds pat arg =
  match (pat, arg) with
  | Pvar var, arg -> match_var bds var arg
  | Papp (phead, pargs), (_, Const {head = head; args = args}) ->
    if length pargs = length args then
      match_list (match_const bds phead head) pargs args
    else
      raise No_match
  | _ -> raise No_match;;

type 'a rule_inst = {
  rule: rewrite;
  inst: (term * 'a fterm) option array * (hol_type * hol_type) list
};;

let try_rwn ibds lt =
  let rec try_rec = function
    | [] -> raise No_match
    | (Rw {lhs = lhs; npv = npv} as rw) :: rwn ->
      let env = Array.make npv None in
      try { rule = rw; inst = match_list (env, ibds) lhs lt }
      with No_match -> try_rec rwn
  in
  try_rec;;

let comb_ct cst arg =
  match cst with
  | { head = head; args = args; rws = Need_arg tail; skip = skip } ->
    Const { head = head; args = arg :: args; rws = tail; skip = skip }
  | { head = head; args = args; rws = End_db; skip = skip } ->
    Const { head = head; args = arg :: args; rws = End_db; skip = skip }
  | { rws = Try _ } ->
    raise (Dead_code "comb_ct: yet rules to try");;

let mk_clos (env, t) =
  match t with
  | Cst (hc, { contents = (db, b) }) -> Const {head = hc; args = []; rws = db; skip = b}
  | Bv i -> List.nth env i
  | Fv -> Neutr
  | _ -> Clos {env = env; term = t};;

(* MLP: the pattern variables are instantiated by INST (compute.ml: SPEC per *)
(* variable), in two rounds: first those under an abstraction of the rule,  *)
(* then the others.  At an abstraction whose body changes, vsubst traverses *)
(* every value of its substitution (capture check), so the values of the     *)
(* variables that occur under no abstraction, such as the rest of the input  *)
(* of the lexer, are traversed by no capture check.                          *)

let inst_rw (th, monitoring,
             {rule = Rw {thm = thm; rhs = rhs; fva = fva; lama = lama};
              inst = (bds, tysub)}) =
  let tirhs = inst_type_dterm (tysub, rhs) in
  let tithm = INST_TYPE tysub thm in
  let il1 = ref [] and il2 = ref [] and venv = ref [] in
  Array.iteri (fun k b ->
      match b with
        Some (tm, v) ->
          let x = inst tysub fva.(k) in
          (if lama.(k) then il1 := (tm,x) :: !il1 else il2 := (tm,x) :: !il2);
          venv := v :: !venv
      | None -> raise (Dead_code "inst_rw")) bds;
  let th1 = if !il1 = [] then tithm else INST !il1 tithm in
  let spec_thm = if !il2 = [] then th1 else INST !il2 th1 in
  let () = if monitoring then print_term (concl spec_thm) in
  trans_thm th spec_thm, mk_clos (!venv, tirhs);;

let monitoring = ref (None: (term -> bool) option);;
let stoppers = ref (None: (term -> bool) option);;

let rec reduce_cst = function
  | th, {head = head; args = args; rws = Try {hcst = hcst; rws = Rewrite rls; tail = tail}; skip = skip} ->
   (try
      let () = match !stoppers with None -> () | Some p -> if p head then raise No_match else () in
      let _, _, tytheta = try term_match [] hcst head with _ -> raise No_match in
      let rule_inst = try_rwn tytheta args rls in
      let mon = match !monitoring with None -> false | Some f -> f head in
      let insted = inst_rw (th, mon, rule_inst) in
        (true, insted)
    with No_match ->
      reduce_cst (th, {head = head; args = args; rws = tail; skip = skip}))
  | th, {head = head; args = args; rws = Try {hcst = hcst; rws = Conv fconv; tail = tail}; skip = skip} ->
   (try
      let thm, ft = fconv (rhs_concl th) in
        (true, (trans_thm th thm, ft))
    with _ ->
      reduce_cst (th, {head = head; args = args; rws = tail; skip = skip}))
  | th, cst -> (false, (th, Const cst));;

let auto_import_definitions = ref true;;

let new_compset = from_list;;
let listItems = deplist;;

type cbv_stack =
  ((thm->thm->thm) * (thm * db fterm),
   (thm->thm->thm) * bool * (thm * db fterm),
   (thm->thm)) stack;;

let rec stack_out = function
  | th, Ztop -> th
  | th, Zrator ((mka, (thb, _)), ctx) -> stack_out (mka th thb, ctx)
  | th, Zrand ((mka, _, (tha, _)), ctx) -> stack_out (mka tha th, ctx)
  | th, Zabs (mkl, ctx) -> stack_out (mkl th, ctx);;

let initial_state rws t =
  ((refl_thm t, mk_clos ([], from_term (rws, [], t))), (Ztop: cbv_stack));;

let rec cbv_wk = function
  | (th, Clos {env = env; term = App (a, args)}), stk ->
    let tha, stka = rev_itlist (push_in_stk (curry mk_clos env)) args (th, stk) in
    cbv_wk ((tha, mk_clos (env, a)), stka)
  | (th, Clos {env = env; term = Abs body}), Zrator ((mka, (thb, cl)), s') ->
    cbv_wk ((beta_thm (mka th thb), mk_clos (cl :: env, body)), s')
  | (th, Const cargs), stk ->
    let reduced, clos = reduce_cst (th, cargs) in
    if reduced then cbv_wk (clos, stk) else cbv_up (clos, stk)
  | clos, stk -> cbv_up (clos, stk)

and cbv_up = function
  | hcl, Zrator ((mka, clos), ctx) ->
    let new_state = clos, Zrand ((mka, false, hcl), ctx) in
    if is_skip hcl then cbv_up new_state else cbv_wk new_state
  | (thb, v), Zrand ((mka, false, (th, Const cargs)), stk) ->
    cbv_wk ((mka th thb, comb_ct cargs (rhs_concl thb, v)), stk)
  | (thb, Neutr), Zrand ((mka, false, (th, Neutr)), stk) ->
    cbv_up ((mka th thb, Neutr), stk)
  | clos, stk -> clos, stk;;

let rec strong = function
  | (th, Clos {env = env; term = Abs t}), stk ->
    let thb, stk' = push_lam_in_stk (th, stk) in
    strong (cbv_wk ((thb, mk_clos (Neutr :: env, t)), stk'))
  | (_, Clos _), stk ->
    raise (Dead_code "strong")
  | (th, Const {skip = skip; args = args}), stk ->
    let argssk, argsrd = partition_skip skip args in
    let th', stk' = rev_itlist (push_skip_stk snd) argssk (th, stk) in
    let th'', stk'' = rev_itlist (push_in_stk snd) argsrd (th', stk') in
    strong_up (th'', stk'')
  | (th, Neutr), stk -> strong_up (th, stk)

and strong_up = function
  | th, Ztop -> th
  | th, Zrand ((mka, false, (tha, Neutr)), ctx) ->
    strong (cbv_wk ((mka tha th, Neutr), ctx))
  | th, Zrand ((mka, false, clos), ctx) ->
    raise (Dead_code "strong_up")
  | th, Zrator ((mka, clos), ctx) ->
    strong (cbv_wk (clos, Zrand ((mka, true, (th, Neutr)), ctx)))
  | th, Zrand ((mka, true, (tha, _)), ctx) ->
    strong_up (mka tha th, ctx)
  | th, Zabs (mkl, ctx) ->
    strong_up (mkl th, ctx);;

let CBV_CONV rws = evaluate o strong o cbv_wk o initial_state rws;;

let WEAK_CBV_CONV rws =
  evaluate
  o (fun ((th, _), stk) -> stack_out (th, stk))
  o cbv_wk
  o initial_state rws;;

let extern_of_conv rws conv tm =
  let thm = conv tm in
  thm, mk_clos ([], from_term (rws, [], rhs (concl thm)));;

let add_conv (cst, arity, conv) rws =
  add_extern (cst, arity, extern_of_conv rws conv) rws;;

let set_skip compset c opt =
  try
    let name, _ = dest_const c in
    set_skip_name compset name opt
  with _ -> failwith "set_skip";;

let bool_redns =
  strictify_thm LET_DEF
  :: List.map lazyfy_thm
    [COND_CLAUSES; COND_ID; NOT_CLAUSES;
     AND_CLAUSES; OR_CLAUSES; IMP_CLAUSES; EQ_CLAUSES];;

let bool_compset () =
  let base = from_list bool_redns in
  let () = set_skip base `COND: bool -> A -> A -> A` None in

  base;;

end;;

(* ------------------------------------------------------------------------- *)
(* Small term utilities.                                                     *)
(* ------------------------------------------------------------------------- *)

let mlp_const_name tm = fst (dest_const tm);;

let mlp_head_name tm =
  let h = fst (strip_comb tm) in
  if is_const h then fst (dest_const h) else "";;

(* Terms made by evaluation share subterms (the continuations of the PEG     *)
(* interpreter much so): traversals visit each physical subterm once.        *)

module Mlp_phys = Hashtbl.Make (struct
  type t = term
  let equal = (==)
  let hash = Hashtbl.hash
end);;

(* the set of constant names occurring in a term *)

let mlp_consts_of tm =
  let seen = Mlp_phys.create 1000 and names = Hashtbl.create 100 in
  let rec go tm =
    if not (Mlp_phys.mem seen tm) then
    begin
      Mlp_phys.replace seen tm ();
      match tm with
        Const(n,_) -> Hashtbl.replace names n ()
      | Comb(f,x) -> go f; go x
      | Abs(_,b) -> go b
      | Var _ -> ()
    end in
  go tm;
  Hashtbl.fold (fun n () acc -> n :: acc) names [];;

(* the number of physically distinct subterms *)

let mlp_dag_size tm =
  let seen = Mlp_phys.create 1000 in
  let rec go tm =
    if not (Mlp_phys.mem seen tm) then
    begin
      Mlp_phys.replace seen tm ();
      match tm with
        Comb(f,x) -> go f; go x
      | Abs(_,b) -> go b
      | _ -> ()
    end in
  go tm; Mlp_phys.length seen;;

(* ------------------------------------------------------------------------- *)
(* Characters: ORD and CHR of literals, memoised (a char literal is ASCII of  *)
(* eight booleans; CHR n with a numeral n becomes such a literal).           *)
(* ------------------------------------------------------------------------- *)

let MLP_ORD_CONV =
  let memo = Array.make 256 None in
  let conv0 = REWR_CONV ORD_DEF THENC REWRITE_CONV[BITVAL_CLAUSES] THENC
              NUM_REDUCE_CONV in
  fun tm ->
    match tm with
      Comb(Const("ORD",_),c) ->
        let k = Char.code (dest_char c) in
        (match memo.(k) with
           Some th -> th
         | None -> let th = conv0 tm in memo.(k) <- Some th; th)
    | _ -> failwith "MLP_ORD_CONV";;

let MLP_CHR_CONV =
  let memo = Hashtbl.create 256 in
  let conv0 = REWR_CONV CHR_DEF THENC NUM_REDUCE_CONV in
  fun tm ->
    match tm with
      Comb(Const("CHR",_),n) when is_numeral n ->
        let k = dest_numeral n in
        (try Hashtbl.find memo k with Not_found ->
           let th = conv0 tm in Hashtbl.replace memo k th; th)
    | _ -> failwith "MLP_CHR_CONV";;

(* ------------------------------------------------------------------------- *)
(* Equality of values: numerals, integers, characters and strings by the     *)
(* library conversions; constructor terms of the kit's datatypes by their    *)
(* distinctness and injectivity theorems (each made into a conversion once,  *)
(* when first needed).                                                       *)
(* ------------------------------------------------------------------------- *)

let mlp_ctor_eq_tbl = (Hashtbl.create 4096 : (string * string, conv) Hashtbl.t);;

let mlp_ctor_types_done = (Hashtbl.create 64 : (string, unit) Hashtbl.t);;

let mlp_add_ctor_eqs (tyname:string) =
  if not (Hashtbl.mem mlp_ctor_types_done tyname) then
  begin
    Hashtbl.replace mlp_ctor_types_done tyname ();
    let ci = try Some (case_info_of_tyname tyname) with Failure _ -> None in
    match ci with
      None -> ()
    | Some ci ->
        let add th =
          let th1 = SPEC_ALL th in
          let th2 = if is_neg (concl th1) then EQF_INTRO th1 else th1 in
          let l,r = dest_eq (lhs (concl th2)) in
          Hashtbl.replace mlp_ctor_eq_tbl (mlp_head_name l,mlp_head_name r)
            (REWR_CONV th2) in
        List.iter add ci.ci_distinct;
        List.iter add ci.ci_inject
  end;;

let mlp_is_string_lit tm =
  let rec go t =
    match t with
      Const("NIL",_) -> true
    | Comb(Comb(Const("CONS",_),c),t') -> can dest_char c && go t'
    | _ -> false in
  go tm;;

let MLP_EQ_CONV tm =
  match tm with
    Comb(Comb(Const("=",_),l),r) ->
      if compare l r = 0 then EQT_INTRO (REFL l) else
      (match type_of l with
         Tyapp("num",[]) -> NUM_EQ_CONV tm
       | Tyapp("int",[]) -> INT_EQ_CONV tm
       | Tyapp("char",[]) -> CHAR_EQ_CONV tm
       | Tyapp("list",[Tyapp("char",[])])
           when mlp_is_string_lit l && mlp_is_string_lit r -> STRING_EQ_CONV tm
       | Tyapp(tyname,_) ->
           mlp_add_ctor_eqs tyname;
           let k = (mlp_head_name l,mlp_head_name r) in
           (try Hashtbl.find mlp_ctor_eq_tbl k with Not_found ->
              failwith "MLP_EQ_CONV") tm
       | _ -> failwith "MLP_EQ_CONV")
  | _ -> failwith "MLP_EQ_CONV";;

(* ------------------------------------------------------------------------- *)
(* The compute set by dependency closure.  HOL4's EVAL has one global       *)
(* compset; HOL Light's Compute needs the defining equations of every        *)
(* constant the evaluation meets, and one missing definition leaves a        *)
(* conditional stuck, whose branches call-by-value then keeps unfolding.    *)
(* mlp_closure starts from some root terms and follows the constants of the  *)
(* equations it finds, looking each constant up in order in:                 *)
(*  - mlp_override: equations that replace a definition (HOL4's [compute]   *)
(*    theorems of a [nocompute] definition, and constants kept opaque);      *)
(*  - the kit's store of cake_def definitions;                               *)
(*  - the case constants of the kit's datatypes (their ci_def);              *)
(*  - mlp_lib_defs: equations of library constants (HOL Light's own         *)
(*    recursive definitions, which keep no record of their equations);      *)
(*  - HOL Light's basic definitions (c = \x1 .. xn. t, used as               *)
(*    c x1 .. xn = t), unless their right side is a choice (@) term.         *)
(* Constructors, numerals and the constants that a conversion evaluates     *)
(* (arithmetic, ORD, CHR, equality) need no equations.                       *)
(* ------------------------------------------------------------------------- *)

let mlp_override = ref ([] : (string * thm list) list);;

let mlp_lib_defs = ref
  (["FST",[FST]; "SND",[SND]; "o",[o_THM]; "I",[I_THM]] : (string * thm list) list);;

(* constants handled by the conversions of the compset (mlp_conv_consts),   *)
(* and literal constants that are not datatype constructors                 *)

let mlp_literal_consts =
  ["NUMERAL"; "BIT0"; "BIT1"; "_0"; "T"; "F"; "int_of_num"; "int_neg";
   "word"; "ASCII"; "one"];;

let mlp_conv_consts = ref
  (setify (["="; "ORD"; "CHR"; "COND"; "/\\"; "\\/"; "~"; "==>"; "LET"] @
     map (fun (pat,_) -> mlp_head_name pat) num_red_conv_list @
     map (fun (pat,_) -> mlp_head_name pat) int_red_conv_list));;

let mlp_is_constructor =
  fun n -> let _,ktab = kit_case_tables () in Hashtbl.mem ktab n;;

(* tables of HOL Light's records of definitions, rebuilt when they change:  *)
(* the_definitions (new_definition and define: the equations as given),     *)
(* the_specifications (new_specification, so new_recursive_definition: the   *)
(* clauses) and the basic definitions of the kernel (c = t)                  *)

let mlp_table_of (get : unit -> 'a list) (keys : 'a -> (string * thm) list) =
  let tbl = ref (Hashtbl.create 1) and cache = ref [] in
  fun () ->
    let ds = get () in
    if not (ds == !cache) then
      (let t = Hashtbl.create 10000 in
       List.iter (fun d -> List.iter (fun (k,th) ->
           if not (Hashtbl.mem t k) then Hashtbl.replace t k th) (keys d)) ds;
       tbl := t; cache := ds);
    !tbl;;

let mlp_clause_heads th =
  setify (map (fun c -> mlp_head_name (lhs (snd (strip_forall c))))
              (conjuncts (snd (strip_forall (concl th)))));;

let mlp_definitions_tbl = mlp_table_of (fun () -> !the_definitions)
  (fun th -> try map (fun n -> n,th) (mlp_clause_heads th) with Failure _ -> []);;

let mlp_specifications_tbl = mlp_table_of (fun () -> !the_specifications)
  (fun ((names,_),sth) -> map (fun n -> n,sth) names);;

let mlp_basic_def_tbl = mlp_table_of definitions
  (fun th -> let l = lhs (concl th) in
             if is_const l then [fst (dest_const l),th] else []);;

(* |- c = \x1 .. xn. t  as  |- !x1 .. xn. c x1 .. xn = t *)

let mlp_applied_def th =
  let vs = fst (strip_abs (rhs (concl th))) in
  if vs = [] then th else GENL vs (RIGHT_BETAS vs th);;

let mlp_has_select th = mem "@" (mlp_consts_of (concl th));;

(* the kit's store of cake_def definitions, by every constant its clauses   *)
(* define (the store is keyed by the first one only: a mutual definition    *)
(* would otherwise be found as the kit's internal encoding of the other     *)
(* functions, through the MUTREC function on a sum type)                     *)

let mlp_store_tbl =
  let tbl = ref (Hashtbl.create 1) and size = ref (-1) in
  fun () ->
    if Hashtbl.length cake_def_store <> !size then
      (let t = Hashtbl.create 5000 in
       Hashtbl.iter (fun _ (_,th) ->
           List.iter (fun n -> if not (Hashtbl.mem t n) then Hashtbl.replace t n th)
             (try mlp_clause_heads th with Failure _ -> [])) cake_def_store;
       tbl := t; size := Hashtbl.length cake_def_store);
    !tbl;;

let mlp_find_defs (n:string) : thm list option =
  let ok th = not (mlp_has_select th) in
  let srcs =
    [(fun () -> assoc n !mlp_override);
     (fun () -> [Hashtbl.find (mlp_store_tbl ()) n]);
     (fun () -> let ctab,_ = kit_case_tables () in [(Hashtbl.find ctab n).ci_def]);
     (fun () -> assoc n !mlp_lib_defs);
     (fun () -> let th = Hashtbl.find (mlp_definitions_tbl ()) n in
                if ok th then [th] else failwith "");
     (fun () -> let th = Hashtbl.find (mlp_specifications_tbl ()) n in
                if ok th then [th] else failwith "");
     (fun () -> let th = mlp_applied_def (Hashtbl.find (mlp_basic_def_tbl ()) n) in
                if ok th then [th] else failwith "")] in
  let rec first l =
    match l with
      [] -> None
    | f::t -> (try Some (f ()) with Failure _ | Not_found -> first t) in
  first srcs;;

(* Paired lambdas \(x,y). t (HOL Light's GABS) are not evaluated by Compute: *)
(* the equations get the kit's ELIM_UNCURRY_CONV form \p. t[FST p/x, ..].   *)

(* Clauses with the patterns 0 and SUC v (an argument of type num) do not  *)
(* match numerals: such a pair of clauses (the other arguments variables)    *)
(* becomes f x1 .. m .. xn = if m = 0 then A else B[m - 1/v].               *)

let mlp_numeral_form th =
  let cls = map (snd o strip_forall) (conjuncts (snd (strip_forall (concl th)))) in
  let suc_pos tm =
    let _,args = strip_comb (lhs tm) in
    let rec find i l = match l with
        [] -> failwith "mlp_numeral_form"
      | a::t -> if is_comb a && is_const (rator a) &&
                   fst (dest_const (rator a)) = "SUC" then i else find (i+1) t in
    find 0 args in
  let c1,c2 = match cls with [a;b] -> a,b | _ -> failwith "mlp_numeral_form" in
  let cz,cs = if can suc_pos c1 then c2,c1 else c1,c2 in
  let p = suc_pos cs in
  let f,zargs = strip_comb (lhs cz) and _,sargs = strip_comb (lhs cs) in
  if el p zargs <> `0` then failwith "mlp_numeral_form" else
  let others = filter (fun (i,_) -> i <> p) (zip (0 -- (length zargs - 1)) zargs) in
  if not (forall (fun (_,a) -> is_var a) others) then failwith "mlp_numeral_form" else
  let v = rand (el p sargs) in
  let m = variant (frees (concl th)) (mk_var("m",`:num`)) in
  let sub = (mk_comb(mk_comb(`(-):num->num->num`,m),`1`),v) ::
            map (fun (i,a) -> (a, el i sargs)) others in
  let rhs_s = vsubst sub (rhs cs) in
  let args = map (fun i -> if i = p then m else el i zargs) (0 -- (length zargs - 1)) in
  let stm = list_mk_forall(args,
              mk_eq(list_mk_comb(f,args),
                    mk_cond(mk_eq(m,`0`),rhs cz,rhs_s))) in
  prove(stm, REPEAT GEN_TAC THEN STRUCT_CASES_TAC (SPEC m num_CASES) THEN
             REWRITE_TAC[th; NOT_SUC; SUC_SUB1]);;

let mlp_prep_thm th =
  let th = if mem "GABS" (mlp_consts_of (concl th))
           then CONV_RULE (TOP_DEPTH_CONV ELIM_UNCURRY_CONV) th else th in
  let has_suc_pat =
    exists (fun c -> mem "SUC" (mlp_consts_of (lhs (snd (strip_forall c)))))
      (conjuncts (snd (strip_forall (concl th)))) in
  if has_suc_pat then mlp_numeral_form th else th;;

(* the constants of the equations of a theorem (outer quantifiers dropped) *)

let mlp_eqn_consts th =
  let cls = conjuncts (snd (strip_forall (concl th))) in
  itlist (fun c acc -> union (mlp_consts_of (snd (strip_forall c))) acc) cls [];;

let mlp_needs_no_def handled (n:string) =
  mem n mlp_literal_consts || mem n !mlp_conv_consts || mem n handled ||
  mlp_is_constructor n;;

(* returns the equations (in the order found) and the constants without     *)
(* equations; a constant whose override list is empty is kept opaque, and   *)
(* the constants in handled are left to conversions of the caller           *)

let mlp_closure ?(handled=[]) (roots:term list) =
  let seen = Hashtbl.create 1000 in
  let ths = ref [] and missing = ref [] and orig = ref [] in
  let rec visit n =
    if not (Hashtbl.mem seen n) then
    begin
      Hashtbl.replace seen n ();
      if mlp_needs_no_def handled n then () else
      match mlp_find_defs n with
        Some l ->
          (* the functions of a mutual definition share their theorem *)
          let l = filter (fun th -> not (List.memq th !orig)) l in
          orig := l @ !orig;
          let l = map mlp_prep_thm l in
          ths := !ths @ l;
          List.iter (fun th -> List.iter visit (mlp_eqn_consts th)) l
      | None -> missing := n :: !missing
    end in
  List.iter (fun t -> List.iter visit (mlp_consts_of t)) roots;
  !ths, rev !missing;;

(* ------------------------------------------------------------------------- *)
(* A compset from equations: call-by-value with lazy conditionals (HOL4's    *)
(* COND skip), numeral and integer arithmetic, ORD, CHR and equality of      *)
(* values.                                                                   *)
(* ------------------------------------------------------------------------- *)

(* The boolean rules: compute.ml's bool_compset has COND T = \t1 t2. t1,    *)
(* whose beta steps traverse the branches (vsubst under \t2, then into the   *)
(* body), exponential for the shared continuations of the PEG interpreter;   *)
(* with HOL4's skip of the branches of COND, the rules COND T t1 t2 = t1 and *)
(* COND F t1 t2 = t2 are just as lazy and need no beta step.                *)

let mlp_bool_rules =
  let ct,cf = CONJ_PAIR (SPEC_ALL COND_CLAUSES) in
  Mlp_compute.strictify_thm LET_DEF :: ct :: cf ::
  map Mlp_compute.lazyfy_thm
    [NOT_CLAUSES; AND_CLAUSES; OR_CLAUSES; IMP_CLAUSES; EQ_CLAUSES];;

let mlp_new_compset (ths:thm list) =
  let cs = Mlp_compute.new_compset mlp_bool_rules in
  Mlp_compute.set_skip cs `COND: bool -> A -> A -> A` (Some 1);
  Mlp_compute.add_conv (`(=):A->A->bool`,2,MLP_EQ_CONV) cs;
  List.iter (fun (pat,cv) ->
      let c,args = strip_comb pat in Mlp_compute.add_conv (c,length args,cv) cs)
    (num_red_conv_list @ int_red_conv_list);
  Mlp_compute.add_conv (`ORD`,1,MLP_ORD_CONV) cs;
  Mlp_compute.add_conv (`CHR`,1,MLP_CHR_CONV) cs;
  Mlp_compute.add_thms ths cs;
  cs;;

(* the compset of the closure of some root terms; fails listing the         *)
(* constants without equations, unless they are allowed                     *)

let mlp_closure_compset ?(allowed=[]) ?(handled=[]) (roots:term list) =
  let ths,missing = mlp_closure ~handled roots in
  let bad = subtract missing allowed in
  if bad <> [] then
    failwith ("mlp_closure_compset: no equations for " ^ String.concat ", " bad)
  else mlp_new_compset ths;;

(* evaluation with a time limit (seconds of CPU time; 0.0 for none): a     *)
(* stopper fails when it is exceeded, so that a stuck evaluation ends       *)

let mlp_time_limit = ref 600.0;;

let mlp_eval (cs:Mlp_compute.compset) (tm:term) =
  let t0 = Sys.time() and lim = !mlp_time_limit and steps = ref 0 in
  let old = !Mlp_compute.stoppers in
  if lim > 0.0 then
    Mlp_compute.stoppers := Some (fun _ ->
      incr steps;
      if !steps land 1023 = 0 && Sys.time() -. t0 > lim
      then failwith "mlp_eval: time limit" else false);
  let th = try Mlp_compute.WEAK_CBV_CONV cs tm
           with e -> (Mlp_compute.stoppers := old; raise e) in
  Mlp_compute.stoppers := old; th;;

(* with the overrides ov added to mlp_override for the time of f () *)

let mlp_with_overrides ov f =
  let old = !mlp_override in
  mlp_override := ov @ old;
  let r = try f () with e -> (mlp_override := old; raise e) in
  mlp_override := old; r;;

(* ------------------------------------------------------------------------- *)
(* The parser's compset.  As in HOL4: the interpreter of the PEG runs by its *)
(* equations peg_exec_thm, applykont_thm and cmlPEG_exec_thm (one per        *)
(* non-terminal, the rule of cmlPEG applied), never by coreloop, and the     *)
(* grammar cmlPEG itself stays opaque (HOL4: cmlPEG_def[nocompute]); the     *)
(* fields of cmlPEG other than its rules are given by their values; the      *)
(* lexer's keyword table is get_token_eqn (HOL4: get_token_def[nocompute]). *)
(* ------------------------------------------------------------------------- *)

let mlp_cmlPEG_fields =
  let accs = CONJUNCTS (record_info "peg").ri_accessors in
  let cpeg = `cmlPEG` in
  map (fun th ->
      let f = rator (lhs (snd (strip_forall (concl th)))) in
      let n = fst (dest_const f) in
      if n = "peg_rules" || n = "peg_start" then n,[] else
      n,[(RAND_CONV (REWR_CONV cmlPEG_def) THENC REWR_CONV th)
           (mk_icomb(f,cpeg))])
    accs;;

let mlp_peg_overrides () =
  ["cmlPEG", []; "coreloop", []] @ mlp_cmlPEG_fields;;

(* The grammar rules, evaluated once: HOL4's cmlPEG_exec_thm has the rules   *)
(* as written (seql, choicel, pegf, tokeq, ...), which EVAL then builds at   *)
(* every call of a non-terminal; here the rules of cmlPEG_exec_thm are      *)
(* evaluated (to pegsym values with closures) when this file is loaded.     *)

let mlp_allq_conv c =
  let rec go tm = if is_forall tm then BINDER_CONV go tm else c tm in go;;

let mlp_cmlPEG_exec_eval_thm = ref TRUTH;;

mlp_cmlPEG_exec_eval_thm :=
  let rule_of th = rand (funpow 6 rator (rhs (snd (strip_forall (concl th))))) in
  let cls = map mlp_prep_thm (CONJUNCTS cmlPEG_exec_thm) in
  (* the non-terminals outside the grammar give Looped *)
  let rules = mapfilter rule_of cls in
  let cs = mlp_with_overrides (mlp_peg_overrides ())
             (fun () -> mlp_closure_compset rules) in
  let one th =
    match (try Some (rule_of th) with Failure _ -> None) with
      None -> th
    | Some r ->
        let rth = mlp_eval cs r in
        CONV_RULE (mlp_allq_conv
          (RAND_CONV (funpow 6 RATOR_CONV (RAND_CONV (K rth))))) th in
  end_itlist CONJ (map one cls);;

(* Memoised conversions for the lexer: the character predicates (HOL4's      *)
(* EVAL computes isSymbol c, a MEM over twenty characters, at each call) and  *)
(* the keyword table get_token (get_token_eqn), evaluated once per character  *)
(* and per identifier with a compset of their own.                           *)

let mlp_char_preds =
  ["isSpace"; "isDigit"; "isAlpha"; "isAlphaNum"; "isAlphaNumPrime"; "isSymbol";
   "is_single_char_symbol"; "isHexDigit"; "isUpper"; "isLower"];;

let mlp_lex_memo_cs =
  mlp_with_overrides ["get_token", [get_token_eqn]]
    (fun () -> mlp_closure_compset (`get_token` :: map (fun n -> mk_const(n,[])) mlp_char_preds));;

let MLP_CHAR_PRED_CONV =
  let tbl = Hashtbl.create 1000 in
  fun tm ->
    match tm with
      Comb(Const(n,_),c) ->
        let k = (n, Char.code (dest_char c)) in
        (try Hashtbl.find tbl k with Not_found ->
           let th = mlp_eval mlp_lex_memo_cs tm in
           Hashtbl.replace tbl k th; th)
    | _ -> failwith "MLP_CHAR_PRED_CONV";;

let MLP_GET_TOKEN_CONV =
  let tbl = Hashtbl.create 1000 in
  fun tm ->
    match tm with
      Comb(Const("get_token",_),s) when mlp_is_string_lit s ->
        let k = String.concat "" (map (fun c -> String.make 1 (dest_char c)) (dest_list s)) in
        (try Hashtbl.find tbl k with Not_found ->
           let th = mlp_eval mlp_lex_memo_cs tm in
           Hashtbl.replace tbl k th; th)
    | _ -> failwith "MLP_GET_TOKEN_CONV";;

(* HOL4's ptree_Expr_pevaled[compute]: the clause of ptree_Expr for a node, *)
(* specialised to each non-terminal ent of an expression.  The clause is     *)
(*   ptree_Expr ent (Nd (nt',loc) subs) =                                    *)
(*     OPTION_BIND (if INL ent = nt' then CHAIN else NONE) k                 *)
(* where CHAIN tests nt' = INL nEbase, nt' = INL nEtuple, ... in turn; with  *)
(* ent a constant N, nt' is INL N in CHAIN (MLP_COND_SUBST), whose tests     *)
(* are then decided, leaving N's branch: one test per call, where EVAL of    *)
(* the general clause makes one per non-terminal before N's.                *)

let MLP_COND_SUBST = prove
 (`!g (x:A) x' y. (g ==> x = x') ==> (if g then x else y) = (if g then x' else y)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[]);;

let mlp_bool_cs = mlp_new_compset [];;

(* decide the closed tests of a chain of conditionals, up to the first true *)

let rec mlp_cond_chain_conv tm =
  if is_cond tm then
    let c,(a,b) = dest_cond tm in
    if frees c <> [] then REFL tm else
    let cth = mlp_eval mlp_bool_cs c in
    let v = rhs (concl cth) in
    if v = `T` then
      TRANS (RATOR_CONV (RATOR_CONV (RAND_CONV (K cth))) tm)
            (CONJUNCT1 (ISPECL [a;b] COND_CLAUSES))
    else if v = `F` then
      let th = TRANS (RATOR_CONV (RATOR_CONV (RAND_CONV (K cth))) tm)
                     (CONJUNCT2 (ISPECL [a;b] COND_CLAUSES)) in
      TRANS th (mlp_cond_chain_conv b)
    else REFL tm
  else REFL tm;;

let mlp_ptree_Expr_pevaled = ref TRUTH;;

mlp_ptree_Expr_pevaled :=
  let cl = find (fun th -> mlp_head_name (rand (lhs (concl th))) = "grammar_Nd")
             (map SPEC_ALL (filter (fun th ->
                  mlp_head_name (lhs (snd (strip_forall (concl th)))) = "ptree_Expr")
                (CONJUNCTS ptree_Expr_def))) in
  let ent = rand (rator (lhs (concl cl))) in
  let one n =
    let th0 = INST [n,ent] cl in
    let r = rhs (concl th0) in
    let condt = rand (rator r) in
    let g,(x,y) = dest_cond condt in
    let gl,ntv = dest_eq g in
    let x' = vsubst [gl,ntv] x in
    let eqth = DISCH g (SUBS_CONV [SYM (ASSUME g)] x) in
    let th1 = MATCH_MP (ISPECL [g;x;x';y] MLP_COND_SUBST) eqth in
    let th2 = mlp_cond_chain_conv x' in
    let th3 = TRANS th1 (AP_THM (AP_TERM (rator (rator (rhs (concl th1)))) th2) y) in
    GEN_ALL (CONV_RULE (RAND_CONV (RATOR_CONV (RAND_CONV (K th3)))) th0) in
  end_itlist CONJ (map one
    [`nEbase`; `nEtuple`; `nElist2`; `nElist1`; `nEapp`; `nEmult`; `nEadd`;
     `nElistop`; `nErel`; `nEcomp`; `nEbefore`; `nEtyped`; `nElogicAND`;
     `nElogicOR`; `nEhandle`; `nE`]);;

let mlp_parser_overrides () =
  (* the general rules (of another type instance of peg_exec, so tried     *)
  (* first, Compute's order) before the 74 of the non-terminals              *)
  ["peg_exec", [peg_exec_thm; !mlp_cmlPEG_exec_eval_thm];
   "ptree_Expr", [ptree_Expr_def; !mlp_ptree_Expr_pevaled];
   "applykont", [applykont_thm]] @ mlp_peg_overrides ();;

let mlp_parse_cs =
  let cs = mlp_with_overrides (mlp_parser_overrides ())
    (fun () -> mlp_closure_compset ~handled:("get_token" :: mlp_char_preds)
                 [`parse_prog (lexer_fun "")`]) in
  List.iter (fun n -> Mlp_compute.add_conv (mk_const(n,[]),1,MLP_CHAR_PRED_CONV) cs)
    mlp_char_preds;
  Mlp_compute.add_conv (`get_token`,1,MLP_GET_TOKEN_CONV) cs;
  (* The furthest error eo of the interpreter (optmax MAXerr eo (SOME err))  *)
  (* is only passed on and returned, never inspected, and parse_prog drops  *)
  (* it: its arguments are not evaluated (skip), saving about a third of    *)
  (* the steps; the results are the same.                                   *)
  Mlp_compute.set_skip cs `optmax:(A->A->A)->(A)option->(A)option->(A)option` (Some 0);
  cs;;

let MLP_PARSE_EVAL_CONV tm = mlp_eval mlp_parse_cs tm;;

(* ------------------------------------------------------------------------- *)
(* The parsers.  parse_prog_thm s is |- parse_prog (lexer_fun s) =           *)
(* peg_Success [] decs NONE, by evaluation of the verified lexer, PEG        *)
(* parser and parse-tree conversion (cmlParse's parse_prog, which the        *)
(* compiler uses); parse_topdecs s is decs (HOL4: parse_topdecs, which       *)
(* EVALs the same functions).  mlp_parse nt sem s is HOL4's parse nt sem q:  *)
(* the AST x of a parse with non-terminal nt and conversion sem, from the    *)
(* theorems |- peg_exec cmlPEG (cmlPEG_pnt nt) (lexer_fun s) [] NONE []      *)
(* pegexec_done failed = Result (peg_Success [] [pt] eo) and |- sem pt =     *)
(* SOME x.  A failed parse fails with the location and message of the        *)
(* parser.                                                                   *)
(* ------------------------------------------------------------------------- *)

let mlp_lexer_tm = `lexer_fun`;;
let mlp_parse_prog_tm = `parse_prog`;;

(* peg_exec cmlPEG (cmlPEG_pnt nt) toks [] NONE [] pegexec_done failed *)

let mlp_peg_exec_tm =
  let pe = `peg_exec cmlPEG (cmlPEG_pnt nE)` in
  let f = rator pe and pnt = rator (rand pe) in
  let args = [`[]:(((mlptree)list)option)list`; `NONE:(locs#string)option`;
              `[]:(locs#string)list`;
              `pegexec_done:(token,MMLnonT,(mlptree)list,string)kont`;
              `failed:(token,MMLnonT,(mlptree)list,string)kont`] in
  fun nt toks -> list_mk_comb(f, mk_comb(pnt,nt) :: toks :: args);;

let mlp_string_of_locs (l:term) =
  try
    let a,b = match strip_comb l with
        Const("Locs",_),[a;b] -> a,b | _ -> failwith "" in
    let pt p = match strip_comb p with
        Const("POSN",_),[r;c] ->
          string_of_int (dest_small_numeral r + 1) ^ ":" ^ string_of_int (dest_small_numeral c + 1)
      | Const(n,_),[] -> n
      | _ -> "?" in
    "line:col " ^ pt a ^ " to " ^ pt b
  with Failure _ -> "unknown location";;

let mlp_fail_result (what:string) (r:term) =
  let msg =
    match strip_comb r with
      Const("Failure",_),[l;e] ->
        (try dest_string e with Failure _ -> "?") ^ " at " ^ mlp_string_of_locs l
    | Const("peg_Success",_),[rest;_;_] ->
        (try "unparsed tokens from " ^
             mlp_string_of_locs (rand (hd (dest_list rest)))
         with Failure _ -> "unparsed tokens")
    | _ -> "evaluation stuck" in
  failwith (what ^ ": " ^ msg);;

let parse_prog_thm (s:string) =
  MLP_PARSE_EVAL_CONV (mk_comb(mlp_parse_prog_tm, mk_comb(mlp_lexer_tm, mk_string s)));;

(* a value: constructors and literals only (no stuck evaluation inside) *)

let mlp_is_value tm =
  forall (fun n -> mlp_is_constructor n || mem n mlp_literal_consts) (mlp_consts_of tm) &&
  frees tm = [];;

(* After a failed parse: the furthest error of the PEG interpreter (eo), by   *)
(* an evaluation of nTopLevelDecs with optmax evaluated (the skip of         *)
(* mlp_parse_cs off for the time of it).  parse_prog reports the location   *)
(* of the first token of the declaration that fails (Expected to be at EOF), *)
(* eo where the parser got furthest.                                         *)

let mlp_optmax_tm = `optmax:(A->A->A)->(A)option->(A)option->(A)option`;;
let mlp_nTopLevelDecs_tm = `nTopLevelDecs`;;

let mlp_furthest_error (s:string) =
  try
    let tm = mlp_peg_exec_tm mlp_nTopLevelDecs_tm (mk_comb(mlp_lexer_tm, mk_string s)) in
    Mlp_compute.set_skip mlp_parse_cs mlp_optmax_tm None;
    let th = try MLP_PARSE_EVAL_CONV tm with e ->
      (Mlp_compute.set_skip mlp_parse_cs mlp_optmax_tm (Some 0); raise e) in
    Mlp_compute.set_skip mlp_parse_cs mlp_optmax_tm (Some 0);
    let r = rand (rhs (concl th)) in
    let le = match strip_comb r with
        Const("peg_Success",_),[_;_;eo] -> rand eo
      | Const("Failure",_),[l;e] -> mk_pair(l,e)
      | _ -> failwith "" in
    let l,e = dest_pair le in
    "; furthest error: " ^ dest_string e ^ " at " ^ mlp_string_of_locs l
  with Failure _ -> "";;

let parse_topdecs (s:string) =
  let th = parse_prog_thm s in
  let r = rhs (concl th) in
  match strip_comb r with
    Const("peg_Success",_),[rest;decs;_] when is_const rest ->
      if mlp_is_value decs then decs
      else failwith "parse_topdecs: the AST is not a value (evaluation stuck)"
  | _ -> (try mlp_fail_result "parse_topdecs" r
          with Failure m -> failwith (m ^ mlp_furthest_error s));;

let mlp_parse (nt:term) (sem:term) (s:string) =
  let toks = mk_comb(mlp_lexer_tm, mk_string s) in
  let ptm = mlp_peg_exec_tm nt toks in
  let pth = MLP_PARSE_EVAL_CONV ptm in
  let r = rhs (concl pth) in
  let res = match strip_comb r with
      Const("Result",_),[x] -> x | _ -> mlp_fail_result "mlp_parse" r in
  match strip_comb res with
    Const("peg_Success",_),[rest;pts;_] when is_const rest ->
      (match dest_list pts with
         [pt] ->
           let sth = MLP_PARSE_EVAL_CONV (mk_icomb(sem,pt)) in
           (match strip_comb (rhs (concl sth)) with
              Const("SOME",_),[x] -> x
            | _ -> failwith "mlp_parse: parse-tree conversion failed")
       | _ -> failwith "mlp_parse: not one parse tree")
  | _ -> mlp_fail_result "mlp_parse" res;;

let parse_exp = mlp_parse `nE` `ptree_Expr nE`;;

let parse_decl = mlp_parse `nDecl` `ptree_Decl`;;

(* ------------------------------------------------------------------------- *)
(* HOL4's cfNormaliseLib (unverified, as in HOL4): normalise_prog turns the  *)
(* bodies of the top-level Dlet and Dletrec declarations into A-normal form  *)
(* (annotations Tannot, Lannot and Ptannot removed first), with fresh names  *)
(* " v0", " v1", ...; the other declarations are unchanged.  A step by step  *)
(* port of the SML (cfNormaliseLib.sml); the order of the calls, and so the  *)
(* names, is HOL4's.                                                          *)
(* ------------------------------------------------------------------------- *)

let mlp_exp_ty = `:exp` and mlp_pat_ty = `:pat`;;
let mlp_mlstring_ty = `:mlstring`;;

(* term builders from precomputed constants (mk_const searches the constant *)
(* table, mk_list makes two such calls per list)                            *)

let mlp_mk_list =
  let tbl = Hashtbl.create 20 in
  fun (tms,ty) ->
    let nil,cons =
      try Hashtbl.find tbl ty with Not_found ->
        let nc = mk_const("NIL",[ty,aty]), mk_const("CONS",[ty,aty]) in
        Hashtbl.replace tbl ty nc; nc in
    itlist (fun h t -> mk_comb(mk_comb(cons,h),t)) tms nil;;

let mlp_char_ty = `:char`;;

let mlp_mk_string s =
  mlp_mk_list (map (fun i -> mk_char (String.get s i)) (0 -- (String.length s - 1)),
               mlp_char_ty);;

let mlp_dest_mlstring tm =
  match tm with
    Comb(Const("implode",_),s) ->
      String.concat "" (map (fun c -> String.make 1 (dest_char c)) (dest_list s))
  | _ -> failwith "mlp_dest_mlstring";;

let mlp_implode_tm = `implode`;;

let mlp_mk_mlstring s = mk_comb(mlp_implode_tm, mlp_mk_string s);;

let mlp_is_con name tm =
  match fst (strip_comb tm) with Const(n,_) -> n = name | _ -> false;;

let mlp_args tm = snd (strip_comb tm);;

let mlp_cn = let tbl = Hashtbl.create 50 in
  fun (n:string) -> try Hashtbl.find tbl n with Not_found ->
    let c = mk_const(n,[]) in Hashtbl.replace tbl n c; c;;

let mlp_mk name args = list_mk_comb(mlp_cn name, args);;

let mlp_short_tm = `Short:mlstring->(mlstring,mlstring)id` and mlp_var_tm = `Var`;;
let mlp_mk_Short x = mk_comb(mlp_short_tm, x);;
let mlp_mk_Var id = mk_comb(mlp_var_tm, id);;
let mlp_mk_Let (xo,e1,e2) = mlp_mk "Let" [xo;e1;e2];;
let mlp_some_name_tm = `SOME:mlstring->(mlstring)option`;;
let mlp_some_name x = mk_comb(mlp_some_name_tm, x);;
let mlp_none_name = `NONE:(mlstring)option`;;
let mlp_mk_exps es = mlp_mk_list(es, mlp_exp_ty);;

(* HOL4: dest_triple, mk_triple *)
let mlp_dest_triple tm = let x,yz = dest_pair tm in let y,z = dest_pair yz in x,y,z;;
let mlp_mk_triple (a,b,c) = mk_pair(a, mk_pair(b,c));;

(* strip_annot_pat, strip_annot_pats, strip_annot_exp, ...: as in HOL4,    *)
(* Pas fails, and so does Pref (HOL4 applies strip_annot_pats, on lists,   *)
(* to the pattern under Pref).                                             *)

let rec mlp_strip_annot_pat p =
  if mlp_is_con "Pvar" p || mlp_is_con "Plit" p || mlp_is_con "Pany" p then p
  else if mlp_is_con "Pcon" p then
    (match mlp_args p with [c;xs] -> mlp_mk "Pcon" [c; mlp_strip_annot_pats xs]
                         | _ -> failwith "strip_annot_pat")
  else if mlp_is_con "Pref" p then
    mlp_mk "Pref" [mlp_strip_annot_pats (hd (mlp_args p))]
  else if mlp_is_con "Ptannot" p then mlp_strip_annot_pat (hd (mlp_args p))
  else failwith "strip_annot_pat: unknown constructor"

and mlp_strip_annot_pats tm =
  mlp_mk_list(map mlp_strip_annot_pat (dest_list tm), mlp_pat_ty);;

let mlp_elty tm = hd (snd (dest_type (type_of tm)));;

let rec mlp_strip_annot_exp tm =
  let a = mlp_args tm in
  if mlp_is_con "Raise" tm then mlp_mk "Raise" [mlp_strip_annot_exp (hd a)]
  else if mlp_is_con "Handle" tm then
    mlp_mk "Handle" [mlp_strip_annot_exp (el 0 a); mlp_strip_annot_pes (el 1 a)]
  else if mlp_is_con "Lit" tm || mlp_is_con "Var" tm then tm
  else if mlp_is_con "Con" tm then
    mlp_mk "Con" [el 0 a; mlp_strip_annot_exps (el 1 a)]
  else if mlp_is_con "Fun" tm then
    mlp_mk "Fun" [el 0 a; mlp_strip_annot_exp (el 1 a)]
  else if mlp_is_con "App" tm then
    mlp_mk "App" [el 0 a; mlp_strip_annot_exps (el 1 a)]
  else if mlp_is_con "Log" tm then
    mlp_mk "Log" [el 0 a; mlp_strip_annot_exp (el 1 a); mlp_strip_annot_exp (el 2 a)]
  else if mlp_is_con "If" tm then
    mlp_mk "If" (map mlp_strip_annot_exp a)
  else if mlp_is_con "Mat" tm then
    mlp_mk "Mat" [mlp_strip_annot_exp (el 0 a); mlp_strip_annot_pes (el 1 a)]
  else if mlp_is_con "Let" tm then
    mlp_mk "Let" [el 0 a; mlp_strip_annot_exp (el 1 a); mlp_strip_annot_exp (el 2 a)]
  else if mlp_is_con "Letrec" tm then
    mlp_mk "Letrec" [mlp_strip_annot_funs (el 0 a); mlp_strip_annot_exp (el 1 a)]
  else if mlp_is_con "Tannot" tm || mlp_is_con "Lannot" tm then
    mlp_strip_annot_exp (el 0 a)
  else failwith "strip_annot_exp: unknown constructor"

and mlp_strip_annot_exps tm =
  mlp_mk_list(map mlp_strip_annot_exp (dest_list tm), mlp_exp_ty)

and mlp_strip_annot_pes tm =
  mlp_mk_list(map (fun pe -> let p,e = dest_pair pe in
                         let p' = mlp_strip_annot_pat p in
                         let e' = mlp_strip_annot_exp e in
                         mk_pair(p',e')) (dest_list tm), mlp_elty tm)

and mlp_strip_annot_funs tm =
  mlp_mk_list(map (fun t -> let f,x,e = mlp_dest_triple t in
                        mlp_mk_triple (f,x,mlp_strip_annot_exp e)) (dest_list tm),
          mlp_elty tm);;

(* The normalisation pass itself. *)

(* HOL4 dest_opapp: App Opapp [f; x], with f itself such an application or  *)
(* not, as (head, arguments); None for other expressions                    *)

let rec mlp_dest_opapp e =
  try
    if not (mlp_is_con "App" e) then failwith "" else
    let op,args = match mlp_args e with [op0;l] -> op0,l | _ -> failwith "" in
    if not (mlp_is_con "Opapp" op) then failwith "" else
    let fx = dest_list args in
    let f = el 0 fx and x = el 1 fx in
    match mlp_dest_opapp f with
      Some (f',args) -> Some (f', args @ [x])
    | None -> Some (f,[x])
  with Failure _ -> None;;

let mlp_opapp_tm = `Opapp`;;

let mlp_mk_opapp xs =
  List.fold_left (fun acc x -> mlp_mk "App" [mlp_opapp_tm; mlp_mk_exps [acc; x]])
    (List.hd xs) (List.tl xs);;

let mlp_fresh_name_in used =
  let rec aux n =
    let v = " v" ^ string_of_int n in
    if mem v used then aux (n + 1) else v in
  aux 0;;

let mlp_mk_names_generator () =
  let used = ref [] in
  let get () = let name = mlp_fresh_name_in !used in used := name :: !used; name in
  let record name = used := name :: !used in
  get, record;;

let rec mlp_record_pat_names record_var pat =
  if mlp_is_con "Pany" pat then ()
  else if mlp_is_con "Pvar" pat then record_var (hd (mlp_args pat))
  else if mlp_is_con "Plit" pat then ()
  else if mlp_is_con "Pcon" pat then
    List.iter (mlp_record_pat_names record_var) (dest_list (el 1 (mlp_args pat)))
  else if mlp_is_con "Pref" pat then mlp_record_pat_names record_var (hd (mlp_args pat))
  else if mlp_is_con "Ptannot" pat then
    mlp_record_pat_names record_var (hd (mlp_args pat))
  else failwith "record_pat_names: unknown constructor";;

let rec mlp_Lets bs body =
  match bs with
    [] -> body
  | (n,x)::xs -> mlp_mk_Let (mlp_some_name n, x, mlp_Lets xs body);;

let mlp_Let_NONE e1 e2 = mlp_mk_Let (mlp_none_name, e1, e2);;

let mlp_is_App_Opapp e =
  mlp_is_con "App" e && mlp_is_con "Opapp" (hd (mlp_args e));;

let mlp_norm_exp (fresh,record_name) e =
  let record_var v = record_name (mlp_dest_mlstring v) in
  let wrap_if_needed needs_wrapping e b =
    if needs_wrapping then
      let x = mlp_mk_mlstring (fresh ()) in
      (mlp_mk_Var (mlp_mk_Short x), b @ [(x, e)])
    else (e, b) in
  let rec norm is_named as_value e =
    let a = mlp_args e in
    if mlp_is_con "Lit" e then (e, [])
    else if mlp_is_con "Var" e then
      let name = hd a in
      let () = if mlp_is_con "Short" name then record_var (hd (mlp_args name)) in
      (e, [])
    else if mlp_is_con "Let" e then
      let opt = el 0 a and e1 = el 1 a and e2 = el 2 a in
      if mlp_is_con "SOME" opt then
        let x = hd (mlp_args opt) in
        let () = record_var x in
        let e1',b1 = norm true false e1 in
        let e2' = protect false e2 in
        let e' = mlp_Lets b1 (mlp_Lets [(x, e1')] e2') in
        wrap_if_needed as_value e' []
      else
        let e1',b1 = norm false false e1 in
        let e2' = protect false e2 in
        wrap_if_needed as_value (mlp_Let_NONE e1' e2') b1
    else if mlp_is_App_Opapp e then
      match mlp_dest_opapp e with
        Some (f,args) ->
          let f',b0 = norm false true f in
          let args',bi = norm_list_aux false true args in
          let e' = mlp_mk_opapp (f' :: args') in
          let b' = List.concat (List.rev (b0 :: bi)) in
          wrap_if_needed as_value e' b'
      | None -> failwith "norm: Opapp"
    else if mlp_is_con "App" e then
      let op = el 0 a in
      let args',bi = norm_list false true (el 1 a) in
      let b' = List.concat (List.rev bi) in
      wrap_if_needed as_value (mlp_mk "App" [op; args']) b'
    else if mlp_is_con "Con" e then
      let x = el 0 a in
      let args',bi = norm_list false true (el 1 a) in
      let b = List.concat (List.rev bi) in
      wrap_if_needed as_value (mlp_mk "Con" [x; args']) b
    else if mlp_is_con "Raise" e then
      let exn',b = norm false true (hd a) in
      wrap_if_needed as_value (mlp_mk "Raise" [exn']) b
    else if mlp_is_con "Log" e then
      let l = el 0 a and e1 = el 1 a and e2 = el 2 a in
      let e1',b1 = norm false true e1 in
      let e2',b2 = norm false true e2 in
      if b2 = [] then
        (if b1 = [] then (mlp_mk "Log" [l; e1'; e2'], [])
         else wrap_if_needed as_value (mlp_mk "Log" [l; e1'; e2']) b1)
      else
        let e2',b2 = norm false false e2 in
        if mlp_is_con "Andalso" l then
          wrap_if_needed as_value (mlp_mk "Log" [l; e1'; mlp_Lets b2 e2']) b1
        else if mlp_is_con "Orelse" l then
          wrap_if_needed as_value (mlp_mk "Log" [l; e1'; mlp_Lets b2 e2']) b1
        else failwith "norm: Log"
    else if mlp_is_con "Fun" e then
      let v = el 0 a and body = el 1 a in
      let () = record_var v in
      let body' = protect is_named body in
      wrap_if_needed (as_value || not is_named) (mlp_mk "Fun" [v; body']) []
    else if mlp_is_con "Mat" e then
      let e1',b1 = norm false true (el 0 a) in
      let rows' = norm_rows (el 1 a) in
      wrap_if_needed as_value (mlp_mk "Mat" [e1'; rows']) b1
    else if mlp_is_con "Handle" e then
      let e1' = protect false (el 0 a) in
      let rows' = norm_rows (el 1 a) in
      wrap_if_needed as_value (mlp_mk "Handle" [e1'; rows']) []
    else if mlp_is_con "If" e then
      let e1',b = norm false true (el 0 a) in
      let e2' = protect false (el 1 a) in
      let e3' = protect false (el 2 a) in
      wrap_if_needed as_value (mlp_mk "If" [e1'; e2'; e3']) b
    else if mlp_is_con "Letrec" e then
      let rs' = norm_letrec_branches (el 0 a) in
      let body' = protect false (el 1 a) in
      wrap_if_needed as_value (mlp_mk "Letrec" [rs'; body']) []
    else if mlp_is_con "Tannot" e || mlp_is_con "Lannot" e then
      norm is_named as_value (el 0 a)
    else failwith "norm: unknown constructor"
  and norm_list is_named as_value l_tm =
    let es,bs = norm_list_aux is_named as_value (dest_list l_tm) in
    (mlp_mk_exps es, bs)
  and norm_list_aux is_named as_value l =
    match l with
      [] -> ([], [])
    | e::es -> let e',b = norm is_named as_value e in
               let es',bs = norm_list_aux is_named as_value es in
               (e' :: es', b :: bs)
  and norm_rows l_tm =
    let rec aux l = match l with
        [] -> []
      | row::rows -> let row' = protect_row false row in row' :: aux rows in
    mlp_mk_list(aux (dest_list l_tm), mlp_elty l_tm)
  and norm_letrec_branches l_tm =
    let rec aux l = match l with
        [] -> []
      | br::brs -> let br' = protect_letrec_branch true br in br' :: aux brs in
    mlp_mk_list(aux (dest_list l_tm), mlp_elty l_tm)
  and protect is_named e =
    let e',b = norm is_named false e in mlp_Lets b e'
  and protect_row is_named row =
    let row_pat,row_body = dest_pair row in
    let () = mlp_record_pat_names record_var row_pat in
    let row_e' = protect is_named row_body in
    mk_pair(row_pat, row_e')
  and protect_letrec_branch is_named branch =
    let f,x,body = mlp_dest_triple branch in
    let () = record_var f in
    let () = record_var x in
    let body' = protect is_named body in
    mlp_mk_triple (f, x, body') in
  protect true e;;

let mlp_strip_annot_decl d =
  let a = mlp_args d in
  if mlp_is_con "Dlet" d then
    mlp_mk "Dlet" [el 0 a; mlp_strip_annot_pat (el 1 a); mlp_strip_annot_exp (el 2 a)]
  else if mlp_is_con "Dletrec" d then
    mlp_mk "Dletrec" [el 0 a; mlp_strip_annot_funs (el 1 a)]
  else d;;

let strip_annot_prog p_tm =
  mlp_mk_list(map mlp_strip_annot_decl (dest_list p_tm), mlp_elty p_tm);;

let normalise_exp e =
  mlp_norm_exp (mlp_mk_names_generator ()) (mlp_strip_annot_exp e);;

let normalise_decl d =
  let a = mlp_args d in
  if mlp_is_con "Dlet" d then
    let locs = el 0 a and pat = el 1 a and exp = el 2 a in
    let exp' = normalise_exp exp in
    mlp_mk "Dlet" [locs; pat; exp']
  else if mlp_is_con "Dletrec" d then
    let locs = el 0 a and l_tm = el 1 a in
    let gen = mlp_mk_names_generator () in
    let record_var v = snd gen (mlp_dest_mlstring v) in
    let rec aux l = match l with
        [] -> []
      | fdecl::rest ->
          let f,x,body = mlp_dest_triple fdecl in
          let () = record_var f in
          let () = record_var x in
          let body' = mlp_norm_exp gen (mlp_strip_annot_exp body) in
          let r = mlp_mk_triple (f, x, body') in
          r :: aux rest in
    mlp_mk "Dletrec" [locs; mlp_mk_list(aux (dest_list l_tm), mlp_elty l_tm)]
  else d;;

let normalise_prog p_tm =
  let rec aux l = match l with
      [] -> []
    | d::ds -> let d' = normalise_decl d in d' :: aux ds in
  mlp_mk_list(aux (dest_list p_tm), mlp_elty p_tm);;

(* ------------------------------------------------------------------------- *)
(* HOL4's process_topdecs (cfTacticsLib) and the Quote cakeml: syntax       *)
(* (basisFunctionsLib cakeml = process_topdecs): the normalised AST of a     *)
(* CakeML program.  HOL4's Quote and backquote quotations start with a       *)
(* location pragma (a space, then #loc LINE COL in comment brackets), a      *)
(* comment for the CakeML lexer that shifts the locations of the tokens of   *)
(* the first line; process_topdecs_at (line,col) s puts that pragma before   *)
(* s, for the locations of HOL4's AST.  Quote add_cakeml: is append_prog o   *)
(* process_topdecs (basisFunctionsLib; append_prog is ml_progLib's).          *)
(* ------------------------------------------------------------------------- *)

let process_topdecs (s:string) = normalise_prog (parse_topdecs s);;

let mlp_loc_pragma (line,col) =
  " (" ^ "*#loc " ^ string_of_int line ^ " " ^ string_of_int col ^ "*" ^ ")";;

let process_topdecs_at (line,col) (s:string) =
  process_topdecs (mlp_loc_pragma (line,col) ^ s);;

let cakeml = process_topdecs;;

(* HOL4 basisFunctionsLib: add_cakeml = append_prog o process_topdecs, with   *)
(* append_prog tm = ml_prog_update (add_prog (EVAL tm) pick_name); the AST   *)
(* of process_topdecs is a value, so its EVAL changes nothing.               *)

let add_cakeml (s:string) =
  ml_prog_update_current (ml_prog_add_prog (process_topdecs s) ml_prog_pick_name);;

let add_cakeml_at (line,col) (s:string) =
  ml_prog_update_current
    (ml_prog_add_prog (process_topdecs_at (line,col) s) ml_prog_pick_name);;
