(* ========================================================================= *)
(* ml_monadBaseLib: port of HOL4 translator/monadic/monad_base/             *)
(* ml_monadBaseLib.sml (CakeML v3479).  Proof automation for the state-and- *)
(* exception monad that is supported by the proof-producing monadic         *)
(* translator: general helpers, and the mechanical definitions of the       *)
(* manipulation functions of the monadic states (get_f, set_f), of the      *)
(* exceptions (raise_E, handle_E), of the arrays (f_length, f_sub,          *)
(* update_f, alloc_f) and of a run function for locally initialised arrays.  *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - HOL4's general helpers dest_fun_type, mk_fun_type, mk_list_vars,       *)
(*   mk_list_vars_same and my_list_mk_comb are mb_dest_fun_type, ...,        *)
(*   mb_my_list_mk_comb (the translator binds another dest_fun_type, and all *)
(*   files share one session); the definitional entry points keep HOL4's    *)
(*   names.                                                                  *)
(* - HOL4's sep_type_unify (in my_list_mk_comb) is HOL Light's type_unify    *)
(*   after the type variables of the combinator are renamed apart from those *)
(*   of the arguments.                                                       *)
(* - HOL4's Define is new_definition: every equation here has a variable    *)
(*   applied to distinct variables on the left.  The generated names are    *)
(*   HOL4's (get_f, set_f, raise_C, handle_C, f_length, f_sub, update_f,     *)
(*   alloc_f, run_NAME) with the HOL Light names of the fields and           *)
(*   constructors.                                                           *)
(* - HOL4's run (ml_monadBase) is ml_monadBase_run.  define_run defines the  *)
(*   new record type with the kit's cake_record (HOL4 astHol_datatype).      *)
(* - create_dynamic_access_functions of HOL4 is not exported by HOL4's       *)
(*   signature and is not used by the monadic translator: not ported.       *)
(* ========================================================================= *)

needs "translator/monadic/monad_base/ml_monadBase.ml";;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Constants and types (HOL4 get_term, get_type)                             *)
(* ------------------------------------------------------------------------- *)

let mb_exc_ty = `:(A,B)exc`;;
let mb_a_ty = `:A` and mb_b_ty = `:B` and mb_c_ty = `:C`;;
let mb_num_ty = `:num`;;
let mb_K_const = `K:A->B->A`;;
let mb_FST_const = `FST:A#B->A`;;
let mb_SND_const = `SND:A#B->B`;;
let mb_REPLICATE_const = `REPLICATE:num->A->A list`;;
let mb_unit_const = `one`;;
let mb_M_failure_const = `M_failure:A->(B,A)exc`;;
let mb_M_success_const = `M_success:A->(A,B)exc`;;
let mb_Marray_length_const = `Marray_length:(S->A list)->S->(num,E)exc#S`;;
let mb_Marray_sub_const = `Marray_sub:(S->A list)->E->num->S->(A,E)exc#S`;;
let mb_Marray_update_const =
  `Marray_update:(S->A list)->(A list->S->S)->E->num->A->S->(1,E)exc#S`;;
let mb_Marray_alloc_const = `Marray_alloc:(A list->S->S)->num->A->S->(1,E)exc#S`;;
let mb_run_const = `ml_monadBase_run:(A->(B,C)exc#A)->A->(B,C)exc`;;

(* ------------------------------------------------------------------------- *)
(* Helper functions                                                          *)
(* ------------------------------------------------------------------------- *)

(* HOL Light's type_subst (typeSysProps binds a theorem of that name) *)
let mb_type_subst i ty = type_of (inst i (mk_var ("x", ty)));;

let mk_exc_type a b = mb_type_subst [a,mb_a_ty; b,mb_b_ty] mb_exc_ty;;

let mk_Mtype a b c =
  let ty = mk_exc_type b c in
  mk_fun_ty a (mk_type ("prod", [ty; a]));;

let mk_Failure exn x_ty =
  let tm = inst [type_of exn,mb_a_ty; x_ty,mb_b_ty] mb_M_failure_const in
  mk_comb (tm, exn);;

let mk_Success x exn_ty =
  let tm = inst [type_of x,mb_a_ty; exn_ty,mb_b_ty] mb_M_success_const in
  mk_comb (tm, x);;

(* HOL4 dest_fun_type: the argument types and the result type *)
let rec mb_dest_fun_type ty =
  if is_type ty && fst (dest_type ty) = "fun" then
    let (ty1,ty2) = dest_fun_ty ty in
    let (params_ty, ret_ty) = mb_dest_fun_type ty2 in
    (ty1 :: params_ty, ret_ty)
  else ([], ty);;

let rec mb_mk_fun_type (tyl, ret_ty) =
  match tyl with
    ty::tyl -> mk_fun_ty ty (mb_mk_fun_type (tyl, ret_ty))
  | [] -> ret_ty;;

(* fresh type variables, renamed apart from those of the arguments *)
let mb_tyvar_count = ref 0;;
let mb_fresh_tyvar () =
  mb_tyvar_count := !mb_tyvar_count + 1;
  mk_vartype ("_mb" ^ string_of_int !mb_tyvar_count);;

(* HOL4 my_list_mk_comb: list_mk_comb after unifying the types of the first *)
(* n argument types of the combinator with the types of the n arguments,     *)
(* "as one" (HOL4's sep_type_unify: the type variables of the combinator and *)
(* of the arguments are separate); a type variable of the combinator that    *)
(* the unification leaves gets back its name, or a fresh A1, A2, ... when    *)
(* the arguments use that name                                               *)
let mb_my_list_mk_comb (comb, args) =
  if args = [] then comb else
  try
    let avoid = itlist (fun a l -> union (type_vars_in_term a) l) args [] in
    let ctvs = type_vars_in_term comb in
    let ren = map (fun tv -> (mb_fresh_tyvar (), tv)) ctvs in
    let comb' = inst ren comb in
    let (all_comb_arg_tys, _) = mb_dest_fun_type (type_of comb') in
    if length args > length all_comb_arg_tys
    then failwith "my_list_mk_comb - too many arguments" else
    let comb_arg_tys = fst (chop_list (length args) all_comb_arg_tys) in
    let mk_ft tys = end_itlist mk_fun_ty tys in
    let uni = type_unify (mk_ft comb_arg_tys) (mk_ft (map type_of args)) [] in
    let comb'' = inst uni comb' and args' = map (inst uni) args in
    let used = ref (itlist (fun a l -> union (type_vars_in_term a) l) args'
                      (type_vars_in_term comb'')) in
    let left = filter (fun (f,_) -> mem f (type_vars_in_term comb'')) ren in
    let pick tv =
      if not (mem tv avoid) && not (mem tv !used) then (used := tv :: !used; tv) else
      let rec go n = let t = mk_vartype ("A" ^ string_of_int n) in
                     if mem t !used || mem t avoid then go (n+1)
                     else (used := t :: !used; t) in
      go 1 in
    let back = map (fun (f,tv) -> (pick tv, f)) left in
    list_mk_comb (inst back comb'', map (inst back) args')
  with Failure s -> failwith ("my_list_mk_comb: " ^ s);;

let mb_mk_list_vars basename types =
  let rec mk_aux types i =
    match types with
      ty::types -> mk_var (basename ^ string_of_int i, ty) :: mk_aux types (i+1)
    | [] -> [] in
  mk_aux types 1;;

let mb_mk_list_vars_same basename ty n =
  let rec mk_aux i =
    if i > n then [] else mk_var (basename ^ string_of_int i, ty) :: mk_aux (i+1) in
  mk_aux 1;;

(* the constructors of a datatype, in order, and its case constant with   *)
(* the type variables of ty (HOL4 TypeBase.constructors_of, case_const_of) *)
let mb_tyname ty = fst (dest_type ty);;

let mb_constructors_of ty =
  let ci = case_info_of_tyname (mb_tyname ty) in
  map (fun (_,pat) ->
         let c = fst (strip_comb pat) in
         let (_,cty) = mb_dest_fun_type (type_of c) in
         inst (type_match cty ty []) c) ci.ci_pats;;

(* the case constant of ty with the return type rty *)
let mb_case_const_of ty rty =
  let ci = case_info_of_tyname (mb_tyname ty) in
  let c = ci.ci_case in
  let (args, ret) = mb_dest_fun_type (type_of c) in
  inst (type_match (mk_fun_ty (hd args) ret) (mk_fun_ty ty rty) []) c;;

(* HOL4 Define on an equation built as a term: new_definition (benign     *)
(* redefinitions give the stored theorem back)                             *)
let mb_define tm = new_definition tm;;

(* ------------------------------------------------------------------------- *)
(* The raise and handle functions of an exception type                       *)
(* (HOL4 define_monad_exception_functions)                                   *)
(* ------------------------------------------------------------------------- *)

let define_monad_exception_functions exn_type state_type =
  let exn_cons = mb_constructors_of exn_type in
  let state_var = mk_var ("state", state_type) in
  (* raise functions *)
  let mk_raise_fun ctor =
    let (params_ty, _) = mb_dest_fun_type (type_of ctor) in
    let vars = mb_mk_list_vars "e" params_ty in
    let fun_body = list_mk_comb (ctor, vars) in
    let fun_body = mk_pair (mk_Failure fun_body mb_a_ty, state_var) in
    let fun_body = mk_abs (state_var, fun_body) in
    let fun_name = "raise_" ^ fst (dest_const ctor) in
    let fun_type = mb_mk_fun_type (params_ty, type_of fun_body) in
    let fun_var = mk_var (fun_name, fun_type) in
    let def_lhs = list_mk_comb (fun_var, vars) in
    mb_define (mk_eq (def_lhs, fun_body)) in
  let raise_funs = map mk_raise_fun exn_cons in
  (* handle functions *)
  let mk_failure_success_fun ctor =
    let (params_ty, _) = mb_dest_fun_type (type_of ctor) in
    let vars = mb_mk_list_vars "e" params_ty in
    let ret_type = mk_exc_type mb_a_ty exn_type in
    let monad_ret_type = mk_fun_ty state_type (mk_type ("prod", [ret_type; state_type])) in
    let f_type = mb_mk_fun_type (params_ty, monad_ret_type) in
    let f_var = mk_var ("f", f_type) in
    let success_fun_body = list_mk_abs (vars, mk_comb (list_mk_comb (f_var, vars), state_var)) in
    let failure_fun_body = mk_Failure (list_mk_comb (ctor, vars)) mb_a_ty in
    let failure_fun_body = list_mk_abs (vars, mk_pair (failure_fun_body, state_var)) in
    (success_fun_body, failure_fun_body) in
  let cases_funs = map mk_failure_success_fun exn_cons in
  let rec mk_funs_list l n =
    match l with
      [] -> []
    | (s,f)::funs -> (if n = 0 then s else f) :: mk_funs_list funs (n-1) in
  let nl = 0 -- (length exn_cons - 1) in
  let funs_lists = map (mk_funs_list cases_funs) nl in
  let funs_pairs = zip exn_cons funs_lists in
  let exc_type = mk_exc_type mb_a_ty exn_type in
  let pair_exc_type = mk_type ("prod", [exc_type; state_type]) in
  let monad_type = mk_fun_ty state_type pair_exc_type in
  let x_var = mk_var ("x", monad_type) in
  (* case x st of (res, st) => ... *)
  let x_st_tm = mk_comb (x_var, state_var) in
  let case_x_st_tm = mk_comb (mb_case_const_of (type_of x_st_tm) pair_exc_type, x_st_tm) in
  let res_var = mk_var ("res", exc_type) in
  (* case res of M_success y => (M_success y, st) | M_failure e => ... *)
  let y_var = mk_var ("y", mb_a_ty) in
  let success_tm = mk_abs (y_var, mk_pair (mk_Success y_var exn_type, state_var)) in
  let case_res_tm = mk_comb (mk_comb (mb_case_const_of exc_type pair_exc_type, res_var),
                             success_tm) in
  let e_var = mk_var ("e", exn_type) in
  let exn_case_tm = mk_comb (mb_case_const_of exn_type pair_exc_type, e_var) in
  let mk_handle_fun (ctor, funs_list) =
    let case_tm = list_mk_comb (exn_case_tm, funs_list) in
    let case_tm = mk_comb (case_res_tm, mk_abs (e_var, case_tm)) in
    let case_tm = list_mk_abs ([res_var; state_var], case_tm) in
    let case_tm = mk_comb (case_x_st_tm, case_tm) in
    let case_tm = mk_abs (state_var, case_tm) in
    let mtype = mk_Mtype state_type mb_a_ty exn_type in
    let params_types = fst (mb_dest_fun_type (type_of ctor)) in
    let ftype = mb_mk_fun_type (params_types, mtype) in
    let fvar = mk_var ("f", ftype) in
    let handle_fun_var_name = "handle_" ^ fst (dest_const ctor) in
    let handle_fun_type = mb_mk_fun_type ([mtype; ftype], mtype) in
    let handle_fun_var = mk_var (handle_fun_var_name, handle_fun_type) in
    let def_lhs = list_mk_comb (handle_fun_var, [x_var; fvar]) in
    mb_define (mk_eq (def_lhs, case_tm)) in
  let handle_funs = map mk_handle_fun funs_pairs in
  zip raise_funs handle_funs;;

(* ------------------------------------------------------------------------- *)
(* Fixed stores: the reference manipulation functions                        *)
(* (HOL4 define_monad_get_fun, define_monad_set_fun, define_monad_access_funs)*)
(* ------------------------------------------------------------------------- *)

let define_monad_get_fun (name, get_fun) =
  let state_var = mk_var ("state", fst (dest_fun_ty (type_of get_fun))) in
  let monad_get_fun = mk_abs (state_var,
    mk_pair (mk_Success (mk_comb (get_fun, state_var)) mb_c_ty, state_var)) in
  let monad_get_fun = rand (concl (TOP_DEPTH_CONV BETA_CONV monad_get_fun)) in
  let monad_get_fun_name = "get_" ^ name in
  let monad_get_fun_var = mk_var (monad_get_fun_name, type_of monad_get_fun) in
  mb_define (mk_eq (monad_get_fun_var, monad_get_fun));;

let define_monad_set_fun (name, set_fun) =
  let param_type = type_of (fst (dest_abs set_fun)) in
  let x_var = mk_var ("x", param_type) in
  let set_fun1 = rand (concl (BETA_CONV (mk_comb (set_fun, x_var)))) in
  let state_ty = fst (dest_fun_ty (type_of set_fun1)) in
  let state_var = mk_var ("state", state_ty) in
  let partial_set_fun = mk_abs (state_var,
    mk_pair (mk_Success mb_unit_const mb_c_ty, mk_comb (set_fun1, state_var))) in
  let monad_set_fun_name = "set_" ^ name in
  let monad_set_fun_var = mk_var (monad_set_fun_name,
                                  mk_fun_ty param_type (type_of partial_set_fun)) in
  mb_define (mk_eq (mk_comb (monad_set_fun_var, x_var), partial_set_fun));;

(* the fields of a record type: (name, accessor, update), instantiated to ty *)
let mb_record_fields ty =
  let ri = record_info (mb_tyname ty) in
  map (fun (f,acc,upd) ->
         let i = type_match (fst (dest_fun_ty (type_of acc))) ty [] in
         (f, inst i acc, inst i upd)) ri.ri_fields;;

let define_monad_access_funs data_type =
  let fields = mb_record_fields data_type in
  let abstract_update set_f =
    (* set_f : (fty -> fty) -> rec -> rec *)
    let fty = fst (dest_fun_ty (fst (dest_fun_ty (type_of set_f)))) in
    let var = mk_var ("x", fty) in
    let k = inst [fty,mb_a_ty; fty,mb_b_ty] mb_K_const in
    mk_abs (var, mk_comb (set_f, mk_comb (k, var))) in
  let names = map (fun (f,_,_) -> f) fields in
  let get_funs = map (fun (f,acc,_) -> define_monad_get_fun (f, acc)) fields in
  let set_funs = map (fun (f,_,upd) -> define_monad_set_fun (f, abstract_update upd)) fields in
  let rec zip3 l1 l2 l3 =
    match l1,l2,l3 with
      x1::l1, x2::l2, x3::l3 -> (x1,x2,x3) :: zip3 l1 l2 l3
    | [],[],[] -> []
    | _ -> failwith "zip3 given lists of different lengths" in
  zip3 names get_funs set_funs;;

(* ------------------------------------------------------------------------- *)
(* Fixed stores: the array manipulation functions                            *)
(* (HOL4 define_MFarray_manip_funs, define_MRarray_manip_funs)               *)
(* ------------------------------------------------------------------------- *)

(* \state. state.f from get_f = \state. (M_success state.f, state), and     *)
(* \x state. state with f := x from set_f x = \state. (M_success (), ...)   *)
let mb_get_fun_of_def get_fun_def =
  let (state, b) = dest_abs (rhs (concl get_fun_def)) in
  mk_abs (state, rand (fst (dest_pair b)));;

let mb_set_fun_of_def set_fun_def =
  let x = fst (dest_forall (concl set_fun_def)) in
  let set_fun = rhs (snd (strip_forall (concl set_fun_def))) in
  let (state, b) = dest_abs set_fun in
  mk_abs (x, mk_abs (state, snd (dest_pair b)));;

let define_MFarray_manip_funs_aux sub_exn update_exn (name, get_fun_def, set_fun_def) =
  let get_fun = mb_get_fun_of_def get_fun_def in
  let set_fun = mb_set_fun_of_def set_fun_def in
  (* length *)
  let length_f = mb_my_list_mk_comb (mb_Marray_length_const, [get_fun]) in
  let length_v = mk_var (name ^ "_length", type_of length_f) in
  let length_def = mb_define (mk_eq (length_v, length_f)) in
  (* sub *)
  let sub_f = mb_my_list_mk_comb (mb_Marray_sub_const, [get_fun; sub_exn]) in
  let sub_v = mk_var (name ^ "_sub", type_of sub_f) in
  let sub_def = mb_define (mk_eq (sub_v, sub_f)) in
  (* update *)
  let update_f = mb_my_list_mk_comb (mb_Marray_update_const, [get_fun; set_fun; update_exn]) in
  let update_v = mk_var ("update_" ^ name, type_of update_f) in
  let update_def = mb_define (mk_eq (update_v, update_f)) in
  (name, get_fun_def, set_fun_def, length_def, sub_def, update_def);;

let define_MRarray_manip_funs_aux sub_exn update_exn (name, get_fun_def, set_fun_def) =
  let set_fun = mb_set_fun_of_def set_fun_def in
  let (name, get_fun_def, set_fun_def, length_def, sub_def, update_def) =
    define_MFarray_manip_funs_aux sub_exn update_exn (name, get_fun_def, set_fun_def) in
  (* alloc *)
  let alloc_f = mb_my_list_mk_comb (mb_Marray_alloc_const, [set_fun]) in
  let alloc_v = mk_var ("alloc_" ^ name, type_of alloc_f) in
  let alloc_def = mb_define (mk_eq (alloc_v, alloc_f)) in
  (name, get_fun_def, set_fun_def, length_def, sub_def, update_def, alloc_def);;

let define_MFarray_manip_funs array_access_funs sub_exn update_exn =
  map (define_MFarray_manip_funs_aux sub_exn update_exn) array_access_funs;;

let define_MRarray_manip_funs array_access_funs sub_exn update_exn =
  map (define_MRarray_manip_funs_aux sub_exn update_exn) array_access_funs;;

(* ------------------------------------------------------------------------- *)
(* Locally initialised fixed-size arrays: a new record type whose array     *)
(* fields are pairs (size, initial value), and its run function             *)
(* (HOL4 define_run)                                                        *)
(* ------------------------------------------------------------------------- *)

(* the run definitions made by define_run, by constant name (HOL4 finds    *)
(* them in its theorem database)                                            *)
let mb_run_defs = ref ([] : (string * thm) list);;

let define_run state array_fields new_state_name =
  let fields = mb_record_fields state in
  let fty_of acc = snd (dest_fun_ty (type_of acc)) in
  let mk_field (field_name, acc, _) =
    let field_type = fty_of acc in
    if mem field_name array_fields then
      let (type_cons, elem_type) = dest_type field_type in
      if type_cons <> "list" then
        failwith ("define_local_init_state : trying to define an array from a field " ^
                  "which is not a list : " ^ field_name) else
      (field_name, mk_type ("prod", [mb_num_ty; hd elem_type]))
    else (field_name, field_type) in
  let fields_info = map mk_field fields in
  let tyvars = tyvars state in
  (if tyvars <> [] then
     failwith "define_run: polymorphic state types are not supported (cake_record)");
  let _ = cake_record new_state_name
            (map (fun (f,ty) -> (f, string_of_type ty)) fields_info) in
  let new_state = mk_type (new_state_name, []) in
  let new_fields = mb_record_fields new_state in
  let new_state_var = mk_var ("state", new_state) in
  let mk_new_field (field_name, acc, _) =
    let field_tm = mk_comb (acc, new_state_var) in
    if mem field_name array_fields then
      let (n_ty, e_ty) = (match dest_type (type_of field_tm) with
                            (_,[a;b]) -> (a,b) | _ -> failwith "define_run") in
      let fst_tm = mk_comb (inst [n_ty,mb_a_ty; e_ty,mb_b_ty] mb_FST_const, field_tm) in
      let snd_tm = mk_comb (inst [n_ty,mb_a_ty; e_ty,mb_b_ty] mb_SND_const, field_tm) in
      list_mk_comb (inst [e_ty,mb_a_ty] mb_REPLICATE_const, [fst_tm; snd_tm])
    else field_tm in
  let new_field_tms = map mk_new_field new_fields in
  let state_cons = hd (mb_constructors_of state) in
  let synth_state = list_mk_comb (state_cons, new_field_tms) in
  let x_var = mk_var ("x", mk_fun_ty state (mk_type ("prod",
                 [mk_exc_type mb_b_ty mb_c_ty; state]))) in
  let run_c = inst [state,mb_a_ty] mb_run_const in
  let body = list_mk_comb (run_c, [x_var; synth_state]) in
  let new_run_type = mb_mk_fun_type ([type_of x_var; new_state], type_of body) in
  let new_run_var = mk_var ("run_" ^ new_state_name, new_run_type) in
  let def = mb_define (mk_eq (list_mk_comb (new_run_var, [x_var; new_state_var]), body)) in
  mb_run_defs := ("run_" ^ new_state_name, def) :: !mb_run_defs;
  def;;
