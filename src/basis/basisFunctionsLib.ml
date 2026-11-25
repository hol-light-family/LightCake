(* ========================================================================= *)
(* basisFunctionsLib: port of HOL4 basis/basisFunctionsLib.sml (CakeML      *)
(* v3479).  Functions that aid building the CakeML code for the basis       *)
(* library: get_module_prefix, get_exn_conv, trans, append_dec,             *)
(* append_decs, append_prog; cakeml and add_cakeml (HOL4's Quote syntax)    *)
(* are ml_parseLib's process_topdecs and add_cakeml.                        *)
(*                                                                           *)
(* Differences from HOL4, forced by HOL Light:                               *)
(* - trans defines its constant under the port's name of the HOL4 name     *)
(*   (doc/names.tsv, through the translator's table of HOL4                *)
(*   names: the top-level plus of mlbasicsProg is mlbasicsProg_plus); the  *)
(*   definition is kept under NAME_def in the translator's theorem table   *)
(*   (tr_fetch "List_append_def"), as HOL4 keeps it in the theory;          *)
(* - HOL4's EVAL (in trans on the preconditions, in append_prog and        *)
(*   append_dec on the declarations) unfolds what its compset knows: here *)
(*   the side-condition definitions of the translation (trans) and the     *)
(*   definitions registered with basis_add_eval_thms (append_prog;          *)
(*   unknown_loc and, from mlbasicsProg on, mk_binop and mk_unop, the       *)
(*   definitions HOL4's EVAL meets in the basis declarations);              *)
(* - prove_ref_spec is a CF tactic (xcf, xsimpl): milestone M10.            *)
(* ========================================================================= *)

needs "translator/ml_translatorLib.ml";;
needs "translator/ml_parseLib.ml";;

(* HOL4 get_module_prefix: the open modules, outermost first, joined by _  *)
let get_module_prefix () =
  match ml_prog_get_open_modules (get_ml_prog_state ()) with
    [] -> ""
  | mods -> String.concat "_" mods ^ "_";;

(* HOL4 get_exn_conv: the stamp of the exception constructor name (an      *)
(* mlstring term) in the current environment                                *)
let basis_lookup_cons_tm =
  `ml_lookup_cons:(mlstring,mlstring)id->v sem_env->(num#stamp)option`;;

let get_exn_conv name =
  let tm = list_mk_comb (basis_lookup_cons_tm, [mk_Short name; get_curr_env ()]) in
  rand (rand (rand (concl (ml_prog_lookup_eq_conv tm))));;

(* ------------------------------------------------------------------------- *)
(* HOL4's EVAL on declarations (append_prog, append_dec, append_decs)        *)
(* ------------------------------------------------------------------------- *)

let basis_eval_thms = ref [unknown_loc_def];;

let basis_add_eval_thms thl = basis_eval_thms := !basis_eval_thms @ thl;;

let basis_eval_conv tm = PURE_REWRITE_CONV (!basis_eval_thms) tm;;

(* ------------------------------------------------------------------------- *)
(* trans                                                                     *)
(* ------------------------------------------------------------------------- *)

(* the port's name of a HOL4 constant of the current translation (names.tsv *)
(* through the translator's table of renamed HOL4 names)                    *)
let basis_hol_light_name hol4_name =
  let thy = ml_prog_current_theory () in
  try fst (find (fun (_,(t,h4,_)) -> t = thy && h4 = hol4_name) !tr_hol4_name_table)
  with Failure _ -> hol4_name;;

(* HOL4 SIMP_RULE std_ss [FUN_EQ_THM] on |- c = rhs: |- !x1 .. xn. c x1 .. *)
(* xn = rhs x1 .. xn, beta-reduced                                           *)
let basis_fun_eq_rule =
  let rec conv tm =
    if is_forall tm then BINDER_CONV conv tm
    else if is_eq tm && is_type (type_of (lhs tm)) &&
            fst (dest_type (type_of (lhs tm))) = "fun" then
      (GEN_REWRITE_CONV I [FUN_EQ_THM] THENC BINDER_CONV conv) tm
    else REFL tm in
  CONV_RULE (conv THENC TOP_DEPTH_CONV BETA_CONV);;

(* HOL4 PRECOND_CONV: c on the argument of every PRECONDITION *)
let basis_precond_conv c tm =
  if is_PRECONDITION tm then RAND_CONV c tm else NO_CONV tm;;

let trans ml_name rhs =
  let prefix = get_module_prefix () in
  let hol4_name = prefix ^ ml_prog_pick_name ml_name in
  let hol_name = basis_hol_light_name hol4_name in
  let tm = mk_eq (mk_var (hol_name, type_of rhs), rhs) in
  let def = new_definition tm in
  ignore (tr_save_thm (hol_name ^ "_def") def);
  next_ml_names := [ml_name];
  let v_thm = translate (basis_fun_eq_rule def) in
  let v_thm = CONV_RULE (DEPTH_CONV ETA_CONV) (REWRITE_RULE [def] v_thm) in
  let v_name = fst (dest_const (rand (concl v_thm))) in
  (* evaluate the precondition (HOL4 EVAL: the side definition unfolds) *)
  let c = lhs (concl def) in
  let pre_def = try get_pre (get_bare_v_thm c) with Failure _ -> TRUTH in
  let v_thm =
    if concl pre_def = `T` then v_thm else
    UNDISCH_ALL (CONV_RULE (ONCE_DEPTH_CONV (basis_precond_conv (REWRITE_CONV [pre_def])))
                           (DISCH_ALL v_thm)) in
  tr_save_thm (v_name ^ "_thm") v_thm;;

(* ------------------------------------------------------------------------- *)
(* append_prog, append_dec, append_decs                                     *)
(* ------------------------------------------------------------------------- *)

let append_prog tm =
  let tm = rhs (concl (basis_eval_conv tm)) in
  ml_prog_update (ml_prog_add_prog tm ml_prog_pick_name);;

let append_dec tm =
  let tm = rhs (concl (basis_eval_conv tm)) in
  ml_prog_update (ml_prog_add_dec tm ml_prog_pick_name);;

let append_decs tm =
  let tm = rhs (concl (basis_eval_conv tm)) in
  List.iter append_dec (dest_list tm);;
