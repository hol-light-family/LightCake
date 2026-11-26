(* ========================================================================= *)
(* ml_monad_translatorLib: port of HOL4                                      *)
(* translator/monadic/ml_monad_translatorLib.sml (CakeML v3479), the main    *)
(* part of the monadic translator: from HOL Light functions in the state-   *)
(* and-exception monad (ml_monadBase: st_ex_return, st_ex_bind, otherwise,  *)
(* raise_E, handle_E, the store accessors) to CakeML code, with             *)
(* certificates                                                              *)
(*   f_v_thm |- ArrowP ro (H,p) (PURE A) (MONAD B C) f f_v                   *)
(* (EvalM, MONAD, PURE, ArrowP, ArrowM of ml_monad_translator.ml).           *)
(*                                                                           *)
(* Entry points (HOL4's names and argument order): init_translation,         *)
(* start_static_init_fixed_store_translation,                                *)
(* start_dynamic_init_fixed_store_translation, add_raise_handle_functions,   *)
(* add_access_pattern, m2deep, m_translate, m_translate_run,                 *)
(* update_local_precondition, m_translation_extends.  Internal functions     *)
(* have the prefix mt_, helper theorems MTLIB_ (one session holds all        *)
(* files: the translator's own remove_Eq, check_inv, get_curr_env, ... must  *)
(* not be shadowed).                                                         *)
(*                                                                           *)
(* Differences from HOL4, forced by HOL Light:                               *)
(* - no mk_thm: HOL4's rm_fix rewrites with mk_thm'd equations to get terms; *)
(*   here a term traversal (EqSt a st and Eq a x become a); HOL4's           *)
(*   extract_precondition_rec builds its precondition terms by rewriting     *)
(*   with mk_thm'd equations: here the same rewrites with ASSUMEd equations  *)
(*   (only the conclusions are used, as in HOL4);                            *)
(* - no deletion of constants: HOL4's temporary code abbreviations           *)
(*   (____f_code____, abbrev_code, abbrev_nsLookup_code) are not made, the   *)
(*   code terms stay explicit;                                               *)
(* - no theory data: the monadic state is a component of ml_progLib's        *)
(*   translation snapshots (translation_register_state); m_translation_     *)
(*   extends name is translation_extends name;                               *)
(* - PMATCH (HOL4's patternMatchesLib case expressions: pmatch_m2deep,       *)
(*   prove_EvalMPatBind) is decision D5 and not ported (OPEN): the kit       *)
(*   compiles every match into case constants, translated by the case        *)
(*   lemmas (inst_case_thm).                                                 *)
(* ========================================================================= *)

needs "translator/monadic/ml_monadStoreLib.ml";;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Constants and types (HOL4 get_term, get_type)                             *)
(* ------------------------------------------------------------------------- *)

let mt_ffi_proj_ty = ms_ffi_proj_ty;;
let mt_poly_M_type = `:A->(B,C)exc#A`;;
let mt_exc_ty = `:(A,B)exc`;;
let mt_unit_ty = `:1`;;
let mt_bool_ty = bool_ty;;
let mt_a_ty = `:A` and mt_b_ty = `:B` and mt_c_ty = `:C`;;
let mt_venv_ty = venv_ty;;
let mt_env = tr_env;;
let mt_cl_env = tr_cl_env;;
let mt_v_var = tr_v_var;;
let mt_exp_var = mk_var ("exp", exp_ty);;
let mt_ro_var = `ro:bool`;;
let mt_p_var = ms_p_var;;

let mt_Eval_tm = `ml_Eval`;;
let mt_EvalM_tm =
  `EvalM:bool->v sem_env->REFS->exp->(REFS->REFS#(v list,v)result->bool)->
         (REFS->hprop)#((FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list))->bool`;;
let mt_MONAD_tm =
  `MONAD:(A->v->bool)->(B->v->bool)->(C->(A,B)exc#C)->C->C#(v list,v)result->bool`;;
let mt_PURE_tm = `PURE:(A->v->bool)->A->B->B#(v list,v)result->bool`;;
let mt_EqSt_tm = `EqSt:(A->B->B#(v list,v)result->bool)->B->A->B->B#(v list,v)result->bool`;;
let mt_ArrowM_tm =
  `ArrowM:bool->(REFS->hprop)#((FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list))->
          (A->REFS->REFS#(v list,v)result->bool)->(B->REFS->REFS#(v list,v)result->bool)->
          (A->B)->REFS->REFS#(v list,v)result->bool`;;
let mt_ArrowP_tm =
  `ArrowP:bool->(REFS->hprop)#((FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list))->
          (A->REFS->REFS#(v list,v)result->bool)->(B->REFS->REFS#(v list,v)result->bool)->
          (A->B)->v->bool`;;
let mt_FST_tm = `FST:A#B->A`;;
let mt_SND_tm = `SND:A#B->B`;;
let mt_LENGTH_v_tm = `LENGTH:(v)list->num`;;
let mt_EL_v_tm = `EL:num->(v)list->v`;;
let mt_Closure_tm = `Closure`;;
let mt_Fun_tm = `Fun`;;
let mt_run_tm = `ml_monadBase_run:(A->(B,C)exc#A)->A->(B,C)exc`;;
let mt_RARRAY_REL_tm = `RARRAY_REL:(A->v->bool)->v->A list->hprop`;;
let mt_ARRAY_REL_tm = `ARRAY_REL:(A->v->bool)->v->A list->hprop`;;
let mt_UNIT_TYPE_tm = `UNIT_TYPE`;;
let mt_CONTAINER_tm = `ml_CONTAINER:bool->bool`;;
let mt_emp_tm = `set_sep_emp:hprop`;;
let mt_T_tm = `T` and mt_F_tm = `F`;;

(* patterns *)
let mt_return_pat = `st_ex_return (x:B):A->(B,C)exc#A`;;
let mt_bind_pat = `st_ex_bind (x:A->(B,C)exc#A) (y:B->A->(D,C)exc#A)`;;
let mt_pure_seq_pat = `pure_seq (x:A) (y:B)`;;
let mt_otherwise_pat = `(x:A->(B,C)exc#A) otherwise y`;;
let mt_if_statement_pat = `if b then (x:A->(B,C)exc#A) else y`;;
let mt_Eval_pat = `ml_Eval env exp ((P:A->v->bool) res)`;;
let mt_Eval_pat2 = `ml_Eval env exp P`;;
let mt_EvalM_pat =
  `EvalM ro env (st:REFS) e (p:REFS->REFS#(v list,v)result->bool)
     (H:(REFS->hprop)#((FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)))`;;
let mt_var_assum = `ml_Eval env (Var n) ((a:A->v->bool) y)`;;
let mt_nsLookup_assum = `nsLookup (env:(mlstring,mlstring,A)namespace) name = opt`;;
let mt_lookup_cons_assum = `ml_lookup_cons name env = opt`;;
let mt_eqtype_assum = `EqualityType (A:B->v->bool)`;;
let mt_nsLookup_val_pat =
  `nsLookup (env:(mlstring,mlstring,v)namespace) (Short (vname:mlstring)) = SOME (loc:v)`;;
let mt_nsLookup_pat =
  `nsLookup (sem_env_v (env:v sem_env)) (Short name) = SOME (exp:v)`;;
let mt_LOOKUP_VAR_pat = `LOOKUP_VAR name env exp`;;
let mt_Eq_pat = `ml_Eq (a:A->v->bool) x`;;
let mt_EqSt_pat = `EqSt (a:A->B->B#(v list,v)result->bool) x`;;
let mt_PRECONDITION_pat = `ml_PRECONDITION x`;;
let mt_CONTAINER_pat = `ml_CONTAINER (b:bool)`;;
(* \name RI. ml_Eval env (Var (Short name)) RI *)
let mt_Eval_name_RI_abs = `\name (RI:v->bool). ml_Eval env (Var (Short name)) RI`;;

(* ------------------------------------------------------------------------- *)
(* The translator state (HOL4 translator_state)                              *)
(* ------------------------------------------------------------------------- *)

let mt_default_H0 = `(\refs:1. set_sep_emp:hprop)`;;

let mt_H_def = ref UNIT_TYPE_def;;
let mt_default_H = ref (mk_pair (mt_default_H0, mt_p_var));;
let mt_H = ref (mk_pair (mt_default_H0, mt_p_var));;
let mt_refs_type = ref mt_unit_ty;;
let mt_EXN_TYPE_def = ref UNIT_TYPE_def;;
let mt_EXN_TYPE = ref mt_UNIT_TYPE_tm;;
let mt_exn_type = ref mt_unit_ty;;
let mt_VALID_STORE_THM = ref (None : thm option);;
let mt_type_theories = ref (["ml_translator"] : string list);;
let mt_exn_handles = ref ([] : (term * thm) list);;
let mt_exn_raises = ref ([] : (term * thm) list);;
let mt_exn_functions_defs = ref ([] : (thm * thm) list);;
let mt_access_patterns = ref ([] : (term * thm) list);;
let mt_refs_functions_defs = ref ([] : (thm * thm) list);;
let mt_rarrays_functions_defs = ref ([] : (thm * thm * thm * thm * thm * thm) list);;
let mt_farrays_functions_defs = ref ([] : (thm * thm * thm * thm * thm) list);;
let mt_induction_helper_thms = ref ([] : (string * thm) list);;
let mt_local_environment_var_name = ref "%env";;
let mt_num_local_environment_vars = ref 0;;
let mt_local_state_init_H = ref false;;
let mt_store_pinv_def = ref (None : thm option);;
(* the specifications for dynamically initialised stores (HOL4: a Net) *)
let mt_dynamic_v_thms = ref ([] : (string * string * term * thm * thm * string option) list);;
let mt_dynamic_refs_bindings = ref ([] : (term * term) list);;
let mt_mem_derive_case_ref = ref ([] : (hol_type * thm) list);;

(* the translation snapshots of ml_progLib (HOL4 theory data) *)
let () =
  translation_register_state "ml_monad_translatorLib"
    (fun () ->
       let a1 = !mt_H_def and a2 = !mt_default_H and a3 = !mt_H and a4 = !mt_refs_type
       and a5 = !mt_EXN_TYPE_def and a6 = !mt_EXN_TYPE and a7 = !mt_exn_type
       and a8 = !mt_VALID_STORE_THM and a9 = !mt_type_theories and a10 = !mt_exn_handles
       and a11 = !mt_exn_raises and a12 = !mt_exn_functions_defs
       and a13 = !mt_access_patterns and a14 = !mt_refs_functions_defs
       and a15 = !mt_rarrays_functions_defs and a16 = !mt_farrays_functions_defs
       and a17 = !mt_local_state_init_H and a18 = !mt_store_pinv_def
       and a19 = !mt_dynamic_refs_bindings and a20 = !mt_mem_derive_case_ref
       and a21 = !mt_dynamic_v_thms in
       fun () ->
         mt_H_def := a1; mt_default_H := a2; mt_H := a3; mt_refs_type := a4;
         mt_EXN_TYPE_def := a5; mt_EXN_TYPE := a6; mt_exn_type := a7;
         mt_VALID_STORE_THM := a8; mt_type_theories := a9; mt_exn_handles := a10;
         mt_exn_raises := a11; mt_exn_functions_defs := a12; mt_access_patterns := a13;
         mt_refs_functions_defs := a14; mt_rarrays_functions_defs := a15;
         mt_farrays_functions_defs := a16; mt_local_state_init_H := a17;
         mt_store_pinv_def := a18; mt_dynamic_refs_bindings := a19;
         mt_mem_derive_case_ref := a20; mt_dynamic_v_thms := a21)
    (fun () ->
       mt_H_def := UNIT_TYPE_def; mt_default_H := mk_pair (mt_default_H0, mt_p_var);
       mt_H := !mt_default_H; mt_refs_type := mt_unit_ty;
       mt_EXN_TYPE_def := UNIT_TYPE_def; mt_EXN_TYPE := mt_UNIT_TYPE_tm;
       mt_exn_type := mt_unit_ty; mt_VALID_STORE_THM := None;
       mt_type_theories := ["ml_translator"]; mt_exn_handles := []; mt_exn_raises := [];
       mt_exn_functions_defs := []; mt_access_patterns := []; mt_refs_functions_defs := [];
       mt_rarrays_functions_defs := []; mt_farrays_functions_defs := [];
       mt_local_state_init_H := false; mt_store_pinv_def := None;
       mt_dynamic_refs_bindings := []; mt_mem_derive_case_ref := [];
       mt_dynamic_v_thms := []);;

(* ------------------------------------------------------------------------- *)
(* Helper functions                                                          *)
(* ------------------------------------------------------------------------- *)

(* HOL4 add_access_pattern: register an access function specification *)
let add_access_pattern th =
  let th' = tr_UNDISCH_ALL (SPEC_ALL (REWRITE_RULE [GSYM IMP_IMP] th)) in
  let tm = rand (rand (rator (concl th'))) in
  mt_access_patterns := (tm, th') :: !mt_access_patterns;
  th;;

let mt_the opt = match opt with Some x -> x | None -> failwith "the of NONE";;

let mt_mk_write name v env = mk_write (name, v, env);;

let mt_my_list_mk_comb = mb_my_list_mk_comb;;

(* HOL4 ISPECL_TM: repeated beta application of an abstraction *)
let mt_ISPECL_TM specs tm =
  let tm' = mt_my_list_mk_comb (tm, specs) in
  let rec beta_conv specs = match specs with
      [] -> ALL_CONV
    | _::xs -> RATOR_CONV (beta_conv xs) THENC BETA_CONV in
  rand (concl (beta_conv (rev specs) tm'));;

(* dest_monad_type `:A -> (B,C) exc # A` = (A, B, C) *)
let mt_dest_monad_type ty =
  let i = type_match mt_poly_M_type ty [] in
  (mb_type_subst i mt_a_ty, mb_type_subst i mt_b_ty, mb_type_subst i mt_c_ty);;

let mt_is_monad_type ty = can mt_dest_monad_type ty;;

let mt_list_dest = ms_list_dest;;

let mt_dest_args tm = snd (strip_comb tm);;

(* HOL4 disch_asms: |- hyp1 /\ hyp2 /\ ... ==> concl, or |- T ==> concl *)
let mt_disch_asms th =
  let discharged = PURE_REWRITE_RULE [IMP_IMP] (DISCH_ALL th) in
  if is_imp (concl discharged) then discharged else DISCH mt_T_tm discharged;;

(* the monad type of the current state and exception types *)
let mt_M_type ty =
  mk_fun_ty !mt_refs_type (mk_type ("prod", [mk_exc_type ty !mt_exn_type; !mt_refs_type]));;

let ISPEC_EvalM th = ISPEC !mt_H th;;
let ISPEC_EvalM_EXN_TYPE th = ISPEC !mt_EXN_TYPE th;;
let ISPEC_EvalM_MONAD th = ISPECL [!mt_H; !mt_EXN_TYPE] th;;
let ISPEC_EvalM_VALID th =
  match !mt_VALID_STORE_THM with
    Some store_th -> MP (ISPEC !mt_H th) store_th
  | None -> UNDISCH (ISPEC !mt_H th);;

(* instantiate ro (HOL4 INST_ro, INST_ro_tm) *)
let INST_ro th = if !mt_local_state_init_H then th else INST [mt_F_tm, mt_ro_var] th;;
let INST_ro_tm tm = if !mt_local_state_init_H then tm else vsubst [mt_F_tm, mt_ro_var] tm;;

(* the current environment: a fresh variable for a local store *)
let mt_get_curr_env () =
  if !mt_local_state_init_H then
    (mt_num_local_environment_vars := !mt_num_local_environment_vars + 1;
     mk_var (!mt_local_environment_var_name ^ string_of_int !mt_num_local_environment_vars,
             mt_venv_ty))
  else get_curr_env ();;

let mk_PURE x = tr_mk_icomb (inst [!mt_refs_type, mt_b_ty] mt_PURE_tm) x;;

(* the parameters of Eval or EvalM (HOL4 get_Eval_arg, get_Eval_env,       *)
(* get_Eval_exp, get_EvalM_state)                                           *)
let mt_is_Eval_tm e = is_const (fst (strip_comb e)) &&
                      fst (dest_const (fst (strip_comb e))) = "ml_Eval";;
let get_Eval_arg e = if mt_is_Eval_tm e then rand (rand e) else rand (rand (rator e));;
let get_Eval_env e = if mt_is_Eval_tm e then rand (rator (rator e))
                     else rand (rator (rator (rator (rator e))));;
let get_Eval_exp e = if mt_is_Eval_tm e then rand (rator e) else rand (rator (rator e));;
let get_EvalM_state tm = rand (rator (rator (rator tm)));;

(* the dynamic specifications (HOL4 lookup_dynamic_v_thm) *)
let lookup_dynamic_v_thm tm =
  let (_, ml_name, _, th, _, _) =
    find (fun (_,_,_,x,_,_) -> rand (rator (concl x)) = tm) !mt_dynamic_v_thms in
  let th = MATCH_MP Eval_Var_Short th in
  let v_name = mk_mlstring ml_name in
  tr_UNDISCH_ALL (SPECL [v_name; mt_env] th);;

(* ------------------------------------------------------------------------- *)
(* The refinement invariants of monad and arrow types (HOL4 get_m_type_inv, *)
(* get_arrow_type_inv, smart_get_type_inv, get_EqSt_var)                     *)
(* ------------------------------------------------------------------------- *)

let get_m_type_inv ty =
  let (_, ret, _) = mt_dest_monad_type ty in
  let ri = get_type_inv ret in
  let monad = inst [!mt_refs_type, mt_c_ty] mt_MONAD_tm in
  tr_list_mk_icomb monad [ri; !mt_EXN_TYPE];;

let mt_REFS_ty = `:REFS`;;
let mt_ArrowM_ro () = mk_comb (inst [!mt_refs_type, mt_REFS_ty] mt_ArrowM_tm, mt_ro_var);;

let rec get_arrow_type_inv ty =
  if mt_is_monad_type ty then get_m_type_inv ty else
  let (ty1, ty2) = dest_fun_ty ty in
  let i1 = try get_arrow_type_inv ty1
           with Failure _ | Unsupported_type _ -> mk_PURE (get_type_inv ty1) in
  let i2 = get_arrow_type_inv ty2 in
  mt_my_list_mk_comb (mt_ArrowM_ro (), [!mt_H; i1; i2]);;

let smart_get_type_inv ty =
  if not (mt_is_monad_type ty) && can get_arrow_type_inv ty then
    rand (rand (concl (ONCE_REWRITE_CONV [ArrowM_def] (get_arrow_type_inv ty))))
  else get_type_inv ty;;

let mt_H_pat_var =
  `H:(REFS->hprop)#((FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list))`;;
let mt_ArrowP_PURE_pat =
  `ArrowP ro (H:(REFS->hprop)#((FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)))
     (a:A->REFS->REFS#(v list,v)result->bool) (PURE (b:B->v->bool))`;;
let mt_ArrowP_EqSt_pat =
  `ArrowP ro (H:(REFS->hprop)#((FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)))
     (EqSt (a:A->REFS->REFS#(v list,v)result->bool) st)
     (b:B->REFS->REFS#(v list,v)result->bool)`;;

let mt_can_match pat tm = can (term_match [] pat) tm;;

let rec get_EqSt_var tm =
  if mt_can_match mt_ArrowP_PURE_pat tm then get_EqSt_var (rand (rand tm))
  else if mt_can_match mt_ArrowP_EqSt_pat tm then Some (rand (rand (rator tm)))
  else None;;

(* ------------------------------------------------------------------------- *)
(* Exceptions: the specifications of the raise and handle functions          *)
(* (HOL4 prove_raise_spec, prove_handle_spec, add_raise_handle_functions)    *)
(* ------------------------------------------------------------------------- *)

let mt_exp_ty = exp_ty;;
let mt_ml_id_ty = ml_id_ty;;
let mt_v_list_ty = `:(v)list`;;
let mt_vbool_ty = `:v->bool`;;
let mt_num_ty = `:num`;;

(* the stamps of the exception invariant without HOL4's K tags            *)
let mt_clean_exn_def th = PURE_REWRITE_RULE [K_THM] th;;

(* from LENGTH l = n (a numeral): l = [x1; ..; xn], substituted *)
(* (the goal: LENGTH l = n ==> t) *)
let mt_length_cases_tac =
  CONV_TAC (LAND_CONV (RAND_CONV (REDEPTH_CONV num_CONV))) THEN
  REWRITE_TAC [LENGTH_EQ_CONS; LENGTH_EQ_NIL; LEFT_IMP_EXISTS_THM; IMP_CONJ] THEN
  REPEAT GEN_TAC THEN REPEAT (DISCH_THEN SUBST1_TAC);;

let mt_prove_raise_spec exn_ri_def exn_ri_tm (raise_fun_def, cons, stamp) =
  let fun_tm = fst (strip_comb (lhs (snd (strip_forall (concl raise_fun_def))))) in
  let exn_param_types = fst (mb_dest_fun_type (type_of cons)) in
  let refin_invs = map smart_get_type_inv exn_param_types in
  let raise_fun = lhs (snd (strip_forall (concl raise_fun_def))) in
  let e = rand (fst (dest_pair (snd (dest_abs (rhs (snd (strip_forall (concl raise_fun_def)))))))) in
  let cons_params = snd (strip_comb e) in
  let eval_conds = tr_mk_list (map mk_comb (zip refin_invs cons_params), mt_vbool_ty) in
  let arity = length cons_params in
  let arity_tm = mk_small_numeral arity in
  let exprs_vars = mb_mk_list_vars_same "_expr" mt_exp_ty arity in
  let exprs = tr_mk_list (exprs_vars, mt_exp_ty) in
  (* instantiate the raise specification *)
  let cv = mk_var (mk_cons_name cons, mt_ml_id_ty) in
  let raise_spec = ISPECL [cv; stamp; exn_ri_tm; eval_conds; arity_tm; e; exprs; raise_fun]
                     EvalM_raise in
  let free_vars = fst (strip_forall (concl raise_spec)) in
  let raise_spec = SPEC_ALL raise_spec in
  (* the exception invariant assumption *)
  let take_assumption th = fst (dest_imp (concl th)) in
  let exn_ri_assum = take_assumption raise_spec in
  let tac =
    GEN_TAC THEN mt_length_cases_tac THEN
    REWRITE_TAC [ZIP; MAP; LIST_CONJ_def; HD; TL] THEN
    CONV_TAC (DEPTH_CONV GEN_BETA_CONV) THEN
    REWRITE_TAC [exn_ri_def; injectivity "v"; CONS_11] THEN MESON_TAC[] in
  let exn_ri_lemma = prove (exn_ri_assum, tac) in
  let raise_spec = MP raise_spec exn_ri_lemma in
  (* the trivial assumptions *)
  let prove_assumption th =
    let a = take_assumption th in
    let c = REWRITE_CONV [raise_fun_def; LENGTH] THENC DEPTH_CONV BETA_CONV THENC
            NUM_REDUCE_CONV THENC REWRITE_CONV [] in
    MP th (EQT_ELIM (c a)) in
  let raise_spec = prove_assumption (prove_assumption (prove_assumption raise_spec)) in
  (* rewrite, generalise *)
  let raise_spec = CONV_RULE (DEPTH_CONV GEN_BETA_CONV)
                     (REWRITE_RULE [LIST_CONJ_def; MAP; ZIP; HD; TL] raise_spec) in
  let raise_spec = REWRITE_RULE [GSYM IMP_IMP] raise_spec in
  let raise_spec = GENL free_vars raise_spec in
  let raise_spec = itlist (fun (x,y) th -> GENL [x; y] th) (zip cons_params exprs_vars)
                     raise_spec in
  let thm_name = "EvalM_" ^ fst (dest_const fun_tm) in
  let raise_spec = tr_save_thm thm_name raise_spec in
  Format.print_string ("Saved theorem __ \"" ^ thm_name ^ "\"\n");
  raise_spec;;

let mt_case_thms exn_type =
  [case_def (fst (dest_type exn_type)); case_def "prod"; case_def "exc"];;

let mt_handle_spec_inst exn_ri_def exn_ri_tm (handle_fun_def, cons, stamp) =
  (* rename the variables of handle_fun_def x1, x2 *)
  let handle_fun_def =
    let vars = fst (strip_forall (concl handle_fun_def)) in
    let new_vars = mb_mk_list_vars "x" (map type_of vars) in
    GENL new_vars (SPECL new_vars handle_fun_def) in
  let handle_fun = lhs (snd (strip_forall (concl handle_fun_def))) in
  let exn_type = hd (snd (dest_type (type_of exn_ri_tm))) in
  let all_cons = mb_constructors_of exn_type in
  let bool_case = mb_case_const_of exn_type bool_ty in
  (* CORRECT_CONS = \e. case e of cons .. => T | _ => F *)
  let correct_cons =
    let mk_case_bool_fun c =
      let types = fst (mb_dest_fun_type (type_of c)) in
      let vars = mb_mk_list_vars "e" types in
      list_mk_abs (vars, if c = cons then mt_T_tm else mt_F_tm) in
    let e_var = mk_var ("e", exn_type) in
    mk_abs (e_var, list_mk_comb (bool_case, e_var :: map mk_case_bool_fun all_cons)) in
  let params_types = fst (mb_dest_fun_type (type_of cons)) in
  let arity = length params_types in
  let arity_tm = mk_small_numeral arity in
  let params_vars = mb_mk_list_vars "_x" params_types in
  (* PARAMS_CONDITIONS = \_E _paramsv. case _E of cons _x1 .. => LENGTH .. /\ .. | _ => F *)
  let params_conditions =
    let paramsv_var = mk_var ("_paramsv", mt_v_list_ty) in
    let length_cond = mk_eq (mk_comb (mt_LENGTH_v_tm, paramsv_var), arity_tm) in
    let mk_type_condition (var, i) =
      let ty_inv = get_type_inv (type_of var) in
      list_mk_comb (ty_inv, [var; list_mk_comb (mt_EL_v_tm, [mk_small_numeral i; paramsv_var])]) in
    let type_conditions = map mk_type_condition (zip params_vars (0 -- (arity - 1))) in
    let conditions = ms_list_mk (fun (a,b) -> mk_conj (a,b))
                       (length_cond :: type_conditions) mt_T_tm in
    let conditions_fun = list_mk_abs (params_vars, conditions) in
    let mk_case_bool_fun c =
      let types = fst (mb_dest_fun_type (type_of c)) in
      if c = cons then conditions_fun
      else list_mk_abs (mb_mk_list_vars "_x" types, mt_F_tm) in
    let e_var = mk_var ("_E", exn_type) in
    list_mk_abs ([e_var; paramsv_var],
                 list_mk_comb (bool_case, e_var :: map mk_case_bool_fun all_cons)) in
  (* the handle function in another form *)
  let (alt_handle_fun, alt_x1, alt_x2) =
    let x1_var = hd (snd (strip_comb handle_fun)) in
    let handle_fun_def_rhs = rhs (snd (strip_forall (concl handle_fun_def))) in
    let (state_var1, case_tm1) = dest_abs handle_fun_def_rhs in
    let case_tm0 = rator case_tm1 in
    let (res_var_state_var2, case_tm2) = strip_abs (rand case_tm1) in
    let (res_var, state_var2) = (el 0 res_var_state_var2, el 1 res_var_state_var2) in
    let case_tm3 = rator case_tm2 in
    let (e_var, alt_x2_body) = dest_abs (rand case_tm2) in
    let alt_x2_tm = list_mk_abs ([e_var; state_var2], alt_x2_body) in
    let alt_x2_var = mk_var ("x2", type_of alt_x2_tm) in
    let alt_handle_fun = list_mk_comb (alt_x2_var, [e_var; state_var2]) in
    let alt_handle_fun = mk_abs (e_var, alt_handle_fun) in
    let alt_handle_fun = mk_comb (case_tm3, alt_handle_fun) in
    let alt_handle_fun = list_mk_abs ([res_var; state_var2], alt_handle_fun) in
    let alt_handle_fun = mk_comb (case_tm0, alt_handle_fun) in
    let alt_handle_fun = list_mk_abs ([x1_var; alt_x2_var; state_var1], alt_handle_fun) in
    (alt_handle_fun, x1_var, alt_x2_tm) in
  (* a2 in another form *)
  let a2_alt =
    let state_type = !mt_refs_type in
    let a2_type = mb_mk_fun_type (state_type :: params_types, bool_ty) in
    let a2_var = mk_var ("a2", a2_type) in
    let e_var = mk_var ("E", exn_type) in
    let state_var = mk_var ("st", state_type) in
    let mk_condition c =
      let types = fst (mb_dest_fun_type (type_of c)) in
      let vars = mb_mk_list_vars "e" types in
      if c = cons then list_mk_abs (vars, list_mk_comb (a2_var, state_var :: vars))
      else list_mk_abs (vars, mt_F_tm) in
    list_mk_abs ([state_var; e_var],
                 list_mk_comb (bool_case, e_var :: map mk_condition all_cons)) in
  (* instantiate the specification *)
  let cv = mk_var (mk_cons_name cons, mt_ml_id_ty) in
  let handle_spec = ISPECL [cv; stamp; correct_cons; params_conditions; exn_ri_tm;
                            alt_handle_fun; alt_x1; alt_x2; arity_tm] EvalM_handle in
  let a2v = fst (dest_forall (concl handle_spec)) in
  let ty_subst = type_match (type_of a2_alt) (type_of a2v) [] in
  let handle_spec = SPEC (inst ty_subst a2_alt) handle_spec in
  let free_vars = fst (strip_forall (concl handle_spec)) in
  let handle_spec = SPECL free_vars handle_spec in
  (handle_spec, handle_fun_def, handle_fun, free_vars, params_types, arity);;

let mt_list_mk_imp (hs, c) = itlist (fun h t -> mk_imp (h, t)) hs c;;

(* l = [x1; ..; xn] from an assumption LENGTH l = n, substituted everywhere *)
let mt_length_subst_tac (asl,w) =
  let th = snd (find (fun (_,th) -> let c = concl th in is_eq c && is_comb (lhs c) &&
                     (try fst (dest_const (rator (lhs c))) = "LENGTH" with Failure _ -> false) &&
                     is_var (rand (lhs c)) && is_numeral (rhs c)) asl) in
  (UNDISCH_TAC (concl th) THEN
   CONV_TAC (LAND_CONV (RAND_CONV (REDEPTH_CONV num_CONV))) THEN
   REWRITE_TAC [LENGTH_EQ_CONS; LENGTH_EQ_NIL; LEFT_IMP_EXISTS_THM; IMP_CONJ] THEN
   REPEAT GEN_TAC THEN REPEAT (DISCH_THEN SUBST_ALL_TAC)) (asl,w);;

(* ?paramsv. ev = Conv _ paramsv /\ ..: the parameters of an assumption    *)
(* ev = Conv _ l                                                             *)
let mt_conv_assum asl =
  snd (find (fun (_,th) -> let c = concl th in is_eq c &&
              (try fst (dest_const (fst (strip_comb (rhs c)))) = "Conv"
               with Failure _ -> false)) asl);;

let mt_exists_paramsv_tac (asl,w) =
  let l = rand (rhs (concl (mt_conv_assum asl))) in
  (EXISTS_TAC l THEN ASM_REWRITE_TAC [] THEN
   CONV_TAC (DEPTH_CONV (LENGTH_CONV ORELSEC EL_CONV)) THEN ASM_REWRITE_TAC []) (asl,w);;

let mt_exists_paramsv_stamp_tac (asl,w) =
  let r = rhs (concl (mt_conv_assum asl)) in
  let l = rand r and k = rand (rand (rand (rator r))) in
  (MAP_EVERY EXISTS_TAC [l; k] THEN ASM_REWRITE_TAC [] THEN CONV_TAC NUM_REDUCE_CONV) (asl,w);;

(* a contradiction from x1 s = (M_failure E0, s0) and an assumption           *)
(* !E s1. CORRECT_CONS E ==> ~(x1 s = (M_failure E, s1)) (HOL4: fs[])        *)
let mt_contr_tac cthms (asl,w) =
  let eqth = snd (find (fun (_,th) -> let c = concl th in is_eq c && is_pair (rhs c) &&
                         (try fst (dest_const (rator (fst (dest_pair (rhs c))))) = "M_failure"
                          with Failure _ -> false)) asl) in
  let (f, s0) = dest_pair (rhs (concl eqth)) in
  let e0 = rand f in
  (FIRST_X_ASSUM (fun th -> if is_forall (concl th) then MP_TAC (SPECL [e0; s0] th)
                            else failwith "mt_contr_tac") THEN
   REWRITE_TAC cthms) (asl,w);;

let mt_prove_handle_spec exn_ri_def exn_ri_tm (handle_fun_def0, cons, stamp) =
  let (handle_spec, handle_fun_def, handle_fun, free_vars, params_types, arity) =
    mt_handle_spec_inst exn_ri_def exn_ri_tm (handle_fun_def0, cons, stamp) in
  let exn_type = hd (snd (dest_type (type_of exn_ri_tm))) in
  let cthms = mt_case_thms exn_type in
  let e_var = mk_var ("E", exn_type) in
  let take_assumption th = fst (dest_imp (concl th)) in
  let beta = CONV_TAC (DEPTH_CONV BETA_CONV) in
  (* branch handle *)
  let l1 = prove (take_assumption handle_spec,
                  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC cthms) in
  let handle_spec = MP handle_spec l1 in
  (* branch let through *)
  let l2 = prove (take_assumption handle_spec,
                  REPEAT STRIP_TAC THEN beta THEN
                  RULE_ASSUM_TAC (CONV_RULE (DEPTH_CONV BETA_CONV)) THEN
                  REPEAT TOP_CASE_TAC THEN FS cthms THEN
                  FIRST [mt_contr_tac cthms; ASM_MESON_TAC cthms]) in
  let handle_spec = MP handle_spec l2 in
  (* refinement invariant equality *)
  let l3 = prove (take_assumption handle_spec,
                  GEN_TAC THEN CASES_ON e_var THEN beta THEN REWRITE_TAC (exn_ri_def :: cthms) THEN
                  REPEAT STRIP_TAC THEN mt_exists_paramsv_tac) in
  let handle_spec = MP handle_spec l3 in
  (* refinement invariant inequality *)
  let l4 = prove (take_assumption handle_spec,
                  GEN_TAC THEN CASES_ON e_var THEN beta THEN REWRITE_TAC (exn_ri_def :: cthms) THEN
                  REPEAT STRIP_TAC THEN mt_exists_paramsv_stamp_tac) in
  let handle_spec = MP handle_spec l4 in
  (* replace the variables E and paramsv of the EvalM assumption by the     *)
  (* constructor's arguments and a list of values                           *)
  let remove_imp t = snd (dest_imp t) in
  let evalm_assum = fst (dest_imp (remove_imp (remove_imp (remove_imp (concl handle_spec))))) in
  let evalm_assum2 = snd (dest_conj evalm_assum) in
  let (vars, body2) = strip_forall evalm_assum2 in
  let (e_v, pv_v) = (el 1 vars, el 2 vars) in
  let v_vars = mb_mk_list_vars_same "v" v_ty arity in
  let e_params_vars = mb_mk_list_vars "e" params_types in
  let e_eq = mk_eq (e_v, list_mk_comb (cons, e_params_vars)) in
  let params_v_eq = mk_eq (pv_v, tr_mk_list (v_vars, v_ty)) in
  let alt2 = list_mk_forall (vars @ e_params_vars @ v_vars,
                             mt_list_mk_imp ([e_eq; params_v_eq], body2)) in
  let pc = fst (dest_imp body2) in
  let ex_lemma = prove (list_mk_forall ([e_v; pv_v],
                          mk_imp (pc, list_mk_exists (e_params_vars @ v_vars,
                                                      mk_conj (e_eq, params_v_eq)))),
                        GEN_TAC THEN CASES_ON e_var THEN beta THEN REWRITE_TAC cthms THEN
                        REPEAT STRIP_TAC THEN mt_length_subst_tac THEN MESON_TAC[]) in
  (* HOL4 rewrites with the equation evalm_assum2 = alt2; the assumption is *)
  (* an antecedent, so alt2 ==> evalm_assum2 is enough (and needs no MESON)  *)
  let imp2 = prove (mk_imp (alt2, evalm_assum2),
    DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
    (fun (asl,w as g) ->
       let pcth = snd (find (fun (_,th) -> can (MATCH_MP ex_lemma) th) asl) in
       let exth = MATCH_MP ex_lemma pcth in
       let (evs, _) = strip_exists (concl exth) in
       let rec choose th k =
         if is_exists (concl th) then
           let (v, _) = dest_exists (concl th) in X_CHOOSE_THEN v (fun th' -> choose th' k) th
         else k th in
       choose exth (fun eqs ->
         FIRST_X_ASSUM (fun th -> if aconv (concl th) alt2 then
                                    MATCH_MP_TAC (PURE_REWRITE_RULE [IMP_IMP] th)
                                  else failwith "") THEN
         MAP_EVERY EXISTS_TAC evs THEN
         REPEAT CONJ_TAC THEN
         FIRST [ACCEPT_TAC (CONJUNCT1 eqs); ACCEPT_TAC (CONJUNCT2 eqs);
                FIRST_ASSUM ACCEPT_TAC]) g)) in
  let handle_spec =
    let th = UNDISCH (UNDISCH (UNDISCH handle_spec)) in
    let hs = map (fun th' -> fst (dest_imp (concl th')))
               [handle_spec; UNDISCH handle_spec; UNDISCH (UNDISCH handle_spec)] in
    let (ab, _) = dest_imp (concl th) in
    let (a, _) = dest_conj ab in
    let new_ab = mk_conj (a, alt2) in
    let nth = ASSUME new_ab in
    let th = DISCH new_ab (MP th (CONJ (CONJUNCT1 nth) (MP imp2 (CONJUNCT2 nth)))) in
    itlist DISCH hs th in
  (* eliminate E in the generated precondition *)
  let pre = fst (dest_imp (remove_imp (remove_imp (remove_imp (remove_imp
              (concl handle_spec)))))) in
  let (pvars, pre_body) = strip_forall pre in
  let (st_v, ep) = (el 0 pvars, el 1 pvars) in
  let (pre1, pre2) = dest_conj pre_body in
  let e_with_params = list_mk_comb (cons, e_params_vars) in
  let pre_alt = list_mk_forall (st_v :: e_params_vars,
                                mk_conj (pre1, vsubst [e_with_params, ep] pre2)) in
  (* the precondition is an antecedent too: pre_alt ==> pre is enough *)
  let pre_imp = prove (mk_imp (pre_alt, pre),
    DISCH_TAC THEN REPEAT GEN_TAC THEN CASES_ON e_var THEN beta THEN
    REWRITE_TAC (ml_CONTAINER_def :: cthms) THEN
    RULE_ASSUM_TAC (CONV_RULE (DEPTH_CONV BETA_CONV) o REWRITE_RULE (ml_CONTAINER_def :: cthms)) THEN
    FIRST [FIRST_ASSUM MATCH_ACCEPT_TAC;
           FIRST_ASSUM (ACCEPT_TAC o CONJUNCT1 o SPEC_ALL);
           ASM_MESON_TAC []]) in
  let handle_spec =
    let th = UNDISCH (UNDISCH (UNDISCH (UNDISCH handle_spec))) in
    let hs = map (fun th' -> fst (dest_imp (concl th')))
               [handle_spec; UNDISCH handle_spec; UNDISCH (UNDISCH handle_spec);
                UNDISCH (UNDISCH (UNDISCH handle_spec))] in
    let th = DISCH pre_alt (MP th (MP pre_imp (ASSUME pre_alt))) in
    itlist DISCH hs th in
  (* rewrite *)
  let handle_spec = CONV_RULE (DEPTH_CONV BETA_CONV) handle_spec in
  let handle_spec = CAKE_SIMP_RULE (cthms @ [LENGTH; EL; HD; TL]) handle_spec in
  let handle_spec = CONV_RULE (DEPTH_CONV ETA_CONV) handle_spec in
  let handle_spec = PURE_REWRITE_RULE [GSYM handle_fun_def] handle_spec in
  let handle_spec = PURE_REWRITE_RULE [GSYM IMP_IMP] handle_spec in
  (* check *)
  let f = rand (rand (rator (concl (tr_UNDISCH_ALL handle_spec)))) in
  (if aconv f handle_fun then () else
   failwith "prove_handle_spec: the generated spec does not have the proper form");
  let handle_spec = GENL free_vars handle_spec in
  let fun_tm = fst (strip_comb handle_fun) in
  let thm_name = "EvalM_" ^ fst (dest_const fun_tm) in
  let handle_spec = tr_save_thm thm_name handle_spec in
  Format.print_string ("Saved theorem __ \"" ^ thm_name ^ "\"\n");
  handle_spec;;

let add_raise_handle_functions exn_functions exn_ri_def =
  let exn_ri_def = mt_clean_exn_def exn_ri_def in
  let (raise_functions, handle_functions) = unzip exn_functions in
  (* the information of the exception invariant *)
  let exn_ri_cases = CONJUNCTS exn_ri_def in
  let exn_ri_tm = rator (rator (lhs (snd (strip_forall (concl (hd exn_ri_cases)))))) in
  let exn_ri_pats = map (fun th -> rand (rator (lhs (snd (strip_forall (concl th))))))
                      exn_ri_cases in
  let exn_ri_cons = map (fun t -> fst (strip_comb t)) exn_ri_pats in
  let exn_ri_params_types = map (fun c -> fst (mb_dest_fun_type (type_of c))) exn_ri_cons in
  let safe_register_type ty =
    if can get_type_inv ty then () else register_type ty in
  let _ = mapfilter safe_register_type (flat exn_ri_params_types) in
  let exn_ri_decomposed_rhs =
    map (fun th -> mt_list_dest dest_conj (snd (strip_exists (rhs (snd (strip_forall
                     (concl th))))))) exn_ri_cases in
  let exn_ri_deep_cons = map (fun l -> rator (rand (hd l))) exn_ri_decomposed_rhs in
  let exn_ri_stamps = map (fun t -> rand (rand (rand t))) exn_ri_deep_cons in
  let exn_info = zip exn_ri_cons exn_ri_stamps in
  let exn_type = hd (snd (dest_type (type_of exn_ri_tm))) in
  (* the raise definitions with their constructors and stamps *)
  let raise_funct_pairs =
    map (fun x -> (x, fst (strip_comb (rand (fst (dest_pair (snd (dest_abs
                     (rhs (snd (strip_forall (concl x))))))))))))
        raise_functions in
  let raise_info =
    map (fun (d, tm) -> tryfind (fun (x1, x2) -> if x1 = tm then (d, x1, x2) else fail ())
                          exn_info) raise_funct_pairs in
  let raise_specs = map (mt_prove_raise_spec exn_ri_def exn_ri_tm) raise_info in
  (* the handle definitions with their constructors *)
  let get_handle_cons handle_fun_def =
    let t1 = rhs (snd (strip_forall (concl handle_fun_def))) in
    let t2 = rand (snd (dest_abs t1)) in
    let t3 = rand (snd (strip_abs t2)) in
    let exn_cases = snd (dest_abs t3) in
    let cases_list = tl (snd (strip_comb exn_cases)) in
    let cases_list = map (fun t -> snd (strip_abs t)) cases_list in
    let cases_cons = mb_constructors_of exn_type in
    let cases_pairs = zip cases_cons cases_list in
    let handled = find (fun (_, y) -> not (is_pair y)) cases_pairs in
    (handle_fun_def, fst handled) in
  let handle_funct_pairs = map get_handle_cons handle_functions in
  let handle_info =
    map (fun (d, tm) -> tryfind (fun (x1, x2) -> if x1 = tm then (d, x1, x2) else fail ())
                          exn_info) handle_funct_pairs in
  let handle_specs = map (mt_prove_handle_spec exn_ri_def exn_ri_tm) handle_info in
  (* store the proved theorems *)
  let extract_pattern th =
    let pat = rand (rand (rator (snd (splitlist dest_imp (snd (strip_forall (concl th))))))) in
    (pat, th) in
  mt_exn_raises := map extract_pattern raise_specs @ !mt_exn_raises;
  mt_exn_handles := map extract_pattern handle_specs @ !mt_exn_handles;
  zip raise_specs handle_specs;;

(* ------------------------------------------------------------------------- *)
(* Initialisation of the translation (HOL4 compute_dynamic_refs_bindings,   *)
(* init_translation, start_static_init_fixed_store_translation,             *)
(* start_dynamic_init_fixed_store_translation)                              *)
(* ------------------------------------------------------------------------- *)

let mt_compute_dynamic_refs_bindings all_access_specs =
  let store_vars = frees (fst (dest_pair !mt_H)) in
  let get_dynamic_init_bindings spec =
    let spec = tr_UNDISCH_ALL (SPEC_ALL spec) in
    let lookup_assums = filter (mt_can_match mt_nsLookup_val_pat) (hyp spec) in
    let get_name_loc tm = (rand (rand (rand (rator tm))), rand (rand tm)) in
    filter (fun (_, y) -> mem y store_vars) (map get_name_loc lookup_assums) in
  let all_bindings = flat (map get_dynamic_init_bindings all_access_specs) in
  let store_varsl = snd (strip_comb (fst (dest_pair !mt_H))) in
  let store_varsl = filter (fun t -> type_of t = v_ty) store_varsl in
  map (fun x -> (fst (find (fun (_, v) -> v = x) all_bindings), x)) store_varsl;;

let init_translation (monad_translation_params : monadic_translation_parameters)
      refs_funs_defs rarrays_funs_defs farrays_funs_defs exn_functions
      store_pred_exists_thm exn_type_def add_type_theories store_pinv_def_opt =
  let store_pred_def = monad_translation_params.store_pred_def in
  let all_refs_specs = flat (map (fun (x, y) -> [x; y]) monad_translation_params.refs_specs) in
  let all_rarrays_specs =
    flat (map (fun (x1, x2, x3, x4) -> [x1; x2; x3; x4]) monad_translation_params.rarrays_specs) in
  let all_farrays_specs =
    flat (map (fun (x1, x2, x3) -> [x1; x2; x3]) monad_translation_params.farrays_specs) in
  let all_access_specs = all_refs_specs @ all_rarrays_specs @ all_farrays_specs in
  let get_access_info spec =
    let pat = rand (rand (rator (snd (splitlist dest_imp (snd (strip_forall (concl spec))))))) in
    (pat, tr_UNDISCH_ALL (SPEC_ALL spec)) in
  let exn_type_def = mt_clean_exn_def exn_type_def in
  mt_H_def := store_pred_def;
  mt_default_H := mk_pair (lhs (snd (strip_forall (concl store_pred_def))), mt_p_var);
  mt_H := !mt_default_H;
  mt_local_state_init_H := (frees (fst (dest_pair !mt_H)) <> []);
  mt_refs_type := fst (dest_fun_ty (type_of (fst (dest_pair !mt_H))));
  mt_EXN_TYPE_def := exn_type_def;
  mt_EXN_TYPE := fst (strip_comb (lhs (snd (strip_forall (concl (hd (CONJUNCTS exn_type_def)))))));
  mt_exn_type := fst (dest_fun_ty (type_of !mt_EXN_TYPE));
  mt_VALID_STORE_THM := store_pred_exists_thm;
  mt_type_theories := add_type_theories @ ["ml_translator"];
  mt_store_pinv_def := store_pinv_def_opt;
  mt_exn_raises := [];
  mt_exn_handles := [];
  mt_exn_functions_defs := exn_functions;
  mt_access_patterns := map get_access_info all_access_specs;
  mt_refs_functions_defs := refs_funs_defs;
  mt_rarrays_functions_defs := rarrays_funs_defs;
  mt_farrays_functions_defs := farrays_funs_defs;
  mt_mem_derive_case_ref := [];
  mt_dynamic_v_thms := [];
  mt_dynamic_refs_bindings :=
    (if !mt_local_state_init_H then mt_compute_dynamic_refs_bindings all_access_specs
     else []);;

let start_static_init_fixed_store_translation refs_init_list rarrays_init_list
      farrays_init_list store_hprop_name state_type exn_ri_def exn_functions
      add_type_theories store_pinv_opt extra_hprop =
  let (monad_translation_params, store_trans_result) =
    translate_static_init_fixed_store refs_init_list rarrays_init_list farrays_init_list
      store_hprop_name state_type exn_ri_def store_pinv_opt extra_hprop in
  let refs_funs_defs = map (fun (_,_,x,y) -> (x,y)) refs_init_list in
  let rarrays_funs_defs =
    map (fun (_,_,x1,x2,x3,x4,x5,x6) -> (x1,x2,x3,x4,x5,x6)) rarrays_init_list in
  let farrays_funs_defs =
    map (fun (_,_,x1,x2,x3,x4,x5) -> (x1,x2,x3,x4,x5)) farrays_init_list in
  let store_pinv_def_opt = match store_pinv_opt with Some (d,_) -> Some d | None -> None in
  let store_pred_exists_thm = Some store_trans_result.store_pred_exists_thm in
  init_translation monad_translation_params refs_funs_defs rarrays_funs_defs
    farrays_funs_defs exn_functions store_pred_exists_thm exn_ri_def add_type_theories
    store_pinv_def_opt;
  let exn_specs = if exn_functions <> [] then add_raise_handle_functions exn_functions exn_ri_def
                  else [] in
  (monad_translation_params, store_trans_result, exn_specs);;

let start_dynamic_init_fixed_store_translation refs_manip_list rarrays_manip_list
      farrays_manip_list store_hprop_name state_type exn_ri_def exn_functions
      add_type_theories store_pinv_def_opt =
  let monad_translation_params =
    translate_dynamic_init_fixed_store refs_manip_list rarrays_manip_list farrays_manip_list
      store_hprop_name state_type exn_ri_def store_pinv_def_opt in
  let refs_funs_defs = map (fun (_,x,y) -> (x,y)) refs_manip_list in
  let rarrays_funs_defs =
    map (fun (_,x1,x2,x3,x4,x5,x6) -> (x1,x2,x3,x4,x5,x6)) rarrays_manip_list in
  let farrays_funs_defs =
    map (fun (_,x1,x2,x3,x4,x5) -> (x1,x2,x3,x4,x5)) farrays_manip_list in
  init_translation monad_translation_params refs_funs_defs rarrays_funs_defs
    farrays_funs_defs exn_functions None exn_ri_def add_type_theories store_pinv_def_opt;
  let exn_specs = if exn_functions <> [] then add_raise_handle_functions exn_functions exn_ri_def
                  else [] in
  (monad_translation_params, exn_specs);;

(* ------------------------------------------------------------------------- *)
(* m2deep helper functions                                                   *)
(* ------------------------------------------------------------------------- *)

let mt_check_inv_fail = ref `T`;;

let mt_check_inv name tm result =
  let result = INST_ro result in
  let tm2 = get_Eval_arg (concl result) in
  let tm2' = try inst (type_match (type_of tm2) (type_of tm) []) tm2 with Failure _ -> tm2 in
  if aconv tm2' tm then result else
  (mt_check_inv_fail := tm;
   Format.print_string ("\n\nm2deep failed at '" ^ name ^ "'\n\ntarget:\n\n");
   print_term tm; Format.print_string "\n\nbut derived:\n\n"; print_term tm2;
   Format.print_string "\n\n\n"; failwith "checkinv");;

(* instantiate the ro of one theorem by the other's (HOL4 inst_ro) *)
let mt_inst_ro th1 th2 =
  try
    let tm1 = hd (mt_dest_args (concl th1)) and tm2 = hd (mt_dest_args (concl th2)) in
    if is_var tm1 && not (is_var tm2) then (INST [tm2, tm1] th1, th2)
    else if is_var tm2 && not (is_var tm1) then (th1, INST [tm1, tm2] th2)
    else (th1, th2)
  with Failure _ -> (th1, th2);;

(* ml_Eval env (Var (Short name)) RI *)
let mt_mk_Eval_name_RI str ri = mt_ISPECL_TM [str; ri] mt_Eval_name_RI_abs;;

let mt_var_hol2deep tm =
  if is_var tm && can get_arrow_type_inv (type_of tm) then
    let (name, ty) = dest_var tm in
    let inv = get_arrow_type_inv ty in
    let inv = rand (rand (concl (ONCE_REWRITE_CONV [ArrowM_def] inv))) in
    let str = mk_mlstring name in
    let result = ASSUME (mt_mk_Eval_name_RI str (mk_comb (inv, tm))) in
    mt_check_inv "var" tm result
  else hol2deep tm;;

let mt_get_pattern patterns tm =
  tryfind (fun (pat, th) -> if mt_can_match pat tm then (pat, th) else failwith "get_pattern")
    patterns;;

(* the environment conversions on the hypotheses (HOL4 simp_EvalM_env) *)
let mt_simp_EvalM_env tm =
  if mt_can_match mt_EvalM_pat tm then
    (* HOL4's REPEATC stops on UNCHANGED; HOL Light's conversions return    *)
    (* REFL: CHANGED_CONV stops it (also when the variable is the written one) *)
    (* it fails when nothing changes (DEPTH_CONV repeats a conversion at    *)
    (* each subterm until it fails)                                          *)
    CHANGED_CONV (REPEATC (CHANGED_CONV (PURE_ONCE_REWRITE_CONV [EvalM_Var_SIMP] THENC
             DEPTH_CONV mlstring_EQ_CONV THENC REWRITE_CONV []))) tm
  else NO_CONV tm;;

let mt_VALID_REFS_PRED_pat =
  `VALID_REFS_PRED (H:(REFS->hprop)#((FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)))`;;

let mt_inst_EvalM_bind th1 th2 =
  (* as HOL4's D, but VALID_REFS_PRED stays a hypothesis *)
  let dfilter th a0 =
    let hyps = hyp th in
    let th = itlist (fun a th -> if mt_can_match mt_VALID_REFS_PRED_pat a then th
                                 else if a = a0 then th else DISCH a th) hyps th in
    let th = PURE_REWRITE_RULE [IMP_IMP] th in
    if is_imp (concl th) then th else DISCH mt_T_tm th in
  let vs = fst (dest_imp (concl th2)) in
  let v = rand vs in
  let z = rand (rator vs) in
  let th2' = dfilter (UNDISCH th2) vs in
  let a2 = fst (dest_imp (concl th2')) in
  let a2 = mk_comb (mk_abs (z, a2), z) in
  let a2_eq = SYM (BETA_CONV a2) in
  let th2' = CONV_RULE (RATOR_CONV (RAND_CONV (PURE_ONCE_REWRITE_CONV [a2_eq]))) th2' in
  let th2' = GENL [z; v] (DISCH vs th2') in
  let x = rand (rand (rator (concl th1))) in
  let st_var = mk_var ("st", !mt_refs_type) in
  let pair_ty = type_of (mk_comb (x, st_var)) in
  let (t1, t2) = (match dest_type pair_ty with (_,[a;b]) -> (a,b) | _ -> failwith "bind") in
  let snd_tm = mk_comb (inst [t1, mt_a_ty; t2, mt_b_ty] mt_SND_tm, mk_comb (x, st_var)) in
  let th2' = INST [snd_tm, st_var] th2' in
  let th1' = mt_disch_asms th1 in
  UNDISCH (MATCH_MP EvalM_bind (CONJ th1' th2'));;

(* Eq a x and EqSt a st := a, for matching (HOL4 rm_fix by mk_thm rewrites) *)
let rec mt_rm_fix tm =
  if mt_can_match mt_Eq_pat tm then mt_rm_fix (rand (rator tm))
  else if mt_can_match mt_EqSt_pat tm then mt_rm_fix (rand (rator tm))
  else match tm with
    Comb(f,x) -> mk_comb (mt_rm_fix f, mt_rm_fix x)
  | Abs(v,b) -> mk_abs (v, mt_rm_fix b)
  | _ -> tm;;

(* eta-reduce the argument invariant of an ArrowM in the conclusion of an  *)
(* EvalM theorem (HOL Light's higher-order match gives \x v. A x v)        *)
let mt_eta_arrow_inv th =
  try CONV_RULE (RATOR_CONV (RAND_CONV (RATOR_CONV (RATOR_CONV (RAND_CONV
                   (DEPTH_CONV ETA_CONV)))))) th
  with Failure _ -> th;;

let m2deep_previously_translated th tm =
  let inst_gen_eq_vars th =
    let xs = map rand (tr_find_terms (mt_can_match mt_Eq_pat) (concl th)) in
    let th = INST (map (fun v -> (genvar (type_of v), v)) (filter is_var xs)) th in
    let thc = rand (rator (rand (concl (PURE_REWRITE_RULE [ArrowM_def] (tr_UNDISCH_ALL th))))) in
    match get_EqSt_var thc with
      None -> th
    | Some v -> if is_var v then INST [genvar (type_of v), v] th else th in
  let th = try inst_gen_eq_vars th with Failure _ -> th in
  let res = rand (concl (tr_UNDISCH_ALL th)) in
  let inv = INST_ro_tm (smart_get_type_inv (type_of tm)) in
  let target = mk_comb (inv, tm) in
  let (_, ss, ii) = try term_match [] res target with Failure _ ->
                    try term_match [] (mt_rm_fix res) (mt_rm_fix target)
                    with Failure _ -> ([], [], []) in
  let th1 = INST ss (INST_TYPE ii th) in
  let lemma = SPEC_ALL (ISPEC_EvalM Eval_IMP_PURE) in
  INST_ro (REWRITE_RULE [GSYM ArrowM_def] (MY_MATCH_MP lemma th1));;

(* the environment of th gets the parameter v (HOL4 inst_EvalM_env) *)
let inst_EvalM_env v th =
  let name = fst (dest_var v) in
  let str = mk_mlstring name in
  let inv = smart_get_type_inv (type_of v) in
  let tys = type_match (type_of v) (hd (snd (dest_type (type_of inv)))) [] in
  let v = inst tys v in
  let ri = mk_comb (inv, v) in
  (* HOL4 instantiates ro (INST_ro) before the contextual simplification *)
  let assum = INST_ro_tm (mt_mk_Eval_name_RI str ri) in
  let new_env = mt_mk_write str mt_v_var mt_env in
  let old_env = mt_env in
  let th = tr_UNDISCH_ALL th in
  let th = PURE_REWRITE_RULE [GSYM SafeVar_def] th in
  (* HOL4: DISCH_ALL, DISCH assum, then SIMP_RULE bool_ss [] rewrites every *)
  (* occurrence of assum among the discharged hypotheses to T (contextual)   *)
  let th = itlist DISCH (filter (fun h -> not (aconv h assum)) (hyp th)) th in
  let th = CONV_RULE (DEPTH_CONV BETA_CONV) th in
  let th = PURE_REWRITE_RULE [EQT_INTRO (ASSUME assum)] th in
  let th = INST_ro (DISCH assum th) in
  let th = REWRITE_RULE [] th in
  let th = INST [new_env, old_env] th in
  let th = REWRITE_RULE [Eval_Var_SIMP; lookup_var_write] th in
  let th = REWRITE_RULE [lookup_cons_write; lookup_var_write] th in
  let th = CONV_RULE (DEPTH_CONV mlstring_EQ_CONV) th in
  let th = REWRITE_RULE [SafeVar_def] th in
  let new_assum = fst (dest_imp (concl th)) in
  let th1 = PURE_REWRITE_RULE [IMP_IMP] (UNDISCH th) in
  let th1 = if is_imp (concl th1)
            then CONV_RULE (RATOR_CONV (RAND_CONV (DEPTH_CONV mt_simp_EvalM_env))) th1
            else th1 in
  let th1 = tr_UNDISCH_ALL th1 in
  let th1 = CONV_RULE (RATOR_CONV (RAND_CONV (RAND_CONV (tr_UNBETA_CONV v)))) th1 in
  DISCH new_assum th1;;

let mt_apply_EvalM_Fun v th fix =
  let inst_new_state_var thms th =
    let fvs = itlist (fun t l -> union (frees (concl (DISCH_ALL t))) l) thms [] in
    let current_state_var = get_EvalM_state (concl (tr_UNDISCH_ALL th)) in
    let rec find_new_state_var i =
      let sv = mk_var ("st" ^ string_of_int i, !mt_refs_type) in
      if not (mem sv fvs) then sv else find_new_state_var (i+1) in
    INST [find_new_state_var 1, current_state_var] th in
  let th1 = inst_EvalM_env v th in
  let th2 = inst_new_state_var [th1] th1 in
  let th3 = if fix then MATCH_MP EvalM_Fun_Eq (GEN mt_v_var th2)
            else MATCH_MP EvalM_Fun (GEN mt_v_var (FORCE_GEN v th2)) in
  mt_eta_arrow_inv th3;;

(* the parameters xl of a handle branch (HOL4 inst_list_EvalM_env) *)
let mt_inst_list_EvalM_env xl th =
  let vl = map (fun x -> genvar v_ty) xl in
  let xv_pairs = zip xl vl in
  let make_new_env (x, v) env = mt_mk_write (mk_mlstring (fst (dest_var x))) v env in
  let old_env = rand (rator (rator (rator (rator (concl (tr_UNDISCH_ALL th)))))) in
  let new_env = rev_itlist make_new_env xv_pairs mt_env in
  let make_inv_assum (x, v) = list_mk_comb (get_type_inv (type_of x), [x; v]) in
  let assums = map make_inv_assum xv_pairs in
  let assums_rws = map ASSUME assums in
  let dischl l th = rev_itlist DISCH l th in
  let th1 = PURE_REWRITE_RULE [GSYM SafeVar_def] th in
  let th1 = DISCH_ALL th1 in
  let th1 = INST [new_env, old_env] th1 in
  let th1 = REWRITE_RULE [Eval_Var_SIMP; lookup_var_write] th1 in
  let th1 = REWRITE_RULE [lookup_cons_write; lookup_var_write] th1 in
  let th1 = CONV_RULE (DEPTH_CONV mlstring_EQ_CONV) th1 in
  let th1 = REWRITE_RULE [SafeVar_def] th1 in
  let th1 = mt_disch_asms th1 in
  let state_var = get_EvalM_state (concl (tr_UNDISCH_ALL th1)) in
  let unbeta_convl vl tm =
    let eq = mk_eq (tm, list_mk_comb (list_mk_abs (vl, tm), vl)) in
    prove (eq, REWRITE_TAC[]) in
  let th2 = PURE_REWRITE_RULE [IMP_IMP] th1 in
  let th2 = CONV_RULE (RATOR_CONV (RAND_CONV (DEPTH_CONV mt_simp_EvalM_env))) th2 in
  let th2 = PURE_REWRITE_RULE assums_rws th2 in
  let th2 = CONV_RULE (RATOR_CONV (RAND_CONV (unbeta_convl (state_var :: xl)))) th2 in
  let th2 = CONV_RULE (RAND_CONV (RATOR_CONV (RAND_CONV (RAND_CONV (unbeta_convl xl))))) th2 in
  let th2 = dischl (rev assums) th2 in
  GENL (state_var :: xl @ vl) th2;;

(* ------------------------------------------------------------------------- *)
(* m2deep: translate monadic terms to CakeML deep embeddings                 *)
(* ------------------------------------------------------------------------- *)

let mt_last_fail = ref `T`;;
let mt_case_hook = ref (fun (_:term) -> (failwith "inst_case_thm" : thm));;

(* the type instance of the monadic state and exception types *)
let mt_inst_monad_type tm =
  try
    let (a, _, c) = mt_dest_monad_type (type_of tm) in
    inst [!mt_refs_type, a; !mt_exn_type, c] tm
  with Failure _ -> tm;;

let mt_is_var_assum = mt_can_match mt_var_assum;;
let mt_is_var_lookup_eqtype_assum x =
  mt_can_match mt_var_assum x || mt_can_match mt_nsLookup_assum x ||
  mt_can_match mt_lookup_cons_assum x || mt_can_match mt_eqtype_assum x;;

let rec m2deep tm =
  (* variable *)
  if is_var tm then
    let (name, ty) = dest_var tm in
    let inv = get_arrow_type_inv ty in
    let inv = rand (rand (concl (ONCE_REWRITE_CONV [ArrowM_def] inv))) in
    let str = mk_mlstring name in
    let result = ASSUME (mt_mk_Eval_name_RI str (mk_comb (inv, tm))) in
    let result = MY_MATCH_MP (SPEC_ALL (ISPEC_EvalM Eval_IMP_PURE)) result in
    let result = REWRITE_RULE [GSYM ArrowM_def] result in
    mt_check_inv "var" tm result
  else
  (* raise *)
  if can (mt_get_pattern !mt_exn_raises) tm then
    let (_, evalm_th) = mt_get_pattern !mt_exn_raises tm in
    let (_, ret_ty, _) = mt_dest_monad_type (type_of tm) in
    let inv = smart_get_type_inv ret_ty in
    let params = snd (strip_comb tm) in
    let params_evalms = map hol2deep params in
    let inst_e_expr lemma th =
      let e = rand (rand (concl lemma)) and expr = rand (rator (concl lemma)) in
      SPECL [e; expr] th in
    let th = rev_itlist inst_e_expr params_evalms evalm_th in
    let th = UNDISCH (SPEC_ALL (ISPECL [inv; !mt_H] th)) in
    let result = rev_itlist (fun lem th -> MP th lem) params_evalms th in
    mt_check_inv "raise custom pattern" tm result
  else
  (* handle *)
  if can (mt_get_pattern !mt_exn_handles) tm then
    let (_, evalm_th) = mt_get_pattern !mt_exn_handles tm in
    mt_check_inv "handle custom pattern" tm (mt_inst_EvalM_handle evalm_th tm)
  else
  (* return *)
  if mt_can_match mt_return_pat tm then
    let th = hol2deep (rand tm) in
    mt_check_inv "return" tm (MATCH_MP (ISPEC_EvalM_MONAD EvalM_return) th)
  else
  (* bind *)
  if mt_can_match mt_bind_pat tm then
    let x1 = rand (rator tm) in
    let (v, x2) = dest_abs (rand tm) in
    let th1 = m2deep x1 in
    let th2 = m2deep x2 in
    let (th1, th2) = mt_inst_ro th1 th2 in
    let th2 = inst_EvalM_env v th2 in
    mt_check_inv "bind" tm (mt_inst_EvalM_bind th1 th2)
  else
  (* pure_seq *)
  if mt_can_match mt_pure_seq_pat tm then
    let th1 = hol2deep (rand (rator tm)) in
    let th2 = m2deep (rand tm) in
    mt_check_inv "pure_seq" tm (MATCH_MP EvalM_pure_seq (CONJ th1 th2))
  else
  (* otherwise *)
  if mt_can_match mt_otherwise_pat tm then
    mt_check_inv "otherwise" tm (mt_inst_EvalM_otherwise tm)
  else
  (* abs *)
  if is_abs tm then
    let (v, x) = dest_abs tm in
    let thx = m2deep x in
    mt_check_inv "abs" tm (mt_apply_EvalM_Fun v thx false)
  else
  (* let expressions: HOL4's form LET (\x. b) e, as the translator's       *)
  (* preprocessing leaves them (no LET_END: HOL Light's is_let fails)      *)
  if tr_is_let tm then
    let (x, y) = (rand (rator tm), rand tm) in
    let (v, x) = dest_abs x in
    let th1 = hol2deep y in
    let th2 = m2deep x in
    let th2 = inst_EvalM_env v th2 in
    let th2 = GEN mt_v_var th2 in
    let z = rand (rand (concl th1)) in
    let th2 = INST [z, v] th2 in
    mt_check_inv "let" tm (MATCH_MP (ISPEC_EvalM EvalM_Let) (CONJ th1 th2))
  else
  (* HOL Light's LET_END (the body of a let), as in hol2deep *)
  if tr_head_is "LET_END" tm then
    let th = m2deep (rand tm) in
    let result = CONV_RULE (RATOR_CONV (RAND_CONV (RAND_CONV
                   (REWR_CONV (GSYM (ISPEC (rand tm) LET_END_DEF)))))) th in
    mt_check_inv "let_end" tm result
  else
  (* data-type pattern-matching *)
  (try !mt_case_hook tm with Failure _ ->
  (* previously translated term for dynamic store initialisation *)
  if can lookup_dynamic_v_thm tm then
    let th = lookup_dynamic_v_thm tm in
    mt_check_inv "lookup_dynamic_v_thm" tm (m2deep_previously_translated th tm)
  else
  (* previously translated term *)
  if can lookup_v_thm tm then
    let th = lookup_v_thm tm in
    mt_check_inv "lookup_v_thm" tm (m2deep_previously_translated th tm)
  else
  (* if statements *)
  if mt_can_match mt_if_statement_pat tm then
    let (t, (x1, x2)) = dest_cond tm in
    let th0 = hol2deep t in
    let th1 = m2deep x1 in
    let th2 = m2deep x2 in
    let (th1, th2) = mt_inst_ro th1 th2 in
    let th = MATCH_MP (ISPEC_EvalM EvalM_If)
               (end_itlist CONJ [mt_disch_asms th0; mt_disch_asms th1; mt_disch_asms th2]) in
    mt_check_inv "if" tm (UNDISCH th)
  else
  (* access functions *)
  if exists (fun (pat,_) -> mt_can_match pat tm) !mt_access_patterns then
    let (pat, spec) = find (fun (pat,_) -> mt_can_match pat tm) !mt_access_patterns in
    let ii = map (fun v -> (genvar (type_of v), v)) (frees pat) in
    let (pat, spec) = (vsubst ii pat, INST ii spec) in
    let (_, tms, _) = term_match [] pat tm in
    let th = INST tms spec in
    let retrieve_params_exps_pair asm =
      if mt_can_match mt_Eval_pat2 asm then (rand (rand asm), rand (rator asm))
      else failwith "retrieve_params_exps_pair" in
    let params_exps_pairs = mapfilter retrieve_params_exps_pair (hyp th) in
    let args = map fst tms in
    let args_evals = map hol2deep args in
    let subst_expr eval_th th =
      try
        let (param, trans_param) = retrieve_params_exps_pair (concl eval_th) in
        let expr_var = assoc param params_exps_pairs in
        INST [trans_param, expr_var] th
      with Failure _ -> th in
    let th = itlist subst_expr args_evals th in
    let result = rev_itlist (fun eval_th th -> MP (DISCH (concl eval_th) th) eval_th)
                   args_evals th in
    mt_check_inv "access ref/array" tm result
  else
  (* recursive pattern *)
  if can match_rec_pattern tm then
    mt_check_inv "rec_pattern" tm (mt_m2deep_rec_pattern tm)
  else
  (* normal function applications *)
  if is_comb tm then
    mt_check_inv "comb" tm (mt_m2deep_normal_fun_app tm)
  else failwith ("cannot translate: " ^ string_of_term tm))

and mt_inst_EvalM_handle evalm_th tm =
  let x = rand (rator tm) and y = rand tm in
  let (vars, y_body) = strip_abs y in
  let thx = m2deep x in
  let thy = m2deep y_body in
  let thy2 = mt_inst_list_EvalM_env vars thy in
  let (_, ret_ty, _) = mt_dest_monad_type (type_of x) in
  let inv = get_type_inv ret_ty in
  let hol_names = map (fun v -> mk_mlstring (fst (dest_var v))) vars in
  let bind_names = tr_mk_list (hol_names, mlstring_ty) in
  let lemma1 = SPEC_ALL (ISPECL [bind_names; inv; !mt_H] evalm_th) in
  let prove_assumption th =
    let a = fst (dest_imp (concl th)) in
    let c = REWRITE_CONV [ALL_DISTINCT; MEM; LENGTH] THENC DEPTH_CONV mlstring_EQ_CONV THENC
            NUM_REDUCE_CONV THENC REWRITE_CONV [] in
    MP th (EQT_ELIM (c a)) in
  let lemma2 = UNDISCH (prove_assumption (prove_assumption lemma1)) in
  let lemma3 = MATCH_MP lemma2 (mt_disch_asms thx) in
  let lemma4 = PURE_REWRITE_RULE [ml_monad_translator_write_list_def] lemma3 in
  let lemma5 = MY_MATCH_MP lemma4 thy2 in
  let lemma5 = CONV_RULE (RATOR_CONV (RAND_CONV (REWRITE_CONV []))) lemma5 in
  let lemma5 = CONV_RULE (RAND_CONV (RATOR_CONV (RATOR_CONV (RAND_CONV
                 (REWRITE_CONV [MAP]))))) lemma5 in
  mt_check_inv "handle" tm (tr_UNDISCH_ALL lemma5)

and mt_inst_EvalM_otherwise tm =
  let x = rand (rator tm) and y = rand tm in
  let th1 = m2deep x in
  let th2 = m2deep y in
  let (th1, th2) = mt_inst_ro th1 th2 in
  let i_var = mk_var ("i", v_ty) in
  let new_env = mt_mk_write (mk_mlstring "v") i_var mt_env in
  let th2 = tr_UNDISCH_ALL th2 in
  let th2 = PURE_REWRITE_RULE [GSYM SafeVar_def] th2 in
  let th2 = INST [new_env, mt_env] (DISCH_ALL th2) in
  let th2 = REWRITE_RULE [Eval_Var_SIMP; lookup_cons_write] th2 in
  let th2 = tr_UNDISCH_ALL th2 in
  let th2 = itlist (fun h th -> let eq = DEPTH_CONV mt_simp_EvalM_env h in
                      if rand (concl eq) = h then th
                      else PROVE_HYP (EQ_MP (SYM eq) (ASSUME (rand (concl eq)))) th)
              (hyp th2) th2 in
  let th2 = DISCH_ALL th2 in
  let th2 = REWRITE_RULE [lookup_cons_write; lookup_var_write] th2 in
  let th2 = CONV_RULE (DEPTH_CONV mlstring_EQ_CONV) th2 in
  let th2 = REWRITE_RULE [SafeVar_def] (REWRITE_RULE [] th2) in
  let th2 = mt_disch_asms th2 in
  let st2 = get_EvalM_state (snd (dest_imp (concl th2))) in
  let assums = fst (dest_imp (concl th2)) in
  let assums_eq = BETA_CONV (mk_comb (mk_abs (st2, assums), st2)) in
  let th3 = CONV_RULE (RATOR_CONV (RAND_CONV (PURE_ONCE_REWRITE_CONV [GSYM assums_eq]))) th2 in
  let th3 = GEN st2 (GEN i_var th3) in
  let th4 = CONJ (mt_disch_asms th1) th3 in
  let result = MATCH_MP (SPEC_ALL EvalM_otherwise) th4 in
  let result = CONV_RULE (RATOR_CONV (RAND_CONV (DEPTH_CONV BETA_CONV))) result in
  UNDISCH result

and mt_m2deep_normal_fun_app tm =
  let (f, x) = dest_comb tm in
  let thf = m2deep f in
  let thf = CONV_RULE (RATOR_CONV (RAND_CONV (RATOR_CONV (RATOR_CONV (RAND_CONV
              (PURE_REWRITE_CONV [ArrowM_def])))))) thf in
  let thf = INST_ro thf in
  (* a pure argument, else a monadic one (HOL4: handle _ => m2deep) *)
  let thx =
    try mt_disch_asms (MATCH_MP (ISPEC_EvalM Eval_IMP_PURE) (hol2deep x))
    with _ -> mt_disch_asms (m2deep x) in
  let thx = INST_ro thx in
  let force_remove_fix thx =
    let xs = map rand (tr_find_terms (mt_can_match mt_Eq_pat) (concl thx)) in
    let s th = REWRITE_RULE [EvalM_FUN_FORALL_EQ; M_FUN_QUANT_SIMP] th in
    let thx = itlist (fun x th -> s (FORCE_GEN x th)) xs thx in
    let thx = PURE_REWRITE_RULE [ArrowM_def] (tr_UNDISCH_ALL thx) in
    let thc = rand (rator (rand (rator (concl thx)))) in
    match get_EqSt_var thc with
      Some st -> PURE_REWRITE_RULE [GSYM ArrowM_def]
                   (REWRITE_RULE [M_FUN_QUANT_SIMP] (MATCH_MP EvalM_FUN_FORALL (GEN st thx)))
    | None -> PURE_REWRITE_RULE [GSYM ArrowM_def] thx in
  let assums = tr_find_terms mt_is_var_lookup_eqtype_assum (concl thx) in
  let delete_assums tm =
    if mem tm assums then MATCH_MP ml_IMP_EQ_T (ASSUME tm) else NO_CONV tm in
  let thx = CONV_RULE (RATOR_CONV (DEPTH_CONV delete_assums)) thx in
  let thx = CONV_RULE (RATOR_CONV (RAND_CONV
              (CAKE_SIMP_CONV [ml_CONTAINER_def; ml_PRECONDITION_def]))) thx in
  let thx = try MP thx TRUTH with Failure _ -> failwith "normal function application" in
  let thx = PURE_REWRITE_RULE [ArrowM_def] (force_remove_fix thx) in
  let result =
    try MATCH_MP (PURE_REWRITE_RULE [ArrowM_def] (MATCH_MP EvalM_ArrowM thf)) thx
    with Failure _ ->
    try MY_MATCH_MP (MATCH_MP EvalM_ArrowM thf) (MATCH_MP EvalM_Eq thx)
    with Failure _ ->
      let state_var = get_EvalM_state (concl thf) in
      let thc = rand (rator (rand (rator (concl (PURE_REWRITE_RULE [ArrowM_def] thf))))) in
      match get_EqSt_var thc with
        None -> failwith "m2deep: function application"
      | Some v -> MY_MATCH_MP (MATCH_MP EvalM_ArrowM_EqSt (INST [state_var, v] thf))
                    (MATCH_MP EvalM_Eq thx) in
  PURE_REWRITE_RULE [GSYM ArrowM_def] result

and mt_m2deep_rec_pattern tm =
  let (lhs, fname, pre_var) = match_rec_pattern tm in
  let (pre_v, pre_var_args) = strip_comb pre_var in
  let pre_v = mk_var (fst (dest_var pre_v), mk_fun_ty !mt_refs_type (type_of pre_v)) in
  let state_var = mk_var ("st", !mt_refs_type) in
  let state_eq_var = genvar !mt_refs_type in
  let pre_var = list_mk_comb (pre_v, state_eq_var :: pre_var_args) in
  let rec dest_args tm = try rand tm :: dest_args (rator tm) with Failure _ -> [] in
  let xs = dest_args tm in
  let f = repeat rator lhs in
  let str = mk_mlstring fname in
  let mk_fix tm =
    let inv = smart_get_type_inv (type_of tm) in
    mk_PURE (mk_Eq (inv, tm)) in
  let mk_fix_st tm =
    let pure = mk_fix tm in
    tr_list_mk_icomb mt_EqSt_tm [pure; state_eq_var] in
  let mk_m_arrow x y = mt_my_list_mk_comb (mt_ArrowM_ro (), [!mt_H; x; y]) in
  let rec mk_inv l res = match l with [] -> res | x::xs -> mk_inv xs (mk_m_arrow (mk_fix x) res) in
  let res = mk_m_arrow (mk_fix_st (hd xs)) (get_m_type_inv (type_of tm)) in
  let inv = mk_inv (tl xs) res in
  let (_, ss, _) = term_match [] lhs tm in
  let tys = type_match (type_of f) (hd (snd (dest_type (type_of inv)))) [] in
  let f = inst tys f in
  let pre = vsubst ss pre_var in
  let evalm = mk_forall (state_var,
                list_mk_comb (inst [!mt_refs_type, `:REFS`] mt_EvalM_tm,
                  [mt_ro_var; mt_env; state_var; mk_Var (mk_Short str); mk_comb (inv, f); !mt_H])) in
  let h = ASSUME (mk_PreImp (pre, evalm)) in
  let h = SPEC state_eq_var (UNDISCH (REWRITE_RULE [ml_PreImp_def] h)) in
  let h = INST [state_var, state_eq_var] h in
  let ys = map (fun tm -> MY_MATCH_MP (SPEC_ALL (ISPEC_EvalM Eval_IMP_PURE))
                            (MY_MATCH_MP Eval_Eq (mt_var_hol2deep tm))) xs in
  let rec apply_arrow h l = match l with
      [] -> INST_ro h
    | x::xs ->
        let th = apply_arrow h xs in
        try MATCH_MP (MATCH_MP (INST_ro EvalM_ArrowM) th) (INST_ro x)
        with Failure _ -> MATCH_MP (MATCH_MP (INST_ro EvalM_ArrowM_EqSt) th) (INST_ro x) in
  apply_arrow h ys;;

(* the derivation of an EvalM case lemma is set below (inst_case_thm) *)
let () = mt_case_hook := (fun tm -> failwith "inst_case_thm: not yet");;

(* ------------------------------------------------------------------------- *)
(* m_translate helper functions                                              *)
(* ------------------------------------------------------------------------- *)

let mt_remove_ArrowM_EqSt th =
  try
    let st_var = rand (rand (rator (rator (rand (rator (concl th)))))) in
    MATCH_MP ArrowM_EqSt_elim (GEN st_var th)
  with Failure _ -> th;;

(* remove the Eq of the parameters and the EqSt of the state (HOL4 remove_Eq) *)
let mt_PURE_ArrowP_Eq_pat =
  `(PURE (ArrowP ro (H:(REFS->hprop)#((FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)))
           (PURE (ml_Eq (a:A->v->bool) x)) (b:B->REFS->REFS#(v list,v)result->bool))
    :(A->B)->REFS->REFS#(v list,v)result->bool)`;;

let mt_remove_Eq_aux th =
  try
    let th = REWRITE_RULE [ArrowM_def] th in
    let rec dest_EqArrows tm =
      if mt_can_match mt_PURE_ArrowP_Eq_pat tm then
        rand (rand (rand (rator (rand tm)))) :: dest_EqArrows (rand (rand tm))
      else [] in
    let rev_params = rev (dest_EqArrows (rator (rand (rator (concl th))))) in
    let f v th = REWRITE_RULE [M_FUN_QUANT_SIMP] (MATCH_MP EvalM_FUN_FORALL (GEN v th)) in
    let th = try itlist f rev_params th with Failure _ -> th in
    REWRITE_RULE [GSYM ArrowM_def] th
  with Failure _ -> th;;

let mt_remove_EqSt th =
  try
    let th = PURE_REWRITE_RULE [ArrowM_def] (tr_UNDISCH_ALL th) in
    let thc = rand (rator (rand (rator (concl th)))) in
    match get_EqSt_var thc with
      Some st -> PURE_REWRITE_RULE [GSYM ArrowM_def]
                   (REWRITE_RULE [M_FUN_QUANT_SIMP] (MATCH_MP EvalM_FUN_FORALL (GEN st th)))
    | None -> PURE_REWRITE_RULE [GSYM ArrowM_def] th
  with Failure _ -> th;;

let mt_remove_Eq th = mt_remove_Eq_aux (mt_remove_EqSt th);;

(* the definitions of the manipulation functions (HOL4                       *)
(* get_manip_functions_defs)                                                 *)
let mt_get_manip_functions_defs () =
  let l = itlist (fun (x,y) l -> x :: y :: l) !mt_exn_functions_defs [] in
  let l = itlist (fun (x,y) l -> x :: y :: l) !mt_refs_functions_defs l in
  let l = itlist (fun (x1,x2,x3,x4,x5,x6) l -> x1::x2::x3::x4::x5::x6::l)
            !mt_rarrays_functions_defs l in
  itlist (fun (x1,x2,x3,x4,x5) l -> x1::x2::x3::x4::x5::l) !mt_farrays_functions_defs l;;

let mt_extract_precondition_non_rec th pre_var =
  if not (is_imp (concl th)) then (th, None) else
  let rw_thms = match !mt_store_pinv_def with
                  Some th -> th :: mt_get_manip_functions_defs ()
                | None -> mt_get_manip_functions_defs () in
  let rw_thms = FALSE_def :: TRUE_def :: rw_thms in
  let c = REWRITE_CONV [ml_CONTAINER_def; ml_PRECONDITION_def] THENC
          ONCE_REWRITE_CONV [GSYM ml_PRECONDITION_def] THENC
          CAKE_SIMP_CONV (ARITH_ss :: rw_thms) in
  let th = CONV_RULE (RATOR_CONV (RAND_CONV c)) th in
  let rhs = rand (fst (dest_imp (concl th))) in
  if rhs = mt_T_tm then (tr_UNDISCH_ALL (REWRITE_RULE [PRECONDITION_T] th), None) else
  let def_tm = mk_eq (pre_var, rhs) in
  let pre_def = tr_new_side_definition def_tm in
  let c = RATOR_CONV (RAND_CONV (RAND_CONV (REWR_CONV (GSYM (SPEC_ALL pre_def))))) in
  let th = tr_UNDISCH_ALL (CONV_RULE c th) in
  let pre_def = clean_precondition pre_def in
  let _ = tr_save_thm (fst (dest_var (fst (strip_comb pre_var))) ^ "_def") pre_def in
  (th, Some pre_def);;

let mt_get_monad_pre_var th lhs fname =
  let thc = rand (rator (rand (rator (concl (PURE_REWRITE_RULE [ArrowM_def]
              (tr_UNDISCH_ALL th)))))) in
  match get_EqSt_var thc with
    None -> get_pre_var lhs fname
  | Some state_var ->
      let args = state_var :: snd (strip_comb lhs) in
      let ty = itlist (fun tm acc -> mk_fun_ty (type_of tm) acc) args bool_ty in
      list_mk_comb (mk_var (fname ^ "_side", ty), args);;

(* instantiate polymorphic state and exception types (HOL4                  *)
(* instantiate_monadic_types)                                                *)
let mt_instantiate_monadic_types def =
  let d = hd (CONJUNCTS def) in
  let ty = type_of (rhs (snd (strip_forall (concl d)))) in
  let state_ty = hd (snd (dest_type ty)) in
  let exn_ty = last (snd (dest_type (hd (snd (dest_type (last (snd (dest_type ty)))))))) in
  let def = if is_vartype state_ty then
              (Format.print_string "Instantiated polymorphic monadic state\n";
               INST_TYPE [!mt_refs_type, state_ty] def)
            else def in
  if is_vartype exn_ty then
    (Format.print_string "Instantiated polymorphic monadic exceptions\n";
     INST_TYPE [!mt_exn_type, exn_ty] def)
  else def;;

let mt_get_monadic_types_inst tm =
  let ty = type_of tm in
  let state_ty = hd (snd (dest_type ty)) in
  let exn_ty = last (snd (dest_type (hd (snd (dest_type (last (snd (dest_type ty)))))))) in
  let tys = if is_vartype state_ty then [!mt_refs_type, state_ty] else [] in
  if is_vartype exn_ty then (!mt_exn_type, exn_ty) :: tys else tys;;

(* ------------------------------------------------------------------------- *)
(* m_translate_main and m_translate                                          *)
(* ------------------------------------------------------------------------- *)

let mt_rec_hook = ref (fun (_:(string*string*thm*thm*term) list) (_:thm option) ->
                         (failwith "recursion: not yet" : (string*string*thm*thm*thm option) list));;

let mt_translate_fail = ref TRUTH;;

let m_translate_main def =
  try
    let def = mt_instantiate_monadic_types def in
    mt_H := !mt_default_H;
    mt_induction_helper_thms := [];
    (* register the types other than the state and exception types *)
    let register_pure_type ty =
      if ty = !mt_refs_type || can (type_match mt_exc_ty ty) [] then ()
      else register_type ty in
    register_term_types register_pure_type (concl def);
    let (is_rec, defs, ind) = preprocess_def def in
    let info = map get_info defs in
    Format.print_string ("Translating " ^
      String.concat ", " (map (fun (f,_,_,_,_) -> f) info) ^ "\n");
    List.iter (fun (fname,ml_fname,lhs,_,_) -> install_rec_pattern lhs fname ml_fname) info;
    let thms = (try map (fun (fname,ml_fname,lhs,rhs,def) ->
                           (fname, ml_fname, m2deep rhs, def)) info
                with e -> (uninstall_rec_patterns (); raise e)) in
    uninstall_rec_patterns ();
    let thms = map (fun (x0,x1,th,x2) -> (x0, x1, instantiate_cons_name th, x2)) thms in
    let optimise_and_abstract (fname, ml_fname, th, def) =
      let rev_params = rev_param_list (lhs (concl def)) in
      let no_params = rev_params = [] in
      let evalm_p_conv conv tm =
        if is_imp tm then RAND_CONV (RATOR_CONV (RAND_CONV conv)) tm
        else RATOR_CONV (RAND_CONV conv) tm in
      (* replace the right side by the left side *)
      let th = CONV_RULE (evalm_p_conv (REWRITE_CONV [ml_CONTAINER_def] THENC
                                        ONCE_REWRITE_CONV [GSYM def])) th in
      let th = mt_disch_asms th in
      let (th, v) =
        if no_params then (th, mt_T_tm) else
        let params = if is_rec then butlast rev_params else rev_params in
        if params = [] then (th, last rev_params) else
        let (x, xs) = (hd params, tl params) in
        let v = last rev_params in
        let th1 = mt_apply_EvalM_Fun x th true in
        let th2 = rev_itlist (fun v th -> mt_remove_ArrowM_EqSt (mt_apply_EvalM_Fun v th true))
                    xs th1 in
        (th2, v) in
      (fname, ml_fname, def, th, v) in
    let thms = map optimise_and_abstract thms in
    let (is_fun, results) =
      if not is_rec then
        let _ = if length thms = 1 then () else failwith "multiple non-rec definitions" in
        let (fname, ml_fname, def, th, v) = hd thms in
        let fname = get_unique_name fname in
        let th = tr_UNDISCH_ALL (PURE_REWRITE_RULE [GSYM IMP_IMP] (DISCH_ALL th)) in
        let th = mt_disch_asms (clean_assumptions (mt_disch_asms th)) in
        let th = CONV_RULE (DEPTH_CONV ETA_CONV) th in
        let th = CONV_RULE (RATOR_CONV (RAND_CONV (REWRITE_CONV [tr_EVAL_T_F]))) th in
        let th = clean_assumptions (mt_disch_asms th) in
        let (lhs, _) = dest_eq (concl def) in
        let pre_var = mt_get_monad_pre_var th lhs fname in
        let (th, pre) = mt_extract_precondition_non_rec th pre_var in
        let th = mt_remove_Eq th in
        let th = SIMP_EqualityType_ASSUMS th in
        let code = rand (rator (rator (concl (tr_UNDISCH_ALL th)))) in
        let is_fun = (try fst (dest_const (fst (strip_comb code))) = "Fun"
                      with Failure _ -> false) in
        let th =
          if is_fun then
            let th = INST [mt_cl_env, mt_env] th in
            let th = PURE_REWRITE_RULE [ArrowM_def] th in
            let th = MATCH_MP EvalM_Fun_Var_intro th in
            let th = PURE_REWRITE_RULE [GSYM ArrowM_def] th in
            UNDISCH (SPEC (mk_mlstring ml_fname) th)
          else failwith "Monadic translation of constants not supported" in
        (is_fun, [(fname, ml_fname, def, th, pre)])
      else (true, !mt_rec_hook (map (fun (a,b,c,d,e) -> (a,b,c,d,e)) thms) ind) in
    let f = tr_can_find_term (fun t -> is_const t && fst (dest_const t) = "WF")
              (concl (mt_disch_asms (end_itlist CONJ (map (fun (_,_,_,th,_) -> th) results)))) in
    if f then failwith "WF" else (is_rec, is_fun, results)
  with e ->
    (mt_translate_fail := def;
     let names = try map (fun th -> fst (dest_const (repeat rator (lhs (concl (SPEC_ALL th))))))
                         (CONJUNCTS (SPEC_ALL def))
                 with Failure _ -> ["<unknown name>"] in
     Format.print_string ("Failed translation: " ^ String.concat ", " names ^ "\n");
     raise e);;

(* the dynamic specifications (HOL4 add_dynamic_v_thms) *)
let mt_add_dynamic_v_thms (name, ml_name, th, pre_def) =
  let th = tr_UNDISCH_ALL th in
  let hol_fun = rand (rator (concl th)) in
  mt_dynamic_v_thms := (name, ml_name, hol_fun, th, pre_def, None) :: !mt_dynamic_v_thms;
  Format.print_string ("Added a dynamic specification for " ^
                       fst (dest_const hol_fun) ^ "\n");
  if concl pre_def = mt_T_tm then () else
  Format.print_string ("\nWARNING: " ^ ml_name ^ " has a precondition.\n\n");;

let mt_st_ex_ignore_bind = prove
 (`(st_ex_ignore_bind:(A->(B,C)exc#A)->(A->(D,C)exc#A)->A->(D,C)exc#A) =
   (\x y. st_ex_bind x (\z. y))`,
  REWRITE_TAC[FUN_EQ_THM; st_ex_ignore_bind_def; st_ex_bind_def]);;

let mt_rec_store_hook = ref (fun (_:(string*string*thm*thm*thm option) list) ->
                               (failwith "recursion: not yet" : thm));;

let m_translate def =
  let def = CONV_RULE (DEPTH_CONV BETA_CONV) (REWRITE_RULE [mt_st_ex_ignore_bind] def) in
  let (is_rec, is_fun, results) = m_translate_main def in
  if is_rec then !mt_rec_store_hook results else
  let (fname, ml_fname, def, th, pre) = hd results in
  if not is_fun then failwith "Monadic translation of constants not supported" else
  let th = INST [mt_get_curr_env (), mt_cl_env] th in
  let n = mk_mlstring ml_fname in
  let lookup_var_assum = find (fun h -> tr_head_is "LOOKUP_VAR" h && hd (tr_dest_args h) = n)
                           (hyp th) in
  let state_var = get_EvalM_state (concl th) in
  let lemma = DISCH lookup_var_assum th in
  let lemma = MATCH_MP LOOKUP_VAR_EvalM_ArrowM_IMP (GENL [state_var; mt_env] lemma) in
  let lemma = tr_UNDISCH_ALL (clean_assumptions (mt_disch_asms lemma)) in
  let lemma = tr_drop_T_hyps lemma in
  let pre_def = match pre with None -> TRUTH | Some d -> d in
  if !mt_local_state_init_H then
    let th = DISCH_ALL lemma in
    (mt_add_dynamic_v_thms (fname, ml_fname, th, pre_def); th)
  else
    let v = rand (rator (rand (concl lemma))) in
    let exp = rand (rand (concl lemma)) in
    let v_name = find_const_name (fname ^ "_v") in
    ml_prog_update (ml_prog_add_Dlet_Fun ml_prog_unknown_loc n v exp v_name);
    let v_def = hd (get_curr_v_defs ()) in
    let v_thm = CONV_RULE (RAND_CONV (REWR_CONV (GSYM v_def))) lemma in
    add_v_thms (fname, ml_fname, v_thm, pre_def);
    tr_save_thm (fname ^ "_v_thm") v_thm;;

(* ------------------------------------------------------------------------- *)
(* The EvalM case lemmas (HOL4 derive_case_of, mem_derive_case_of,           *)
(* inst_case_thm_for, inst_case_thm)                                         *)
(* ------------------------------------------------------------------------- *)

(* the EvalM version of the translator's case lemma of ty (HOL4             *)
(* derive_case_of converts the Eval case lemma; here it is built as the      *)
(* translator builds its own (prove_case_of_lemma) and proved from           *)
(* IMP_EvalM_Mat_cases): the same statement                                  *)
let mt_H_case_var () =
  mk_var ("H", mk_type ("prod", [mk_fun_ty !mt_refs_type ms_hprop_ty; mt_ffi_proj_ty]));;

let mt_st_var () = mk_var ("st", !mt_refs_type);;

let mt_mk_EvalM env exp p h =
  list_mk_comb (inst [!mt_refs_type, mt_REFS_ty] mt_EvalM_tm,
                [mt_ro_var; env; mt_st_var (); exp; p; h]);;

let mt_prove_case_of_lemma ty =
  let (_, inv_def, _, eval_case_lemma) = lookup_type_thms ty in
  let tyname = fst (dest_type ty) in
  let is_simple_case = tyname = "prod" || ty = `:1` in
  let type_assum = fst (dest_imp (concl eval_case_lemma)) in
  let case_th = get_nchotomy_of ty in
  let ci = tr_case_info ty in
  let c0 = ci.ci_case in
  let cty = type_of c0 in
  let dom0 = fst (dest_fun_ty cty) in
  let rty0 = snd (splitlist dest_fun_ty cty) in
  let ret_ty = tr_ret_tyvar ty in
  let ret_m_ty = mt_M_type ret_ty in
  let c = inst (type_match dom0 ty [ret_m_ty, rty0]) c0 in
  let pats = tr_nchotomy_pats case_th in
  (* the return type is a function type: take one argument per constructor *)
  let rec take_args n ty =
    if n = 0 then [] else let (a,b) = dest_fun_ty ty in a :: take_args (n-1) b in
  let ftys = take_args (length pats) (snd (dest_fun_ty (type_of c))) in
  let fs = map2 (fun ty k -> mk_var ("f" ^ string_of_int k, ty)) ftys (1--(length ftys)) in
  let input_var = mk_var ("input", ty) in
  let cases_tm = list_mk_comb (c, input_var :: fs) in
  let str_tl s = String.sub s 1 (String.length s - 1) in
  let ts = map2 (fun (f,tm) n ->
      let xs = snd (strip_comb tm) in
      let fxs = list_mk_comb (f, xs) in
      let pxs = list_mk_comb (mk_var ("b" ^ string_of_int n,
                                      itlist (fun x t -> mk_fun_ty (type_of x) t) xs bool_ty), xs) in
      let xs = map (fun x -> let s = str_tl (fst (dest_var x)) in
                     (x, mk_var ("n" ^ s, mlstring_ty), mk_var ("v" ^ s, v_ty))) xs in
      let exp = mk_var ("exp" ^ string_of_int n, exp_ty) in
      (n,f,fxs,pxs,tm,exp,xs)) (zip fs pats) (1--(length pats)) in
  let stamps = if is_simple_case then [] else
               map (fun t -> dest_eq t) (conjuncts type_assum) in
  let get_stamp kv = rand (rand (snd (find (fun (tm,_) -> free_in kv tm) stamps))) in
  let row_of (n,f,fxs,pxs,tm,exp,xs) =
    let ctor = fst (strip_comb tm) in
    let kv = mk_var (mk_cons_name ctor, ml_id_ty) in
    let vars = tr_mk_list (map (fun (_,n,_) -> n) xs, mlstring_ty) in
    (kv, vars, exp, (if is_simple_case then tr_ARB_stamp_tm else get_stamp kv), ctor) in
  let rows = map row_of ts in
  let y_tm =
    if is_simple_case then
      let (_,vars,exp,_,_) = hd rows in
      mk_comb (tr_INL_cases_tm, mk_pair (vars, exp))
    else
      mk_comb (tr_INR_cases_tm,
               tr_mk_list (map (fun (kv,vars,exp,st,_) ->
                                  mk_pair (kv, mk_pair (vars, mk_pair (exp, st)))) rows,
                           tr_ps_cases_ty)) in
  let patterns = mk_comb (tr_Mat_cases_tm, y_tm) in
  let ret_inv = get_type_inv ret_ty in
  let ret_minv = tr_list_mk_icomb (inst [!mt_refs_type, mt_c_ty] mt_MONAD_tm)
                   [ret_inv; !mt_EXN_TYPE] in
  let h_var = mt_H_case_var () in
  let exp_var = mk_var ("exp", exp_ty) in
  let result = mt_mk_EvalM mt_env (mk_Mat (exp_var, patterns)) (mk_comb (ret_minv, cases_tm)) h_var in
  let vs = flat (map (fun (n,f,fxs,pxs,tm,exp,xs) -> map (fun (x,_,_) -> x) xs) ts) in
  let b0 = mk_var ("b0", bool_ty) in
  let rtm = list_mk_conj (b0 :: map (fun (n,f,fxs,pxs,tm,exp,xs) ->
                            mk_imp (mk_CONTAINER (mk_eq (input_var, tm)), pxs)) ts) in
  let rtm = list_mk_forall (vs, rtm) in
  let rtag = mk_TAG (`one`, rtm) in
  let result = mk_imp (rtag, result) in
  let inv_tm = get_type_inv ty in
  let find_inv tm =
    if type_of tm = ty then mk_comb (inv_tm, tm) else mk_comb (get_type_inv (type_of tm), tm) in
  let mk_hyp (n,f,fxs,pxs,tm,exp,xs) =
    let env = itlist (fun (x,n,v) e -> mk_write (n,v,e)) (rev xs) mt_env in
    let tm = map (fun (x,n,v) -> mk_comb (find_inv x, v)) xs @ [pxs] in
    let tm = list_mk_conj tm in
    let tm = mk_imp (tm, mt_mk_EvalM env exp (mk_comb (ret_minv, fxs)) h_var) in
    let vs = map (fun (x,_,_) -> x) xs @ map (fun (_,_,v) -> v) xs in
    mk_TAG (mk_small_numeral n, list_mk_forall (vs, tm)) in
  let mk_alld (n,f,fxs,pxs,tm,exp,xs) =
    mk_comb (tr_ALL_DISTINCT_names_tm, tr_mk_list (map (fun (_,x,_) -> x) xs, mlstring_ty)) in
  let tt = if ts = [] then mt_T_tm else list_mk_conj (map mk_alld ts) in
  let hyps = map mk_hyp ts in
  let x = mk_comb (inv_tm, input_var) in
  let ev = mk_Eval (mt_env, exp_var, x) in
  let hyp0 = mk_TAG (`0`, mk_imp (b0, ev)) in
  let hyps_tm = list_mk_conj (hyp0 :: hyps) in
  (* the proof *)
  let ath = ASSUME type_assum and tth = ASSUME tt and hth = ASSUME hyps_tm
  and rth0 = ASSUME rtag in
  let untag th = CONV_RULE (REWR_CONV ml_TAG_def) th in
  let rth = SPEC_ALL (untag rth0) in
  let hths = map untag (CONJUNCTS hth) in
  let b0th = CONJUNCT1 rth in
  let e0 = MP (hd hths) b0th in
  let lemma = tr_ISPECL_NAMED ["st", mt_st_var (); "a", inv_tm; "r1", input_var; "env", mt_env;
                               "exp", exp_var; "r2", mk_comb (ret_minv, cases_tm);
                               "y", y_tm] IMP_EvalM_Mat_cases in
  let lemma = INST [h_var, mk_var ("H", type_of h_var)] lemma in
  let lemma = CONV_RULE (LAND_CONV (RAND_CONV (REWRITE_CONV [tr_sum_case_def; tr_pair_case_def] THENC
                                                DEPTH_CONV GEN_BETA_CONV))) lemma in
  let side = rand (lhand (concl lemma)) in
  let side_parts = conjuncts side in
  let main_goal = last side_parts in
  let rows6 = map2 (fun (kv,vars,exp,st,ctor) h -> (kv,vars,exp,st,ctor,h)) rows (tl hths) in
  let main_th =
    TAC_PROOF (([], main_goal),
      X_GEN_TAC tr_v_v THEN DISCH_TAC THEN
      STRIP_ASSUME_TAC (SPEC input_var case_th) THEN
      tr_case_branch_tac input_var inv_def ci.ci_def rows6 rth) in
  let side_conv =
    REWRITE_CONV [MAP; good_cons_env_def; ALL; HD; pat_bindings_def; APPEND;
                  tr_pair_case_def; same_type_def; o_THM; FST; SND; LET_DEF; LET_END_DEF] THENC
    TOP_DEPTH_CONV (GEN_BETA_CONV ORELSEC GEN_REWRITE_CONV I [tr_pair_case_def]) THENC
    REWRITE_CONV [o_THM; FST; SND] THENC DEPTH_CONV LENGTH_CONV THENC
    REWRITE_CONV [ath; same_type_def] THENC
    tr_ALL_DISTINCT_CONV THENC REWRITE_CONV (tr_distinct_rws tth) in
  let other_ths = map (fun t -> EQT_ELIM (side_conv t)) (butlast side_parts) in
  let side_th = end_itlist CONJ (other_ths @ [main_th]) in
  let res = MP lemma (CONJ e0 side_th) in
  let res = itlist DISCH [type_assum; tt; hyps_tm; rtag] res in
  let res = PURE_REWRITE_RULE [ml_TAG_def; ml_Mat_cases_def; MAP] res in
  let res = CONV_RULE (TOP_DEPTH_CONV (GEN_BETA_CONV ORELSEC
                                       GEN_REWRITE_CONV I [tr_pair_case_def; MAP])) res in
  GEN h_var res;;

(* the case lemmas are cached per type (HOL4 mem_derive_case_of) *)
let mt_mem_derive_case_of ty =
  let th =
    try snd (find (fun (y,_) -> can (type_match y ty) []) !mt_mem_derive_case_ref)
    with Failure _ ->
      let gty = try let (y,_,_,_) = find (fun (y,_,_,_) -> can (type_match y ty) [])
                                       !tr_type_memory in y
                with Failure _ -> ty in
      let th = mt_prove_case_of_lemma gty in
      mt_mem_derive_case_ref := (gty, th) :: !mt_mem_derive_case_ref; th in
  let h_ty = type_of (fst (dest_forall (concl th))) in
  let h_st = !mt_H in
  SPEC (inst (type_match (type_of h_st) h_ty []) h_st) th;;

let mt_inst_case_fail = ref `T`;;

let mt_inst_case_thm_for tm =
  try
    let h, args = strip_comb tm in
    let x0 = hd args and arms = tl args in
    let th = UNDISCH (mt_mem_derive_case_of (type_of x0)) in
    let pat = rand (rand (rator (concl (tr_UNDISCH_ALL th)))) in
    let (_, ss, i) = term_match [] pat tm in
    let th = INST ss (INST_TYPE i th) in
    let ss = map (fun (y,x) -> (smart_get_type_inv y, inst i (smart_get_type_inv x))) i in
    let th = INST ss th in
    let th = CONV_RULE (DEPTH_CONV BETA_CONV) th in
    (* the arms' variable names for the n, v and x variables of the lemma *)
    (* tr_case_info_of_const: the kit's tables and the translator's one_CASE *)
    let ci = tr_case_info_of_const h in
    let arities = map (fun (vs,_) -> length vs) ci.ci_pats in
    let names = map2 tr_arm_vars arities arms in
    let ts = tr_find_terms (fun t -> is_CONTAINER t && type_of t = bool_ty &&
                                     is_eq (rand t)) (concl th) in
    let ts = map (fun t -> rand (rand t)) ts in
    let rename_var prefix ty v =
      let s = fst (dest_var v) in mk_var (prefix ^ String.sub s 1 (String.length s - 1), ty) in
    let ns = flat (map (fun t ->
        let c = fst (strip_comb t) in
        let cname t = fst (dest_const t) in
        let k = index (cname c) (map (fun (_,p) -> cname (fst (strip_comb p))) ci.ci_pats) in
        let aa = el k names in
        let xs = snd (strip_comb t) in
        zip aa (map (fun x -> (x, rename_var "n" mlstring_ty x, rename_var "v" v_ty x)) xs))
      (setify ts)) in
    let ms = map (fun (b,(x,n,v)) -> (mk_mlstring (fst (dest_var b)), n)) ns in
    let th = INST ms th in
    let ks = map (fun (b,(x,n,v)) -> (fst (dest_var x), fst (dest_var b))) ns @
             map (fun (b,(x,n,v)) -> (fst (dest_var v), fst (dest_var b) ^ "{value}")) ns in
    let rename_bound_conv tm =
      let v,_ = dest_abs tm in
      let (s,ty) = dest_var v in
      let new_s = try assoc s ks with Failure _ -> failwith "" in
      ALPHA_CONV (mk_var (new_s, ty)) tm in
    let th = CONV_RULE (DEPTH_CONV rename_bound_conv) th in
    let th = CONV_RULE (RATOR_CONV (RAND_CONV tr_ALL_DISTINCT_CONV)) th in
    INST_ro (MP th TRUTH)
  with Failure s -> (mt_inst_case_fail := tm; failwith ("inst_case_thm_for: " ^ s));;

let mt_simp_env tm =
  if mt_can_match mt_EvalM_pat tm then
    (* HOL4's REPEATC stops on UNCHANGED; HOL Light's conversions return    *)
    (* REFL: CHANGED_CONV stops it (also when the variable is the written one) *)
    (* it fails when nothing changes (DEPTH_CONV repeats a conversion at    *)
    (* each subterm until it fails)                                          *)
    CHANGED_CONV (REPEATC (CHANGED_CONV (PURE_ONCE_REWRITE_CONV [EvalM_Var_SIMP] THENC
             DEPTH_CONV mlstring_EQ_CONV THENC REWRITE_CONV []))) tm
  else NO_CONV tm;;

let mt_inst_case_thm tm m2deep =
  let tm = mt_inst_monad_type tm in
  let th = mt_inst_case_thm_for tm in
  let th = CONV_RULE (RATOR_CONV (PURE_REWRITE_CONV [CONJ_ASSOC])) th in
  let (hyps, _) = dest_imp (concl th) in
  let sat_hyp tm =
    try
      let (vs, x) = strip_forall tm in
      let (x, y) = dest_imp x in
      let z = get_Eval_arg y in
      let lemma = if mt_is_monad_type (type_of z) then m2deep z else hol2deep z in
      let lemma = mt_disch_asms (INST_ro lemma) in
      let new_env = get_Eval_env y in
      let lemma = PURE_REWRITE_RULE [lookup_cons_write] (INST [new_env, mt_env] lemma) in
      let (x1, x2) = try dest_conj x with Failure _ -> (mt_T_tm, x) in
      let (z1, z2) = dest_imp (concl lemma) in
      let c = tr_env_hyp_conv (CONJUNCTS (ASSUME x1)) THENC
              ONCE_DEPTH_CONV mt_simp_env THENC
              REWRITE_CONV [lookup_cons_write; lookup_var_write] THENC
              DEPTH_CONV mlstring_EQ_CONV THENC REWRITE_CONV [] in
      let thz = DISCH x1 (c z1) in
      let lemma = MATCH_MP sat_hyp_lemma (CONJ thz lemma) in
      let bs = fst (chop_list (length vs / 2) vs) in
      let rec list_unbeta_conv l = match l with
          [] -> ALL_CONV
        | x::xs -> tr_UNBETA_CONV x THENC RATOR_CONV (list_unbeta_conv xs) in
      let lemma = CONV_RULE (RATOR_CONV (RAND_CONV (RAND_CONV
                    (list_unbeta_conv (rev bs))))) lemma in
      let lemma = GENL vs lemma in
      (if can (term_match [] tm) (concl lemma) then () else failwith "sat_hyp failed");
      remove_primes lemma
    with Failure s -> (mt_last_fail := tm; failwith s) in
  let rec sat_hyps tm =
    if is_conj tm then let (x,y) = dest_conj tm in CONJ (sat_hyps x) (sat_hyps y)
    else sat_hyp tm in
  let lemma = sat_hyps hyps in
  let th = MATCH_MP th lemma in
  let th = CONV_RULE (RATOR_CONV (DEPTH_CONV BETA_CONV THENC REWRITE_CONV [])) th in
  tr_UNDISCH_ALL th;;

let () = mt_case_hook := (fun tm -> mt_check_inv "case" tm (mt_inst_case_thm tm m2deep));;

(* ------------------------------------------------------------------------- *)
(* Recursive functions (HOL4 apply_EvalM_Recclosure, extract_precondition_rec,*)
(* apply_ind, and the recursive branches of m_translate_main and m_translate) *)
(* ------------------------------------------------------------------------- *)

let mt_env2 = mk_var ("env2", venv_ty);;
let mt_shadow_env = mk_var ("shadow_env", venv_ty);;

let mt_ArrowM_pat =
  `ArrowM ro (H:(REFS->hprop)#((FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)))
     (a:A->REFS->REFS#(v list,v)result->bool) (b:B->REFS->REFS#(v list,v)result->bool)`;;

let mt_apply_EvalM_Recclosure recc fname v th =
  let vname = fst (dest_var v) in
  let vname_str = mk_mlstring vname and fname_str = mk_mlstring fname in
  let is_monad_only = not (mt_can_match mt_ArrowM_pat (rator (rand (rator (concl th))))) in
  let lemma =
    if is_monad_only then
      SPEC_ALL (UNDISCH (tr_ISPECL_NAMED ["H", !mt_H; "funs", recc; "fname", fname_str;
                                          "env2", mt_env2] EvalM_Recclosure_ALT2))
    else tr_ISPECL_NAMED ["H", !mt_H; "funs", recc; "fname", fname_str; "env2", mt_env2]
           EvalM_Recclosure_ALT in
  (* ALL_DISTINCT of the function names and find_recfun, by evaluation *)
  let ad = find_term (fun t -> tr_head_is "ALL_DISTINCT" t) (concl lemma) in
  let adth = (tr_map_fst3_conv THENC tr_ALL_DISTINCT_CONV) ad in
  let lemma = PURE_REWRITE_RULE [adth] lemma in
  let fr = find_term (fun t -> tr_head_is "find_recfun" t) (concl lemma) in
  let frth = tr_find_recfun_conv fr in
  let (x, e) = dest_pair (rand (rhs (concl frth))) in
  (* tr_ISPECL_NAMED leaves name and body free (SPEC_ALL): instantiate them *)
  let name_var = find (fun t -> fst (dest_var t) = "name") (frees (concl lemma)) in
  let body_var = find (fun t -> fst (dest_var t) = "body") (frees (concl lemma)) in
  let lemma = INST [x, name_var; e, body_var] (REWRITE_RULE [IMP_CLAUSES] lemma) in
  let frth' = INST [x, name_var; e, body_var] frth in
  let lemma = PURE_REWRITE_RULE [frth'] lemma in
  let lemma = REWRITE_RULE [IMP_CLAUSES] lemma in
  let lemma = INST_ro lemma in
  let inv = smart_get_type_inv (type_of v) in
  let new_env = mt_mk_write x mt_v_var (list_mk_comb (tr_write_rec_tm, [recc; mt_env2; mt_env2])) in
  let old_env = mt_env in
  let tys = type_match (type_of v) (hd (snd (dest_type (type_of inv)))) [] in
  let v = inst tys v in
  let assum = vsubst [new_env, old_env] (mt_mk_Eval_name_RI vname_str (mk_comb (inv, v))) in
  let assum = INST_ro_tm assum in
  let state_var = get_EvalM_state (concl (tr_UNDISCH_ALL th)) in
  let thx = tr_UNDISCH_ALL th in
  let thx = PURE_REWRITE_RULE [GSYM SafeVar_def] thx in
  let thx = DISCH assum (DISCH_ALL thx) in
  let thx = INST [new_env, old_env] thx in
  let thx = REWRITE_RULE [EvalM_Var_SIMP_ArrowM; Eval_Var_SIMP; lookup_var_write;
                          lookup_cons_write] thx in
  let thx = CONV_RULE (DEPTH_CONV mlstring_EQ_CONV) thx in
  let thx = REWRITE_RULE [SafeVar_def] thx in
  let new_assum = fst (dest_imp (concl thx)) in
  let th1 = REWRITE_RULE [ASSUME new_assum] (UNDISCH thx) in
  let th1 = tr_UNDISCH_ALL th1 in
  let th1 = CONV_RULE (RATOR_CONV (RAND_CONV (RAND_CONV (tr_UNBETA_CONV v)))) th1 in
  let th1 = DISCH new_assum th1 in
  let th2 =
    if not is_monad_only then
      MATCH_MP lemma (INST [mt_cl_env, mt_env] (GENL [state_var; mt_v_var] th1))
    else
      let assum = fst (dest_imp (concl (DISCH_ALL th1))) in
      let a = mk_abs (state_var, assum) in
      let a_eq = BETA_CONV (mk_comb (a, state_var)) in
      let th = INST [mt_cl_env, mt_env] (GENL [state_var; mt_v_var] (DISCH_ALL th1)) in
      let th = PURE_ONCE_REWRITE_RULE [GSYM a_eq] th in
      let lemma3 = SPEC_ALL (tr_ISPECL_NAMED ["H", !mt_H; "funs", recc; "fname", fname_str;
                                              "env2", mt_env2] EvalM_Recclosure_ALT3) in
      let th = UNDISCH (REWRITE_RULE [a_eq] (MATCH_MP lemma3 th)) in
      let ad = find_term (fun t -> tr_head_is "ALL_DISTINCT" t) (concl th) in
      let th = PURE_REWRITE_RULE [(tr_map_fst3_conv THENC tr_ALL_DISTINCT_CONV) ad] th in
      let fr = find_term (fun t -> tr_head_is "find_recfun" t) (concl th) in
      REWRITE_RULE [IMP_CLAUSES; tr_find_recfun_conv fr] th in
  let assum = ASSUME (fst (dest_imp (concl th2))) in
  let th3 = REWRITE_RULE [assum] (mt_disch_asms th2) in
  let th3 = REWRITE_RULE [Eval_Var_SIMP; EvalM_Var_SIMP_ArrowM; lookup_var_write; ITLIST;
                          ml_write_rec_def] th3 in
  let th3 = CONV_RULE (DEPTH_CONV GEN_BETA_CONV) th3 in
  let th3 = REWRITE_RULE [Eval_Var_SIMP; EvalM_Var_SIMP_ArrowM; lookup_var_write; ITLIST; FST] th3 in
  let th3 = CONV_RULE (DEPTH_CONV mlstring_EQ_CONV) th3 in
  let th3 = REWRITE_RULE [SafeVar_def] th3 in
  let lemma = INST_ro (UNDISCH EvalM_Eq_Recclosure) in
  let lemma_lhs = lhs (concl lemma) in
  let replace_conv tm =
    let (_, i, t) = term_match [] lemma_lhs tm in
    let th9 = INST i (INST_TYPE t lemma) in
    let name = rand (rand (inst t (vsubst i lemma_lhs))) in
    INST [name, mk_var ("name", mlstring_ty)] th9 in
  CONV_RULE (DEPTH_CONV replace_conv) th3;;

let mt_TRUE_tm = rhs (concl TRUE_def);;
let mt_PreImp_simp = ASSUME `!a b. (ml_PreImp a b /\ ml_PRECONDITION a) <=> b`;;

let mt_extract_precondition_rec thms =
  let rephrase_pre (fname, ml_fname, def, th) =
    let (lhs, _) = dest_eq (concl def) in
    let pre_var = mt_get_monad_pre_var th lhs fname in
    let th = REWRITE_RULE [CONTAINER_NOT_ZERO] th in
    let th = ex_rename_bound_vars_rule th in
    let th = CONV_RULE (RATOR_CONV (RAND_CONV (REWRITE_CONV [GSYM IMP_IMP]))) th in
    let tm = fst (dest_imp (concl th)) in
    let tm0 = rand (concl (REWRITE_CONV [tr_rw0] tm)) in
    let tm1 = rand (concl (REWRITE_CONV [tr_rw1] tm0)) in
    let h = !mt_H in
    let pat = mt_mk_EvalM mt_env mt_exp_var (mk_var ("P", mk_fun_ty !mt_refs_type
                (mk_fun_ty (mk_type ("prod", [!mt_refs_type; `:(v list,v)result`])) bool_ty))) h in
    let pat = vsubst [mk_var ("st", !mt_refs_type), mt_st_var ()] pat in
    let rw2 = ASSUME (list_mk_forall (frees pat, mk_eq (pat, mt_T_tm))) in
    let tm2 = rand (concl (REWRITE_CONV [tr_rw0; rw2; ml_PreImp_def] tm)) in
    (fname, ml_fname, def, th, pre_var, tm1, tm2, rw2) in
  let thms = map rephrase_pre thms in
  (* check whether the precondition is T *)
  let get_subst (_,_,_,_,pre_var,_,_,_) =
    (list_mk_abs (snd (strip_comb pre_var), mt_T_tm), fst (strip_comb pre_var)) in
  let ss = map get_subst thms in
  let rw_thms = match !mt_store_pinv_def with
                  Some th -> th :: mt_get_manip_functions_defs ()
                | None -> mt_get_manip_functions_defs () in
  let is_true_pre (_,_,_,_,_,_,tm2,rw2) =
    rand (concl ((REWRITE_CONV ([rw2; ml_PreImp_def; ml_PRECONDITION_def; ml_CONTAINER_def] @
                                rw_thms) THENC
                  CAKE_SIMP_CONV [ARITH_ss; FALSE_def; TRUE_def]) (vsubst ss tm2))) = mt_T_tm in
  let no_pre = forall is_true_pre thms in
  if no_pre then
    map (fun (fname,ml_fname,def,th,_,_,_,_) ->
           let th5 = INST ss th in
           let th5 = REWRITE_RULE [PRECONDITION_EQ_CONTAINER] th5 in
           let th5 = PURE_REWRITE_RULE [ml_PreImp_def; ml_PRECONDITION_def] th5 in
           let th5 = CONV_RULE (DEPTH_CONV BETA_CONV THENC
                                RATOR_CONV (RAND_CONV (REWRITE_CONV []))) th5 in
           (fname, ml_fname, def, th5, (None : thm option))) thms
  else
  (* the EvalM predicates and their precondition variables *)
  let pre_var_EvalM_pairs =
    map (fun (_,ml_fname,def,th,_,_,_,_) ->
           (mt_get_monad_pre_var th (lhs (concl def)) ml_fname,
            concl (tr_UNDISCH_ALL th))) thms in
  (* these rewrites only build terms (HOL4: mk_thm) *)
  let pre_var_EvalM_rws = map (fun (x, y) ->
      ASSUME (mk_eq (mk_forall (get_EvalM_state y, y), x))) pre_var_EvalM_pairs in
  let replace_EvalM (_,_,_,th,_,_,_,_) =
    let rws = mt_PreImp_simp :: pre_var_EvalM_rws in
    let assum = fst (dest_imp (concl th)) in
    let st = get_EvalM_state (snd (dest_imp (concl th))) in
    concl (PURE_REWRITE_RULE rws (DISCH assum (GEN st (UNDISCH th)))) in
  let no_quant_pres = map replace_EvalM thms in
  let all_pre_vars = map (fun (x,_) -> repeat rator x) pre_var_EvalM_pairs in
  let (all_pres_list, vsl) =
    unzip (map (fun tm -> let vs = subtract (frees tm) all_pre_vars in
                          (list_mk_forall (vs, tm), vs)) no_quant_pres) in
  let all_pres = list_mk_conj all_pres_list in
  (* HOL4 Hol_reln: the side conditions as an inductive definition, with the *)
  (* translator's names (f_side, or THY_f_side when f_side is taken)          *)
  let hol4_names = map (fun v -> fst (dest_var v)) all_pre_vars in
  let ren = map (fun v -> (mk_var (tr_side_const_name (fst (dest_var v)), type_of v), v))
                all_pre_vars in
  let all_pres = vsubst ren all_pres in
  let (_, pre_ind, pre_def) = new_inductive_definition all_pres in
  let clean_pre_def = PURE_REWRITE_RULE [ml_CONTAINER_def; ml_PRECONDITION_def] pre_def in
  let _ = tr_save_thm (hd hol4_names ^ "_def") clean_pre_def in
  (* for every precondition: pre_cond ==> EvalM ... *)
  let evalm_abs (pre_var_tm, evalm_tm) =
    let (_, args) = strip_comb pre_var_tm in
    let st = get_EvalM_state evalm_tm in
    list_mk_abs (args, mk_forall (st, evalm_tm)) in
  let inst_pre_ind = SPECL (map evalm_abs pre_var_EvalM_pairs) pre_ind in
  let inst_pre_ind = CONV_RULE (DEPTH_CONV BETA_CONV) inst_pre_ind in
  let pre_var_T_subst = map (fun (pre_var_tm,_) ->
      let (pre_var, args) = strip_comb pre_var_tm in
      (list_mk_abs (args, mt_TRUE_tm), pre_var)) pre_var_EvalM_pairs in
  let inst_EvalM_thm (vs, (_,_,_,th,_,_,_,_)) =
    let th1 = INST pre_var_T_subst th in
    let th1 = CONV_RULE (DEPTH_CONV BETA_CONV) th1 in
    let th1 = PURE_REWRITE_RULE [PreImp_PRECONDITION_T_SIMP] th1 in
    let assum = fst (dest_imp (concl th1)) in
    let st = get_EvalM_state (snd (dest_imp (concl th1))) in
    GENL vs (DISCH assum (GEN st (UNDISCH th1))) in
  let evalm_thms = end_itlist CONJ (map inst_EvalM_thm (zip vsl thms)) in
  let thms2 = CONJUNCTS (MATCH_MP inst_pre_ind evalm_thms) in
  let pre_defs = map SPEC_ALL (CONJUNCTS clean_pre_def) in
  let clean ((pre, lemma), (fname,ml_fname,def,_,_,_,_,_)) =
    let th1 = SPEC_ALL lemma in
    let assum = fst (dest_imp (concl th1)) in
    let th2 = DISCH assum (SPEC_ALL (UNDISCH th1)) in
    let precond_eq = ISPEC assum ml_PRECONDITION_def in
    let th3 = PURE_ONCE_REWRITE_RULE [GSYM precond_eq] th2 in
    (fname, ml_fname, def, th3, Some pre) in
  map clean (zip (zip pre_defs thms2) thms);;

(* the induction for recursive functions without preconditions (HOL4       *)
(* apply_ind); a goal that the tactics do not prove stays a hypothesis      *)
let mt_apply_ind thms ind =
  let get_goal (fname, ml_fname, def, th, pre) =
    let th = REWRITE_RULE [ml_CONTAINER_def] th in
    let hs = hyp th in
    let rev_params = rev_param_list (lhs (concl def)) in
    let c = concl (tr_UNDISCH_ALL th) in
    let state_var = get_EvalM_state c in
    let forall_st_tm = mk_forall (state_var, c) in
    let thc = rand (rator (rand (rator (concl (PURE_REWRITE_RULE [ArrowM_def]
                (tr_UNDISCH_ALL th)))))) in
    let st_eq_tm = mt_the (get_EqSt_var thc) in
    let forall_st_tm = mk_forall (st_eq_tm, forall_st_tm) in
    let hyp_tm = list_mk_abs (rev rev_params, forall_st_tm) in
    let goal = list_mk_forall (rev rev_params, forall_st_tm) in
    (hyp_tm, (th, (hs, goal))) in
  let goals = map get_goal thms in
  let gs = list_mk_conj (map (fun (_,(_,(_,g))) -> g) goals) in
  let hs_l = setify (flat (map (fun (_,(_,(h,_))) -> h) goals)) in
  let hs = if hs_l = [] then mt_T_tm else list_mk_conj hs_l in
  let goal = mk_imp (hs, gs) in
  let ind_thm = rename_bound_vars_rule "i" (mt_the ind) in
  let ind_thm = CONV_RULE (DEPTH_CONV BETA_CONV)
                  (try ISPECL (map fst goals) ind_thm with Failure _ -> ind_thm) in
  let ths = map (fun (_,(th,_)) -> th) goals in
  let tac1 =
    DISCH_THEN (fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
    MATCH_MP_TAC ind_thm THEN REPEAT STRIP_TAC THEN
    FIRST (map MATCH_MP_TAC ths) THEN REPEAT STRIP_TAC THEN
    RFS [ADD1; TRUE_def; FALSE_def; UNCURRY_SIMP; ARITH_ss] THEN ASM_MESON_TAC [] in
  let tac2 =
    DISCH_THEN (fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
    MATCH_MP_TAC ind_thm THEN REPEAT STRIP_TAC THEN
    FIRST (map MATCH_MP_TAC ths) THEN REPEAT STRIP_TAC THEN
    LAST_X_ASSUM MATCH_MP_TAC THEN RFS [ADD1; TRUE_def; FALSE_def; UNCURRY_SIMP; ARITH_ss] THEN
    TRY (ASM_MESON_TAC []) in
  let tac3 =
    DISCH_THEN (fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
    REWRITE_TAC [FORALL_PAIR_THM] THEN
    (MATCH_MP_TAC ind_thm ORELSE
     MATCH_MP_TAC (REWRITE_RULE [FORALL_PAIR_THM] ind_thm)) THEN
    REPEAT STRIP_TAC THEN FIRST (map MATCH_MP_TAC ths) THEN
    RFS [ADD1; TRUE_def; FALSE_def; UNCURRY_SIMP; ARITH_ss] THEN
    REPEAT STRIP_TAC THEN RFS [ADD1; UNCURRY_SIMP; ARITH_ss] THEN ASM_MESON_TAC [] in
  (* tac0 is tac1 with the hypotheses hs of the certificates hidden from the  *)
  (* simplifier and MESON (RFS rewrote every assumption with them: 22 s for   *)
  (* candle_kernelProg's exec, 0.3 s without them); they stay assumptions of   *)
  (* the goals the certificates are applied in, so the proof is the same       *)
  (* theorem; the tactics below are the original ones, tried if tac0 fails    *)
  let hide_hs (tac : tactic) : tactic = fun (asl, w) ->
    tac (filter (fun (_,th) -> not (mem (concl th) hs_l)) asl, w) in
  let tac0 =
    DISCH_THEN (fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
    MATCH_MP_TAC ind_thm THEN REPEAT STRIP_TAC THEN
    FIRST (map MATCH_MP_TAC ths) THEN REPEAT STRIP_TAC THEN
    hide_hs (RFS [ADD1; TRUE_def; FALSE_def; UNCURRY_SIMP; ARITH_ss] THEN ASM_MESON_TAC []) in
  let lemma =
    try prove (goal, tac0) with Failure _ ->
    try prove (goal, tac1) with Failure _ ->
    try prove (goal, tac2) with Failure _ ->
    try prove (goal, tac3) with Failure _ ->
      let (_, ml_name, _, _, _) = hd thms in
      Format.print_string ("\nERROR: Unable to prove induction for " ^ ml_name ^
                           "\nThe goal is left as an assumption of the theorem.\n");
      mt_induction_helper_thms :=
        map (fun (k, (_,(th,_))) -> (ml_name ^ "_helper_" ^ string_of_int k, th))
            (zip (0 -- (length goals - 1)) goals) @ !mt_induction_helper_thms;
      DISCH hs (UNDISCH_ALL (ASSUME goal)) in
  let results = map SPEC_ALL (CONJUNCTS (UNDISCH lemma)) in
  map (fun (th, (fname, ml_fname, def, _, pre)) -> (fname, ml_fname, def, th, pre))
      (zip results thms);;

let mt_VALID_REFS_PRED_tm =
  `VALID_REFS_PRED:(REFS->hprop)#((FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list))->bool`;;

(* the recursive branch of m_translate_main *)
let mt_translate_main_rec thms ind =
  let mk_Recclosure_part (fname, ml_fname, def, th, v) =
    let fname = mk_mlstring ml_fname in
    let name = mk_mlstring (fst (dest_var v)) in
    let body = rand (rator (rator (concl (tr_UNDISCH_ALL th)))) in
    mk_pair (fname, mk_pair (name, body)) in
  let parts = map mk_Recclosure_part thms in
  let recc = tr_mk_list (parts, type_of (hd parts)) in
  let move_VALID_REFS_PRED_to_assums th =
    let pat = mk_comb (inst [!mt_refs_type, mt_REFS_ty] mt_VALID_REFS_PRED_tm, !mt_H) in
    let pat = inst (type_match (fst (dest_fun_ty (type_of (rator pat)))) (type_of !mt_H) []) pat in
    REWRITE_RULE [ASSUME pat] th in
  let apply_recc (fname, ml_fname, def, th, v) =
    let th = mt_apply_EvalM_Recclosure recc ml_fname v th in
    let th = clean_assumptions th in
    let th = CONV_RULE (DEPTH_CONV ETA_CONV) th in
    let th = INST [mt_cl_env, mt_env2; mt_cl_env, mt_shadow_env] th in
    let th = REWRITE_RULE [] th in
    let th = CONV_RULE (RATOR_CONV (RAND_CONV (REWRITE_CONV [tr_EVAL_T_F]))) th in
    let th = move_VALID_REFS_PRED_to_assums (clean_assumptions th) in
    (fname, ml_fname, def, th) in
  let thms = map apply_recc thms in
  (* the preconditions *)
  let thms = mt_extract_precondition_rec thms in
  (* the induction, for recursive functions without preconditions *)
  let thms = match thms with
               (_,_,_,_,Some _)::_ -> thms
             | _ -> mt_apply_ind thms ind in
  let fix_thm th =
    let th = SIMP_EqualityType_ASSUMS (mt_remove_Eq th) in
    tr_UNDISCH_ALL (SPEC_ALL (tr_UNDISCH_ALL (REWRITE_RULE [GSYM IMP_IMP] (DISCH_ALL th)))) in
  let results = map (fun (fname, ml_fname, def, th, pre) ->
                       (fname, ml_fname, def, fix_thm th, pre)) thms in
  mt_induction_helper_thms := map (fun (n, th) -> (n, fix_thm th)) !mt_induction_helper_thms;
  results;;

let () = mt_rec_hook := mt_translate_main_rec;;

(* the recursive branch of m_translate: the Dletrec and the certificates *)
let mt_translate_rec_store results =
  let recc = rand (rator (rand (find (mt_can_match mt_LOOKUP_VAR_pat)
                                  (hyp ((fun (_,_,_,th,_) -> th) (hd results)))))) in
  let curr_env = mt_get_curr_env () in
  let ii = INST [curr_env, mt_cl_env] in
  let v_names = map (fun (f,_,_,_,_) -> find_const_name (f ^ "_v")) results in
  let _ = if not !mt_local_state_init_H then
            ml_prog_update (ml_prog_add_Dletrec ml_prog_unknown_loc recc v_names) in
  let v_defs = if not !mt_local_state_init_H
               then fst (chop_list (length v_names) (get_curr_v_defs ())) else [] in
  (* the environment after the declaration (HOL4 evaluates get_curr_env ()  *)
  (* again here) *)
  let jj = INST (if !mt_local_state_init_H then [] else [mt_get_curr_env (), mt_env]) in
  let lemmas = LOOKUP_VAR_def :: map GSYM v_defs in
  mt_induction_helper_thms :=
    map (fun (name, th) ->
           let th' = DISCH_ALL (clean_assumptions (REWRITE_RULE [ml_lookup_var_def]
                       (REWRITE_RULE lemmas (mt_disch_asms (jj (ii th)))))) in
           let _ = tr_save_thm name th' in
           Format.print_string ("Saved theorem ____ :" ^ name ^ "\n");
           (name, th')) !mt_induction_helper_thms;
  let inst_envs (fname, ml_fname, def, th, pre) =
    let th = jj (ii th) in
    let state_var = get_EvalM_state (concl th) in
    let th = GEN state_var th in
    let th = CONV_RULE (BINDER_CONV (RATOR_CONV (RAND_CONV (RATOR_CONV (RATOR_CONV
               (RAND_CONV (PURE_REWRITE_CONV [ArrowM_def]))))))) th in
    let th = try MATCH_MP EvalM_Var_ArrowP th
             with Failure _ -> MATCH_MP EvalM_Var_ArrowP_EqSt th in
    let th = PURE_REWRITE_RULE [GSYM ArrowM_def] th in
    let assum = fst (dest_imp (concl th)) in
    let v = rand (find (fun h -> mt_can_match assum h) (hyp th)) in
    let th = UNDISCH (INST [v, rand assum] th) in
    let th = REWRITE_RULE lemmas (mt_disch_asms th) in
    let th = REWRITE_RULE [ml_lookup_var_def] th in
    let th = tr_UNDISCH_ALL (clean_assumptions th) in
    let th = tr_drop_T_hyps th in
    let pre_def = match pre with None -> TRUTH | Some d -> d in
    if !mt_local_state_init_H then
      (mt_add_dynamic_v_thms (fname, ml_fname, th, pre_def); th)
    else
      (add_v_thms (fname, ml_fname, th, pre_def);
       tr_save_thm (fname ^ "_v_thm") th) in
  end_itlist CONJ (map inst_envs results);;

let () = mt_rec_store_hook := mt_translate_rec_store;;

(* ------------------------------------------------------------------------- *)
(* Locally initialised stores: update_local_precondition and m_translate_run *)
(* (HOL4 update_local_precondition, compute_env_index,                      *)
(* instantiate_local_environment, clean_lookup_assums,                      *)
(* create_local_fun_defs, create_local_references, apply_Eval_Fun_Eq,       *)
(* m_translate_run_abstract_parameters, m_translate_run_preprocess_def,      *)
(* m_translate_run)                                                          *)
(* ------------------------------------------------------------------------- *)

(* HOL4 remove_Eq_from_v_thm (the monadic version: EqSt, then Eq) *)
let mt_remove_Eq_from_v_thm th =
  let foo v th =
    let th = MATCH_MP FUN_FORALL_INTRO (GEN v th) in
    let th = REWRITE_RULE [FUN_QUANT_SIMP] th in
    let th = PURE_REWRITE_RULE [ArrowM_def] th in
    let th = REWRITE_RULE [M_FUN_QUANT_SIMP] th in
    PURE_REWRITE_RULE [GSYM ArrowM_def] th in
  let try_foo v th = try foo v th with Failure _ -> th in
  let vs = map rand (tr_find_terms (mt_can_match mt_EqSt_pat) (concl th)) in
  let th = rev_itlist try_foo vs th in
  let vs = map rand (tr_find_terms (mt_can_match mt_Eq_pat) (concl th)) in
  rev_itlist try_foo vs th;;

let update_local_precondition new_pre =
  let update_aux (name, ml_name, tm, th, pre, md) =
    let th1 = mt_disch_asms th in
    let (new_pre, th1) =
      if is_imp (concl (SPEC_ALL new_pre)) then
        ((try MATCH_MP ml_IMP_EQ_T (MP (mt_disch_asms new_pre) TRUTH) with Failure _ -> new_pre)
         |> PURE_REWRITE_RULE [GSYM CONJ_ASSOC],
         PURE_REWRITE_RULE [GSYM CONJ_ASSOC] th1)
      else (new_pre, th1) in
    let th2 = PURE_REWRITE_RULE [new_pre; PRECONDITION_T] th1 in
    if aconv (concl th1) (concl th2) then (name, ml_name, tm, th, pre, md) else
    let th2 = REWRITE_RULE [] th2 in
    let th = mt_remove_Eq_from_v_thm th2 in
    Format.print_string ("Updating " ^ name ^ "_v_thm\n");
    let new_pre = if tr_can_find_term is_PRECONDITION (concl (SPEC_ALL th))
                  then new_pre else TRUTH in
    (name, ml_name, tm, tr_UNDISCH_ALL th, new_pre, md) in
  mt_dynamic_v_thms := map update_aux !mt_dynamic_v_thms;
  new_pre;;

let mt_compute_env_index env =
  let env_name = fst (dest_var env) in
  let n = String.length !mt_local_environment_var_name in
  int_of_string (String.sub env_name n (String.length env_name - n));;

let mt_instantiate_local_environment th =
  let env = rand (rator (rator (rator (rator (concl th))))) in
  INST [mt_get_curr_env (), env] th;;

let mt_clean_lookup_assums th =
  (* the literals' injectivity decides the name equations, as HOL4's        *)
  (* mlstring_rewrites and list_ss do (the kit's simpset alone left equations *)
  (* ASCII .. = ASCII .. of characters, so GEN failed with ABS)               *)
  let c = CAKE_SIMP_CONV [build_rec_env_def; lookup_var_write; LOOKUP_ASSUM_SIMP; ITLIST;
                          injectivity "mlstring"; injectivity "char"; CONS_11;
                          NOT_CONS_NIL; NOT_NIL_CONS] in
  let th = itlist (fun h th ->
             let eq = c h in
             if rand (concl eq) = h then th
             else if rand (concl eq) = mt_T_tm then PROVE_HYP (EQT_ELIM eq) th
             else PROVE_HYP (EQ_MP (SYM eq) (ASSUME (rand (concl eq)))) th) (hyp th) th in
  try MP (DISCH mt_T_tm th) TRUTH with Failure _ -> th;;

let mt_is_Recclosure tm = tr_head_is "Recclosure" tm;;

(* the closures of the dynamically specified functions become local         *)
(* function declarations (HOL4 create_local_fun_defs)                        *)
let mt_create_local_fun_defs th =
  let assums = filter (mt_can_match mt_nsLookup_pat) (hyp th) in
  let get_name_expr tm = (rand (rand (rand (rator tm))), rand (rand tm)) in
  let lookup_info = map get_name_expr assums in
  let lookup_info = filter (fun (_, y) -> not (is_var y)) lookup_info in
  let get_clenv_index_var (name, expr) =
    let clenv = rand (rator (rator expr)) in
    (if is_var clenv && type_of clenv = mt_venv_ty then () else failwith "get_env_var");
    (mt_compute_env_index clenv, (clenv, name, expr)) in
  let lookup_info = mapfilter get_clenv_index_var lookup_info in
  (* one definition per environment, the newest first *)
  let rec dedup l = match l with
      [] -> []
    | (i,x)::t -> (i,x) :: dedup (filter (fun (j,_) -> j <> i) t) in
  let defs_info = dedup (sort (fun (i1,_) (i2,_) -> i1 > i2) lookup_info) in
  let defs_info = map snd defs_info in
  if defs_info = [] then th else
  let current_env = rand (rator (rator (rator (rator (concl th))))) in
  let all_envs = map (fun (e,_,_) -> e) defs_info in
  let all_envs = current_env :: fst (chop_list (length all_envs - 1) all_envs) in
  let defs_env_info = zip all_envs defs_info in
  let h_unit = inst [mt_unit_ty, `:FFI`] !mt_H in
  let create_fun_let (env_var2, (env_var1, name, fexp)) th =
    if mt_is_Recclosure fexp then
      let funs = rand (rator fexp) in
      let exp = rand (rator (rator (concl th))) in
      let st = get_EvalM_state (concl th) in
      let p = rand (rator (concl th)) in
      let lemma = ISPECL [funs; env_var1; exp; st; p; h_unit] EvalSt_Letrec_Fun in
      let assum = fst (dest_imp (concl lemma)) in
      let assum_th = EQT_ELIM ((tr_map_fst3_conv THENC tr_ALL_DISTINCT_CONV) assum) in
      let lemma = MP lemma assum_th in
      let nenv = rand (rator (rator (rator (rator (fst (dest_imp (concl lemma))))))) in
      let lemma = MP lemma (INST [nenv, env_var2] th) in
      mt_clean_lookup_assums lemma
    else
      let xv = rand (rator fexp) and fexp' = rand fexp in
      let closure_exp = list_mk_comb (mt_Closure_tm, [env_var1; xv; fexp']) in
      let nenv = mt_mk_write name closure_exp env_var1 in
      let th' = INST [nenv, env_var2] th in
      mt_clean_lookup_assums (MATCH_MP EvalSt_Let_Fun th') in
  rev_itlist create_fun_let defs_env_info th;;

(* the store of a local state: the references and arrays are allocated by  *)
(* Let declarations (HOL4 create_local_references)                           *)
let mt_create_local_references init_state th =
  let th = PURE_REWRITE_RULE [!mt_H_def] th in
  let th = PURE_ONCE_REWRITE_RULE [GSYM H_STAR_emp] th in
  let th = PURE_REWRITE_RULE [GSYM STAR_ASSOC] th in
  (* rename the state variable of the heap invariant *)
  let state_var = rand (rator (rator (rator (concl th)))) in
  let state = rand (rand (rand (rator (concl th)))) in
  let th = if is_var state_var then
             let h_eq = (RATOR_CONV (RAND_CONV (ALPHA_CONV state_var))) (rand (concl th)) in
             PURE_ONCE_REWRITE_RULE [h_eq] th
           else th in
  let p = rand (rator (concl th)) in
  let init_state_type = type_of init_state in
  (* the accessors of the two state types *)
  let fields_of ty =
    let ri = record_info (fst (dest_type ty)) in
    map (fun (f,acc,_) -> (f, inst (type_match (fst (dest_fun_ty (type_of acc))) ty []) acc))
        ri.ri_fields in
  let state_accessors = zip (map snd (fields_of (type_of state_var)))
                            (map snd (fields_of init_state_type)) in
  let accessor_rws = (record_info (fst (dest_type init_state_type))).ri_accessors in
  let get_farray_access_fun state_field =
    let accessor = rator state_field in
    snd (find (fun (x,_) -> x = accessor) state_accessors) in
  let rewrite_field_access_conv tm = CAKE_SIMP_CONV [accessor_rws] tm in
  let get_field_access_eval_thm tm =
    let tm_eq = rewrite_field_access_conv tm in
    let tm' = rhs (concl tm_eq) in
    let eval_thm = hol2deep tm' in
    CONV_RULE (RAND_CONV (RAND_CONV (PURE_ONCE_REWRITE_CONV [GSYM tm_eq]))) eval_thm in
  (* HOL4 TypeBase.accessors_of the monad state type *)
  let state_accessors_thms =
    CONJUNCTS (record_info (fst (dest_type (type_of state_var)))).ri_accessors in
  let rec create_local_refs loc_info th =
    match loc_info with
      [] -> th
    | (loc_name, loc) :: loc_info ->
        let exp = rand (rator (rator (concl th))) in
        let original_h = rand (concl th) in
        let (state_var, h_part) = dest_abs (fst (dest_pair original_h)) in
        let (h_part1, h_part2) = ms_dest_star h_part in
        let h_part2 = mk_abs (state_var, h_part2) in
        let state_field = rand h_part1 in
        let get_ref_fun = mk_abs (state_var, state_field) in
        let ty_inv = get_type_inv (type_of state_field) in
        let accessor = get_farray_access_fun state_field in
        let env = rand (rator (rator (rator (rator (concl th))))) in
        let nenv = mt_mk_write loc_name loc env in
        let gen_th = GEN loc (mt_clean_lookup_assums (INST [nenv, env] th)) in
        let head = fst (strip_comb h_part1) in
        let is_rarray = (try fst (dest_const head) = "RARRAY_REL" with Failure _ -> false) in
        let is_farray = (try fst (dest_const head) = "ARRAY_REL" with Failure _ -> false) in
        let st_name = mk_mlstring (fst (dest_var state_var)) in
        let lemma =
          if is_rarray then
            UNDISCH (BETA_RULE (ISPECL [exp; get_ref_fun; loc_name; rand ty_inv; st_name; env;
                                        h_part2; p; state_var] EvalSt_AllocEmpty))
          else if is_farray then
            let fst_tm = mt_my_list_mk_comb (mt_FST_tm, [mk_comb (accessor, init_state)]) in
            let nexp_eval = get_field_access_eval_thm fst_tm in
            let nexp = rand (rator (concl nexp_eval)) in
            let n = rand (rand (concl nexp_eval)) in
            let snd_tm = mt_my_list_mk_comb (mt_SND_tm, [mk_comb (accessor, init_state)]) in
            let xexp_eval = get_field_access_eval_thm snd_tm in
            let xexp = rand (rator (concl xexp_eval)) in
            let (ty_x, x) = dest_comb (rand (concl xexp_eval)) in
            let lemma = PURE_REWRITE_RULE [GSYM ml_NUM_def; GSYM ml_INT_def] EvalSt_Alloc in
            let lemma = UNDISCH (ISPECL [exp; nexp; n; xexp; x; rator state_field; loc_name;
                                         ty_x; env; h_part2; p; state] lemma) in
            let lemma = MATCH_MP (MATCH_MP lemma nexp_eval) xexp_eval in
            let lemma = CONV_RULE (DEPTH_CONV BETA_CONV) lemma in
            let eq_hyps = filter (fun h -> tr_head_is "ml_monad_translator_EQ" h) (hyp lemma) in
            itlist (fun g th ->
                      try let l = prove (g, REWRITE_TAC [ml_monad_translator_EQ_def] THEN
                                            SIMP [accessor_rws]) in
                          PROVE_HYP l th
                      with Failure _ -> th) eq_hyps lemma
          else
            let eval_state_field = get_field_access_eval_thm (mk_comb (accessor, init_state)) in
            let get_ref_exp = rand (rator (concl eval_state_field)) in
            let lemma = ISPECL [exp; get_ref_exp; get_ref_fun; loc_name; ty_inv; st_name; env;
                                h_part2; p; state] EvalSt_Opref in
            let lemma = PURE_REWRITE_RULE state_accessors_thms (BETA_RULE lemma) in
            MATCH_MP lemma eval_state_field in
        create_local_refs loc_info (MY_MATCH_MP lemma gen_th) in
  let th = create_local_refs !mt_dynamic_refs_bindings th in
  MATCH_MP EvalSt_to_Eval th;;

(* HOL4 apply_Eval_Fun_Eq *)
let mt_apply_Eval_Fun_Eq (vname, x) th =
  let env = get_Eval_env (concl th) in
  let v = genvar v_ty in
  let nenv = mt_mk_write vname v env in
  let th = mt_clean_lookup_assums (INST [nenv, env] th) in
  let assum = find (fun h -> is_comb h && rand h = v && rand (rator h) = x) (hyp th) in
  let x = rand (rator assum) in
  let th = CONV_RULE (RAND_CONV (RAND_CONV (tr_UNBETA_CONV x))) th in
  let th = GEN v (DISCH assum th) in
  (* HOL Light's higher-order match gives \x v. A x v for A *)
  tr_eta_inv_rule (MATCH_MP Eval_Fun_Eq th);;

let mt_m_translate_run_abstract_parameters th def params_evals =
  let params_bindings = map (fun x ->
      let c = concl x in
      (* EvalM ro env st (Var (Short name)) (PURE inv tm) H *)
      let var_exp = rand (rator (rator c)) in
      let pure = rand (rator c) in
      (rand (rand var_exp), rand pure)) params_evals in
  let th = PURE_REWRITE_RULE [GSYM def] th in
  let th = itlist mt_apply_Eval_Fun_Eq params_bindings th in
  (* the function in the theorem *)
  let f = rand (rand (concl th)) in
  let fc = fst (strip_comb (lhs (concl (SPEC_ALL def)))) in
  let f_eq = prove (mk_eq (f, fc), REWRITE_TAC [FUN_EQ_THM] THEN REWRITE_TAC []) in
  PURE_REWRITE_RULE [f_eq] th;;

let mt_m_translate_run_preprocess_def def =
  let tys = mt_get_monadic_types_inst (rand (rator (rhs (snd (strip_forall (concl def)))))) in
  (if tys <> [] then Format.print_string "m_translate_run: instantiated monadic types\n");
  let def = INST_TYPE tys def in
  register_term_types register_type (concl def);
  def;;

let mt_exc_ty_gen = `:(A,B)exc`;;

let m_translate_run def =
  let def = rename_bound_vars_rule "v" (mt_m_translate_run_preprocess_def def) in
  let (def_lhs, def_rhs) = dest_eq (snd (strip_forall (concl def))) in
  let fname = get_unique_name (fst (dest_const (repeat rator def_lhs))) in
  Format.print_string ("Translating monadic run: " ^ fname ^ "\n");
  let fname_str = mk_mlstring fname in
  let state = rand def_rhs in
  let monad_tm = rand (rator def_rhs) in
  let run_tm = rator (rator def_rhs) in
  let (monad_f, monad_params) = strip_comb monad_tm in
  (* the run constant: ml_monadBase_run, or a run_NAME of define_run *)
  let using_monadBase_run = (try fst (dest_const run_tm) = "ml_monadBase_run"
                             with Failure _ -> false) in
  let run_def = if using_monadBase_run then ml_monadBase_run_def
                else try assoc (fst (dest_const run_tm)) !mb_run_defs
                     with Failure _ -> failwith ("m_translate_run: no run definition for " ^
                                                 fst (dest_const run_tm)) in
  let def = if using_monadBase_run then def else PURE_REWRITE_RULE [run_def] def in
  let (state, init_state) =
    if using_monadBase_run then (state, state)
    else (rand (rhs (concl (PURE_REWRITE_CONV [run_def] def_rhs))), state) in
  (* the EvalM predicates of the parameters *)
  let var_create_Eval tm =
    let (name, ty) = dest_var tm in
    let inv = get_type_inv ty in
    let str = mk_mlstring name in
    let result = ASSUME (mt_mk_Eval_name_RI str (mk_comb (inv, tm))) in
    let result = MATCH_MP (ISPEC_EvalM Eval_IMP_PURE) result in
    let st = get_EvalM_state (concl result) in
    let result = INST [state, st] result in
    let ro = hd (mt_dest_args (concl (tr_UNDISCH_ALL result))) in
    let result = if is_var ro then INST [mt_T_tm, ro] result else result in
    mt_check_inv "var" tm result in
  let params_evals = map var_create_Eval monad_params in
  (* the monadic specification *)
  let monad_th = lookup_dynamic_v_thm monad_f in
  let lemma = ISPEC !mt_H (INST_TYPE [!mt_refs_type, `:REFS`] Eval_IMP_PURE_EvalM_T) in
  let monad_th = MATCH_MP (SPEC_ALL lemma) monad_th in
  let monad_th = PURE_REWRITE_RULE [GSYM ArrowM_def] monad_th in
  let monad_th = INST [state, get_EvalM_state (concl monad_th)] monad_th in
  (* instantiate ro to T *)
  let ro_var = hd (snd (strip_comb (rand (rator (concl monad_th))))) in
  let monad_th = if is_var ro_var then INST [mt_T_tm, ro_var] monad_th else monad_th in
  let inst_gen_eq_vars2 st th =
    let xs = map rand (tr_find_terms (mt_can_match mt_Eq_pat) (concl th)) in
    let th = INST (map (fun v -> (genvar (type_of v), v)) (filter is_var xs)) th in
    let thc = rand (rator (rand (rator (concl (PURE_REWRITE_RULE [ArrowM_def]
                (tr_UNDISCH_ALL th)))))) in
    match get_EqSt_var thc with None -> th | Some v -> INST [st, v] th in
  let monad_th = try inst_gen_eq_vars2 state monad_th with Failure _ -> monad_th in
  let insert_param x th =
    try MY_MATCH_MP (MATCH_MP EvalM_ArrowM_EqSt_Eq th) x with Failure _ ->
    try MY_MATCH_MP (MATCH_MP EvalM_ArrowM_Eq th) x with Failure _ ->
    MY_MATCH_MP (MATCH_MP EvalM_ArrowM th) x in
  let monad_th = rev_itlist insert_param params_evals monad_th in
  let monad_th = INST_TYPE [mt_unit_ty, `:FFI`] monad_th in
  (* the exc type *)
  let exc_type_tm = rator (rator (get_type_inv mt_exc_ty_gen)) in
  let exc_type_def = try tr_fetch (fst (dest_const exc_type_tm) ^ "_def")
                     with Failure _ -> failwith "m_translate_run: the exc type needs to be registered" in
  let exc_type_def = mt_clean_exn_def exc_type_def in
  let first_clause = hd (conjuncts (concl exc_type_def)) in
  let exc_type_stamp =
    let r = rhs (snd (strip_forall first_clause)) in
    let conv = rand (fst (dest_conj (snd (strip_exists r)))) in
    rand (rand (rator conv)) |> rand in
  let exc_type_rw =
    let x = rator (rator (rator (rator (lhs (snd (strip_forall (concl (SPEC exc_type_stamp
              (CONJUNCT1 EXC_TYPE_aux_def))))))))) in
    prove (mk_eq (x, exc_type_tm),
           REWRITE_TAC [FUN_EQ_THM] THEN GEN_TAC THEN GEN_TAC THEN
           MATCH_MP_TAC exc_INDUCT THEN REWRITE_TAC [EXC_TYPE_aux_def; exc_type_def]) in
  (* the run construct *)
  let env = get_Eval_env (concl monad_th) in
  let x = get_Eval_arg (concl monad_th) in
  let exp = get_Eval_exp (concl monad_th) in
  let monad_type = rator (rand (rator (concl monad_th))) in
  let exn_type = rand monad_type in
  let ty_inv = rand (rator monad_type) in
  let th = ISPECL [exc_type_stamp; ty_inv; exn_type; x; exp;
                   inst [mt_unit_ty, `:FFI`] !mt_H; state; env] EvalM_to_EvalSt in
  let th = PURE_REWRITE_RULE [exc_type_rw] th in
  let th = UNDISCH (UNDISCH (MATCH_MP th monad_th)) in
  let th = mt_instantiate_local_environment th in
  let th = mt_create_local_fun_defs th in
  let th = mt_create_local_references init_state th in
  (* abstract the parameters *)
  let all_params = snd (strip_comb def_lhs) in
  let params_evals = map var_create_Eval all_params in
  let th = mt_m_translate_run_abstract_parameters th def params_evals in
  let th = instantiate_cons_name th in
  (* the global environment *)
  let global_env = get_curr_env () in
  let env = get_Eval_env (concl th) in
  let th = INST [global_env, env] th in
  let th = clean_assumptions (mt_disch_asms th) in
  let th = if is_imp (concl th) then th else DISCH mt_T_tm th in
  (* the precondition *)
  let th = CONV_RULE (RATOR_CONV (RAND_CONV (CAKE_SIMP_CONV [ml_monad_translator_EQ_def;
                                                             ml_PRECONDITION_def])))
             (mt_disch_asms th) in
  let precond = fst (dest_imp (concl th)) in
  let (th, pre) =
    if precond = mt_T_tm then (MP th TRUTH, TRUTH) else
    let extra_free_vars = filter (fun v -> not (mem v all_params)) (frees precond) in
    let args = extra_free_vars @ all_params in
    let pre_type = itlist (fun a t -> mk_fun_ty (type_of a) t) args bool_ty in
    let pre_var = mk_var (fname ^ "_side", pre_type) in
    let pre = list_mk_comb (pre_var, args) in
    let pre_def = tr_new_side_definition (mk_eq (pre, precond)) in
    let _ = tr_save_thm (fname ^ "_side_def") pre_def in
    let pre_eq = SPEC (lhs (concl (SPEC_ALL pre_def))) ml_PRECONDITION_def in
    let th = CONV_RULE (RATOR_CONV (RAND_CONV (PURE_REWRITE_CONV [GSYM (SPEC_ALL pre_def)] THENC
                                                 PURE_ONCE_REWRITE_CONV [GSYM pre_eq]))) th in
    (UNDISCH th, pre_def) in
  let th = PURE_REWRITE_RULE [handle_mult_def] th in
  (* store the specification *)
  let th = PURE_REWRITE_RULE [TR2AUX_Eval_Fun_rw] th in
  let clo = rand (concl th) in
  let (_, v, e) = dest_Closure clo in
  let v_name = find_const_name (fname ^ "_v") in
  ml_prog_update (ml_prog_add_Dlet_Fun ml_prog_unknown_loc fname_str v e v_name);
  let v_def = hd (get_curr_v_defs ()) in
  let th = REWRITE_RULE [GSYM v_def] th in
  let th = mt_remove_Eq_from_v_thm th in
  add_v_thms (fname, fname, th, pre);
  Format.print_string "Added to v_thms\n";
  tr_save_thm (fname ^ "_v_thm") th;;

(* ------------------------------------------------------------------------- *)
(* The resumption of a monadic translation (HOL4 m_translation_extends): the *)
(* monadic state is a component of ml_progLib's translation snapshots, so    *)
(* translation_extends restores it with the rest                            *)
(* ------------------------------------------------------------------------- *)

let m_translation_extends name = translation_extends name;;
