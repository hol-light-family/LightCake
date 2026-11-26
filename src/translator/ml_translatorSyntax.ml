(* ========================================================================= *)
(* ml_translatorSyntax: port of HOL4 translator/ml_translatorSyntax.sml     *)
(* (CakeML v3479) with the syntax of the CakeML AST and values that HOL4's  *)
(* translator takes from astSyntax, semanticPrimitivesSyntax and           *)
(* mlstringSyntax: constructors, destructors and tests for the judgements  *)
(* of ml_translator (ml_Eval, ml_Arrow, ml_Eq, ...) and for the terms of   *)
(* the generated code.  HOL Light quotations have no antiquotes: every     *)
(* term is built with mk_comb from the constants below, whose generic types *)
(* are given in full (type_invention_error).                                *)
(* ========================================================================= *)

needs "translator/ml_translator.ml";;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Generic helpers                                                           *)
(* ------------------------------------------------------------------------- *)

(* the type variables of a template are renamed apart from those of the     *)
(* arguments before matching, so that a generic constant with type          *)
(* variables A and B never captures an argument's A or B (the prototype's   *)
(* mk_Arrow bug, PLAN 1c.8 H11)                                            *)

let mlts_tyvar_count = ref 0;;

let mlts_fresh_tyvar () =
  mlts_tyvar_count := !mlts_tyvar_count + 1;
  mk_vartype ("_mlts" ^ string_of_int !mlts_tyvar_count);;

(* list_mk_icomb with the type variables of c instantiated all at once;  *)
(* a type variable of c that the arguments do not fix keeps its name        *)
let tr_list_mk_icomb (c:term) (args:term list) : term =
  let avoid = itlist (fun a l -> union (type_vars_in_term a) l) args [] in
  let clash = filter (fun tv -> mem tv avoid) (type_vars_in_term c) in
  let ren = map (fun tv -> (mlts_fresh_tyvar (), tv)) clash in
  let c' = if ren = [] then c else inst ren c in
  let rec dom_tys ty n =
    if n = 0 then [] else
    let d,r = dest_fun_ty ty in d :: dom_tys r (n-1) in
  let doms = dom_tys (type_of c') (length args) in
  let tyin = itlist2 (fun d a i -> type_match d (type_of a) i) doms args [] in
  let c'' = inst tyin c' in
  (* a renamed type variable that the arguments do not fix gets a name used *)
  (* neither by the arguments nor by c''                                     *)
  let left = filter (fun (f,_) -> mem f (type_vars_in_term c'')) ren in
  let used = ref (union avoid (type_vars_in_term c'')) in
  let pick () =
    let rec go n = let tv = mk_vartype ("A" ^ string_of_int n) in
                   if mem tv !used then go (n+1) else (used := tv :: !used; tv) in
    go 1 in
  let back = map (fun (f,_) -> (pick (), f)) left in
  list_mk_comb ((if back = [] then c'' else inst back c''), args);;

let tr_mk_icomb c x = tr_list_mk_icomb c [x];;

let rec tr_list_dest f tm =
  try let x,y = f tm in tr_list_dest f x @ tr_list_dest f y
  with Failure _ -> [tm];;

(* the arguments of an application, HOL4 dest_args *)
let tr_dest_args tm = snd (strip_comb tm);;

let tr_is_const_named s tm = is_const tm && fst (dest_const tm) = s;;

let tr_head_is s tm = tr_is_const_named s (fst (strip_comb tm));;

(* ------------------------------------------------------------------------- *)
(* Types                                                                      *)
(* ------------------------------------------------------------------------- *)

let v_ty = `:v`;;
let venv_ty = `:v sem_env`;;
let exp_ty = `:exp`;;
let pat_ty = `:pat`;;
let dec_ty = `:dec`;;
let ast_t_ty = `:ast_t`;;
let mlstring_ty = `:mlstring`;;
let ml_id_ty = `:(mlstring,mlstring)id`;;
let stamp_ty = `:stamp`;;
let mlinv_ty ty = mk_fun_ty ty (mk_fun_ty v_ty bool_ty);;

(* ------------------------------------------------------------------------- *)
(* Strings: CakeML identifiers are mlstrings implode "..."                   *)
(* ------------------------------------------------------------------------- *)

(* lists and strings from precomputed constants: HOL Light's mk_list and  *)
(* mk_string call mk_const, a linear search of the constant list (about    *)
(* 2 ms per call in a session with the whole library)                      *)
let tr_nil_tm = mk_const ("NIL",[]) and tr_cons_tm = mk_const ("CONS",[]);;
let tr_mk_list (tms,ty) =
  let nil = inst [ty,aty] tr_nil_tm and cons = inst [ty,aty] tr_cons_tm in
  itlist (fun h t -> mk_comb (mk_comb (cons,h),t)) tms nil;;
let tr_char_terms = Array.init 256 (fun i -> mk_char (Char.chr i));;
let tr_char_ty0 = `:char`;;
let tr_mk_string s =
  let rec go i acc = if i < 0 then acc else go (i - 1) (tr_char_terms.(Char.code s.[i]) :: acc) in
  tr_mk_list (go (String.length s - 1) [], tr_char_ty0);;
let tr_arb_tm = `ARB:A`;;
let tr_mk_arb ty = inst [ty,aty] tr_arb_tm;;

let tr_implode_tm = `implode`;;
let mk_mlstring s = mk_comb (tr_implode_tm, tr_mk_string s);;
let is_mlstring_literal tm =
  is_comb tm && rator tm = tr_implode_tm && can dest_string (rand tm);;
let dest_mlstring tm =
  if is_mlstring_literal tm then dest_string (rand tm)
  else failwith "dest_mlstring";;

(* ------------------------------------------------------------------------- *)
(* The AST                                                                    *)
(* ------------------------------------------------------------------------- *)

let tr_Short_tm = `Short:mlstring->(mlstring,mlstring)id`;;
let tr_Long_tm = `Long:mlstring->(mlstring,mlstring)id->(mlstring,mlstring)id`;;
let mk_Short s = mk_comb (tr_Short_tm, s);;
let mk_Long (m,i) = list_mk_comb (tr_Long_tm, [m; i]);;
let is_Short tm = is_comb tm && rator tm = tr_Short_tm;;
let is_Long tm = is_comb tm && is_comb (rator tm) && rator (rator tm) = tr_Long_tm;;
let dest_Long tm = if is_Long tm then (rand (rator tm), rand tm) else failwith "dest_Long";;

let tr_Var_tm = `Var:(mlstring,mlstring)id->exp`;;
let mk_Var id = mk_comb (tr_Var_tm, id);;
let is_Var tm = is_comb tm && rator tm = tr_Var_tm;;
let mk_Var_Short s = mk_Var (mk_Short (mk_mlstring s));;

let tr_Lit_tm = `Lit:lit->exp`;;
let mk_Lit l = mk_comb (tr_Lit_tm, l);;
let is_Lit tm = is_comb tm && rator tm = tr_Lit_tm;;

let tr_Fun_tm = `Fun:mlstring->exp->exp`;;
let mk_Fun (n,e) = list_mk_comb (tr_Fun_tm, [n; e]);;
let is_Fun tm = is_comb tm && is_comb (rator tm) && rator (rator tm) = tr_Fun_tm;;

let tr_Con_tm = `Con:((mlstring,mlstring)id)option->(exp)list->exp`;;
let mk_Con (n,es) = list_mk_comb (tr_Con_tm, [n; es]);;
let is_Con tm = is_comb tm && is_comb (rator tm) && rator (rator tm) = tr_Con_tm;;

let tr_Mat_tm = `Mat:exp->(pat#exp)list->exp`;;
let mk_Mat (e,ps) = list_mk_comb (tr_Mat_tm, [e; ps]);;

let tr_Raise_tm = `Raise:exp->exp`;;
let mk_Raise e = mk_comb (tr_Raise_tm, e);;

let tr_Pvar_tm = `Pvar:mlstring->pat`;;
let mk_Pvar n = mk_comb (tr_Pvar_tm, n);;
let tr_Pcon_tm = `Pcon:((mlstring,mlstring)id)option->(pat)list->pat`;;
let mk_Pcon (n,ps) = list_mk_comb (tr_Pcon_tm, [n; ps]);;
let tr_Plit_tm = `Plit:lit->pat`;;
let mk_Plit l = mk_comb (tr_Plit_tm, l);;

let tr_Recclosure_tm = `Recclosure:v sem_env->(mlstring#mlstring#exp)list->mlstring->v`;;
let tr_Closure_tm = `Closure:v sem_env->mlstring->exp->v`;;
let is_Recclosure tm = tr_head_is "Recclosure" tm && length (tr_dest_args tm) = 3;;
let is_Closure tm = tr_head_is "Closure" tm && length (tr_dest_args tm) = 3;;
let dest_Closure tm =
  match tr_dest_args tm with [a;b;c] when is_Closure tm -> (a,b,c)
  | _ -> failwith "dest_Closure";;

let tr_Conv_tm = `Conv:(stamp)option->(v)list->v`;;
let mk_Conv (s,vs) = list_mk_comb (tr_Conv_tm, [s; vs]);;
let is_Conv tm = tr_head_is "Conv" tm && length (tr_dest_args tm) = 2;;
let dest_Conv tm =
  match tr_dest_args tm with [a;b] when is_Conv tm -> (a,b)
  | _ -> failwith "dest_Conv";;

let tr_TypeStamp_tm = `TypeStamp:mlstring->num->stamp`;;
let mk_TypeStamp (s,n) = list_mk_comb (tr_TypeStamp_tm, [s; n]);;
let is_TypeStamp tm = tr_head_is "TypeStamp" tm && length (tr_dest_args tm) = 2;;
let dest_TypeStamp tm =
  match tr_dest_args tm with [a;b] when is_TypeStamp tm -> (a,b)
  | _ -> failwith "dest_TypeStamp";;
let tr_ExnStamp_tm = `ExnStamp:num->stamp`;;
let mk_ExnStamp n = mk_comb (tr_ExnStamp_tm, n);;
let is_ExnStamp tm = is_comb tm && rator tm = tr_ExnStamp_tm;;
let dest_ExnStamp tm = if is_ExnStamp tm then rand tm else failwith "dest_ExnStamp";;

let tr_unknown_loc_tm = `unknown_loc`;;

let tr_Dtype_tm = `Dtype:locs->((mlstring)list#mlstring#(mlstring#(ast_t)list)list)list->dec`;;
let mk_Dtype tds = list_mk_comb (tr_Dtype_tm, [tr_unknown_loc_tm; tds]);;
let tr_Dexn_tm = `Dexn:locs->mlstring->(ast_t)list->dec`;;
let mk_Dexn (n,ts) = list_mk_comb (tr_Dexn_tm, [tr_unknown_loc_tm; n; ts]);;
let tr_Dtabbrev_tm = `Dtabbrev:locs->(mlstring)list->mlstring->ast_t->dec`;;
let mk_Dtabbrev (name,t) =
  list_mk_comb (tr_Dtabbrev_tm, [tr_unknown_loc_tm; tr_mk_list([],mlstring_ty); name; t]);;

let tr_Atvar_tm = `Atvar:mlstring->ast_t`;;
let tr_Atfun_tm = `Atfun:ast_t->ast_t->ast_t`;;
let tr_Attup_tm = `Attup:(ast_t)list->ast_t`;;
let tr_Atapp_tm = `Atapp:(ast_t)list->(mlstring,mlstring)id->ast_t`;;
let mk_Atvar s = mk_comb (tr_Atvar_tm, s);;
let mk_Atfun (a,b) = list_mk_comb (tr_Atfun_tm, [a; b]);;
let mk_Attup ts = mk_comb (tr_Attup_tm, tr_mk_list (ts, ast_t_ty));;
let mk_Atapp (ts,id) = list_mk_comb (tr_Atapp_tm, [tr_mk_list (ts, ast_t_ty); id]);;

(* ------------------------------------------------------------------------- *)
(* The judgements and markers of ml_translator                               *)
(* ------------------------------------------------------------------------- *)

let tr_Eval_tm = `ml_Eval:v sem_env->exp->(v->bool)->bool`;;
let mk_Eval (env,exp,p) = list_mk_comb (tr_Eval_tm, [env; exp; p]);;
let dest_Eval tm =
  match strip_comb tm with
    (c,[env;exp;p]) when c = tr_Eval_tm -> (env,exp,p)
  | _ -> failwith "dest_Eval";;
let is_Eval tm = can dest_Eval tm;;

let tr_Arrow_tm = `ml_Arrow:(A->v->bool)->(B->v->bool)->(A->B)->v->bool`;;
let mk_Arrow (a,b) = tr_list_mk_icomb tr_Arrow_tm [a; b];;
let is_Arrow tm = tr_head_is "ml_Arrow" tm && length (tr_dest_args tm) = 2;;
let dest_Arrow tm =
  match tr_dest_args tm with [a;b] when is_Arrow tm -> (a,b)
  | _ -> failwith "dest_Arrow";;

let tr_Eq_tm = `ml_Eq:(A->v->bool)->A->A->v->bool`;;
let mk_Eq (a,x) = tr_list_mk_icomb tr_Eq_tm [a; x];;
let is_Eq tm = tr_head_is "ml_Eq" tm && length (tr_dest_args tm) = 2;;
let dest_Eq tm =
  match tr_dest_args tm with [a;x] when is_Eq tm -> (a,x)
  | _ -> failwith "dest_Eq";;

let tr_And_tm = `ml_And:(A->v->bool)->(A->bool)->A->v->bool`;;
let mk_And (a,p) = tr_list_mk_icomb tr_And_tm [a; p];;

let tr_PRECONDITION_tm = `ml_PRECONDITION`;;
let mk_PRECONDITION b = mk_comb (tr_PRECONDITION_tm, b);;
let is_PRECONDITION tm = is_comb tm && rator tm = tr_PRECONDITION_tm;;

let tr_CONTAINER_tm = `ml_CONTAINER:A->A`;;
let mk_CONTAINER x = tr_mk_icomb tr_CONTAINER_tm x;;
let is_CONTAINER tm = is_comb tm && tr_is_const_named "ml_CONTAINER" (rator tm);;

let tr_TAG_tm = `ml_TAG:B->A->A`;;
let mk_TAG (n,x) = tr_list_mk_icomb tr_TAG_tm [n; x];;

let tr_PreImp_tm = `ml_PreImp`;;
let mk_PreImp (b1,b2) = list_mk_comb (tr_PreImp_tm, [b1; b2]);;
let is_PreImp tm = tr_head_is "ml_PreImp" tm && length (tr_dest_args tm) = 2;;

let tr_EqualityType_tm = `EqualityType:(A->v->bool)->bool`;;
let mk_EqualityType a = tr_mk_icomb tr_EqualityType_tm a;;
let is_EqualityType tm = is_comb tm && tr_is_const_named "EqualityType" (rator tm);;

let tr_IsTypeRep_tm = `IsTypeRep:(A->v)->(A->v->bool)->bool`;;
let mk_IsTypeRep (f,r) = tr_list_mk_icomb tr_IsTypeRep_tm [f; r];;
let is_IsTypeRep tm = tr_head_is "IsTypeRep" tm && length (tr_dest_args tm) = 2;;
let dest_IsTypeRep tm =
  if is_IsTypeRep tm then (rand (rator tm), rand tm) else failwith "dest_IsTypeRep";;

let tr_LOOKUP_VAR_tm = `LOOKUP_VAR`;;
let mk_LOOKUP_VAR (n,env,v) = list_mk_comb (tr_LOOKUP_VAR_tm, [n; env; v]);;

let tr_lookup_cons_tm = `ml_lookup_cons`;;
let mk_lookup_cons (n,env) = list_mk_comb (tr_lookup_cons_tm, [n; env]);;
let is_lookup_cons tm = tr_head_is "ml_lookup_cons" tm && length (tr_dest_args tm) = 2;;

let tr_write_tm = `ml_write`;;
let mk_write (n,v,env) = list_mk_comb (tr_write_tm, [n; v; env]);;

let tr_nsLookup_tm = `nsLookup:(mlstring,mlstring,v)namespace->(mlstring,mlstring)id->(v)option`;;
let tr_sem_env_v_tm = `sem_env_v:v sem_env->(mlstring,mlstring,v)namespace`;;
let mk_nsLookup_v (env,id) =
  list_mk_comb (tr_nsLookup_tm, [mk_comb (tr_sem_env_v_tm, env); id]);;

let tr_FUN_FORALL_tm = mk_const ("FUN_FORALL", []);;

let tr_env = mk_var ("env", venv_ty);;
let tr_cl_env = mk_var ("cl_env", venv_ty);;
let tr_v_var = mk_var ("v", v_ty);;

(* the refinement invariant INV of a certificate |- ml_Eval env exp (INV t) *)
let tr_cert_tm th = let (_,_,p) = dest_Eval (concl th) in rand p;;
let tr_cert_exp th = let (_,e,_) = dest_Eval (concl th) in e;;

(* GENERATED from the naming tables doc/names.tsv and doc/ident_map.tsv:  *)
(* do not edit by hand.                                                      *)
let tr_hol4_type_table = ref [
  ("app_list",("misc","app_list"));
  ("num_set",("misc","num_set"));
  ("num_map",("misc","num_map"));
  ("mlstring",("mlstring","mlstring"));
  ("app_list_ann",("mlstring","app_list_ann"));
  ("sexp",("mlsexp","sexp"));
  ("mlsexp_token",("mlsexp","token"));
  ("mlsexp_result",("mlsexp","result"));
  ("str_tree",("mlsexp","str_tree"));
  ("pretty",("mlsexp","pretty"));
  ("alist",("namespace","alist"));
  ("id",("namespace","id"));
  ("namespace",("namespace","namespace"));
  ("lit",("ast","lit"));
  ("shift",("ast","shift"));
  ("arith",("ast","arith"));
  ("modN",("ast","modN"));
  ("varN",("ast","varN"));
  ("conN",("ast","conN"));
  ("typeN",("ast","typeN"));
  ("tvarN",("ast","tvarN"));
  ("word_size",("ast","word_size"));
  ("thunk_mode",("ast","thunk_mode"));
  ("thunk_op",("ast","thunk_op"));
  ("opb",("ast","opb"));
  ("test",("ast","test"));
  ("prim_type",("ast","prim_type"));
  ("op",("ast","op"));
  ("op_class",("ast","op_class"));
  ("ast_t",("ast","ast_t"));
  ("pat",("ast","pat"));
  ("lop",("ast","lop"));
  ("exp",("ast","exp"));
  ("type_def",("ast","type_def"));
  ("dec",("ast","dec"));
  ("fp_cmp",("fpSem","fp_cmp"));
  ("fp_uop",("fpSem","fp_uop"));
  ("fp_bop",("fpSem","fp_bop"));
  ("fp_top",("fpSem","fp_top"));
  ("ffi_outcome",("ffi","ffi_outcome"));
  ("oracle_result",("ffi","oracle_result"));
  ("shmem_op",("ffi","shmem_op"));
  ("ffiname",("ffi","ffiname"));
  ("oracle_function",("ffi","oracle_function"));
  ("oracle",("ffi","oracle"));
  ("io_event",("ffi","io_event"));
  ("final_event",("ffi","final_event"));
  ("ffi_state",("ffi","ffi_state"));
  ("ffi_result",("ffi","ffi_result"));
  ("outcome",("ffi","outcome"));
  ("behaviour",("ffi","behaviour"));
  ("stamp",("semanticPrimitives","stamp"));
  ("sem_env",("semanticPrimitives","sem_env"));
  ("v",("semanticPrimitives","v"));
  ("env_ctor",("semanticPrimitives","env_ctor"));
  ("env_val",("semanticPrimitives","env_val"));
  ("abort",("semanticPrimitives","abort"));
  ("error_result",("semanticPrimitives","error_result"));
  ("result",("semanticPrimitives","result"));
  ("store_v",("semanticPrimitives","store_v"));
  ("store",("semanticPrimitives","store"));
  ("compiler_args",("semanticPrimitives","compiler_args"));
  ("compiler_fun",("semanticPrimitives","compiler_fun"));
  ("eval_decs_state",("semanticPrimitives","eval_decs_state"));
  ("eval_oracle_fun",("semanticPrimitives","eval_oracle_fun"));
  ("eval_oracle_state",("semanticPrimitives","eval_oracle_state"));
  ("eval_state",("semanticPrimitives","eval_state"));
  ("state",("semanticPrimitives","state"));
  ("match_result",("semanticPrimitives","match_result"));
  ("eq_result",("semanticPrimitives","eq_result"));
  ("exp_or_val",("semanticPrimitives","exp_or_val"));
  ("store_ffi",("semanticPrimitives","store_ffi"));
  ("dest_thunk_ret",("semanticPrimitives","dest_thunk_ret"));
  ("opw",("backend_common","opw"));
  ("tra",("backend_common","tra"));
  ("flat_op",("flatLang","op"));
  ("ctor_id",("flatLang","ctor_id"));
  ("type_id",("flatLang","type_id"));
  ("type_group_id",("flatLang","type_group_id"));
  ("flat_pat",("flatLang","pat"));
  ("flat_exp",("flatLang","exp"));
  ("position",("pattern_common","position"));
  ("pmatchResult",("pattern_common","pmatchResult"));
  ("matchResult",("pattern_common","matchResult"));
  ("kind",("pattern_semantics","kind"));
  ("pattern_semantics_tag",("pattern_semantics","tag"));
  ("siblings",("pattern_semantics","siblings"));
  ("pattern_semantics_pat",("pattern_semantics","pat"));
  ("dTest",("pattern_semantics","dTest"));
  ("dGuard",("pattern_semantics","dGuard"));
  ("dTree",("pattern_semantics","dTree"));
  ("term",("pattern_semantics","term"));
  ("ctor",("pattern_exh","ctor"));
  ("flat_pattern_config",("flat_pattern","config"));
  ("var_name",("source_to_flat","var_name"));
  ("source_to_flat_environment",("source_to_flat","environment"));
  ("environment_generation_store",("source_to_flat","environment_generation_store"));
  ("environment_store",("source_to_flat","environment_store"));
  ("next_indices",("source_to_flat","next_indices"));
  ("source_to_flat_config",("source_to_flat","config"));
  ("const",("closLang","const"));
  ("const_part",("closLang","const_part"));
  ("int_op",("closLang","int_op"));
  ("word_op",("closLang","word_op"));
  ("block_op",("closLang","block_op"));
  ("glob_op",("closLang","glob_op"));
  ("mem_op",("closLang","mem_op"));
  ("clos_op",("closLang","op"));
  ("clos_exp",("closLang","exp"));
  ("clos_prog",("closLang","clos_prog"));
  ("clos_cc",("closLang","clos_cc"));
  ("db_var_set",("db_vars","db_var_set"));
  ("val_approx",("clos_known","val_approx"));
  ("globalOpt",("clos_known","globalOpt"));
  ("inliningDecision",("clos_known","inliningDecision"));
  ("clos_known_config",("clos_known","config"));
  ("bvl_exp",("bvl","exp"));
  ("clos_to_bvl_config",("clos_to_bvl","config"));
  ("bvi_exp",("bvi","exp"));
  ("assoc_op",("bvi_tailrec","assoc_op"));
  ("v_ty",("bvi_tailrec","v_ty"));
  ("call_block",("bvi_tmc","call_block"));
  ("data_prog",("dataLang","prog"));
  ("bvl_to_bvi_config",("bvl_to_bvi","config"));
  ("asm_reg",("asm","reg"));
  ("fp_reg",("asm","fp_reg"));
  ("imm",("asm","imm"));
  ("reg_imm",("asm","reg_imm"));
  ("binop",("asm","binop"));
  ("cmp",("asm","cmp"));
  ("asm_arith",("asm","arith"));
  ("fp",("asm","fp"));
  ("addr",("asm","addr"));
  ("memop",("asm","memop"));
  ("inst",("asm","inst"));
  ("asm",("asm","asm"));
  ("architecture",("asm","architecture"));
  ("asm_config",("asm","asm_config"));
  ("store_name",("stackLang","store_name"));
  ("stack_prog",("stackLang","prog"));
  ("wl_shift",("wordLang","shift"));
  ("wl_exp",("wordLang","exp"));
  ("cutsets",("wordLang","cutsets"));
  ("wl_prog",("wordLang","prog"));
  ("word_loc",("wordLang","word_loc"));
  ("exc",("ml_monadBase","exc"));
  ("ml_monadBase_M",("ml_monadBase","M"));
  ("store_ref",("ml_monadBase","store_ref"));
  ("reg_alloc_tag",("reg_alloc","tag"));
  ("ra_state",("reg_alloc","ra_state"));
  ("state_exn",("reg_alloc","state_exn"));
  ("clash_tree",("reg_alloc","clash_tree"));
  ("algorithm",("reg_alloc","algorithm"));
  ("ira_state",("reg_alloc","ira_state"));
  ("live_tree",("linear_scan","live_tree"));
  ("linear_scan_state",("linear_scan","linear_scan_state"));
  ("linear_scan_hidden_state",("linear_scan","linear_scan_hidden_state"));
  ("bijection_state",("linear_scan","bijection_state"));
  ("i_linear_scan_hidden_state",("linear_scan","i_linear_scan_hidden_state"));
  ("heu_data",("word_alloc","heu_data"));
  ("knowledge",("word_cse","knowledge"));
  ("copy_state",("word_copy","copy_state"));
  ("word_to_word_config",("word_to_word","config"));
  ("address",("word_bignum","address"));
  ("mini",("word_bignum","mini"));
  ("call_tree",("word_depth","call_tree"));
  ("gc_kind",("data_to_word","gc_kind"));
  ("data_to_word_config",("data_to_word","config"));
  ("word_op_type",("data_to_word","word_op_type"));
  ("word_to_stack_config",("word_to_stack","config"));
  ("lab_reg",("labLang","reg"));
  ("lab",("labLang","lab"));
  ("asm_with_lab",("labLang","asm_with_lab"));
  ("asm_or_cbw",("labLang","asm_or_cbw"));
  ("line",("labLang","line"));
  ("sec",("labLang","sec"));
  ("lab_prog",("labLang","prog"));
  ("stack_to_lab_config",("stack_to_lab","config"));
  ("shmem_info_num",("lab_to_target","shmem_info_num"));
  ("lab_to_target_config",("lab_to_target","config"));
  ("obj",("jsonLang","obj"));
  ("sExp",("displayLang","sExp"));
  ("tap_config",("presLang","tap_config"));
  ("type_ident",("typeSystem","type_ident"));
  ("t",("typeSystem","t"));
  ("tenv_val_exp",("typeSystem","tenv_val_exp"));
  ("tenv_abbrev",("typeSystem","tenv_abbrev"));
  ("tenv_ctor",("typeSystem","tenv_ctor"));
  ("tenv_val",("typeSystem","tenv_val"));
  ("type_env",("typeSystem","type_env"));
  ("backend_config",("backend","config"));
  ("backend_progs",("backend","backend_progs"));
  ("any_prog",("backend_passes","any_prog"));
  ("heap_address",("gc_shared","heap_address"));
  ("heap_element",("gc_shared","heap_element"));
  ("gc_state",("gc_shared","gc_state"));
  ("gen_gc_conf",("gen_gc","gen_gc_conf"));
  ("gen_gc_partial_conf",("gen_gc_partial","gen_gc_partial_conf"));
  ("data_sort",("gen_gc_partial","data_sort"));
  ("gen_state",("gc_combined","gen_state"));
  ("tokens_path",("tokens","path"));
  ("token",("tokens","token"));
  ("lexer_fun_symbol",("lexer_fun","symbol"));
  ("MMLnonT",("gram","MMLnonT"));
  ("NT",("gram","NT"));
  ("mlptree",("gram","mlptree"));
  ("PCstate0",("cmlPtreeConversion","PCstate0"));
  ("M",("cmlPtreeConversion","M"));
  ("ptree",("cmlPtreeConversion","ptree"));
  ("semantics_state",("semantics","state"));
  ("semantics",("semantics","semantics"));
  ("store_t",("typeSoundInvariants","store_t"));
  ("tenv_store",("typeSoundInvariants","tenv_store"));
  ("ctMap",("typeSoundInvariants","ctMap"));
  ("compiler_instance",("source_evalProof","compiler_instance"));
  ("flat_environment",("flatSem","environment"));
  ("flat_v",("flatSem","v"));
  ("install_config",("flatSem","install_config"));
  ("flat_state",("flatSem","state"));
  ("flat_dest_thunk_ret",("flatSem","dest_thunk_ret"));
  ("global_env",("source_to_flatProof","global_env"));
  ("idx_types",("source_to_flatProof","idx_types"));
  ("clos_ref",("closSem","ref"));
  ("clos_v",("closSem","v"));
  ("clos_co",("closSem","clos_co"));
  ("clos_state",("closSem","state"));
  ("clos_dest_thunk_ret",("closSem","dest_thunk_ret"));
  ("app_kind",("closSem","app_kind"));
  ("bvl_ref",("bvlSem","ref"));
  ("bvl_v",("bvlSem","v"));
  ("bvl_state",("bvlSem","state"));
  ("bvl_dest_thunk_ret",("bvlSem","dest_thunk_ret"));
  ("calls_state",("clos_callProof","calls_state"));
  ("abs_calls_state",("clos_callProof","abs_calls_state"));
  ("exn_or_ret",("bviSem","exn_or_ret"));
  ("bvi_result",("bviSem","bvi_result"));
  ("bvi_state",("bviSem","state"));
  ("bvi_dest_thunk_ret",("bviSem","dest_thunk_ret"));
  ("data_v",("dataSem","v"));
  ("stack",("dataSem","stack"));
  ("limits",("dataSem","limits"));
  ("data_state",("dataSem","state"));
  ("data_dest_thunk_ret",("dataSem","dest_thunk_ret"));
  ("buffer",("wordSem","buffer"));
  ("stack_frame",("wordSem","stack_frame"));
  ("gc_fun_type",("wordSem","gc_fun_type"));
  ("wl_state",("wordSem","state"));
  ("wl_result",("wordSem","result"));
  ("asm_state",("asmSem","asm_state"));
  ("target",("asmProps","target"));
  ("machine_result",("targetSem","machine_result"));
  ("machine_config",("targetSem","machine_config"));
  ("word8_loc",("labSem","word8_loc"));
  ("lab_state",("labSem","state"));
  ("data_to_word_memoryProof_tag",("data_to_word_memoryProof","tag"));
  ("ml_el",("data_to_word_memoryProof","ml_el"));
  ("ml_heap",("data_to_word_memoryProof","ml_heap"));
  ("word_bignumProof_state",("word_bignumProof","state"));
  ("data_to_word_gcProof_state",("data_to_word_gcProof","state"));
  ("word_instProof_result",("word_instProof","result"));
  ("stack_result",("stackSem","result"));
  ("stack_state",("stackSem","state"));
  ("word_to_stackProof_state",("word_to_stackProof","state"));
  ("word_to_stackProof_result",("word_to_stackProof","result"));
  ("stack_rawcallProof_prog",("stack_rawcallProof","prog"));
  ("result_view",("stack_to_labProof","result_view"));
  ("interference_app",("targetProps","interference_app"));
  ("cmlParse_M",("cmlParse","M"));
  ("infer_t",("infer_t","infer_t"));
  ("atom",("unify","atom"));
  ("kcockont",("unify","kcockont"));
  ("kclkont",("unify","kclkont"));
  ("kcunifkont",("unify","kcunifkont"));
  ("err_var",("infer","err_var"));
  ("loc_err_info",("infer","loc_err_info"));
  ("infer_st",("infer","infer_st"));
  ("inf_env",("infer","inf_env"));
  ("compiler_config",("compiler","config"));
  ("compile_error",("compiler","compile_error"));
  ("panLang_shift",("panLang","shift"));
  ("stcname",("panLang","stcname"));
  ("fldname",("panLang","fldname"));
  ("varname",("panLang","varname"));
  ("funname",("panLang","funname"));
  ("eid",("panLang","eid"));
  ("decname",("panLang","decname"));
  ("index",("panLang","index"));
  ("shape",("panLang","shape"));
  ("panop",("panLang","panop"));
  ("varkind",("panLang","varkind"));
  ("panLang_exp",("panLang","exp"));
  ("opsize",("panLang","opsize"));
  ("primop",("panLang","primop"));
  ("panLang_prog",("panLang","prog"));
  ("fun_decl",("panLang","fun_decl"));
  ("decl",("panLang","decl"));
  ("struct_info",("panLang","struct_info"));
  ("funcT",("ag32","funcT"));
  ("shiftT",("ag32","shiftT"));
  ("reg_immT",("ag32","reg_immT"));
  ("instruction",("ag32","instruction"));
  ("ag32_state",("ag32","ag32_state"));
  ("error",("errorMonad","error"));
  ("errorLogMonad_M",("errorLogMonad","M"));
  ("itree_el",("itreeTau","itree_el"));
  ("itree_rep",("itreeTau","itree_rep"));
  ("itree",("itreeTau","itree"));
  ("itree_next",("itreeTau","itree_next"));
  ("crep_shift",("crepLang","shift"));
  ("crep_varname",("crepLang","varname"));
  ("crep_funname",("crepLang","funname"));
  ("crepop",("crepLang","crepop"));
  ("crep_exp",("crepLang","exp"));
  ("crep_prog",("crepLang","prog"));
  ("early_exit",("crep_inline","early_exit"));
  ("loop_shift",("loopLang","shift"));
  ("loop_exp",("loopLang","exp"));
  ("loop_arith",("loopLang","loop_arith"));
  ("loop_prog",("loopLang","prog"));
  ("crep_to_loop_context",("crep_to_loop","context"));
  ("map",("mlmap","map"));
  ("staterr",("panStatic","staterr"));
  ("static_result",("panStatic","static_result"));
  ("based",("panStatic","based"));
  ("shaped_based",("panStatic","shaped_based"));
  ("reachable",("panStatic","reachable"));
  ("last_stmt",("panStatic","last_stmt"));
  ("func_info",("panStatic","func_info"));
  ("local_info",("panStatic","local_info"));
  ("global_info",("panStatic","global_info"));
  ("scope",("panStatic","scope"));
  ("panStatic_context",("panStatic","context"));
  ("exp_return",("panStatic","exp_return"));
  ("exps_return",("panStatic","exps_return"));
  ("prog_return",("panStatic","prog_return"));
  ("scoped_id",("panStatic","scoped_id"));
  ("pan_globals_context",("pan_globals","context"));
  ("pan_structs_context",("pan_structs","context"));
  ("pan_to_crep_context",("pan_to_crep","context"));
  ("any_pan_prog",("pan_passes","any_pan_prog"));
  ("keyword",("panLexer","keyword"));
  ("panLexer_token",("panLexer","token"));
  ("panLexer_atom",("panLexer","atom"));
  ("pancakeNT",("panPEG","pancakeNT"));
  ("word_lab",("panSem","word_lab"));
  ("pan_v",("panSem","v"));
  ("pan_state",("panSem","state"));
  ("pan_result",("panSem","result"));
  ("crepSem_varname",("crepSem","varname"));
  ("crepSem_funname",("crepSem","funname"));
  ("crep_state",("crepSem","state"));
  ("crep_result",("crepSem","result"));
  ("pan_semantics_run_res",("panProps","semantics_run_res"));
  ("loop_state",("loopSem","state"));
  ("loop_result",("loopSem","result"));
  ("crep_to_loopProof_semantics_run_res",("crep_to_loopProof","semantics_run_res"));
  ("bstate",("pan_itreeSem","bstate"));
  ("ev",("pan_itreeSem","ev"));
  ("pan_itreeSem_ptree",("pan_itreeSem","ptree"));
  ("fst",("pan_itreeSem","fst"));
  ("pan_to_wordProof_prog",("pan_to_wordProof","prog"));
  ("hol_result",("holSyntaxLib","result"));
  ("hol_type",("holSyntax","type"));
  ("hol_term",("holSyntax","term"));
  ("tysig",("holSyntax","tysig"));
  ("tmsig",("holSyntax","tmsig"));
  ("sig",("holSyntax","sig"));
  ("thy",("holSyntax","thy"));
  ("update",("holSyntax","update"));
  ("dbterm",("holSyntaxExtra","dbterm"));
  ("ethy",("littleTheoriesSyntax","ethy"));
  ("SIG",("littleTheoriesSyntax","SIG"));
  ("update'",("littleTheoriesSyntax","update'"));
  ("subst_step",("littleTheoriesSyntaxOldSystem","subst_step"));
  ("tyass",("holSemantics","tyass"));
  ("tyval",("holSemantics","tyval"));
  ("tmass",("holSemantics","tmass"));
  ("tmval",("holSemantics","tmval"));
  ("interpretation",("holSemantics","interpretation"));
  ("valuation",("holSemantics","valuation"));
  ("V",("setModel","V"));
  ("ffi_inner",("cfFFIType","ffi_inner"));
  ("ffi",("cfFFIType","ffi"));
  ("cf_ffi_result",("cfHeapsBase","ffi_result"));
  ("cf_loc",("cfHeapsBase","loc"));
  ("ffi_next",("cfHeapsBase","ffi_next"));
  ("heap_part",("cfHeapsBase","heap_part"));
  ("heap",("cfHeapsBase","heap"));
  ("hprop",("cfHeapsBase","hprop"));
  ("res",("cfHeapsBase","res"));
  ("ffi_proj",("cfHeapsBase","ffi_proj"));
  ("ml_state",("ml_translator","state"));
  ("cf_state",("cfApp","state"));
  ("pp_data",("mlprettyprinter","pp_data"));
  ("default_type",("mlprettyprinter","default_type"));
  ("rat",("rat","rat"));
  ("rational",("mlrat","rational"));
  ("mlset",("mlset","mlset"));
  ("ml_monad_translatorBase_state",("ml_monad_translatorBase","state"));
  ("ml_monad_translator_state",("ml_monad_translator","state"));
  ("ml_monad_translator_M",("ml_monad_translator","M"));
  ("H",("ml_monad_translator","H"));
  ("float64",("DoubleProg","float64"));
  ("instream",("TextIOProg","instream"));
  ("outstream",("TextIOProg","outstream"));
  ("inode",("fsFFI","inode"));
  ("mode",("fsFFI","mode"));
  ("IO_fs",("fsFFI","IO_fs"));
  ("thm",("holKernel","thm"));
  ("hol_refs",("holKernel","hol_refs"));
  ("hol_exn",("holKernel","hol_exn"));
  ("holKernel_M",("holKernel","M"));
  ("holKernelProof_M",("holKernelProof","M"));
  ("compute_binop",("compute_syntax","binop"));
  ("uop",("compute_syntax","uop"));
  ("compute_exp",("compute_syntax","compute_exp"));
  ("cv",("compute_exec","cv"));
  ("ce",("compute_exec","ce"));
  ("holKernelPmatch_M",("holKernelPmatch","M"));
  ("ml_hol_kernel_funsProg_state",("ml_hol_kernel_funsProg","state"));
  ("perms_loc",("perms","loc"));
  ("permission",("perms","permission"))
  ];;

let tr_hol4_name_table = ref [
  ("combin_K",("combin","K","k"));
  ("mlstring_shrink",("mlstring","shrink","shrink"));
  ("PAIR_MAP",("pair","##","map"));
  ("DoubleProg_construct",("DoubleProg","construct","construct"));
  ("DoubleProg_exponent",("DoubleProg","exponent","exponent"));
  ("DoubleProg_sign",("DoubleProg","sign","sign"));
  ("DoubleProg_significand",("DoubleProg","significand","significand"));
  ("ListProg_FMAP_EQ_ALIST",("ListProg","FMAP_EQ_ALIST","fmap_eq_alist"));
  ("ListProg_FMAP_TYPE",("ListProg","FMAP_TYPE","fmap_type"));
  ("RatProg_pair_add",("RatProg","pair_add","pair_add"));
  ("RatProg_pair_compare",("RatProg","pair_compare","pair_compare"));
  ("RatProg_pair_denom",("RatProg","pair_denom","pair_denom"));
  ("RatProg_pair_floor",("RatProg","pair_floor","pair_floor"));
  ("RatProg_pair_inv",("RatProg","pair_inv","pair_inv"));
  ("RatProg_pair_is_int",("RatProg","pair_is_int","pair_is_int"));
  ("RatProg_pair_le",("RatProg","pair_le","pair_le"));
  ("RatProg_pair_lt",("RatProg","pair_lt","pair_lt"));
  ("RatProg_pair_mul",("RatProg","pair_mul","pair_mul"));
  ("RatProg_pair_num",("RatProg","pair_num","pair_num"));
  ("RatProg_pair_sub",("RatProg","pair_sub","pair_sub"));
  ("RuntimeProg_debugMsg",("RuntimeProg","debugMsg","debugmsg"));
  ("RuntimeProg_fail",("RuntimeProg","fail","fail"));
  ("RuntimeProg_fullGC",("RuntimeProg","fullGC","fullgc"));
  ("minimal",("While","LEAST","least"));
  ("Word64Prog_var_word_asr",("Word64Prog","var_word_asr","var_word_asr"));
  ("Word64Prog_var_word_lsl",("Word64Prog","var_word_lsl","var_word_lsl"));
  ("Word64Prog_var_word_lsr",("Word64Prog","var_word_lsr","var_word_lsr"));
  ("Word64Prog_var_word_ror",("Word64Prog","var_word_ror","var_word_ror"));
  ("Word8ArrayProof_findi",("Word8ArrayProof","findi","findi"));
  ("Word8Prog_var_word_asr",("Word8Prog","var_word_asr","var_word_asr"));
  ("Word8Prog_var_word_lsl",("Word8Prog","var_word_lsl","var_word_lsl"));
  ("Word8Prog_var_word_lsr",("Word8Prog","var_word_lsr","var_word_lsr"));
  ("Word8Prog_var_word_ror",("Word8Prog","var_word_ror","var_word_ror"));
  ("ITER",("arithmetic","FUNPOW","funpow"));
  ("balanced_map_delete",("balanced_map","delete","delete"));
  ("balanced_map_delta",("balanced_map","delta","delta"));
  ("balanced_map_empty",("balanced_map","empty","empty"));
  ("balanced_map_every",("balanced_map","every","every"));
  ("balanced_map_exists",("balanced_map","exists","exists"));
  ("balanced_map_filter",("balanced_map","filter","filter"));
  ("balanced_map_fromList",("balanced_map","fromList","fromlist"));
  ("balanced_map_glue",("balanced_map","glue","glue"));
  ("balanced_map_insert",("balanced_map","insert","insert"));
  ("balanced_map_invariant",("balanced_map","invariant","invariant"));
  ("balanced_map_link",("balanced_map","link","link"));
  ("balanced_map_link2",("balanced_map","link2","link2"));
  ("balanced_map_lookup",("balanced_map","lookup","lookup"));
  ("balanced_map_map",("balanced_map","map","map"));
  ("balanced_map_member",("balanced_map","member","member"));
  ("balanced_map_size'",("balanced_map","size","size"));
  ("balanced_map_trim",("balanced_map","trim","trim"));
  ("balanced_map_union",("balanced_map","union","union"));
  ("compute_compute",("compute","compute","compute"));
  ("compute_check",("compute_eval","check","check"));
  ("compute_dest_binary",("compute_eval","dest_binary","dest_binary"));
  ("compute_dest_cexp",("compute_eval","dest_cexp","dest_cexp"));
  ("compute_dest_num",("compute_eval","dest_num","dest_num"));
  ("compute_dest_numeral",("compute_eval","dest_numeral","dest_numeral"));
  ("compute_dest_numeral_opt",("compute_eval","dest_numeral_opt","dest_numeral_opt"));
  ("compute_do_arith",("compute_eval","do_arith","do_arith"));
  ("compute_do_binop",("compute_eval","do_binop","do_binop"));
  ("compute_do_eq",("compute_eval","do_eq","do_eq"));
  ("compute_do_fst",("compute_eval","do_fst","do_fst"));
  ("compute_do_ispair",("compute_eval","do_ispair","do_ispair"));
  ("compute_do_reln",("compute_eval","do_reln","do_reln"));
  ("compute_do_snd",("compute_eval","do_snd","do_snd"));
  ("compute_do_uop",("compute_eval","do_uop","do_uop"));
  ("compute_map",("compute_eval","map","map"));
  ("compute_mapOption",("compute_eval","mapOption","mapoption"));
  ("compute_option",("compute_eval","option","option"));
  ("compute_subst",("compute_eval","subst","subst"));
  ("compute_binop",("compute_exec","binop","binop"));
  ("compute_binop_add",("compute_exec","binop_add","binop_add"));
  ("compute_binop_div",("compute_exec","binop_div","binop_div"));
  ("compute_binop_eq",("compute_exec","binop_eq","binop_eq"));
  ("compute_binop_less",("compute_exec","binop_less","binop_less"));
  ("compute_binop_mod",("compute_exec","binop_mod","binop_mod"));
  ("compute_binop_mul",("compute_exec","binop_mul","binop_mul"));
  ("compute_binop_sub",("compute_exec","binop_sub","binop_sub"));
  ("compute_monop",("compute_exec","monop","monop"));
  ("compute_monop_fst",("compute_exec","monop_fst","monop_fst"));
  ("compute_monop_ispair",("compute_exec","monop_ispair","monop_ispair"));
  ("compute_monop_snd",("compute_exec","monop_snd","monop_snd"));
  ("compute_exec_App",("compute_exec","App","App"));
  ("compute_exec_Binop",("compute_exec","Binop","Binop"));
  ("compute_exec_Const",("compute_exec","Const","Const"));
  ("compute_exec_If",("compute_exec","If","If"));
  ("compute_exec_Let",("compute_exec","Let","Let"));
  ("compute_exec_Monop",("compute_exec","Monop","Monop"));
  ("compute_exec_Num",("compute_exec","Num","Num"));
  ("compute_exec_Pair",("compute_exec","Pair","Pair"));
  ("compute_exec_Var",("compute_exec","Var","Var"));
  ("compute_Add",("compute_syntax","Add","Add"));
  ("compute_App",("compute_syntax","App","App"));
  ("compute_Binop",("compute_syntax","Binop","Binop"));
  ("compute_Div",("compute_syntax","Div","Div"));
  ("compute_Eq",("compute_syntax","Eq","Eq"));
  ("compute_Fst",("compute_syntax","Fst","Fst"));
  ("compute_If",("compute_syntax","If","If"));
  ("compute_Ispair",("compute_syntax","Ispair","Ispair"));
  ("compute_Less",("compute_syntax","Less","Less"));
  ("compute_Let",("compute_syntax","Let","Let"));
  ("compute_Mod",("compute_syntax","Mod","Mod"));
  ("compute_Mul",("compute_syntax","Mul","Mul"));
  ("compute_Num",("compute_syntax","Num","Num"));
  ("compute_Pair",("compute_syntax","Pair","Pair"));
  ("compute_Snd",("compute_syntax","Snd","Snd"));
  ("compute_Sub",("compute_syntax","Sub","Sub"));
  ("compute_Uop",("compute_syntax","Uop","Uop"));
  ("compute_Var",("compute_syntax","Var","Var"));
  ("num_gcd",("gcd","gcd","gcd"));
  ("holKernel_ABS",("holKernel","ABS","abs"));
  ("holKernel_ALPHA_THM",("holKernel","ALPHA_THM","alpha_thm"));
  ("holKernel_ASSUME",("holKernel","ASSUME","assume"));
  ("holKernel_BETA",("holKernel","BETA","beta"));
  ("holKernel_DEDUCT_ANTISYM_RULE",("holKernel","DEDUCT_ANTISYM_RULE","deduct_antisym_rule"));
  ("holKernel_EQ_MP",("holKernel","EQ_MP","eq_mp"));
  ("holKernel_INST",("holKernel","INST","inst"));
  ("holKernel_INST_TYPE",("holKernel","INST_TYPE","inst_type"));
  ("holKernel_MK_COMB",("holKernel","MK_COMB","mk_comb"));
  ("holKernel_PROVE_HYP",("holKernel","PROVE_HYP","prove_hyp"));
  ("holKernel_REFL",("holKernel","REFL","refl"));
  ("holKernel_SYM",("holKernel","SYM","sym"));
  ("holKernel_TRANS",("holKernel","TRANS","trans"));
  ("holKernel_aconv",("holKernel","aconv","aconv"));
  ("holKernel_add_constants",("holKernel","add_constants","add_constants"));
  ("holKernel_add_def",("holKernel","add_def","add_def"));
  ("holKernel_add_type",("holKernel","add_type","add_type"));
  ("holKernel_alphavars",("holKernel","alphavars","alphavars"));
  ("holKernel_assoc",("holKernel","assoc","assoc"));
  ("holKernel_aty",("holKernel","aty","aty"));
  ("holKernel_axioms",("holKernel","axioms","axioms"));
  ("holKernel_bool_ty",("holKernel","bool_ty","bool_ty"));
  ("holKernel_bty",("holKernel","bty","bty"));
  ("holKernel_concl",("holKernel","concl","concl"));
  ("holKernel_constants",("holKernel","constants","constants"));
  ("holKernel_context",("holKernel","context","context"));
  ("holKernel_dest_abs",("holKernel","dest_abs","dest_abs"));
  ("holKernel_dest_comb",("holKernel","dest_comb","dest_comb"));
  ("holKernel_dest_const",("holKernel","dest_const","dest_const"));
  ("holKernel_dest_eq",("holKernel","dest_eq","dest_eq"));
  ("holKernel_dest_thm",("holKernel","dest_thm","dest_thm"));
  ("holKernel_dest_type",("holKernel","dest_type","dest_type"));
  ("holKernel_dest_var",("holKernel","dest_var","dest_var"));
  ("holKernel_dest_vartype",("holKernel","dest_vartype","dest_vartype"));
  ("holKernel_first_dup",("holKernel","first_dup","first_dup"));
  ("holKernel_forall",("holKernel","forall","forall"));
  ("holKernel_freesin",("holKernel","freesin","freesin"));
  ("holKernel_freesl",("holKernel","freesl","freesl"));
  ("holKernel_get_const_type",("holKernel","get_const_type","get_const_type"));
  ("holKernel_get_the_axioms",("holKernel","get_the_axioms","get_the_axioms"));
  ("holKernel_get_the_context",("holKernel","get_the_context","get_the_context"));
  ("holKernel_get_the_term_constants",("holKernel","get_the_term_constants","get_the_term_constants"));
  ("holKernel_get_the_type_constants",("holKernel","get_the_type_constants","get_the_type_constants"));
  ("holKernel_get_type_arity",("holKernel","get_type_arity","get_type_arity"));
  ("holKernel_handle_Clash",("holKernel","handle_Clash","handle_clash"));
  ("holKernel_handle_Failure",("holKernel","handle_Failure","handle_failure"));
  ("holKernel_hyp",("holKernel","hyp","hyp"));
  ("holKernel_image",("holKernel","image","image"));
  ("holKernel_inst",("holKernel","inst","inst"));
  ("holKernel_inst_aux",("holKernel","inst_aux","inst_aux"));
  ("holKernel_is_abs",("holKernel","is_abs","is_abs"));
  ("holKernel_is_comb",("holKernel","is_comb","is_comb"));
  ("holKernel_is_const",("holKernel","is_const","is_const"));
  ("holKernel_is_eq",("holKernel","is_eq","is_eq"));
  ("holKernel_is_type",("holKernel","is_type","is_type"));
  ("holKernel_is_var",("holKernel","is_var","is_var"));
  ("holKernel_is_vartype",("holKernel","is_vartype","is_vartype"));
  ("holKernel_list_to_hypset",("holKernel","list_to_hypset","list_to_hypset"));
  ("holKernel_map",("holKernel","map","map"));
  ("holKernel_mk_abs",("holKernel","mk_abs","mk_abs"));
  ("holKernel_mk_comb",("holKernel","mk_comb","mk_comb"));
  ("holKernel_mk_const",("holKernel","mk_const","mk_const"));
  ("holKernel_mk_eq",("holKernel","mk_eq","mk_eq"));
  ("holKernel_mk_fun_ty",("holKernel","mk_fun_ty","mk_fun_ty"));
  ("holKernel_mk_type",("holKernel","mk_type","mk_type"));
  ("holKernel_mk_var",("holKernel","mk_var","mk_var"));
  ("holKernel_mk_vartype",("holKernel","mk_vartype","mk_vartype"));
  ("holKernel_my_term_size",("holKernel","my_term_size","my_term_size"));
  ("holKernel_new_axiom",("holKernel","new_axiom","new_axiom"));
  ("holKernel_new_basic_definition",("holKernel","new_basic_definition","new_basic_definition"));
  ("holKernel_new_basic_type_definition",("holKernel","new_basic_type_definition","new_basic_type_definition"));
  ("holKernel_new_constant",("holKernel","new_constant","new_constant"));
  ("holKernel_new_specification",("holKernel","new_specification","new_specification"));
  ("holKernel_new_type",("holKernel","new_type","new_type"));
  ("holKernel_raconv",("holKernel","raconv","raconv"));
  ("holKernel_raise_Clash",("holKernel","raise_Clash","raise_clash"));
  ("holKernel_raise_Failure",("holKernel","raise_Failure","raise_failure"));
  ("holKernel_rand",("holKernel","rand","rand"));
  ("holKernel_rator",("holKernel","rator","rator"));
  ("holKernel_rev_assocd",("holKernel","rev_assocd","rev_assocd"));
  ("holKernel_safe_mk_eq",("holKernel","safe_mk_eq","safe_mk_eq"));
  ("holKernel_set_the_axioms",("holKernel","set_the_axioms","set_the_axioms"));
  ("holKernel_set_the_context",("holKernel","set_the_context","set_the_context"));
  ("holKernel_set_the_term_constants",("holKernel","set_the_term_constants","set_the_term_constants"));
  ("holKernel_set_the_type_constants",("holKernel","set_the_type_constants","set_the_type_constants"));
  ("holKernel_subset",("holKernel","subset","subset"));
  ("holKernel_try",("holKernel","try","try"));
  ("holKernel_type_of",("holKernel","type_of","type_of"));
  ("holKernel_type_subst",("holKernel","type_subst","type_subst"));
  ("holKernel_type_vars_in_term",("holKernel","type_vars_in_term","type_vars_in_term"));
  ("holKernel_types",("holKernel","types","types"));
  ("holKernel_tyvars",("holKernel","tyvars","tyvars"));
  ("holKernel_vsubst",("holKernel","vsubst","vsubst"));
  ("holKernel_vsubst_aux",("holKernel","vsubst_aux","vsubst_aux"));
  ("holKernel_Clash",("holKernel","Clash","Clash"));
  ("holKernel_Failure",("holKernel","Failure","Failure"));
  ("equation",("holSyntax","===","-"));
  ("hol_domain",("holSyntax","domain","domain"));
  ("hol_term_ok",("holSyntax","term_ok","term_ok"));
  ("hol_tyvars",("holSyntax","tyvars","tyvars"));
  ("proves",("holSyntax","|-","-"));
  ("hol_Abs",("holSyntax","Abs","Abs"));
  ("hol_Comb",("holSyntax","Comb","Comb"));
  ("hol_Const",("holSyntax","Const","Const"));
  ("hol_ConstSpec",("holSyntax","ConstSpec","Constspec"));
  ("hol_NewAxiom",("holSyntax","NewAxiom","Newaxiom"));
  ("hol_NewConst",("holSyntax","NewConst","Newconst"));
  ("hol_NewType",("holSyntax","NewType","Newtype"));
  ("hol_TypeDefn",("holSyntax","TypeDefn","Typedefn"));
  ("hol_Var",("holSyntax","Var","Var"));
  ("hol_bind",("holSyntaxExtra","bind","bind"));
  ("hol_db",("holSyntaxExtra","db","db"));
  ("hol_frees",("holSyntaxExtra","frees","frees"));
  ("hol_fresh",("holSyntaxExtra","fresh","fresh"));
  ("hol_insert",("holSyntaxExtra","insert","insert"));
  ("hol_union",("holSyntaxExtra","union","union"));
  ("abs",("integer","ABS","abs"));
  ("num_of_int",("integer","Num","num"));
  ("ival",("integer_word","w2i","w2i"));
  ("iword",("integer_word","i2w","i2w"));
  ("ALL",("list","EVERY","every"));
  ("BUTLAST",("list","FRONT","front"));
  ("EX",("list","EXISTS","exists"));
  ("ITLIST",("list","FOLDR","foldr"));
  ("list_of_seq",("list","GENLIST","genlist"));
  ("set_of_list",("list","set","set"));
  ("misc_between",("misc","between","between"));
  ("misc_range",("misc","range","range"));
  ("misc_steps",("misc","steps","steps"));
  ("misc_the",("misc","the","the"));
  ("misc_word_list",("misc","word_list","word_list"));
  ("misc_Append",("misc","Append","Append"));
  ("misc_List",("misc","List","List"));
  ("ml_monadBase_can",("ml_monadBase","can","can"));
  ("ml_monadBase_run",("ml_monadBase","run","run"));
  ("ml_And",("ml_translator","And","and"));
  ("ml_AppReturns",("ml_translator","AppReturns","appreturns"));
  ("ml_Arrow",("ml_translator","Arrow","arrow"));
  ("ml_BOOL",("ml_translator","BOOL","bool"));
  ("ml_CHAR",("ml_translator","CHAR","char"));
  ("ml_CONTAINER",("ml_translator","CONTAINER","container"));
  ("ml_Eq",("ml_translator","Eq","eq"));
  ("ml_Eval",("ml_translator","Eval","eval"));
  ("ml_FLOAT64",("ml_translator","FLOAT64","float64"));
  ("ml_INT",("ml_translator","INT","int"));
  ("ml_NUM",("ml_translator","NUM","num"));
  ("ml_PRECONDITION",("ml_translator","PRECONDITION","precondition"));
  ("ml_PreImp",("ml_translator","PreImp","preimp"));
  ("ml_PreImpEval",("ml_translator","PreImpEval","preimpeval"));
  ("ml_TAG",("ml_translator","TAG","tag"));
  ("ml_WORD",("ml_translator","WORD","word"));
  ("ml_empty_state",("ml_translator","empty_state","empty_state"));
  ("ml_num_of_int",("ml_translator","num_of_int","num_of_int"));
  ("ml_write_list",("ml_translator","write_list","write_list"));
  ("mlbasicsProg_append",("mlbasicsProg","append","append"));
  ("mlbasicsProg_div",("mlbasicsProg","div","div"));
  ("mlbasicsProg_eq",("mlbasicsProg","eq","eq"));
  ("mlbasicsProg_ge",("mlbasicsProg","ge","ge"));
  ("mlbasicsProg_gt",("mlbasicsProg","gt","gt"));
  ("mlbasicsProg_le",("mlbasicsProg","le","le"));
  ("mlbasicsProg_lt",("mlbasicsProg","lt","lt"));
  ("mlbasicsProg_minus",("mlbasicsProg","minus","minus"));
  ("mlbasicsProg_mk_binop",("mlbasicsProg","mk_binop","mk_binop"));
  ("mlbasicsProg_mk_unop",("mlbasicsProg","mk_unop","mk_unop"));
  ("mlbasicsProg_mod",("mlbasicsProg","mod","mod"));
  ("mlbasicsProg_neq",("mlbasicsProg","neq","neq"));
  ("mlbasicsProg_not",("mlbasicsProg","not","not"));
  ("mlbasicsProg_plus",("mlbasicsProg","plus","plus"));
  ("mlbasicsProg_strcat",("mlbasicsProg","strcat","strcat"));
  ("mlbasicsProg_times",("mlbasicsProg","times","times"));
  ("mlbasicsProg_uminus",("mlbasicsProg","uminus","uminus"));
  ("mlint_fromString",("mlint","fromString","fromstring"));
  ("mlint_int_cmp",("mlint","int_cmp","int_cmp"));
  ("mlint_int_gcd",("mlint","int_gcd","int_gcd"));
  ("mlint_num_gcd",("mlint","num_gcd","num_gcd"));
  ("mllist_collate",("mllist","collate","collate"));
  ("mllist_drop",("mllist","drop","drop"));
  ("mllist_foldl",("mllist","foldl","foldl"));
  ("mllist_foldli",("mllist","foldli","foldli"));
  ("mllist_foldli_aux",("mllist","foldli_aux","foldli_aux"));
  ("mllist_mapPartial",("mllist","mapPartial","mappartial"));
  ("mllist_mapi",("mllist","mapi","mapi"));
  ("mllist_tabulate",("mllist","tabulate","tabulate"));
  ("mloption_compare",("mloption","compare","compare"));
  ("mloption_mapPartial",("mloption","mapPartial","mappartial"));
  ("mlrat_toString",("mlrat","toString","tostring"));
  ("mlset_all",("mlset","all","all"));
  ("mlset_compare",("mlset","compare","compare"));
  ("mlset_delete",("mlset","delete","delete"));
  ("mlset_empty",("mlset","empty","empty"));
  ("mlset_exists",("mlset","exists","exists"));
  ("mlset_filter",("mlset","filter","filter"));
  ("mlset_fold",("mlset","fold","fold"));
  ("mlset_fromList",("mlset","fromList","fromlist"));
  ("mlset_insert",("mlset","insert","insert"));
  ("mlset_isSubset",("mlset","isSubset","issubset"));
  ("mlset_map",("mlset","map","map"));
  ("mlset_member",("mlset","member","member"));
  ("mlset_null",("mlset","null","null"));
  ("mlset_singleton",("mlset","singleton","singleton"));
  ("mlset_size'",("mlset","size","size"));
  ("mlset_toList",("mlset","toList","tolist"));
  ("mlset_translate",("mlset","translate","translate"));
  ("mlset_union",("mlset","union","union"));
  ("mlset_Set",("mlset","Set","Set"));
  ("mlsexp_annotate",("mlsexp","annotate","annotate"));
  ("mlsexp_flatten",("mlsexp","flatten","flatten"));
  ("mlsexp_fromString",("mlsexp","fromString","fromstring"));
  ("mlsexp_get_size",("mlsexp","get_size","get_size"));
  ("mlsexp_lex",("mlsexp","lex","lex"));
  ("mlsexp_lex_aux",("mlsexp","lex_aux","lex_aux"));
  ("mlsexp_parse",("mlsexp","parse","parse"));
  ("mlsexp_read_string",("mlsexp","read_string","read_string"));
  ("mlsexp_Append",("mlsexp","Append","Append"));
  ("mlsexp_Str",("mlsexp","Str","Str"));
  ("mlsexp_String",("mlsexp","String","String"));
  ("mlstring_collate",("mlstring","collate","collate"));
  ("mlstring_collate_aux",("mlstring","collate_aux","collate_aux"));
  ("mlstring_compare",("mlstring","compare","compare"));
  ("mlstring_concat",("mlstring","concat","concat"));
  ("mlstring_extract",("mlstring","extract","extract"));
  ("mlvector_all",("mlvector","all","all"));
  ("mlvector_collate",("mlvector","collate","collate"));
  ("mlvector_collate_aux",("mlvector","collate_aux","collate_aux"));
  ("mlvector_concat",("mlvector","concat","concat"));
  ("mlvector_exists",("mlvector","exists","exists"));
  ("mlvector_findi",("mlvector","findi","findi"));
  ("mlvector_foldl",("mlvector","foldl","foldl"));
  ("mlvector_foldli",("mlvector","foldli","foldli"));
  ("mlvector_foldli_aux",("mlvector","foldli_aux","foldli_aux"));
  ("mlvector_map",("mlvector","map","map"));
  ("mlvector_mapi",("mlvector","mapi","mapi"));
  ("mlvector_tabulate",("mlvector","tabulate","tabulate"));
  ("mlvector_toList",("mlvector","toList","tolist"));
  ("MEASURE",("prim_rec","measure","measure"));
  ("semantics_state_sem_env",("semantics","state_sem_env","-"));
  ("semantics_state_sem_st",("semantics","state_sem_st","-"));
  ("semantics_state_tenv",("semantics","state_tenv","-"));
  ("semantics_state_type_ids",("semantics","state_type_ids","-"));
  ("tokens_CharT",("tokens","CharT","Chart"));
  ("tokens_IntT",("tokens","IntT","Intt"));
  ("tokens_Mod",("tokens","Mod","Mod"));
  ("tokens_WordT",("tokens","WordT","Wordt"));
  ("val",("words","w2n","w2n"));
  ("word",("words","n2w","n2w"));
  ("word_ishr",("words","word_asr","word_asr"));
  ("word_join",("words","word_concat","word_concat"));
  ("word_shl",("words","word_lsl","word_lsl"));
  ("word_subword",("words","word_extract","word_extract"));
  ("word_ule",("words","word_ls","word_ls"));
  ("word_ult",("words","word_lo","word_lo"));
  ("word_ushr",("words","word_lsr","word_lsr"));
  ("word_zx",("words","w2w","w2w"));
  ("=+",("combin","UPDATE","update"));
  ("flip",("combin","C","c"))
  ];;
(* END GENERATED *)
