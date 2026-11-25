(* ========================================================================= *)
(* ml_progLib: port of HOL4 translator/ml_progLib.sml and                    *)
(* ml_progComputeLib.sml (CakeML v3479).  A CakeML program is built one      *)
(* declaration at a time together with the theorem                           *)
(*     |- ML_code ml_init_env blocks st                                      *)
(* (theory translator/ml_prog.ml): blocks are the open modules and local     *)
(* blocks, innermost first, each (comment, start state, declarations, env).  *)
(* Environments, states and values are abbreviated by constants THY_env,     *)
(* THY_env_0, ..., THY_st, THY_st_0, ... and NAME_v (THY the name of the     *)
(* translation, normally the file being loaded); nsLookup_conv evaluates     *)
(* lookups in such environments with the sorted-tree representations of     *)
(* alist_treeLib (O(log n) steps per lookup, cached).                        *)
(*                                                                           *)
(* HOL4's algorithm step by step: ML_code_upd and its adjusters, the same    *)
(* ML_code_* lemmas, abbreviations and lookup theorems.  Differences, forced *)
(* by HOL Light:                                                             *)
(* - OCaml names take the prefix ml_prog_ (one OCaml name space for the      *)
(*   whole build), except nsLookup_conv, nsLookup_pf_conv and the            *)
(*   translation_ functions; HOL4's theorem database is a table              *)
(*   (ml_prog_fetch "nsLookup_ListProg_env_3_pfun_eqs");                     *)
(* - one constant name space: abbreviation names are checked against the     *)
(*   whole session (HOL4: the current theory);                               *)
(* - EVAL is HOL Light's Compute with the compset ml_prog_cs (the state     *)
(*   abbreviations are added to it, as HOL4 adds them to EVAL);              *)
(* - an abbreviation with several free variables takes them curried (HOL4:  *)
(*   one tuple); in practice only ffi is free;                               *)
(* - no theory data and no export hook: finalise_translation () at the end  *)
(*   of a translation file snapshots the registered translator state under  *)
(*   the file's name, translation_extends "file" restores it (DMTCP images  *)
(*   carry the OCaml state across sessions);                                 *)
(* - HOL Light cannot delete constants: clean_state only forgets the        *)
(*   definitions;                                                            *)
(* - the last step of ML_code_upd instantiates the program variables        *)
(*   directly (MATCH_MP would traverse the whole program); remove_snocs      *)
(*   gives HOL4's result (every SNOC and APPEND list of the theorem a CONS  *)
(*   list) in one pass that builds theorems only for the changed lists.      *)
(* ========================================================================= *)

needs "translator/ml_prog.ml";;
needs "hol4/alist_treeLib.ml";;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Syntax                                                                    *)
(* ------------------------------------------------------------------------- *)

let ml_prog_verbose = ref false;;

let ml_prog_message s =
  if !ml_prog_verbose then (Format.print_string s; Format.print_flush ());;

let ml_prog_v_ty = `:v`;;
let ml_prog_env_ty = `:v sem_env`;;
let ml_prog_decs_ty = `:(dec)list`;;
let ml_prog_mlstring_ty = `:mlstring`;;
let ml_prog_num_ty = `:num`;;
let ml_prog_char_ty = `:char`;;
let ml_prog_string_ty = `:string`;;
let ml_prog_implode_tm = `implode`;;
let ml_prog_T_tm = `T`;;
let ml_prog_unknown_loc = `unknown_loc`;;

let ml_prog_is_const_named = alist_tree_is_const_named;;

(* terms in error messages, cut to a readable length *)
let ml_prog_string_of_term_short tm =
  let s = string_of_term tm in
  if String.length s <= 1000 then s
  else String.sub s 0 1000 ^ " ... (" ^ string_of_int (String.length s) ^ " characters)";;

(* lists and strings without mk_const at each call: get_const_type is a    *)
(* search of the constant list, newest first, so mk_const "NIL" costs about *)
(* 2 ms in a session with the whole library (HOL Light's mk_list and        *)
(* mk_string call it every time)                                             *)
let ml_prog_nil_tm = mk_const ("NIL",[]) and ml_prog_cons_tm = mk_const ("CONS",[]);;

let ml_prog_mk_list (tms,ty) =
  let nil = inst [ty,aty] ml_prog_nil_tm and cons = inst [ty,aty] ml_prog_cons_tm in
  itlist (fun h t -> mk_comb (mk_comb (cons,h),t)) tms nil;;

let ml_prog_char_terms = Array.init 256 (fun i -> mk_char (Char.chr i));;

let ml_prog_mk_string s =
  let rec go i acc = if i < 0 then acc else go (i - 1) (ml_prog_char_terms.(Char.code s.[i]) :: acc) in
  ml_prog_mk_list (go (String.length s - 1) [], ml_prog_char_ty);;

let ml_prog_mk_mlstring s = mk_comb (ml_prog_implode_tm, ml_prog_mk_string s);;

let ml_prog_mlstring_codes tm =
  match tm with
    Comb(Const("implode",_),s) -> map (fun c -> Char.code (dest_char c)) (dest_list s)
  | _ -> failwith "ml_prog_mlstring_codes";;

let ml_prog_dest_mlstring tm =
  match tm with
    Comb(Const("implode",_),s) ->
      implode (map (fun c -> String.make 1 (dest_char c)) (dest_list s))
  | _ -> failwith "ml_prog_dest_mlstring";;

let ml_prog_is_mlstring tm = can ml_prog_mlstring_codes tm;;

(* f applied to n arguments, f a constant of the given name *)
let ml_prog_is_app name n tm =
  let f,xs = strip_comb tm in ml_prog_is_const_named name f && length xs = n;;

let ml_prog_dest_app name n tm =
  let f,xs = strip_comb tm in
  if ml_prog_is_const_named name f && length xs = n then xs
  else failwith ("ml_prog_dest_app: " ^ name);;

let ml_prog_list_mk_pair l = end_itlist (curry mk_pair) l;;

(* the theorems of a conjunction, quantifiers stripped (HOL4 BODY_CONJUNCTS) *)
let rec ml_prog_BODY_CONJUNCTS th =
  let th = SPEC_ALL th in
  if is_conj (concl th) then
    ml_prog_BODY_CONJUNCTS (CONJUNCT1 th) @ ml_prog_BODY_CONJUNCTS (CONJUNCT2 th)
  else [th];;

let ml_prog_ISPECL_NAMED = alist_tree_ISPECL_NAMED;;

(* the antecedent of th proved by conv (HOL4 prove_assum_by_conv) *)
let ml_prog_prove_assum_by_conv conv th =
  let x,_ = dest_imp (concl th) in
  let eq = conv x in
  try MP th (EQT_ELIM eq) with Failure _ ->
    failwith ("ml_prog_prove_assum_by_conv: unable to reduce the antecedent to T; " ^
              "it reduced to: " ^ ml_prog_string_of_term_short (rand (concl eq)));;

(* ------------------------------------------------------------------------- *)
(* The theorem table (HOL4 save_thm and DB.fetch for the theorems the        *)
(* library makes: NAME_def of each abbreviation, nsLookup_C_pfun_eqs)       *)
(* ------------------------------------------------------------------------- *)

let ml_prog_thm_table = (Hashtbl.create 1000 : (string, thm) Hashtbl.t);;

let ml_prog_save_thm name th = Hashtbl.replace ml_prog_thm_table name th; th;;

let ml_prog_fetch name =
  try Hashtbl.find ml_prog_thm_table name
  with Not_found -> failwith ("ml_prog_fetch: no theorem " ^ name);;

(* ------------------------------------------------------------------------- *)
(* Comparisons of mlstring literals (the keys of the lookups)                *)
(* ------------------------------------------------------------------------- *)

let ML_PROG_MLSTRING_LT_IMPLODE = prove
 (`!s1 s2. mlstring_lt (implode s1) (implode s2) <=> string_lt s1 s2`,
  REWRITE_TAC[mlstring_lt_inv_image; inv_image_THM; explode_thm]);;

let ML_PROG_STRING_LT_NIL_R = prove
 (`!s:string. string_lt s [] <=> F`,
  REWRITE_TAC[string_lt_def]);;

let ML_PROG_STRING_LT_NIL_CONS = prove
 (`!(c:char) (s:string). string_lt [] (CONS c s) <=> T`,
  REWRITE_TAC[string_lt_def]);;

let ML_PROG_STRING_LT_CONS_EQ = prove
 (`!(c:char) (s1:string) s2. string_lt (CONS c s1) (CONS c s2) <=> string_lt s1 s2`,
  REWRITE_TAC[string_lt_def; char_lt_def; LT_REFL]);;

let ML_PROG_STRING_LT_CONS_NEQ = prove
 (`!(c1:char) c2 (s1:string) s2. ~(c1 = c2) ==>
     (string_lt (CONS c1 s1) (CONS c2 s2) <=> ORD c1 < ORD c2)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[string_lt_def; char_lt_def]);;

let ML_PROG_IMPLODE_11 = injectivity "mlstring";;

(* ORD of a character literal, cached by character code *)
let ml_prog_ord_cache = (Hashtbl.create 256 : (int, thm) Hashtbl.t);;

let ml_prog_ord_eval_conv = REWRITE_CONV [ORD_DEF; BITVAL_CLAUSES] THENC NUM_REDUCE_CONV;;

let ml_prog_ORD_CONV tm =
  match tm with
    Comb(Const("ORD",_),c) ->
      let k = Char.code (dest_char c) in
      (try Hashtbl.find ml_prog_ord_cache k with Not_found ->
       let th = ml_prog_ord_eval_conv tm in
       let _ = is_numeral (rand (concl th)) || failwith "ml_prog_ORD_CONV" in
       Hashtbl.add ml_prog_ord_cache k th; th)
  | _ -> failwith "ml_prog_ORD_CONV";;

(* the four lemmas with their variables, for INST (cheaper than SPECL) *)
let ml_prog_var_of th n = find (fun v -> fst (dest_var v) = n) (frees (concl th));;

let ml_prog_lt_nil_r = SPEC_ALL ML_PROG_STRING_LT_NIL_R;;
let ml_prog_lt_nil_r_s = ml_prog_var_of ml_prog_lt_nil_r "s";;
let ml_prog_lt_nil_cons = SPEC_ALL ML_PROG_STRING_LT_NIL_CONS;;
let ml_prog_lt_nil_cons_c = ml_prog_var_of ml_prog_lt_nil_cons "c";;
let ml_prog_lt_nil_cons_s = ml_prog_var_of ml_prog_lt_nil_cons "s";;
let ml_prog_lt_cons_eq = SPEC_ALL ML_PROG_STRING_LT_CONS_EQ;;
let ml_prog_lt_cons_eq_vs =
  map (ml_prog_var_of ml_prog_lt_cons_eq) ["c"; "s1"; "s2"];;
let ml_prog_lt_cons_neq = SPEC_ALL ML_PROG_STRING_LT_CONS_NEQ;;
let ml_prog_lt_cons_neq_vs =
  map (ml_prog_var_of ml_prog_lt_cons_neq) ["c1"; "c2"; "s1"; "s2"];;

(* string_lt s1 s2 for string literals, = T or F *)
let rec ml_prog_STRING_LT_CONV tm =
  let s1 = lhand tm and s2 = rand tm in
  if alist_tree_is_nil s2 then INST [s1,ml_prog_lt_nil_r_s] ml_prog_lt_nil_r
  else if alist_tree_is_nil s1 then
    let c,s = dest_cons s2 in
    INST [c,ml_prog_lt_nil_cons_c; s,ml_prog_lt_nil_cons_s] ml_prog_lt_nil_cons
  else
    let c1,t1 = dest_cons s1 and c2,t2 = dest_cons s2 in
    if compare c1 c2 = 0 then
      let th = INST (zip [c1;t1;t2] ml_prog_lt_cons_eq_vs) ml_prog_lt_cons_eq in
      TRANS th (ml_prog_STRING_LT_CONV (rand (concl th)))
    else
      let th = MP (INST (zip [c1;c2;t1;t2] ml_prog_lt_cons_neq_vs) ml_prog_lt_cons_neq)
                  (EQF_ELIM (CHAR_EQ_CONV (mk_eq (c1,c2)))) in
      CONV_RULE (RAND_CONV (BINOP_CONV ml_prog_ORD_CONV THENC NUM_LT_CONV)) th;;

(* mlstring_lt (implode s1) (implode s2) for literals, = T or F *)
let ML_PROG_MLSTRING_LT_CONV tm =
  match tm with
    Comb(Comb(Const("mlstring_lt",_),a),b) when ml_prog_is_mlstring a && ml_prog_is_mlstring b ->
      let th = SPECL [rand a; rand b] ML_PROG_MLSTRING_LT_IMPLODE in
      TRANS th (ml_prog_STRING_LT_CONV (rand (concl th)))
  | _ -> failwith "ML_PROG_MLSTRING_LT_CONV";;

(* implode s1 = implode s2 for literals, = T or F *)
let ML_PROG_MLSTRING_EQ_CONV tm =
  let a,b = dest_eq tm in
  if not (ml_prog_is_mlstring a && ml_prog_is_mlstring b)
  then failwith "ML_PROG_MLSTRING_EQ_CONV" else
  if compare a b = 0 then EQT_INTRO (REFL a) else
  let th = SPECL [rand a; rand b] ML_PROG_IMPLODE_11 in
  TRANS th (STRING_EQ_CONV (rand (concl th)));;

(* the side conditions of alist_treeLib on mlstring keys *)
let ml_prog_key_conv tm =
  if is_eq tm then ML_PROG_MLSTRING_EQ_CONV tm else ML_PROG_MLSTRING_LT_CONV tm;;

(* = on literals of the types that the evaluations below meet *)
let ml_prog_lit_eq_conv tm =
  let a,_ = dest_eq tm in
  let ty = type_of a in
  if ty = ml_prog_mlstring_ty then ML_PROG_MLSTRING_EQ_CONV tm
  else if ty = ml_prog_num_ty then NUM_EQ_CONV tm
  else if ty = ml_prog_char_ty then CHAR_EQ_CONV tm
  else if ty = ml_prog_string_ty then STRING_EQ_CONV tm
  else failwith "ml_prog_lit_eq_conv";;

(* ------------------------------------------------------------------------- *)
(* The compset (HOL4 EVAL for the program state, ml_progComputeLib)          *)
(* ------------------------------------------------------------------------- *)

(* ~(a = b) as a = b <=> F and b = a <=> F *)
let ml_prog_eqf_rules th =
  flat (map (fun th -> let th = SPEC_ALL th in
                       [EQF_INTRO th; EQF_INTRO (GSYM th)])
            (CONJUNCTS th));;

let ml_prog_cs =
  let cs = Compute.bool_compset () in
  Compute.set_skip cs `COND: bool -> A -> A -> A` (Some 1);
  num_compute_add_convs cs;
  Compute.add_conv (`LET:(A->B)->A->B`,2,let_CONV) cs;
  Compute.add_conv (`(=):A->A->bool`,2,ml_prog_lit_eq_conv) cs;
  Compute.add_conv (`GABS:((A->B)->bool)->A->B`,2,GEN_BETA_CONV) cs;
  let st = record_info "state" in
  Compute.add_thms
    [st.ri_accessors; st.ri_fupds; K_THM; LET_END_DEF; LENGTH; APPEND; MAP;
     REVERSE; ITLIST; ALL; ALL_DISTINCT; MEM; FST; SND; case_def "prod";
     case_def "option"; case_def "list"; case_def "id"; case_def "namespace";
     check_dup_ctors_def; build_constrs_def;
     ml_write_tdefs_def; ml_write_conses_def; ml_init_state_def;
     injectivity "option"; PAIR_EQ; injectivity "stamp"] cs;
  Compute.add_thms (ml_prog_eqf_rules (distinctness "option") @
                    ml_prog_eqf_rules (distinctness "stamp")) cs;
  cs;;

(* the theorems ml_progScript marks [compute] (HOL4's EVAL has them): the   *)
(* environment operators themselves stay symbolic, as with HOL4's           *)
(* [nocompute] definitions                                                   *)
let () =
  Compute.add_thms [nsLookup_nsAppend_Short; write_simp; write_cons_simp; write_mod_simp;
                    empty_simp; mod_defined_nsLookup_Mod1; nsLookup_nsBind_compute;
                    nsLookup_nsAppend; mod_defined_base] ml_prog_cs;;

let ML_PROG_EVAL_CONV tm = Compute.CBV_CONV ml_prog_cs tm;;

(* HOL4 ml_progComputeLib.add_env_compset: the environment rewrites for     *)
(* clients' compsets                                                         *)
let ml_prog_add_env_compset cs =
  Compute.add_thms [write_simp; write_cons_simp; write_mod_simp; empty_simp;
                    nsLookup_merge_env; mk_id_def; id_to_n_def;
                    nsLookup_nsAppend_Short] cs;;

(* ------------------------------------------------------------------------- *)
(* Lookups: the nsLookup representation of each environment constant        *)
(* (HOL4 nsLookup_repr_set, check_in_repr_set, nsLookup_pf_conv,             *)
(* nsLookup_conv)                                                            *)
(* ------------------------------------------------------------------------- *)

(* the pfun equations of each environment constant, by name *)
let ml_prog_pfun_eqs = (Hashtbl.create 1000 : (string, thm) Hashtbl.t);;

let ml_prog_pfun_eq_name c = "nsLookup_" ^ fst (dest_const c) ^ "_pfun_eqs";;

let () =
  Hashtbl.replace ml_prog_pfun_eqs "ml_init_env" nsLookup_init_env_pfun_eqs;
  ignore (ml_prog_save_thm "nsLookup_init_env_pfun_eqs" nsLookup_init_env_pfun_eqs);;

let ml_prog_nsLookup_repr_set =
  alist_tree_mk_alist_reprs (CONJ irreflexive_mlstring_lt transitive_mlstring_lt)
    ml_prog_key_conv ml_prog_mlstring_codes (fun (a:int list) b -> compare a b);;

(* the environment constants whose pfun equations are in the repr set *)
let ml_prog_pfun_eqs_in_repr = (Hashtbl.create 1000 : (string, unit) Hashtbl.t);;

let ml_prog_is_env_const tm = is_const tm && type_of tm = ml_prog_env_ty;;

let ml_prog_env_consts tms =
  setify (flat (map (find_terms ml_prog_is_env_const) tms));;

let ml_prog_get_pfun_thm c =
  try c, Hashtbl.find ml_prog_pfun_eqs (fst (dest_const c))
  with Not_found -> failwith "ml_prog_get_pfun_thm";;

let ml_prog_check_in_repr_set tms =
  let chained = Hashtbl.create 16 in
  let known c = let n = fst (dest_const c) in
                Hashtbl.mem ml_prog_pfun_eqs_in_repr n || Hashtbl.mem chained n in
  let deps t =
    mapfilter ml_prog_get_pfun_thm
      (filter (fun c -> not (known c))
         (ml_prog_env_consts (map rhs (conjuncts (concl t))))) in
  let rec mk_chain cs chain =
    match cs with
      [] -> chain
    | (c,t)::rest ->
        if known c then mk_chain rest chain else
        let ds = deps t in
        if ds = [] then (Hashtbl.replace chained (fst (dest_const c)) ();
                         mk_chain rest ((c,t)::chain))
        else mk_chain (ds @ cs) chain in
  let consts = mapfilter ml_prog_get_pfun_thm
                 (filter (fun c -> not (known c)) (ml_prog_env_consts tms)) in
  let chain = mk_chain consts [] in
  if chain = [] then () else
  let names = map (fun (c,_) -> fst (dest_const c)) (rev chain) in
  ml_prog_message ("Adding nsLookup representation thms for " ^
                   string_of_int (length names) ^ " consts [" ^
                   (if length names > 3 then hd names ^ ", ..., " ^ last names
                    else String.concat ", " names) ^ "]\n");
  List.iter (fun (c,t) ->
      List.iter (alist_tree_add_alist_repr ml_prog_nsLookup_repr_set) (CONJUNCTS t);
      Hashtbl.replace ml_prog_pfun_eqs_in_repr (fst (dest_const c)) ())
    (rev chain);;

(* cache of the lookups made, one theorem per environment constant and key *)
let ml_prog_lookup_cache = (Hashtbl.create 10000 : (string, thm) Hashtbl.t);;

let ml_prog_lookup_key tm =
  match tm with
    Comb(Comb(Const(f,_),Comb(Const(fld,_),Const(c,_))),k)
      when ml_prog_is_mlstring k ->
        Some (f ^ "|" ^ fld ^ "|" ^ c ^ "|" ^ ml_prog_dest_mlstring k)
  | _ -> None;;

(* nsLookup_Short ns nm, nsLookup_Mod1 ns nm for ns in the repr set *)
let nsLookup_pf_conv tm =
  let f,xs = strip_comb tm in
  if not (length xs = 2 && is_const f &&
          mem (fst (dest_const f)) ["nsLookup"; "nsLookup_Mod1"; "nsLookup_Short"])
  then failwith "nsLookup_pf_conv" else
  let key = ml_prog_lookup_key tm in
  match (match key with Some k -> (try Some (Hashtbl.find ml_prog_lookup_cache k)
                                    with Not_found -> None)
                      | None -> None) with
    Some th -> th
  | None ->
      ml_prog_check_in_repr_set [hd xs];
      let th = alist_tree_reprs_conv ml_prog_nsLookup_repr_set tm in
      (match key with Some k -> Hashtbl.replace ml_prog_lookup_cache k th | None -> ());
      th;;

let ml_prog_arg1_heads = ["/\\"; "\\/"; "="; "COND"; "option_CASE"; "OPTION_CHOICE"];;

let nsLookup_arg1_conv conv tm =
  let f,xs = strip_comb tm in
  if not (is_const f && mem (fst (dest_const f)) ml_prog_arg1_heads)
  then failwith "nsLookup_arg1_conv" else
  let rec go n tm =
    if n > 1 then RATOR_CONV (go (n - 1)) tm
    else if n = 1 then RAND_CONV conv tm
    else failwith "nsLookup_arg1_conv" in
  go (length xs) tm;;

(* HOL4's nsLookup_rewrs, and (an extension) the equations of ml_write,   *)
(* ml_write_cons and ml_write_mod, so that explicit writes on top of the     *)
(* environment constants evaluate too (the translator's write "x" v env)    *)
let ml_prog_nsLookup_rewrs =
  flat (map ml_prog_BODY_CONJUNCTS
    [nsLookup_eq; option_choice_f_apply; COND_CLAUSES; case_def "option";
     OPTION_CHOICE_DEF; AND_CLAUSES; OR_CLAUSES; REFL_CLAUSE; nsLookup_pf_nsBind;
     nsLookup_Short_nsAppend; nsLookup_Mod1_nsAppend; nsLookup_Short_Bind;
     nsLookup_Mod1_Bind; nsLookup_merge_env_eqs; nsLookup_empty_eqs; ALOOKUP_def;
     nsLookup_write_eqs; nsLookup_write_cons_eqs; nsLookup_write_mod_eqs]);;

let ml_prog_nsLookup_rewr_conv = GEN_REWRITE_CONV I ml_prog_nsLookup_rewrs;;

(* evaluation of nsLookup env.v id, nsLookup env.c id (and conjunctions,   *)
(* equations, conditionals and case expressions over them) to SOME x or     *)
(* NONE, for env built from environment constants, merge_env, ml_write ...  *)
(* It fails when it changes nothing (HOL4 raises UNCHANGED), so that the    *)
(* HOL4 uses DEPTH_CONV nsLookup_conv and TOP_DEPTH_CONV nsLookup_conv      *)
(* terminate; where HOL4 composes it with THENC, use TRY_CONV nsLookup_conv *)
let rec nsLookup_conv tm =
  CHANGED_CONV
    (REPEATC (BETA_CONV ORELSEC ml_prog_nsLookup_rewr_conv ORELSEC
              RATOR_CONV ml_prog_nsLookup_rewr_conv ORELSEC
              nsLookup_arg1_conv (nsLookup_conv ORELSEC ML_PROG_MLSTRING_EQ_CONV) ORELSEC
              CHANGED_CONV nsLookup_pf_conv)) tm;;

(* the lookups in compsets (HOL4 adds nsLookup_conv to EVAL's global       *)
(* compset): nsLookup_eq, and nsLookup_conv on nsLookup_Short and           *)
(* nsLookup_Mod1 applications; in ml_prog_cs, and for clients' compsets     *)
let ml_prog_add_nsLookup_convs cs =
  Compute.add_thms [nsLookup_eq] cs;
  List.iter (fun c -> Compute.add_conv (c,2,nsLookup_conv) cs)
    [mk_const ("nsLookup_Short",[]); mk_const ("nsLookup_Mod1",[])];;

let () = ml_prog_add_nsLookup_convs ml_prog_cs;;

(* lookups of variables and constructors to T/F: ml_lookup_cons id env =   *)
(* r, ml_lookup_var n env = r, nsLookup (sem_env_v env) id = r, ...         *)
(* (HOL4 ml_translatorLib's prove_lookup_cons_eq; for the translator)      *)
let ml_prog_lookup_eq_conv tm =
  (REWRITE_CONV [ml_lookup_cons_def; ml_lookup_var_def] THENC
   TOP_DEPTH_CONV nsLookup_conv THENC ML_PROG_EVAL_CONV) tm;;

(* ------------------------------------------------------------------------- *)
(* The program state                                                         *)
(* ------------------------------------------------------------------------- *)

type ml_prog_state =
  { mlps_st_defs : thm list;    (* state abbreviations, newest first *)
    mlps_env_defs : thm list;   (* environment abbreviations, newest first *)
    mlps_v_defs : thm list;     (* value abbreviations, newest first *)
    mlps_thm : thm };;          (* |- ML_code ml_init_env blocks st *)

(* the name of the translation (HOL4 current_theory): set explicitly, else  *)
(* the file being loaded, else the file of cake_begin                       *)
let ml_prog_theory_name = ref (None : string option);;

let ml_prog_set_theory_name s = ml_prog_theory_name := s;;

let ml_prog_current_theory () =
  let base f = Filename.remove_extension (Filename.basename f) in
  match !ml_prog_theory_name with
    Some n -> n
  | None ->
  match !cake_loading with
    f::_ -> base f
  | [] -> match !cake_context with Some f -> base f | None -> "ml_prog";;

(* names of abbreviations (HOL4 ml_name, is_const_str, find_name); the     *)
(* counters only make the search for the first free NAME_n start late      *)
let ml_prog_ok_char c =
  ('0' <= c && c <= '9') || ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z') ||
  c = '_' || c = '\'';;

let ml_prog_ml_name s =
  let b = Buffer.create (String.length s) in
  String.iter (fun c -> if ml_prog_ok_char c then Buffer.add_char b c
                        else Buffer.add_string b ("c" ^ string_of_int (Char.code c))) s;
  Buffer.contents b;;

(* constant names, by a hash table kept up to date with the constant list *)
(* of the kernel (new constants are consed to its head): can get_const_type *)
(* searches the whole list (about 2 ms in a session of the whole library)    *)
let ml_prog_const_names = (Hashtbl.create 50000 : (string, unit) Hashtbl.t);;

let ml_prog_consts_seen = ref ([] : (string * hol_type) list);;

let ml_prog_refresh_consts () =
  let l = constants () in
  if l == !ml_prog_consts_seen then () else
  let rec walk l =
    if l == !ml_prog_consts_seen then true else
    match l with
      [] -> false
    | (n,_)::t -> Hashtbl.replace ml_prog_const_names n (); walk t in
  if not (walk l) then
    (Hashtbl.reset ml_prog_const_names;
     List.iter (fun (n,_) -> Hashtbl.replace ml_prog_const_names n ()) l);
  ml_prog_consts_seen := l;;

let ml_prog_is_const_str s =
  ml_prog_refresh_consts (); Hashtbl.mem ml_prog_const_names s;;

let ml_prog_name_counters = (Hashtbl.create 100 : (string, int) Hashtbl.t);;

let ml_prog_find_name name =
  let n0 = try Hashtbl.find ml_prog_name_counters name with Not_found -> 0 in
  let rec aux n =
    let s = name ^ "_" ^ string_of_int n in
    if ml_prog_is_const_str s then aux (n + 1)
    else (Hashtbl.replace ml_prog_name_counters name (n + 1); s) in
  aux n0;;

(* the theory (translation) in which each abbreviation was defined *)
let ml_prog_abbrev_theory = (Hashtbl.create 1000 : (string, string) Hashtbl.t);;

(* HOL4 define_abbrev for_eval name tm: name vars = tm, vars the free       *)
(* variables of tm sorted by name; for_eval adds it to the compset.  A name *)
(* that is taken: by an abbreviation of the current translation, HOL4's     *)
(* find_name (name_0, name_1, ...); by any other constant (HOL Light has    *)
(* one name space; HOL4 only looks at the current theory), the name with    *)
(* the translation's prefix, THY_name (doc/CONVENTIONS.md), then            *)
(* find_name on that                                                         *)
let ml_prog_define_abbrev for_eval name tm =
  let thy = ml_prog_current_theory () in
  let name = ml_prog_ml_name name in
  let name =
    if not (ml_prog_is_const_str name) then name
    else if (try Hashtbl.find ml_prog_abbrev_theory name = thy with Not_found -> false)
    then ml_prog_find_name name
    else
      let pname = thy ^ "_" ^ name in
      if not (ml_prog_is_const_str pname) then pname else ml_prog_find_name pname in
  let vs = sort (fun v1 v2 -> fst (dest_var v1) <= fst (dest_var v2)) (frees tm) in
  let ty = itlist (fun v ty -> mk_fun_ty (type_of v) ty) vs (type_of tm) in
  let def = new_definition (mk_eq (list_mk_comb (mk_var (name,ty), vs), tm)) in
  Hashtbl.replace ml_prog_abbrev_theory name thy;
  let _ = ml_prog_save_thm (name ^ "_def") def in
  if for_eval then Compute.add_thms [def] ml_prog_cs;
  def;;

let ml_prog_auto_name sfx = ml_prog_current_theory () ^ "_" ^ sfx;;

let ml_prog_dest_block tm =
  let comm,r1 = dest_pair tm in
  let st,r2 = dest_pair r1 in
  let decls,env = dest_pair r2 in
  [comm; st; decls; env];;

let ml_prog_ML_code_blocks tm =
  let f,xs = strip_comb tm in
  if not (ml_prog_is_const_named "ML_code" f && length xs = 3)
  then failwith "ml_prog_ML_code_blocks: not ML_code" else
  map ml_prog_dest_block (dest_list (el 1 xs));;

(* HOL4 let_conv_ML_upd: conv on the value of the let, then the let *)
let ml_prog_let_conv_ML_upd conv nm (th,s) =
  if not (is_let (concl th)) then failwith ("ml_prog_let_conv_ML_upd: " ^ nm ^ ": not let")
  else CONV_RULE (RAND_CONV conv THENC let_CONV) th, s;;

(* HOL4 cond_let_abbrev: the value of the let, after conv, is abbreviated   *)
(* (unless cond and it is a constant applied to variables)                   *)
let ml_prog_cond_let_abbrev cond for_eval name conv op_nm th =
  if not (is_let (concl th))
  then failwith ("ml_prog_cond_let_abbrev: " ^ op_nm ^ ": not let") else
  let th = CONV_RULE (RAND_CONV conv) th in
  let tm = rand (concl th) in
  let f,xs = strip_comb tm in
  if cond && is_const f && forall is_var xs then CONV_RULE let_CONV th, []
  else
    let def = SPEC_ALL (ml_prog_define_abbrev for_eval name tm) in
    CONV_RULE (RAND_CONV (REWR_CONV (SYM def)) THENC let_CONV) th, [def];;

let ml_prog_let_st_abbrev conv op_nm (th,s) =
  let th,defs = ml_prog_cond_let_abbrev true true (ml_prog_auto_name "st") conv op_nm th in
  th, { s with mlps_st_defs = defs @ s.mlps_st_defs };;

(* the pfun equations of a new environment constant (HOL4                  *)
(* derive_nsLookup_thms): nsLookup_Short C.v = ..., nsLookup_Short C.c,     *)
(* nsLookup_Mod1 C.v, nsLookup_Mod1 C.c, in terms of older constants         *)
let ml_prog_pfun_rewr_conv =
  REWRITE_CONV [nsLookup_write_eqs; nsLookup_write_cons_eqs; nsLookup_merge_env_eqs;
                nsLookup_write_mod_eqs; nsLookup_empty_eqs];;

let ml_prog_derive_nsLookup_thms def =
  let env_const = lhs (concl def) in
  let xs = map lhs (conjuncts (concl (SPEC env_const nsLookup_eq_format))) in
  let conv = RAND_CONV (RAND_CONV (REWR_CONV def)) THENC ml_prog_pfun_rewr_conv in
  let pfun_eqs = end_itlist CONJ (map conv xs) in
  let _ = ml_prog_save_thm (ml_prog_pfun_eq_name env_const) pfun_eqs in
  Hashtbl.replace ml_prog_pfun_eqs (fst (dest_const env_const)) pfun_eqs;
  pfun_eqs;;

let ml_prog_let_env_abbrev conv op_nm (th,s) =
  let th,defs = ml_prog_cond_let_abbrev true false (ml_prog_auto_name "env") conv op_nm th in
  let _ = map ml_prog_derive_nsLookup_thms defs in
  th, { s with mlps_env_defs = defs @ s.mlps_env_defs };;

let ml_prog_let_v_abbrev nm conv op_nm (th,s) =
  let th,defs = ml_prog_cond_let_abbrev false false nm conv op_nm th in
  th, { s with mlps_v_defs = defs @ s.mlps_v_defs };;

let ml_prog_solve_ml_imp f nm (th,s) =
  if not (is_imp (concl th)) then failwith ("ml_prog_solve_ml_imp: " ^ nm ^ ": not imp")
  else f th, s;;

let ml_prog_solve_ml_imp_mp lemma = ml_prog_solve_ml_imp (fun th -> MATCH_MP th lemma);;

let ml_prog_solve_ml_imp_conv conv = ml_prog_solve_ml_imp (ml_prog_prove_assum_by_conv conv);;

(* HOL4 forall_nsLookup_upd: !x. nsLookup cenv.v vname = SOME x ==> P x     *)
(* becomes P y, y found by nsLookup_conv                                     *)
let ml_prog_forall_nsLookup_upd nm (th,s) =
  let x,bod = try dest_forall (concl th)
              with Failure _ -> failwith ("ml_prog_forall_nsLookup_upd: " ^ nm) in
  let look = lhs (fst (dest_imp bod)) in
  let lth = (TRY_CONV nsLookup_conv THENC ML_PROG_EVAL_CONV) look in
  let r = rhs (concl lth) in
  if not (ml_prog_is_app "SOME" 1 r)
  then failwith "ml_prog_forall_nsLookup_upd: nsLookup failed to produce SOME" else
  let y = rand r in
  MP (SPEC y th) lth, s;;

(* HOL4 ML_code_upd: the update is made on the theorem with every program  *)
(* abstracted to a variable prog_var_i, and connected to the real theorem   *)
(* in one final step                                                         *)
let ml_prog_ML_code_upd nm mp_thm adjs (s:ml_prog_state) =
  let orig_th = s.mlps_thm in
  let c = concl orig_th in
  let f,xs = strip_comb c in
  let blocks = ml_prog_ML_code_blocks c in
  let pvars = List.mapi (fun i _ -> mk_var ("prog_var_" ^ string_of_int i, ml_prog_decs_ty))
                blocks in
  let abs_blocks = List.map2 (fun bl pv -> ml_prog_list_mk_pair
                                (List.mapi (fun j t -> if j = 2 then pv else t) bl))
                     blocks pvars in
  let abs_blocks_tm = ml_prog_mk_list (abs_blocks, type_of (hd abs_blocks)) in
  let abs_concl = list_mk_comb (f, [el 0 xs; abs_blocks_tm; el 2 xs]) in
  let preproc_th = MATCH_MP mp_thm (ASSUME abs_concl) in
  let proc_th,s' = List.fold_left (fun acc adj -> adj nm acc) (preproc_th,s) adjs in
  let _ = ml_prog_is_const_named "ML_code" (fst (strip_comb (concl proc_th))) ||
          failwith ("ml_prog_ML_code_upd: " ^ nm ^ ": unfinished: " ^
                    ml_prog_string_of_term_short (concl proc_th)) in
  let inst = List.map2 (fun bl pv -> (el 2 bl, pv)) blocks pvars in
  let th = MP (INST inst (DISCH abs_concl proc_th)) orig_th in
  { s' with mlps_thm = th };;

(* ------------------------------------------------------------------------- *)
(* The operations (HOL4 init_state, open_module, add_Dtype, ...)             *)
(* ------------------------------------------------------------------------- *)

let ml_prog_init_state () =
  { mlps_st_defs = [SPEC_ALL ml_init_state_def]; mlps_env_defs = [ml_init_env_def];
    mlps_v_defs = []; mlps_thm = ML_code_NIL };;

let ml_prog_mk_comment (s1,s2) = mk_pair (ml_prog_mk_mlstring s1, ml_prog_mk_mlstring s2);;

let ml_prog_dest_comment t =
  let s1,s2 = dest_pair t in ml_prog_dest_mlstring s1, ml_prog_dest_mlstring s2;;

let ml_prog_ML_code_env_conv = REWRITE_CONV [ML_code_env_def];;

let ml_prog_open_block nm comment =
  ml_prog_ML_code_upd nm (ml_prog_ISPECL_NAMED ["comm2",comment] ML_code_new_block)
    [ml_prog_let_conv_ML_upd ml_prog_ML_code_env_conv];;

let ml_prog_open_module mn_str s =
  ml_prog_open_block "open_module" (ml_prog_mk_comment ("Module",mn_str)) s;;

(* the signature is ignored, as in HOL4 *)
let ml_prog_close_module (sig_opt:term option) s =
  ml_prog_ML_code_upd "close_module" ML_code_close_module
    [ml_prog_let_env_abbrev ALL_CONV] s;;

let ml_prog_open_local_block s =
  ml_prog_open_block "open_local_block" (ml_prog_mk_comment ("Local","local")) s;;

let ml_prog_open_local_in_block s =
  ml_prog_open_block "open_local_in_block" (ml_prog_mk_comment ("Local","in")) s;;

let ml_prog_close_local_block s =
  ml_prog_ML_code_upd "close_local_block" ML_code_close_local
    [ml_prog_let_env_abbrev ALL_CONV] s;;

let ml_prog_add_Dtype loc tds_tm s =
  ml_prog_ML_code_upd "add_Dtype"
    (ml_prog_ISPECL_NAMED ["tds",tds_tm; "locs",loc] ML_code_Dtype)
    [ml_prog_solve_ml_imp_conv ML_PROG_EVAL_CONV;
     ml_prog_let_conv_ML_upd ML_PROG_EVAL_CONV;
     ml_prog_let_st_abbrev ML_PROG_EVAL_CONV;
     ml_prog_let_env_abbrev ML_PROG_EVAL_CONV] s;;

let ml_prog_add_Dexn loc n_tm l_tm s =
  ml_prog_ML_code_upd "add_Dexn"
    (ml_prog_ISPECL_NAMED ["n",n_tm; "l",l_tm; "locs",loc] ML_code_Dexn)
    [ml_prog_let_conv_ML_upd ML_PROG_EVAL_CONV;
     ml_prog_let_st_abbrev ML_PROG_EVAL_CONV;
     ml_prog_let_env_abbrev ML_PROG_EVAL_CONV] s;;

let ml_prog_add_Dtabbrev loc l1_tm l2_tm l3_tm s =
  ml_prog_ML_code_upd "add_Dtabbrev"
    (ml_prog_ISPECL_NAMED ["x",l1_tm; "y",l2_tm; "z",l3_tm; "locs",loc] ML_code_Dtabbrev)
    [] s;;

(* eval_thm: |- eval_rel s env e s' x, s the current state, env the current *)
(* environment                                                               *)
let ml_prog_add_Dlet eval_thm var_str s =
  let xs = ml_prog_dest_app "eval_rel" 5 (concl eval_thm) in
  let mp_thm = ml_prog_ISPECL_NAMED
      ["cenv",el 1 xs; "e",el 2 xs; "s3",el 3 xs; "x",el 4 xs;
       "n",ml_prog_mk_mlstring var_str; "locs",ml_prog_unknown_loc] ML_code_Dlet_var in
  ml_prog_ML_code_upd "add_Dlet" mp_thm
    [ml_prog_solve_ml_imp_mp eval_thm;
     ml_prog_solve_ml_imp_conv ml_prog_ML_code_env_conv;
     ml_prog_let_env_abbrev ALL_CONV;
     ml_prog_let_st_abbrev ML_PROG_EVAL_CONV] s;;

let ml_prog_add_Dlet_lit loc n l s =
  ml_prog_ML_code_upd "add_Dlet_lit"
    (ml_prog_ISPECL_NAMED ["loc",loc; "name",n; "l",l] ML_code_Dlet_var_lit)
    [ml_prog_let_env_abbrev ALL_CONV; ml_prog_let_env_abbrev ALL_CONV] s;;

(* eval_thm: |- declare_env_rel s env s' envv *)
let ml_prog_add_Denv eval_thm var_str s =
  let xs = ml_prog_dest_app "declare_env_rel" 4 (concl eval_thm) in
  let mp_thm = ml_prog_ISPECL_NAMED
      ["n",ml_prog_mk_mlstring var_str; "cenv",el 1 xs; "s3",el 2 xs; "envv",el 3 xs]
      ML_code_Denv in
  ml_prog_ML_code_upd "add_Denv" mp_thm
    [ml_prog_solve_ml_imp_mp eval_thm;
     ml_prog_solve_ml_imp_conv ml_prog_ML_code_env_conv;
     ml_prog_let_env_abbrev ALL_CONV;
     ml_prog_let_st_abbrev ML_PROG_EVAL_CONV] s;;

let ml_prog_add_Dlet_Fun loc n v exp v_name s =
  ml_prog_ML_code_upd "add_Dlet_Fun"
    (ml_prog_ISPECL_NAMED ["n",n; "v",v; "e",exp; "locs",loc] ML_code_Dlet_Fun)
    [ml_prog_let_conv_ML_upd ml_prog_ML_code_env_conv;
     ml_prog_let_v_abbrev v_name ALL_CONV;
     ml_prog_let_env_abbrev ALL_CONV] s;;

let ml_prog_add_Dlet_Var_Var loc n var_name s =
  ml_prog_ML_code_upd "add_Dlet_Var_Var"
    (ml_prog_ISPECL_NAMED ["n",n; "vname",var_name; "locs",loc] ML_code_Dlet_Var_Var)
    [ml_prog_let_conv_ML_upd ml_prog_ML_code_env_conv;
     ml_prog_forall_nsLookup_upd;
     ml_prog_let_env_abbrev ALL_CONV] s;;

let ml_prog_add_Dlet_Var_Ref_Var loc n var_name v_name s =
  ml_prog_ML_code_upd "add_Dlet_Var_Ref_Var"
    (ml_prog_ISPECL_NAMED ["n",n; "vname",var_name; "locs",loc] ML_code_Dlet_Var_Ref_Var)
    [ml_prog_let_conv_ML_upd ml_prog_ML_code_env_conv;
     ml_prog_forall_nsLookup_upd;
     ml_prog_let_conv_ML_upd ML_PROG_EVAL_CONV;
     ml_prog_let_v_abbrev v_name ALL_CONV;
     ml_prog_let_env_abbrev ALL_CONV;
     ml_prog_let_st_abbrev ML_PROG_EVAL_CONV] s;;

let ml_prog_write_rec_conv = REWRITE_CONV [ml_write_rec_def; ITLIST; FST];;

(* funs: the list of (name, parameter, body); v_names: the names of the    *)
(* closure constants, in the order of funs                                   *)
let ml_prog_add_Dletrec loc funs v_names s =
  let fnames = map (fun t -> fst (dest_pair t)) (dest_list funs) in
  let _ = length fnames = length v_names ||
          failwith "ml_prog_add_Dletrec: one name per function" in
  let proc nm (th,s) =
    let th = CONV_RULE (RAND_CONV ml_prog_write_rec_conv) th in
    if not (is_let (concl th)) then failwith "ml_prog_add_Dletrec: not let" else
    let tm = rand (concl th) in
    let clos = find_terms (fun t -> ml_prog_is_app "Recclosure" 3 t) tm in
    let v_defs = map2 (fun fname vn ->
        let cl = try find (fun t -> rand t = fname) clos
                 with Failure _ -> failwith "ml_prog_add_Dletrec: closure" in
        ml_prog_define_abbrev false vn cl) fnames v_names in
    let th = CONV_RULE (RAND_CONV (PURE_REWRITE_CONV (map SYM v_defs))) th in
    ml_prog_let_env_abbrev ALL_CONV nm
      (th, { s with mlps_v_defs = v_defs @ s.mlps_v_defs }) in
  ml_prog_ML_code_upd "add_Dletrec"
    (ml_prog_ISPECL_NAMED ["fns",funs; "locs",loc] ML_code_Dletrec)
    [ml_prog_solve_ml_imp_conv ML_PROG_EVAL_CONV;
     ml_prog_let_conv_ML_upd ml_prog_ML_code_env_conv;
     proc] s;;

let ml_prog_get_block_names s =
  map (fun bl -> ml_prog_dest_comment (hd bl)) (ml_prog_ML_code_blocks (concl s.mlps_thm));;

(* the open modules, outermost first *)
let ml_prog_get_open_modules s =
  rev (map snd (filter (fun (k,_) -> k = "Module") (ml_prog_get_block_names s)));;

(* the prefix of value constant names (HOL4 get_mod_prefix: the first of  *)
(* get_open_modules, the outermost open module)                            *)
let ml_prog_get_mod_prefix s =
  match ml_prog_get_open_modules s with [] -> "" | m::_ -> m ^ "_";;

let rec ml_prog_close_local_blocks s =
  match ml_prog_get_block_names s with
    ("Local","in")::_ -> ml_prog_close_local_blocks (ml_prog_close_local_block s)
  | ("Local","local")::_ ->
      ml_prog_close_local_blocks (ml_prog_close_local_block (ml_prog_open_local_in_block s))
  | _ -> s;;

(* HOL4 pick_name: CakeML operator names to identifiers *)
let ml_prog_pick_name str =
  match str with
    "<" -> "lt" | ">" -> "gt" | "<=" -> "le" | ">=" -> "ge" | "=" -> "eq"
  | "<>" -> "neq" | "~" -> "uminus" | "+" -> "plus" | "-" -> "minus"
  | "*" -> "times" | "/" -> "div" | "!" -> "deref" | ":=" -> "assign"
  | "@" -> "append" | "^" -> "strcat" | "<<" -> "lsl" | ">>" -> "lsr"
  | "~>>" -> "asr" | _ -> str;;

let rec ml_prog_add_dec dec_tm pick_name s =
  let f,args = strip_comb dec_tm in
  let hd_name = if is_const f then fst (dest_const f) else "" in
  if hd_name = "Dexn" && length args = 3 then
    ml_prog_add_Dexn (el 0 args) (el 1 args) (el 2 args) s
  else if hd_name = "Dtype" && length args = 2 then
    ml_prog_add_Dtype (el 0 args) (el 1 args) s
  else if hd_name = "Dtabbrev" && length args = 4 then
    ml_prog_add_Dtabbrev (el 0 args) (el 1 args) (el 2 args) (el 3 args) s
  else if hd_name = "Dletrec" && length args = 2 then
    let prefix = ml_prog_get_mod_prefix s in
    let names = map (fun t -> prefix ^ pick_name (ml_prog_dest_mlstring (fst (dest_pair t))) ^ "_v")
                  (dest_list (el 1 args)) in
    ml_prog_add_Dletrec (el 0 args) (el 1 args) names s
  else if hd_name = "Dlet" && length args = 3 && ml_prog_is_app "Pvar" 1 (el 1 args) then
    let loc = el 0 args and n = rand (el 1 args) and e = el 2 args in
    if ml_prog_is_app "Fun" 2 e then
      let w,body = match ml_prog_dest_app "Fun" 2 e with [w;b] -> w,b | _ -> fail() in
      let v_name = ml_prog_get_mod_prefix s ^ pick_name (ml_prog_dest_mlstring n) ^ "_v" in
      ml_prog_add_Dlet_Fun loc n w body v_name s
    else if ml_prog_is_app "Lit" 1 e then ml_prog_add_Dlet_lit loc n (rand e) s
    else if ml_prog_is_app "Var" 1 e then ml_prog_add_Dlet_Var_Var loc n (rand e) s
    else if ml_prog_is_app "App" 2 e && ml_prog_is_const_named "Opref" (lhand e) &&
            (match dest_list (rand e) with [a] -> ml_prog_is_app "Var" 1 a | _ -> false) then
      let v_name = ml_prog_get_mod_prefix s ^ pick_name (ml_prog_dest_mlstring n) ^ "_v" in
      ml_prog_add_Dlet_Var_Ref_Var loc n (rand (hd (dest_list (rand e)))) v_name s
    else failwith ("ml_prog_add_dec does not support this shape: " ^
                   ml_prog_string_of_term_short dec_tm)
  else if hd_name = "Dmod" && length args = 2 then
    let name_str = ml_prog_dest_mlstring (el 0 args) in
    let s = try ml_prog_open_module name_str s with Failure _ ->
            failwith ("ml_prog_add_dec: failed to open module " ^ name_str) in
    let s = itlist (fun d s -> try ml_prog_add_dec d pick_name s with Failure e ->
                       failwith ("ml_prog_add_dec: in module " ^ name_str ^ " failed to add " ^
                                 ml_prog_string_of_term_short d ^ "\n " ^ e))
              (rev (dest_list (el 1 args))) s in
    (try ml_prog_close_module None s with Failure e ->
       failwith ("ml_prog_add_dec: failed to close module " ^ name_str ^ "\n " ^ e))
  else failwith ("ml_prog_add_dec does not support this shape: " ^
                 ml_prog_string_of_term_short dec_tm);;

(* remove_snocs.  HOL4 rewrites the whole theorem with SNOC_APPEND, then    *)
(* with GSYM APPEND_ASSOC, then with APPEND: every list built with SNOC or  *)
(* APPEND (the declarations of each block, and those inside every Dmod and  *)
(* Dlocal) becomes a CONS list.  The same result here in one pass over the  *)
(* conclusion: a subterm without SNOC and APPEND yields no theorem and is   *)
(* not rebuilt (the basis program has some 600,000 term nodes); a list      *)
(* spine of SNOC, APPEND and CONS is normalised, its elements first, in a   *)
(* number of steps linear in its length; a spine that is not a literal list *)
(* (a list variable in it) gets HOL4's three rewriting passes                *)
let ML_PROG_SNOC_APPEND = prove
 (`!(x:A) l. SNOC x l = APPEND l [x]`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[SNOC; APPEND]);;

let ML_PROG_APPEND_SNOC_ACC = prove
 (`!(x:A) l acc. APPEND (SNOC x l) acc = APPEND l (CONS x acc)`,
  REWRITE_TAC[ML_PROG_SNOC_APPEND; GSYM APPEND_ASSOC; APPEND]);;

let ML_PROG_APPEND_APPEND_ACC = prove
 (`!(a:A list) b acc. APPEND (APPEND a b) acc = APPEND a (APPEND b acc)`,
  REWRITE_TAC[APPEND_ASSOC]);;

let ML_PROG_APPEND_NIL_ACC = prove
 (`!acc:A list. APPEND [] acc = acc`, REWRITE_TAC[APPEND]);;

let ML_PROG_APPEND_CONS_ACC = prove
 (`!(h:A) t acc. APPEND (CONS h t) acc = CONS h (APPEND t acc)`, REWRITE_TAC[APPEND]);;

let ML_PROG_ADD_NIL_ACC = prove
 (`!l:A list. l = APPEND l []`, REWRITE_TAC[APPEND_NIL]);;

(* APPEND t acc, acc a CONS list: each SNOC, APPEND and CONS of t is      *)
(* rewritten once, by instantiating the lemmas directly (REWR_CONV would    *)
(* traverse the whole remaining list at each step: PART_MATCH computes its  *)
(* variables, quadratic for a long list of big declarations)                *)
let rec ml_prog_append_acc_conv tm =
  let t = lhand tm and acc = rand tm in
  match t with
    Const("NIL",_) ->
      alist_tree_fast_inst "ML_PROG_APPEND_NIL_ACC" ML_PROG_APPEND_NIL_ACC ["acc",acc]
  | Comb(Comb(Const("CONS",_),h),t') ->
      let th = alist_tree_fast_inst "ML_PROG_APPEND_CONS_ACC" ML_PROG_APPEND_CONS_ACC
                 ["h",h; "t",t'; "acc",acc] in
      TRANS th (RAND_CONV ml_prog_append_acc_conv (rhs (concl th)))
  | Comb(Comb(Const("SNOC",_),x),l) ->
      let th = alist_tree_fast_inst "ML_PROG_APPEND_SNOC_ACC" ML_PROG_APPEND_SNOC_ACC
                 ["x",x; "l",l; "acc",acc] in
      TRANS th (ml_prog_append_acc_conv (rhs (concl th)))
  | Comb(Comb(Const("APPEND",_),a),b) ->
      let th = alist_tree_fast_inst "ML_PROG_APPEND_APPEND_ACC" ML_PROG_APPEND_APPEND_ACC
                 ["a",a; "b",b; "acc",acc] in
      let th2 = TRANS th (RAND_CONV ml_prog_append_acc_conv (rhs (concl th))) in
      TRANS th2 (ml_prog_append_acc_conv (rhs (concl th2)))
  | _ -> failwith "ml_prog_append_acc_conv";;

(* a spine of SNOC, APPEND, CONS and NIL to a CONS list, linear in the length *)
let rec ml_prog_list_norm_conv tm =
  match tm with
    Const("NIL",_) -> REFL tm
  | Comb(Comb(Const("CONS",_),_),t) ->
      let th = ml_prog_list_norm_conv t in
      if rhs (concl th) == t then REFL tm else AP_TERM (rator tm) th
  | Comb(Comb(Const(("SNOC"|"APPEND"),_),_),_) ->
      let th = alist_tree_fast_inst "ML_PROG_ADD_NIL_ACC" ML_PROG_ADD_NIL_ACC ["l",tm] in
      TRANS th (ml_prog_append_acc_conv (rhs (concl th)))
  | _ -> REFL tm;;

(* HOL4's remove_snocs, for the lists that are not literal *)
let ml_prog_hol4_snoc_conv =
  PURE_REWRITE_CONV [ML_PROG_SNOC_APPEND] THENC
  PURE_REWRITE_CONV [GSYM APPEND_ASSOC] THENC PURE_REWRITE_CONV [APPEND];;

(* tm = c a b; the equations of a and b, None where unchanged *)
let ml_prog_mk_comb2 tm th1 th2 =
  match th1 with
    None -> (match th2 with None -> None | Some t2 -> Some (AP_TERM (rator tm) t2))
  | Some t1 ->
      let th = AP_TERM (rator (rator tm)) t1 in
      (match th2 with None -> Some (AP_THM th (rand tm)) | Some t2 -> Some (MK_COMB (th,t2)));;

(* Some (|- tm = tm') with every SNOC and APPEND list of tm normalised, or  *)
(* None if tm has none                                                       *)
let rec ml_prog_snoc_norm tm =
  match tm with
    Comb(Comb(Const(("SNOC"|"APPEND"),_),_),_) -> Some (ml_prog_spine_norm tm)
  | Comb(f,x) ->
      (match ml_prog_snoc_norm f with
         None -> (match ml_prog_snoc_norm x with
                    None -> None
                  | Some th -> Some (AP_TERM f th))
       | Some th1 -> (match ml_prog_snoc_norm x with
                        None -> Some (AP_THM th1 x)
                      | Some th2 -> Some (MK_COMB (th1,th2))))
  | Abs(v,b) -> (match ml_prog_snoc_norm b with None -> None | Some th -> Some (ABS v th))
  | _ -> None

(* the elements of a spine of SNOC, APPEND and CONS *)
and ml_prog_spine_elems tm =
  match tm with
    Comb(Comb(Const("CONS",_),h),t) ->
      ml_prog_mk_comb2 tm (ml_prog_snoc_norm h) (ml_prog_spine_elems t)
  | Comb(Comb(Const("SNOC",_),x),l) ->
      ml_prog_mk_comb2 tm (ml_prog_snoc_norm x) (ml_prog_spine_elems l)
  | Comb(Comb(Const("APPEND",_),a),b) ->
      ml_prog_mk_comb2 tm (ml_prog_spine_elems a) (ml_prog_spine_elems b)
  | _ -> ml_prog_snoc_norm tm

(* a spine headed by SNOC or APPEND: its elements, then the spine *)
and ml_prog_spine_norm tm =
  let th1 = match ml_prog_spine_elems tm with None -> REFL tm | Some th -> th in
  let tm1 = rhs (concl th1) in
  let th2 = try ml_prog_list_norm_conv tm1 with Failure _ -> ml_prog_hol4_snoc_conv tm1 in
  TRANS th1 th2;;

let ml_prog_remove_snocs s =
  match ml_prog_snoc_norm (concl s.mlps_thm) with
    None -> s
  | Some eq -> { s with mlps_thm = EQ_MP eq s.mlps_thm };;

let ml_prog_add_prog prog_tm pick_name s =
  ml_prog_remove_snocs
    (List.fold_left (fun s d -> ml_prog_add_dec d pick_name s) s (dest_list prog_tm));;

let ml_prog_get_thm s = s.mlps_thm;;
let ml_prog_get_v_defs s = s.mlps_v_defs;;
let ml_prog_get_env_defs s = s.mlps_env_defs;;
let ml_prog_get_st_defs s = s.mlps_st_defs;;

let ml_prog_get_prog s =
  match ml_prog_ML_code_blocks (concl s.mlps_thm) with
    [[_;_;prog;_]] -> prog
  | _ -> failwith "ml_prog_get_prog: couldn't get toplevel declarations";;

(* ML_code env1 [(comm,st1,prog,env2)] st2 ==> Decls env1 st1 prog env2 st2, *)
(* instantiated directly (MATCH_MP would traverse the whole program)        *)
let ml_prog_get_Decls_thm s =
  let th = s.mlps_thm in
  let env1 = el 0 (snd (strip_comb (concl th))) and st2 = rand (concl th) in
  match ml_prog_ML_code_blocks (concl th) with
    [[comm;st1;prog;env2]] ->
      MP (alist_tree_fast_inst "ML_code_Decls" ML_code_Decls
            ["env1",env1; "comm",comm; "st1",st1; "prog",prog; "env2",env2; "st2",st2]) th
  | _ -> failwith "ml_prog_get_Decls_thm: couldn't get toplevel declarations";;

let ml_prog_merge_env_tm = `merge_env`;;

(* the current environment: merge_env env_k (... (merge_env env_0 init_env)) *)
let ml_prog_get_env s =
  let th = s.mlps_thm in
  let bls = ml_prog_ML_code_blocks (concl th) in
  let rec mk bls =
    match bls with
      [] -> hd (snd (strip_comb (concl th)))
    | bl::bls -> list_mk_comb (ml_prog_merge_env_tm, [last bl; mk bls]) in
  mk bls;;

let ml_prog_get_state s = rand (concl s.mlps_thm);;

let ml_prog_next_type_stamp_tm = mk_const ("state_next_type_stamp",[]);;
let ml_prog_next_exn_stamp_tm = mk_const ("state_next_exn_stamp",[]);;

let ml_prog_get_next_type_stamp s =
  let tm = mk_icomb (ml_prog_next_type_stamp_tm, ml_prog_get_state s) in
  dest_small_numeral (rhs (concl (ML_PROG_EVAL_CONV tm)));;

let ml_prog_get_next_exn_stamp s =
  let tm = mk_icomb (ml_prog_next_exn_stamp_tm, ml_prog_get_state s) in
  dest_small_numeral (rhs (concl (ML_PROG_EVAL_CONV tm)));;

(* ML_code env0 [(comm,s1,prog,env1)] s2 ==> state_eval_state s1 = NONE ==> *)
(* !es. ..., instantiated directly                                           *)
let ml_prog_set_eval_state es s =
  let th = s.mlps_thm in
  let env0 = el 0 (snd (strip_comb (concl th))) and s2 = rand (concl th) in
  let th1 = match ml_prog_ML_code_blocks (concl th) with
      [[comm;s1;prog;env1]] ->
        MP (alist_tree_fast_inst "ML_code_set_eval_state" ML_code_set_eval_state
              ["env0",env0; "comm",comm; "s1",s1; "prog",prog; "env1",env1; "s2",s2]) th
    | _ -> failwith "ml_prog_set_eval_state: only at the top level" in
  let th2 = CONV_RULE (LAND_CONV ML_PROG_EVAL_CONV) th1 in
  let th3 = try MP th2 TRUTH with Failure _ ->
    failwith "ml_prog_set_eval_state: unable to prove that eval_state was NONE" in
  { s with mlps_thm = SPEC es th3 };;

(* HOL4 clean_state: only the newest state and environment definitions are *)
(* kept (HOL Light cannot delete the others' bindings)                       *)
let ml_prog_clean_state s =
  let first l = match l with [] -> [] | x::_ -> [x] in
  { s with mlps_st_defs = first s.mlps_st_defs; mlps_env_defs = first s.mlps_env_defs;
           mlps_v_defs = [] };;

(* ------------------------------------------------------------------------- *)
(* The current program state and the translator-state snapshots              *)
(* (HOL4 ml_translatorLib's prog_state, finalise_translation and             *)
(* translation_extends, without theory data)                                 *)
(* ------------------------------------------------------------------------- *)

let ml_prog_current = ref (None : ml_prog_state option);;

let ml_prog_get_current () =
  match !ml_prog_current with
    Some s -> s
  | None -> let s = ml_prog_init_state () in ml_prog_current := Some s; s;;

let ml_prog_set_current s = ml_prog_current := Some s;;

let ml_prog_update_current f = ml_prog_set_current (f (ml_prog_get_current ()));;

(* components: name, save (returns its restorer), reset *)
let translation_state_components =
  ref ([] : (string * (unit -> (unit -> unit)) * (unit -> unit)) list);;

let translation_register_state name save reset =
  translation_state_components :=
    filter (fun (n,_,_) -> n <> name) !translation_state_components @ [name,save,reset];;

let translation_snapshots =
  (Hashtbl.create 50 : (string, (string * (unit -> unit)) list) Hashtbl.t);;

let translation_finalise_functions = ref ([] : (unit -> unit) list);;

let add_finalise_function f =
  translation_finalise_functions := !translation_finalise_functions @ [f];;

(* the end of a translation file (HOL4: the export hook) *)
let finalise_translation () =
  List.iter (fun f -> f ()) !translation_finalise_functions;
  let name = ml_prog_current_theory () in
  let snap = map (fun (n,save,_) -> n, save ()) !translation_state_components in
  Hashtbl.replace translation_snapshots name snap;;

let translation_snapshot_names () =
  Hashtbl.fold (fun k _ acc -> k :: acc) translation_snapshots [];;

let translation_extends name =
  let snap = try Hashtbl.find translation_snapshots name with Not_found ->
    failwith ("translation_extends: no translator snapshot named " ^ name ^
              " (the translation file must end with finalise_translation ())") in
  List.iter (fun (n,_,reset) ->
      match (try Some (assoc n snap) with Failure _ -> None) with
        Some restore -> restore ()
      | None -> reset ()) !translation_state_components;;

(* the state of a fresh HOL4 process *)
let translation_reset () =
  List.iter (fun (_,_,reset) -> reset ()) !translation_state_components;;

let () = translation_register_state "ml_progLib"
  (fun () -> let s = !ml_prog_current in fun () -> ml_prog_current := s)
  (fun () -> ml_prog_current := None);;

(* ------------------------------------------------------------------------- *)
(* A short printer for states (the theorems can be big)                     *)
(* ------------------------------------------------------------------------- *)

let rec ml_prog_count_decs tm =
  if alist_tree_is_nil tm then 0
  else if is_cons tm || ml_prog_is_app "SNOC" 2 tm then 1 + ml_prog_count_decs (rand tm)
  else if ml_prog_is_app "APPEND" 2 tm then
    ml_prog_count_decs (lhand tm) + ml_prog_count_decs (rand tm)
  else 0;;

let pp_print_ml_prog_state fmt (s:ml_prog_state) =
  try
    let bls = ml_prog_ML_code_blocks (concl s.mlps_thm) in
    let n = itlist (fun bl n -> ml_prog_count_decs (el 2 bl) + n) bls 0 in
    let names = map (fun (a,b) -> a ^ " " ^ b) (ml_prog_get_block_names s) in
    Format.fprintf fmt "<ml_prog_state: %d declarations; blocks [%s]; env %s; state %s>"
      n (String.concat ", " names) (string_of_term (ml_prog_get_env s))
      (string_of_term (ml_prog_get_state s))
  with Failure _ -> Format.fprintf fmt "<ml_prog_state>";;

#install_printer pp_print_ml_prog_state;;
