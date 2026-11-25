(* ========================================================================= *)
(* ml_translatorLib: port of HOL4 translator/ml_translatorLib.sml (CakeML   *)
(* v3479), the proof-producing translator from HOL Light functions to       *)
(* CakeML code.  The entry points are HOL4's: translate, translate_no_ind,  *)
(* register_type, register_exn_type, hol2deep, get_type_inv, add_type_inv,  *)
(* update_precondition, add_user_proved_v_thm, next_ml_names, ...           *)
(*                                                                           *)
(* HOL4's algorithm is followed step by step, with the same certificate     *)
(* theorems (ml_translator.ml) and the same refinement invariants.  The      *)
(* program state (the ML_code theorem, the environment and its lookups) is  *)
(* ml_progLib's.  Differences from HOL4, all forced by HOL Light:           *)
(* - no theory data, no theorem database: the translator's tables are OCaml *)
(*   values (snapshots per translation file, see translation_extends), the  *)
(*   generated theorems are returned and also kept in a name table          *)
(*   (tr_fetch "fst_v_thm");                                                 *)
(* - no deletion of constants: temporary code constants are avoided (the    *)
(*   code terms stay explicit);                                              *)
(* - one global name space for constants: generated names are checked       *)
(*   against the whole session (doc/CONVENTIONS.md);                        *)
(* - one-line forms (PLAN 1c.8 H7): HOL Light's definitions by clauses do   *)
(*   not give ARB for the cases no clause covers (HD [] is unspecified).    *)
(*   Rule: the kit's ONELINE (one equation, ARB where no clause matches)    *)
(*   when it proves the equation (complete patterns, overlapping clauses    *)
(*   completed by the kit as HOL4's TFL does); otherwise the equation under *)
(*   ml_PRECONDITION (pattern_complete def vs), the disjunction over the    *)
(*   clauses of ?xs. v = pat, unless that disjunction is provable for all   *)
(*   arguments (complete patterns that ONELINE does not compile, e.g.       *)
(*   literals with a variable row): then no precondition.  HOL4 does the    *)
(*   same: single_line_def adds PRECONDITION (pattern_complete def vs) when *)
(*   TFL's primitive definition contains ARB, and one_line_ify (HOL4's       *)
(*   route for primitive recursive definitions such as HD) adds the         *)
(*   hypothesis ?xs. v = pat \/ .. over the case tree's leaves.  So the     *)
(*   side condition of a partial definition has HOL4's conjuncts (HD:       *)
(*   hd_side v <=> ~(v = []) /\ ?h t. v = CONS h t); the known differences  *)
(*   are conjunct order and the names of bound variables;                    *)
(* - HOL Light's let terms LET (\x. LET_END b) e are read as HOL4's          *)
(*   LET (\x. b) e;                                                          *)
(* - HOL Light's matching is higher order where HOL4's is first order:      *)
(*   invariants that HO matching eta-expands (\x v. LIST_TYPE a x v) are    *)
(*   eta-reduced, and HOL4's match_mp_tac on quantified conclusions is      *)
(*   replaced by matching the goal as it is first;                          *)
(* - side-condition constants of the same HOL4 name made by two translation *)
(*   files: the second is THY_f_side (the theorem keeps HOL4's name);        *)
(* - HOL4 renames T and F to TRUE and FALSE before translating; inside the  *)
(*   character literals of HOL Light (ASCII b0 .. b7) they are kept;          *)
(* - HOL4's character literals, written CHR n in the port, are translated   *)
(*   as the literals they denote (Lit (Char c));                             *)
(* - HOL Light's paired abstractions (GABS) are first written as HOL4's     *)
(*   UNCURRY form (remove_pair_abs);                                         *)
(* - HOL Light has no case constant for the unit type: the translator       *)
(*   defines HOL4's one_CASE (unit patterns f () = e become f v =           *)
(*   one_CASE v e, HOL4's case v of () => e);                               *)
(* - the HOL4 names of types and constants (FOO_TYPE names, CakeML          *)
(*   identifiers) come from doc/names.tsv and ident_map.tsv (the            *)
(*   tables in ml_translatorSyntax.ml).                                     *)
(* HOL4's ml_translator_test was ported as the translator's regression      *)
(* test; it is not part of this repository.                                  *)
(* ========================================================================= *)

needs "translator/ml_translatorSyntax.ml";;
needs "translator/ml_optimise.ml";;
needs "translator/ml_progLib.ml";;

type_invention_error := true;;

(* terms and types used in function bodies, parsed once (a quotation in a  *)
(* function body is parsed at every call)                                   *)
let tr_T_tm = `T` and tr_F_tm = `F` and tr_TRUE_tm = `TRUE` and tr_FALSE_tm = `FALSE`
and tr_one_tm = `one` and tr_num0_tm = `0` and tr_v_v = `v:v`;;
let tr_BOOL_inv = `ml_BOOL` and tr_NUM_inv = `ml_NUM` and tr_INT_inv = `ml_INT`
and tr_CHAR_inv = `ml_CHAR` and tr_HOL_STRING_inv = `HOL_STRING_TYPE`
and tr_STRING_inv = `STRING_TYPE` and tr_FLOAT64_inv = `ml_FLOAT64`;;
let tr_dec_ty = `:dec`;;
let tr_LET_tm = `LET:(A->B)->A->B`;;
let tr_K_num_tm = `K:num->mlstring->num`;;
let tr_LIST_TYPE_CHAR_tm = `LIST_TYPE ml_CHAR`;;
let tr_v2_v = `v2:v`;;
let tr_SOME_stamp_tm = `SOME:stamp->(stamp)option`;;
let tr_SOME_num_stamp_tm = `SOME:num#stamp->(num#stamp)option`;;
let tr_NONE_num_stamp_tm = `NONE:(num#stamp)option`;;
let tr_ARB_stamp_tm = `ARB:stamp`;;
let tr_NONE_id_tm = `NONE:((mlstring,mlstring)id)option`;;
let tr_SOME_id_tm = `SOME:(mlstring,mlstring)id->((mlstring,mlstring)id)option`;;
let tr_ALL_DISTINCT_names_tm = `ALL_DISTINCT:(mlstring)list->bool`;;
let tr_ps_cases_ty = `:(mlstring,mlstring)id#(mlstring)list#exp#stamp`;;
let tr_INL_cases_tm =
  `INL:(mlstring)list#exp->((mlstring)list#exp)+(((mlstring,mlstring)id#(mlstring)list#exp#stamp)list)`;;
let tr_INR_cases_tm =
  `INR:(((mlstring,mlstring)id#(mlstring)list#exp#stamp)list)->((mlstring)list#exp)+(((mlstring,mlstring)id#(mlstring)list#exp#stamp)list)`;;
let tr_Mat_cases_tm = `Mat_cases`;;
let tr_dtype_part_ty = `:(mlstring)list#mlstring#(mlstring#(ast_t)list)list`;;
let tr_dtype_line_ty = `:mlstring#(ast_t)list`;;
let tr_UNIT_TYPE_tm = `UNIT_TYPE`;;
let tr_write_rec_tm = `ml_write_rec`;;

(* HOL4 wordsLib.WORD_CONV on the code: dimindex of numeral types, numeral *)
(* arithmetic, lets, word operations on literals, conditionals             *)
let tr_WORD_CONV =
  TOP_DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV THENC
  PURE_REWRITE_CONV [LET_DEF; LET_END_DEF] THENC DEPTH_CONV BETA_CONV THENC
  WORD_REDUCE_CONV THENC REWRITE_CONV [];;

(* HOL4 UnableToTranslate, UnsupportedType, NotFoundVThm (HOL Light's lexer *)
(* reads such names with inner capitals as value names)                     *)
exception Unable_to_translate of term;;
exception Unsupported_type of hol_type;;
exception Not_found_v_thm of term;;

(* ------------------------------------------------------------------------- *)
(* Small rules (HOL4 D, normalise_assums, MY_MP, auto_prove)                 *)
(* ------------------------------------------------------------------------- *)

(* HOL4 do_timing / trace_timing_to: the (processor) time of the main     *)
(* steps, printed when tr_timing is set (Sys.time: the batch toplevel has  *)
(* no Unix module)                                                         *)
let tr_timing = ref false;;
let tr_timing_file = ref (None : string option);;
let tr_time name f x =
  if not !tr_timing && !tr_timing_file = None then f x else
  let t0 = Sys.time () in
  let r = f x in
  let line = Printf.sprintf "TIME %s: %.2f s\n" name (Sys.time () -. t0) in
  Format.print_string line; Format.print_flush ();
  (match !tr_timing_file with
     None -> ()
   | Some f -> let oc = open_out_gen [Open_append; Open_creat] 0o644 f in
               output_string oc line; close_out oc);
  r;;

(* MESON's progress output off (HOL4's proof tools print nothing) *)
let tr_quiet_tac (t:tactic) : tactic = fun g ->
  let old = !verbose in
  verbose := false;
  try let r = t g in verbose := old; r with e -> (verbose := old; raise e);;

(* HOL4 D: all hypotheses into one antecedent, T if there are none *)
let tr_D th =
  let th = PURE_REWRITE_RULE [IMP_IMP] (DISCH_ALL th) in
  if is_imp (concl th) then th else DISCH tr_T_tm th;;

let tr_normalise_assums th =
  UNDISCH_ALL (PURE_REWRITE_RULE [GSYM IMP_IMP] (DISCH_ALL th));;

let tr_auto_prove name (goal,tac) =
  try prove (goal,tac)
  with Failure s -> failwith ("auto_prove failed for " ^ name ^ ": " ^ s);;

let rec tr_UNDISCH_ALL th = if is_imp (concl th) then tr_UNDISCH_ALL (UNDISCH th) else th;;

(* HOL4 UNBETA_CONV x: |- t = (\x. t) x *)
let tr_UNBETA_CONV x tm = SYM (BETA_CONV (mk_comb (mk_abs (x,tm), x)));;

let tr_find_terms p tm =
  let rec go tm acc =
    let acc = if p tm then insert tm acc else acc in
    match tm with
      Comb(f,x) -> go x (go f acc)
    | Abs(_,b) -> go b acc
    | _ -> acc in
  go tm [];;

let tr_can_find_term p tm = try ignore (find_term p tm); true with Failure _ -> false;;

(* HOL4 SPEC_ALL followed by instantiation of named variables *)
let tr_ISPECL_NAMED (l:(string * term) list) th =
  let th = SPEC_ALL th in
  let vs = frees (concl th) in
  let pick (n,t) =
    let v = try find (fun v -> fst (dest_var v) = n) vs
            with Failure _ -> failwith ("tr_ISPECL_NAMED: no variable " ^ n) in
    v,t in
  let prs = map pick l in
  let tyin = itlist (fun (v,t) i -> type_match (type_of v) (type_of t) i) prs [] in
  let th = INST_TYPE tyin th in
  INST (map (fun (v,t) -> (t, inst tyin v)) prs) th;;

(* SPEC of an outer quantifier named n, or INST of a free variable named n  *)
(* (the templates keep HOL4's mix of quantified and free variables)        *)
let tr_SPEC_NAMED n t th =
  let c = concl th in
  if is_forall c && fst (dest_var (fst (dest_forall c))) = n then ISPEC t th
  else
    let v = try find (fun v -> fst (dest_var v) = n) (frees c)
            with Failure _ -> failwith ("tr_SPEC_NAMED: no variable " ^ n) in
    let tyin = type_match (type_of v) (type_of t) [] in
    INST [t, inst tyin v] (INST_TYPE tyin th);;

(* ------------------------------------------------------------------------- *)
(* The translator's state: certificates (HOL4 v_thms), eval theorems, the   *)
(* constructor names and the modules of types                                *)
(* ------------------------------------------------------------------------- *)

(* name, ML name, HOL term, certificate (|- A c c_v, PRECONDITION hyps), *)
(* precondition definition (TRUTH if none), module scope                  *)
let tr_v_thms = ref ([] : (string * string * term * thm * thm * string list) list);;
let tr_eval_thms = ref ([] : (string * term * thm) list);;
let tr_cons_name_state = ref ([] : (string * (term * string list)) list);;
let tr_type_mod_state = ref ([] : (string * string list) list);;

(* the generated theorems by HOL4 name (HOL4 save_thm / fetch "-") *)
let tr_saved_thms = (Hashtbl.create 1000 : (string, thm) Hashtbl.t);;
let tr_save_thm name th = Hashtbl.replace tr_saved_thms name th; th;;
let tr_fetch name =
  try Hashtbl.find tr_saved_thms name with Not_found -> failwith ("tr_fetch: " ^ name);;

let get_ml_name (_,nm,_,_,_,_) = nm;;
let get_const (_,_,tm,_,_,_) = tm;;
let get_cert (_,_,_,th,_,_) = th;;
let get_pre (_,_,_,_,th,_) = th;;
let get_v_thms () = !tr_v_thms;;
let get_names () = map get_ml_name !tr_v_thms;;

(* the program state is ml_progLib's current state (HOL4 prog_state with *)
(* ml_prog_update, get_ml_prog_state, get_curr_env, ...)                    *)
let ml_prog_update f = ml_prog_update_current f;;
let get_ml_prog_state () = ml_prog_get_current ();;
let get_curr_env () = ml_prog_get_env (ml_prog_get_current ());;
let get_curr_state () = ml_prog_get_state (ml_prog_get_current ());;
let get_curr_v_defs () = ml_prog_get_v_defs (ml_prog_get_current ());;
let get_curr_modules () = ml_prog_get_open_modules (ml_prog_get_current ());;

(* the identifier of item base defined in module path mods, seen from the *)
(* current module path (HOL4 mk_qualified_relative_name)                   *)
let mk_qualified_relative_name curr_mods mods base =
  let base_nm = mk_Short base in
  let rec drop_same xs ys = match xs,ys with
      x::xt, y::yt -> if x = y then drop_same xt yt else xs
    | _ -> xs in
  let rel_mods = drop_same mods curr_mods in
  let rec mk_name ms b = match ms with
      [] -> b
    | m::mt -> mk_Long (mk_mlstring m, mk_name mt b) in
  mk_name rel_mods base_nm;;

let get_qualified_name mods base =
  mk_qualified_relative_name (get_curr_modules ()) mods base;;

let add_v_thms (name,ml_name,th,pre_def) =
  let thc = concl th in
  let tm,th =
    if is_Eval thc then rand (rand thc), tr_normalise_assums th
    else rand (rator thc), th in
  let modules = get_curr_modules () in
  (if concl pre_def = tr_T_tm then () else
   Format.print_string ("\nWARNING: " ^ ml_name ^ " has a precondition.\n\n"));
  tr_v_thms := (name,ml_name,tm,th,pre_def,modules) :: !tr_v_thms;;

let filter_v_thms f =
  let xs = !tr_v_thms in
  let ys = filter f xs in
  tr_v_thms := ys; length xs - length ys;;

let replace_v_thm c th =
  let rec f l = match l with
      [] -> failwith "replace_v_thm: not found"
    | (name,ml_name,c',th',pre,m)::vths ->
        if c = c' then (name,ml_name,c,th,pre,m)::vths
        else (name,ml_name,c',th',pre,m) :: f vths in
  tr_v_thms := f !tr_v_thms;;

(* HOL4 add_user_proved_v_thm: th |- P c v for an existing value constant v *)
let add_user_proved_v_thm th =
  let th = tr_UNDISCH_ALL th in
  let v = rand (concl th) in
  (if type_of v = v_ty then () else failwith "add_user_proved_v_thm not a v thm");
  let tm = rand (rator (concl th)) in
  let (name,ml_name,_,_,_,module_name) =
    try find (fun (_,_,_,th',_,_) -> aconv (rand (concl th')) v) !tr_v_thms
    with Failure _ -> failwith "add_user_proved_v_thm: no certificate with this value" in
  tr_v_thms := (name,ml_name,tm,th,TRUTH,module_name) :: !tr_v_thms; th;;

let get_bare_v_thm const =
  find (fun (_,_,c,_,_,_) -> can (term_match [] c) const) !tr_v_thms;;

(* HOL4 lookup_v_thm: the certificate of a translated constant as         *)
(*   nsLookup env.v id = SOME c_v |- ml_Eval env (Var id) (A c)            *)
let lookup_v_thm const =
  let (name,ml_name,c,th,pre,m) = get_bare_v_thm const in
  let th = tr_UNDISCH_ALL (SPEC_ALL th) in
  let iden = get_qualified_name m (mk_mlstring ml_name) in
  let p = rator (concl th) and cv = rand (concl th) in
  let lemma = tr_ISPECL_NAMED ["P",p; "v",cv; "env",tr_env] Eval_Var_general in
  tr_UNDISCH_ALL (tr_SPEC_NAMED "iden" iden (MP lemma th));;

let lookup_eval_thm const =
  let (_,_,th) = find (fun (_,c,_) -> can (term_match [] c) const) !tr_eval_thms in
  tr_UNDISCH_ALL (SPEC_ALL th);;

(* HOL4 remove_Eq_from_v_thm: |- (Eq A x --> B) f f_v with no hypothesis   *)
(* about x becomes |- (A --> B) f f_v                                      *)
let remove_Eq_from_v_thm th =
  let xs = map (fun t -> snd (dest_Eq (fst (dest_Arrow t))))
               (tr_find_terms (fun t -> is_Arrow t && is_Eq (fst (dest_Arrow t))) (concl th)) in
  let foo v th =
    let c = concl th in
    let p = rator (rator c) and f = rand (rator c) and fv = rand c in
    let lemma = tr_ISPECL_NAMED ["p", mk_abs (v, p); "f", f; "v", fv] FUN_FORALL_INTRO in
    let lemma = CONV_RULE (LAND_CONV (BINDER_CONV (RATOR_CONV (RATOR_CONV BETA_CONV)))) lemma in
    let th1 = MP lemma (GEN v th) in
    CONV_RULE (RATOR_CONV (RATOR_CONV (DEPTH_CONV BETA_CONV THENC
                                       REWRITE_CONV [FUN_QUANT_SIMP]))) th1 in
  itlist (fun v th -> try foo v th with Failure _ -> th) xs th;;

(* HOL4 update_precondition: |- !x. f_side x <=> simpler (or the proved    *)
(* induction goal f_ind) rewrites every stored certificate; certificates   *)
(* whose precondition becomes T lose it and their Eq                        *)
let update_precondition new_pre =
  let update_aux (name,ml_name,tm,th,pre,modu) =
    let th1 = tr_D th in
    let (new_pre,th1) =
      if is_imp (concl (SPEC_ALL new_pre)) then
        ((try MATCH_MP ml_IMP_EQ_T (MP (tr_D new_pre) TRUTH) with Failure _ -> new_pre) |>
           PURE_REWRITE_RULE [GSYM CONJ_ASSOC],
         PURE_REWRITE_RULE [GSYM CONJ_ASSOC] th1)
      else (new_pre,th1) in
    let th2 = PURE_REWRITE_RULE [new_pre; PRECONDITION_T] th1 in
    if aconv (concl th1) (concl th2) then (name,ml_name,tm,th,pre,modu) else
    let th2 = REWRITE_RULE [] th2 in
    let th2 = if is_imp (concl th2) then th2 else th2 in
    let th = remove_Eq_from_v_thm (if is_imp (concl th2) then tr_UNDISCH_ALL th2 else th2) in
    let thm_name = name ^ "_v_thm" in
    Format.print_string ("Updating " ^ thm_name ^ "\n");
    let th = tr_save_thm thm_name th in
    let new_pre = if tr_can_find_term is_PRECONDITION (concl (tr_D th)) then new_pre else TRUTH in
    (name,ml_name,tm,tr_UNDISCH_ALL th,new_pre,modu) in
  tr_v_thms := map update_aux !tr_v_thms;
  new_pre;;

let add_eval_thm th =
  let tm = concl (tr_UNDISCH_ALL (SPEC_ALL th)) in
  let const = rand (rand tm) in
  tr_eval_thms := (string_of_term const, const, th) :: !tr_eval_thms; th;;

let check_no_ind_assum tm th =
  let hs = hyp (tr_normalise_assums th) in
  if exists is_forall hs then
    let str = "User must prove skipped induction theorem for " ^ string_of_term tm in
    (Format.print_string ("\nERROR: " ^ str ^ "\n\n"); failwith str)
  else ();;

(* ------------------------------------------------------------------------- *)
(* Modules of types and constructor names                                    *)
(* ------------------------------------------------------------------------- *)

let lookup_type_mod tyname =
  try Some (assoc tyname !tr_type_mod_state) with Failure _ -> None;;

let enter_type_mod tyname =
  let mods = get_curr_modules () in
  (if lookup_type_mod tyname = None then () else failwith ("duplicate type: " ^ tyname));
  match mods with
    [] -> ()
  | _ -> tr_type_mod_state := (tyname,mods) :: !tr_type_mod_state;;

let lookup_cons_name key = assoc key !tr_cons_name_state;;

(* ------------------------------------------------------------------------- *)
(* Type information (HOL4 TypeBase): the HOL4 names and theories of the    *)
(* types, needed for the CakeML type and constructor names (decision D4)    *)
(* ------------------------------------------------------------------------- *)

(* HOL Light type name -> (HOL4 theory, HOL4 type name); filled from       *)
(* doc/names.tsv by ml_translatorSyntax (tr_hol4_type_table)                *)
let tr_hol4_type_info tyname =
  try assoc tyname !tr_hol4_type_table
  with Failure _ ->
    match tyname with
      "list" -> ("list","list") | "option" -> ("option","option")
    | "sum" -> ("sum","sum") | "prod" -> ("pair","pair") | "1" -> ("one","one")
    | "num" -> ("num","num") | "bool" -> ("min","bool") | "int" -> ("integer","int")
    | "char" -> ("string","char") | _ -> ("",tyname);;

let basic_theories =
  ["alist"; "arithmetic"; "bag"; "bitstring"; "bit"; "bool";
   "combin"; "container"; "divides"; "fcp"; "finite_map"; "float";
   "fmaptree"; "frac"; "gcdset"; "gcd"; "ind_type"; "integer_word";
   "integer"; "integral"; "list"; "llist"; "marker"; "machine_ieee";
   "measure"; "numeral_bit"; "numeral"; "numpair"; "numposrep"; "num";
   "one"; "operator"; "option"; "pair"; "path"; "patricia_casts";
   "patricia"; "poly"; "poset"; "powser"; "pred_set"; "prelim";
   "prim_rec"; "quote"; "quotient_list"; "quotient_option";
   "quotient_pair"; "quotient_pred_set"; "quotient_sum"; "quotient";
   "rat"; "real_sigma"; "realax"; "real"; "relation"; "res_quan";
   "rich_list"; "ringNorm"; "ring"; "sat"; "semi_ring"; "seq";
   "set_relation"; "sorting"; "state_option"; "state_transformer";
   "string_num"; "string"; "sum_num"; "sum"; "topology"; "transc";
   "update"; "util_prob"; "while"; "words"; "min"];;

let use_full_type_names = ref true;;

let name_of_type ty = snd (tr_hol4_type_info (fst (dest_type ty)));;

let full_name_of_type ty =
  if !use_full_type_names then
    let thy = fst (tr_hol4_type_info (fst (dest_type ty))) in
    let pre = if thy = "" || mem thy basic_theories then "" else thy ^ "_" in
    pre ^ name_of_type ty
  else name_of_type ty;;

(* HOL Light numeral types: 1, tybit0 t (2 t), tybit1 t (2 t + 1) *)
let rec tr_numeral_type_value ty =
  match dest_type ty with
    "1",[] -> 1
  | "tybit0",[t] -> 2 * tr_numeral_type_value t
  | "tybit1",[t] -> 2 * tr_numeral_type_value t + 1
  | _ -> failwith "tr_numeral_type_value";;

let tr_is_numeral_type ty = can tr_numeral_type_value ty;;

let tr_is_word_type ty =
  is_type ty && (match dest_type ty with "word",[_] -> true | _ -> false);;

let tr_word_dim ty = tr_numeral_type_value (hd (snd (dest_type ty)));;

(* ty must be a word type with dimindex <= 64 *)
let word_ty_ok ty = tr_is_word_type ty && (try tr_word_dim ty <= 64 with Failure _ -> false);;

let tr_float64_ty = `:(52,11)float`;;

(* the primitive exceptions of the initial environment (HOL4 prim_exn_list) *)
let tr_prim_exns =
  let c = rand (rand (concl ml_init_env_def)) in
  let xs = dest_list (rand (rator c)) in
  mapfilter (fun t -> let n,p = dest_pair t in
                      let ar,st = dest_pair p in
                      if is_ExnStamp st then (dest_mlstring n, dest_small_numeral ar, p)
                      else fail()) xs;;

let get_primitive_exception name =
  let (_,arity,value) = find (fun (n,_,_) -> n = name) tr_prim_exns in (arity,value);;
let is_primitive_exception name = can get_primitive_exception name;;

(* ------------------------------------------------------------------------- *)
(* Refinement invariants of types (HOL4 get_type_inv) and the CakeML types  *)
(* of HOL types (HOL4 type2t)                                                *)
(* ------------------------------------------------------------------------- *)

let use_string_type_ref = ref false;;
let use_string_type b =
  use_string_type_ref := b;
  if b then Format.print_string "Translator now treats `char list` as a CakeML string.\n"
  else Format.print_string "Translator now treats `char list` as a list of characters in CakeML.\n";;
let use_hol_string_type () = !use_string_type_ref;;
let use_sub_check_ref = ref false;;
let use_sub_check b =
  use_sub_check_ref := b;
  if b then Format.print_string "Translator now uses checked subtraction on num.\n"
  else Format.print_string "Translator now generates side conditions for subtraction on num.\n";;
let sub_check () = !use_sub_check_ref;;

let tr_type_mappings = ref ([] : (hol_type * hol_type) list);;
let tr_other_types = ref ([] : (hol_type * term) list);;
let tr_preprocessor_rws = ref ([] : thm list);;
let tr_type_memory = ref ([] : (hol_type * thm * (term * thm) list * thm) list);;
(* HOL4 default_eq_lemmas: the EqualityType and IsTypeRep lemmas of the    *)
(* basic types                                                              *)
let tr_default_eq_lemmas () =
  CONJUNCTS EqualityType_NUM_BOOL @ CONJUNCTS IsTypeRep_NUM_BOOL @
  [IsTypeRep_PAIR; IsTypeRep_LIST; IsTypeRep_VECTOR];;
let tr_all_eq_lemmas = ref (tr_default_eq_lemmas ());;

let type_reset () =
  tr_type_mappings := []; tr_other_types := []; tr_preprocessor_rws := [];
  tr_type_memory := []; tr_all_eq_lemmas := tr_default_eq_lemmas ();;

let dest_fun_type ty =
  match dest_type ty with
    "fun",[a;b] -> (a,b)
  | _ -> failwith "not fun type";;

let find_type_mapping ty =
  find (fun (t,_) -> can (type_match t ty) []) !tr_type_mappings;;

let free_typevars ty = tyvars ty;;

let add_new_type_mapping ty target_ty =
  tr_type_mappings := (ty,target_ty) :: !tr_type_mappings;;

let prim_type name = mk_Atapp ([], mk_Short (mk_mlstring name));;
let bool_ast_t = prim_type "bool";;
let int_ast_t = prim_type "int";;
let char_ast_t = prim_type "char";;
let word8_ast_t = prim_type "word8";;
let word64_ast_t = prim_type "word64";;
let string_ast_t = prim_type "string";;
let double_ast_t = prim_type "double";;
let one_ast_t = mk_Attup [];;

(* HOL Light type variable A is HOL4's 'a *)
let tr_tyvar_ml_name ty = "'" ^ String.lowercase_ascii (dest_vartype ty);;

let tr_one_ty = `:1`;;
let tr_num_ty = `:num`;;
let tr_int_ty = `:int`;;
let tr_char_ty = `:char`;;
let tr_string_ty = `:(char)list`;;

let tr_vector_tyname = "vector";;
let is_vector_type ty =
  is_type ty && (match dest_type ty with (n,[_]) -> n = tr_vector_tyname | _ -> false);;
let dest_vector_type ty = hd (snd (dest_type ty));;

(* HOL4 full_id: Short, or Long for a type of another module *)
let full_id n =
  match lookup_type_mod (dest_mlstring n) with
    None -> mk_Short n
  | Some type_mod -> get_qualified_name type_mod n;;

let rec type2t ty =
  if ty = bool_ty then bool_ast_t else
  if word_ty_ok ty then
    (if tr_word_dim ty <= 8 then word8_ast_t else word64_ast_t) else
  if ty = tr_int_ty then int_ast_t else
  if ty = tr_num_ty then int_ast_t else
  if ty = tr_char_ty then char_ast_t else
  if ty = tr_one_ty then one_ast_t else
  if use_hol_string_type () && ty = tr_string_ty then string_ast_t else
  if ty = mlstring_ty then string_ast_t else
  if ty = tr_float64_ty then double_ast_t else
  if is_vartype ty then mk_Atvar (mk_mlstring (tr_tyvar_ml_name ty)) else
  try
    let (lhs,rhs) = find_type_mapping ty in
    let i = type_match lhs ty [] in
    let xs = free_typevars rhs in
    let i = filter (fun (_,a) -> mem a xs) i in
    let tm = type2t rhs in
    let s = map (fun (b,a) -> (type2t b, type2t a)) i in
    subst s tm
  with Failure _ ->
    let (x,tt) = dest_type ty in
    let name = if x = "fun" then "fun" else
               if x = "prod" then "prod" else full_name_of_type ty in
    let tt = map type2t tt in
    let name_tm = mk_mlstring name in
    if name = "fun" then mk_Atfun (el 0 tt, el 1 tt) else
    if name = "prod" then mk_Attup tt else
    if name = "list" then mk_Atapp (tt, mk_Short name_tm)
    else mk_Atapp (tt, full_id name_tm);;

(* the invariant variable of a type variable: a:A->v->bool for A *)
let tr_inv_var_of_tyvar ty =
  mk_var (String.lowercase_ascii (dest_vartype ty), mlinv_ty ty);;

let tr_VECTOR_TYPE_tm = `VECTOR_TYPE:(A->v->bool)->(A)vector->v->bool`;;
let tr_WORD_tm = `ml_WORD:(A)word->v->bool`;;

let rec inst_type_inv (ty,inv) ty0 =
  let i = type_match ty ty0 [] in
  let ss = map (fun (y,x) -> (get_type_inv y, inst i (get_type_inv x))) i in
  vsubst ss (inst i inv)

and list_inst_type_inv ty0 l =
  match l with
    [] -> failwith "list_inst_type_inv"
  | (ty,inv)::xs -> (try inst_type_inv (ty,inv) ty0
                     with Failure _ -> list_inst_type_inv ty0 xs)

and get_type_inv ty =
  if is_vartype ty then tr_inv_var_of_tyvar ty else
  if can dest_fun_type ty then
    let (t1,t2) = dest_fun_type ty in mk_Arrow (get_type_inv t1, get_type_inv t2) else
  if ty = bool_ty then tr_BOOL_inv else
  if word_ty_ok ty then inst [hd (snd (dest_type ty)), aty] tr_WORD_tm else
  if ty = tr_num_ty then tr_NUM_inv else
  if ty = tr_int_ty then tr_INT_inv else
  if ty = tr_char_ty then tr_CHAR_inv else
  if use_hol_string_type () && ty = tr_string_ty then tr_HOL_STRING_inv else
  if ty = mlstring_ty then tr_STRING_inv else
  if ty = tr_float64_ty then tr_FLOAT64_inv else
  if is_vector_type ty then tr_mk_icomb tr_VECTOR_TYPE_tm (get_type_inv (dest_vector_type ty))
  else
    try list_inst_type_inv ty !tr_other_types
    with Failure _ -> raise (Unsupported_type ty);;

let new_type_inv ty inv = tr_other_types := (ty,inv) :: !tr_other_types;;

let add_type_inv tm target_ty =
  let ty = fst (dest_fun_type (type_of tm)) in
  add_new_type_mapping ty target_ty; new_type_inv ty tm;;

let get_user_supplied_types () = map fst !tr_other_types;;

let add_eq_lemma eq_lemma =
  if concl eq_lemma = tr_T_tm then () else
  tr_all_eq_lemmas := eq_lemma :: !tr_all_eq_lemmas;;

let add_type_thms (rws1,rws2,res,tr_lemmas) =
  List.iter (fun (ty,eq_lemma,inv_def,conses,case_lemma,ts) -> add_eq_lemma eq_lemma) res;
  List.iter add_eq_lemma tr_lemmas;
  tr_type_memory := map (fun (ty,eq_lemma,inv_def,conses,case_lemma,ts) ->
                            (ty,inv_def,conses,case_lemma)) res @ !tr_type_memory;
  tr_preprocessor_rws := rws2 @ !tr_preprocessor_rws;;

let ignore_type ty = tr_type_memory := (ty,TRUTH,[],TRUTH) :: !tr_type_memory;;

let lookup_type_thms ty =
  find (fun (ty1,_,_,_) -> can (type_match ty1 ty) []) !tr_type_memory;;

let eq_lemmas () = !tr_all_eq_lemmas;;
let get_preprocessor_rws () = !tr_preprocessor_rws;;

(* ------------------------------------------------------------------------- *)
(* Names (HOL4 clean_lowercase, clean_uppercase, get_unique_name)            *)
(* ------------------------------------------------------------------------- *)

let tr_translate_string f s =
  String.concat "" (map (fun c -> f c) (explode s));;

let clean_lowercase s =
  let f c = if "a" <= c && c <= "z" then c else
            if "A" <= c && c <= "Z" then String.lowercase_ascii c else
            if "0" <= c && c <= "9" then c else
            if c = "," then "pair" else
            if c = "_" || c = "'" then c else "" in
  tr_translate_string f s;;

let clean_uppercase s =
  let f c = if "a" <= c && c <= "z" then String.uppercase_ascii c else
            if "A" <= c && c <= "Z" then c else
            if "0" <= c && c <= "9" then c else
            if c = "," then "PAIR" else
            if c = "_" || c = "'" then c else "" in
  tr_translate_string f s;;

let sml_keywords_and_predefined = ["o"; "+"; "-"; "*"; "div"; "mod";
  "<"; ">"; "<="; ">="; "ref"; "and"; "andalso"; "case"; "datatype";
  "else"; "end"; "eqtype"; "exception"; "fn"; "fun"; "handle"; "if";
  "in"; "include"; "let"; "local"; "of"; "op"; "open"; "orelse";
  "raise"; "rec"; "sharing"; "sig"; "signature"; "struct";
  "structure"; "then"; "type"; "val"; "where"; "while"; "with";
  "withtype"];;

let get_unique_name str =
  let names = get_names () @ sml_keywords_and_predefined in
  let rec find_name str n =
    let new_name = str ^ "_" ^ string_of_int n in
    if mem new_name names then find_name str (n+1) else new_name in
  let find_new_name str = if mem str names then find_name str 1 else str in
  let initial_name = clean_lowercase str in
  let initial_name = if initial_name = "" then "f" else initial_name in
  find_new_name initial_name;;

(* ------------------------------------------------------------------------- *)
(* Support for user-defined datatypes (HOL4 TL:955-2107)                     *)
(* ------------------------------------------------------------------------- *)

let tr_tyname ty = fst (dest_type ty);;

(* HOL Light's type_subst (a src file binds the name type_subst) *)
let tr_type_subst i ty = type_of (inst i (mk_var ("x", ty)));;

(* the case constant of the unit type (HOL4 one_CASE, one_case_def): HOL   *)
(* Light has none, and the kit's case constants are for inductive types.  *)
(* The translator writes a unit pattern f () = e as f v = one_CASE v e,    *)
(* HOL4's one-line form case v of () => e, translated as                   *)
(* Mat v [(Pcon NONE [], e)] (tr_unit_pat_rule, tr_derive_unit_thms).      *)
(* Its case information is the translator's own (not in the kit's tables) *)
let one_case_def = new_definition `one_CASE (u:1) (x:A) = x`;;

let tr_one_case_info =
  let c = `one_CASE:1->A->A` in
  let def = prove (`!f1:A. one_CASE one f1 = f1`, REWRITE_TAC [one_case_def]) in
  let nch = prove (`!x:1. x = one`, MATCH_ACCEPT_TAC one) in
  let ceq = prove (`!(x:1) (f1:A) (v:A). one_CASE x f1 = v <=> x = one /\ f1 = v`,
                   REWRITE_TAC [one_case_def] THEN ONCE_REWRITE_TAC [one] THEN
                   REWRITE_TAC []) in
  { ci_tyname = "1"; ci_case = c; ci_def = def; ci_pats = [([], tr_one_tm)];
    ci_nchotomy = nch; ci_case_eq = ceq; ci_match = ref None;
    ci_distinct = []; ci_inject = [] };;

let tr_is_one_CASE tm = is_const tm && fst (dest_const tm) = "one_CASE";;

let tr_case_info ty =
  if ty = tr_one_ty then tr_one_case_info else
  try case_info_of_tyname (tr_tyname ty)
  with Failure _ -> failwith ("no case constant for type " ^ string_of_type ty);;

let tr_case_info_of_const h =
  if tr_is_one_CASE h then tr_one_case_info else case_info_of_const h;;

let type_of_cases_const ty = type_of (tr_case_info ty).ci_case;;

(* rename free variables x' x'' to x (HOL4 remove_primes) *)
let remove_primes th =
  let rec strip s = let n = String.length s in
    if n > 0 && String.sub s (n-1) 1 = "'" then strip (String.sub s 0 (n-1)) else s in
  let fvs = itlist (fun t l -> union (frees t) l) (concl th :: hyp th) [] in
  let i = mapfilter (fun x -> let (n,ty) = dest_var x in
                       let n' = strip n in
                       if n = n' then fail() else (mk_var(n',ty), x)) fvs in
  if i = [] then th else INST i th;;

(* the cases theorem with the variables x{k}_{j} (constructor k, argument j, *)
(* in the order of the type's nchotomy), HOL4 get_nchotomy_of              *)
let get_nchotomy_of ty =
  let ci = tr_case_info ty in
  let nch = ci.ci_nchotomy in
  let x0 = fst (dest_forall (concl nch)) in
  let nch = INST_TYPE (type_match (type_of x0) ty []) nch in
  let x0,bod = dest_forall (concl nch) in
  let x_var = mk_var ("x", ty) in
  let disjs = disjuncts bod in
  let lines = map2 (fun d k ->
      let vs,eq = strip_exists d in
      let pat = rand eq in
      let args = snd (strip_comb pat) in
      let ws = map2 (fun a j -> mk_var ("x" ^ string_of_int k ^ "_" ^ string_of_int j,
                                         type_of a)) args (1--(length args)) in
      let pat' = list_mk_comb (fst (strip_comb pat), ws) in
      list_mk_exists (ws, mk_eq (x_var, pat')))
    disjs (1--(length disjs)) in
  let goal = mk_forall (x_var, list_mk_disj lines) in
  EQ_MP (ALPHA (concl nch) goal) nch;;

(* the constructor patterns of a cases theorem, in order *)
let tr_nchotomy_pats th =
  map (fun d -> rand (snd (strip_exists d))) (disjuncts (snd (dest_forall (concl th))));;

(* the types of a mutual (or nested) group: input :v gives [:v] etc.        *)
(* (HOL4 find_mutrec_types, from the recursion theorem)                    *)
let find_mutrec_types ty =
  let is_pair_ty ty = fst (dest_type ty) = "prod" in
  if is_pair_ty ty then [ty] else
  try
    let (_,_,rth) = assoc (tr_tyname ty) !inductive_type_store in
    let xs = map (fun v -> fst (dest_fun_ty (type_of v)))
                 (fst (strip_exists (snd (strip_forall (concl rth))))) in
    (* instantiate the group to the type arguments of ty *)
    let gen = find (fun t -> tr_tyname t = tr_tyname ty) xs in
    let i = type_match gen ty [] in
    let xs = map (tr_type_subst i) xs in
    let xs = filter (fun t -> intersect (snd (dest_type t)) xs = []) xs in
    if xs = [] then [ty] else xs
  with Failure _ -> [ty];;

(* ------------------------------------------------------------------------- *)
(* Deciding equations between literals: mlstrings, stamps, numerals          *)
(* ------------------------------------------------------------------------- *)

let tr_lit_eq_conv =
  let inj = [injectivity "mlstring"; injectivity "stamp"; injectivity "option";
             PAIR_EQ; injectivity "char"] in
  let dist = distinctness "stamp" :: distinctness "option" ::
             map (fun th -> EQF_INTRO (SPEC_ALL th))
                 (CONJUNCTS (distinctness "stamp")) in
  fun tm ->
    if not (is_eq tm) then failwith "tr_lit_eq_conv" else
    let l,r = dest_eq tm in
    if l = r then EQT_INTRO (REFL l) else
    let ty = type_of l in
    if ty = tr_num_ty && is_numeral l && is_numeral r then NUM_EQ_CONV tm else
    if ty = tr_string_ty && can dest_string l && can dest_string r then STRING_EQ_CONV tm else
    if ty = mlstring_ty || ty = stamp_ty then
      let th = (REWRITE_CONV (inj @ dist) THENC
                DEPTH_CONV (fun t -> if is_eq t && type_of (lhand t) = tr_string_ty &&
                                        can dest_string (lhand t) && can dest_string (rand t)
                                     then STRING_EQ_CONV t
                                     else if is_eq t && type_of (lhand t) = tr_num_ty &&
                                             is_numeral (lhand t) && is_numeral (rand t)
                                     then NUM_EQ_CONV t else failwith "") THENC
                REWRITE_CONV []) tm in
      let r = rand (concl th) in
      if r = tr_T_tm || r = tr_F_tm then th else failwith "tr_lit_eq_conv: undecided"
    else failwith "tr_lit_eq_conv";;

(* ALL_DISTINCT of a list of literals (HOL4 mlstr_all_distinct_conv) *)
let tr_ALL_DISTINCT_CONV_generic tm =
  (REWRITE_CONV [ALL_DISTINCT; MEM; DE_MORGAN_THM] THENC
   DEPTH_CONV (fun t -> if is_eq t then tr_lit_eq_conv t else failwith "") THENC
   REWRITE_CONV []) tm;;

(* equations between literals of the shapes of constructor names and stamps *)
(* (strings, numerals, implode s, TypeStamp s n, ExnStamp n) decided at the *)
(* top, without rewriting the strings' characters; tr_lit_eq_conv otherwise *)
let tr_ml_inj = injectivity "mlstring" and tr_st_inj = injectivity "stamp";;
let tr_st_dist = EQF_INTRO (SPEC_ALL (distinctness "stamp"));;
let tr_st_dist' = EQF_INTRO (GSYM (SPEC_ALL (distinctness "stamp")));;

let rec tr_lit_eq_fast tm =
    let head t = fst (strip_comb t) in
    let l,r = dest_eq tm in
    if l = r then EQT_INTRO (REFL l) else
    let ty = type_of l in
    if ty = tr_string_ty && can dest_string l && can dest_string r then STRING_EQ_CONV tm else
    if ty = tr_num_ty && is_numeral l && is_numeral r then NUM_EQ_CONV tm else
    if ty = mlstring_ty && tr_is_const_named "implode" (head l) &&
       tr_is_const_named "implode" (head r) then
      (GEN_REWRITE_CONV I [tr_ml_inj] THENC tr_lit_eq_fast) tm else
    if ty = stamp_ty && is_const (head l) && is_const (head r) then
      (if head l = head r then
         (GEN_REWRITE_CONV I [tr_st_inj] THENC
          (fun t -> if is_conj t then BINOP_CONV tr_lit_eq_fast t else tr_lit_eq_fast t) THENC
          REWRITE_CONV []) tm
       else GEN_REWRITE_CONV I [tr_st_dist; tr_st_dist'] tm)
    else tr_lit_eq_conv tm;;

(* ALL_DISTINCT l = T for a list of pairwise distinct literals, by MEM's and *)
(* ALL_DISTINCT's clauses and one inequality per pair; the rewriting of the  *)
(* generic version took 1.4 s for the 43 stamps of op                       *)
let tr_ALL_DISTINCT_CONV =
  let ad_nil = prove (`ALL_DISTINCT ([]:A list)`, REWRITE_TAC [ALL_DISTINCT]) in
  let ad_cons = prove (`!(h:A) t. ~MEM h t /\ ALL_DISTINCT t ==> ALL_DISTINCT (CONS h t)`,
                       SIMP_TAC [ALL_DISTINCT]) in
  let nm_nil = prove (`!h:A. ~MEM h []`, REWRITE_TAC [MEM]) in
  let nm_cons = prove (`!(h:A) x t. ~(h = x) /\ ~MEM h t ==> ~MEM h (CONS x t)`,
                       SIMP_TAC [MEM; DE_MORGAN_THM]) in
  let is_nil t = is_const t && fst (dest_const t) = "NIL" in
  let neq a b =
    let th = tr_lit_eq_fast (mk_eq (a, b)) in
    if rand (concl th) = tr_F_tm then EQF_ELIM th else failwith "tr_ALL_DISTINCT_CONV" in
  let rec not_mem h l =
    if is_nil l then ISPEC h nm_nil else
    let x,t = dest_cons l in
    MP (ISPECL [h; x; t] nm_cons) (CONJ (neq h x) (not_mem h t)) in
  let rec all_d l =
    if is_nil l then INST_TYPE [hd (snd (dest_type (type_of l))), aty] ad_nil else
    let h,t = dest_cons l in
    MP (ISPECL [h; t] ad_cons) (CONJ (not_mem h t) (all_d t)) in
  fun tm ->
    try
      (match tm with
         Comb(Const("ALL_DISTINCT",_), l) -> EQT_INTRO (all_d l)
       | _ -> failwith "")
    with Failure _ -> tr_ALL_DISTINCT_CONV_generic tm;;

let mlstring_EQ_CONV tm =
  if is_eq tm && type_of (lhand tm) = mlstring_ty &&
     is_mlstring_literal (lhand tm) && is_mlstring_literal (rand tm)
  then tr_lit_eq_conv tm else failwith "mlstring_EQ_CONV";;

(* ------------------------------------------------------------------------- *)
(* Lookups of constructors in the current environment (HOL4                *)
(* prove_lookup_cons_eq): |- lookup_cons n env_c = x <=> T (or F)          *)
(* ------------------------------------------------------------------------- *)

let prove_lookup_cons_eq tm =
  let res = (ml_prog_lookup_eq_conv THENC
             DEPTH_CONV (fun t -> if is_eq t then tr_lit_eq_conv t else failwith "") THENC
             REWRITE_CONV []) tm in
  let c = rand (concl res) in
  if frees tm <> [] || c = tr_T_tm || c = tr_F_tm then res
  else failwith "prove_lookup_cons_eq failed to reduce to F or T";;

(* HOL4 tag_name: the CakeML constructor name, unique in the current env *)
let tr_hol4_const_name c =
  try let (_,h4,_) = assoc c !tr_hol4_name_table in h4 with Failure _ -> c;;

let tag_name type_name const_name =
  if type_name = "LIST_TYPE" && const_name = "NIL" then "nil" else
  if type_name = "LIST_TYPE" && const_name = "CONS" then "::" else
  let x = clean_lowercase type_name in
  let y = clean_lowercase (tr_hol4_const_name const_name) in
  let upper_case_hd s =
    if s = "" then s else
    clean_uppercase (String.sub s 0 1) ^ String.sub s 1 (String.length s - 1) in
  let name = if y = "" then upper_case_hd x else upper_case_hd y in
  let is_taken_name name =
    let tm = mk_eq (mk_lookup_cons (mk_Short (mk_mlstring name), get_curr_env ()),
                    tr_NONE_num_stamp_tm) in
    let lemma = prove_lookup_cons_eq tm in
    rand (concl lemma) = tr_F_tm in
  let rec find_unique name n =
    if not (is_taken_name name) then name else
    let new_name = name ^ "_" ^ string_of_int n in
    if not (is_taken_name new_name) then new_name else find_unique name (n+1) in
  find_unique name 1;;

(* HOL4 rename_bound_vars_rule prefix: bound variables renamed prefix1, ...  *)
(* (prefixK_x_ for a variable x not named by the first renaming, as HOL4).  *)
(* Deviation: a genvar _N (HOL4 %%genvar%%N) becomes prefixK, not          *)
(* prefixK__N_, so that the generated code does not depend on the genvar   *)
(* counter of the session (the longer name only if prefixK would capture)  *)
let tr_is_genvar_name s =
  let n = String.length s in
  n > 1 && s.[0] = '_' &&
  (let rec digits j = j >= n || (s.[j] >= '0' && s.[j] <= '9' && digits (j+1)) in digits 1);;

let rename_bound_vars_rule prefix th =
  let i = ref 0 in
  let is_prefix p s = String.length s >= String.length p &&
                      String.sub s 0 (String.length p) = p in
  let next_alpha_conv tm =
    let v,_ = dest_abs tm in
    let (name,ty) = dest_var v in
    if is_prefix prefix name then failwith "" else
    (i := !i + 1;
     let n = prefix ^ string_of_int !i in
     if String.contains name ' ' then ALPHA_CONV (mk_var (n, ty)) tm
     else if tr_is_genvar_name name then
       (try ALPHA_CONV (mk_var (n, ty)) tm
        with Failure _ -> ALPHA_CONV (mk_var (n ^ "_" ^ name ^ "_", ty)) tm)
     else ALPHA_CONV (mk_var (n ^ "_" ^ name ^ "_", ty)) tm) in
  CONV_RULE (DEPTH_CONV next_alpha_conv) th;;

(* the constructor-name keys %%thy%%type%%ctor%% (HOL4 mk_cons_name) *)
let mk_cons_name tm =
  let _,ty = splitlist dest_fun_ty (type_of tm) in
  let (thy,tyn) = tr_hol4_type_info (fst (dest_type ty)) in
  let name = fst (dest_const tm) in
  String.concat "" ["%%"; thy; "%%"; tyn; "%%"; name; "%%"];;

let enter_cons_name (tm, v_tm) =
  let key = mk_cons_name tm in
  let mods = get_curr_modules () in
  let (v_tm', mods') = try lookup_cons_name key with Failure _ -> (v_tm, mods) in
  if aconv v_tm' v_tm && mods = mods' then
    (tr_cons_name_state := (key, (v_tm, mods)) :: !tr_cons_name_state; key)
  else failwith ("enter_cons_name: already entered with different value: " ^
                 string_of_term v_tm);;

let tys_is_pair_type tys = match tys with [ty] -> fst (dest_type ty) = "prod" | _ -> false;;
let tys_is_list_type tys = match tys with [ty] -> fst (dest_type ty) = "list" | _ -> false;;
let tys_is_unit_type tys = match tys with [ty] -> ty = tr_one_ty | _ -> false;;
let tys_is_order_type tys =
  match tys with [ty] -> (try tr_hol4_type_info (fst (dest_type ty)) = ("toto","cpn")
                          with Failure _ -> false)
               | _ -> false;;

(* the type arguments of a datatype that are type variables (HOL4: the fcp *)
(* numeric arguments are not generalised)                                  *)
let tr_type_params ty = filter is_vartype (snd (dest_type ty));;

(* ------------------------------------------------------------------------- *)
(* The refinement invariant of a group of types (HOL4 define_ref_inv)       *)
(* ------------------------------------------------------------------------- *)

let tr_last_def_tm = ref `T`;;

(* HOL4 OPTION_TYPE_SIMP (define_ref_inv's opt_extra_rw), once option is   *)
(* registered:  OPTION_TYPE p x =                                           *)
(*   ml_CONTAINER OPTION_TYPE (\y v. if x = SOME y then p y v else ARB) x    *)
(* (it exposes x = SOME y to the termination proofs of nested invariants)  *)
let tr_option_type_simp_cache = ref ([] : (term * thm) list);;
let tr_option_simp_pat =
  `!x. ml_CONTAINER (OPT:(A->v->bool)->(A)option->v->bool)
         (\y v. if x = SOME y then (p:A->v->bool) y v else ARB) x = OPT p x`;;
let tr_option_A_ty = `:(A)option` and tr_OPT_var = `OPT:(A->v->bool)->(A)option->v->bool`
and tr_option_x = `x:(A)option`;;

let tr_option_type_simp () =
  try
    let opt = rator (get_type_inv tr_option_A_ty) in
    (try [assoc opt !tr_option_type_simp_cache] with Failure _ ->
     let opt_def = tr_fetch (fst (dest_const opt) ^ "_def") in
     let goal = subst [opt, tr_OPT_var] tr_option_simp_pat in
     let th = prove (goal,
       GEN_TAC THEN STRUCT_CASES_TAC (ISPEC tr_option_x (cases "option")) THEN
       REWRITE_TAC [ml_CONTAINER_def; FUN_EQ_THM; opt_def; injectivity "option";
                    distinctness "option"] THEN
       CONV_TAC (DEPTH_CONV BETA_CONV) THEN REWRITE_TAC []) in
     let th = GSYM (SPEC tr_option_x th) in
     tr_option_type_simp_cache := (opt, th) :: !tr_option_type_simp_cache;
     [th])
  with Failure _ -> [];;

(* a definition, or the stored one if the session already has it: the kit *)
(* gives a benign redefinition (the same clauses, with the constants for   *)
(* the function variables) the stored theorem back, so a translation file  *)
(* can be loaded again in a session that holds it; other clauses for a     *)
(* defined name fail (HOL Light has one name space: HOL4 would define the  *)
(* constant again in another theory)                                       *)
(* HOL4 define_ref_inv's termination: tDefine with the measure of the     *)
(* input argument's size (build_measure) and a size tactic.  The kit tuples *)
(* the arguments of each function (right-nested) and injects the tuples of *)
(* a mutual group into a right-nested sum (cake_def_mutual).               *)
let tr_sum_size_tm = `sum_size:(A->num)->(B->num)->A+B->num`;;
let tr_MEASURE_tm = `MEASURE:(A->num)->A->A->bool`;;

let tr_inv_measure fns =
  let size_part f =
    let tys,_ = splitlist dest_fun_ty (type_of f) in
    let tupty = end_itlist (fun a b -> mk_type ("prod",[a;b])) tys in
    let p = mk_var ("p", tupty) in
    let inp = el (length tys - 2) (tuple_selectors (length tys) p) in
    mk_abs (p, mk_comb (size_of_type [] (type_of inp), inp)) in
  let rec combine l = match l with
      [f] -> f
    | f::rest ->
        let g = combine rest in
        let ta = fst (dest_fun_ty (type_of f)) and tb = fst (dest_fun_ty (type_of g)) in
        list_mk_comb (inst [ta, aty; tb, bty] tr_sum_size_tm, [f; g])
    | [] -> failwith "tr_inv_measure" in
  let m = combine (map size_part fns) in
  mk_comb (inst [fst (dest_fun_ty (type_of m)), aty] tr_MEASURE_tm, m);;

(* the termination conditions: the kit's TERM_TAC, with pair_size unfolded *)
(* for the elements of a list of pairs (PAIR_TYPE_SIMP's FST x, SND x)     *)
let tr_inv_term_tac : tactic =
  REPEAT BOSS_STRIP_TAC THEN RVEQ_TAC THEN
  (fun g -> let c = cake_term_rw_conv () in
            (RULE_ASSUM_TAC (CONV_RULE c) THEN CONV_TAC c) g) THEN
  MEM_SIZE_TAC THEN
  RULE_ASSUM_TAC (REWRITE_RULE [pair_size_THM; pair_size]) THEN
  REWRITE_TAC [pair_size] THEN
  ASM_ARITH_TAC;;

(* a definition, or the stored one if the session already has it: the kit *)
(* gives a benign redefinition (the same clauses, with the constants for   *)
(* the function variables) the stored theorem back, so a translation file  *)
(* can be loaded again in a session that holds it; other clauses for a     *)
(* defined name fail (HOL Light has one name space: HOL4 would define the  *)
(* constant again in another theory).  Recursive invariants by the measure *)
(* (cake_def as the fallback).                                              *)
let tr_define_benign name def_tm =
  let cvars = setify (map (fun c -> fst (strip_comb (lhs (snd (strip_forall c)))))
                          (conjuncts def_tm)) in
  let cnames = map (fun v -> fst (dest_var v)) cvars in
  let is_rec = exists (fun c -> let r = rhs (snd (strip_forall c)) in
                                exists (fun f -> free_in f r) cvars) (conjuncts def_tm) in
  let define tm =
    if is_rec then
      (try tr_time "invariant definition (cake_def_wf)"
             (cake_def_wf (tr_inv_measure cvars) tr_inv_term_tac) tm
       with Failure _ -> tr_time "invariant definition (cake_def)" cake_def tm)
    else tr_time "invariant definition (cake_def)" cake_def tm in
  if exists (fun n -> can get_const_type n) cnames then
    let sub = map (fun v -> let c = mk_const (fst (dest_var v), []) in
                            (inst (type_match (type_of c) (type_of v) []) c, v)) cvars in
    (try define (vsubst sub def_tm)
     with Failure s ->
       failwith ("define: " ^ String.concat " " cnames ^
                 " already defined with other clauses (" ^ s ^ ")"))
  else define def_tm;;

let define_ref_inv is_exn_type tys =
  let is_pair_type = tys_is_pair_type tys in
  let is_list_type = tys_is_list_type tys in
  let is_unit_type = tys_is_unit_type tys in
  let is_order_type = tys_is_order_type tys in
  let smart_full_name_of_type ty =
    if is_unit_type then "unit" else
    if is_order_type then "order" else full_name_of_type ty in
  let get_name ty = clean_uppercase (smart_full_name_of_type ty) ^ "_TYPE" in
  let names = map get_name tys in
  let name = hd names in
  let cases_thms = map get_nchotomy_of tys in
  let tmp_v_var = mk_var ("v", v_ty) in
  (* the left-hand sides FOO_TYPE a1 .. ak input v, with a variable FOO_TYPE *)
  let mk_lhs (name,ty,case_th) =
    let xs = tr_nchotomy_pats case_th in
    let ss = map get_type_inv (tr_type_params ty) in
    let input = mk_var ("input", ty) in
    let ml_ty_name = smart_full_name_of_type ty in
    let def_name = mk_var (name, itlist (fun x t -> mk_fun_ty (type_of x) t)
                                         (ss @ [input]) (mk_fun_ty v_ty bool_ty)) in
    let lhs = list_mk_comb (def_name, ss @ [input; tmp_v_var]) in
    (ml_ty_name, xs, ty, lhs, input) in
  let ys = map mk_lhs (zip names (zip tys cases_thms) |> map (fun (x,(y,z)) -> (x,y,z))) in
  let reg_type (_,_,ty,lhs,_) = new_type_inv ty (rator (rator lhs)) in
  let _ = map reg_type ys in
  let rw_lemmas = [LIST_TYPE_SIMP; PAIR_TYPE_SIMP] @ tr_option_type_simp () in
  let stamp = if is_exn_type then ml_prog_get_next_exn_stamp (get_ml_prog_state ())
              else ml_prog_get_next_type_stamp (get_ml_prog_state ()) in
  let get_def_tm () =
    (* one clause per constructor, the last constructor first (as HOL4) *)
    let mk_lines ml_ty_name lhs ty xs input stamp =
      let n = length xs in
      let rec go k stamp acc =
        if k = 0 then rev acc else
        let x = el (k-1) xs in
        let cons_name = fst (dest_const (fst (strip_comb x))) in
        let hol4_cons = tr_hol4_const_name cons_name in
        let tag = if is_exn_type && is_primitive_exception hol4_cons then hol4_cons
                  else tag_name name cons_name in
        let args = snd (strip_comb x) in
        let vars = map2 (fun a j -> (a, mk_var ("v" ^ string_of_int k ^ "_" ^ string_of_int j, v_ty)))
                        args (1--(length args)) in
        let find_inv tm = mk_comb (get_type_inv (type_of tm), tm) in
        let ys = map (fun (y,z) -> mk_comb (find_inv y, z)) vars in
        let tm = if ys = [] then tr_T_tm else list_mk_conj ys in
        let str = mk_mlstring tag in
        let vs = tr_mk_list (map snd vars, v_ty) in
        (* HOL4 attach_name: ExnStamp (K n "Tag") keeps the exception's name *)
        let attach_name tag t = mk_comb (rator t, list_mk_comb (tr_K_num_tm, [rand t; mk_mlstring tag])) in
        let tag_tm =
          if is_exn_type then
            (if is_primitive_exception tag then
               let (arity,value) = get_primitive_exception tag in
               if length vars = arity then mk_comb (tr_SOME_stamp_tm, attach_name tag (rand value))
               else failwith ("Incorrect arity for primitive exn: " ^ tag)
             else mk_comb (tr_SOME_stamp_tm, attach_name tag (mk_ExnStamp (mk_small_numeral stamp))))
          else mk_comb (tr_SOME_stamp_tm,
                        mk_TypeStamp (str, mk_small_numeral stamp)) in
        let tm = mk_conj (mk_eq (tmp_v_var, mk_Conv (tag_tm, vs)), tm) in
        let tm = list_mk_exists (map snd vars, tm) in
        let tm = vsubst [x, input] (mk_eq (lhs, tm)) in
        let stamp' = if is_exn_type && not (is_primitive_exception tag) then stamp + 1
                     else stamp in
        go (k-1) stamp' (tm :: acc) in
      go n stamp [] in
    let rec mk_all_lines ys stamp =
      match ys with
        [] -> []
      | (ml_ty_name,xs,ty,lhs,input)::rest ->
          mk_lines ml_ty_name lhs ty xs input stamp @
          mk_all_lines rest (if is_exn_type then stamp + length xs else stamp + 1) in
    let zs = mk_all_lines ys stamp in
    let def_tm = list_mk_conj zs in
    rand (concl (REWRITE_CONV rw_lemmas def_tm)) in
  let inv_def =
    if is_list_type then LIST_TYPE_def else
    if is_pair_type then PAIR_TYPE_def else
    if is_unit_type then UNIT_TYPE_def else
    let def_tm = get_def_tm () in
    let _ = tr_last_def_tm := def_tm in
    tr_define_benign name def_tm in
  (* HOL Light's higher-order matching rewrites the outer container first: *)
  (* LIST_TYPE (\x v. PAIR_TYPE a b x v) where HOL4's first-order matching *)
  (* gives LIST_TYPE (PAIR_TYPE a b)                                       *)
  let inv_def = CONV_RULE (DEPTH_CONV ETA_CONV) (REWRITE_RULE (map GSYM rw_lemmas) inv_def) in
  let _ = if is_list_type || is_pair_type || is_unit_type then inv_def
          (* HOL4 saves NAME_def with K_THM applied (ExnStamp 8, not       *)
          (* ExnStamp (K 8 "Failure")): later scripts rewrite with it       *)
          else tr_save_thm (name ^ "_def") (REWRITE_RULE [K_THM] inv_def) in
  let has_arg_with_type ty line =
    type_of (rand (rator (lhs (snd (strip_forall (concl line)))))) = ty in
  let inv_defs = map (fun ty -> (ty, end_itlist CONJ
                     (filter (has_arg_with_type ty) (CONJUNCTS inv_def)))) tys in
  (* register the new type invariants (constants now) *)
  let lhs_of_clause th = lhs (snd (strip_forall (concl (hd (CONJUNCTS th))))) in
  let sub l th =
    let c = fst (strip_comb (lhs_of_clause th)) in
    vsubst [c, fst (strip_comb l)] l in
  let ys2 = map2 (fun (_,th) (ml_ty_name,xs,ty,lhs,input) ->
                   (ml_ty_name,xs,ty,sub lhs th,input)) inv_defs ys in
  let _ = map reg_type ys2 in
  (name, inv_defs);;

(* ------------------------------------------------------------------------- *)
(* The case lemma of a type (HOL4 prove_case_of_lemma)                       *)
(* ------------------------------------------------------------------------- *)

let tr_ret_tyvar ty =
  let used = tyvars ty in
  let rec pick n = let tv = mk_vartype (if n = 0 then "RT" else "RT" ^ string_of_int n) in
                   if mem tv used then pick (n+1) else tv in
  pick 0;;

let tr_sum_case_def = (case_info_of_tyname "sum").ci_def;;
let tr_pair_case_def = (case_info_of_tyname "prod").ci_def;;

(* the main conjunct of IMP_Eval_Mat_cases, one goal per constructor: the *)
(* assumption input = Ci xs selects the row (kv, vars, exp_i, stamp, Ci);  *)
(* rth is the antecedent !vs. b0 /\ (CONTAINER (input = C1 ..) ==> ..) /\ ..*)
(* (TAG removed, as an assumption theorem), hyps the branch hypotheses     *)
(* ASM_REWRITE_TAC thl for many goals with the same long list thl: the net  *)
(* of the basic rewrites and thl is built once and the assumptions of each *)
(* goal are added to it (the same rewrites in the same order as             *)
(* ASM_REWRITE_TAC thl; the kit's memo of nets misses when the assumptions  *)
(* differ, and a case constant's clauses with n functions take long to     *)
(* canonicalize)                                                            *)
let tr_asm_rewrite_tac_with thl =
  let base = itlist (net_of_thm true) (itlist (mk_rewrites false) thl []) (basic_net ()) in
  fun (asl,w as g) -> CONV_TAC (GENERAL_REWRITE_CONV true TOP_DEPTH_CONV base (map snd asl)) g;;

(* MEM x [h1; ..; hn] = T when x is one of the hi (up to alpha), by MEM's  *)
(* clauses at the position of x only (no rewriting of the other elements) *)
let tr_MEM_T_CONV =
  let mem_hd = prove (`!(x:A) h t. x = h ==> MEM x (CONS h t)`, SIMP_TAC [MEM]) and
      mem_tl = prove (`!(x:A) h t. MEM x t ==> MEM x (CONS h t)`, SIMP_TAC [MEM]) in
  let rec prove_mem x l =
    let h,t = dest_cons l in
    if aconv x h then MP (ISPECL [x; h; t] mem_hd) (REFL x)
    else MP (ISPECL [x; h; t] mem_tl) (prove_mem x t) in
  fun tm ->
    match strip_comb tm with
      (c,[x;l]) when is_const c && fst (dest_const c) = "MEM" -> EQT_INTRO (prove_mem x l)
    | _ -> failwith "tr_MEM_T_CONV";;

let tr_case_branch_tac input inv_def case_def rows rth : tactic =
  let main_rw = tr_asm_rewrite_tac_with [MEM; LENGTH; ZIP; HD; TL; ml_write_list_def;
                                         case_def; K_THM] in
  fun (asl,w as g) ->
    let eqth = snd (find (fun (_,th) -> let c = concl th in
                           is_eq c && lhs c = input) asl) in
    let pat = rand (concl eqth) in
    let c = fst (strip_comb pat) in
    let (kv,vars,expi,stamp,ci,hypi) =
      find (fun (_,_,_,_,ci,_) -> ci = c) rows in
    (* b_i xs from the antecedent *)
    let rconjs = conjuncts (concl rth) in
    let rimp = find (fun t -> is_imp t &&
                         (let a = lhand t in is_CONTAINER a &&
                          (let e = rand a in is_eq e && lhs e = input &&
                           fst (strip_comb (rand e)) = c))) rconjs in
    let rimpth = find (fun th -> concl th = rimp) (CONJUNCTS rth) in
    let _,i,_ = term_match [] (rand (rand (lhand rimp))) pat in
    let bith = MP (INST i rimpth) (EQ_MP (SYM (ISPEC (concl eqth) ml_CONTAINER_def)) eqth) in
    (ASSUME_TAC bith THEN
     FIRST_X_ASSUM (fun th -> if concl th = concl eqth then SUBST_ALL_TAC th else failwith "") THEN
     FIRST_X_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE [inv_def] o
                    check (fun th -> let t = concl th in
                           is_comb t && rand t = tr_v_v && not (is_eq t))) THEN
     (fun (asl,w as g) ->
        let veq = snd (find (fun (_,th) -> let t = concl th in is_eq t && lhs t = tr_v_v) asl) in
        let ws = rand (rand (concl veq)) in
        (* IMP_Eval_Mat_cases: ?name vals t. (INL, pairs and unit) or     *)
        (* ?name vals t vars exp. (INR); ?vals. in older forms              *)
        let nex = if is_exists w then length (fst (strip_exists w)) else 0 in
        ((if nex = 1 then EXISTS_TAC ws
          else if nex = 3 then MAP_EVERY EXISTS_TAC [kv; ws; stamp]
          else MAP_EVERY EXISTS_TAC [kv; ws; stamp; vars; expi]) THEN
         CONV_TAC (ONCE_DEPTH_CONV tr_MEM_T_CONV) THEN main_rw THEN
         MATCH_MP_TAC hypi THEN ASM_REWRITE_TAC []) g)) g;;

(* rewrites from ALL_DISTINCT facts: ~(a = b) in both orientations *)
let tr_distinct_rws th =
  let cs = CONJUNCTS (REWRITE_RULE [ALL_DISTINCT; MEM; DE_MORGAN_THM; CONJ_ACI] th) in
  let cs = filter (fun c -> is_neg (concl c) && is_eq (rand (concl c))) cs in
  cs @ map (fun c -> CONV_RULE (RAND_CONV SYM_CONV) c) cs;;

let tr_case_dbg = ref (TRUTH, ([]:term list), TRUTH, TRUTH);;

let prove_case_of_lemma is_simple_case type_assum (ty, case_th, inv_lhs, inv_def) =
  let ci = tr_case_info ty in
  let c0 = ci.ci_case in
  let cty = type_of c0 in
  let dom0 = fst (dest_fun_ty cty) in
  let rty0 = snd (splitlist dest_fun_ty cty) in
  let ret_ty = tr_ret_tyvar ty in
  let c = inst (type_match dom0 ty [ret_ty, rty0]) c0 in
  let ftys = fst (splitlist dest_fun_ty (snd (dest_fun_ty (type_of c)))) in
  let fs = map2 (fun ty k -> mk_var ("f" ^ string_of_int k, ty)) ftys (1--(length ftys)) in
  let input_var = mk_var ("input", ty) in
  let cases_tm = list_mk_comb (c, input_var :: fs) in
  let pats = tr_nchotomy_pats case_th in
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
  (* the patterns *)
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
      mk_comb (tr_INL_cases_tm,
               mk_pair (vars, exp))
    else
      mk_comb (tr_INR_cases_tm,
               tr_mk_list (map (fun (kv,vars,exp,st,_) -> mk_pair (kv, mk_pair (vars, mk_pair (exp, st)))) rows,
                        tr_ps_cases_ty)) in
  let patterns = mk_comb (tr_Mat_cases_tm, y_tm) in
  let ret_inv = get_type_inv ret_ty in
  let exp_var = mk_var ("exp", exp_ty) in
  let result = mk_Eval (tr_env, mk_Mat (exp_var, patterns), mk_comb (ret_inv, cases_tm)) in
  let vs = flat (map (fun (n,f,fxs,pxs,tm,exp,xs) -> map (fun (x,_,_) -> x) xs) ts) in
  let b0 = mk_var ("b0", bool_ty) in
  let rtm = list_mk_conj (b0 :: map (fun (n,f,fxs,pxs,tm,exp,xs) ->
                            mk_imp (mk_CONTAINER (mk_eq (input_var, tm)), pxs)) ts) in
  let rtm = list_mk_forall (vs, rtm) in
  let rtag = mk_TAG (tr_one_tm, rtm) in
  let result = mk_imp (rtag, result) in
  let find_inv tm =
    if type_of tm = ty then mk_comb (rator (rator inv_lhs), tm)
    else mk_comb (get_type_inv (type_of tm), tm) in
  let mk_hyp (n,f,fxs,pxs,tm,exp,xs) =
    let env = itlist (fun (x,n,v) e -> mk_write (n,v,e)) (rev xs) tr_env in
    let tm = map (fun (x,n,v) -> mk_comb (find_inv x, v)) xs @ [pxs] in
    let tm = list_mk_conj tm in
    let tm = mk_imp (tm, mk_Eval (env, exp, mk_comb (ret_inv, fxs))) in
    let vs = map (fun (x,_,_) -> x) xs @ map (fun (_,_,v) -> v) xs in
    mk_TAG (mk_small_numeral n, list_mk_forall (vs, tm)) in
  let mk_alld (n,f,fxs,pxs,tm,exp,xs) =
    mk_comb (tr_ALL_DISTINCT_names_tm, tr_mk_list (map (fun (_,x,_) -> x) xs, mlstring_ty)) in
  let tt = if ts = [] then tr_T_tm else list_mk_conj (map mk_alld ts) in
  let hyps = map mk_hyp ts in
  let x = mk_comb (rator (rator inv_lhs), input_var) in
  let ev = mk_Eval (tr_env, exp_var, x) in
  let hyp0 = mk_TAG (tr_num0_tm, mk_imp (b0, ev)) in
  let hyps_tm = list_mk_conj (hyp0 :: hyps) in
  let goal = mk_imp (type_assum, mk_imp (tt, mk_imp (hyps_tm, result))) in
  (* the proof *)
  let ath = ASSUME type_assum and tth = ASSUME tt and hth = ASSUME hyps_tm
  and rth0 = ASSUME rtag in
  let untag th = CONV_RULE (REWR_CONV ml_TAG_def) th in
  let rth = SPEC_ALL (untag rth0) in
  let hths = map untag (CONJUNCTS hth) in
  let b0th = CONJUNCT1 rth in
  let e0 = MP (hd hths) b0th in
  let lemma = tr_ISPECL_NAMED ["a", rator x; "r1", input_var; "env", tr_env;
                               "exp", exp_var; "r2", mk_comb (ret_inv, cases_tm);
                               "y", y_tm] IMP_Eval_Mat_cases in
  let lemma = CONV_RULE (LAND_CONV (RAND_CONV (REWRITE_CONV [tr_sum_case_def; tr_pair_case_def] THENC
                                                DEPTH_CONV GEN_BETA_CONV))) lemma in
  let side = rand (lhand (concl lemma)) in
  let side_parts = conjuncts side in
  let _ = tr_case_dbg := (lemma, side_parts, ath, tth) in
  let main_goal = last side_parts in
  let rows6 = map2 (fun (kv,vars,exp,st,ctor) h -> (kv,vars,exp,st,ctor,h)) rows (tl hths) in
  let nch = case_th in
  let main_th =
    TAC_PROOF (([], main_goal),
      X_GEN_TAC tr_v_v THEN DISCH_TAC THEN
      STRIP_ASSUME_TAC (SPEC input_var nch) THEN
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
  (res, ts);;

(* ------------------------------------------------------------------------- *)
(* Constructor lemmas (HOL4 derive_cons)                                     *)
(* ------------------------------------------------------------------------- *)

let tr_ps_ty = `:(v->bool)#exp`;;

let derive_cons is_simple_case type_assum ty inv_lhs inv_def (n,f,fxs,pxs,tm,exp,xs) =
  let pat = tm in
  let str_tl s = String.sub s 1 (String.length s - 1) in
  let exps = map (fun (x,_,_) -> (x, mk_var ("exp" ^ str_tl (fst (dest_var x)), exp_ty))) xs in
  let ctor = fst (strip_comb tm) in
  let tag = if is_simple_case then "" else mk_cons_name ctor in
  let exps_tm = tr_mk_list (map snd exps, exp_ty) in
  let inv = rator (rator inv_lhs) in
  let cv = mk_var (tag, ml_id_ty) in
  let the_tag_name = if is_simple_case then tr_NONE_id_tm
                     else mk_comb (tr_SOME_id_tm, cv) in
  let find_inv tm =
    if type_of tm = ty then mk_comb (inv, tm) else mk_comb (get_type_inv (type_of tm), tm) in
  let ps = tr_mk_list (map (fun (x,exp) -> mk_pair (find_inv x, exp)) exps, tr_ps_ty) in
  let result = mk_Eval (tr_env, mk_Con (the_tag_name, exps_tm), mk_comb (inv, tm)) in
  let tms = map (fun (x,exp) -> mk_Eval (tr_env, exp, find_inv x)) exps in
  let etm = if tms = [] then tr_T_tm else list_mk_conj tms in
  let cons_assum =
    if is_simple_case then tr_T_tm else
    let cs = filter (fun t -> rand (lhs t) = tr_env && rand (rator (lhs t)) = cv)
                    (conjuncts type_assum) in
    if cs = [] then tr_T_tm else list_mk_conj cs in
  let goal = mk_imp (cons_assum, mk_imp (etm, result)) in
  let lemma0 = if is_simple_case then
                 tr_ISPECL_NAMED ["ps", ps; "env", tr_env; "q", mk_comb (inv, tm)] Eval_Con_NONE
               else
                 let st = rand (rand (rhs (hd (conjuncts cons_assum)))) in
                 tr_ISPECL_NAMED ["ps", ps; "name", cv; "env", tr_env; "stamp", st;
                                  "q", mk_comb (inv, tm)] Eval_Con in
  let lemma0 = CONV_RULE (RAND_CONV (REWRITE_CONV [MAP])) lemma0 in
  let lemma0 = CONV_RULE (LAND_CONV (DEPTH_CONV LENGTH_CONV THENC
                                     REWRITE_CONV [ALL] THENC DEPTH_CONV GEN_BETA_CONV THENC
                                     REWRITE_CONV [FST; SND] THENC
                                     REWRITE_CONV [LIST_REL_CONS1; LIST_REL_NIL] THENC
                                     DEPTH_CONV GEN_BETA_CONV THENC REWRITE_CONV [FST])) lemma0 in
  let witness_tac : tactic = fun (asl,w as g) ->
    let ws,bod = strip_exists w in
    let veq = hd (conjuncts bod) in
    let ts = dest_list (rand (lhs veq)) in
    (MAP_EVERY EXISTS_TAC ts THEN ASM_REWRITE_TAC []) g in
  let th = TAC_PROOF (([], goal),
    DISCH_TAC THEN DISCH_TAC THEN MATCH_MP_TAC lemma0 THEN
    ASM_REWRITE_TAC [] THEN
    REPEAT STRIP_TAC THEN REPEAT (FIRST_X_ASSUM SUBST_ALL_TAC) THEN
    REWRITE_TAC [inv_def; K_THM] THEN
    (witness_tac ORELSE ASM_REWRITE_TAC [])) in
  (pat, th);;

(* ------------------------------------------------------------------------- *)
(* EqualityType lemmas (HOL4 mk_EqualityType_ind, mk_EqualityType_thm,     *)
(* simp_eq_lemma): EqualityType a /\ .. ==> EqualityType (FOO_TYPE a ..),  *)
(* by induction over the type group with EqualityType_at at each value;   *)
(* TRUTH when the proof fails (types with functions)                       *)
(* ------------------------------------------------------------------------- *)

let tr_inv_head_defs = ref ([] : (string * thm) list);;

let tr_inv_def_of_head c =
  let n = fst (dest_const c) in
  try assoc n !tr_inv_head_defs with Failure _ ->
  match n with
    "LIST_TYPE" -> LIST_TYPE_def
  | "PAIR_TYPE" -> PAIR_TYPE_def
  | "UNIT_TYPE" -> UNIT_TYPE_def
  | _ -> tr_fetch (n ^ "_def");;

let tr_induction_of_group ty =
  let (_,ith,_) = assoc (tr_tyname ty) !inductive_type_store in
  let ps = fst (strip_forall (concl ith)) in
  let tys = map (fun p -> fst (dest_fun_ty (type_of p))) ps in
  let gen = find (fun t -> tr_tyname t = tr_tyname ty) tys in
  INST_TYPE (type_match gen ty []) ith;;

(* the three parts of EqualityType / EqualityType_at as separate facts *)
let tr_eq_facts th = CONJUNCTS (REWRITE_RULE [EqualityType_def; EqualityType_at_def] th);;

let tr_option_case_def = (case_info_of_tyname "option").ci_def;;

(* the pairs of different constructors C_i a, C_j b in EqualityType_at's    *)
(* second and third conjuncts: both sides of v = v2 <=> C_i a = C_j b are   *)
(* false and types_match v v2 holds, by the stamps of the values; proved    *)
(* from these two lemmas, the shape inv (C xs) v ==> ?vs. v = Conv (SOME st) *)
(* vs of each constructor (once) and one literal inequality, instead of the  *)
(* rewriting of both invariants for each of the n^2 pairs                    *)
let tr_eq_pairB = prove
 (`!(P1:bool) (P2:bool) (x1:A) (x2:A) (v:v) (v2:v) (st1:stamp) (st2:stamp).
     (P1 ==> ?vs. v = Conv (SOME st1) vs) /\ (P2 ==> ?vs. v2 = Conv (SOME st2) vs) /\
     ~(st1 = st2) /\ ~(x1 = x2) ==> (P1 /\ P2 ==> (v = v2 <=> x1 = x2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN RES_TAC THEN
  ASM_REWRITE_TAC [injectivity "v"; injectivity "option"]);;

let tr_eq_pairC = prove
 (`!(P1:bool) (P2:bool) (v:v) (v2:v) s1 s2 n.
     (P1 ==> ?vs. v = Conv (SOME (TypeStamp s1 n)) vs) /\
     (P2 ==> ?vs. v2 = Conv (SOME (TypeStamp s2 n)) vs) /\
     ~(s1 = s2) ==> (P1 /\ P2 ==> types_match v v2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN RES_TAC THEN
  ASM_REWRITE_TAC [types_match_def; ctor_same_type_def; same_type_def; injectivity "option";
                   injectivity "stamp"] THEN CASE_REWRITE_TAC [same_type_def] THEN
  ASM_REWRITE_TAC [injectivity "option"; injectivity "stamp"]);;

let tr_vs_var = `vs:v list`;;

(* the goal !v2. inv (C_i a) v /\ inv (C_j b) v2 ==> (v = v2 <=> C_i a = C_j b) *)
(* or ==> types_match v v2, for different constructors C_i, C_j; inv_conv     *)
(* rewrites with the invariant definitions, dist_conv with distinctness       *)
let tr_eq_pair_tac inv_conv dist_conv : tactic =
  let shapes = ref ([] : (term * thm) list) in
  let shape inv_tm =
    let x = rand (rator inv_tm) in
    let c = fst (strip_comb x) in
    let gen =
      try assoc c !shapes with Failure _ ->
      let w = rand inv_tm in
      let th = inv_conv inv_tm in
      let ws,b = strip_exists (rand (concl th)) in
      let eq = hd (conjuncts b) in
      if not (is_eq eq && lhs eq = w) then failwith "tr_eq_pair_tac: shape" else
      let ctm = rhs eq in
      let goal = mk_imp (inv_tm, mk_exists (tr_vs_var, mk_eq (w, mk_comb (rator ctm, tr_vs_var)))) in
      let sh = prove (goal,
        DISCH_THEN (MP_TAC o EQ_MP th) THEN STRIP_TAC THEN
        (fun (asl,g as gl) ->
           let e = snd (find (fun (_,a) -> let t = concl a in is_eq t && lhs t = w) asl) in
           (EXISTS_TAC (rand (rhs (concl e))) THEN ACCEPT_TAC e) gl)) in
      let sh = GEN_ALL sh in
      shapes := (c, sh) :: !shapes; sh in
    PART_MATCH lhand gen inv_tm in
  let stamp_of sh = rand (rand (rator (rhs (snd (dest_exists (rand (concl sh))))))) in
  fun (asl,w as g) ->
    let v2,bod = dest_forall w in
    let ant,cl = dest_imp bod in
    let inv1,inv2 = dest_conj ant in
    let x1 = rand (rator inv1) and x2 = rand (rator inv2) in
    let c1 = fst (strip_comb x1) and c2 = fst (strip_comb x2) in
    if not (is_const c1 && is_const c2) || c1 = c2 then failwith "tr_eq_pair_tac" else
    let sh1 = shape inv1 and sh2 = shape inv2 in
    let st1 = stamp_of sh1 and st2 = stamp_of sh2 in
    if is_eq cl then
      let v = lhs (lhs cl) in
      let st_neq = EQF_ELIM (tr_lit_eq_fast (mk_eq (st1, st2))) in
      let x_neq = EQF_ELIM (dist_conv (mk_eq (x1, x2))) in
      let th = MP (ISPECL [inv1; inv2; x1; x2; v; v2; st1; st2] tr_eq_pairB)
                  (CONJ sh1 (CONJ sh2 (CONJ st_neq x_neq))) in
      ACCEPT_TAC (GEN v2 th) g
    else
      let v = rand (rator cl) in
      let (s1,n1) = dest_TypeStamp st1 and (s2,n2) = dest_TypeStamp st2 in
      if n1 <> n2 then failwith "tr_eq_pair_tac: type numbers" else
      let s_neq = EQF_ELIM (tr_lit_eq_fast (mk_eq (s1, s2))) in
      let th = MP (ISPECL [inv1; inv2; v; v2; s1; s2; n1] tr_eq_pairC)
                  (CONJ sh1 (CONJ sh2 s_neq)) in
      ACCEPT_TAC (GEN v2 th) g;;

let tr_eqat_case_tac inv_defs nchs type_rws =
  (* the facts of the EqualityType and EqualityType_at assumptions, once per  *)
  (* assumption theorem (the global ones are shared by all the goals)         *)
  let facts_memo = ref ([] : (thm * thm list) list) in
  let facts_of th =
    let h = fst (strip_comb (concl th)) in
    if not (tr_is_const_named "EqualityType" h || tr_is_const_named "EqualityType_at" h)
    then [] else
    try List.assq th !facts_memo with Not_found ->
      let fs = filter (fun f -> is_forall (concl f)) (try tr_eq_facts th with Failure _ -> []) in
      facts_memo := (th, fs) :: !facts_memo; fs in
  let all_facts asl = flat (map (fun (_,th) -> facts_of th) asl) in
  let close_by_facts : tactic = fun (asl,w as g) ->
    let facts = all_facts asl in
    let asms = map snd asl in
    (* the goal no_closures v: first the invariant assumptions about v *)
    let asms1 = if is_comb w then filter (fun a -> let t = concl a in
                                           is_comb t && rand t = rand w) asms else [] in
    let cands1 = flat (map (fun f -> mapfilter (fun a -> MATCH_MP f a) asms1) facts) in
    try FIRST (map ACCEPT_TAC cands1) g with Failure _ ->
    let cands = flat (map (fun f -> mapfilter (fun a -> MATCH_MP f a) asms) facts) in
    FIRST (map ACCEPT_TAC cands) g in
  let res_facts : tactic = fun (asl,w as g) ->
    let facts = all_facts asl in
    MAP_EVERY (fun f -> TRY (IMP_RES_TAC f)) facts g in
  (* the facts a x v /\ a x2 v2 ==> .. for pairs of invariant assumptions    *)
  (* with the same invariant (IMP_RES_TAC with every fact took most of the   *)
  (* time of the nested types)                                               *)
  let res_pairs : tactic = fun (asl,w as g) ->
    let facts = all_facts asl in
    let invs = filter (fun a -> let t = concl a in
                         is_comb t && is_comb (rator t) && is_var (rand t) &&
                         type_of (rand t) = v_ty) (map snd asl) in
    let news = flat (map (fun a1 -> flat (map (fun a2 ->
                 if a1 == a2 || rator (rator (concl a1)) <> rator (rator (concl a2)) then []
                 else mapfilter (fun f -> MATCH_MP f (CONJ a1 a2)) facts) invs)) invs) in
    MAP_EVERY ASSUME_TAC news g in
  let res_close = (res_pairs THEN ASM_REWRITE_TAC [] THEN NO_TAC) ORELSE
                  (res_facts THEN ASM_REWRITE_TAC []) in
  let split_x2 : tactic = fun (asl,w as g) ->
    let (x2,_) = dest_forall (snd (dest_forall w)) in
    (* the nchotomy of a nested type (b list in a group) is the generic one *)
    let nch = tryfind (fun th -> let x = fst (dest_forall (concl th)) in
                         INST_TYPE (type_match (type_of x) (type_of x2) []) th) nchs in
    (X_GEN_TAC tr_v_v THEN X_GEN_TAC x2 THEN
     STRUCT_CASES_TAC (ISPEC x2 nch)) g in
  (* literal equalities: implode injectivity and CONS_11 can split a string *)
  (* literal into char equalities before STRING_EQ_CONV sees it            *)
  let lit_eq_conv = DEPTH_CONV (STRING_EQ_CONV ORELSEC CHAR_EQ_CONV ORELSEC NUM_EQ_CONV) in
  let simp_rws = [injectivity "v"; injectivity "option"; injectivity "stamp";
                  injectivity "mlstring"; CONS_11; NOT_CONS_NIL; NOT_NIL_CONS;
                  distinctness "option"; distinctness "stamp"; K_THM] in
  (* the rewrites of the pairwise goals as conversions built once (the nets  *)
  (* of ASM_REWRITE_TAC with the big lists were rebuilt for each of the n^2  *)
  (* goals: most of the time of a type with 40 constructors)                 *)
  let simp_conv = REWRITE_CONV simp_rws in
  let simp_type_conv = REWRITE_CONV (simp_rws @ type_rws) in
  let tm_conv = REWRITE_CONV ([types_match_def; ctor_same_type_def; same_type_def;
                               tr_option_case_def] @ simp_rws) in
  (* likewise the invariant definitions (REWRITE_TAC inv_defs, 2 n^2 + n times) *)
  let inv_conv = REWRITE_CONV inv_defs in
  let pair_tac = tr_eq_pair_tac inv_conv (GEN_REWRITE_CONV I type_rws) in
  REPEAT GEN_TAC THEN
  (fun (asl,w as g) -> if is_imp w then DISCH_THEN STRIP_ASSUME_TAC g else ALL_TAC g) THEN
  REWRITE_TAC [EqualityType_at_def] THEN REPEAT CONJ_TAC THENL
  [GEN_TAC THEN CONV_TAC inv_conv THEN STRIP_TAC THEN
   ASM_REWRITE_TAC [no_closures_def; ALL] THEN REPEAT CONJ_TAC THEN close_by_facts;
   split_x2 THEN (pair_tac ORELSE (X_GEN_TAC tr_v2_v THEN CONV_TAC inv_conv THEN STRIP_TAC THEN
   ASM_REWRITE_TAC [] THEN CONV_TAC simp_conv THEN CONV_TAC lit_eq_conv THEN
   CONV_TAC simp_type_conv THEN CONV_TAC lit_eq_conv THEN REWRITE_TAC [] THEN
   res_close));
   split_x2 THEN (pair_tac ORELSE (X_GEN_TAC tr_v2_v THEN CONV_TAC inv_conv THEN STRIP_TAC THEN
   ASM_REWRITE_TAC [] THEN CONV_TAC tm_conv THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN CONV_TAC tm_conv THEN
   CONV_TAC lit_eq_conv THEN REWRITE_TAC [] THEN
   res_close))];;
let tr_eq_dbg = ref (`T`, ([]:term list));;
let tr_EqualityType_at_tm = `EqualityType_at:(A->v->bool)->A->bool`;;

let mk_EqualityType_group tys =
  let ind = tr_induction_of_group (hd tys) in
  let ps,body = strip_forall (concl ind) in
  let ind_p,ind_c = dest_imp body in
  let proof_tys = map (fun c -> type_of (fst (dest_forall c))) (conjuncts ind_c) in
  let rec arg_tys tm =
    if is_forall tm then let (v,b) = dest_forall tm in type_of v :: arg_tys b
    else if is_imp tm then arg_tys (snd (dest_imp tm))
    else if is_conj tm then let (a,b) = dest_conj tm in arg_tys a @ arg_tys b
    else [] in
  let assum_tys = setify (arg_tys ind_p) in
  let ex_assum_tys = subtract assum_tys proof_tys in
  let invs = map get_type_inv proof_tys in
  let heads = setify (filter is_const (map (fun i -> fst (strip_comb i)) invs)) in
  let inv_defs = map tr_inv_def_of_head heads in
  let gl = list_mk_conj (map mk_EqualityType invs) in
  let assums = map (fun t -> mk_EqualityType (get_type_inv t)) ex_assum_tys in
  let goal = if assums = [] then gl else mk_imp (list_mk_conj assums, gl) in
  let _ = tr_eq_dbg := (goal, assums) in
  let nchs = map (fun t -> (tr_case_info t).ci_nchotomy) proof_tys in
  let type_rws = flat (map (fun t -> let ci = tr_case_info t in ci.ci_distinct @ ci.ci_inject)
                       proof_tys) in
  let pinst = map2 (fun p i -> let x = mk_var ("x", fst (dest_fun_ty (type_of p))) in
                      mk_abs (x, tr_list_mk_icomb tr_EqualityType_at_tm [i; x])) ps invs in
  let ind' = CONV_RULE (DEPTH_CONV BETA_CONV) (ISPECL pinst ind) in
  let tac =
    (if assums = [] then ALL_TAC else DISCH_THEN (STRIP_ASSUME_TAC)) THEN
    REWRITE_TAC [EqualityType_eq_at] THEN
    MATCH_MP_TAC ind' THEN REPEAT CONJ_TAC THEN
    tr_eqat_case_tac inv_defs nchs type_rws in
  (assums, prove (goal, tac));;
(* the EqualityType lemma of each type of a group, with the hypotheses the  *)
(* eq lemmas prove removed (HOL4 simp_eq_lemma); TRUTH if the proof fails  *)
let tr_simp_eq_hyps th =
  let lemmas = map (fun l -> tr_UNDISCH_ALL (REWRITE_RULE [GSYM IMP_IMP] (SPEC_ALL l)))
                   (eq_lemmas ()) in
  let rec find_match l tm = match l with
      [] -> failwith "find_match"
    | th1::rest ->
        (try let (_,ss,i) = term_match [] (concl th1) tm in INST ss (INST_TYPE i th1)
         with Failure _ -> find_match rest tm) in
  let rec remove th =
    try let h = find (fun h -> can (find_match lemmas) h) (hyp th) in
        remove (PROVE_HYP (find_match lemmas h) th)
    with Failure _ -> th in
  remove th;;

(* ------------------------------------------------------------------------- *)
(* Type representations (HOL4 fetch_v_fun_ex, define_v_fun, define_type_reps, *)
(* simp_eq_lemma): FOO_v : foo -> v with |- IsTypeRep FOO_v FOO_TYPE for the *)
(* types with EqualityType                                                   *)
(* ------------------------------------------------------------------------- *)

(* HOL4 strip_imp: the antecedents and the conclusion *)
let tr_strip_imp tm = splitlist dest_imp tm;;

let tr_DUMMY_TYPE_REP_v_tm =
  fst (strip_comb (lhs (snd (strip_forall (concl DUMMY_TYPE_REP_v)))));;

let rec fetch_v_fun_ex extra_tms extra_thms ty =
  match (try Some (assoc ty extra_tms) with Failure _ -> None) with
    Some v_fun -> (v_fun, [])
  | None ->
    if is_vartype ty then (mk_var ("t_" ^ dest_vartype ty ^ "_v", mk_fun_ty ty v_ty), []) else
    let inv = get_type_inv ty in
    let inv_head = fst (strip_comb inv) in
    (* HOL4: HOL_STRING_TYPE and other constant invariants have no arguments *)
    let tys = if is_const inv then [] else snd (dest_type ty) in
    let opts = mapfilter (fun t ->
        let (f,r) = dest_IsTypeRep (snd (tr_strip_imp (concl (SPEC_ALL t)))) in
        (* HOL4 same_const: by name (the lemma's constant is generic) *)
        let h = fst (strip_comb r) in
        if is_const h && is_const inv_head && fst (dest_const h) = fst (dest_const inv_head)
        then (fst (strip_comb f), t) else fail ())
      (extra_thms @ eq_lemmas ()) in
    let opts = rev (itlist (fun (f,t) acc -> if exists (fun (g,_) -> g = f) acc then acc
                                             else (f,t) :: acc) (rev opts) []) in
    let (f, arg_tys, thms) =
      match opts with
        [] -> (tr_DUMMY_TYPE_REP_v_tm, [], [])
      | [(f,th)] -> (f, tys, [th])
      | _ -> failwith ("fetch_v_fun_ex: multiple options for " ^ string_of_type ty) in
    let rec_xs = map (fetch_v_fun_ex extra_tms extra_thms) arg_tys in
    let arg_funs = map fst rec_xs in
    let f_arg = last (fst (splitlist dest_fun_ty (type_of f))) in
    let m = type_match f_arg ty [] in
    (list_mk_comb (inst m f, arg_funs), thms @ flat (map snd rec_xs));;

let mk_v_app extras v = mk_comb (fst (fetch_v_fun_ex extras [] (type_of v)), v);;

let fetch_v_fun ty = fetch_v_fun_ex [] [] ty;;

(* the type's induction theorem at ty (HOL4 matching_induction_of) *)
let matching_induction_of ty =
  let (_,ind,_) = assoc (tr_tyname ty) !inductive_type_store in
  let ind_c = snd (dest_imp (snd (strip_forall (concl ind)))) in
  let var_tys = map (fun c -> type_of (fst (dest_forall c))) (conjuncts ind_c) in
  let m = tryfind (fun vty -> type_match vty ty []) var_tys in
  INST_TYPE m ind;;

let tr_replace_suffix s from to_ =
  let n = String.length s and k = String.length from in
  if n >= k && String.sub s (n-k) k = from then String.sub s 0 (n-k) ^ to_ else s;;

(* a side condition of a type-rep or EqualityType lemma proved by the eq    *)
(* lemmas (HOL4 EqualityType_cc_conv): |- A ==> tm, A weaker or T           *)
let rec tr_eq_cc depth tm =
  if depth > 8 then DISCH tm (ASSUME tm) else
  if not (is_IsTypeRep tm || is_EqualityType tm) then
    (try let eq = tr_WORD_CONV tm in
         if rand (concl eq) = tr_T_tm then DISCH tr_T_tm (EQ_MP (SYM eq) TRUTH) else fail ()
     with Failure _ -> DISCH tm (ASSUME tm)) else
  let try_lemma l =
    (* HOL4: REWRITE_RULE [AND_IMP_INTRO]: the antecedents as one conjunction *)
    let l = PURE_REWRITE_RULE [IMP_IMP] (SPEC_ALL l) in
    let c = concl l in
    if is_imp c then
      let (a,b) = dest_imp c in
      let (_,ss,ii) = term_match [] b tm in
      let l' = INST ss (INST_TYPE ii l) in
      let a' = fst (dest_imp (concl l')) in
      if frees a' <> [] && exists (fun v -> not (mem v (frees tm))) (frees a') then fail () else
      (* the new antecedent's conjuncts in turn *)
      let parts = map (tr_eq_cc (depth+1)) (conjuncts a') in
      let ants = map (fun th -> fst (dest_imp (concl th))) parts in
      let ants = filter (fun t -> t <> tr_T_tm) ants in
      let ant = if ants = [] then tr_T_tm else list_mk_conj ants in
      let ath = ASSUME ant in
      let athl = if ants = [] then [] else CONJUNCTS ath in
      let prove_part th =
        let a = fst (dest_imp (concl th)) in
        if a = tr_T_tm then MP th TRUTH else MP th (find (fun x -> concl x = a) athl) in
      let a'th = end_itlist CONJ (map prove_part parts) in
      DISCH ant (MP l' a'th)
    else
      let (_,ss,ii) = term_match [] c tm in
      DISCH tr_T_tm (INST ss (INST_TYPE ii l)) in
  try tryfind try_lemma (eq_lemmas ()) with Failure _ -> DISCH tm (ASSUME tm);;

(* |- tm from the eq lemmas (HOL4: fs (map (REWRITE_RULE [AND_IMP_INTRO]) (eq_lemmas ()))) *)
let tr_prove_by_eq_lemmas tm =
  let th = tr_eq_cc 0 tm in
  if fst (dest_imp (concl th)) = tr_T_tm then MP th TRUTH
  else failwith ("tr_prove_by_eq_lemmas: " ^ string_of_term (fst (dest_imp (concl th))));;

let simp_eq_lemma th =
  if not (is_imp (concl th)) then th else
  let a,_ = dest_imp (concl th) in
  let parts = map (tr_eq_cc 0) (conjuncts a) in
  let ants = filter (fun t -> t <> tr_T_tm) (map (fun p -> fst (dest_imp (concl p))) parts) in
  let ant = if ants = [] then tr_T_tm else list_mk_conj ants in
  let athl = if ants = [] then [] else CONJUNCTS (ASSUME ant) in
  let prove_part p =
    let a = fst (dest_imp (concl p)) in
    if a = tr_T_tm then MP p TRUTH else MP p (find (fun x -> concl x = a) athl) in
  let th' = MP th (end_itlist CONJ (map prove_part parts)) in
  if ants = [] then th' else DISCH ant th';;

let tr_type_rep_ss_rws () = [injectivity "v"; CONS_11; injectivity "option"];;

(* functions over a (nested) type group by its recursion theorem, with      *)
(* parameters params before the recursion argument: HOL Light's             *)
(* new_recursive_definition first; else the theorem instantiated directly   *)
(* (the kit's define_size_functions does the same: the recursion theorem of *)
(* a nested group has clauses such as fn3 (a0,a1) = f4 a1 a0 (fn0 a0) that  *)
(* the recursion package does not match), then skolemized over params       *)
let tr_new_recursive_definition rth def params =
  try kit_new_recursive_definition rth def with Failure _ ->
  let user = map (fun c -> let l,r = dest_eq (snd (strip_forall c)) in
                           let opapp,pat = dest_comb l in
                           (fst (strip_comb opapp), pat, r)) (conjuncts def) in
  let ops = setify (map (fun (f,_,_) -> f) user) in
  let dom_of_op f = last (fst (splitlist dest_fun_ty (type_of f))) in
  let fvs0,bod0 = strip_forall (concl rth) in
  let fns0,_ = strip_exists bod0 in
  let tyin = map (fun fn -> (v_ty, snd (dest_fun_ty (type_of fn)))) fns0 in
  let rthn = INST_TYPE tyin rth in
  let fvs',bod' = strip_forall (concl rthn) in
  let fns',cls' = strip_exists bod' in
  let op_of_fn fn = find (fun f -> dom_of_op f = fst (dest_fun_ty (type_of fn))) ops in
  let opapp_of_fn fn = list_mk_comb (op_of_fn fn, params) in
  let inst_of cl =
    let _,eq = strip_forall cl in
    let l,r = dest_eq eq in
    let fn = rator l and pat = rand l in
    let fi,rargs = strip_comb r in
    let opf = op_of_fn fn in
    let (_,upat,urhs) = find (fun (f',p,_) -> f' = opf && can (term_match [] p) pat) user in
    let (_,ren,_) = term_match [] upat pat in
    let urhs' = vsubst ren urhs in
    let rvs = map (fun t -> if is_var t then t else genvar (type_of t)) rargs in
    let repl = mapfilter (fun (rv,t) -> if is_var t then fail () else
                            let fnl,x = dest_comb t in (rv, mk_comb (opapp_of_fn fnl, x)))
                         (zip rvs rargs) in
    let body = subst repl urhs' in
    (fi, list_mk_abs (rvs, body)) in
  let insts = map inst_of (conjuncts cls') in
  let th1 = CONV_RULE (DEPTH_CONV BETA_CONV) (ISPECL (map (fun f -> assoc f insts) fvs') rthn) in
  let th2 = if params = [] then th1 else CONV_RULE SKOLEM_CONV (GENL params th1) in
  let names = map (fun fn -> fst (dest_var (op_of_fn fn))) fns' in
  let sp = new_specification names th2 in
  let sp = SPECL params sp in
  end_itlist CONJ (map GEN_ALL (CONJUNCTS sp));;

let tr_vfun_dbg = ref (TRUTH, "");;

let define_v_fun ty =
  let main_ty = ty in
  let ind = matching_induction_of ty in
  let args = map (fun c -> fst (dest_forall c))
                 (conjuncts (snd (dest_imp (snd (strip_forall (concl ind)))))) in
  let param_tys = map (fun tv -> fst (fetch_v_fun tv)) (tr_type_params main_ty) in
  let ty_inv_defs = map tr_inv_def_of_head
      (setify (filter is_const (map (fun a -> fst (strip_comb (get_type_inv (type_of a)))) args))) in
  let name t = tr_replace_suffix (fst (dest_const (fst (strip_comb (get_type_inv t))))) "_TYPE" "_v" in
  let is_aux t = exists (fun a -> not (is_vartype a)) (snd (dest_type t)) in
  let aux_name i t = if is_aux t then name main_ty ^ "_aux_" ^ string_of_int i else name t in
  let ops = map2 (fun v i ->
      list_mk_comb (mk_var (aux_name i (type_of v),
                            itlist (fun h t -> mk_fun_ty (type_of h) t) param_tys
                                   (mk_fun_ty (type_of v) v_ty)), param_tys))
    args (0--(length args - 1)) in
  let op_tups = map (fun t -> (fst (dest_fun_ty (type_of t)), t)) ops in
  let cases = map (fun c -> rand (snd (tr_strip_imp (snd (strip_forall c)))))
                  (conjuncts (fst (dest_imp (snd (strip_forall (concl ind)))))) in
  let inv_def_eqs = flat (map (fun th -> conjuncts (concl th)) ty_inv_defs) in
  let case_eqn t =
    let (c, xs) = strip_comb t in
    let eq = find (fun e -> can (find_term (fun x -> is_const x && fst (dest_const x) =
                                                     fst (dest_const c)))
                                (lhs (snd (strip_forall e)))) inv_def_eqs in
    let conv = find_term is_Conv eq in
    let stamp = fst (dest_Conv conv) in
    mk_eq (mk_v_app op_tups t, mk_Conv (stamp, tr_mk_list (map (mk_v_app op_tups) xs, v_ty))) in
  let def = list_mk_conj (map case_eqn cases) in
  let (_,_,rth) = assoc (tr_tyname ty) !inductive_type_store in
  let def_thm = tr_new_recursive_definition rth def param_tys in
  tr_vfun_dbg := (def_thm, "defined");
  let const_ops = setify (map (fun c -> rator (lhs (snd (strip_forall c))))
                              (conjuncts (concl def_thm))) in
  let const_op_tups = map (fun t -> (fst (dest_fun_ty (type_of t)), t)) (const_ops @ param_tys) in
  let mk_is_tr t = mk_IsTypeRep (fst (fetch_v_fun_ex const_op_tups [] t), get_type_inv t) in
  let arg_tys = map type_of args in
  let all_tys = setify (map type_of (flat (map (fun c -> filter is_var (snd (strip_comb c))) cases))) in
  let other_tys = subtract all_tys arg_tys in
  let prop = list_mk_conj (map (fun a -> mk_is_tr (type_of a)) args) in
  let asms = list_mk_conj (tr_T_tm :: map mk_is_tr other_tys) in
  tr_vfun_dbg := (def_thm, "proving");
  let thm = prove (mk_imp (asms, prop),
    REWRITE_TAC [IsTypeRep_def] THEN TRY (DISCH_THEN STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC ind THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC (def_thm :: ty_inv_defs) THEN
    REWRITE_TAC (tr_type_rep_ss_rws ()) THEN
    tr_quiet_tac (ASM_MESON_TAC [])) in
  let res = map (fun t -> prove (mk_imp (asms, mk_is_tr t),
                                 DISCH_TAC THEN MP_TAC thm THEN ASM_REWRITE_TAC [] THEN
                                 STRIP_TAC THEN ASM_REWRITE_TAC []))
                (filter (fun t -> not (is_aux t)) arg_tys) in
  res;;

let rec define_type_reps tys =
  match tys with
    [] -> []
  | ty :: rest ->
      let reps = define_type_reps rest in
      let more = match (try Some (fetch_v_fun_ex [] reps ty) with Failure _ -> None) with
          Some (_, []) -> define_v_fun ty
        | _ -> [] in
      more @ reps;;

let mk_EqualityType_thms tys =
  try
    let (assums, th) = mk_EqualityType_group tys in
    let th = if assums = [] then th else tr_normalise_assums (UNDISCH th) in
    let invs = map get_type_inv tys in
    map (fun inv ->
           let c = find (fun c -> rand (concl c) = inv) (CONJUNCTS th) in
           let c = tr_simp_eq_hyps c in
           let hs = hyp c in
           itlist DISCH hs c) invs
  with Failure s ->
    (Format.print_string (".. cannot do EqualityType proof (" ^ s ^ ").\n");
     map (fun _ -> TRUTH) tys);;

(* ------------------------------------------------------------------------- *)
(* Records (HOL4 derive_record_specific_thms): the accessors and updates as  *)
(* case expressions, translated at registration (rws1), and the canonical   *)
(* order of updates for the preprocessor (rws2)                             *)
(* ------------------------------------------------------------------------- *)

let tr_is_record ty = can record_info (tr_tyname ty);;

let derive_record_specific_thms ty =
  let ri = record_info (tr_tyname ty) in
  let ci = tr_case_info ty in
  let nch = ci.ci_nchotomy in
  let x0 = fst (dest_forall (concl nch)) in
  let nch = INST_TYPE (type_match (type_of x0) ty []) nch in
  let pat = rand (snd (strip_exists (snd (dest_forall (concl nch))))) in
  let cons,xs = strip_comb pat in
  let case_c = let c0 = ci.ci_case in
               let dom0 = fst (dest_fun_ty (type_of c0)) in
               inst (type_match dom0 ty []) c0 in
  let v = mk_var ("v", ty) in
  let prove_eq goal =
    tr_auto_prove "record lemma" (goal,
      REPEAT GEN_TAC THEN STRUCT_CASES_TAC (ISPEC v nch) THEN
      REWRITE_TAC [ri.ri_accessors; ri.ri_fupds; ci.ci_def] THEN
      CONV_TAC (DEPTH_CONV BETA_CONV) THEN REWRITE_TAC []) in
  let mk_case f =
    let cty = type_of case_c in
    let rty = snd (splitlist dest_fun_ty cty) in
    let c' = inst (type_match rty (type_of (snd (strip_abs f))) []) case_c in
    list_mk_comb (c', [v; f]) in
  let a_lemmas = map2 (fun (_,acc,_) x ->
      let acc = inst (type_match (fst (dest_fun_ty (type_of acc))) ty []) acc in
      let f = list_mk_abs (xs, x) in
      prove_eq (mk_forall (v, mk_eq (mk_comb (acc, v), mk_case f)))) ri.ri_fields xs in
  let b_lemmas = map2 (fun (_,_,upd) x ->
      let gty = fst (dest_fun_ty (type_of upd)) in
      let upd = inst (type_match (snd (dest_fun_ty (snd (dest_fun_ty (type_of upd))))) ty []) upd in
      let gty = fst (dest_fun_ty (type_of upd)) in
      let g = mk_var ("g", gty) in
      let body = list_mk_comb (cons, map (fun y -> if y = x then mk_comb (g, y) else y) xs) in
      let f = list_mk_abs (xs, body) in
      prove_eq (mk_forall (v, mk_forall (g, mk_eq (list_mk_comb (upd, [g; v]), mk_case f)))))
    ri.ri_fields xs in
  let rws2 = if length ri.ri_fields > 1 then [ri.ri_fupdcanon] else [] in
  (a_lemmas @ b_lemmas, rws2);;

(* ------------------------------------------------------------------------- *)
(* All theorems of a type group (HOL4 derive_thms_for_type)                 *)
(* ------------------------------------------------------------------------- *)

let tr_lhs_of_clause th = lhs (snd (strip_forall (concl (hd (CONJUNCTS th)))));;

(* the generic type of the type operator of ty (the first argument of its *)
(* case constant), with numeric type arguments of ty kept where the generic *)
(* type has a type variable (HOL4 derive_thms_for_type, inst_fcp_types:    *)
(* word lengths are not generalised)                                        *)
let tr_generic_type ty =
  let gen = fst (dest_fun_ty (type_of_cases_const ty)) in
  let (_, tyargs) = dest_type ty and (_, gen_tyargs) = dest_type gen in
  let i = itlist2 (fun x y acc ->
             if is_vartype y && (try tr_numeral_type_value x > 1 with Failure _ -> false)
             then (x, y) :: acc else acc) tyargs gen_tyargs [] in
  tr_type_subst i gen;;

(* the unit type :1 (HOL4 register_type ``:unit``, the is_unit_type case): *)
(* the invariant UNIT_TYPE, the declaration type unit = (), the case       *)
(* lemma of one_CASE (Mat x [(Pcon NONE [], e)]); one itself is translated *)
(* by hol2deep (Eval_Val_UNIT)                                             *)
let tr_derive_unit_thms () =
  Format.print_string "Adding type unit\n";
  new_type_inv tr_one_ty (fst (strip_comb (lhs (snd (strip_forall (concl UNIT_TYPE_def))))));
  let dtype = mk_Dtabbrev (mk_mlstring "unit", mk_Attup []) in
  let _ = enter_type_mod "unit" in
  let inv_lhs = tr_lhs_of_clause UNIT_TYPE_def in
  let inv_lhs = subst [mk_var ("input", tr_one_ty), rand (rator inv_lhs)] inv_lhs in
  let (case_lemma, ts) =
    prove_case_of_lemma true tr_T_tm
      (tr_one_ty, get_nchotomy_of tr_one_ty, inv_lhs, UNIT_TYPE_def) in
  ([], [], [(tr_one_ty, TRUTH, UNIT_TYPE_def, [], case_lemma, ts)], [],
   tr_mk_list ([dtype], tr_dec_ty));;

let derive_thms_for_type is_exn_type ty =
  if ty = tr_one_ty then tr_derive_unit_thms () else
  let ty = tr_generic_type ty in
  let tys = find_mutrec_types ty in
  let is_pair_type = tys_is_pair_type tys in
  let is_list_type = tys_is_list_type tys in
  let is_unit_type = tys_is_unit_type tys in
  let is_order_type = tys_is_order_type tys in
  let is_simple_case = is_pair_type || is_unit_type in
  let _ = List.iter (fun ty -> Format.print_string
                      ("Adding type " ^ string_of_type ty ^ "\n")) tys in
  let case_thms = map (fun ty -> (ty, get_nchotomy_of ty)) tys in
  let (name, inv_defs) = tr_time "define_ref_inv" (define_ref_inv is_exn_type) tys in
  (* the CakeML datatype declaration *)
  let (dtype, dtype_list) =
    if name = "UNIT_TYPE" then
      (mk_Dtabbrev (mk_mlstring "unit", mk_Attup []), tr_mk_list ([], tr_dec_ty)) else
    if name = "PAIR_TYPE" then (mk_Dtype (tr_mk_list ([], tr_dtype_part_ty)),
                                tr_mk_list ([], tr_dec_ty)) else
    let extract_dtype_part (ty0, th) =
      let xs = map (fun c -> dest_eq (concl (SPEC_ALL c))) (CONJUNCTS th) in
      let ys = map (fun (x,y) ->
                 let body = snd (strip_exists y) in
                 let veq = hd (conjuncts body) in
                 (rand (rator x), rand (rand (rator (rand veq))))) xs in
      let tyname =
        if is_order_type then mk_mlstring "order" else
        if is_unit_type then mk_mlstring "unit" else
        let t = rand (type2t (type_of (fst (hd ys)))) in
        let rec strip t = if is_Long t then strip (snd (dest_Long t)) else t in
        rand (strip t) in
      let ys = map (fun (x,y) ->
                 ((if is_exn_type then rand (rand y) else rand (rator y)),
                  map (fun a -> type2t (type_of a)) (snd (strip_comb x)))) ys in
      let mk_line (x,y) = mk_pair (x, tr_mk_list (y, ast_t_ty)) in
      let lines = tr_mk_list (map mk_line ys, tr_dtype_line_ty) in
      let ts = map (fun tv -> mk_mlstring (tr_tyvar_ml_name tv)) (tr_type_params ty0) in
      let ts_tm = tr_mk_list (ts, mlstring_ty) in
      mk_pair (ts_tm, mk_pair (tyname, lines)) in
    let dtype_parts = map extract_dtype_part inv_defs in
    let dtype_list = tr_mk_list (dtype_parts, type_of (hd dtype_parts)) in
    (mk_Dtype dtype_list, dtype_list) in
  (* constructor assumptions *)
  let mk_assum tm =
    if not is_exn_type then
      let x = find_term is_TypeStamp (rhs tm) in
      let (n,k) = dest_TypeStamp x in
      let input = rand (rator (lhs tm)) in
      let l = mk_small_numeral (length (snd (strip_comb input))) in
      let ctor = fst (strip_comb input) in
      let cv = mk_var (enter_cons_name (ctor, n), ml_id_ty) in
      mk_eq (mk_lookup_cons (cv, tr_env),
             mk_comb (tr_SOME_num_stamp_tm, mk_pair (l, x)))
    else
      let x = find_term is_ExnStamp tm in
      let n = dest_ExnStamp x in
      let input = rand (rator (lhs tm)) in
      let l = mk_small_numeral (length (snd (strip_comb input))) in
      let ctor = fst (strip_comb input) in
      let cv = mk_var (enter_cons_name (ctor, rand n), ml_id_ty) in
      mk_eq (mk_lookup_cons (cv, tr_env),
             mk_comb (tr_SOME_num_stamp_tm, mk_pair (l, mk_ExnStamp (rand (rator n))))) in
  let type_assum =
    if name = "PAIR_TYPE" || name = "UNIT_TYPE" then tr_T_tm else
    list_mk_conj (map (fun c -> mk_assum (concl (SPEC_ALL c)))
                      (flat (map (fun (_,x) -> CONJUNCTS x) inv_defs))) in
  let make_calls ((ty,case_th),(_,inv_def)) =
    let inv_lhs = tr_lhs_of_clause inv_def in
    let x = rand (rator inv_lhs) in
    let input = mk_var ("input", type_of x) in
    let inv_lhs = subst [input, x] inv_lhs in
    let (case_lemma, ts) = prove_case_of_lemma is_simple_case type_assum
                             (ty, case_th, inv_lhs, inv_def) in
    let conses = map (derive_cons is_simple_case type_assum ty inv_lhs inv_def) ts in
    (ty, TRUTH, inv_def, conses, case_lemma, ts) in
  let res = tr_time "case and constructor lemmas" (map make_calls) (zip case_thms inv_defs) in
  (* EqualityType lemmas (HOL4 define_ref_inv's eq_lemmas) *)
  let _ = List.iter (fun (_,inv_def) ->
            let c = fst (strip_comb (tr_lhs_of_clause inv_def)) in
            tr_inv_head_defs := (fst (dest_const c), REWRITE_RULE [K_THM] inv_def) ::
                                !tr_inv_head_defs) inv_defs in
  let eqs = tr_time "EqualityType" mk_EqualityType_thms tys in
  (* HOL4 define_ref_inv's type_rep_lemmas *)
  let tr_lemmas =
    let tys_eq = map fst (filter (fun (_,eq) -> concl eq <> tr_T_tm) (zip tys eqs)) in
    try map simp_eq_lemma (tr_time "type reps" define_type_reps tys_eq)
    with Failure s -> (Format.print_string (".. cannot define type reps (" ^ s ^ ").\n"); []) in
  let res = map2 (fun (ty,_,inv_def,conses,case_lemma,ts) eq ->
                    (ty,eq,inv_def,conses,case_lemma,ts)) res eqs in
  (* the exception declarations (HOL4 dexn_list): one Dexn per constructor *)
  (* that is not a primitive exception                                    *)
  let dexn_list =
    if not is_exn_type then [] else
    let lines = flat (map (fun part -> dest_list (rand (rand part))) (dest_list dtype_list)) in
    let ds = map (fun l -> let (x,y) = dest_pair l in (x, mk_Dexn (x, y))) lines in
    map snd (filter (fun (x,_) -> not (is_primitive_exception (dest_mlstring x))) ds) in
  let dprog =
    let decs = if mem name ["LIST_TYPE"; "PAIR_TYPE"] then []
               else if is_exn_type then dexn_list else [dtype] in
    tr_mk_list (decs, tr_dec_ty) in
  let (rws1,rws2) = if not (tr_is_record ty) then ([],[])
                    else derive_record_specific_thms (hd tys) in
  let name = full_name_of_type ty in
  let _ = enter_type_mod name in
  (rws1, rws2, res, tr_lemmas, dprog);;

(* ------------------------------------------------------------------------- *)
(* register_type (HOL4 add_type, lookup_add_type, register_type_main)        *)
(* ------------------------------------------------------------------------- *)

let tr_translator = ref (fun (th:thm) -> th);;
let set_translator t = tr_translator := t;;

let tr_store_dprog dprog = ml_prog_update (ml_prog_add_prog dprog I);;

let add_type ty =
  let (rws1,rws2,res,tr_lemmas,dprog) = derive_thms_for_type false ty in
  tr_store_dprog dprog;
  add_type_thms (rws1,rws2,res,tr_lemmas);
  List.iter (fun th -> ignore (!tr_translator th)) rws1;
  res;;

let lookup_add_type ty =
  try lookup_type_thms ty
  with Failure _ -> (ignore (add_type ty); lookup_type_thms ty);;

let rec register_type ty =
  try ignore (lookup_add_type ty)
  with Unsupported_type ty1 -> (register_type ty1; register_type ty);;

(* HOL4 register_exn_type: the constructors become exceptions (Dexn, the  *)
(* primitive exceptions Bind, Chr, Div, Subscript of the initial env kept) *)
let register_exn_type ty =
  let (rws1,rws2,res,tr_lemmas,dprog) = derive_thms_for_type true ty in
  tr_store_dprog dprog;
  add_type_thms (rws1,rws2,res,tr_lemmas);
  List.iter (fun th -> ignore (!tr_translator th)) rws1;;

let conses_of ty = let (_,_,conses,_) = lookup_type_thms ty in conses;;

let cons_for tm =
  try
    let ty = type_of tm in
    let conses = conses_of ty in
    let (pat,th) = find (fun (x,th) -> can (term_match [] x) tm) conses in
    let (_,_,i) = term_match [] pat tm in
    let ss = map (fun (y,x) -> (get_type_inv y, inst i (get_type_inv x))) i in
    INST ss (INST_TYPE i th)
  with Failure _ -> failwith "cons_for: Not a constructor for a registered type.";;

let case_of ty = let (_,_,_,case_lemma) = lookup_type_thms ty in case_lemma;;

(* ------------------------------------------------------------------------- *)
(* Constructors and case expressions in hol2deep (HOL4 inst_cons_thm,        *)
(* inst_case_thm_for, inst_case_thm)                                         *)
(* ------------------------------------------------------------------------- *)

let inst_cons_thm tm hol2deep =
  let th = UNDISCH (cons_for tm) in
  let res = rand (rand (concl (tr_UNDISCH_ALL th))) in
  let xs = snd (strip_comb res) in
  let (_,ss,_) = term_match [] res tm in
  let ys = map (fun x -> remove_primes (hol2deep (vsubst ss x))) xs in
  (* an argument translated with HOL_STRING_TYPE where the constructor     *)
  (* expects LIST_TYPE ml_CHAR, or the other way round (HOL4 insert_HOL_STRING) *)
  let ys =
    try
      let refs = map rand (conjuncts (fst (dest_imp (concl th)))) in
      let insert_HOL_STRING (y,r) =
        if can (term_match [] r) (rand (concl y)) then y else
        let res = MATCH_MP Eval_HOL_STRING_INTRO y in
        Format.print_string "Warning: automatically added string IMPLODE due to HOL_STRING_TYPE\n";
        res in
      map insert_HOL_STRING (zip ys refs)
    with Failure _ -> ys in
  let th1 = if ys = [] then TRUTH else end_itlist CONJ ys in
  try MATCH_MP th (tr_UNDISCH_ALL th1)
  with Failure _ ->
    if use_hol_string_type () && type_of tm = tr_string_ty then failwith "string cons"
    else raise (Unable_to_translate tm);;

(* the names of the pattern variables of a case arm with k arguments *)
let tr_arm_vars k f =
  let vs,_ = strip_abs f in
  if length vs >= k then fst (chop_list k vs)
  else failwith "tr_arm_vars: case arm is not a lambda of the constructor's arity";;

let tr_inst_case_fail = ref `T`;;

let inst_case_thm_for tm =
  try
    let h,args = strip_comb tm in
    let x0 = hd args and arms = tl args in
    let th = UNDISCH (case_of (type_of x0)) in
    let pat = rand (rand (concl (tr_UNDISCH_ALL th))) in
    let (_,ss,i) = term_match [] pat tm in
    let th = INST ss (INST_TYPE i th) in
    let ss = map (fun (y,x) -> (get_type_inv y, inst i (get_type_inv x))) i in
    let th = INST ss th in
    let th = CONV_RULE (DEPTH_CONV BETA_CONV) th in
    (* the arms' variable names for the n, v and x variables of the lemma *)
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
        (* by name: the constructors of the lemma are type-instantiated *)
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
    MP th TRUTH
  with Failure s -> (tr_inst_case_fail := tm; failwith ("inst_case_thm_for: " ^ s));;

(* hypotheses about variables in an environment ml_write n v env (HOL4     *)
(* SIMP_CONV std_ss [Eval_Var_SIMP, lookup_var_write] THENC                 *)
(* DEPTH_CONV mlstring_EQ_CONV THENC SIMP_CONV std_ss [])                   *)
let tr_env_hyp_conv extra =
  REWRITE_CONV ([Eval_Var_SIMP; lookup_var_write; lookup_cons_write] @ extra) THENC
  DEPTH_CONV mlstring_EQ_CONV THENC
  REWRITE_CONV ([Eval_Var_SIMP; lookup_var_write; lookup_cons_write] @ extra);;

let tr_last_fail = ref `T`;;

(* the residual hypotheses of a case arm (|- x1 /\ r ==> y, x1 the pattern  *)
(* variables' invariants): the conjuncts of r that do not mention the arm's *)
(* variables vs and are lookup, Eval or EqualityType facts become           *)
(* hypotheses of the theorem.  clean_assumptions lifts such facts out at    *)
(* the end anyway; lifted here, they are no longer repeated in every arm    *)
(* of nested cases (balanceL: a 50000-character hypothesis, rewritten at    *)
(* every level and for every parameter).  Conditions such as PRECONDITION  *)
(* stay in the arm                                                          *)
let tr_liftable_fact tm =
  is_EqualityType tm || is_Eval tm ||
  (is_eq tm && (let l = lhs tm in
                is_lookup_cons l || (tr_head_is "nsLookup" l && length (tr_dest_args l) = 2)));;

let tr_lift_closed_facts vs th =
  let ant,_ = dest_imp (concl th) in
  let x1,r = dest_conj ant in
  let cs = conjuncts r in
  let closed c = not (exists (fun v -> vfree_in v c) vs) in
  let lift c = c <> tr_T_tm && closed c && tr_liftable_fact c in
  let gs = filter lift cs in
  if gs = [] then th else
  (* the other conjuncts in r's nesting (the shape clean_assumptions leaves *)
  (* when it rewrites the lifted facts to T)                                *)
  let rec prune t =
    if is_conj t then
      (match prune (lhand t), prune (rand t) with
         None, b -> b
       | a, None -> a
       | Some a, Some b -> Some (mk_conj (a, b)))
    else if lift t then None else Some t in
  let l = match prune r with None -> tr_T_tm | Some t -> t in
  let bl = mk_conj (x1, l) in
  let a = ASSUME bl in
  let lths = if l = tr_T_tm then [] else CONJUNCTS (CONJUNCT2 a) in
  let facts = map ASSUME gs @ lths @ [TRUTH] in
  let rec build t =
    if is_conj t then CONJ (build (lhand t)) (build (rand t))
    else find (fun f -> aconv (concl f) t) facts in
  DISCH bl (MP th (CONJ (CONJUNCT1 a) (build r)));;

let inst_case_thm tm hol2deep =
  let th = inst_case_thm_for tm in
  let th = CONV_RULE (RATOR_CONV (PURE_REWRITE_CONV [CONJ_ASSOC])) th in
  let (hyps,rest) = dest_imp (concl th) in
  let sat_hyp tm =
    try
      let (vs,x) = strip_forall tm in
      let (x,y) = dest_imp x in
      let z = rand (rand y) in
      let lemma = tr_D (hol2deep z) in
      let new_env = rand (rator (rator y)) in
      let lemma = PURE_REWRITE_RULE [lookup_cons_write] (INST [new_env, tr_env] lemma) in
      let (x1,x2) = try dest_conj x with Failure _ -> (tr_T_tm, x) in
      let (z1,z2) = dest_imp (concl lemma) in
      let thz = DISCH x1 (tr_env_hyp_conv (CONJUNCTS (ASSUME x1)) z1) in
      let lemma = MATCH_MP sat_hyp_lemma (CONJ thz lemma) in
      let lemma = tr_lift_closed_facts vs lemma in
      let bs = fst (chop_list (length vs / 2) vs) in
      let rec list_unbeta_conv l = match l with
          [] -> ALL_CONV
        | x::xs -> tr_UNBETA_CONV x THENC RATOR_CONV (list_unbeta_conv xs) in
      let lemma = CONV_RULE (RATOR_CONV (RAND_CONV (RAND_CONV
                    (list_unbeta_conv (rev bs))))) lemma in
      let lemma = GENL vs lemma in
      (if can (term_match [] tm) (concl lemma) then () else failwith "sat_hyp failed");
      remove_primes lemma
    with Failure s -> (tr_last_fail := tm; failwith s)
       | Unable_to_translate t -> (tr_last_fail := tm; raise (Unable_to_translate t)) in
  let rec sat_hyps tm =
    if is_conj tm then let (x,y) = dest_conj tm in CONJ (sat_hyps x) (sat_hyps y)
    else sat_hyp tm in
  let lemma = sat_hyps hyps in
  let th = MATCH_MP th lemma in
  let th = CONV_RULE (RATOR_CONV (DEPTH_CONV BETA_CONV THENC REWRITE_CONV [])) th in
  tr_UNDISCH_ALL th;;

(* EqualityType hypotheses discharged by the eq lemmas (HOL4                *)
(* SIMP_EqualityType_ASSUMS)                                                 *)
let SIMP_EqualityType_ASSUMS th =
  let lemmas = map (fun l -> tr_UNDISCH_ALL (REWRITE_RULE [GSYM IMP_IMP] (SPEC_ALL l)))
                   (eq_lemmas ()) in
  let th = tr_normalise_assums th in
  let xs = map (fun th -> (concl th, th)) lemmas in
  let rec find_match l tm = match l with
      [] -> failwith "find_match"
    | (pat,th1)::rest ->
        (try let (_,ss,i) = term_match [] pat tm in INST ss (INST_TYPE i th1)
         with Failure _ -> find_match rest tm) in
  let rec remove_one th =
    try
      let hs = hyp th in
      let tm = find (fun h -> can (find_match xs) h) hs in
      let lemma = find_match xs tm in
      remove_one (PROVE_HYP lemma th)
    with Failure _ -> th in
  remove_one th;;

(* ------------------------------------------------------------------------- *)
(* Preprocessing (HOL4 TL:2611-3094)                                         *)
(* ------------------------------------------------------------------------- *)

(* HOL4 pattern_complete: PRECONDITION (some clause matches) *)
let pattern_complete def vs =
  let lines = map (fun c -> lhs (concl (SPEC_ALL c))) (CONJUNCTS (SPEC_ALL def)) in
  let const = fst (strip_comb (hd lines)) in
  let ws = map (fun v -> (v, genvar (type_of v))) vs in
  let tm = list_mk_comb (const, map snd ws) in
  let tt line =
    let (_,i,_) = term_match [] tm line in
    list_mk_exists (frees line,
      list_mk_conj (map (fun (_,w) -> mk_eq (w, vsubst i w)) ws)) in
  let pat_tm = list_mk_disj (map tt lines) in
  let pat_tm = vsubst (map (fun (y,x) -> (y,x)) ws) pat_tm in
  mk_PRECONDITION pat_tm;;

let is_rec_def def =
  let thms = map SPEC_ALL (CONJUNCTS (SPEC_ALL def)) in
  let consts = setify (map (fun th -> fst (strip_comb (lhs (concl th)))) thms) in
  let rhss = map (rand o concl) thms in
  exists (fun r -> exists (fun c -> free_in c r) consts) rhss;;

(* the induction theorem of a definition: the kit's cake_ind, or a         *)
(* registered one (HOL4 add_preferred_thy / f_ind lookup), or the type's    *)
(* structural induction                                                     *)
let tr_ind_overrides = ref ([] : (string * thm) list);;
let add_ind_thm name th = tr_ind_overrides := (name, th) :: !tr_ind_overrides;;

let find_ind_thm def =
  let const = fst (strip_comb (lhs (concl (SPEC_ALL (hd (CONJUNCTS (SPEC_ALL def))))))) in
  let name = fst (dest_const const) in
  try assoc name !tr_ind_overrides with Failure _ ->
  try cake_ind name with Failure _ -> TRUTH;;

(* HOL Light's let terms: LET (\x. LET_END b) e becomes LET (\x. b) e *)
let tr_LET_END_CONV = REWRITE_CONV [LET_END_DEF];;

(* HOL4 split_let_and_conv: let x = a and y = b in t -> nested lets *)
let split_let_and_conv tm =
  let f,args = strip_comb tm in
  if not (tr_is_const_named "LET" f) || length args < 3 then failwith "split_let_and_conv" else
  let lam = hd args and vals = tl args in
  let vs,b = strip_abs lam in
  if length vs <> length vals || length vs < 2 then failwith "split_let_and_conv" else
  let ys = map (fun (x,y) -> (x, genvar (type_of x), y)) (zip vs vals) in
  let b2 = vsubst (map (fun (x,y,_) -> (y,x)) ys) b in
  let mk_let1 (y,z) b = list_mk_comb (inst [type_of y, aty; type_of b, bty] tr_LET_tm,
                                      [mk_abs (y, b); z]) in
  let tm2 = itlist (fun (x,y,z) b -> mk_let1 (y,z) b) ys b2 in
  let goal = mk_eq (tm, tm2) in
  tr_auto_prove "split_let_and_conv"
    (goal, REWRITE_TAC [LET_DEF] THEN CONV_TAC (DEPTH_CONV BETA_CONV) THEN REWRITE_TAC []);;

(* one equation per function of a definition, f v1 .. vn = rhs (HOL4      *)
(* mutual_to_single_line_def / single_line_def): the kit's ONELINE for each *)
(* function; when the patterns are incomplete (HOL Light leaves the other  *)
(* arguments unspecified) a conditional form                                *)
(*   PRECONDITION (some clause matches) ==> f v1 .. vn = case .. ARB ..      *)
(* (PLAN 1c.8 H7)                                                           *)
let tr_group_by_function def =
  let cls = map SPEC_ALL (CONJUNCTS (SPEC_ALL def)) in
  let head c = fst (strip_comb (lhs (concl c))) in
  let fs = rev (itlist (fun c l -> let h = head c in if mem h l then l else h :: l)
                       (rev cls) []) in
  map (fun f -> f, filter (fun c -> head c = f) cls) fs;;

(* the clauses as one equation under the precondition that some clause    *)
(* matches (HOL4 single_line_def with pattern_complete; the kit's ONELINE  *)
(* builds the same case tree, with ARB where no clause matches)            *)
(* the coverage disjunction (?xs. v = pat1) \/ .. of complete patterns that  *)
(* ONELINE does not compile (boolean literals, also under constructors):    *)
(* split the variables compared with constructor or literal patterns (by    *)
(* the type's nchotomy, BOOL_CASES_TAC), rewrite with injectivity and       *)
(* distinctness, at most depth splits on a branch                           *)
let tr_cover_rules tyname =
  (try [injectivity tyname] with Failure _ -> []) @
  (try let th = distinctness tyname in
       flat (map (fun c -> let c = SPEC_ALL c in [EQF_INTRO c; EQF_INTRO (GSYM c)])
                 (CONJUNCTS th))
   with Failure _ -> []);;

let tr_EXISTS_REFL' = prove (`!a:A. (?x. a = x) <=> T`, MESON_TAC []);;

let rec tr_cover_tac rules depth : tactic = fun (asl,w as g) ->
  let close = REWRITE_TAC (rules @ [EXISTS_REFL; tr_EXISTS_REFL'; UNWIND_THM1; UNWIND_THM2])
              THEN NO_TAC in
  (close ORELSE
   (fun (asl,w as g) ->
      if depth = 0 then NO_TAC g else
      let cands = find_terms (fun t -> is_eq t && is_var (lhs t) && free_in (lhs t) w &&
                                       not (is_var (rhs t))) w in
      (* boolean literals become ~a0 and a0 after rewriting: split those too *)
      let bools = filter (fun v -> type_of v = bool_ty) (frees w) in
      let cands = cands @ map (fun v -> mk_eq (v, tr_T_tm)) bools in
      match cands with
        [] -> NO_TAC g
      | eq :: _ ->
          let v = lhs eq in
          let ty = type_of v in
          let (split, rules') =
            if ty = bool_ty then (BOOL_CASES_TAC v, rules) else
            let tyname = fst (dest_type ty) in
            (STRUCT_CASES_TAC (ISPEC v (tr_case_info ty).ci_nchotomy),
             rules @ tr_cover_rules tyname) in
          (split THEN REWRITE_TAC rules' THEN tr_cover_tac rules' (depth - 1)) g)) g;;

let tr_conditional_oneline f cls =
  let rows = map (fun c -> let l,r = dest_eq (concl c) in
                           let g,args = strip_comb l in g,args,r,c) cls in
  let _,args1,_,_ = hd rows in
  let n = length args1 in
  let patcols = filter (fun i -> exists (fun (_,a,_,_) -> not (is_var (el i a))) rows)
                       (0--(n-1)) in
  let patfvs = itlist (fun (_,a,_,_) acc ->
                         union (freesl (map (fun i -> el i a) patcols)) acc) rows [] in
  let avoid = ref patfvs in
  (* HOL4 one_line_ify: the pattern columns, right to left, get v, v0, v1 .. *)
  (* (numvariant; primes would be removed by remove_primes, making two      *)
  (* arguments v of different types, one CakeML name)                       *)
  let rec numvariant v =
    let (s,ty) = dest_var v in
    if not (mem s (map (fun u -> fst (dest_var u)) !avoid)) then (avoid := v :: !avoid; v) else
    let k = String.length s in
    let rec digits j = if j > 0 && s.[j-1] >= '0' && s.[j-1] <= '9' then digits (j-1) else j in
    let j = digits k in
    let s' = if j < k then String.sub s 0 j ^ string_of_int (int_of_string (String.sub s j (k-j)) + 1)
             else s ^ "0" in
    numvariant (mk_var (s',ty)) in
  let actual = rev (map (fun i -> let a = el i args1 in
                           if mem i patcols then numvariant (mk_var ("v", type_of a))
                           else pm_fresh avoid a) (rev (0--(n-1)))) in
  let counter = ref 0 in
  let pmrows = map (fun (_,a,r,_) ->
      let theta = mapfilter (fun i -> if mem i patcols then fail() else el i actual, el i a)
                            (0--(n-1)) in
      let pats = map (fun i -> el i a) patcols in
      let vs = filter (fun v -> not (is_wildcard v)) (freesl pats) in
      let ren = map (fun v -> incr counter;
                       mk_var (fst (dest_var v) ^ "%pm" ^ string_of_int !counter, type_of v), v) vs in
      {pm_pats = map (vsubst ren) pats; pm_guard = None;
       pm_rhs = vsubst ren (vsubst theta r)}) rows in
  let rty = type_of (let _,_,r,_ = hd rows in r) in
  let dflt = tr_mk_arb rty in
  let scruts = map (fun i -> el i actual) patcols in
  let body = compile_rows actual scruts pmrows dflt in
  let def = end_itlist CONJ (map GEN_ALL cls) in
  let pre = pattern_complete def actual in
  let goal = list_mk_forall (actual, mk_imp (pre, mk_eq (list_mk_comb (f, actual), body))) in
  (* the case tree of compile_rows: case constants, and conditionals for   *)
  (* boolean literal patterns (bool_compare T F = ..)                        *)
  let rec go g =
    ((REWRITE_TAC [def] THEN CASE_REWRITE_TAC [] THEN NO_TAC) ORELSE
     (ASM_REWRITE_TAC [def] THEN NO_TAC) ORELSE
     (FIRST_X_ASSUM (MP_TAC o check (fun th -> is_disj (concl th) || is_exists (concl th) ||
                                                 is_eq (concl th))) THEN
      REWRITE_TAC [] THEN SIMP [] THEN NO_TAC) ORELSE
     (COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN go) ORELSE
     (TOP_CASE_TAC THEN go)) g in
  let th = prove (goal, REPEAT GEN_TAC THEN REWRITE_TAC [ml_PRECONDITION_def] THEN
                        DISCH_TAC THEN go) in
  (* complete patterns that ONELINE does not compile (literal patterns with *)
  (* a variable row, as TFL's literal_case): no ARB is reachable, as for   *)
  (* HOL4's single_line_def, which adds the precondition only when the     *)
  (* primitive definition has ARB                                           *)
  (* only with a catch-all row (all pattern columns variables): otherwise the  *)
  (* patterns leave cases open and MESON would search long in vain           *)
  let catch_all = exists (fun (_,a,_,_) -> forall (fun i -> is_var (el i a)) patcols) rows in
  (* boolean pattern columns (T and F literals): by case analysis *)
  let all_bool = forall (fun i -> type_of (el i actual) = bool_ty) patcols in
  let bool_vars = map (fun i -> el i actual) patcols in
  match (if catch_all then
           (try Some (prove (list_mk_forall (actual, rand pre),
                             REPEAT GEN_TAC THEN tr_quiet_tac (MESON_TAC [])))
            with Failure _ -> None)
         else if all_bool then
           (try Some (prove (list_mk_forall (actual, rand pre),
                             REPEAT GEN_TAC THEN MAP_EVERY BOOL_CASES_TAC bool_vars THEN
                             REWRITE_TAC [] THEN tr_quiet_tac (MESON_TAC [])))
            with Failure _ -> None)
         else
           (* boolean literals under constructors and other complete patterns *)
           let rec size t = if is_var t then 0 else
             1 + itlist (fun a n -> size a + n) (snd (strip_comb t)) 0 in
           let depth = min 12 (2 + itlist (fun (_,a,_,_) n ->
                                         max n (itlist (fun i m -> size (el i a) + m) patcols 0))
                                       rows 0) in
           (try Some (prove (list_mk_forall (actual, rand pre),
                             REPEAT GEN_TAC THEN tr_cover_tac [] depth))
            with Failure _ -> None)) with
    Some cov -> GENL actual (MP (SPECL actual th)
                               (EQ_MP (SYM (REWR_CONV ml_PRECONDITION_def pre)) (SPECL actual cov)))
  | None -> th;;

let tr_oneline f cls =
  let def = end_itlist CONJ (map GEN_ALL cls) in
  try ONELINE def with Failure _ -> tr_conditional_oneline f cls;;

(* structural induction for the first pattern argument of a definition by  *)
(* clauses (HOL4 get_induction_for_def's fallback from TypeBase)            *)
let tr_struct_ind def =
  let groups = tr_group_by_function def in
  if length groups <> 1 then failwith "tr_struct_ind: mutual" else
  let (f,cls) = hd groups in
  let args0 = snd (strip_comb (lhs (concl (hd cls)))) in
  let k = index true (map (fun a -> not (is_var a)) args0) in
  let ty = type_of (el k args0) in
  let ind =
    if ty = tr_num_ty then num_INDUCTION else
    let (_,ith,_) = assoc (fst (dest_type ty)) !inductive_type_store in
    let p = fst (dest_forall (concl ith)) in
    INST_TYPE (type_match (fst (dest_fun_ty (type_of p))) ty []) ith in
  let pv0,body = dest_forall (concl ind) in
  if length (conjuncts (rand body)) <> 1 then failwith "tr_struct_ind: nested type" else
  let avoid = frees (concl (end_itlist CONJ cls)) in
  let vs = map2 (fun a i -> variant avoid (mk_var ("v" ^ string_of_int (i+1), type_of a)))
                args0 (0--(length args0 - 1)) in
  let pv = mk_var ("P", itlist (fun v t -> mk_fun_ty (type_of v) t) vs bool_ty) in
  let vk = el k vs in
  let others = filter (fun v -> v <> vk) vs in
  let step = mk_abs (vk, list_mk_forall (others, list_mk_comb (pv, vs))) in
  let ind' = CONV_RULE (DEPTH_CONV BETA_CONV) (ISPEC step ind) in
  let goal2 = list_mk_forall (vs, list_mk_comb (pv, vs)) in
  let goal1 = snd (dest_imp (concl ind')) in
  let lemma = tr_auto_prove "get_induction_for" (mk_imp (goal1, goal2),
                REPEAT STRIP_TAC THEN ASM_REWRITE_TAC []) in
  GEN pv (DISCH (fst (dest_imp (concl ind'))) (MP lemma (UNDISCH ind')));;

(* unit patterns (HOL4 one_line_ify: case v of () => e): a clause          *)
(* f .. one .. = e becomes f .. v .. = one_CASE v e, one one_CASE for each *)
(* unit argument, the first one outermost                                  *)
let tr_unit_pat_rule c =
  let l,r = dest_eq (concl c) in
  let g,args = strip_comb l in
  if not (mem tr_one_tm args) then c else
  let avoid = ref (frees (concl c)) in
  let args' = map (fun a ->
      if a <> tr_one_tm then a else
      let v = variant !avoid (mk_var ("v", tr_one_ty)) in (avoid := v :: !avoid; v)) args in
  let us = filter (fun a -> not (mem a args)) args' in
  let one_case = inst [type_of r, aty] tr_one_case_info.ci_case in
  let r' = itlist (fun u t -> list_mk_comb (one_case, [u; t])) us r in
  let l' = list_mk_comb (g, args') in
  let th1 = SUBS_CONV (map (fun u -> ISPEC u one) us) l' in
  let rec strip k = if k = 0 then ALL_CONV else REWR_CONV one_case_def THENC strip (k-1) in
  TRANS th1 (TRANS c (SYM (strip (length us) r')));;

let mutual_to_single_line_def def =
  let groups = tr_group_by_function def in
  let groups = map (fun (f,cls) -> (f, map tr_unit_pat_rule cls)) groups in
  let defs = map (fun (f,cls) -> let th = SPEC_ALL (tr_oneline f cls) in
                                  if is_imp (concl th) then UNDISCH th else th) groups in
  let ind = if is_rec_def def then
              let th = find_ind_thm def in
              Some (if concl th = tr_T_tm then (try tr_struct_ind def with Failure _ -> th) else th)
            else None in
  (defs, ind);;

(* HOL4 remove_pair_abs.  Its first step, a pair argument f (x,y) = ..     *)
(* becoming f v = case v of (x,y) => .., is done by the one-line form of    *)
(* the clauses.  Its second step rewrites the right-hand side with          *)
(* UNCURRY_SIMP and beta: HOL4's paired abstraction \(x,y). b is            *)
(* UNCURRY (\x y. b), which becomes \v. case v of (x,y) => b.  HOL Light's  *)
(* paired abstraction is a GABS, first written as UNCURRY (\x y. b)         *)
(* (nested patterns: nested UNCURRY) by tr_GABS_UNCURRY_CONV                *)
let tr_GABS_UNCURRY_CONV =
  let unc_tm = `UNCURRY:(A->B->C)->A#B->C` in
  let rec tuple_vars tm =
    if is_var tm then [tm] else
    let l,r = dest_pair tm in tuple_vars l @ tuple_vars r in
  let rec mk_uncurried p b =
    if is_var p then mk_abs (p,b) else
    let s,t = dest_pair p in
    mk_icomb (unc_tm, mk_uncurried s (mk_uncurried t b)) in
  (* |- w p = b for w = mk_uncurried p b *)
  let rec uncurried_conv p w =
    if is_var p then BETA_CONV (mk_comb (w,p)) else
    let s,t = dest_pair p in
    let f = rand w in
    let th1 = ISPECL [f; s; t] UNCURRY_DEF in
    let th2 = uncurried_conv s f in
    TRANS th1 (TRANS (AP_THM th2 t) (uncurried_conv t (rand (concl th2)))) in
  (* the goal !z. P z becomes P p *)
  let rec pat_gen_tac p =
    if is_var p then X_GEN_TAC p else
    let s,t = dest_pair p in
    GEN_REWRITE_TAC I [FORALL_PAIR_THM] THEN pat_gen_tac s THEN pat_gen_tac t in
  fun tm ->
    if is_abs tm || not (is_gabs tm) then failwith "tr_GABS_UNCURRY_CONV" else
    let p,b = dest_gabs tm in
    let vs = try tuple_vars p with Failure _ -> failwith "tr_GABS_UNCURRY_CONV" in
    if length (setify vs) <> length vs then failwith "tr_GABS_UNCURRY_CONV" else
    let w = mk_uncurried p b in
    let pth = TRANS (GEN_BETA_CONV (mk_comb (tm,p))) (SYM (uncurried_conv p w)) in
    prove (mk_eq (tm,w), GEN_REWRITE_TAC I [FUN_EQ_THM] THEN pat_gen_tac p THEN
                         ACCEPT_TAC pth);;

let tr_pair_abs_conv =
  TOP_DEPTH_CONV tr_GABS_UNCURRY_CONV THENC
  TOP_DEPTH_CONV (GEN_REWRITE_CONV I [UNCURRY_SIMP] ORELSEC BETA_CONV);;

let remove_pair_abs def =
  CONV_RULE (RAND_CONV tr_pair_abs_conv) (SPEC_ALL def);;

let force_eqns def =
  let f th = if is_eq (concl (SPEC_ALL th)) then th else
               try GEN_ALL (MATCH_MP IMP_EQ_F (SPEC_ALL th))
               with Failure _ -> GEN_ALL (MATCH_MP ml_IMP_EQ_T (SPEC_ALL th)) in
  end_itlist CONJ (map f (CONJUNCTS (SPEC_ALL def)));;

(* ------------------------------------------------------------------------- *)
(* Built-in operations (HOL4 builtin_terops, builtin_binops, builtin_monops) *)
(* ------------------------------------------------------------------------- *)

let tr_op_of_lemma k th =
  let c = concl (tr_UNDISCH_ALL (SPEC_ALL th)) in
  let t = rand (rand c) in
  let rec go k t = if k = 0 then t else go (k-1) (rator t) in
  go k t;;

let builtin_terops = ref ([] : (term * thm) list);;
let builtin_binops = ref ([] : (term * thm) list);;
let builtin_monops = ref ([] : (term * thm) list);;
let builtin_hol_string_binops = ref ([] : (term * thm) list);;
let builtin_hol_string_monops = ref ([] : (term * thm) list);;
let builtin_sub_check = ref ([] : (term * thm) list);;

let tr_set_builtins tbl k ths = tbl := map (fun th -> (tr_op_of_lemma k th, th)) ths;;

let () =
  tr_set_builtins builtin_terops 3 [ml_Eval_substring; Eval_FLOAT_FMA];
  tr_set_builtins builtin_binops 2
    [Eval_NUM_ADD; Eval_NUM_SUB; Eval_NUM_SUB_check; Eval_NUM_MULT; Eval_NUM_DIV; Eval_NUM_MOD;
     Eval_NUM_LESS; Eval_NUM_LESS_EQ; Eval_NUM_GREATER; Eval_NUM_GREATER_EQ;
     Eval_NUM_EQ; Eval_BOOL_EQ;
     ml_Eval_char_lt; ml_Eval_char_le; ml_Eval_char_gt; ml_Eval_char_ge; ml_Eval_char_eq;
     ml_Eval_str_eq;
     Eval_INT_ADD; Eval_INT_SUB; Eval_INT_MULT; Eval_INT_DIV; Eval_INT_MOD;
     Eval_INT_EQ; Eval_INT_LESS; Eval_INT_LESS_EQ; Eval_INT_GREATER; Eval_INT_GREATER_EQ;
     Eval_FLOAT_ADD; Eval_FLOAT_SUB; Eval_FLOAT_MULT; Eval_FLOAT_DIV;
     Eval_FLOAT_LESS; Eval_FLOAT_LESS_EQ; Eval_FLOAT_GREATER; Eval_FLOAT_GREATER_EQ;
     Eval_FLOAT_EQ;
     ml_Eval_force_gc_to_run; ml_Eval_force_unit_type; ml_Eval_strsub; Eval_ListAppend;
     ml_Eval_mlstring_lt; ml_Eval_mlstring_le; ml_Eval_mlstring_gt; ml_Eval_mlstring_ge;
     ml_Eval_fast_lt; ml_Eval_fast_le; ml_Eval_fast_gt; ml_Eval_fast_ge;
     ml_Eval_sub; ml_Eval_sub_unsafe; Eval_Implies; ml_Eval_pure_seq];
  tr_set_builtins builtin_sub_check 2 [Eval_NUM_SUB_check'];
  tr_set_builtins builtin_monops 1
    [ml_Eval_implode; ml_Eval_explode; ml_Eval_strlen; ml_Eval_concat; Eval_Bool_Not;
     ml_Eval_int_negate; ml_Eval_length; ml_Eval_vector; ml_Eval_int_of_num;
     ml_Eval_num_of_int; Eval_FLOAT_ABS; Eval_FLOAT_SQRT; Eval_FLOAT_NEG;
     Eval_FP_fromWord; Eval_FP_toWord; ml_Eval_empty_ffi;
     ml_Eval_force_out_of_memory_error; ml_Eval_char_to_word8; ml_Eval_word8_to_char;
     Eval_Chr; Eval_Ord];
  tr_set_builtins builtin_hol_string_binops 2
    [Eval_HOL_STRING_EL; Eval_HOL_STRING_CONS; Eval_HOL_STRING_APPEND];
  tr_set_builtins builtin_hol_string_monops 1
    [Eval_HOL_STRING_LENGTH; Eval_HOL_STRING_IMPLODE; Eval_HOL_STRING_EXPLODE;
     Eval_HOL_STRING_HD; Eval_HOL_STRING_FLAT; ml_Eval_implode_nop; Eval_HOL_STRING_explode];;

let tr_dest_builtin tbl k tm =
  let rec strip k tm acc = if k = 0 then (tm, acc) else
    let f,x = dest_comb tm in strip (k-1) f (x :: acc) in
  let p,args = strip k tm [] in
  let (x,th) = find (fun (x,_) -> can (term_match [] x) p) tbl in
  let (_,ss,ii) = term_match [] x p in
  (p, args, INST ss (INST_TYPE ii th));;

let dest_builtin_terop tm = tr_dest_builtin !builtin_terops 3 tm;;
let dest_builtin_binop tm =
  tr_dest_builtin ((if sub_check () then !builtin_sub_check else []) @
                   (if use_hol_string_type () then !builtin_hol_string_binops else []) @
                   !builtin_binops) 2 tm;;
let dest_builtin_monop tm =
  tr_dest_builtin ((if use_hol_string_type () then !builtin_hol_string_monops else []) @
                   !builtin_monops) 1 tm;;

(* HOL4 AUTO_ETA_EXPAND_CONV: partially applied constructors, built-in     *)
(* operators and = are eta-expanded; an operator is the lemma's constant   *)
(* exactly (HOL4 tmem), so instances of polymorphic ones (pure_seq at a    *)
(* monad type, APPEND at :num list) are left alone                          *)
let AUTO_ETA_EXPAND_CONV =
  let must_eta_expand_ops () =
    map fst (!builtin_terops @ !builtin_binops @ !builtin_sub_check @ !builtin_monops @
             !builtin_hol_string_binops @ !builtin_hol_string_monops) in
  let is_constructor tm =
    is_const tm &&
    (let n = fst (dest_const tm) in
     Hashtbl.mem (snd (kit_case_tables ())) n) in
  let must_eta_expand tm =
    is_constructor tm ||
    exists (fun p -> aconv p tm) (must_eta_expand_ops ()) ||
    (is_const tm && fst (dest_const tm) = "=") in
  let full_arg_num tm = length (fst (splitlist dest_fun_ty (type_of tm))) in
  let rec FULL_ETA_CONV tm =
    try let v = genvar (fst (dest_fun_ty (type_of tm))) in
        let lemma = ETA_CONV (mk_abs (v, mk_comb (tm, v))) in
        (K (SYM lemma) THENC ABS_CONV FULL_ETA_CONV) tm
    with Failure _ -> ALL_CONV tm in
  let rec aux n tm =
    if is_const tm then
      (if n < full_arg_num tm && must_eta_expand tm then FULL_ETA_CONV tm else ALL_CONV tm)
    else if is_comb tm then (RATOR_CONV (aux (n+1)) THENC RAND_CONV (aux 0)) tm
    else if is_abs tm then ABS_CONV (aux 0) tm
    else if is_var tm then ALL_CONV tm
    else failwith "AUTO_ETA_EXPAND_CONV" in
  aux 0;;

let use_mem_intro = ref false;;

(* the preprocessor: (is_rec, one equation per function, induction) *)
(* type variables with names that are no identifiers (HOL Light's invented  *)
(* ?N, from definitions parsed without type annotations, e.g. ITER) become    *)
(* A, B, ... (HOL4 avoid_v_subst renames 'v likewise)                        *)
let tr_tidy_tyvars th =
  let tvs = itlist (fun t l -> union (type_vars_in_term t) l) (concl th :: hyp th) [] in
  let bad = filter (fun tv -> let n = dest_vartype tv in
                      n = "" || n = "V" || not (n.[0] >= 'A' && n.[0] <= 'Z')) tvs in
  if bad = [] then th else
  let used = ref (subtract tvs bad) in
  let pick () =
    let cands = ["A";"B";"C";"D";"E";"F";"G";"H";"J";"K";"L";"M";"N";"P";"Q";"S";"T";"U"] in
    let rec go l = match l with
        [] -> failwith "tr_tidy_tyvars"
      | c::rest -> let tv = mk_vartype c in
                   if mem tv !used then go rest else (used := tv :: !used; tv) in
    go cands in
  INST_TYPE (map (fun tv -> (pick (), tv)) bad) th;;

(* HOL4 PURE_ONCE_REWRITE_RULE [GSYM TRUE_def, GSYM FALSE_def]: T and F    *)
(* become TRUE and FALSE, except inside HOL Light's character literals      *)
(* ASCII b0 .. b7 (HOL4's characters are CHR n)                              *)
let tr_true_false_conv =
  let tth = SYM TRUE_def and fth = SYM FALSE_def in
  let rec conv tm =
    if tm = tr_T_tm then tth else
    if tm = tr_F_tm then fth else
    match tm with
      Comb(f,x) ->
        let h = fst (strip_comb f) in
        if is_const h && fst (dest_const h) = "ASCII" then REFL tm
        else MK_COMB (conv f, conv x)
    | Abs(v,b) -> ABS v (conv b)
    | _ -> REFL tm in
  conv;;

(* TFL's stored definitions have the recursive calls eta-expanded: a      *)
(* partial application of a function being defined, f a1 .. ak with k less *)
(* than f's arity, becomes \a. f a1 .. ak a (HOL4's holKernel type_subst:  *)
(* MAP (\a. type_subst i a) args), so that the recursion pattern sees full *)
(* calls and MAP (\a. ..) gets HOL4's MEM context.  The definition is      *)
(* unchanged when there is no such application                             *)
let tr_eta_defined_rule def =
  let cls = map SPEC_ALL (CONJUNCTS (SPEC_ALL def)) in
  let ar = map (fun c -> let h,args = strip_comb (lhs (concl c)) in
                         ((if is_const h then fst (dest_const h) else ""), length args)) cls in
  let arity_of h =
    if is_const h then (try Some (assoc (fst (dest_const h)) ar) with Failure _ -> None)
    else None in
  let rec expand k tm =
    if k = 0 then REFL tm else
    let ty = fst (dest_fun_ty (type_of tm)) in
    let y = variant (frees tm) (mk_var ("a", ty)) in
    let th1 = SYM (ETA_CONV (mk_abs (y, mk_comb (tm, y)))) in
    TRANS th1 (ABS_CONV (expand (k-1)) (rhs (concl th1))) in
  let rec conv tm =
    match tm with
      Var(_,_) -> REFL tm
    | Abs(v,b) -> ABS v (conv b)
    | _ ->
      let h,args = strip_comb tm in
      let th_h = (match h with Abs(_,_) -> conv h | _ -> REFL h) in
      let th = rev_itlist (fun a th -> MK_COMB (th, conv a)) args th_h in
      (match arity_of h with
         Some n when length args < n -> TRANS th (expand (n - length args) (rand (concl th)))
       | _ -> th) in
  let cls' = map (fun c -> CONV_RULE (RAND_CONV conv) c) cls in
  if forall2 (fun c c' -> concl c = concl c') cls cls' then def
  else end_itlist CONJ (map GEN_ALL cls');;

(* the kit's induction theorems (cake_ind) can have a recursive call under  *)
(* a condition c and again under ~c, where TFL's (HOL4's) has it once: a     *)
(* let-bound call used in both branches of an if (holKernel vsubst_aux).     *)
(* Such pairs !vs. A /\ c ==> Q, !vs. A /\ ~c ==> Q of the step's            *)
(* hypotheses become !vs. A ==> Q (the theorem is proved from the original) *)
let tr_merge_ind_cases ith =
  try
    let p,bod = dest_forall (concl ith) in
    let step,cpart = dest_imp bod in
    let xs,sb = strip_forall step in
    let hyps_tm,pc = dest_imp sb in
    let dest_h h = let vs,b = strip_forall h in
                   if is_imp b then (vs, conjuncts (fst (dest_imp b)), snd (dest_imp b))
                   else (vs, [], b) in
    let hs = map dest_h (conjuncts hyps_tm) in
    let rec remove_one t l = match l with
        [] -> failwith "remove_one"
      | h::r -> if aconv h t then r else h :: remove_one t r in
    let same_ms l1 l2 = length l1 = length l2 &&
      (try itlist remove_one l1 l2 = [] with Failure _ -> false) in
    let neg_of c = if is_neg c then rand c else mk_neg c in
    let merge (vs1,cs1,q1) (vs2,cs2,q2) =
      if vs1 <> vs2 || not (aconv q1 q2) then failwith "merge" else
      let c = find (fun c -> exists (aconv (neg_of c)) cs2 &&
                             same_ms (remove_one c cs1) (remove_one (neg_of c) cs2)) cs1 in
      (vs1, remove_one c cs1, q1) in
    let rec merge_once l = match l with
        [] -> failwith "merge_once"
      | h::t ->
          (try let rec go acc r = match r with
                   [] -> failwith ""
                 | h2::r2 -> (try merge h h2 :: (rev acc @ r2) with Failure _ -> go (h2::acc) r2) in
               go [] t
           with Failure _ -> h :: merge_once t) in
    let hs' = repeat merge_once hs in
    if length hs' = length hs then ith else
    let mk_h (vs,cs,q) = list_mk_forall (vs, if cs = [] then q else mk_imp (list_mk_conj cs, q)) in
    let step' = list_mk_forall (xs, mk_imp (list_mk_conj (map mk_h hs'), pc)) in
    let goal = mk_forall (p, mk_imp (step', cpart)) in
    prove (goal,
      GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC ith THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN POP_ASSUM STRIP_ASSUME_TAC THEN REPEAT CONJ_TAC THEN
      (FIRST_ASSUM ACCEPT_TAC ORELSE tr_quiet_tac (ASM_MESON_TAC [])))
  with Failure _ -> ith;;

let preprocess_def def =
  let def = tr_tidy_tyvars def in
  let def = force_eqns def in
  let def = tr_eta_defined_rule def in
  let is_rec = is_rec_def def in
  let (defs,ind) = mutual_to_single_line_def def in
  let rephrase_def def =
    let def = CONV_RULE (RAND_CONV tr_true_false_conv) (SPEC_ALL def) in
    let def = CONV_RULE (RAND_CONV tr_LET_END_CONV) def in
    let def = remove_pair_abs def in
    let def = SPEC_ALL (rename_bound_vars_rule " variable " (GEN_ALL def)) in
    let def = CONV_RULE (DEPTH_CONV split_let_and_conv) def in
    let def = if is_const (lhs (concl (SPEC_ALL def)))
              then SPEC_ALL (ONCE_REWRITE_RULE [FUN_EQ_THM] def) else def in
    let def = PURE_REWRITE_RULE ([ADD1; num_case_thm] @ get_preprocessor_rws ()) def in
    let def = CONV_RULE (AUTO_ETA_EXPAND_CONV THENC REDEPTH_CONV BETA_CONV) def in
    let def = SPEC_ALL (rename_bound_vars_rule "v" (GEN_ALL def)) in
    def in
  let defs = map rephrase_def defs in
  (* the induction theorem gets the definition's paired-abstraction       *)
  (* rewriting too (remove_pair_abs: GABS as \v. case v of (x,y) => ..),   *)
  (* so that its recursive calls match the definition's                    *)
  let rephrase_ind th =
    PURE_REWRITE_RULE ([ADD1; num_case_thm] @ get_preprocessor_rws ())
      (tr_merge_ind_cases (CONV_RULE tr_pair_abs_conv th)) in
  let ind = match ind with Some ind -> Some (rephrase_ind ind) | None -> None in
  (* HOL4: MEM as the basis's MEMBER when use_mem_intro is set *)
  let mem_intro_rule = PURE_REWRITE_RULE [MEMBER_INTRO] in
  let (defs,ind) =
    if not !use_mem_intro then (defs,ind) else
    (map mem_intro_rule defs,
     match ind with Some ind -> Some (mem_intro_rule ind) | None -> None) in
  (is_rec, defs, ind);;

(* ------------------------------------------------------------------------- *)
(* Parameters (HOL4 inst_Eval_env, FORCE_GEN, apply_Eval_Fun)                *)
(* ------------------------------------------------------------------------- *)

let inst_Eval_env v th =
  let name = fst (dest_var v) in
  let str = mk_mlstring name in
  let inv = get_type_inv (type_of v) in
  let assum = mk_Eval (tr_env, mk_Var (mk_Short str), mk_comb (inv, v)) in
  let new_env = mk_write (str, tr_v_var, tr_env) in
  let c = tr_env_hyp_conv [] in
  let c1 = RATOR_CONV (RAND_CONV (REWRITE_CONV [ASSUME assum])) in
  let th = DISCH assum (CONV_RULE c1 (tr_D th)) in
  let th = INST [new_env, tr_env] th in
  let th = PURE_REWRITE_RULE [lookup_cons_write; lookup_var_write; nsLookup_write] th in
  let th = CONV_RULE (RATOR_CONV (RAND_CONV c) THENC
                      RAND_CONV (RATOR_CONV (RAND_CONV c))) th in
  let new_assum = fst (dest_imp (concl th)) in
  let th1 = tr_UNDISCH_ALL th in
  let th1 = CONV_RULE (RAND_CONV (RAND_CONV (tr_UNBETA_CONV v))) th1 in
  DISCH new_assum th1;;

let FORCE_GEN v th1 =
  try GEN v th1 with Failure _ ->
    let hs = hyp th1 in
    let xs = filter (fun tm -> vfree_in v tm) hs in
    let th2 = DISCH tr_T_tm th1 in
    let th3 = itlist (fun tm th -> ONCE_REWRITE_RULE [IMP_IMP] (DISCH tm th)) xs th2 in
    let th4 = GEN v th3 in
    let th4 = MATCH_MP PUSH_FORALL_INTO_IMP th4 in
    UNDISCH th4;;

let tr_apply_Eval_Fun_fail = ref (`T`, TRUTH, true);;

(* HOL Light's MATCH_MP matches a x v in Eval_Fun higher order and gives the *)
(* invariant \x v. LIST_TYPE a x v where HOL4's first-order MATCH_MP gives    *)
(* LIST_TYPE a: eta-reduce the invariant (not the HOL function)              *)
let tr_eta_inv_rule th = CONV_RULE (RAND_CONV (RATOR_CONV (DEPTH_CONV ETA_CONV))) th;;

let apply_Eval_Fun v th fix =
  try
    let th1 = inst_Eval_env v th in
    if fix then tr_eta_inv_rule (MATCH_MP Eval_Fun_Eq (GEN tr_v_var th1))
    else tr_eta_inv_rule (MATCH_MP Eval_Fun (GEN tr_v_var (FORCE_GEN v th1)))
  with Failure s -> (tr_apply_Eval_Fun_fail := (v, th, fix);
                     failwith ("apply_Eval_Fun: " ^ s));;

(* ------------------------------------------------------------------------- *)
(* Cleaning the hypotheses (HOL4 move_Eval_conv, clean_assumptions)         *)
(* ------------------------------------------------------------------------- *)

let move_Eval_conv tm =
  let (_,tm1) = strip_forall tm in
  let tm2 = try snd (dest_imp tm1) with Failure _ -> tm1 in
  if is_Eval tm2 then MATCH_MP ml_IMP_EQ_T (ASSUME tm) else failwith "move_Eval_conv";;

let tr_is_lookup_assum tm =
  is_eq tm &&
  (let l = lhs tm in
   is_lookup_cons l ||
   (tr_head_is "nsLookup" l && length (tr_dest_args l) = 2));;

let clean_assumptions_aux be_quiet th =
  let lookup_assums = tr_find_terms tr_is_lookup_assum (concl th) in
  let lemmas = mapfilter (fun t -> let th = prove_lookup_cons_eq t in
                            if is_const (rand (concl th)) then th else fail()) lookup_assums in
  (match (try Some (find (fun l -> rand (concl l) = tr_F_tm) lemmas) with Failure _ -> None) with
     None -> ()
   | Some t -> ((if be_quiet then () else
                 (Format.print_string "clean_assumptions: false assumption\n\n";
                  print_thm t; Format.print_string "\n\n"));
                failwith ("clean_assumptions: false " ^ string_of_thm t)));
  let th = REWRITE_RULE lemmas th in
  (* lift EqualityType, lookup_cons, nsLookup and Eval assumptions out *)
  let eq_assums = tr_find_terms is_EqualityType (concl th) in
  let th = REWRITE_RULE (map ASSUME eq_assums) th in
  let lc_assums = tr_find_terms (fun t -> is_eq t && is_lookup_cons (lhs t)) (concl th) in
  let th = REWRITE_RULE (map ASSUME lc_assums) th in
  let ns_assums = tr_find_terms (fun t -> is_eq t && tr_head_is "nsLookup" (lhs t) &&
                                         length (tr_dest_args (lhs t)) = 2) (concl th) in
  let th = REWRITE_RULE (map ASSUME ns_assums) th in
  let th1 = REWRITE_RULE [GSYM ml_PreImpEval_def] th in
  let th2 = try CONV_RULE (LAND_CONV (ONCE_DEPTH_CONV move_Eval_conv)) th1
            with Failure _ -> th1 in
  REWRITE_RULE [ml_PreImpEval_def] th2;;

let clean_assumptions th = clean_assumptions_aux false th;;
let clean_assumptions_quietly th = clean_assumptions_aux true th;;

let get_pre_var lhs fname =
  let args = snd (strip_comb lhs) in
  let ty = itlist (fun x ty -> mk_fun_ty (type_of x) ty) args bool_ty in
  list_mk_comb (mk_var (fname ^ "_side", ty), args);;

let tr_rec_patterns = ref ([] : (term * string * string) list);;
let install_rec_pattern lhs fname ml_fname =
  tr_rec_patterns := (lhs,fname,ml_fname) :: !tr_rec_patterns;;
let uninstall_rec_patterns () = tr_rec_patterns := [];;
let match_rec_pattern tm =
  let (lhs,fname,ml_fname) = find (fun (pat,_,_) -> can (term_match [] pat) tm) !tr_rec_patterns in
  (lhs, ml_fname, get_pre_var lhs fname);;
let get_rec_patterns () = !tr_rec_patterns;;

let tr_check_inv_fail = ref `T`;;

let check_inv name tm result =
  let tm2 = rand (rand (concl result)) in
  if aconv tm2 tm then result else
  (tr_check_inv_fail := tm;
   Format.print_string ("\n\nhol2deep failed at '" ^ name ^ "'\n\ntarget:\n\n");
   print_term tm; Format.print_string "\n\nbut derived:\n\n"; print_term tm2;
   Format.print_string "\n\n\n"; failwith "checkinv");;

let MY_MATCH_MP th1 th2 =
  let tm1 = fst (dest_imp (concl th1)) in
  let tm2 = concl th2 in
  let (_,s,i) = term_match [] tm1 tm2 in
  MP (INST s (INST_TYPE i th1)) th2;;

(* Eq b x := b in a term, for matching (HOL4 rm_fix by a mk_thm rewrite) *)
let rec rm_fix tm =
  if is_Eq tm then fst (dest_Eq tm) else
  match tm with
    Comb(f,x) -> mk_comb (rm_fix f, rm_fix x)
  | Abs(v,b) -> mk_abs (v, rm_fix b)
  | _ -> tm;;

let force_remove_fix thx =
  let xs = map (fun t -> snd (dest_Eq t)) (tr_find_terms is_Eq (concl thx)) in
  let s th = REWRITE_RULE [Eval_FUN_FORALL_EQ; FUN_QUANT_SIMP] th in
  itlist (fun x th -> s (FORCE_GEN x th)) xs thx;;

(* ------------------------------------------------------------------------- *)
(* hol2deep: |- ml_Eval env exp (INV tm), with hypotheses (HOL4 TL:3444)     *)
(* ------------------------------------------------------------------------- *)

let tr_map_pattern = `MAP:(A->B)->(A)list->(B)list`;;
let tr_every_pattern = `ALL:(A->bool)->(A)list->bool`;;
let tr_exists_pattern = `EX:(A->bool)->(A)list->bool`;;


let tr_is_int_literal tm = type_of tm = tr_int_ty && can dest_intconst tm;;

let tr_is_char_literal tm = type_of tm = tr_char_ty && can dest_char tm;;

(* HOL4's character literals as the port writes them (hol4/string4.ml):    *)
(* CHR n, n a numeral below 256, becomes the literal ASCII b7 .. b0, and   *)
(* is translated as Lit (Char c) (HOL4 Eval_Val_CHAR), not as Char.chr n   *)
let tr_is_CHR_numeral tm =
  is_comb tm && tr_is_const_named "CHR" (rator tm) && is_numeral (rand tm) &&
  (try dest_small_numeral (rand tm) < 256 with Failure _ -> false);;

let tr_CHR_literal_conv tm =
  if tr_is_CHR_numeral tm then (REWR_CONV CHR_DEF THENC NUM_REDUCE_CONV) tm
  else failwith "tr_CHR_literal_conv";;

let tr_is_hol_string_literal tm = type_of tm = tr_string_ty && can dest_string tm;;

let tr_bind_exn = `Raise (Con (SOME (Short (implode "Bind"))) [])`;;

let tr_is_let tm =
  match strip_comb tm with
    (Const("LET",_),[f;_]) -> is_abs f
  | _ -> false;;

(* terms of hol2deep, parsed once (a quotation in a function body is parsed *)
(* at every call)                                                           *)
let tr_PRECONDITION_F_tm = mk_PRECONDITION tr_F_tm;;

(* ------------------------------------------------------------------------- *)
(* Words, floats and HOL strings in hol2deep (HOL4 WORD_CONV, the word       *)
(* lemmas Eval_n2w .. Eval_word_ror, is_word_literal, is_float_literal)       *)
(* ------------------------------------------------------------------------- *)


(* a word lemma instantiated at numeral types: its side conditions about    *)
(* dimindex proved, the code of its conclusion evaluated                    *)
let rec tr_word_simp_lemma th =
  let c = concl th in
  if is_forall c then tr_word_simp_lemma (SPEC_ALL th) else
  if is_imp c then
    let a = lhand c in
    if forall is_Eval (conjuncts a) then DISCH a (tr_word_simp_lemma (UNDISCH th)) else
    let eq = tr_WORD_CONV a in
    if rand (concl eq) = tr_T_tm then tr_word_simp_lemma (MP th (EQ_MP (SYM eq) TRUTH))
    else failwith ("tr_word_simp_lemma: side condition " ^ string_of_term (rand (concl eq)))
  else CONV_RULE (RATOR_CONV (RAND_CONV tr_WORD_CONV)) th;;

let tr_word_dim_ty ty = hd (snd (dest_type ty));;

(* word n with a numeral n (HOL4 n2w literal) *)
let tr_is_word_literal tm =
  tr_is_word_type (type_of tm) && tr_head_is "word" tm && is_numeral (rand tm);;

(* float_REC s e m with word literals, of type (52,11)float *)
let tr_is_float_literal tm =
  type_of tm = tr_float64_ty && tr_head_is "float_REC" tm &&
  forall tr_is_word_literal (snd (strip_comb tm));;

(* word binary operations and comparisons (HOL4 dest_word_binop): HOL Light *)
(* word_add .. word_xor, word_ult (HOL4 <+), word_ule, word_ugt, word_uge  *)
let tr_word_binops =
  ["word_and", ml_Eval_word_and; "word_add", ml_Eval_word_add;
   "word_or", ml_Eval_word_or; "word_xor", ml_Eval_word_xor;
   "word_sub", ml_Eval_word_sub; "word_ult", ml_Eval_word_lo;
   "word_ule", ml_Eval_word_ls; "word_ugt", ml_Eval_word_hi;
   "word_uge", ml_Eval_word_hs];;

let tr_dest_word_binop tm =
  if is_eq tm then ml_Eval_word_eq else
  let h = fst (strip_comb tm) in
  if is_const h && length (tr_dest_args tm) = 2 then
    (try assoc (fst (dest_const h)) tr_word_binops
     with Failure _ -> failwith "not a word binop")
  else failwith "not a word binop";;

(* word shifts by a numeral (HOL4 dest_word_shift): word_shl (HOL4 <<),    *)
(* word_ushr (>>>), word_ishr (>>), word_ror (#>>)                          *)
let tr_word_shifts =
  ["word_shl", ml_Eval_word_lsl; "word_ushr", ml_Eval_word_lsr;
   "word_ishr", ml_Eval_word_asr; "word_ror", ml_Eval_word_ror];;

let tr_dest_word_shift tm =
  let h = fst (strip_comb tm) in
  if is_const h && length (tr_dest_args tm) = 2 then
    (try assoc (fst (dest_const h)) tr_word_shifts
     with Failure _ -> failwith "not a word shift")
  else failwith "not a word shift";;

let tr_float_lit_conv =
  REWR_CONV float_to_fp64_def THENC PURE_REWRITE_CONV [float_accessors] THENC
  WORD_REDUCE_CONV;;

(* int_of_num o f and f o int_of_num (HOL4 int_of_num_o_pat, o_int_of_num_pat) *)
let tr_is_o_app tm =
  is_comb tm && is_comb (rator tm) && tr_is_const_named "o" (rator (rator tm));;

let rec hol2deep tm =
  (* variables *)
  if is_var tm then
    let (name,ty) = dest_var tm in
    let inv = get_type_inv ty in
    let str = mk_mlstring name in
    let result = ASSUME (mk_Eval (tr_env, mk_Var (mk_Short str), mk_comb (inv, tm))) in
    check_inv "var" tm result else
  (* constants *)
  if tm = tr_one_tm then tr_ISPECL_NAMED ["env", tr_env] Eval_Val_UNIT else
  if is_numeral tm && type_of tm = tr_num_ty then
    tr_ISPECL_NAMED ["env", tr_env; "n", tm] Eval_Val_NUM else
  if tr_is_int_literal tm then tr_ISPECL_NAMED ["env", tr_env; "n", tm] Eval_Val_INT else
  if tr_is_word_literal tm && word_ty_ok (type_of tm) then
    let dim = tr_word_dim_ty (type_of tm) in
    let th = tr_word_simp_lemma (SPEC tm (INST_TYPE [dim, aty] Eval_Val_WORD)) in
    check_inv "word_literal" tm th else
  if tr_is_char_literal tm then tr_ISPECL_NAMED ["env", tr_env; "c", tm] Eval_Val_CHAR else
  if tr_is_CHR_numeral tm then
    let th = tr_CHR_literal_conv tm in
    let th1 = tr_ISPECL_NAMED ["env", tr_env; "c", rand (concl th)] Eval_Val_CHAR in
    check_inv "chr_literal" tm (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (SYM th)))) th1) else
  if tr_is_float_literal tm then
    let th0 = SPEC tm Eval_Val_FLOAT64 in
    CONV_RULE (RATOR_CONV (RAND_CONV (RAND_CONV (RAND_CONV tr_float_lit_conv)))) th0 else
  if is_mlstring_literal tm then tr_ISPECL_NAMED ["env", tr_env; "s", tm] Eval_Val_STRING else
  if use_hol_string_type () && type_of tm = tr_string_ty && can dest_string tm then
    SPEC tm Eval_HOL_STRING_LITERAL else
  if tm = tr_T_tm then tr_ISPECL_NAMED ["env", tr_env] Eval_Val_BOOL_T else
  if tm = tr_F_tm then tr_ISPECL_NAMED ["env", tr_env] Eval_Val_BOOL_F else
  if tm = tr_TRUE_tm then tr_ISPECL_NAMED ["env", tr_env] Eval_Val_BOOL_TRUE else
  if tm = tr_FALSE_tm then tr_ISPECL_NAMED ["env", tr_env] Eval_Val_BOOL_FALSE else
  (* datatype constructors and case expressions *)
  try inst_cons_thm tm hol2deep with Failure _ ->
  try inst_case_thm tm hol2deep with Failure _ ->
  (* recursive calls *)
  if can match_rec_pattern tm then
    let (lhs,fname,pre_var) = match_rec_pattern tm in
    let xs = rev (snd (strip_comb tm)) in
    let f = fst (strip_comb lhs) in
    let str = mk_mlstring fname in
    let mk_fix tm = mk_Eq (get_type_inv (type_of tm), tm) in
    let inv = itlist (fun x res -> mk_Arrow (mk_fix x, res)) (rev xs)
                     (get_type_inv (type_of tm)) in
    let (_,ss,_) = term_match [] lhs tm in
    let pre = vsubst ss pre_var in
    let pre_imp = mk_PreImp (pre, mk_Eval (tr_env, mk_Var (mk_Short str), mk_comb (inv, f))) in
    let h = UNDISCH (REWRITE_RULE [ml_PreImp_def] (ASSUME pre_imp)) in
    let ys = map (fun tm -> MATCH_MP Eval_Eq (hol2deep tm)) xs in
    let rec apply_arrow hyp l = match l with
        [] -> hyp
      | x::xs -> MATCH_MP (MATCH_MP Eval_Arrow (apply_arrow hyp xs)) x in
    let result = apply_arrow h ys in
    check_inv "rec_pattern" tm result else
  (* previously translated constants *)
  if can lookup_v_thm tm then
    let th = lookup_v_thm tm in
    let _ = check_no_ind_assum tm th in
    let xs = map (fun t -> snd (dest_Eq t)) (tr_find_terms is_Eq (concl th)) in
    let ss = map (fun v -> (genvar (type_of v), v)) (filter is_var xs) in
    let th = INST ss th in
    let res = rand (concl (tr_UNDISCH_ALL th)) in
    let inv = get_type_inv (type_of tm) in
    let target = mk_comb (inv, tm) in
    let (ss,ii) = try let (_,s,i) = term_match [] res target in (s,i) with Failure _ ->
                  try let (_,s,i) = term_match [] (rm_fix res) (rm_fix target) in (s,i)
                  with Failure _ ->
                  (* a certificate made without HOL_STRING_TYPE (HOL4) *)
                  try let new_target = subst [tr_LIST_TYPE_CHAR_tm, tr_HOL_STRING_inv] target in
                      let (_,s,i) = term_match [] res new_target in (s,i)
                  with Failure _ -> ([],[]) in
    let result = INST ss (INST_TYPE ii th) in
    check_inv "lookup_v_thm" tm result else
  if can lookup_eval_thm tm then
    let th = lookup_eval_thm tm in
    let inv = rator (rand (concl (hol2deep (mk_var ("v", type_of tm))))) in
    let pat = rator (rand (concl th)) in
    let (_,ss,ii) = term_match [] pat inv in
    let result = INST ss (INST_TYPE ii th) in
    check_inv "lookup_eval_thm" tm result else
  (* built-in ternary operations *)
  if can dest_builtin_terop tm then
    let (p,args,lemma) = dest_builtin_terop tm in
    let [x1;x2;x3] = args in
    let th1 = hol2deep x1 and th2 = hol2deep x2 and th3 = hol2deep x3 in
    (* SPEC_ALL: HOL Light's MATCH_MP generalises the variables it does not *)
    (* instantiate (Eval_HOL_STRING_APPEND has an unused !n:A)               *)
    let result = tr_UNDISCH_ALL (SPEC_ALL (MATCH_MP (MATCH_MP (MATCH_MP lemma th1)
                   (tr_UNDISCH_ALL (SPEC_ALL th2))) (tr_UNDISCH_ALL th3))) in
    check_inv "terop" tm result else
  (* n = 0 and 0 = n *)
  if is_eq tm && type_of (lhs tm) = tr_num_ty && rhs tm = tr_num0_tm then
    let th1 = hol2deep (lhs tm) in
    let result = MATCH_MP Eval_NUM_EQ_0 th1 in
    check_inv "num_eq_0" tm result else
  if is_eq tm && type_of (lhs tm) = tr_num_ty && lhs tm = tr_num0_tm then
    let th1 = hol2deep (rhs tm) in
    let result = CONV_RULE (RAND_CONV (RAND_CONV SYM_CONV)) (MATCH_MP Eval_NUM_EQ_0 th1) in
    check_inv "0_eq_num" tm result else
  (* built-in binary operations *)
  if can dest_builtin_binop tm then
    let (p,args,lemma) = dest_builtin_binop tm in
    let [x1;x2] = args in
    let th1 = hol2deep x1 and th2 = hol2deep x2 in
    let result = tr_UNDISCH_ALL (SPEC_ALL (MATCH_MP (SPEC_ALL (MATCH_MP lemma th1))
                                                     (tr_UNDISCH_ALL th2))) in
    check_inv "binop" tm result else
  (* built-in unary operations *)
  if can dest_builtin_monop tm then
    let (p,args,lemma) = dest_builtin_monop tm in
    let [x1] = args in
    let th1 = hol2deep x1 in
    let result = tr_UNDISCH_ALL (SPEC_ALL (MATCH_MP lemma th1)) in
    check_inv "monop" tm result else
  (* equality (not of words) *)
  if is_eq tm && not (word_ty_ok (type_of (rand tm))) then
    let (x1,x2) = dest_eq tm in
    let th1 = hol2deep x1 and th2 = hol2deep x2 in
    let result = UNDISCH (MATCH_MP Eval_Equality (CONJ th1 th2)) in
    check_inv "equal" tm result else
  (* and, or *)
  if is_conj tm then
    let (x1,x2) = dest_conj tm in
    let th1 = hol2deep x1 and th2 = hol2deep x2 in
    let result = UNDISCH (MATCH_MP Eval_And (CONJ (tr_D th1) (tr_D th2))) in
    check_inv "and" tm result else
  if is_disj tm then
    let (x1,x2) = dest_disj tm in
    let th1 = hol2deep x1 and th2 = hol2deep x2 in
    let result = UNDISCH (MATCH_MP Eval_Or (CONJ (tr_D th1) (tr_D th2))) in
    check_inv "or" tm result else
  (* if-then-else *)
  if is_cond tm then
    let (x1,(x2,x3)) = dest_cond tm in
    if is_PRECONDITION x1 then
      let th2 = hol2deep x2 in
      let lemma = SYM (UNDISCH (ISPECL [x1; x2; x3] IF_TAKEN)) in
      let result = CONV_RULE (RAND_CONV (RAND_CONV (K lemma))) th2 in
      check_inv "if" tm result
    else
      let th1 = hol2deep x1 and th2 = hol2deep x2 and th3 = hol2deep x3 in
      let th = MATCH_MP Eval_If (end_itlist CONJ [tr_D th1; tr_D th2; tr_D th3]) in
      check_inv "if" tm (UNDISCH th) else
  (* Num (ABS i) *)
  if tr_head_is "num_of_int" tm && tr_head_is "int_abs" (rand tm) then
    let th1 = hol2deep (rand (rand tm)) in
    check_inv "num_abs" tm (MATCH_MP Eval_Num_ABS th1) else
  (* Num i *)
  if tr_head_is "num_of_int" tm then
    let th1 = hol2deep (rand tm) in
    check_inv "num" tm (tr_UNDISCH_ALL (MATCH_MP Eval_Num th1)) else
  (* word n (HOL4 n2w) and iword i (i2w) at a known length *)
  if (tr_head_is "word" tm || tr_head_is "iword" tm) && length (tr_dest_args tm) = 1 &&
     word_ty_ok (type_of tm) then
    let dim = tr_word_dim_ty (type_of tm) in
    let th1 = hol2deep (rand tm) in
    let lemma = if tr_head_is "word" tm then ml_Eval_n2w else ml_Eval_i2w in
    let lemma = tr_word_simp_lemma (INST_TYPE [dim, aty] lemma) in
    check_inv (if tr_head_is "word" tm then "n2w" else "i2w") tm (MATCH_MP lemma th1) else
  (* val w (HOL4 w2n) and ival w (w2i) *)
  if (tr_head_is "val" tm || tr_head_is "ival" tm) && length (tr_dest_args tm) = 1 &&
     word_ty_ok (type_of (rand tm)) then
    let dim = tr_word_dim_ty (type_of (rand tm)) in
    let th1 = hol2deep (rand tm) in
    let lemma = if tr_head_is "val" tm then ml_Eval_w2n else ml_Eval_w2i in
    let lemma = tr_word_simp_lemma (INST_TYPE [dim, aty] lemma) in
    check_inv (if tr_head_is "val" tm then "w2n" else "w2i") tm (MATCH_MP lemma th1) else
  (* word_zx (HOL4 w2w) *)
  if tr_head_is "word_zx" tm && length (tr_dest_args tm) = 1 &&
     word_ty_ok (type_of (rand tm)) && word_ty_ok (type_of tm) then
    let dim1 = tr_word_dim_ty (type_of tm) and dim2 = tr_word_dim_ty (type_of (rand tm)) in
    let th1 = hol2deep (rand tm) in
    let lemma = tr_word_simp_lemma (INST_TYPE [dim1, aty; dim2, bty] ml_Eval_w2w) in
    check_inv "w2w" tm (MATCH_MP lemma th1) else
  (* word_add, word_and, word_or, word_xor, word_sub, comparisons, = *)
  if can tr_dest_word_binop tm && word_ty_ok (type_of (rand tm)) then
    let lemma = tr_dest_word_binop tm in
    let dim = tr_word_dim_ty (type_of (rand tm)) in
    let lemma = tr_word_simp_lemma (INST_TYPE [dim, aty] lemma) in
    let th1 = hol2deep (rand (rator tm)) and th2 = hol2deep (rand tm) in
    check_inv "word_binop" tm (MATCH_MP lemma (CONJ th1 th2)) else
  (* shifts by a numeral *)
  if can tr_dest_word_shift tm && word_ty_ok (type_of tm) then
    let n = rand tm in
    (if is_numeral n then () else
     failwith "2nd arg to word shifts must be numeral constant");
    let dim = tr_word_dim_ty (type_of tm) in
    let lemma = SPEC n (INST_TYPE [dim, aty] (tr_dest_word_shift tm)) in
    let th1 = hol2deep (rand (rator tm)) in
    let lemma = tr_word_simp_lemma (MATCH_MP lemma th1) in
    check_inv "word_shift" tm lemma else
  (* int_of_num o f, f o int_of_num *)
  if tr_is_o_app tm && tr_is_const_named "int_of_num" (rand (rator tm)) then
    let th1 = hol2deep (rand tm) in
    check_inv "int_of_num_o" tm (MATCH_MP ml_Eval_int_of_num_o th1) else
  if tr_is_o_app tm && tr_is_const_named "int_of_num" (rand tm) then
    let th1 = hol2deep (rand (rator tm)) in
    check_inv "o_int_of_num" tm (MATCH_MP ml_Eval_o_int_of_num th1) else
  (* let expressions *)
  if tr_is_let tm then
    let (_,[f;y]) = strip_comb tm in
    let (v,x) = dest_abs f in
    let th1 = hol2deep y in
    let th2 = inst_Eval_env v (hol2deep x) in
    let th2 = GEN tr_v_var th2 in
    let z = rand (rand (concl th1)) in
    let th2 = INST [z, v] th2 in
    let result = MATCH_MP Eval_Let (CONJ th1 th2) in
    check_inv "let" tm result else
  (* HOL Light's LET_END (the body of a let) *)
  if tr_head_is "LET_END" tm then
    let th = hol2deep (rand tm) in
    let result = CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM (ISPEC (rand tm) LET_END_DEF))))) th in
    check_inv "let_end" tm result else
  (* HOL Light's paired abstractions, if not removed by the preprocessing *)
  (* (remove_pair_abs): \v. case v of (x,y) => b                         *)
  if is_gabs tm && not (is_abs tm) then
    let th = tr_pair_abs_conv tm in
    let th1 = hol2deep (rand (concl th)) in
    check_inv "pair_abs" tm (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (SYM th)))) th1) else
  (* MAP, ALL, EX of a lambda (HOL4: side conditions of the body may assume MEM x l) *)
  try tr_map_like tm with Failure _ ->
  (* applications *)
  if is_comb tm then
    let (f,x) = dest_comb tm in
    let thf = remove_primes (hol2deep f) in
    let thx = remove_primes (hol2deep x) in
    let thx = force_remove_fix thx in
    let result =
      try MATCH_MP (MATCH_MP Eval_Arrow thf) thx with Failure _ ->
      try MY_MATCH_MP (MATCH_MP Eval_Arrow thf) (MATCH_MP Eval_Eq thx) with Failure e ->
      (* patch up the difference between HOL_STRING_TYPE and LIST_TYPE ml_CHAR *)
      (try let thx' = MATCH_MP Eval_HOL_STRING_DEST thx in
           let res = try MATCH_MP (MATCH_MP Eval_Arrow thf) thx' with Failure _ ->
                     MY_MATCH_MP (MATCH_MP Eval_Arrow thf) (MATCH_MP Eval_Eq thx') in
           Format.print_string
             "Warning: automatically added string EXPLODE due to HOL_STRING_TYPE\n";
           res
       with Failure _ -> failwith e) in
    check_inv "comb" tm result else
  (* lambda abstractions *)
  if is_abs tm then
    let (v,x) = dest_abs tm in
    let thx = hol2deep x in
    let result = apply_Eval_Fun v thx false in
    check_inv "abs" tm result else
  if is_const tm && fst (dest_const tm) = "ARB" then
    let inv = get_type_inv (type_of tm) in
    let goal = mk_imp (tr_PRECONDITION_F_tm, mk_Eval (tr_env, tr_bind_exn, mk_comb (inv, tm))) in
    let result = UNDISCH (tr_auto_prove "hol2deep"
                   (goal, REWRITE_TAC [ml_PRECONDITION_def])) in
    check_inv "arb" tm result
  else raise (Unable_to_translate tm)

and tr_map_like tm =
  if not (is_comb tm && is_abs (rand tm)) then failwith "tr_map_like" else
  let r = rator tm in
  if not (tr_is_const_named "MAP" r || tr_is_const_named "ALL" r || tr_is_const_named "EX" r)
  then failwith "tr_map_like" else
  let f = rand tm in
  (* HOL4: hol2deep of rator of MAP_pattern, the constant at its generic    *)
  (* type: the certificate's invariants a, b are free and the MATCH_MP with *)
  (* Eval_Arrow below instantiates them (to ml_And a P for the argument);   *)
  (* at tm's instance type they are fixed and the match failed              *)
  let th_m = hol2deep (mk_const (fst (dest_const r), [])) in
  let (v,x) = dest_abs f in
  let th_f = hol2deep x in
  let th_f = apply_Eval_Fun v th_f true in
  if hyp th_f = [] then failwith "tr_map_like: no hypotheses" else
  let thi = GEN v (PURE_REWRITE_RULE [IMP_IMP] (DISCH_ALL th_f)) in
  (* Eq_IMP_And, instantiated explicitly (HOL4 HO_MATCH_MP) *)
  let (bv,bod) = dest_forall (concl thi) in
  let (hyps_v, ev) = dest_imp bod in
  let (env,fexp,pr) = dest_Eval ev in
  let (eqa,bb) = dest_Arrow (rator pr) in
  let (a,_) = dest_Eq eqa in
  let (name,exp) = (rand (rator fexp), rand fexp) in
  let lemma = tr_ISPECL_NAMED ["env", env; "name", name; "exp", exp; "a", a;
                               "P", mk_abs (bv, hyps_v); "b", bb; "f", rand pr] Eq_IMP_And in
  let lemma = CONV_RULE (LAND_CONV (BINDER_CONV (LAND_CONV BETA_CONV))) lemma in
  let thi = MP lemma thi in
  let thi = MATCH_MP (MATCH_MP Eval_Arrow th_m) thi in
  let thi = REWRITE_RULE [LIST_TYPE_And] thi in
  let thi = SPEC_ALL (MATCH_MP And_IMP_Eq thi) in
  let thi = REWRITE_RULE [EVERY_MEM_CONTAINER] thi in
  check_inv "map" tm (tr_UNDISCH_ALL thi);;

(* ------------------------------------------------------------------------- *)
(* Preconditions (HOL4 clean_precondition, extract_precondition_non_rec,     *)
(* derive_split, extract_precondition_rec)                                   *)
(* ------------------------------------------------------------------------- *)

(* generated constant -> the translation (file) that made it *)
let tr_generated_consts = (Hashtbl.create 1000 : (string, string) Hashtbl.t);;

let find_const_name str =
  let thy = ml_prog_current_theory () in
  let taken s = can get_const_type s in
  let mine s = (try Hashtbl.find tr_generated_consts s = thy with Not_found -> false) in
  let name =
    if not (taken str) then str
    else if mine str then
      (* HOL4: str_0, str_1, ... within the theory *)
      let rec aux n = let s = str ^ "_" ^ string_of_int n in
                      if taken s then aux (n+1) else s in aux 0
    else
      let s = thy ^ "_" ^ str in
      if not (taken s) then s else
      let rec aux n = let s' = s ^ "_" ^ string_of_int n in
                      if taken s' then aux (n+1) else s' in aux 0 in
  Hashtbl.replace tr_generated_consts name thy; name;;

(* the constant of a side condition: HOL4's name f_side, or THY_f_side when *)
(* another translation (file) has f_side (HOL4 keeps them apart by theory;   *)
(* NAMING.md 11.4); the same translation loaded again keeps its name (a      *)
(* benign redefinition).  The saved theorem keeps HOL4's name f_side_def    *)
(* (tr_fetch gives the newest).                                             *)
let tr_side_const_name name =
  let thy = ml_prog_current_theory () in
  let mine s = (try Hashtbl.find tr_generated_consts s = thy with Not_found -> false) in
  let pick s = Hashtbl.replace tr_generated_consts s thy; s in
  if not (can get_const_type name) || mine name then pick name else
  let s = thy ^ "_" ^ name in
  if not (can get_const_type s) || mine s then pick s else
  find_const_name s;;

let tr_new_side_definition tm =
  (* f_side v1 .. vn = rhs, f_side a new constant *)
  let l = lhs tm in
  let c0 = fst (strip_comb l) in
  let c = mk_var (tr_side_const_name (fst (dest_var c0)), type_of c0) in
  let tm = vsubst [c, c0] tm in
  let l = lhs tm in
  let name = fst (dest_var c) in
  (* new_definition gives a benign redefinition (the same equation, with   *)
  (* the constant) the stored theorem back                                 *)
  if can get_const_type name then
    let k = mk_const (name, []) in
    let k = inst (type_match (type_of k) (type_of c) []) k in
    (try new_definition (vsubst [k, c] tm)
     with Failure _ -> failwith ("side condition: " ^ name ^ " already defined with another body"))
  else new_definition tm;;

(* the [simp] rewrites of HOL4's integerTheory that srw_ss applies to side   *)
(* conditions (a translator-local list, not the kit's simpset): INT_INJ,    *)
(* INT_LT, INT_LE, INT_NEG_0, INT_ABS_NUM, the units and zeros, INT_NEGNEG, *)
(* INT_EQ_NEG, int_eq_calculate, NUM_OF_INT, INT_OF_NUM, the ABS laws        *)
let tr_INT_OF_NUM = prove
 (`!i. &(num_of_int i) = i <=> &0 <= i`,
  GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN (SUBST1_TAC o SYM) THEN REWRITE_TAC [INT_POS];
    REWRITE_TAC [INT_OF_NUM_OF_INT]]);;
let tr_int_eq_calculate = prove
 (`!n m. (&n = -- &m <=> n = 0 /\ m = 0) /\ (-- &n = &m <=> n = 0 /\ m = 0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC [GSYM INT_OF_NUM_EQ] THEN INT_ARITH_TAC);;
let tr_int_simps =
  [INT_OF_NUM_EQ; INT_OF_NUM_LT; INT_OF_NUM_LE; INT_OF_NUM_GT; INT_OF_NUM_GE;
   INT_NEG_0; INT_ABS_NUM; INT_ADD_LID; INT_ADD_RID; INT_MUL_LID; INT_MUL_RID;
   INT_MUL_LZERO; INT_MUL_RZERO; INT_NEG_NEG; INT_LE_REFL; INT_LT_REFL;
   INT_SUB_LZERO; INT_SUB_RZERO; INT_EQ_NEG2; INT_NEG_EQ_0; tr_int_eq_calculate;
   NUM_OF_INT_OF_NUM; tr_INT_OF_NUM; INT_ABS_POS; INT_ABS_NEG; INT_ABS_ABS;
   INT_ABS_ZERO; GSYM INT_ABS_NZ; INT_ADD_LINV; INT_ADD_RINV];;

let clean_precondition pre_def =
  let th = CAKE_SIMP_RULE tr_int_simps pre_def in
  let th = REWRITE_RULE [ml_CONTAINER_def] th in
  SPEC_ALL (rename_bound_vars_rule "v" (GEN_ALL th));;

let tr_EVAL_PRECONDITION_T = PRECONDITION_T;;

let extract_precondition_non_rec th pre_var =
  if not (is_imp (concl th)) then (th, None) else
  let c = REWRITE_CONV [ml_CONTAINER_def; ml_PRECONDITION_def] THENC
          ONCE_REWRITE_CONV [GSYM ml_PRECONDITION_def] THENC
          CAKE_SIMP_CONV ([ARITH_ss; FALSE_def; TRUE_def] @ tr_int_simps) in
  let th = CONV_RULE (RATOR_CONV (RAND_CONV c)) th in
  (* a propositional tautology left by the simplifier (the unreachable ARB  *)
  (* arms of a complete boolean case tree: ~((v2 /\ ~v1) /\ v1) ..), which   *)
  (* HOL4's simpset removes: T                                             *)
  let th =
    let r = rand (fst (dest_imp (concl th))) in
    let rec atoms t acc =
      if is_conj t || is_disj t || is_imp t || (is_eq t && type_of (lhs t) = bool_ty)
      then atoms (lhand t) (atoms (rand t) acc)
      else if is_neg t then atoms (rand t) acc
      else if t = tr_T_tm || t = tr_F_tm then acc else insert t acc in
    if r = tr_T_tm || length (atoms r []) > 10 then th else
    (try let eq = EQT_INTRO (TAUT r) in
         CONV_RULE (RATOR_CONV (RAND_CONV (RAND_CONV (K eq)))) th
     with Failure _ -> th) in
  let rhs = rand (fst (dest_imp (concl th))) in
  if rhs = tr_T_tm then
    (tr_UNDISCH_ALL (REWRITE_RULE [tr_EVAL_PRECONDITION_T] th), None)
  else
    (* variables of the precondition other than the parameters: arguments of *)
    (* a translated function that the definition does not apply (rename =   *)
    (* f, eta-expanded once as HOL4 does, for an f of two arguments with a   *)
    (* precondition): the side condition holds for all of them              *)
    let extra = subtract (frees rhs) (frees pre_var) in
    let (th, rhs) =
      if extra = [] then (th, rhs) else
      let extra' = map (fun v -> mk_var ("x" ^ string_of_int (index v extra + 1), type_of v))
                       extra in
      let extra' = map2 (fun v v' -> variant (frees rhs) v') extra extra' in
      let rhs' = list_mk_forall (extra', vsubst (zip extra' extra) rhs) in
      let a' = ASSUME (mk_PRECONDITION rhs') in
      let inst = SPECL extra (EQ_MP (REWR_CONV ml_PRECONDITION_def (concl a')) a') in
      let pre_th = EQ_MP (SYM (REWR_CONV ml_PRECONDITION_def (mk_PRECONDITION rhs))) inst in
      (DISCH (concl a') (MP th pre_th), rhs') in
    let def_tm = mk_eq (pre_var, rhs) in
    let pre_def = tr_new_side_definition def_tm in
    let c = RATOR_CONV (RAND_CONV (RAND_CONV (REWR_CONV (GSYM (SPEC_ALL pre_def))))) in
    let th = tr_UNDISCH_ALL (CONV_RULE c th) in
    let pre_def = clean_precondition pre_def in
    let _ = tr_save_thm (fst (dest_var (fst (strip_comb pre_var))) ^ "_def") pre_def in
    (th, Some pre_def);;

(* ------------------------------------------------------------------------- *)
(* Removing the Eq of the parameters (HOL4 remove_Eq)                        *)
(* ------------------------------------------------------------------------- *)

let rec tr_dest_EqArrows tm =
  if is_Arrow tm && is_Eq (fst (dest_Arrow tm))
  then snd (dest_Eq (fst (dest_Arrow tm))) :: tr_dest_EqArrows (snd (dest_Arrow tm))
  else [];;

let remove_Eq th =
  try
    let (env,exp,p) = dest_Eval (concl th) in
    let rev_params = rev (tr_dest_EqArrows (rator p)) in
    let f v th =
      let (env,exp,p) = dest_Eval (concl th) in
      let inv = rator p and fn = rand p in
      let lemma = tr_ISPECL_NAMED ["env", env; "exp", exp; "p", mk_abs (v, inv); "f", fn]
                    Eval_FUN_FORALL in
      let lemma = CONV_RULE (LAND_CONV (BINDER_CONV (RAND_CONV (RATOR_CONV BETA_CONV)))) lemma in
      let th1 = MP lemma (GEN v th) in
      CONV_RULE (RAND_CONV (RATOR_CONV (DEPTH_CONV BETA_CONV THENC
                                        REWRITE_CONV [FUN_QUANT_SIMP]))) th1 in
    itlist f rev_params th
  with Failure _ -> th;;

(* the Eq of a variable that is not a parameter (a genvar from an argument    *)
(* that the definition does not apply, rename = f with f's precondition):   *)
(* removed one by one when it is not in a hypothesis (HOL4 never gets there) *)
let tr_remove_genvar_Eqs th =
  try
    let (env,exp,p) = dest_Eval (concl th) in
    let vs = filter (fun v -> is_var v && String.length (fst (dest_var v)) > 0 &&
                              (fst (dest_var v)).[0] = '_' &&
                              not (exists (vfree_in v) (hyp th)))
                    (tr_dest_EqArrows (rator p)) in
    let f v th =
      try
        let (env,exp,p) = dest_Eval (concl th) in
        let inv = rator p and fn = rand p in
        let lemma = tr_ISPECL_NAMED ["env", env; "exp", exp; "p", mk_abs (v, inv); "f", fn]
                      Eval_FUN_FORALL in
        let lemma = CONV_RULE (LAND_CONV (BINDER_CONV (RAND_CONV (RATOR_CONV BETA_CONV)))) lemma in
        let th1 = MP lemma (GEN v th) in
        CONV_RULE (RAND_CONV (RATOR_CONV (DEPTH_CONV BETA_CONV THENC
                                          REWRITE_CONV [FUN_QUANT_SIMP]))) th1
      with Failure _ -> th in
    itlist f (rev vs) th
  with Failure _ -> th;;

let rec rev_param_list tm = if is_comb tm then rand tm :: rev_param_list (rator tm) else [];;

(* ------------------------------------------------------------------------- *)
(* Names of translated functions (HOL4 use_long_names, pick_name,           *)
(* next_ml_names, get_info)                                                  *)
(* ------------------------------------------------------------------------- *)

let use_long_names = ref false;;
let pick_name = ref (fun (c:term) -> (failwith "pick_name" : string));;
let next_ml_names = ref ([] : string list);;

let get_next_ml_name default_name =
  match !next_ml_names with
    [] -> default_name
  | x::xs -> (next_ml_names := xs; x);;

(* the HOL4 name of a constant (decision D4): ident_map, else its own name *)
let tr_hol4_name_of_const c =
  let n = fst (dest_const c) in
  try let (_,h4,_) = assoc n !tr_hol4_name_table in h4 with Failure _ -> n;;

let get_info def =
  let (lhs,rhs) = dest_eq (concl def) in
  let c = fst (strip_comb lhs) in
  let name = tr_hol4_name_of_const c in
  let name = if !use_long_names then
               (let (thy,_,_) = try assoc (fst (dest_const c)) !tr_hol4_name_table
                                with Failure _ -> ("","","") in thy ^ "_" ^ name)
             else name in
  let fname = get_unique_name (try !pick_name c with Failure _ -> name) in
  (fname, get_next_ml_name fname, lhs, rhs, def);;

(* ------------------------------------------------------------------------- *)
(* Names of generated constants (HOL4 find_const_name; NAMING.md 11.4)       *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Instantiating the constructor-name variables (HOL4 instantiate_cons_name)  *)
(* ------------------------------------------------------------------------- *)

let instantiate_cons_name th =
  let lcs = itlist (fun h l -> union (tr_find_terms (fun t -> is_eq t && is_lookup_cons (lhs t)) h) l)
                   (hyp th) [] in
  let vars = filter is_var (map (fun t -> rand (rator (lhs t))) lcs) in
  let inst_var tm =
    let (nm, mods) = lookup_cons_name (fst (dest_var tm)) in
    get_qualified_name mods nm in
  INST (map (fun tm -> (inst_var tm, tm)) (setify vars)) th;;

(* ------------------------------------------------------------------------- *)
(* The translation of a definition (HOL4 translate_main, translate_options)  *)
(* ------------------------------------------------------------------------- *)

let find_def_for_const = ref (fun (const:term) -> (raise (Unable_to_translate const) : thm));;

let find_def_for_const_wrapper tm =
  if not (is_const tm) then raise (Unable_to_translate tm) else
  let def = !find_def_for_const tm in
  if tr_can_find_term (fun t -> t = tm || (is_const t && fst (dest_const t) = fst (dest_const tm)))
                      (concl def) then def
  else failwith ("find_def_for_const_wrapper: bad def: " ^ fst (dest_const tm));;

let register_term_types register_type tm =
  let special_types = [tr_num_ty; tr_int_ty; bool_ty; tr_char_ty; mlstring_ty;
                       tr_float64_ty] @ get_user_supplied_types () in
  let ignore_type ty =
    if exists (fun ty1 -> can (type_match ty1 ty) []) special_types then true else
    if is_vartype ty then true else
    if can dest_fun_type ty then true else
    if tr_is_word_type ty then true else
    if is_vector_type ty then true else
    (* numeral types (word lengths) above 1; :1 is the unit type (HOL4 one) *)
    if (try tr_numeral_type_value ty > 1 with Failure _ -> false) then true else false in
  let rec typeops ty =
    if is_vartype ty then [] else
    let (_,targs) = dest_type ty in ty :: flat (map typeops targs) in
  let register_term_type tm =
    let tys = filter (fun t -> not (ignore_type t)) (typeops (type_of tm)) in
    List.iter register_type tys in
  let rec every_term tm =
    (match tm with
       Abs(_,b) -> every_term b
     | Comb(f,x) -> every_term x; every_term f
     | _ -> ());
    register_term_type tm in
  every_term tm;;

type translate_option = No_ind;;  (* HOL4 NoInd *)

let tr_latest_ind = ref (None : thm option);;
let latest_ind () = match !tr_latest_ind with Some th -> th | None -> failwith "latest_ind";;

let tr_EVAL_T_F =
  CONJ (ISPEC `TRUE` ml_CONTAINER_def) (ISPEC `FALSE` ml_CONTAINER_def);;

let tr_drop_T_hyps th = if mem `T` (hyp th) then PROVE_HYP TRUTH th else th;;

(* ------------------------------------------------------------------------- *)
(* Evaluating the optimiser on generated code (HOL4 optimise_and_abstract:   *)
(* MATCH_MP Eval_OPTIMISE, then EVAL on OPTIMISE exp)                        *)
(* ------------------------------------------------------------------------- *)

(* equality of ground constructor terms with literal leaves (HOL4's EVAL  *)
(* decides these with the datatype's injectivity and distinctness)         *)
let tr_eq_rules_cache = (Hashtbl.create 50 : (string, thm list) Hashtbl.t);;
let tr_eq_rules tyname =
  try Hashtbl.find tr_eq_rules_cache tyname with Not_found ->
  let inj = try [injectivity tyname] with Failure _ -> [] in
  let dist = try let th = distinctness tyname in
                 flat (map (fun c -> let c = SPEC_ALL c in [EQF_INTRO c; EQF_INTRO (GSYM c)])
                           (CONJUNCTS th))
             with Failure _ -> [] in
  let rules = inj @ dist in
  Hashtbl.replace tr_eq_rules_cache tyname rules; rules;;

let rec tr_ground_eq_conv tm =
  let l,r = dest_eq tm in
  if aconv l r then EQT_INTRO (REFL l) else
  let ty = type_of l in
  if ty = tr_num_ty then NUM_EQ_CONV tm else
  if ty = tr_int_ty then INT_EQ_CONV tm else
  if ty = tr_char_ty then CHAR_EQ_CONV tm else
  if ty = tr_string_ty && can dest_string l && can dest_string r then STRING_EQ_CONV tm else
  if tr_is_word_type ty then WORD_REDUCE_CONV tm else
  let tyname = fst (dest_type ty) in
  let th = GEN_REWRITE_CONV I (tr_eq_rules tyname) tm in
  let rhs = rand (concl th) in
  if rhs = tr_T_tm || rhs = tr_F_tm then th else
  let c t = if is_eq t then tr_ground_eq_conv t else failwith "tr_ground_eq_conv" in
  TRANS th ((ONCE_DEPTH_CONV c THENC REWRITE_CONV []) rhs);;

(* the compset for OPTIMISE exp (HOL4 EVAL with ml_optimiseTheory) *)
let tr_opt_cs = ref (None : Compute.compset option);;
let tr_get_opt_cs () =
  match !tr_opt_cs with Some cs -> cs | None ->
  let cs = Compute.bool_compset () in
  Compute.set_skip cs `COND: bool -> A -> A -> A` (Some 1);
  num_compute_add_convs cs;
  Compute.add_conv (`(=):A->A->bool`, 2, tr_ground_eq_conv) cs;
  Compute.add_thms
    [OPTIMISE_def; o_THM; BOTTOM_UP_OPT_def; abs2let_def; let_id_def; dest_binop_def;
     opt_sub_add_def; case_def "exp"; case_def "list"; case_def "option"; case_def "prod";
     case_def "lit"; case_def "op"] cs;
  tr_opt_cs := Some cs; cs;;

let tr_OPTIMISE_CONV tm = Compute.CBV_CONV (tr_get_opt_cs ()) tm;;

(* whether OPTIMISE can change the code: a redex of abs2let                *)
(* (App Opapp [Fun v e; y]), let_id (Let (SOME v) x (Var (Short v))) or      *)
(* opt_sub_add (App (Arith op IntT) [App (Arith op' IntT) [x; Lit l]; Lit l']) *)
(* (later passes only rewrite redexes made by earlier ones, so code without *)
(* any is its own optimisation and the evaluation of OPTIMISE is skipped)   *)
let tr_may_optimise code =
  let is_c n t = is_const t && fst (dest_const t) = n in
  let app_args t = (* App op [args] -> (op, args) *)
    match t with
      Comb(Comb(c,op),l) when is_c "App" c -> (try Some (op, dest_list l) with Failure _ -> None)
    | _ -> None in
  let is_arith_int op =
    match op with
      Comb(Comb(c,_),ty) when is_c "Arith" c -> is_c "IntT" ty
    | _ -> false in
  let is_lit t = match t with Comb(c,_) -> is_c "Lit" c | _ -> false in
  let redex t =
    (match app_args t with
       Some (op, [f; _]) when is_c "Opapp" op ->
         (match f with Comb(Comb(c,_),_) -> is_c "Fun" c | _ -> false)
     | Some (op, [y; z]) when is_arith_int op && is_lit z ->
         (match app_args y with
            Some (op2, [_; l]) -> is_arith_int op2 && is_lit l
          | _ -> false)
     | _ -> false) ||
    (match t with
       Comb(Comb(Comb(c,n),_),body) when is_c "Let" c ->
         (match n, body with
            Comb(s,v), Comb(vc, Comb(sh,v')) ->
              is_c "SOME" s && is_c "Var" vc && is_c "Short" sh && v = v'
          | _ -> false)
     | _ -> false) in
  can (find_term redex) code;;

(* |- ml_Eval env exp P  to  |- ml_Eval env exp' P with the optimised code *)
let tr_optimise th =
  let th = tr_UNDISCH_ALL th in
  let (_,code,_) = dest_Eval (concl th) in
  if not (tr_may_optimise code) then th else
  let th = MATCH_MP Eval_OPTIMISE th in
  CONV_RULE (RATOR_CONV (RAND_CONV tr_OPTIMISE_CONV)) th;;

let tr_translate_fail = ref TRUTH;;

let translate_main_nonrec thms =
  let (fname,ml_fname,def,th,v) = hd thms in
  let fname = get_unique_name fname in
  let th = tr_D (clean_assumptions (tr_D th)) in
  let th = CONV_RULE (DEPTH_CONV ETA_CONV) th in
  let th = CONV_RULE (RATOR_CONV (RAND_CONV (REWRITE_CONV [tr_EVAL_T_F; ml_CONTAINER_def;
                                                          TRUE_def; FALSE_def]))) th in
  let th = clean_assumptions (tr_D th) in
  let (lhs,rhs) = dest_eq (concl def) in
  let pre_var = get_pre_var lhs fname in
  let (th,pre) = extract_precondition_non_rec th pre_var in
  let th = tr_remove_genvar_Eqs (remove_Eq th) in
  let th = SIMP_EqualityType_ASSUMS th in
  let code = let (_,e,_) = dest_Eval (concl th) in e in
  let is_fun = is_Fun code in
  let th =
    if is_fun then
      let th = INST [tr_cl_env, tr_env] th in
      let (_,fexp,p) = dest_Eval (concl th) in
      let lemma = tr_ISPECL_NAMED ["cl_env", tr_cl_env; "n", rand (rator fexp);
                                   "exp", rand fexp; "P", p; "env", tr_env]
                                  Eval_Fun_Var_intro in
      UNDISCH (tr_SPEC_NAMED "name" (mk_mlstring ml_fname) (MP lemma th))
    else th in
  (is_fun, [(fname,ml_fname,def,th,pre)]);;

let translate_main_rec_ref =
  ref (fun (_:translate_option list) (_:(string*string*thm*thm*term) list) (_:thm option)
           (_:thm) -> (failwith "recursion: not yet" : bool * (string*string*thm*thm*thm option) list));;

let translate_main options translate register_type def =
  let original_def = def in
  register_term_types register_type (concl def);
  let (is_rec,defs,ind) = tr_time "translate: preprocess_def" preprocess_def def in
  register_term_types register_type (concl (end_itlist CONJ defs));
  let info = map get_info defs in
  let compute_deep_embedding info =
    List.iter (fun (fname,ml_fname,lhs,_,_) -> install_rec_pattern lhs fname ml_fname) info;
    let thms = try map (fun (fname,ml_fname,lhs,rhs,def) ->
                          (fname,ml_fname,hol2deep rhs,def)) info
               with e -> (uninstall_rec_patterns (); raise e) in
    uninstall_rec_patterns (); thms in
  let rec loop info =
    try compute_deep_embedding info
    with Unable_to_translate tm ->
      (ignore (translate (find_def_for_const_wrapper tm)); loop info) in
  let thms = tr_time "translate: hol2deep" loop info in
  let thms = map (fun (x0,x1,th,x2) -> (x0,x1,instantiate_cons_name th,x2)) thms in
  Format.print_string ("Translating " ^ String.concat ", " (map (fun (f,_,_,_) -> f) thms) ^ "\n");
  let optimise_and_abstract (fname,ml_fname,th,def) =
    let th = CONV_RULE (RAND_CONV (RAND_CONV (REWRITE_CONV [ml_CONTAINER_def] THENC
                                               ONCE_REWRITE_CONV [GSYM def]))) th in
    (* optimise the generated code (HOL4 Eval_OPTIMISE and EVAL) *)
    let th = tr_optimise th in
    let th = tr_D (tr_drop_T_hyps (tr_UNDISCH_ALL th)) in
    let rev_params = rev_param_list (lhs (concl def)) in
    let (th,v) =
      if rev_params = [] then (th, tr_T_tm) else
      (itlist (fun v th -> apply_Eval_Fun v th true)
              (rev (if is_rec then butlast rev_params else rev_params)) th,
       last rev_params) in
    (fname,ml_fname,def,th,v) in
  let thms = tr_time "translate: optimise and abstract" (map optimise_and_abstract) thms in
  let (is_fun,results) =
    if not is_rec then
      (if length thms = 1 then () else failwith "multiple non-rec definitions";
       tr_time "translate: main_nonrec" translate_main_nonrec thms)
    else tr_time "translate: main_rec" (!translate_main_rec_ref options thms ind) original_def in
  let th = end_itlist CONJ (map (fun (_,_,_,th,_) -> th) results) in
  if tr_can_find_term (fun t -> is_const t && fst (dest_const t) = "WF") (concl (tr_D th))
  then failwith "WF" else (is_rec, is_fun, results);;

let translate_rec_store_ref =
  ref (fun (_:(string*string*thm*thm*thm option) list) -> (failwith "rec store" : thm));;

(* a definition of a value, not a function (HOL4 translate_options, the   *)
(* "val" case): the value constant NAME_v and the extra references        *)
(* NAME_refs by new_specification, the declaration Dlet by ml_progLib     *)
let tr_state_refs_tm = `state_refs:(FFI)state->(v store_v)list`;;

let translate_value (fname,ml_fname,def,th,pre) =
  let th = INST [get_curr_env (), tr_env] th in
  let th = tr_drop_T_hyps (tr_UNDISCH_ALL (clean_assumptions (tr_D th))) in
  let curr_state = get_curr_state () in
  let curr_refs = tr_mk_icomb tr_state_refs_tm curr_state in
  let curr_refs_eq = ML_PROG_EVAL_CONV curr_refs in
  (* free invariant variables of type variables become UNIT_TYPE (HOL4) *)
  let th1 = itlist (fun v th ->
      try let (_,ss,ii) = term_match [] v tr_UNIT_TYPE_tm in INST ss (INST_TYPE ii th)
      with Failure _ -> th) (frees (concl th)) th in
  let lemma = tr_ISPECL_NAMED ["refs", curr_refs] ml_Eval_constant in
  let lemma = PURE_REWRITE_RULE [curr_refs_eq] lemma in
  let lemma = MATCH_MP lemma th1 in
  let lemma = REWRITE_RULE [PULL_EXISTS_EXTRA] (tr_D lemma) in
  let v_name = find_const_name (fname ^ "_v") in
  let refs_name = find_const_name (fname ^ "_refs") in
  let v_thm_temp = new_specification [v_name; refs_name] lemma in
  let v_thm_temp = tr_UNDISCH_ALL (PURE_REWRITE_RULE [ml_PRECONDITION_def] v_thm_temp) in
  (* HOL4: NAME_refs_def, |- NAME_refs = [] when the code changes no references *)
  let _ = if not (is_conj (concl v_thm_temp)) then TRUTH else
    (try
       let ref_def = CONJUNCT2 v_thm_temp in
       let c = REWRITE_CONV [ALL; MAP; SND; no_change_refs_def] in
       let ref_def_lemma = CONV_RULE (RATOR_CONV (RAND_CONV c)) ref_def in
       tr_save_thm (refs_name ^ "_def") (MP ref_def_lemma TRUTH)
     with Failure _ -> TRUTH) in
  let v_thm_temp = if is_conj (concl v_thm_temp) then CONJUNCT1 v_thm_temp else v_thm_temp in
  let v_thm = MATCH_MP Eval_evaluate_IMP (CONJ th v_thm_temp) in
  let v_thm = tr_UNDISCH_ALL (SIMP_EqualityType_ASSUMS v_thm) in
  let eval_thm = MATCH_MP evaluate_empty_state_IMP
                   (PURE_REWRITE_RULE [GSYM curr_refs_eq] v_thm_temp) in
  let pre_def = match pre with None -> TRUTH | Some pre_def -> pre_def in
  ml_prog_update (ml_prog_add_Dlet eval_thm ml_fname);
  add_v_thms (fname,ml_fname,v_thm,pre_def);
  let v_thm = tr_UNDISCH_ALL (PURE_REWRITE_RULE [GSYM IMP_IMP] (DISCH_ALL v_thm)) in
  tr_save_thm (fname ^ "_v_thm") v_thm;;

(* a new reference cell with initial value tm (HOL4 declare_new_ref):      *)
(* val name = Ref tm, the constants name_init_val and name_loc, and          *)
(* |- A tm name_init_val /\ name_loc = Loc T k saved as name_def            *)
let declare_new_ref name tm =
  let init_val_th = hol2deep tm in
  let init_val_th1 = clean_assumptions (tr_D (INST [get_curr_env (), tr_env] init_val_th)) in
  let init_val_th1 =
    if not (is_imp (concl init_val_th1)) then init_val_th1 else
    try MP init_val_th1 TRUTH with Failure _ ->
      failwith "translate_new_ref failed: translation of init value has preconditions" in
  let th = MATCH_MP ml_new_ref_thm init_val_th1 in
  let th = CONV_RULE (RATOR_CONV (RAND_CONV (REWRITE_CONV [ALL; MAP; SND; no_change_refs_def]))) th in
  let th = try MP th TRUTH with Failure _ ->
    failwith ("translate_new_ref failed: init value not simple enough to prove no refs " ^
              "changed during evaluation of init value") in
  let curr_state = get_curr_state () in
  let curr_refs = tr_mk_icomb tr_state_refs_tm curr_state in
  let curr_refs_eq = ML_PROG_EVAL_CONV curr_refs in
  let lemma = tr_SPEC_NAMED "s" curr_state evaluate_empty_state_IMP in
  let lemma1 = PURE_REWRITE_RULE [curr_refs_eq] lemma in
  let th = SPEC (rand (concl curr_refs_eq)) th in
  let res = new_specification [find_const_name (name ^ "_init_val");
                               find_const_name (name ^ "_loc")] th in
  let eval_rel_thm = CONJUNCT1 res in
  let v_def = CONJUNCT2 res in
  let th = PURE_REWRITE_RULE [APPEND] (MATCH_MP lemma1 eval_rel_thm) in
  ml_prog_update (ml_prog_add_Dlet th name);
  tr_save_thm (name ^ "_def") v_def;;

(* HOL4 add_preferred_thy: theorems such as NAME_ind and NAME_trans_ind of   *)
(* the given theory are preferred by find_ind_thm.  LightCake has no theorem  *)
(* database: register such an induction theorem with add_ind_thm "NAME" th   *)
(* (this function only remembers the names)                                  *)
let tr_preferred_thys = ref ([] : string list);;
let add_preferred_thy thy = tr_preferred_thys := thy :: !tr_preferred_thys;;

let rec translate_options options def =
    let (is_rec,is_fun,results) =
      try translate_main options (translate_options options) register_type def
      with e -> (tr_translate_fail := def; raise e) in
    if is_rec then !translate_rec_store_ref results
    else
      let (fname,ml_fname,def,th,pre) = hd results in
      if is_fun then
        let th = INST [get_curr_env (), tr_cl_env] th in
        let n = mk_mlstring ml_fname in
        let lookup_var_assum = find (fun h -> tr_head_is "LOOKUP_VAR" h &&
                                       hd (tr_dest_args h) = n) (hyp th) in
        let lemma = MATCH_MP Eval_Var_LOOKUP_VAR_elim (GEN tr_env (DISCH lookup_var_assum th)) in
        let lemma = tr_UNDISCH_ALL (clean_assumptions (tr_D lemma)) in
        let lemma = tr_drop_T_hyps lemma in
        let clo = rand (concl lemma) in
        let (_,v,exp) = dest_Closure clo in
        let v_name = find_const_name (fname ^ "_v") in
        ml_prog_update (ml_prog_add_Dlet_Fun ml_prog_unknown_loc n v exp v_name);
        let v_def = hd (get_curr_v_defs ()) in
        let v_thm = CONV_RULE (RAND_CONV (REWR_CONV (GSYM v_def))) lemma in
        let pre_def = match pre with None -> TRUTH | Some pre_def -> pre_def in
        add_v_thms (fname,ml_fname,v_thm,pre_def);
        tr_save_thm (fname ^ "_v_thm") v_thm
      else translate_value (fname,ml_fname,def,th,pre);;

let translate def = translate_options [] def;;
let translate_no_ind def = translate_options [No_ind] def;;
let () = set_translator translate;;

(* ------------------------------------------------------------------------- *)
(* Recursive functions (HOL4 apply_Eval_Recclosure, extract_precondition_rec,*)
(* get_ind_thm_goal, prove_ind_thm, hide_ind_goal_rule and the recursive    *)
(* branch of translate_main and translate_options)                           *)
(* ------------------------------------------------------------------------- *)

let tr_list_case_def = (case_info_of_tyname "list").ci_def;;

(* find_recfun on the concrete list of a Recclosure, one unfolding at a     *)
(* time: REWRITE_CONV with the one-line find_recfun_def unfolds the         *)
(* recursive call under the case's lambda without end when the first name  *)
(* is not the one looked for (a later function of a mutual group)          *)
let rec tr_find_recfun_conv tm =
  let step = GEN_REWRITE_CONV I [find_recfun_def] THENC
             REWRITE_CONV [tr_list_case_def; tr_pair_case_def] THENC
             DEPTH_CONV BETA_CONV THENC
             REWRITE_CONV [tr_pair_case_def] THENC DEPTH_CONV BETA_CONV THENC
             DEPTH_CONV mlstring_EQ_CONV THENC REWRITE_CONV [] in
  let th = step tm in
  let r = rhs (concl th) in
  if tr_head_is "find_recfun" r then TRANS th (tr_find_recfun_conv r) else th;;

let tr_map_fst3_conv =
  REWRITE_CONV [MAP] THENC
  TOP_DEPTH_CONV (GEN_BETA_CONV ORELSEC GEN_REWRITE_CONV I [tr_pair_case_def]);;

let tr_env2 = mk_var ("env2", venv_ty);;
let tr_shadow_env = mk_var ("shadow_env", venv_ty);;

let apply_Eval_Recclosure recc fname v th =
  let vname = fst (dest_var v) in
  let vname_str = mk_mlstring vname in
  let fname_str = mk_mlstring fname in
  let lemma = tr_ISPECL_NAMED ["funs", recc; "fname", fname_str; "env2", tr_env2]
                Eval_Recclosure_ALT in
  (* ALL_DISTINCT of the function names and find_recfun, by evaluation *)
  let ad = fst (dest_imp (concl lemma)) in
  let adth = EQT_ELIM ((tr_map_fst3_conv THENC tr_ALL_DISTINCT_CONV) ad) in
  let lemma = MP lemma adth in
  let fr = find_term (fun t -> tr_head_is "find_recfun" t) (concl lemma) in
  let frth = tr_find_recfun_conv fr in
  let (x,e) = dest_pair (rand (rhs (concl frth))) in
  let name_var = find (fun t -> fst (dest_var t) = "name") (frees (concl lemma)) in
  let body_var = find (fun t -> fst (dest_var t) = "body") (frees (concl lemma)) in
  let lemma = INST [x, name_var; e, body_var] lemma in
  let frth' = INST [x, name_var; e, body_var] frth in
  let inv = get_type_inv (type_of v) in
  let wr = list_mk_comb (tr_write_rec_tm, [recc; tr_env2; tr_env2]) in
  let new_env = mk_write (x, tr_v_var, wr) in
  let assum_eval = mk_Eval (tr_env, mk_Var (mk_Short vname_str), mk_comb (inv, v)) in
  let assum = vsubst [new_env, tr_env] assum_eval in
  let thx = tr_UNDISCH_ALL th in
  let thx = REWRITE_RULE [GSYM SafeVar_def] thx in
  let thx = DISCH assum (DISCH_ALL thx) in
  let thx = INST [new_env, tr_env] thx in
  let thx = PURE_REWRITE_RULE [Eval_Var_SIMP; lookup_var_write; lookup_cons_write] thx in
  let thx = CONV_RULE (DEPTH_CONV mlstring_EQ_CONV) thx in
  let thx = REWRITE_RULE [SafeVar_def] thx in
  let new_assum = fst (dest_imp (concl thx)) in
  let th1 = REWRITE_RULE [ASSUME new_assum] (UNDISCH thx) in
  let th1 = tr_UNDISCH_ALL th1 in
  let th1 = CONV_RULE (RAND_CONV (RAND_CONV (tr_UNBETA_CONV v))) th1 in
  let th1 = DISCH new_assum th1 in
  let th2 = MATCH_MP lemma (INST [tr_cl_env, tr_env] (GEN tr_v_var th1)) in
  (* th2: LOOKUP_VAR f env (Recclosure ..) ==> find_recfun .. ==> ml_Eval .. *)
  let lv = fst (dest_imp (concl th2)) in
  let th2 = MP (UNDISCH th2) frth' in
  let th2 = DISCH lv th2 in
  let assum = ASSUME lv in
  let th3 = REWRITE_RULE [assum] (tr_D th2) in
  let th3 = REWRITE_RULE [Eval_Var_SIMP; lookup_var_write; ITLIST; ml_write_rec_def] th3 in
  let th3 = CONV_RULE (DEPTH_CONV BETA_CONV) th3 in
  let th3 = REWRITE_RULE [Eval_Var_SIMP; lookup_var_write; ITLIST; FST] th3 in
  let th3 = CONV_RULE (DEPTH_CONV mlstring_EQ_CONV) th3 in
  let th3 = REWRITE_RULE [SafeVar_def] th3 in
  let lemma = UNDISCH (SPEC_ALL Eval_Eq_Recclosure) in
  let lemma_lhs = lhs (concl lemma) in
  let replace_conv tm =
    let (_,i,t) = term_match [] lemma_lhs tm in
    let th9 = INST i (INST_TYPE t lemma) in
    let recc_tm = rand tm in
    let nm = rand recc_tm in
    INST [nm, mk_var ("name", mlstring_ty)] th9 in
  CONV_RULE (DEPTH_CONV replace_conv) th3;;

(* ------------------------------------------------------------------------- *)
(* Preconditions of recursive functions (HOL4 extract_precondition_rec)      *)
(* ------------------------------------------------------------------------- *)

(* HOL4 ex_rename_bound_vars_rule: bound variables x1, x2, ...  *)
let ex_rename_bound_vars_rule th =
  let i = ref 0 in
  let is_prefix p s = String.length s >= String.length p && String.sub s 0 (String.length p) = p in
  let next_name orig =
    i := !i + 1;
    let n = "x" ^ string_of_int !i in
    if String.contains orig ' ' then n else n ^ "_" ^ orig ^ "_" in
  let next_alpha_conv tm =
    let v,_ = dest_abs tm in
    let (name,ty) = dest_var v in
    if is_prefix "x" name then failwith "" else ALPHA_CONV (mk_var (next_name name, ty)) tm in
  CONV_RULE (DEPTH_CONV next_alpha_conv) th;;

let tr_rw0 = ASSUME `!x1 x2 x3. (ml_lookup_cons x1 x2 = SOME x3) <=> T`;;
let tr_rw1 = ASSUME `!b. ml_PRECONDITION b <=> T`;;
let tr_rw2 = ASSUME `!env exp P. ml_Eval env exp P <=> T`;;

let derive_split =
  let pre_imp_rhs = rand (concl (SPEC_ALL PRE_IMP)) in
  let preimp_imp_t_rhs = rand (concl (SPEC_ALL PreImp_IMP_T)) in
  let rec derive_split tm =
    if can (term_match [] pre_imp_rhs) tm then
      let (_,m,_) = term_match [] pre_imp_rhs tm in INST m (SPEC_ALL PRE_IMP) else
    if can (term_match [] preimp_imp_t_rhs) tm then
      let (_,m,_) = term_match [] preimp_imp_t_rhs tm in INST m (SPEC_ALL PreImp_IMP_T) else
    if is_conj tm then
      let (x1,x2) = dest_conj tm in
      MATCH_MP CONJ_IMP (CONJ (derive_split x1) (derive_split x2)) else
    if is_imp tm then
      let (x1,x2) = dest_imp tm in
      let th1 = REFL x1 in
      let th2 = derive_split x2 in
      MATCH_MP IMP_SPLIT (CONJ th1 th2) else
    if is_forall tm then
      let (v,body) = dest_forall tm in
      let th = derive_split body in
      let th = CONV_RULE (RAND_CONV (tr_UNBETA_CONV v) THENC
                          RATOR_CONV (RAND_CONV (BINOP_CONV (tr_UNBETA_CONV v)))) th in
      MATCH_MP FORALL_SPLIT (GEN v th) else
    SPEC tm DEFAULT_IMP in
  derive_split;;

let tr_prerec_dbg = ref ([] : (string * string * thm * thm) list);;
let tr_split_dbg = ref (TRUTH, TRUTH);;

let extract_precondition_rec thms =
  tr_prerec_dbg := thms;
  let rephrase_pre (fname,ml_fname,def,th) =
    let (lhs,_) = dest_eq (concl def) in
    let pre_var = get_pre_var lhs fname in
    let th = REWRITE_RULE [CONTAINER_NOT_ZERO] th in
    let th = ex_rename_bound_vars_rule th in
    let th = CONV_RULE (RATOR_CONV (RAND_CONV (REWRITE_CONV [GSYM IMP_IMP]))) th in
    let tm = fst (dest_imp (concl th)) in
    let tm0 = rand (concl (REWRITE_CONV [tr_rw0] tm)) in
    let tm1 = rand (concl (REWRITE_CONV [tr_rw1] tm0)) in
    let tm2 = rand (concl (REWRITE_CONV [tr_rw0; tr_rw2; ml_PreImp_def] tm)) in
    (fname,ml_fname,def,th,pre_var,tm1,tm2) in
  let thms = map rephrase_pre thms in
  let get_subst (_,_,_,_,pre_var,_,_) =
    let pre_v = fst (strip_comb pre_var) in
    (list_mk_abs (snd (strip_comb pre_var), tr_T_tm), pre_v) in
  let ss = map get_subst thms in
  let is_true_pre (_,_,_,_,_,_,tm2) =
    rand (concl ((REWRITE_CONV [tr_rw2; ml_PreImp_def; ml_PRECONDITION_def; ml_CONTAINER_def] THENC
                  CAKE_SIMP_CONV ([ARITH_ss; FALSE_def; TRUE_def] @ tr_int_simps))
                 (vsubst ss tm2))) = tr_T_tm in
  let no_pre = forall is_true_pre thms in
  if no_pre then
    map (fun (fname,ml_fname,def,th,pre_var,tm1,tm2) ->
           let th5 = INST ss th in
           let th5 = REWRITE_RULE [PRECONDITION_EQ_CONTAINER] th5 in
           let th5 = PURE_REWRITE_RULE [ml_PreImp_def; ml_PRECONDITION_def] th5 in
           let th5 = CONV_RULE (DEPTH_CONV BETA_CONV THENC
                                RATOR_CONV (RAND_CONV (REWRITE_CONV []))) th5 in
           (fname,ml_fname,def,th5,None)) thms
  else
  let separate_pre (fname,ml_fname,def,th,pre_var,tm1,tm2) =
    let lemma = derive_split (fst (dest_imp (concl th))) in
    tr_split_dbg := (lemma, th);
    let lemma = MATCH_MP combine_lemma (CONJ lemma th) in
    let lemma = CONV_RULE (RATOR_CONV (RAND_CONV (PURE_REWRITE_CONV [ml_PRECONDITION_def])))
                  lemma in
    (fname,ml_fname,def,lemma,pre_var) in
  let thms2 = map separate_pre thms in
  let all_pre_vars = map (fun (_,_,_,_,pre_var) -> fst (strip_comb pre_var)) thms2 in
  let all_pres = list_mk_conj (map (fun (fname,ml_fname,def,lemma,pre_var) ->
      let tm = fst (dest_imp (concl lemma)) in
      let vs = subtract (frees tm) all_pre_vars in
      let ws = snd (strip_comb pre_var) in
      let ws = ws @ subtract vs ws in
      list_mk_forall (ws, mk_imp (tm, pre_var))) thms2) in
  (* HOL4 Hol_reln: the side condition is the cases theorem of an inductive *)
  (* definition; CONTAINER is removed from it                               *)
  (* the constants' names (tr_side_const_name); theorems keep HOL4's names *)
  let hol4_names = map (fun v -> fst (dest_var v)) all_pre_vars in
  let ren = map (fun v -> (mk_var (tr_side_const_name (fst (dest_var v)), type_of v), v))
                all_pre_vars in
  let all_pres = vsubst ren all_pres in
  let all_pre_vars = map fst ren in
  let names = map (fun v -> fst (dest_var v)) all_pre_vars in
  let defined = filter (fun n -> can get_const_type n) names in
  (* a session that has the side condition already (a translation file      *)
  (* loaded again): new_inductive_definition gives the stored theorems back *)
  (* for the same clauses with the constants (a benign redefinition)       *)
  let pre_def =
    if defined <> [] then
      let sub = map (fun v -> let c = mk_const (fst (dest_var v), []) in
                              (inst (type_match (type_of c) (type_of v) []) c, v)) all_pre_vars in
      (try let (_,_,cases) = new_inductive_definition (vsubst sub all_pres) in cases
       with Failure _ -> failwith ("side condition: " ^ hd defined ^
                                   " already defined with other clauses"))
    else
      let (_,_,cases) = new_inductive_definition all_pres in
      cases in
  let clean_pre_def = PURE_REWRITE_RULE [ml_CONTAINER_def] pre_def in
  (* HOL4 saves the cases theorem without CONTAINER as NAME_side_def *)
  let _ = tr_save_thm (hd hol4_names ^ "_def") clean_pre_def in
  let pre_defs = map SPEC_ALL (CONJUNCTS pre_def) in
  let thms3 = zip pre_defs thms2 in
  let get_sub (pre,(fname,ml_fname,def,lemma,pre_var)) =
    let x = fst (strip_comb pre_var) in
    let y = fst (strip_comb (lhs (concl pre))) in
    (y, x) in
  let ss = map get_sub thms3 in
  let rec list_dest_Eq_Arrow tm =
    if is_Arrow tm && is_Eq (fst (dest_Arrow tm)) then
      snd (dest_Eq (fst (dest_Arrow tm))) :: list_dest_Eq_Arrow (snd (dest_Arrow tm))
    else [] in
  let compact_pre (pre,(fname,ml_fname,def,lemma,pre_var)) =
    let vs = snd (strip_comb (lhs (concl pre))) in
    let ws = list_dest_Eq_Arrow (rator (rand (concl (tr_UNDISCH_ALL lemma)))) in
    let i = try map2 (fun x y -> (y, x)) vs ws with Failure _ -> [] in
    let c = RATOR_CONV (RAND_CONV (REWR_CONV (SYM (INST i pre)))) in
    let lemma = MATCH_MP IMP_PreImp_LEMMA (CONV_RULE c (INST ss lemma)) in
    let pre = PURE_REWRITE_RULE [ml_CONTAINER_def] pre in
    (fname,ml_fname,def,lemma,Some pre) in
  map compact_pre thms3;;

(* ------------------------------------------------------------------------- *)
(* The induction (HOL4 get_ind_thm_goal, prove_ind_thm, hide_ind_goal_rule)   *)
(* ------------------------------------------------------------------------- *)

let get_ind_thm_goal goals =
  let ind_vars = match goals with [_] -> ["P"]
                 | _ -> map (fun n -> "P" ^ string_of_int n) (0--(length goals - 1)) in
  let make_pat (name,(t,_)) =
    let p = mk_var (name, type_of t) in
    let xs,body = strip_abs t in
    (body, list_mk_comb (p, xs)) in
  let replace_pat pat x tm =
    try let (_,i,_) = term_match [] pat tm in Some (vsubst i x) with Failure _ -> None in
  let rec replace_pat_list l tm = match l with
      [] -> tm
    | (pat,x)::rest -> (match replace_pat pat x tm with Some x -> x
                        | None -> replace_pat_list rest tm) in
  let rec rec_replace_pat_list xs tm =
    match tm with
      Comb(x,y) -> replace_pat_list xs (mk_comb (rec_replace_pat_list xs x,
                                                 rec_replace_pat_list xs y))
    | Abs(x,y) -> replace_pat_list xs (mk_abs (x, rec_replace_pat_list xs y))
    | _ -> replace_pat_list xs tm in
  let pats = map make_pat (zip ind_vars goals) in
  let pss = map2 (fun (_,p) (x,(tt,_)) ->
                    let xs = fst (strip_abs x) in
                    (list_mk_forall (xs, p),
                     list_mk_forall (xs, rec_replace_pat_list pats (concl tt))))
                 pats goals in
  let ps = map (fun (a,_) -> fst (strip_comb (snd (strip_forall a)))) pss in
  let rec remove_pres tm =
    if is_forall tm then let (v,tm) = dest_forall tm in mk_forall (v, remove_pres tm)
    else if is_CONTAINER tm then rand tm
    else if is_neg tm && is_CONTAINER (rand tm) then mk_neg (rand (rand tm))
    else if is_conj tm then let (x,y) = dest_conj tm in mk_conj (remove_pres x, remove_pres y)
    else if is_imp tm then let (x,y) = dest_imp tm in mk_imp (remove_pres x, remove_pres y)
    else if is_var (fst (strip_comb tm)) then tm else tr_T_tm in
  let g = list_mk_forall (ps, mk_imp (remove_pres (list_mk_conj (map snd pss)),
                                      list_mk_conj (map fst pss))) in
  rand (concl (REWRITE_CONV [ml_CONTAINER_def] g));;

(* an induction theorem whose conclusion has a precondition (HOL4's WHILE_ind:  *)
(* ... ==> !p g x. IS_SOME (OWHILE p g x) ==> P p g x): the goal's conclusion  *)
(* becomes the theorem's (HOL4 get_custom_ind_with_pre)                        *)
let get_custom_ind_with_pre ind ind_thm_goal =
  match ind with
    None -> ind_thm_goal
  | Some ith ->
    if concl ith = tr_T_tm then ind_thm_goal else
    let has_pre =
      try is_imp (concl (SPEC_ALL (hd (CONJUNCTS (UNDISCH (SPEC_ALL ith))))))
      with Failure _ -> false in
    if not has_pre then ind_thm_goal else
    let tmg,bg = strip_forall (concl ith) in
    let tmi,bi = strip_forall ind_thm_goal in
    let (_,s,i) = term_match [] (end_itlist (curry mk_pair) tmg) (end_itlist (curry mk_pair) tmi) in
    let new_concl = snd (dest_imp (vsubst s (inst i bg))) in
    let old_hyp = fst (dest_imp bi) in
    list_mk_forall (tmi, mk_imp (old_hyp, new_concl));;

let tr_prove_ind_dbg = ref (TRUTH, `T`);;
let tr_ind_meson = ref true;;

let prove_ind_thm ind ind_thm_goal =
  match ind with
    None -> failwith "prove_ind_thm: no induction theorem"
  | Some ith ->
    tr_prove_ind_dbg := (ith, ind_thm_goal);
    if concl ith = tr_T_tm then failwith "prove_ind_thm: no induction theorem" else
    let tac =
      REPEAT GEN_TAC THEN REWRITE_TAC [TRUE_def; FALSE_def] THEN
      REPEAT (DISCH_THEN STRIP_ASSUME_TAC) THEN
      (* HOL4's match_mp_tac matches the conclusion's quantified variables  *)
      (* with terms (P v z against P (p1,p2) z after FORALL_PROD); HOL      *)
      (* Light's MATCH_MP_TAC matches the quantifiers: the goal as it is    *)
      (* first, then with the pairs split                                   *)
      (MATCH_MP_TAC ith ORELSE
       (REWRITE_TAC [FORALL_PAIR_THM; SUC_SUB1_LEMMA] THEN MATCH_MP_TAC ith)) THEN
      REWRITE_TAC [UNCURRY_SIMP] THEN REPEAT STRIP_TAC THEN
      LAST_X_ASSUM MATCH_MP_TAC THEN REPEAT STRIP_TAC THEN
      RFS [ARITH_ss] THEN RVEQ_TAC THEN RFS [ADD1; UNCURRY_SIMP; ARITH_ss] in
    let tac2 =
      REPEAT GEN_TAC THEN REWRITE_TAC [TRUE_def; FALSE_def] THEN
      REPEAT (DISCH_THEN STRIP_ASSUME_TAC) THEN
      (* HOL4's match_mp_tac matches the conclusion's quantified variables  *)
      (* with terms (P v z against P (p1,p2) z after FORALL_PROD); HOL      *)
      (* Light's MATCH_MP_TAC matches the quantifiers: the goal as it is    *)
      (* first, then with the pairs split                                   *)
      (MATCH_MP_TAC ith ORELSE
       (REWRITE_TAC [FORALL_PAIR_THM; SUC_SUB1_LEMMA] THEN MATCH_MP_TAC ith)) THEN
      REWRITE_TAC [UNCURRY_SIMP] THEN REPEAT STRIP_TAC THEN
      LAST_X_ASSUM MATCH_MP_TAC THEN REPEAT STRIP_TAC THEN
      RFS [ARITH_ss] THEN RFS [FORALL_PAIR_THM] THEN
      IMP_RES_TAC LENGTH_EQ_SUC_IMP THEN RVEQ_TAC THEN
      RFS [ADD1; UNCURRY_SIMP; ARITH_ss] THEN tr_quiet_tac (ASM_MESON_TAC []) in
    try tr_auto_prove "prove_ind_thm" (ind_thm_goal, tac)
    with Failure _ ->
      if not !tr_ind_meson then failwith "prove_ind_thm: tac2 off" else
      tr_auto_prove "prove_ind_thm" (ind_thm_goal, tac2);;

(* the induction goal as a hypothesis f_ind (:A) .. (HOL4 hide_ind_goal_rule) *)
let hide_ind_goal_rule name th1 =
  let name_ind = name ^ "_ind" in
  let ind_goal = fst (dest_imp (concl th1)) in
  let tys = tyvars (type_of (list_mk_abs (frees ind_goal, ind_goal))) in
  let tys = setify (itlist (fun t l -> union (type_vars_in_term t) l) [ind_goal] []) in
  let vs = map (fun ty -> mk_var ("x" ^ String.lowercase_ascii (dest_vartype ty),
                                  mk_fun_ty ty bool_ty)) tys in
  let ty = itlist (fun v t -> mk_fun_ty (type_of v) t) vs bool_ty in
  let c = mk_var (find_const_name name_ind, ty) in
  let def_thm = new_definition (mk_eq (list_mk_comb (c, vs), ind_goal)) in
  let args = map (fun ty -> mk_const ("UNIV", [ty, aty])) tys in
  let def_thm' = SPECL args def_thm in
  (UNDISCH (CONV_RULE (RATOR_CONV (RAND_CONV (REWR_CONV (GSYM def_thm')))) th1), def_thm);;

let tr_unroll_dbg = ref `T`;;

let translate_main_rec options thms ind original_def =
  (* the Recclosure: one (name, parameter, body) per function *)
  let mk_Recclosure_part (fname,ml_fname,def,th,v) =
    let body = let (_,e,_) = dest_Eval (concl (tr_UNDISCH_ALL th)) in e in
    mk_pair (mk_mlstring ml_fname, mk_pair (mk_mlstring (fst (dest_var v)), body)) in
  let parts = map mk_Recclosure_part thms in
  let recc = tr_mk_list (parts, type_of (hd parts)) in
  let apply_recc (fname,ml_fname,def,th,v) =
    let th = apply_Eval_Recclosure recc ml_fname v th in
    let th = clean_assumptions th in
    let th = CONV_RULE (DEPTH_CONV ETA_CONV) th in
    let th = REWRITE_RULE [] (INST [tr_cl_env, tr_env2; tr_cl_env, tr_shadow_env] th) in
    let th = CONV_RULE (RATOR_CONV (RAND_CONV (REWRITE_CONV [tr_EVAL_T_F; TRUE_def; FALSE_def])))
               th in
    let th = clean_assumptions th in
    (fname,ml_fname,def,th) in
  let thms = map apply_recc thms in
  let thms = extract_precondition_rec thms in
  let get_goal (fname,ml_fname,def,th,pre) =
    let th = REWRITE_RULE [] th in
    let hs = hyp th in
    let params = rev (rev_param_list (lhs (concl def))) in
    let c = concl (tr_UNDISCH_ALL th) in
    let hyp_tm = list_mk_abs (params, c) in
    let goal = list_mk_forall (params, c) in
    (hyp_tm, (th, (hs, goal))) in
  let goals = map get_goal thms in
  let ind_thm_goal = get_custom_ind_with_pre ind (get_ind_thm_goal goals) in
  let custom_ind_thm = ASSUME ind_thm_goal in
  let lemma = SPECL (map fst goals) custom_ind_thm in
  let lemma = REWRITE_RULE [ml_CONTAINER_def] (CONV_RULE (DEPTH_CONV BETA_CONV) lemma) in
  let lemma1 = CONV_RULE (DEPTH_CONV BETA_CONV)
                 (end_itlist CONJ (map (fun (x,(tt,_)) -> GENL (fst (strip_abs x)) tt) goals)) in
  let lemma1 = REWRITE_RULE [ml_CONTAINER_def] lemma1 in
  let g0 = concl lemma1 and g1 = fst (dest_imp (concl lemma)) in
  let lemma1 = if aconv g0 g1 then lemma1 else
    let gs = mk_imp (g0, g1) in
    tr_unroll_dbg := gs;
    let pre_defs = map (fun (_,_,_,_,pre) -> match pre with None -> TRUTH | Some t -> t) thms in
    (* HOL4's tactic step by step *)
    let lem = tr_auto_prove "unroll_pre_in_ind" (gs,
      REPEAT STRIP_TAC THEN
      TRY (MATCH_MP_TAC PreImp_LEMMA THEN
           CONV_TAC (RATOR_CONV (ONCE_REWRITE_CONV pre_defs)) THEN STRIP_TAC) THEN
      LAST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC [ml_CONTAINER_def] THEN
      REPEAT STRIP_TAC THEN
      TRY (TRY (LAST_X_ASSUM MATCH_MP_TAC) THEN ASM_REWRITE_TAC [] THEN RES_TAC THEN
           FS [] THEN NO_TAC) THEN
      (* HOL4's gvs decides the linear arithmetic of builtin preconditions *)
      (* (n < length v under ~(length v <= n)); here ASM_ARITH_TAC        *)
      TRY (GVS []) THEN TRY ASM_ARITH_TAC) in
    MP lem lemma1 in
  let th = MP lemma lemma1 in
  tr_latest_ind := ind;
  let th =
    if mem No_ind options then
      let name = let (f,_,_,_,_) = hd thms in f in
      fst (hide_ind_goal_rule name (DISCH ind_thm_goal th))
    else
      (try MP (DISCH ind_thm_goal th) (prove_ind_thm ind ind_thm_goal)
       with Failure _ ->
         let name = let (f,_,_,_,_) = hd thms in f in
         let (th2,ind_goal_def) = hide_ind_goal_rule name (DISCH ind_thm_goal th) in
         Format.print_string ("\nERROR: Unable to prove induction for " ^ name ^
           ".\n  The induction goal has been left as an assumption: prove it and use update_precondition.\n");
         th2) in
  let results = map SPEC_ALL (CONJUNCTS th) in
  let fix (th,(fname,ml_fname,def,_,pre)) =
    let th = try
        let thi = MATCH_MP IMP_PreImp_THM th in
        let thi = CONV_RULE (RATOR_CONV (RAND_CONV
                    ((match pre with Some p -> ONCE_REWRITE_CONV [p] | None -> ALL_CONV) THENC
                     REWRITE_CONV [ml_PRECONDITION_def]))) thi in
        MP thi TRUTH
      with Failure _ -> th in
    let th = tr_UNDISCH_ALL (REWRITE_RULE [ml_PreImp_def] th) in
    let th = remove_Eq th in
    let th = SIMP_EqualityType_ASSUMS th in
    (fname,ml_fname,def,th,pre) in
  (true, map fix (zip results thms));;

translate_main_rec_ref := translate_main_rec;;

let tr_rec_store_dbg = ref TRUTH;;

(* the declaration of a recursive group and its certificates *)
let translate_rec_store results =
  let (_,_,_,th0,_) = hd results in
  let lv = find (fun h -> tr_can_find_term is_Recclosure h) (hyp th0) in
  let clo = find_term is_Recclosure lv in
  let recc = rand (rator clo) in
  let curr_env = get_curr_env () in
  let ii = INST [curr_env, tr_cl_env] in
  let v_names = map (fun (f,_,_,_,_) -> find_const_name (f ^ "_v")) results in
  ml_prog_update (ml_prog_add_Dletrec ml_prog_unknown_loc recc v_names);
  let v_defs = fst (chop_list (length v_names) (get_curr_v_defs ())) in
  let new_env = get_curr_env () in
  let jj = INST [new_env, tr_env] in
  let inst_envs (fname,ml_fname,def,th,pre) =
    let th = jj (ii th) in
    let lemmas = LOOKUP_VAR_def :: map GSYM v_defs in
    let th = REWRITE_RULE lemmas (tr_D th) in
    let th = REWRITE_RULE [Eval_Var; ml_lookup_var_def] th in
    (* ?v. nsLookup env.v (Short f) = SOME v /\ P v, with the lookup computed *)
    let th = CONV_RULE (RAND_CONV (ONCE_DEPTH_CONV (CHANGED_CONV nsLookup_conv) THENC
                                   REWRITE_CONV [injectivity "option"; UNWIND_THM1])) th in
    let th = clean_assumptions th in
    let th = tr_drop_T_hyps (tr_UNDISCH_ALL th) in
    tr_rec_store_dbg := th;
    let pre_def = match pre with None -> TRUTH | Some pre_def -> pre_def in
    add_v_thms (fname,ml_fname,th,pre_def);
    tr_save_thm (fname ^ "_v_thm") th in
  let v_thm = end_itlist CONJ (map inst_envs results) in
  tr_UNDISCH_ALL (PURE_REWRITE_RULE [GSYM IMP_IMP] (DISCH_ALL v_thm));;

translate_rec_store_ref := translate_rec_store;;

(* ------------------------------------------------------------------------- *)
(* Unreachable certificates (HOL4 clean_v_thms, a finalise function) and the *)
(* translator's part of the snapshots (HOL4 pack_state and unpack_state: the *)
(* program state itself is ml_progLib's component)                           *)
(* ------------------------------------------------------------------------- *)

let clean_v_thms () =
  let inst_env = INST [get_curr_env (), tr_env] in
  let can_lookup_constant (_,_,c_tm,_,_,_) =
    try ignore (clean_assumptions_quietly (tr_D (inst_env (lookup_v_thm c_tm)))); true
    with Failure _ -> false in
  let delete_count = filter_v_thms can_lookup_constant in
  if delete_count < 1 then () else
    Format.print_string ("Removed " ^ string_of_int delete_count ^
                         " unreachable v thms from translator's state.\n");;

let () = add_finalise_function clean_v_thms;;

let () = translation_register_state "ml_translatorLib"
  (fun () ->
     let s1 = !tr_v_thms and s2 = !tr_eval_thms and s3 = !tr_cons_name_state
     and s4 = !tr_type_mod_state and s5 = !tr_type_mappings and s6 = !tr_other_types
     and s7 = !tr_preprocessor_rws and s8 = !tr_type_memory and s9 = !tr_all_eq_lemmas in
     fun () ->
       tr_v_thms := s1; tr_eval_thms := s2; tr_cons_name_state := s3;
       tr_type_mod_state := s4; tr_type_mappings := s5; tr_other_types := s6;
       tr_preprocessor_rws := s7; tr_type_memory := s8; tr_all_eq_lemmas := s9)
  (fun () ->
     tr_v_thms := []; tr_eval_thms := []; tr_cons_name_state := [];
     tr_type_mod_state := []; type_reset ());;

(* ------------------------------------------------------------------------- *)
(* The rest of HOL4's interface (ml_translatorLib.sig)                       *)
(* ------------------------------------------------------------------------- *)

let auto_prove = tr_auto_prove;;

(* HOL4 EqualityType_rule prems ty: |- EqualityType INV_prems ==> EqualityType INV_ty *)
(* from the eq lemmas                                                        *)
let EqualityType_rule prems ty =
  let mk t = mk_EqualityType (get_type_inv t) in
  let goal = if prems = [] then mk ty else mk_imp (list_mk_conj (map mk prems), mk ty) in
  prove (goal,
    REPEAT STRIP_TAC THEN
    (fun (asl,w as g) -> (MP_TAC (tr_eq_cc 0 w) THEN ASM_REWRITE_TAC []) g));;

(* HOL4 store_eq_thm: an EqualityType (or IsTypeRep) lemma proved by the user *)
let store_eq_thm th = add_eq_lemma th; th;;

(* HOL4 reset_translation: the state of a fresh process (all components) *)
let reset_translation () = translation_reset ();;

(* HOL4 clean_on_exit: clean the program state when the translation is      *)
(* finalised (HOL4 packs ml_progLib.clean_state of the state)               *)
let clean_on_exit = ref false;;
let () = add_finalise_function
  (fun () -> if !clean_on_exit then ml_prog_update ml_prog_clean_state);;

(* HOL4 flags without effect here: print_asts (print the generated code),   *)
(* generate_sigs and module_signatures (signatures are not supported, HOL4   *)
(* returns T too)                                                            *)
let print_asts = ref false;;
let generate_sigs = ref false;;
let module_signatures (_:string list) = tr_T_tm;;

(* HOL4 trace_timing_to: the times of the main steps (Some file: appended  *)
(* to the file; here also printed)                                          *)
let trace_timing_to = tr_timing_file;;

(* the translator's tables for other libraries (HOL4 get_v_thms_ref,        *)
(* get_cons_names) and HOL4's comma                                         *)
let get_v_thms_ref () = tr_v_thms;;
let get_cons_names () = !tr_cons_name_state;;
let comma l = String.concat ", " l;;
