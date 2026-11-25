(* ========================================================================= *)
(* ml_monadStoreLib: port of HOL4 translator/monadic/ml_monadStoreLib.sml   *)
(* (CakeML v3479).  Automation that derives lemmas about arrays and         *)
(* references for use by the monadic translator: the declarations of the    *)
(* store (references, resizable and fixed-size arrays), the store predicate  *)
(* (HOL_STORE, ...), the specifications of the access functions             *)
(* (get_X_thm, set_X_thm, X_length_thm, X_sub_thm, X_update_thm,             *)
(* X_alloc_thm), the theorem INIT_STORE that the initial store satisfies the *)
(* predicate, and STORE_EXISTS (VALID_REFS_PRED).                            *)
(*                                                                           *)
(* The entry points keep HOL4's names and argument order:                    *)
(*   translate_static_init_fixed_store  refs rarrays farrays store_name      *)
(*       state_type exn_ri_def store_pinv_opt extra_hprop                    *)
(*   translate_dynamic_init_fixed_store refs rarrays farrays store_name      *)
(*       state_type exn_ri_def store_pinv_def_opt                            *)
(* with HOL4's records monadic_translation_parameters and                    *)
(* store_translation_result.  The internal functions have the prefix ms_     *)
(* (one session holds every file); helper theorems the prefix MSLIB_.        *)
(*                                                                           *)
(* Differences from HOL4, forced by HOL Light:                               *)
(* - HOL4's derive_eval_thm (SIMP and EVAL of an evaluate goal) is only used *)
(*   on App Opref [Var (Short n)]: here it is MSLIB_eval_rel_Opref, the     *)
(*   lookup of n by ml_progLib's nsLookup_conv and the location computed by  *)
(*   ML_PROG_EVAL_CONV (as HOL4's EVAL, it leaves the NAME_refs constants of *)
(*   translated values symbolic).                                            *)
(* - HOL4's proof of INIT_STORE (prove_valid_store_X_hprop) evaluates the    *)
(*   whole store and peels the inherited cells with GC; here the inherited   *)
(*   store stays symbolic (state_refs of the state before the allocations)   *)
(*   and the new cells are matched by MSLIB_STORE_REF_HEAD and friends: the *)
(*   same theorem.                                                           *)
(* - HOL4 sorts the heap predicate with AC_Sort (PICK_REF_CONV) to put the   *)
(*   accessed reference first; here the other conjuncts keep their order and *)
(*   the rearrangement is proved by AC: the specifications are the same      *)
(*   after folding the store predicate.                                      *)
(* - HOL4's PURE_FACTS_FIRST_CONV, EXTRACT_PURE_FACTS_CONV and               *)
(*   EXTRACT_PURE_FACTS_TAC (copied from cfLetAutoLib) are only used by its  *)
(*   proof of INIT_STORE: not needed.                                        *)
(* ========================================================================= *)

needs "translator/ml_translatorLib.ml";;
needs "translator/monadic/ml_monad_translatorBase.ml";;
needs "translator/monadic/ml_monadStore.ml";;
needs "translator/monadic/ml_monad_translator.ml";;
needs "translator/monadic/monad_base/ml_monadBaseLib.ml";;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Helper theorems                                                           *)
(* ------------------------------------------------------------------------- *)

let MSLIB_eval_rel_Opref = prove
 (`!(env:v sem_env) (s:(FFI)state) n xv.
     nsLookup (sem_env_v env) (Short n) = SOME xv ==>
     eval_rel s env (App Opref [Var (Short n)])
       (state_refs_fupd (K (APPEND (state_refs s) [Refv xv])) s)
       (Loc T (LENGTH (state_refs s)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[eval_rel_def] THEN SIMP[] THEN
  MAP_EVERY EXISTS_TAC [`state_clock (s:(FFI)state)`; `state_clock (s:(FFI)state)`] THEN
  FS[evaluate_def; REVERSE; APPEND; getOpClass_def; do_app_def; store_alloc_def;
     list_result_def; state_component_equality]);;

(* the cells of the new store elements, one at a time (the index m of the  *)
(* location in the heap predicate is proved equal to the position n)        *)
let MSLIB_STORE_REF_HEAD = prove
 (`!(TYPE:A->v->bool) x v m n (H:hprop) b.
     m = n /\ TYPE x v /\ H (store2heap_aux (n + 1) b) ==>
     (REF_REL TYPE (Loc T m) x STAR H) (store2heap_aux n (CONS (Refv v) b))`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST1_TAC THEN
  MATCH_MP_TAC (REWRITE_RULE[IMP_IMP] store2heap_aux_decompose_store2) THEN
  ASM_REWRITE_TAC[REF_REL_def; SEP_EXISTS_THM; cf_HCOND_EXTRACT] THEN
  EXISTS_TAC `v:v` THEN ASM_REWRITE_TAC[store2heap_REF_SAT]);;

let MSLIB_STORE_FARRAY_HEAD = prove
 (`!(TYPE:A->v->bool) x av m n (H:hprop) b.
     m = n /\ ALL2 TYPE x av /\ H (store2heap_aux (n + 1) b) ==>
     (ARRAY_REL TYPE (Loc T m) x STAR H) (store2heap_aux n (CONS (Varray av) b))`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST1_TAC THEN
  MATCH_MP_TAC (REWRITE_RULE[IMP_IMP] store2heap_aux_decompose_store2) THEN
  ASM_REWRITE_TAC[ARRAY_REL_def; SEP_EXISTS_THM; cf_HCOND_EXTRACT] THEN
  EXISTS_TAC `av:v list` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC farray_exact_thm THEN REWRITE_TAC[]);;

let MSLIB_STORE_RARRAY_HEAD = prove
 (`!(TYPE:A->v->bool) x av m l n (H:hprop) b.
     m = n + 1 /\ l = Loc T n /\ ALL2 TYPE x av /\ H (store2heap_aux (n + 2) b) ==>
     (RARRAY_REL TYPE (Loc T m) x STAR H)
       (store2heap_aux n (CONS (Varray av) (CONS (Refv l) b)))`,
  REPEAT STRIP_TAC THEN REPEAT (FIRST_X_ASSUM SUBST1_TAC) THEN
  ONCE_REWRITE_TAC[cons_to_append] THEN
  MATCH_MP_TAC (REWRITE_RULE[IMP_IMP] store2heap_aux_decompose_store1) THEN
  REWRITE_TAC[LENGTH; ARITH_RULE `n + SUC (SUC 0) = n + 2`] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[RARRAY_REL_def; SEP_EXISTS_THM; cf_HCOND_EXTRACT] THEN
  EXISTS_TAC `av:v list` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC rarray_exact_thm THEN REWRITE_TAC[]);;

(* store elements that the predicate does not describe are garbage *)
let MSLIB_STORE_JUNK = prove
 (`!(P:hprop) n J l.
     P STAR cf_GC = P /\ P (store2heap_aux (n + LENGTH J) l) ==>
     P (store2heap_aux n (APPEND J l))`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM (fun th -> ONCE_REWRITE_TAC[SYM th]) THEN
  ONCE_REWRITE_TAC[STAR_COMM] THEN MATCH_MP_TAC MON1AUX_STAR_I THEN
  MAP_EVERY EXISTS_TAC [`store2heap_aux n (J:(v store_v)list)`;
                        `store2heap_aux (n + LENGTH (J:(v store_v)list)) l`] THEN
  ASM_REWRITE_TAC[store2heap_aux_SPLIT; SAT_GC]);;

let MSLIB_STORE_COND_HEAD = prove
 (`!b (H:hprop) s. b /\ H s ==> (set_sep_cond b STAR H) s`,
  SIMP[cf_HCOND_EXTRACT]);;

let MSLIB_STORE_END = prove
 (`!n. cf_GC (store2heap_aux n [])`,
  REWRITE_TAC[SAT_GC]);;

(* the inherited store and the ffi part are garbage *)
let MSLIB_STORE_INHERITED = prove
 (`!(H:hprop) a b.
     (H STAR cf_GC) (store2heap_aux (LENGTH a) b) ==>
     (H STAR cf_GC) (store2heap_aux 0 (APPEND a b))`,
  REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`a:(v store_v)list`; `b:(v store_v)list`]
            (INST [`H STAR cf_GC`,`H:hprop`] eliminate_inherited_references_thm)) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `cf_GC STAR (H STAR cf_GC) = (H STAR cf_GC):hprop` SUBST1_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [STAR_COMM] THEN REWRITE_TAC[GSYM STAR_ASSOC; GC_STAR_GC];
    REWRITE_TAC[]]);;

let MSLIB_STORE_ST2HEAP = prove
 (`!(H:hprop) p (s:(FFI)state).
     (H STAR cf_GC) (store2heap (state_refs s)) ==> (H STAR cf_GC) (st2heap p s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC (INST [`H STAR cf_GC`,`H:hprop`] (SPEC_ALL store2heap_eliminate_ffi_thm)) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `cf_GC STAR (H STAR cf_GC) = (H STAR cf_GC):hprop` SUBST1_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [STAR_COMM] THEN REWRITE_TAC[GSYM STAR_ASSOC; GC_STAR_GC];
    REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Constants and term constructors                                           *)
(* ------------------------------------------------------------------------- *)

let ms_hprop_ty = `:hprop`;;
let ms_ffi_proj_ty = `:(FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)`;;
let ms_ffi_state_ty = `:(FFI)state`;;
let ms_p_var = mk_var ("p", ms_ffi_proj_ty);;
let ms_emp_tm = `set_sep_emp:hprop`;;
let ms_STAR_tm = `(STAR):hprop->hprop->hprop`;;
let ms_cond_tm = `set_sep_cond:bool->hprop`;;
let ms_REF_REL_tm = `REF_REL:(A->v->bool)->v->A->hprop`;;
let ms_RARRAY_REL_tm = `RARRAY_REL:(A->v->bool)->v->A list->hprop`;;
let ms_ARRAY_REL_tm = `ARRAY_REL:(A->v->bool)->v->A list->hprop`;;
let ms_REFS_PRED_tm =
  `REFS_PRED:(A->hprop)#((FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list))->
             A->(FFI)state->bool`;;
let ms_VALID_REFS_PRED_tm =
  `VALID_REFS_PRED:(A->hprop)#((FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list))->
                   bool`;;
let ms_state_refs_tm = `state_refs:(FFI)state->(v store_v)list`;;
let ms_LENGTH_refs_tm = `LENGTH:(v store_v)list->num`;;
let ms_APPEND_refs_tm = `APPEND:(v store_v)list->(v store_v)list->(v store_v)list`;;
let ms_Opref_exp n =
  mk_comb (`App Opref`, tr_mk_list ([mk_Var (mk_Short n)], exp_ty));;
let ms_Conv_Subscript = `Conv (SOME (ExnStamp 3)) []`;;

let mk_REF_REL ty_inv r x = tr_list_mk_icomb ms_REF_REL_tm [ty_inv; r; x];;
let mk_RARRAY_REL ty_inv r x = tr_list_mk_icomb ms_RARRAY_REL_tm [ty_inv; r; x];;
let mk_ARRAY_REL ty_inv r x = tr_list_mk_icomb ms_ARRAY_REL_tm [ty_inv; r; x];;
let mk_REFS_PRED h refs p s = tr_list_mk_icomb ms_REFS_PRED_tm [mk_pair (h, p); refs; s];;
let mk_VALID_REFS_PRED hp = tr_mk_icomb ms_VALID_REFS_PRED_tm hp;;

let ms_mk_star (p,q) = list_mk_comb (ms_STAR_tm, [p; q]);;
let ms_dest_star tm =
  match tm with
    Comb(Comb(c,p),q) when is_const c && fst (dest_const c) = "STAR" -> (p,q)
  | _ -> failwith "ms_dest_star";;
let ms_is_star tm = can ms_dest_star tm;;
let ms_mk_cond b = mk_comb (ms_cond_tm, b);;
let ms_is_cond tm = is_comb tm && rator tm = ms_cond_tm;;

(* HOL4 list_dest and helperLib.list_mk *)
let rec ms_list_dest f tm =
  try let (x,y) = f tm in ms_list_dest f x @ ms_list_dest f y
  with Failure _ -> [tm];;

let rec ms_list_mk f l e =
  match l with
    [] -> e
  | [x] -> x
  | x1::xs -> f (x1, ms_list_mk f xs e);;

(* left-associated and right-associated products of heap predicates *)
let ms_mk_star_left l = end_itlist (fun x y -> ms_mk_star (y,x)) (rev l);;
let ms_mk_star_right l = end_itlist (fun x y -> ms_mk_star (x,y)) l;;

(* the left side constant of a definition (HOL4 left_const) *)
let ms_left_const th =
  fst (strip_comb (lhs (snd (strip_forall (hd (conjuncts (concl th)))))));;

(* the refs of a state (HOL4 mk_get_refs) *)
let ms_mk_get_refs state = tr_mk_icomb ms_state_refs_tm state;;

(* the type invariant of ty, registering ty if needed *)
let ms_get_type_inv_reg ty =
  try get_type_inv ty with Failure _ | Unsupported_type _ ->
    (register_type ty; get_type_inv ty);;

(* the ML name of a translated constant (HOL4 assumes the constant's name) *)
let ms_ml_name_of_const c =
  try get_ml_name (get_bare_v_thm c) with Failure _ -> fst (dest_const c);;

(* the access functions of the get/set definitions                           *)
(* get_f = \state. (M_success (f state), state)   gives  \state. f state     *)
(* set_f x = \state. (M_success (), upd state)   gives  \x state. upd state  *)
let ms_read_fun get_fun_def =
  let (state, pair) = dest_abs (rhs (concl get_fun_def)) in
  mk_abs (state, rand (fst (dest_pair pair)));;

let ms_write_fun set_fun_def =
  let (x, body) = dest_forall (concl set_fun_def) in
  let (state, pair) = dest_abs (rhs (snd (strip_forall body))) in
  mk_abs (x, mk_abs (state, snd (dest_pair pair)));;

(* ------------------------------------------------------------------------- *)
(* Allocating the store (HOL4 derive_eval_thm, create_store)                 *)
(* ------------------------------------------------------------------------- *)

(* |- eval_rel S ENV (App Opref [Var (Short n)]) S' NAME, NAME = Loc T k     *)
(* defined by ml_progLib's define_abbrev (HOL4 derive_eval_thm)             *)
(* the length of the store, as HOL4's SIMP with LENGTH_APPEND and EVAL give *)
(* it: the NAME_refs constants of translated values stay symbolic           *)
let ms_LENGTH_CONV =
  ML_PROG_EVAL_CONV THENC REWRITE_CONV [LENGTH_APPEND; LENGTH] THENC NUM_REDUCE_CONV;;

let ms_derive_eval_thm_Opref for_eval v_name ml_name =
  let env = get_curr_env () and st = get_curr_state () in
  let n = mk_mlstring ml_name in
  let lookup = nsLookup_conv (mk_nsLookup_v (env, mk_Short n)) in
  let th = MP (tr_ISPECL_NAMED ["env",env; "s",st; "n",n; "xv",rand (rhs (concl lookup))]
                 MSLIB_eval_rel_Opref) lookup in
  let len = rand (rand (concl th)) in
  let len_eq = ms_LENGTH_CONV len in
  let th = CONV_RULE (RAND_CONV (RAND_CONV (K len_eq))) th in
  let v_tm = rand (concl th) in
  let v_def = ml_prog_define_abbrev for_eval v_name v_tm in
  (PURE_ONCE_REWRITE_RULE [GSYM v_def] th, v_def);;


(* the arrays (HOL4 derive_eval_thm_ALLOCATE_EMPTY_ARRAY): Dlet NAME =     *)
(* Ref (Array.arrayEmpty ()); the abbreviations NAME_v = [] (the initial   *)
(* array value), NAME_loc (the location of the array) and NAME_ref (the     *)
(* location of the reference, the value of NAME); returns                   *)
(* (|- LIST_REL TYPE init NAME_v, NAME_loc_def, NAME_ref_def, eval theorem)  *)
let ms_derive_eval_thm_ALLOCATE_EMPTY_ARRAY v_name value_def =
  let env = get_curr_env () and s = get_curr_state () in
  let array_v_name = find_const_name (v_name ^ "_v") in
  let array_loc_name = find_const_name (v_name ^ "_loc") in
  let ref_name = find_const_name (v_name ^ "_ref") in
  let array_v_def = ml_prog_define_abbrev false array_v_name `[]:v list` in
  let elem_ty = hd (snd (dest_type (type_of (rhs (concl value_def))))) in
  let ri = get_type_inv elem_ty in
  let elem_nil = mk_const ("NIL", [elem_ty, aty]) in
  let all2 = mk_const ("ALL2", [elem_ty, aty; v_ty, `:B`]) in
  let array_v_thm = prove (list_mk_comb (all2, [ri; elem_nil; `[]:v list`]),
                           REWRITE_TAC [ALL2]) in
  let array_v_thm = PURE_REWRITE_RULE [GSYM value_def; GSYM array_v_def] array_v_thm in
  (* expand the definitions *)
  let th = tr_ISPECL_NAMED ["env",env; "s",s] ALLOCATE_EMPTY_RARRAY_evaluate in
  let th = PURE_REWRITE_RULE [GSYM array_v_def] th in
  let len_eq = ms_LENGTH_CONV (mk_comb (ms_LENGTH_refs_tm, ms_mk_get_refs s)) in
  let th = PURE_REWRITE_RULE [len_eq] th in
  let th = CONV_RULE (RAND_CONV NUM_REDUCE_CONV) th in
  (* abbreviate the array location *)
  let array_loc_def = ml_prog_define_abbrev false array_loc_name
                        (mk_comb (`Loc T`, rand (concl len_eq))) in
  let th = PURE_REWRITE_RULE [GSYM array_loc_def] th in
  (* abbreviate the reference location *)
  let ref_def = ml_prog_define_abbrev false ref_name (rand (concl th)) in
  let th = PURE_REWRITE_RULE [GSYM ref_def] th in
  (array_v_thm, array_loc_def, ref_def, th);;

(* the fixed-size arrays (HOL4 derive_eval_thm_ALLOCATE_ARRAY): Dlet NAME = *)
(* Array.array n init, after the translation of init (under its own ML     *)
(* name); the abbreviations NAME_v = REPLICATE n init_v, NAME_loc and      *)
(* init_NAME = REPLICATE n init; returns (|- LIST_REL TYPE init_NAME NAME_v *)
(* (saved as init_NAME_v_thm), NAME_loc_def, eval theorem)                 *)
let ms_derive_eval_thm_ALLOCATE_ARRAY name n init_value_def =
  let c = ms_left_const init_value_def in
  let init_value_name = fst (dest_const c) in
  next_ml_names := init_value_name :: !next_ml_names;
  let init_value_v_thm = translate init_value_def in
  let env = get_curr_env () and s = get_curr_state () in
  let xname = mk_mlstring (ms_ml_name_of_const c) in
  let lookup_assum = nsLookup_conv (mk_nsLookup_v (env, mk_Short xname)) in
  let th = tr_ISPECL_NAMED ["env",env; "s",s; "n",mk_small_numeral n; "xname",xname;
                            "xv",rand (rhs (concl lookup_assum))] ALLOCATE_ARRAY_evaluate in
  let th = MP th lookup_assum in
  (* abbreviate the constants and simplify the theorem *)
  let len_eq = ms_LENGTH_CONV (mk_comb (ms_LENGTH_refs_tm, ms_mk_get_refs s)) in
  let th = CONV_RULE (RAND_CONV (RAND_CONV (K len_eq))) th in
  let new_st = rand (rator (concl th)) in
  let array_v = rand (fst (dest_cons (rand (rand (rand (rator new_st)))))) in
  let array_v_name = find_const_name (name ^ "_v") in
  let array_v_def = ml_prog_define_abbrev false array_v_name array_v in
  let th = PURE_REWRITE_RULE [GSYM array_v_def] th in
  let array_loc_name = find_const_name (name ^ "_loc") in
  let array_loc_def = ml_prog_define_abbrev false array_loc_name (rand (concl th)) in
  let th = PURE_REWRITE_RULE [GSYM array_loc_def] th in
  (* define init_array *)
  let init_name = find_const_name ("init_" ^ name) in
  let init_v_th = MATCH_MP (SPEC (mk_small_numeral n) LIST_REL_REPLICATE) init_value_v_thm in
  let init_array = rand (rator (concl init_v_th)) in
  let array_abbrev = ml_prog_define_abbrev false init_name init_array in
  let init_v_th = PURE_REWRITE_RULE [GSYM array_abbrev; GSYM array_v_def] init_v_th in
  let _ = tr_save_thm (init_name ^ "_v_thm") init_v_th in
  Format.print_string ("Saved theorem: " ^ init_name ^ "_v_thm\n");
  (init_v_th, array_loc_def, th);;

(* create the store for a static initialisation (HOL4 create_store): the   *)
(* references, then the resizable arrays, then the fixed-size arrays; also *)
(* returns the store before the allocations                                *)
let ms_create_store refs_init_list rarrays_init_list farrays_init_list =
  let initial_state = get_curr_state () in
  let create_ref (name, def) =
    let value_def = translate def in
    let ml_name = ms_ml_name_of_const (ms_left_const def) in
    let (eval_thm, ref_def) = ms_derive_eval_thm_Opref false name ml_name in
    ml_prog_update (ml_prog_add_Dlet eval_thm name);
    (value_def, ref_def) in
  let refs_trans_results =
    map (fun (n,d,_,_) -> create_ref (n,d)) refs_init_list in
  let create_rarray (name, def) =
    let init_name = fst (dest_const (ms_left_const def)) in
    let (array_v_thm, array_loc_def, ref_def, eval_th) =
      ms_derive_eval_thm_ALLOCATE_EMPTY_ARRAY init_name def in
    ml_prog_update (ml_prog_add_Dlet eval_th name);
    (array_v_thm, array_loc_def, ref_def) in
  let rarrays_trans_results =
    map (fun (n,d,_,_,_,_,_,_) -> create_rarray (n,d)) rarrays_init_list in
  let create_farray (name, (n, def)) =
    let (array_v_thm, array_loc_def, eval_th) = ms_derive_eval_thm_ALLOCATE_ARRAY name n def in
    ml_prog_update (ml_prog_add_Dlet eval_th name);
    (array_v_thm, array_loc_def) in
  let farrays_trans_results =
    map (fun (n,d,_,_,_,_,_) -> create_farray (n,d)) farrays_init_list in
  (initial_state, refs_trans_results, rarrays_trans_results, farrays_trans_results);;

(* ------------------------------------------------------------------------- *)
(* The access functions of the store fields (HOL4                           *)
(* find_refs_access_functions, find_rarrays_access_functions,               *)
(* find_farrays_access_functions)                                            *)
(* ------------------------------------------------------------------------- *)

let ms_find_refs_access_functions refs_init_list =
  map (fun (name, get_fun, set_fun) ->
         (name, get_fun, ms_read_fun get_fun, set_fun, ms_write_fun set_fun))
      refs_init_list;;

let ms_find_rarrays_access_functions arrays_init_list =
  map (fun (name, get, set, length, sub, update, alloc) ->
         (name, get, ms_read_fun get, set, ms_write_fun set, length, sub, update, alloc))
      arrays_init_list;;

let ms_find_farrays_access_functions arrays_init_list =
  map (fun (name, get, set, length, sub, update) ->
         (name, get, ms_read_fun get, set, ms_write_fun set, length, sub, update))
      arrays_init_list;;

(* ------------------------------------------------------------------------- *)
(* The store predicate (HOL4 create_store_X_hprop)                           *)
(* ------------------------------------------------------------------------- *)

let ms_beta_app f x = rand (concl (BETA_CONV (mk_comb (f, x))));;

let ms_create_store_X_hprop refs_manip_list refs_locs rarrays_manip_list rarrays_refs_locs
      farrays_manip_list farrays_locs state_type store_hprop_name store_pinv_def_opt
      extra_hprop =
  let state_var = mk_var ("state", state_type) in
  (* references *)
  let create_ref_hprop ((_,_,get_f,_,_), ref_loc) =
    let ty = type_of (snd (dest_abs get_f)) in
    let ref_inv = ms_get_type_inv_reg ty in
    mk_REF_REL ref_inv ref_loc (ms_beta_app get_f state_var) in
  let refs_hprops = map create_ref_hprop (zip refs_manip_list refs_locs) in
  (* resizable arrays *)
  let create_rarray_hprop ((_,_,get_f,_,_,_,_,_,_), rarray_ref_loc) =
    let ty = hd (snd (dest_type (type_of (snd (dest_abs get_f))))) in
    mk_RARRAY_REL (get_type_inv ty) rarray_ref_loc (ms_beta_app get_f state_var) in
  let rarrays_hprops = map create_rarray_hprop (zip rarrays_manip_list rarrays_refs_locs) in
  (* fixed-size arrays *)
  let create_farray_hprop ((_,_,get_f,_,_,_,_,_), farray_loc) =
    let ty = hd (snd (dest_type (type_of (snd (dest_abs get_f))))) in
    mk_ARRAY_REL (get_type_inv ty) farray_loc (ms_beta_app get_f state_var) in
  let farrays_hprops = map create_farray_hprop (zip farrays_manip_list farrays_locs) in
  (* extra heap propositions, e.g. for I/O *)
  let extra_hprops =
    match extra_hprop with
      None -> []
    | Some x ->
        let vs = frees x in
        (if length vs = 1 then () else
         failwith "malformed extra_hprop: must have only one free variable");
        ms_list_dest ms_dest_star (vsubst [state_var, hd vs] x) in
  (* the conjunction of the heap predicates *)
  let all_hprops = refs_hprops @ rarrays_hprops @ farrays_hprops @ extra_hprops in
  let store_hprop = if all_hprops = [] then ms_emp_tm else ms_mk_star_left all_hprops in
  let store_hprop =
    match store_pinv_def_opt with
      Some pinv_def ->
        let pinv = ms_left_const pinv_def in
        ms_mk_star (store_hprop, ms_mk_cond (mk_comb (pinv, state_var)))
    | None -> store_hprop in
  let store_hprop = mk_abs (state_var, store_hprop) in
  (* the constant of the store predicate: its parameters are the invariants *)
  (* of the type variables of the state type, then the location variables  *)
  let loc_vars = filter is_var (refs_locs @ rarrays_refs_locs @ farrays_locs) in
  let tyvars_ref_invs = map get_type_inv (rev (tyvars (type_of store_hprop))) in
  let params = tyvars_ref_invs @ loc_vars in
  let store_hprop_type = itlist (fun p ty -> mk_fun_ty (type_of p) ty) params
                           (type_of store_hprop) in
  let store_hprop_var = mk_var (store_hprop_name, store_hprop_type) in
  let store_hprop_pred = list_mk_comb (store_hprop_var, params) in
  new_definition (mk_eq (store_hprop_pred, store_hprop));;

(* ------------------------------------------------------------------------- *)
(* The initial store satisfies the store predicate                           *)
(* (HOL4 prove_valid_store_X_hprop, prove_exists_store_X_hprop)              *)
(* ------------------------------------------------------------------------- *)

let MSLIB_STORE_JUNK1 = prove
 (`!(P:hprop) n c l.
     P STAR cf_GC = P /\ P (store2heap_aux (n + 1) l) ==>
     P (store2heap_aux n (CONS c l))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `CONS (c:v store_v) l = APPEND [c] l` SUBST1_TAC THENL
   [REWRITE_TAC[APPEND];
    MATCH_MP_TAC MSLIB_STORE_JUNK THEN
    ASM_REWRITE_TAC[LENGTH; GSYM ONE]]);;

let ms_APPEND_tm = `APPEND:(v store_v)list->(v store_v)list->(v store_v)list`;;
let ms_is_APPEND_refs tm =
  match tm with Comb(Comb(c,_),_) -> c = ms_APPEND_tm | _ -> false;;

let ms_head_is name tm = let c = fst (strip_comb tm) in is_const c && fst (dest_const c) = name;;

(* GC absorbs: P STAR cf_GC = P for a product ending in cf_GC *)
let ms_gc_absorb_tac = REWRITE_TAC[GSYM STAR_ASSOC; GC_STAR_GC];;

let ms_arith_eq m n = try Some (ARITH_RULE (mk_eq (m,n))) with Failure _ -> None;;

let ms_GC_tm = `cf_GC`;;
let ms_plus_tm = `(+):num->num->num`;;
let ms_one_tm = `1`;;

(* prove P (store2heap_aux n l) for P = R1 STAR (R2 STAR .. (Rk STAR cf_GC)), *)
(* the Ri with locations Loc T mi: each Ri matches the store cell at index  *)
(* mi, the other cells are garbage; facts give the invariants of the        *)
(* initial values, cond_tac proves the pure invariant                        *)
let rec ms_store_sat_tac facts cond_tac (asl,w as g) =
  let p = rator w and h = rand w in
  let n = rand (rator h) and l = rand h in
  if p = ms_GC_tm then ACCEPT_TAC (ISPEC h SAT_GC) g else
  let (r, _) = ms_dest_star p in
  let recurse = ms_store_sat_tac facts cond_tac in
  let fact_tac = FIRST (map MATCH_ACCEPT_TAC facts) ORELSE REWRITE_TAC[ALL2] in
  if ms_is_cond r then
    (MATCH_MP_TAC MSLIB_STORE_COND_HEAD THEN CONJ_TAC THENL [cond_tac; recurse]) g
  else if ms_is_APPEND_refs l then
    (MATCH_MP_TAC MSLIB_STORE_JUNK THEN CONJ_TAC THENL [ms_gc_absorb_tac; recurse]) g
  else if not (is_cons l) then failwith "ms_store_sat_tac: the store is too short" else
  let (c, b) = dest_cons l in
  let loc_index = try Some (rand (el 1 (snd (strip_comb r)))) with Failure _ -> None in
  let junk = MATCH_MP_TAC MSLIB_STORE_JUNK1 THEN CONJ_TAC THENL [ms_gc_absorb_tac; recurse] in
  match loc_index with
    None -> junk g
  | Some m ->
      if ms_head_is "REF_REL" r && ms_head_is "Refv" c && ms_arith_eq m n <> None then
        (MATCH_MP_TAC MSLIB_STORE_REF_HEAD THEN REPEAT CONJ_TAC THENL
           [ARITH_TAC; fact_tac; recurse]) g
      else if ms_head_is "ARRAY_REL" r && ms_head_is "Varray" c && ms_arith_eq m n <> None then
        (MATCH_MP_TAC MSLIB_STORE_FARRAY_HEAD THEN REPEAT CONJ_TAC THENL
           [ARITH_TAC; fact_tac; recurse]) g
      else if ms_head_is "RARRAY_REL" r && ms_head_is "Varray" c && is_cons b &&
              ms_head_is "Refv" (fst (dest_cons b)) &&
              ms_arith_eq m (mk_binop ms_plus_tm n ms_one_tm) <> None then
        (MATCH_MP_TAC MSLIB_STORE_RARRAY_HEAD THEN REPEAT CONJ_TAC THENL
           [ARITH_TAC; REWRITE_TAC[injectivity "v"] THEN ARITH_TAC; fact_tac; recurse]) g
      else junk g;;

let ms_prove_valid_store_X_hprop save_th refs_manip_list rarrays_manip_list
      farrays_manip_list refs_trans_results rarrays_trans_results farrays_trans_results
      current_state state_type store_X_hprop_def store_pinv_info_opt =
  let store_hprop_const = lhs (snd (strip_forall (concl store_X_hprop_def))) in
  let state_var = mk_var ("state", state_type) in
  let refs_get_funs = map (fun (_,_,x,_,_) -> x) refs_manip_list in
  let refs_init_values = map (fun (x,_) -> rand (rator (concl x))) refs_trans_results in
  let rarrays_get_funs = map (fun (_,_,x,_,_,_,_,_,_) -> x) rarrays_manip_list in
  let rarrays_init_values = map (fun (x,_,_) -> rand (rator (concl x))) rarrays_trans_results in
  let farrays_get_funs = map (fun (_,_,x,_,_,_,_,_) -> x) farrays_manip_list in
  let farrays_init_values = map (fun (x,_) -> rand (rator (concl x))) farrays_trans_results in
  let mk_get_eq (f, v) = mk_eq ((try ms_beta_app f state_var with Failure _ -> mk_comb (f, state_var)), v) in
  let hyps = map mk_get_eq (zip refs_get_funs refs_init_values @
                            zip rarrays_get_funs rarrays_init_values @
                            zip farrays_get_funs farrays_init_values) in
  let hyps_tm = if hyps = [] then `T` else list_mk_conj hyps in
  let goal = mk_REFS_PRED store_hprop_const state_var ms_p_var current_state in
  let goal = list_mk_forall ([state_var; ms_p_var], mk_imp (hyps_tm, goal)) in
  let facts = map fst refs_trans_results @ map (fun (x,_,_) -> x) rarrays_trans_results @
              map fst farrays_trans_results in
  let loc_defs = map snd refs_trans_results @
                 flat (map (fun (_,x,y) -> [x; y]) rarrays_trans_results) @
                 map snd farrays_trans_results in
  let cond_tac =
    match store_pinv_info_opt with
      Some (refs_init_list, _, _, (_, th)) ->
        let th = PURE_REWRITE_RULE [GSYM IMP_IMP] th in
        let init_values = map (fun (_,x,_,_) -> x) refs_init_list in
        FS init_values THEN IMP_RES_TAC th THEN FS[]
    | None -> ALL_TAC in
  let store_conv =
    ML_PROG_EVAL_CONV THENC REWRITE_CONV [GSYM APPEND_ASSOC; APPEND] in
  let tac =
    REPEAT GEN_TAC THEN DISCH_THEN (fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
    REWRITE_TAC[REFS_PRED_def; store_X_hprop_def] THEN CONV_TAC (DEPTH_CONV BETA_CONV) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MSLIB_STORE_ST2HEAP THEN REWRITE_TAC[store2heap_def] THEN
    CONV_TAC (RAND_CONV (RAND_CONV store_conv)) THEN
    REWRITE_TAC[GSYM STAR_ASSOC; SEP_CLAUSES] THEN PURE_REWRITE_TAC loc_defs THEN
    ms_store_sat_tac facts cond_tac in
  let th = prove (goal, tac) in
  let th = PURE_REWRITE_RULE [IMP_CLAUSES] th in
  let thm_name = "INIT_" ^ fst (dest_const (fst (strip_comb store_hprop_const))) in
  let th = if save_th then tr_save_thm thm_name th else th in
  Format.print_string ("Saved theorem __ \"" ^ thm_name ^ "\"\n");
  th;;

let ms_prove_exists_store_X_hprop save_th state_type store_hprop_name valid_store_X_hprop_thm =
  let store_hprop_const = mk_mconst (store_hprop_name, mk_fun_ty state_type ms_hprop_ty) in
  let current_state = get_curr_state () in
  let (vars, body) = strip_forall (concl valid_store_X_hprop_thm) in
  (if length vars = 2 then () else failwith "prove_exists_store_X_hprop");
  let refs_var = hd vars in
  let hyps = if is_imp body then fst (dest_imp body) else `T` in
  (* a state of the fields' initial values (HOL4 srw_tac[QI_ss][]) *)
  let witness =
    if hyps = `T` then tr_mk_arb state_type else
    let eqs = conjuncts hyps in
    let ri = record_info (fst (dest_type state_type)) in
    let value_of (_,acc,_) =
      let acc = inst (type_match (fst (dest_fun_ty (type_of acc))) state_type []) acc in
      try rhs (find (fun e -> lhs e = mk_comb (acc, refs_var)) eqs)
      with Failure _ -> tr_mk_arb (snd (dest_fun_ty (type_of acc))) in
    let args = map value_of ri.ri_fields in
    let cons = hd (mb_constructors_of state_type) in
    list_mk_comb (cons, args) in
  let th = SPECL [witness; ms_p_var] valid_store_X_hprop_thm in
  let th = if is_imp (concl th) then
             let a = fst (dest_imp (concl th)) in
             let ri = record_info (fst (dest_type state_type)) in
             MP th (EQT_ELIM (REWRITE_CONV [ri.ri_accessors] a))
           else th in
  let goal = mk_VALID_REFS_PRED (mk_pair (store_hprop_const, ms_p_var)) in
  let tac = REWRITE_TAC[VALID_REFS_PRED_def] THEN
            MAP_EVERY EXISTS_TAC [current_state; witness] THEN ACCEPT_TAC th in
  let thm_name = store_hprop_name ^ "_EXISTS" in
  let res = prove (goal, tac) in
  let res = if save_th then tr_save_thm thm_name res else res in
  Format.print_string ("Saved theorem __ \"" ^ thm_name ^ "\"\n");
  res;;

(* ------------------------------------------------------------------------- *)
(* The specifications of the access functions (HOL4 prove_store_access_specs)*)
(* ------------------------------------------------------------------------- *)

(* |- store_pred = \state. R STAR (rest), R the heap predicate of the field  *)
(* at location loc, rest the others in their order, right associated, and  *)
(* the rest as \state. rest (\state. emp if R is alone)                     *)
let ms_pick_ref store_X_hprop_def loc =
  let store_pred = lhs (snd (strip_forall (concl store_X_hprop_def))) in
  let def = SPEC_ALL store_X_hprop_def in
  let (state_var, body) = dest_abs (rhs (concl def)) in
  let hprops = ms_list_dest ms_dest_star body in
  let has_loc t = try rand (rator t) = loc with Failure _ -> false in
  let (picked, rest) = partition has_loc hprops in
  (if length picked = 1 then () else failwith "ms_pick_ref: location not found");
  let r = hd picked in
  if rest = [] then
    (def, mk_abs (state_var, ms_emp_tm), store_pred, state_var)
  else
    let new_body = ms_mk_star (r, ms_mk_star_right rest) in
    let eq = if aconv body new_body then REFL body
             else AC LSORTAUX_STAR_AC (mk_eq (body, new_body)) in
    let h_eq = TRANS def (ABS state_var eq) in
    (h_eq, mk_abs (state_var, ms_mk_star_right rest), store_pred, state_var);;

let ms_remove_assumption th =
  let assum = fst (dest_imp (concl th)) in
  MP th (EQT_ELIM (CAKE_SIMP_CONV [] assum));;

(* |- EXN_TYPE e (Conv (SOME (ExnStamp 3)) []) if the exception e is linked *)
(* to CakeML's Subscript by the exception invariant (HOL4: EVAL)            *)
let ms_subscript_eval exn_ri_def exn_ri e =
  let tm = list_mk_comb (exn_ri, [e; ms_Conv_Subscript]) in
  try
    let th = (REWRITE_CONV [exn_ri_def] THENC CAKE_SIMP_CONV []) tm in
    Some (EQT_ELIM th)
  with Failure _ -> None;;

let ms_prove_store_access_specs refs_manip_list rarrays_manip_list farrays_manip_list
      refs_locs_defs rarrays_refs_locs_defs farrays_locs_defs store_X_hprop_def
      state_type exn_ri_def store_pinv_def_opt extra_hprop =
  let exn_ri = rator (rator (lhs (snd (strip_forall (concl (hd (CONJUNCTS exn_ri_def))))))) in
  let intro_hprop th = REWRITE_RULE [GSYM store_X_hprop_def; SEP_CLAUSES] th in
  (* references *)
  let prove_ref_specs ((name, get_fun_def, read_fun, set_fun_def, write_fun), loc_def) =
    let name_v = mk_mlstring name in
    let loc = lhs (concl loc_def) in
    let ty_inv = get_type_inv (type_of (snd (dest_abs read_fun))) in
    let (h_eq, h_part, store_pred, state_var) = ms_pick_ref store_X_hprop_def loc in
    (* the pure invariant, if any, is the last conjunct *)
    let (pinv, h_part2) =
      match store_pinv_def_opt with
        Some _ ->
          let (sv, b) = dest_abs h_part in
          let hs = ms_list_dest ms_dest_star b in
          let c = last hs and others = butlast hs in
          (rator (rand c),
           mk_abs (sv, if others = [] then ms_emp_tm else ms_mk_star_right others))
      | None -> (mk_abs (state_var, `T`), h_part) in
    let rewrite_thm th =
      let th = PURE_ONCE_REWRITE_RULE [GSYM loc_def] th in
      let th = PURE_REWRITE_RULE [GSYM get_fun_def; GSYM set_fun_def; GSYM STAR_ASSOC] th in
      let th = CONV_RULE (DEPTH_CONV BETA_CONV) th in
      let th = PURE_REWRITE_RULE [H_STAR_empty; ml_monadStore_H_STAR_TRUE; GSYM h_eq] th in
      let th = PURE_REWRITE_RULE [GSYM get_fun_def; GSYM set_fun_def] th in
      let th = PURE_REWRITE_RULE [GSYM h_eq] th in
      let th = PURE_REWRITE_RULE [GSYM get_fun_def; GSYM set_fun_def] th in
      let th = PURE_REWRITE_RULE [PRECONDITION_T; IMP_CLAUSES] th in
      let hprop = fst (dest_pair (rand (concl (tr_UNDISCH_ALL (SPEC_ALL th))))) in
      (if aconv hprop store_pred then () else failwith "rewrite_thm in prove_ref_specs");
      th in
    (* read *)
    let read_spec = ISPECL [name_v; loc; ty_inv; exn_ri; h_part; read_fun] EvalM_read_heap in
    let read_spec = rewrite_thm read_spec in
    let thm_name = "get_" ^ name ^ "_thm" in
    let _ = tr_save_thm thm_name read_spec in
    Format.print_string ("Saved theorem __ \"" ^ thm_name ^ "\"\n");
    (* write *)
    let write_spec = ISPECL [name_v; loc; ty_inv; pinv; exn_ri; h_part2; read_fun; write_fun]
                       EvalM_write_heap in
    let write_spec = CONV_RULE (DEPTH_CONV BETA_CONV) (SPEC_ALL write_spec) in
    let rw_thms = match store_pinv_def_opt with Some d -> [d] | None -> [] in
    let discharge th =
      let a = fst (dest_imp (concl th)) in
      MP th (EQT_ELIM (CAKE_SIMP_CONV rw_thms a)) in
    let write_spec = discharge (discharge write_spec) in
    let write_spec = REWRITE_RULE [] (rewrite_thm write_spec) in
    let thm_name = "set_" ^ name ^ "_thm" in
    let _ = tr_save_thm thm_name write_spec in
    Format.print_string ("Saved theorem __ \"" ^ thm_name ^ "\"\n");
    (intro_hprop read_spec, intro_hprop write_spec) in
  let refs_access_thms = map prove_ref_specs (zip refs_manip_list refs_locs_defs) in
  (* arrays: the shared part *)
  let array_specs kind (name, get_fun, set_fun, length_def, sub_def, update_def, alloc_def_opt)
                  loc_def =
    let name_v = mk_mlstring name in
    let loc = lhs (concl loc_def) in
    let ty_inv = get_type_inv (hd (snd (dest_type (type_of (snd (dest_abs get_fun)))))) in
    let sub_exn = rand (rhs (concl sub_def)) in
    let update_exn = rand (rhs (concl update_def)) in
    let eval_sub_rexp = hol2deep sub_exn in
    let sub_rexp = tr_cert_exp eval_sub_rexp in
    let eval_update_rexp = hol2deep update_exn in
    let update_rexp = tr_cert_exp eval_update_rexp in
    let (h_eq, h_part, _, _) = ms_pick_ref store_X_hprop_def loc in
    let defs = [length_def; sub_def; update_def] @
               (match alloc_def_opt with Some d -> [d] | None -> []) in
    let rewrite_thm th =
      let th = PURE_ONCE_REWRITE_RULE [GSYM loc_def] th in
      let th = PURE_REWRITE_RULE (map GSYM defs) th in
      let th = CONV_RULE (DEPTH_CONV BETA_CONV) th in
      PURE_REWRITE_RULE [GSYM h_eq] th in
    let (th_length, th_sub_sub, th_sub_handle, th_upd_sub, th_upd_handle) =
      if kind = "R" then
        (EvalM_R_Marray_length, EvalM_R_Marray_sub_subscript, EvalM_R_Marray_sub_handle,
         EvalM_R_Marray_update_subscript, EvalM_R_Marray_update_handle)
      else
        (EvalM_F_Marray_length, EvalM_F_Marray_sub_subscript, EvalM_F_Marray_sub_handle,
         EvalM_F_Marray_update_subscript, EvalM_F_Marray_update_handle) in
    (* length *)
    let length_thm = rewrite_thm (ISPECL [name_v; loc; ty_inv; exn_ri; h_part; get_fun] th_length) in
    let thm_name = name ^ "_length_thm" in
    let _ = tr_save_thm thm_name length_thm in
    Format.print_string ("Saved theorem __ \"" ^ thm_name ^ "\"\n");
    (* sub *)
    let sub_thm =
      match ms_subscript_eval exn_ri_def exn_ri sub_exn with
        Some subscript_eval ->
          let th = SPEC_ALL (ISPECL [name_v; loc; ty_inv; exn_ri; h_part; get_fun; sub_exn]
                               th_sub_sub) in
          rewrite_thm (UNDISCH (UNDISCH (MP th subscript_eval)))
      | None ->
          let th = SPEC_ALL (ISPECL [name_v; loc; ty_inv; exn_ri; h_part; get_fun; sub_exn;
                                     sub_rexp] th_sub_handle) in
          let th = UNDISCH (UNDISCH (UNDISCH (rewrite_thm th))) in
          MP th eval_sub_rexp in
    let thm_name = name ^ "_sub_thm" in
    let _ = tr_save_thm thm_name sub_thm in
    Format.print_string ("Saved theorem __ \"" ^ thm_name ^ "\"\n");
    (* update *)
    let update_thm =
      match ms_subscript_eval exn_ri_def exn_ri update_exn with
        Some subscript_eval ->
          let th = SPEC_ALL (ISPECL [name_v; loc; ty_inv; exn_ri; h_part; get_fun; set_fun;
                                     update_exn] th_upd_sub) in
          let th = UNDISCH (UNDISCH th) in
          let th = ms_remove_assumption (ms_remove_assumption (MP th subscript_eval)) in
          rewrite_thm (tr_UNDISCH_ALL th)
      | None ->
          let th = SPEC_ALL (ISPECL [name_v; loc; ty_inv; exn_ri; h_part; get_fun; set_fun;
                                     update_exn; update_rexp] th_upd_handle) in
          let th = UNDISCH (UNDISCH th) in
          let th = UNDISCH (ms_remove_assumption (ms_remove_assumption th)) in
          rewrite_thm (UNDISCH (MP th eval_update_rexp)) in
    let thm_name = name ^ "_update_thm" in
    let _ = tr_save_thm thm_name update_thm in
    Format.print_string ("Saved theorem __ \"" ^ thm_name ^ "\"\n");
    (* alloc *)
    let alloc_thm =
      match alloc_def_opt with
        None -> None
      | Some _ ->
          let th = SPEC_ALL (ISPECL [name_v; loc; ty_inv; exn_ri; h_part; get_fun; set_fun]
                               EvalM_R_Marray_alloc) in
          let th = UNDISCH (rewrite_thm th) in
          let th = ms_remove_assumption (ms_remove_assumption th) in
          let thm_name = name ^ "_alloc_thm" in
          let _ = tr_save_thm thm_name th in
          Format.print_string ("Saved theorem __ \"" ^ thm_name ^ "\"\n");
          Some th in
    (intro_hprop length_thm, intro_hprop sub_thm, intro_hprop update_thm,
     match alloc_thm with Some th -> Some (intro_hprop th) | None -> None) in
  let prove_rarray_specs ((name, _, get_fun, _, set_fun, length_def, sub_def, update_def,
                           alloc_def), loc_def) =
    match array_specs "R" (name, get_fun, set_fun, length_def, sub_def, update_def,
                           Some alloc_def) loc_def with
      (a, b, c, Some d) -> (a, b, c, d)
    | _ -> failwith "prove_rarray_specs" in
  let rarrays_access_thms = map prove_rarray_specs (zip rarrays_manip_list rarrays_refs_locs_defs) in
  let prove_farray_specs ((name, _, get_fun, _, set_fun, length_def, sub_def, update_def),
                          loc_def) =
    let (a, b, c, _) = array_specs "F" (name, get_fun, set_fun, length_def, sub_def,
                                        update_def, None) loc_def in
    (a, b, c) in
  let farrays_access_thms = map prove_farray_specs (zip farrays_manip_list farrays_locs_defs) in
  (refs_access_thms, rarrays_access_thms, farrays_access_thms);;

(* ------------------------------------------------------------------------- *)
(* The entry points (HOL4 translate_dynamic_init_fixed_store,                *)
(* translate_static_init_fixed_store)                                        *)
(* ------------------------------------------------------------------------- *)

type monadic_translation_parameters =
  { store_pred_def : thm;
    refs_specs : (thm * thm) list;
    rarrays_specs : (thm * thm * thm * thm) list;
    farrays_specs : (thm * thm * thm) list };;

type store_translation_result =
  { refs_init_values : thm list;
    refs_locations : thm list;
    rarrays_init_values : thm list;
    farrays_init_values : thm list;
    rarrays_locations : thm list;
    farrays_locations : thm list;
    store_pred_validity : thm;
    store_pred_exists_thm : thm };;

let v_ty_tm = `:v`;;

(* the locations of a dynamically initialised store are variables init_NAME *)
let ms_create_locs_variables refs_manip_list rarrays_manip_list farrays_manip_list =
  let mk names = map (fun x -> mk_var ("init_" ^ x, v_ty)) names in
  (mk (map (fun (n,_,_) -> n) refs_manip_list),
   mk (map (fun (n,_,_,_,_,_,_) -> n) rarrays_manip_list),
   mk (map (fun (n,_,_,_,_,_) -> n) farrays_manip_list));;

let translate_dynamic_init_fixed_store refs_manip_list rarrays_manip_list farrays_manip_list
      store_hprop_name state_type exn_ri_def store_pinv_def_opt =
  let (refs_locs, rarrays_refs_locs, farrays_locs) =
    ms_create_locs_variables refs_manip_list rarrays_manip_list farrays_manip_list in
  let refs_manip_list = ms_find_refs_access_functions refs_manip_list in
  let rarrays_manip_list = ms_find_rarrays_access_functions rarrays_manip_list in
  let farrays_manip_list = ms_find_farrays_access_functions farrays_manip_list in
  let extra_hprop = None in
  let store_X_hprop_def =
    ms_create_store_X_hprop refs_manip_list refs_locs rarrays_manip_list rarrays_refs_locs
      farrays_manip_list farrays_locs state_type store_hprop_name store_pinv_def_opt
      extra_hprop in
  (* dummy rewriting rules for the locations *)
  let refs_locs_defs = map REFL refs_locs in
  let rarrays_refs_locs_defs = map REFL rarrays_refs_locs in
  let farrays_locs_defs = map REFL farrays_locs in
  let (refs_access_thms, rarrays_access_thms, farrays_access_thms) =
    ms_prove_store_access_specs refs_manip_list rarrays_manip_list farrays_manip_list
      refs_locs_defs rarrays_refs_locs_defs farrays_locs_defs store_X_hprop_def
      state_type exn_ri_def store_pinv_def_opt extra_hprop in
  { store_pred_def = store_X_hprop_def;
    refs_specs = refs_access_thms;
    rarrays_specs = rarrays_access_thms;
    farrays_specs = farrays_access_thms };;

let translate_static_init_fixed_store refs_init_list rarrays_init_list farrays_init_list
      store_hprop_name state_type exn_ri_def store_pinv_opt extra_hprop =
  (* create the store *)
  let (_, refs_trans_results, rarrays_trans_results, farrays_trans_results) =
    ms_create_store refs_init_list rarrays_init_list farrays_init_list in
  (* create the store predicate *)
  let refs_manip_list =
    ms_find_refs_access_functions (map (fun (x,_,y,z) -> (x,y,z)) refs_init_list) in
  let rarrays_manip_list =
    ms_find_rarrays_access_functions
      (map (fun (x1,_,x2,x3,x4,x5,x6,x7) -> (x1,x2,x3,x4,x5,x6,x7)) rarrays_init_list) in
  let farrays_manip_list =
    ms_find_farrays_access_functions
      (map (fun (x1,_,x2,x3,x4,x5,x6) -> (x1,x2,x3,x4,x5,x6)) farrays_init_list) in
  let refs_locs_defs = map snd refs_trans_results in
  let rarrays_refs_locs_defs = map (fun (_,_,x) -> x) rarrays_trans_results in
  let farrays_locs_defs = map snd farrays_trans_results in
  let refs_locs = map (lhs o concl) refs_locs_defs in
  let rarrays_refs_locs = map (lhs o concl) rarrays_refs_locs_defs in
  let farrays_locs = map (lhs o concl) farrays_locs_defs in
  let store_pinv_def_opt = match store_pinv_opt with Some (d,_) -> Some d | None -> None in
  let store_X_hprop_def =
    ms_create_store_X_hprop refs_manip_list refs_locs rarrays_manip_list rarrays_refs_locs
      farrays_manip_list farrays_locs state_type store_hprop_name store_pinv_def_opt
      extra_hprop in
  (* the access specifications *)
  let (refs_access_thms, rarrays_access_thms, farrays_access_thms) =
    ms_prove_store_access_specs refs_manip_list rarrays_manip_list farrays_manip_list
      refs_locs_defs rarrays_refs_locs_defs farrays_locs_defs store_X_hprop_def
      state_type exn_ri_def store_pinv_def_opt extra_hprop in
  (* the validity and existential theorems *)
  let current_state = get_curr_state () in
  let store_pinv_info_opt =
    match store_pinv_opt with
      Some x -> Some (refs_init_list, rarrays_init_list, farrays_init_list, x)
    | None -> None in
  let valid_store_X_hprop_thm =
    if extra_hprop <> None then TRUTH else
    ms_prove_valid_store_X_hprop true refs_manip_list rarrays_manip_list farrays_manip_list
      refs_trans_results rarrays_trans_results farrays_trans_results current_state
      state_type store_X_hprop_def store_pinv_info_opt in
  let exists_store_X_hprop_thm =
    if extra_hprop <> None then TRUTH else
    ms_prove_exists_store_X_hprop true state_type store_hprop_name valid_store_X_hprop_thm in
  let (refs_values, refs_locs) = unzip refs_trans_results in
  let (rarrays_values, rarrays_locs) =
    unzip (map (fun (x,_,y) -> (x,y)) rarrays_trans_results) in
  let (farrays_values, farrays_locs) = unzip farrays_trans_results in
  ({ store_pred_def = store_X_hprop_def;
     refs_specs = refs_access_thms;
     rarrays_specs = rarrays_access_thms;
     farrays_specs = farrays_access_thms },
   { refs_init_values = refs_values;
     refs_locations = refs_locs;
     rarrays_init_values = rarrays_values;
     rarrays_locations = rarrays_locs;
     farrays_init_values = farrays_values;
     farrays_locations = farrays_locs;
     store_pred_validity = valid_store_X_hprop_thm;
     store_pred_exists_thm = exists_store_X_hprop_thm });;
