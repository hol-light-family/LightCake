(* ========================================================================= *)
(* ml_monad_translator_interfaceLib: port of HOL4                            *)
(* translator/monadic/ml_monad_translator_interfaceLib.sml (CakeML v3479),   *)
(* the user-friendly interface to the monadic translator:                    *)
(*                                                                           *)
(*   let config =                                                            *)
(*     with_resizeable_arrays [...] (with_fixed_arrays [...]                 *)
(*       (with_refs ["ref1", `init1`; ...]                                   *)
(*         (with_exception `:exn_type` (with_state `:state_type`             *)
(*           global_state_config))));;                                       *)
(*   start_translation config;;                                              *)
(*   m_translate foo_def;;                                                   *)
(*                                                                           *)
(* (HOL4's |> is OCaml's |> too: global_state_config |> with_state ty |> ..).*)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - HOL4's set_up_monadic_translator installs the do-notation and parser    *)
(*   overloads; HOL Light has no monad syntax (definitions use st_ex_bind,   *)
(*   st_ex_return, ... as holKernel.ml does): here it only sets              *)
(*   use_full_type_names := false.                                           *)
(* - mDefine name tm and mtDefine name tm R tac (HOL4: Define with eta-     *)
(*   expanded binds, so that                                                 *)
(*   TFL sees the state in termination conditions) are cake_def and          *)
(*   cake_def_wf: the kit's recursion package handles st_ex_bind directly   *)
(*   (holKernel.ml's recursive kernel functions are defined that way).       *)
(* - with_heap_propositions, with_stdio and with_commandline (extra heap     *)
(*   propositions, e.g. TextIOProof's MONAD_IO) need the CF specifications   *)
(*   of TextIOProof and CommandLineProof (milestone M10) and HOL4's          *)
(*   apropos search of EvalM theorems: not ported (OPEN).                    *)
(* - The internal functions have the prefix mi_, the fields of config the    *)
(*   prefix cfg_ (record labels share one OCaml name space).                *)
(* ========================================================================= *)

needs "translator/monadic/ml_monad_translatorLib.ml";;

type_invention_error := true;;

let set_up_monadic_translator () = use_full_type_names := false;;

let mi_toUppers s = String.uppercase_ascii s;;
let mi_unit_ty = `:1`;;

(* HOL4 GLOBAL and LOCAL (HOL Light's lexer reads all-capital names as values) *)
type translator_mode = Global_mode | Local_mode;;

(* the internal state of the interface (HOL4 internal_state) *)
let mi_state_access_funs = ref ([] : (string * thm * thm) list);;
let mi_store_invariant_name = ref "STATE_STORE";;
let mi_store_exn_invariant_name = ref "STATE_EXN";;
let mi_exn_type_def = ref UNIT_TYPE_def;;
let mi_additional_type_theories = ref ([] : string list);;
let mi_monad_translation_params = ref (None : monadic_translation_parameters option);;
let mi_store_trans_result = ref (None : store_translation_result option);;
let mi_exn_specs = ref ([] : (thm * thm) list);;
let mi_state_type = ref mi_unit_ty;;
let mi_exn_type = ref mi_unit_ty;;

(* the user-visible configuration (HOL4 config) *)
type config =
  { cfg_mode : translator_mode;
    cfg_state_type : hol_type ref;
    cfg_exn_type : hol_type ref;
    cfg_exn_access_funs : (thm * thm) list ref;                     (* raise, handle *)
    cfg_refs : (string * thm * thm * thm) list ref;                 (* name, init, get, set *)
    cfg_fixed_arrays : (string * (int * thm) * thm * thm * thm * thm * thm) list ref;
    cfg_resizeable_arrays : (string * thm * thm * thm * thm * thm * thm * thm) list ref;
    cfg_extra_hprop : term option ref;
    cfg_extra_state_inv : (thm * thm) option ref };;

let local_state_config : config =
  { cfg_mode = Local_mode; cfg_state_type = mi_state_type; cfg_exn_type = mi_exn_type;
    cfg_exn_access_funs = ref []; cfg_refs = ref []; cfg_fixed_arrays = ref [];
    cfg_resizeable_arrays = ref []; cfg_extra_hprop = ref None; cfg_extra_state_inv = ref None };;

let global_state_config : config =
  { cfg_mode = Global_mode; cfg_state_type = mi_state_type; cfg_exn_type = mi_exn_type;
    cfg_exn_access_funs = ref []; cfg_refs = ref []; cfg_fixed_arrays = ref [];
    cfg_resizeable_arrays = ref []; cfg_extra_hprop = ref None; cfg_extra_state_inv = ref None };;

(* ------------------------------------------------------------------------- *)
(* The configuration functions                                               *)
(* ------------------------------------------------------------------------- *)

(* the state type and its monadic access functions *)
let with_state state_type (translator_config : config) =
  let accessors = define_monad_access_funs state_type in
  mi_state_type := state_type;
  mi_store_invariant_name := mi_toUppers (fst (dest_type state_type));
  mi_state_access_funs := accessors;
  translator_config;;

(* register the exception type, return its invariant definition *)
let mi_register_exception_type exn_type =
  let exn_name = mi_toUppers (fst (dest_type exn_type)) in
  let exn_type_def_name = exn_name ^ "_TYPE_def" in
  register_type `:1`;
  register_type `:A#B`;
  register_type `:(A)list`;
  register_type `:(A)option`;
  register_exn_type exn_type;
  mi_store_exn_invariant_name := exn_name;
  tr_fetch exn_type_def_name;;

(* the exception type and its raise/handle functions *)
let with_exception exn_type (translator_config : config) =
  let state_type = !(translator_config.cfg_state_type) in
  let exn_access_funs =
    if exn_type = mi_unit_ty then []
    else define_monad_exception_functions exn_type state_type in
  mi_exn_type := exn_type;
  translator_config.cfg_exn_access_funs := exn_access_funs;
  mi_exn_type_def := mi_register_exception_type exn_type;
  translator_config;;

(* state fields as references, with initial values *)
let mi_find_accessors field_name =
  try find (fun (n,_,_) -> n = field_name) !mi_state_access_funs
  with Failure _ -> failwith ("no state field " ^ field_name);;

let mi_mk_ref_init (field_name, init_value) =
  let init_var = mk_var ("ref_init_" ^ field_name, type_of init_value) in
  let (_, get, set) = mi_find_accessors field_name in
  (field_name, new_definition (mk_eq (init_var, init_value)), get, set);;

let with_refs refs (translator_config : config) =
  translator_config.cfg_refs := map mi_mk_ref_init refs;
  translator_config;;

(* state fields as fixed-size arrays: initial element, length, the        *)
(* subscript and update exceptions                                         *)
let mi_mk_farray_init (field_name, init_value, init_info, sub_exn, update_exn) =
  let init_var = mk_var ("farray_init_" ^ field_name, type_of init_value) in
  let accessors = mi_find_accessors field_name in
  let (_, get, set, len, sub, update) =
    hd (define_MFarray_manip_funs [accessors] sub_exn update_exn) in
  (field_name, (init_info, new_definition (mk_eq (init_var, init_value))),
   get, set, len, sub, update);;

let with_fixed_arrays farrays (translator_config : config) =
  translator_config.cfg_fixed_arrays := map mi_mk_farray_init farrays;
  translator_config;;

(* state fields as resizable arrays: initial array, the subscript and      *)
(* update exceptions                                                       *)
let mi_mk_rarray_init (field_name, init_value, sub_exn, update_exn) =
  let init_var = mk_var ("rarray_init_" ^ field_name, type_of init_value) in
  let accessors = mi_find_accessors field_name in
  let (_, get, set, len, sub, update, alloc) =
    hd (define_MRarray_manip_funs [accessors] sub_exn update_exn) in
  (field_name, new_definition (mk_eq (init_var, init_value)),
   get, set, len, sub, update, alloc);;

let with_resizeable_arrays rarrays (translator_config : config) =
  translator_config.cfg_resizeable_arrays := map mi_mk_rarray_init rarrays;
  translator_config;;

(* a user-defined additional state invariant *)
let with_state_invariant inv_def inv_valid (translator_config : config) =
  translator_config.cfg_extra_state_inv := Some (inv_def, inv_valid);
  translator_config;;

(* ------------------------------------------------------------------------- *)
(* Initialisation and translation functions                                  *)
(* ------------------------------------------------------------------------- *)

(* one session holds every file: the interface state and the two configs  *)
(* are reset after a start, so that the next configuration starts from     *)
(* HOL4's initial values (HOL4 runs each script in its own session)         *)
let mi_reset () =
  mi_state_type := mi_unit_ty; mi_exn_type := mi_unit_ty;
  mi_exn_type_def := UNIT_TYPE_def;
  mi_store_invariant_name := "STATE_STORE"; mi_store_exn_invariant_name := "STATE_EXN";
  mi_state_access_funs := [];
  List.iter (fun (c:config) ->
      c.cfg_exn_access_funs := []; c.cfg_refs := []; c.cfg_fixed_arrays := [];
      c.cfg_resizeable_arrays := []; c.cfg_extra_hprop := None;
      c.cfg_extra_state_inv := None) [local_state_config; global_state_config];;

let start_translation (translator_config : config) =
  let c = translator_config in
  (match c.cfg_mode with
    Global_mode ->
      let (monad_trans_params, store_trans_result, exn_specs) =
        start_static_init_fixed_store_translation
          !(c.cfg_refs) !(c.cfg_resizeable_arrays) !(c.cfg_fixed_arrays)
          !mi_store_invariant_name !(c.cfg_state_type) !mi_exn_type_def
          !(c.cfg_exn_access_funs) !mi_additional_type_theories
          !(c.cfg_extra_state_inv) !(c.cfg_extra_hprop) in
      mi_monad_translation_params := Some monad_trans_params;
      mi_store_trans_result := Some store_trans_result;
      mi_exn_specs := exn_specs
  | Local_mode ->
      let (monad_trans_params, exn_specs) =
        start_dynamic_init_fixed_store_translation
          (map (fun (n,_,g,s) -> (n,g,s)) !(c.cfg_refs))
          (map (fun (n,_,g,s,l,sb,u,a) -> (n,g,s,l,sb,u,a)) !(c.cfg_resizeable_arrays))
          (map (fun (n,_,g,s,l,sb,u) -> (n,g,s,l,sb,u)) !(c.cfg_fixed_arrays))
          !mi_store_invariant_name !(c.cfg_state_type) !mi_exn_type_def
          !(c.cfg_exn_access_funs) !mi_additional_type_theories
          (match !(c.cfg_extra_state_inv) with Some (d,_) -> Some d | None -> None) in
      mi_monad_translation_params := Some monad_trans_params;
      mi_exn_specs := exn_specs);
  mi_reset ();;

(* m_translation_extends, translate, translation_extends,                     *)
(* update_precondition, register_type, update_local_precondition,            *)
(* m_translate, m_translate_run and define_run are the libraries' own        *)
(* (HOL4 re-exports them)                                                    *)

(* the definitional entry points (HOL4 mDefine, mtDefine) *)
let mDefine (name:string) tm = ignore name; cake_def tm;;
let mtDefine (name:string) tm r tac = ignore name; cake_def_wf r tac tm;;
