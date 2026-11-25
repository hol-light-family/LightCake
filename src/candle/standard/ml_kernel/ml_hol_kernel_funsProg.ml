(* ========================================================================= *)
(* ml_hol_kernel_funsProg: port of HOL4 candle/standard/ml_kernel/           *)
(* ml_hol_kernel_funsProgScript.sml (CakeML v3479).  Apply the monadic       *)
(* translator to the Candle kernel to generate the deeply embedded CakeML    *)
(* code for the kernel.  As a side effect, the monadic translator proves     *)
(* certificate theorems that state a formal connection between the          *)
(* generated code and the input HOL functions.                               *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - Decision D5 (user, 2026-11-24): the kernel functions that HOL4          *)
(*   translates from the PMATCH restatements of holKernelPmatch (raconv,     *)
(*   is_var, is_const, is_abs, is_comb, vfree_in, is_eq, dest_var,           *)
(*   dest_const, dest_comb, dest_abs, rator, rand, dest_eq, mk_abs,          *)
(*   codomain, type_of, mk_comb, EQ_MP, TRANS, MK_COMB, ABS, BETA) are       *)
(*   translated from their holKernel definitions: the translator compiles    *)
(*   the kit's case constants into nested one-level Mats where HOL4's        *)
(*   PMATCH route gives one Mat with nested patterns.  Names, module         *)
(*   structure and order of the declarations are HOL4's.                     *)
(* - HOL4's types term and type are holSyntax's hol_term and hol_type       *)
(*   (CakeML type names term and type, constructors Var, Const, Comb, Abs,  *)
(*   Tyvar, Tyapp, as in HOL4); the kernel's constants have the prefix       *)
(*   holKernel_ (holKernel.ml).                                              *)
(* - HOL4's check [`v`] def is runtime_check_check ["v"] def                 *)
(*   (runtime_checkLib.ml); HOL4's Q.SPEC `n` before a check is SPEC of a    *)
(*   variable n, as in HOL4.                                                 *)
(* - The generated theorems (FOO_TYPE_def, NAME_v_def, NAME_v_thm, ...) are *)
(*   bound at the end of the file under their HOL4 names (HOL4 saves them   *)
(*   in the theory), for the Candle proofs.                                  *)
(* - Tuple matches (HOL4 case (t1,t2) of .., in type_compare, term_compare  *)
(*   and holSyntax's orda and term_union): the kit compiles them column by    *)
(*   column, so the code tests t1 and t2 directly; HOL4's case compiler      *)
(*   probably gives pair_CASE (t1,t2) .. and a Mat on the tuple (to be      *)
(*   compared with a HOL4 build).                                            *)
(* - The kit stores no induction theorem for holSyntaxExtra's itlist and     *)
(*   holKernel's rev_assocd (recursion on the second argument): they are     *)
(*   proved here in HOL4's TFL form (CAN1AUX_itlist_ind,                     *)
(*   CAN1AUX_rev_assocd_ind) and registered with add_ind_thm.                *)
(* - HOL4's Overload abs_v = abs_1_v is an interface entry.                  *)
(* - HOL4's temp_delsimps, hide "abs" and the printing settings at the end   *)
(*   only affect HOL4's simplifier, parser and printer.                      *)
(* - Local helpers that are not HOL4 theorems are CAN1AUX_ (OCaml values     *)
(*   can1aux_).                                                              *)
(* ========================================================================= *)

needs "basis/basisProg.ml";;
needs "translator/monadic/ml_monad_translatorLib.ml";;
needs "candle/standard/monadic/holKernel.ml";;
needs "candle/standard/syntax/holAxiomsSyntax.ml";;
needs "candle/standard/ml_kernel/runtime_checkLib.ml";;

type_invention_error := true;;

translation_extends "basisProg";;

use_full_type_names := false;;

(* HOL4 Type state = ``:'ffi semanticPrimitives$state`` *)
new_type_abbrev("ml_hol_kernel_funsProg_state",`:(FFI)state`);;

(* construct type refinement invariants *)

register_type `:hol_type`;;
register_type `:hol_term`;;
register_type `:thm`;;

(* check :hol_type is known to be an EqualityType *)
let EqualityType_TYPE = EqualityType_rule [] `:hol_type`;;

register_exn_type `:hol_exn`;;
register_type `:update`;;
let HOL_EXN_TYPE_def = tr_fetch "HOL_EXN_TYPE_def";;

(* add an abbreviation mapping hol_type to type for HOL Light *)

ml_prog_update
  (ml_prog_add_Dtabbrev ml_prog_unknown_loc `[]:mlstring list` `implode "hol_type"`
     `Atapp [] (Short (implode "type"))`);;

ml_prog_update (ml_prog_open_module "Kernel");;

ml_prog_update ml_prog_open_local_block;;

(* Initialize the translation *)

let init_type_constants_def = new_definition
  `init_type_constants = [(implode "bool",0); (implode "fun",2:num)]`;;

let init_term_constants_def = new_definition
  `init_term_constants =
     [(implode "=",
       Tyapp (implode "fun")
         [Tyvar (implode "A");
          Tyapp (implode "fun")
            [Tyvar (implode "A");
             Tyapp (implode "bool") []]])]`;;

let init_axioms_def = new_definition
  `init_axioms = []:thm list`;;

(* HOL4 [local] *)
let init_axioms_alt = prove
 (CASE_TERM
  `init_axioms =
     match [Sequent [] (hol_Var (implode "") (Tyvar (implode "")))] with
       [] -> []
     | CONS _ xs -> xs`,
  REWRITE_TAC[init_axioms_def; list_CASE]);;

let init_context_def = new_definition
  (mk_eq (`init_context:update list`, rhs (concl init_ctxt_def)));;

let can1aux_refs_init_list =
  ["the_type_constants", init_type_constants_def, holKernel_get_the_type_constants_def,
     holKernel_set_the_type_constants_def;
   "the_term_constants", init_term_constants_def, holKernel_get_the_term_constants_def,
     holKernel_set_the_term_constants_def;
   "the_axioms", init_axioms_alt, holKernel_get_the_axioms_def, holKernel_set_the_axioms_def;
   "the_context", init_context_def, holKernel_get_the_context_def,
     holKernel_set_the_context_def];;

let can1aux_rarrays_init_list = ([] : (string * thm * thm * thm * thm * thm * thm * thm) list);;
let can1aux_farrays_init_list = ([] : (string * (int * thm) * thm * thm * thm * thm * thm) list);;

let can1aux_raise_functions = [holKernel_raise_Failure_def; holKernel_raise_Clash_def];;
let can1aux_handle_functions = [holKernel_handle_Failure_def; holKernel_handle_Clash_def];;
let can1aux_exn_functions = zip can1aux_raise_functions can1aux_handle_functions;;

let can1aux_store_hprop_name = "HOL_STORE";;
let can1aux_state_type = `:hol_refs`;;
let can1aux_exn_ri_def = HOL_EXN_TYPE_def;;

let (can1aux_monad_parameters, can1aux_store_translation, can1aux_exn_specs) =
  start_static_init_fixed_store_translation can1aux_refs_init_list
                                            can1aux_rarrays_init_list
                                            can1aux_farrays_init_list
                                            can1aux_store_hprop_name
                                            can1aux_state_type
                                            can1aux_exn_ri_def
                                            can1aux_exn_functions
                                            []
                                            None
                                            None;;

(* Translate type-checking code from runtime_check *)

let _ = translate check_ty_def;;
let _ = translate check_tm_def;;
let _ = translate check_thm_def;;
let _ = translate check_ty_ty_def;;
let _ = translate check_tm_tm_def;;

(* ------------------------------------------------------------------------- *)
(* --- perform translation ---                                               *)
(* ------------------------------------------------------------------------- *)

(* HOL4 leaves the translation of mlstring's explode_aux, explode and       *)
(* strcat commented out here (TODO: want builtin support for these)         *)

let _ = translate string_lt_def;;
let _ = translate string_le_def;;
let _ = translate TO_of_LinearOrder;;

(* -- *)
let _ = translate (REWRITE_RULE [MEMBER_INTRO] holKernel_subset_def);;
let _ = translate (REWRITE_RULE [MEMBER_INTRO] subtract_def);;
let _ = translate (REWRITE_RULE [MEMBER_INTRO] hol_insert_def);;
(* HOL4's TFL gives itlist_ind (holSyntaxExtra); the kit stores no         *)
(* induction theorem for this definition                                    *)
let CAN1AUX_itlist_ind = prove
 (`!P. (!(f:A->B->B) (l:A list) (b:B). (!h t. l = CONS h t ==> P f t b) ==> P f l b)
       ==> !x1 x2 x3. P x1 x2 x3`,
  GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_MESON_TAC[NOT_CONS_NIL; CONS_11]);;
add_ind_thm "itlist" CAN1AUX_itlist_ind;;
let _ = translate itlist_def;;
let _ = translate hol_union_def;;

ml_prog_update ml_prog_open_local_in_block;;

let _ = translate (runtime_check_check ["v"] holKernel_mk_vartype_def);;
let _ = translate (runtime_check_check ["t"] holKernel_is_type_def);;
let _ = translate (runtime_check_check ["t"] holKernel_is_vartype_def);;

ml_prog_update ml_prog_open_local_block;;

(* HOL4's TFL gives rev_assocd_ind; the kit stores no induction theorem    *)
(* for this definition                                                      *)
let CAN1AUX_rev_assocd_ind = prove
 (`!P. (!(a:B) (l:(A#B)list) (d:A).
          (!x y l1. l = CONS (x,y) l1 /\ ~(y = a) ==> P a l1 d) ==> P a l d)
       ==> !x1 x2 x3. P x1 x2 x3`,
  GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN ASM_MESON_TAC[NOT_CONS_NIL; CONS_11; PAIR]);;
add_ind_thm "holKernel_rev_assocd" CAN1AUX_rev_assocd_ind;;
let _ = translate holKernel_rev_assocd_def;;

let call_type_subst_def = new_definition
  `call_type_subst i ty = holKernel_type_subst i ty`;;
let _ = cake_add_simps [call_type_subst_def];;
next_ml_names := ["type_subst_aux"];;
let _ = translate holKernel_type_subst_def;;
next_ml_names := ["type_subst"];;

ml_prog_update ml_prog_open_local_in_block;;

let _ = translate (runtime_check_check ["i"; "ty"] call_type_subst_def);;

ml_prog_update ml_prog_open_local_block;;

let _ = translate holKernel_alphavars_def;;
(* D5: HOL4 translates holKernelPmatch's raconv_def *)
let _ = translate holKernel_raconv_def;;

let _ = translate (runtime_check_check ["tm1"; "tm2"] holKernel_aconv_def);;

ml_prog_update ml_prog_open_local_in_block;;

(* D5: HOL4 translates holKernelPmatch's is_var_def, is_const_def,         *)
(* is_abs_def and is_comb_def                                               *)
let _ = translate (runtime_check_check ["x"] holKernel_is_var_def);;
let _ = translate (runtime_check_check ["x"] holKernel_is_const_def);;
let _ = translate (runtime_check_check ["x"] holKernel_is_abs_def);;
let _ = translate (runtime_check_check ["x"] holKernel_is_comb_def);;
let _ = translate (runtime_check_check ["v"; "ty"] holKernel_mk_var_def);;

ml_prog_update ml_prog_open_local_block;;

let call_frees_def = new_definition
  `call_frees tm = hol_frees tm`;;
let _ = cake_add_simps [call_frees_def];;
next_ml_names := ["frees_aux"];;
let _ = translate hol_frees_def;;
next_ml_names := ["frees"];;

let call_freesin_def = new_definition
  `call_freesin acc tm = holKernel_freesin acc tm`;;
let _ = cake_add_simps [call_freesin_def];;
next_ml_names := ["freesin_aux"];;
let _ = translate (REWRITE_RULE [MEMBER_INTRO] holKernel_freesin_def);;
next_ml_names := ["freesin"];;

let call_vfree_in_def = new_definition
  `call_vfree_in v tm = vfree_in v tm`;;
let _ = cake_add_simps [call_vfree_in_def];;
next_ml_names := ["vfree_in_aux"];;
(* D5: HOL4 translates holKernelPmatch's vfree_in_def *)
let _ = translate vfree_in_def;;
next_ml_names := ["vfree_in"];;

let call_tyvars_def = new_definition
  `call_tyvars x = holKernel_tyvars x`;;
let _ = cake_add_simps [call_tyvars_def];;
next_ml_names := ["tyvars_aux"];;
let _ = translate holKernel_tyvars_def;;
next_ml_names := ["tyvars"];;

let call_type_vars_in_term_def = new_definition
  `call_type_vars_in_term tm = holKernel_type_vars_in_term tm`;;
let _ = cake_add_simps [call_type_vars_in_term_def];;
next_ml_names := ["type_vars_in_term_aux"];;
let _ = translate holKernel_type_vars_in_term_def;;
next_ml_names := ["type_vars_in_term"];;

let call_variant_def = new_definition
  `call_variant avoid v = variant avoid v`;;
let _ = cake_add_simps [call_variant_def];;
next_ml_names := ["variant_aux"];;
let _ = translate variant_def;;
next_ml_names := ["variant"];;

let _ = translate holKernel_vsubst_aux_def;;

ml_prog_update ml_prog_open_local_in_block;;

let _ = translate (runtime_check_check ["v"; "tm"] call_vfree_in_def);;
let _ = translate (runtime_check_check ["acc"; "tm"] call_freesin_def);;
let _ = translate (runtime_check_check ["tm"] call_frees_def);;
let _ = translate (runtime_check_check ["tml"] holKernel_freesl_def);;
let _ = translate (runtime_check_check ["x"] call_tyvars_def);;
let _ = translate (runtime_check_check ["tm"] call_type_vars_in_term_def);;
let _ = translate (runtime_check_check ["avoid"; "v"] call_variant_def);;

ml_prog_update ml_prog_open_local_block;;

(* D5: HOL4 translates holKernelPmatch's is_eq_def *)
let _ = translate (runtime_check_check ["tm"] holKernel_is_eq_def);;

ml_prog_update ml_prog_open_local_in_block;;

let _ = translate holKernel_dest_thm_def;;
let _ = translate holKernel_hyp_def;;
let _ = translate holKernel_concl_def;;

ml_prog_update ml_prog_open_local_block;;

let type_compare_def = cake_def
  `(type_compare t1 t2 =
      match (t1,t2) with
        (Tyvar x1,Tyvar x2) -> mlstring_compare x1 x2
      | (Tyvar x1,Tyapp _ _) -> LESS
      | (Tyapp x1 a1,Tyvar _) -> GREATER
      | (Tyapp x1 a1,Tyapp x2 a2) ->
          (match mlstring_compare x1 x2 with
             EQUAL -> type_list_compare a1 a2
           | other -> other)) /\
   (type_list_compare ts1 ts2 =
      match (ts1,ts2) with
        ([],[]) -> EQUAL
      | ([],CONS t2 ts2) -> LESS
      | (CONS t1 ts1,[]) -> GREATER
      | (CONS t1 ts1,CONS t2 ts2) ->
          (match type_compare t1 t2 with
             EQUAL -> type_list_compare ts1 ts2
           | other -> other))`;;

let type_compare_ind = cake_ind "type_compare";;

(* HOL4: val type_cmp_thm (an SML value; holSyntaxExtra's type_cmp_thm is  *)
(* another theorem)                                                         *)
let CAN1AUX_type_cmp_thm = prove
 (`(type_cmp = type_compare) /\
   (list_compare type_cmp = type_list_compare)`,
  REWRITE_TAC[FUN_EQ_THM] THEN MATCH_MP_TAC type_compare_ind THEN CONJ_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THENL
   [ONCE_REWRITE_TAC[type_cmp_thm] THEN ONCE_REWRITE_TAC[type_compare_def] THEN
    REPEAT TOP_CASE_TAC THEN RFS[pair_cmp_def];
    ONCE_REWRITE_TAC[type_compare_def] THEN REPEAT TOP_CASE_TAC THEN
    RFS[list_compare_def]]);;
let CAN1AUX_type_cmp_thm = CONJUNCT1 CAN1AUX_type_cmp_thm;;

(* HOL4 add_preferred_thy "-" with Theorem type_cmp_ind *)
let ml_hol_kernel_funsProg_type_cmp_ind =
  REWRITE_RULE [GSYM CAN1AUX_type_cmp_thm] type_compare_ind;;
add_ind_thm "type_cmp" ml_hol_kernel_funsProg_type_cmp_ind;;
let _ = translate (REWRITE_RULE [GSYM CAN1AUX_type_cmp_thm] type_compare_def);;

let term_compare_def = cake_def
  `term_compare t1 t2 =
     match (t1,t2) with
       (hol_Var x1 ty1,hol_Var x2 ty2) ->
         (match mlstring_compare x1 x2 with
            LESS -> LESS
          | EQUAL -> type_cmp ty1 ty2
          | GREATER -> GREATER)
     | (hol_Var x1 ty1,hol_Const v52 v53) -> LESS
     | (hol_Var x1 ty1,hol_Comb v54 v55) -> LESS
     | (hol_Var x1 ty1,hol_Abs v56 v57) -> LESS
     | (hol_Const x1' ty1',hol_Var v66 v67) -> GREATER
     | (hol_Const x1' ty1',hol_Const x2' ty2') ->
         (match mlstring_compare x1' x2' with
            LESS -> LESS
          | EQUAL -> type_cmp ty1' ty2'
          | GREATER -> GREATER)
     | (hol_Const x1' ty1',hol_Comb v70 v71) -> LESS
     | (hol_Const x1' ty1',hol_Abs v72 v73) -> LESS
     | (hol_Comb s1 t1,hol_Var v82 v83) -> GREATER
     | (hol_Comb s1 t1,hol_Const v84 v85) -> GREATER
     | (hol_Comb s1 t1,hol_Comb s2 t2) ->
         (match term_compare s1 s2 with
            LESS -> LESS
          | EQUAL -> term_compare t1 t2
          | GREATER -> GREATER)
     | (hol_Comb s1 t1,hol_Abs v88 v89) -> LESS
     | (hol_Abs s1' t1',hol_Var v98 v99) -> GREATER
     | (hol_Abs s1' t1',hol_Const v100 v101) -> GREATER
     | (hol_Abs s1' t1',hol_Comb v102 v103) -> GREATER
     | (hol_Abs s1' t1',hol_Abs s2' t2') ->
         (match term_compare s1' s2' with
            LESS -> LESS
          | EQUAL -> term_compare t1' t2'
          | GREATER -> GREATER)`;;

let term_compare_ind = cake_ind "term_compare";;

(* HOL4 [local] *)
let ml_hol_kernel_funsProg_term_cmp_thm = prove
 (`term_cmp = term_compare`,
  REWRITE_TAC[FUN_EQ_THM] THEN MATCH_MP_TAC term_compare_ind THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[term_cmp_thm] THEN ONCE_REWRITE_TAC[term_compare_def] THEN
  REPEAT TOP_CASE_TAC THEN RFS[pair_cmp_def]);;

(* HOL4 add_preferred_thy "-" with Theorem term_cmp_ind *)
let ml_hol_kernel_funsProg_term_cmp_ind =
  REWRITE_RULE [GSYM ml_hol_kernel_funsProg_term_cmp_thm] term_compare_ind;;
add_ind_thm "term_cmp" ml_hol_kernel_funsProg_term_cmp_ind;;
let _ = translate (REWRITE_RULE [GSYM ml_hol_kernel_funsProg_term_cmp_thm] term_compare_def);;

(* D5: HOL4 translates holKernelPmatch's codomain_def (a restatement of     *)
(* holSyntax's codomain_raw)                                                 *)
let _ = translate (runtime_check_check ["ty"] codomain_raw);;
let _ = translate typeof_def;;
let _ = translate ordav_def;;
let _ = translate orda_def;;
let _ = translate term_remove_def;;
let _ = translate term_union_def;;

let _ = m_translate holKernel_try_def;;
let _ = m_translate holKernel_assoc_def;;
let _ = m_translate holKernel_map_def;;
let _ = m_translate holKernel_forall_def;;

ml_prog_update ml_prog_open_local_in_block;;

let _ = m_translate (runtime_check_check ["t"] holKernel_dest_type_def);;
let _ = m_translate (runtime_check_check ["t"] holKernel_dest_vartype_def);;
(* D5: HOL4 translates holKernelPmatch's dest_var_def, dest_const_def,      *)
(* dest_comb_def, dest_abs_def, rator_def, rand_def, dest_eq_def            *)
let _ = m_translate (runtime_check_check ["tm"] holKernel_dest_var_def);;
let _ = m_translate (runtime_check_check ["tm"] holKernel_dest_const_def);;
let _ = m_translate (runtime_check_check ["tm"] holKernel_dest_comb_def);;
let _ = m_translate (runtime_check_check ["tm"] holKernel_dest_abs_def);;
let _ = m_translate (runtime_check_check ["tm"] holKernel_rator_def);;
let _ = m_translate (runtime_check_check ["tm"] holKernel_rand_def);;
let _ = m_translate (runtime_check_check ["tm"] holKernel_dest_eq_def);;

(* D5: HOL4 translates holKernelPmatch's mk_abs_def *)
let _ = m_translate (runtime_check_check ["bvar"; "bod"] holKernel_mk_abs_def);;
let _ = m_translate (runtime_check_check ["s"] holKernel_get_type_arity_def);;
let _ = m_translate (runtime_check_check ["tyop"; "args"] holKernel_mk_type_def);;

ml_prog_update ml_prog_open_local_block;;

let _ = translate holKernel_bool_ty_def;;
let _ = translate (runtime_check_check ["ty1"; "ty2"] holKernel_mk_fun_ty_def);;
let _ = translate holKernel_aty_def;;
let _ = translate holKernel_bty_def;;

let call_type_of_def = new_definition
  `call_type_of tm = holKernel_type_of tm`;;
let _ = cake_add_simps [call_type_of_def];;
next_ml_names := ["type_of_aux"];;
(* D5: HOL4 translates holKernelPmatch's type_of_def *)
let _ = m_translate holKernel_type_of_def;;
next_ml_names := ["type_of"];;

let _ = m_translate ml_monadBase_can_def;;
let _ = m_translate holKernel_image_def;;

ml_prog_update ml_prog_open_local_in_block;;

let _ = m_translate (runtime_check_check ["tm"] call_type_of_def);;
let _ = m_translate (runtime_check_check ["s"] holKernel_get_const_type_def);;
(* D5: HOL4 translates holKernelPmatch's mk_comb_def *)
let _ = m_translate (runtime_check_check ["f"; "a"] holKernel_mk_comb_def);;
let _ = m_translate
  (runtime_check_check ["n"; "theta"] (SPEC `n:mlstring` holKernel_mk_const_def));;

ml_prog_update ml_prog_open_local_block;;

let check_for_dups_def = cake_def
  `check_for_dups ls cs =
     match ls with
       [] -> st_ex_return one
     | CONS x xs ->
         if MEMBER x cs then
           holKernel_raise_Failure
             (strcat (strcat (implode "add_constants: ") x)
                     (implode " appears twice or has already been declared"))
         else check_for_dups xs (CONS x cs)`;;

let add_constants_alt = prove
 (`holKernel_add_constants ls =
     st_ex_bind holKernel_get_the_term_constants (\cs.
     st_ex_bind (check_for_dups (MAP FST ls) (MAP FST cs)) (\u.
       holKernel_set_the_term_constants (APPEND ls cs)))`,
  REWRITE_TAC[holKernel_add_constants_def] THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  X_GEN_TAC `cs:(mlstring#hol_type)list` THEN
  SPEC_TAC (`MAP FST (cs:(mlstring#hol_type)list)`, `ys:mlstring list`) THEN
  SPEC_TAC (`MAP FST (ls:(mlstring#hol_type)list)`, `xs:mlstring list`) THEN
  LIST_INDUCT_TAC THEN GEN_TAC THEN
  ONCE_REWRITE_TAC[holKernel_first_dup_def] THEN ONCE_REWRITE_TAC[check_for_dups_def] THEN
  REWRITE_TAC[GSYM MEMBER_INTRO; list_CASE] THEN
  REPEAT STRIP_TAC THEN TRY COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  RW[st_ex_bind_def; st_ex_return_def; holKernel_raise_Failure_def]);;

let _ = m_translate check_for_dups_def;;
let _ = m_translate add_constants_alt;;

let _ = m_translate holKernel_add_def_def;;

ml_prog_update ml_prog_open_local_in_block;;

let _ = m_translate
  (runtime_check_check ["n"; "ty"] (SPEC `n:mlstring` holKernel_new_constant_def));;

ml_prog_update ml_prog_open_local_block;;

let _ = m_translate holKernel_add_type_def;;

let call_new_type_def = cake_def
  `call_new_type (n:mlstring, arity:int) =
     if &0 <= arity then holKernel_new_type (n, num_of_int (abs arity))
     else holKernel_raise_Failure (implode "negative arity")`;;
let _ = cake_add_simps [call_new_type_def];;

next_ml_names := ["new_type_num"];;
let _ = m_translate holKernel_new_type_def;;

ml_prog_update ml_prog_open_local_in_block;;

next_ml_names := ["new_type"];;
let _ = m_translate (runtime_check_check ["n"] call_new_type_def);;

next_ml_names := ["EQ_MP"; "ASSUME"];;
(* D5: HOL4 translates holKernelPmatch's EQ_MP_def *)
let _ = m_translate holKernel_EQ_MP_def;;
let _ = m_translate (runtime_check_check ["tm"] holKernel_ASSUME_def);;

let _ = m_translate (runtime_check_check ["tm"] holKernel_new_axiom_def);;
let _ = m_translate (runtime_check_check ["theta"; "tm"] holKernel_vsubst_def);;

ml_prog_update ml_prog_open_local_block;;

let _ = m_translate holKernel_inst_aux_def;;

ml_prog_update ml_prog_open_local_in_block;;

let _ = m_translate (runtime_check_check ["tyin"; "tm"] holKernel_inst_def);;

ml_prog_update ml_prog_open_local_block;;

let _ = m_translate (runtime_check_check ["l"; "r"] holKernel_safe_mk_eq_def);;
let _ = m_translate (runtime_check_check ["l"; "r"] holKernel_mk_eq_def);;
let _ = translate holKernel_list_to_hypset_def;;

ml_prog_update ml_prog_open_local_in_block;;

next_ml_names := ["REFL"; "TRANS"; "MK_COMB"; "ABS"; "BETA"];;
let _ = m_translate (runtime_check_check ["tm"] holKernel_REFL_def);;
(* D5: HOL4 translates holKernelPmatch's TRANS_def *)
let _ = m_translate holKernel_TRANS_def;;

(* D5: HOL4 unfolds holKernelPmatch's MK_COMB_def on the right *)
let MK_COMB_lemma =
  let th = SPEC_ALL (prove
   (CASE_TERM
    `!x. holKernel_MK_COMB x =
       match x with
         (Sequent asl1 c1,Sequent asl2 c2) ->
           holKernel_MK_COMB (Sequent asl1 c1,Sequent asl2 c2)`,
    REWRITE_TAC[FORALL_PAIR_THM] THEN X_GEN_TAC `p1:thm` THEN X_GEN_TAC `p2:thm` THEN
    MAP_EVERY (fun v -> STRUCT_CASES_TAC (ISPEC v (cases "thm"))) [`p1:thm`; `p2:thm`] THEN
    CASE_REWRITE_TAC[])) in
  CONV_RULE (RAND_CONV (REWRITE_CONV [holKernel_MK_COMB_def])) th;;
let _ = m_translate MK_COMB_lemma;;

(* D5: HOL4 translates holKernelPmatch's ABS_def *)
let _ = m_translate (runtime_check_check ["v"] holKernel_ABS_def);;
(* workaround contamination of translator's guts by DoubleProg.abs (HOL4: *)
(* Overload abs_v = abs_1_v; here an interface entry)                      *)
override_interface ("abs_v",`abs_1_v`);;
let ml_hol_kernel_funsProg_abs_v_def = ml_prog_fetch "abs_1_v_def";;
let abs_v_thm = tr_fetch "abs_1_v_thm";;

(* D5: HOL4 translates holKernelPmatch's BETA_def *)
let _ = m_translate (runtime_check_check ["tm"] holKernel_BETA_def);;

next_ml_names := ["DEDUCT_ANTISYM_RULE"];;
let _ = m_translate holKernel_DEDUCT_ANTISYM_RULE_def;;
let _ = m_translate holKernel_new_specification_def;;
let _ = m_translate (runtime_check_check ["tm"] holKernel_new_basic_definition_def);;

next_ml_names := ["INST_TYPE"; "INST"];;
(* HOL4 SIMP_RULE std_ss [LET_DEF] *)
let _ = m_translate
  (runtime_check_check ["theta"]
     (CONV_RULE (DEPTH_CONV BETA_CONV)
        (REWRITE_RULE [LET_DEF; LET_END_DEF] holKernel_INST_TYPE_def)));;
let _ = m_translate
  (runtime_check_check ["theta"]
     (CONV_RULE (DEPTH_CONV BETA_CONV)
        (REWRITE_RULE [LET_DEF; LET_END_DEF] holKernel_INST_def)));;
let _ = m_translate
  (runtime_check_check ["tyname"; "absname"; "repname"]
     holKernel_new_basic_type_definition_def);;

ml_prog_update ml_prog_open_local_block;;

let _ = translate holKernel_list_to_hypset_def;;

ml_prog_update ml_prog_open_local_in_block;;

(* HOL4 [local] *)
let axioms_eq = prove
 (`holKernel_axioms (u:1) =
   one_CASE u (holKernel_get_the_axioms:hol_refs->((thm)list,C)exc#hol_refs)`,
  ONCE_REWRITE_TAC[one] THEN REWRITE_TAC[holKernel_axioms_def; one_case_def]);;

(* HOL4 [local] *)
let types_eq = prove
 (`holKernel_types (u:1) =
   one_CASE u
     (holKernel_get_the_type_constants:hol_refs->((mlstring#num)list,C)exc#hol_refs)`,
  ONCE_REWRITE_TAC[one] THEN REWRITE_TAC[holKernel_types_def; one_case_def]);;

(* HOL4 [local] *)
let constants_eq = prove
 (`holKernel_constants (u:1) =
   one_CASE u
     (holKernel_get_the_term_constants:
        hol_refs->((mlstring#hol_type)list,C)exc#hol_refs)`,
  ONCE_REWRITE_TAC[one] THEN REWRITE_TAC[holKernel_constants_def; one_case_def]);;

let _ = m_translate axioms_eq;;
let _ = m_translate types_eq;;
let _ = m_translate constants_eq;;

(* The kernel module is closed in subsequent script files:
   ml_hol_kernelProgScript.sml and candle_kernelProgScript.sml *)

finalise_translation ();;

(* ------------------------------------------------------------------------- *)
(* The generated theorems that HOL4 saves in the theory, under their HOL4    *)
(* names (doc/reserved_generated.tsv), for the Candle proofs                 *)
(* ------------------------------------------------------------------------- *)

let can1aux_fetch n = try tr_fetch n with Failure _ -> ml_prog_fetch n;;

(* four closure constants have the theory prefix (one name space: StringProg *)
(* and SetProg have string_lt_v, string_le_v, insert_1_v and union_1_v; HOL4 *)
(* has them in other theories): their definitions are bound under the HOL4  *)
(* theorem names                                                             *)

let TERM_TYPE_def = can1aux_fetch "TERM_TYPE_def";;
let THM_TYPE_def = can1aux_fetch "THM_TYPE_def";;
let TYPE_TYPE_def = can1aux_fetch "TYPE_TYPE_def";;
let UPDATE_TYPE_def = can1aux_fetch "UPDATE_TYPE_def";;
let TYPE_TYPE_ind = cake_ind "TYPE_TYPE";;
let aty_refs_def = can1aux_fetch "aty_refs_def";;
let bool_ty_refs_def = can1aux_fetch "bool_ty_refs_def";;
let bty_refs_def = can1aux_fetch "bty_refs_def";;
let abs_1_v_def = can1aux_fetch "abs_1_v_def";;
let aconv_v_def = can1aux_fetch "aconv_v_def";;
let add_constants_v_def = can1aux_fetch "add_constants_v_def";;
let add_def_v_def = can1aux_fetch "add_def_v_def";;
let add_type_v_def = can1aux_fetch "add_type_v_def";;
let alphavars_v_def = can1aux_fetch "alphavars_v_def";;
let assoc_v_def = can1aux_fetch "assoc_v_def";;
let assume_v_def = can1aux_fetch "assume_v_def";;
let axioms_v_def = can1aux_fetch "axioms_v_def";;
let beta_v_def = can1aux_fetch "beta_v_def";;
let call_frees_v_def = can1aux_fetch "call_frees_v_def";;
let call_freesin_v_def = can1aux_fetch "call_freesin_v_def";;
let call_new_type_v_def = can1aux_fetch "call_new_type_v_def";;
let call_type_of_v_def = can1aux_fetch "call_type_of_v_def";;
let call_type_subst_v_def = can1aux_fetch "call_type_subst_v_def";;
let call_type_vars_in_term_v_def = can1aux_fetch "call_type_vars_in_term_v_def";;
let call_tyvars_v_def = can1aux_fetch "call_tyvars_v_def";;
let call_variant_v_def = can1aux_fetch "call_variant_v_def";;
let call_vfree_in_v_def = can1aux_fetch "call_vfree_in_v_def";;
let can_v_def = can1aux_fetch "can_v_def";;
let check_for_dups_v_def = can1aux_fetch "check_for_dups_v_def";;
let check_thm_v_def = can1aux_fetch "check_thm_v_def";;
let check_tm_tm_v_def = can1aux_fetch "check_tm_tm_v_def";;
let check_tm_v_def = can1aux_fetch "check_tm_v_def";;
let check_ty_ty_v_def = can1aux_fetch "check_ty_ty_v_def";;
let check_ty_v_def = can1aux_fetch "check_ty_v_def";;
let codomain_v_def = can1aux_fetch "codomain_v_def";;
let concl_v_def = can1aux_fetch "concl_v_def";;
let constants_v_def = can1aux_fetch "constants_v_def";;
let deduct_antisym_rule_v_def = can1aux_fetch "deduct_antisym_rule_v_def";;
let dest_abs_v_def = can1aux_fetch "dest_abs_v_def";;
let dest_comb_v_def = can1aux_fetch "dest_comb_v_def";;
let dest_const_v_def = can1aux_fetch "dest_const_v_def";;
let dest_eq_v_def = can1aux_fetch "dest_eq_v_def";;
let dest_thm_v_def = can1aux_fetch "dest_thm_v_def";;
let dest_type_v_def = can1aux_fetch "dest_type_v_def";;
let dest_var_v_def = can1aux_fetch "dest_var_v_def";;
let dest_vartype_v_def = can1aux_fetch "dest_vartype_v_def";;
let eq_mp_v_def = can1aux_fetch "eq_mp_v_def";;
let forall_v_def = can1aux_fetch "forall_v_def";;
let frees_v_def = can1aux_fetch "frees_v_def";;
let freesin_v_def = can1aux_fetch "freesin_v_def";;
let freesl_v_def = can1aux_fetch "freesl_v_def";;
let get_const_type_v_def = can1aux_fetch "get_const_type_v_def";;
let get_type_arity_v_def = can1aux_fetch "get_type_arity_v_def";;
let hyp_v_def = can1aux_fetch "hyp_v_def";;
let image_v_def = can1aux_fetch "image_v_def";;
let insert_1_v_def = can1aux_fetch "ml_hol_kernel_funsProg_insert_1_v_def";;
let inst_1_v_def = can1aux_fetch "inst_1_v_def";;
let inst_aux_v_def = can1aux_fetch "inst_aux_v_def";;
let inst_type_v_def = can1aux_fetch "inst_type_v_def";;
let inst_v_def = can1aux_fetch "inst_v_def";;
let is_abs_v_def = can1aux_fetch "is_abs_v_def";;
let is_comb_v_def = can1aux_fetch "is_comb_v_def";;
let is_const_v_def = can1aux_fetch "is_const_v_def";;
let is_type_v_def = can1aux_fetch "is_type_v_def";;
let is_var_v_def = can1aux_fetch "is_var_v_def";;
let is_vartype_v_def = can1aux_fetch "is_vartype_v_def";;
let itlist_v_def = can1aux_fetch "itlist_v_def";;
let mk_abs_v_def = can1aux_fetch "mk_abs_v_def";;
let mk_comb_1_v_def = can1aux_fetch "mk_comb_1_v_def";;
let mk_comb_v_def = can1aux_fetch "mk_comb_v_def";;
let mk_const_v_def = can1aux_fetch "mk_const_v_def";;
let mk_eq_v_def = can1aux_fetch "mk_eq_v_def";;
let mk_fun_ty_v_def = can1aux_fetch "mk_fun_ty_v_def";;
let mk_type_v_def = can1aux_fetch "mk_type_v_def";;
let mk_var_v_def = can1aux_fetch "mk_var_v_def";;
let mk_vartype_v_def = can1aux_fetch "mk_vartype_v_def";;
let new_axiom_v_def = can1aux_fetch "new_axiom_v_def";;
let new_basic_definition_v_def = can1aux_fetch "new_basic_definition_v_def";;
let new_basic_type_definition_v_def = can1aux_fetch "new_basic_type_definition_v_def";;
let new_constant_v_def = can1aux_fetch "new_constant_v_def";;
let new_specification_v_def = can1aux_fetch "new_specification_v_def";;
let new_type_v_def = can1aux_fetch "new_type_v_def";;
let orda_v_def = can1aux_fetch "orda_v_def";;
let ordav_v_def = can1aux_fetch "ordav_v_def";;
let raconv_v_def = can1aux_fetch "raconv_v_def";;
let rand_v_def = can1aux_fetch "rand_v_def";;
let rator_v_def = can1aux_fetch "rator_v_def";;
let refl_v_def = can1aux_fetch "refl_v_def";;
let rev_assocd_v_def = can1aux_fetch "rev_assocd_v_def";;
let safe_mk_eq_v_def = can1aux_fetch "safe_mk_eq_v_def";;
let string_le_v_def = can1aux_fetch "ml_hol_kernel_funsProg_string_le_v_def";;
let string_lt_v_def = can1aux_fetch "ml_hol_kernel_funsProg_string_lt_v_def";;
let subset_v_def = can1aux_fetch "subset_v_def";;
let subtract_v_def = can1aux_fetch "subtract_v_def";;
let term_cmp_v_def = can1aux_fetch "term_cmp_v_def";;
let term_remove_v_def = can1aux_fetch "term_remove_v_def";;
let term_union_v_def = can1aux_fetch "term_union_v_def";;
let trans_v_def = can1aux_fetch "trans_v_def";;
let try_v_def = can1aux_fetch "try_v_def";;
let type_cmp_v_def = can1aux_fetch "type_cmp_v_def";;
let type_of_v_def = can1aux_fetch "type_of_v_def";;
let type_subst_v_def = can1aux_fetch "type_subst_v_def";;
let type_vars_in_term_v_def = can1aux_fetch "type_vars_in_term_v_def";;
let typeof_v_def = can1aux_fetch "typeof_v_def";;
let types_v_def = can1aux_fetch "types_v_def";;
let tyvars_v_def = can1aux_fetch "tyvars_v_def";;
let union_1_v_def = can1aux_fetch "ml_hol_kernel_funsProg_union_1_v_def";;
let variant_v_def = can1aux_fetch "variant_v_def";;
let vfree_in_v_def = can1aux_fetch "vfree_in_v_def";;
let vsubst_aux_v_def = can1aux_fetch "vsubst_aux_v_def";;
let vsubst_v_def = can1aux_fetch "vsubst_v_def";;
let abs_1_v_thm = can1aux_fetch "abs_1_v_thm";;
let assume_v_thm = can1aux_fetch "assume_v_thm";;
let aty_v_thm = can1aux_fetch "aty_v_thm";;
let axioms_v_thm = can1aux_fetch "axioms_v_thm";;
let beta_v_thm = can1aux_fetch "beta_v_thm";;
let bool_ty_v_thm = can1aux_fetch "bool_ty_v_thm";;
let call_frees_v_thm = can1aux_fetch "call_frees_v_thm";;
let call_freesin_v_thm = can1aux_fetch "call_freesin_v_thm";;
let call_new_type_v_thm = can1aux_fetch "call_new_type_v_thm";;
let call_type_of_v_thm = can1aux_fetch "call_type_of_v_thm";;
let call_type_subst_v_thm = can1aux_fetch "call_type_subst_v_thm";;
let call_type_vars_in_term_v_thm = can1aux_fetch "call_type_vars_in_term_v_thm";;
let call_tyvars_v_thm = can1aux_fetch "call_tyvars_v_thm";;
let call_variant_v_thm = can1aux_fetch "call_variant_v_thm";;
let call_vfree_in_v_thm = can1aux_fetch "call_vfree_in_v_thm";;
let concl_v_thm = can1aux_fetch "concl_v_thm";;
let constants_v_thm = can1aux_fetch "constants_v_thm";;
let deduct_antisym_rule_v_thm = can1aux_fetch "deduct_antisym_rule_v_thm";;
let dest_abs_v_thm = can1aux_fetch "dest_abs_v_thm";;
let dest_comb_v_thm = can1aux_fetch "dest_comb_v_thm";;
let dest_const_v_thm = can1aux_fetch "dest_const_v_thm";;
let dest_eq_v_thm = can1aux_fetch "dest_eq_v_thm";;
let dest_thm_v_thm = can1aux_fetch "dest_thm_v_thm";;
let dest_type_v_thm = can1aux_fetch "dest_type_v_thm";;
let dest_var_v_thm = can1aux_fetch "dest_var_v_thm";;
let dest_vartype_v_thm = can1aux_fetch "dest_vartype_v_thm";;
let eq_mp_v_thm = can1aux_fetch "eq_mp_v_thm";;
let freesl_v_thm = can1aux_fetch "freesl_v_thm";;
let get_const_type_v_thm = can1aux_fetch "get_const_type_v_thm";;
let get_type_arity_v_thm = can1aux_fetch "get_type_arity_v_thm";;
let hyp_v_thm = can1aux_fetch "hyp_v_thm";;
let inst_1_v_thm = can1aux_fetch "inst_1_v_thm";;
let inst_type_v_thm = can1aux_fetch "inst_type_v_thm";;
let inst_v_thm = can1aux_fetch "inst_v_thm";;
let is_abs_v_thm = can1aux_fetch "is_abs_v_thm";;
let is_comb_v_thm = can1aux_fetch "is_comb_v_thm";;
let is_const_v_thm = can1aux_fetch "is_const_v_thm";;
let is_type_v_thm = can1aux_fetch "is_type_v_thm";;
let is_var_v_thm = can1aux_fetch "is_var_v_thm";;
let is_vartype_v_thm = can1aux_fetch "is_vartype_v_thm";;
let mk_abs_v_thm = can1aux_fetch "mk_abs_v_thm";;
let mk_comb_1_v_thm = can1aux_fetch "mk_comb_1_v_thm";;
let mk_comb_v_thm = can1aux_fetch "mk_comb_v_thm";;
let mk_const_v_thm = can1aux_fetch "mk_const_v_thm";;
let mk_type_v_thm = can1aux_fetch "mk_type_v_thm";;
let mk_var_v_thm = can1aux_fetch "mk_var_v_thm";;
let mk_vartype_v_thm = can1aux_fetch "mk_vartype_v_thm";;
let new_axiom_v_thm = can1aux_fetch "new_axiom_v_thm";;
let new_basic_definition_v_thm = can1aux_fetch "new_basic_definition_v_thm";;
let new_basic_type_definition_v_thm = can1aux_fetch "new_basic_type_definition_v_thm";;
let new_constant_v_thm = can1aux_fetch "new_constant_v_thm";;
let new_specification_v_thm = can1aux_fetch "new_specification_v_thm";;
let rand_v_thm = can1aux_fetch "rand_v_thm";;
let rator_v_thm = can1aux_fetch "rator_v_thm";;
let refl_v_thm = can1aux_fetch "refl_v_thm";;
let trans_v_thm = can1aux_fetch "trans_v_thm";;
let types_v_thm = can1aux_fetch "types_v_thm";;
let vsubst_v_thm = can1aux_fetch "vsubst_v_thm";;
let get_the_context_thm = can1aux_fetch "get_the_context_thm";;
let init_axioms_v_thm = can1aux_fetch "init_axioms_v_thm";;
let init_context_v_thm = can1aux_fetch "init_context_v_thm";;
let init_term_constants_v_thm = can1aux_fetch "init_term_constants_v_thm";;
let init_type_constants_v_thm = can1aux_fetch "init_type_constants_v_thm";;
let the_axioms_def = can1aux_fetch "the_axioms_def";;
let the_context_def = can1aux_fetch "the_context_def";;
let the_term_constants_def = can1aux_fetch "the_term_constants_def";;
let the_type_constants_def = can1aux_fetch "the_type_constants_def";;
let HOL_STORE_def = can1aux_monad_parameters.store_pred_def;;
