(* ========================================================================= *)
(* candle_kernel_perms: port of HOL4 candle/prover/                          *)
(* candle_kernel_permsScript.sml (CakeML v3479).  Prove perms theorems for  *)
(* kernel functions.                                                         *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - Every closure is proved by the generic tactic of the HOL4 script,      *)
(*   rw[perms_ok_def, f_v_def, pat_bindings_def, perms_ok_env_def], then,   *)
(*   where the closure has free variables, pop_assum mp_tac \\              *)
(*   eval_nsLookup_tac \\ rw[] with the perms theorems proved before (all  *)
(*   [simp], as in HOL4).  KPERMSAUX_RW is the kit's RW with what HOL4's     *)
(*   srw_ss contributes here (membership in finite sets, pat_bindings,       *)
(*   equations of string literals); KPERMSAUX_LOOKUP_TAC takes the lookup    *)
(*   assumption by its shape (RW orders the assumptions differently) and    *)
(*   evaluates it with ml_progLib's nsLookup_conv.  The kernel closures are *)
(*   bigger than HOL4's (decision D5: nested one-level Mats); the largest,   *)
(*   dest_cexp_v (30,000 term nodes), takes about 8 s, the whole file about *)
(*   80 s.                                                                   *)
(* - The generated theorems that no file binds are fetched from the         *)
(*   translator's store by their HOL4 names (KPERMSAUX_FETCH "fst_v_def"   *)
(*   for HOL4 std_preludeTheory.fst_v_def); the kernel's ones are the       *)
(*   bindings (ml_hol_kernel_funsProg.ml, candle_kernelProg.ml).             *)
(* - Closure names (doc/reserved_generated.tsv): HOL4                        *)
(*   ListProg$filter_v is ListProg_filter_v; the kernel's map_1_v,           *)
(*   string_lt_v, string_le_v, insert_1_v and union_1_v are                  *)
(*   ml_hol_kernel_funsProg_map_1_v, ...; abs_v is the interface name of     *)
(*   abs_1_v (HOL4 Overload), HOL4's abs_v_def is                            *)
(*   ml_hol_kernel_funsProg_abs_v_def.                                       *)
(* - HOL4's EVAL steps: after the lookups of length_v and compare_1_v       *)
(*   nothing is left to evaluate; the values cv_t_v, cv_f_v, bool_ty_v,      *)
(*   aty_v, exp_for_dec_enc_v and compute_default_clock_v are unfolded by    *)
(*   rewriting with the definitions of their refinement invariants.          *)
(* - Statements with free variables in HOL4 are universally quantified;     *)
(*   evaluate_kernel_perms and evaluate_empty_perms (HOL4 derives them by   *)
(*   SIMP_RULE) are stated and proved as theorems.                          *)
(* - The theorems that the HOL4 script leaves in a comment                   *)
(*   (perms_ok_member_v .. perms_ok_disj1_v) are not ported.                 *)
(* ========================================================================= *)

needs "candle/prover/candle_kernel_vals.ml";;
needs "candle/prover/perms.ml";;
needs "misc/misc.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "hol4/sptree.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/proofs/namespaceProps.ml";;
needs "semantics/proofs/evaluateProps.ml";;
needs "candle/prover/candle_kernelProg.ml";;
needs "candle/prover/candle_prover_inv.ml";;
needs "candle/standard/ml_kernel/ml_hol_kernel_funsProg.ml";;
needs "candle/prover/ast_extras.ml";;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The generic tactic of the HOL4 script                                     *)
(* ------------------------------------------------------------------------- *)

(* the theorems that the translations generate (HOL4 saves them in the       *)
(* theories: Word8ProgTheory.word8_fromint_v_def, ...)                       *)
let KPERMSAUX_FETCH name = try tr_fetch name with Failure _ -> ml_prog_fetch name;;

(* HOL4's rw: its simpset srw_ss decides membership in finite sets,          *)
(* computes pat_bindings and decides equations of string literals            *)
let KPERMSAUX_SET_RULES =
  [UNIONS_INSERT; UNIONS_0; IN_UNION; IN_INSERT; IN_DIFF; NOT_IN_EMPTY;
   UNION_EMPTY; IN_SING; pat_bindings_def; injectivity "char"];;

let KPERMSAUX_RW thl = RW (thl @ KPERMSAUX_SET_RULES);;

(* HOL4 eval_nsLookup_tac, rewrite_tac [nsLookup_merge_env] \\              *)
(* CONV_TAC (DEPTH_CONV nsLookup_conv): ml_progLib's nsLookup_conv          *)
(* evaluates lookups in merge_env chains itself (rewriting with              *)
(* nsLookup_merge_env first gives the same result ten times slower)          *)
let KPERMSAUX_EVAL_NSLOOKUP_TAC = CONV_TAC(DEPTH_CONV nsLookup_conv);;

(* HOL4 pop_assum mp_tac \\ eval_nsLookup_tac: the lookup of the free        *)
(* variable, the newest assumption that HOL4's rw leaves, is not always the  *)
(* newest one here: it is taken by its shape                                  *)
let KPERMSAUX_LOOKUP_TAC =
  QPAT_X_ASSUM "nsLookup _ _ = SOME _" MP_TAC THEN KPERMSAUX_EVAL_NSLOOKUP_TAC;;

(* ------------------------------------------------------------------------- *)
(* Functions translated with translate should be proved for any ps          *)
(* ------------------------------------------------------------------------- *)

let perms_ok_word8_fromint_v = prove
 (`!ps. perms_ok ps word8_fromint_v`,
  KPERMSAUX_RW[perms_ok_def; KPERMSAUX_FETCH "word8_fromint_v_def"; pat_bindings_def;
               perms_ok_env_def]);;
let _ = cake_add_simps [perms_ok_word8_fromint_v];;

let perms_ok_fst_v = prove
 (`!ps. perms_ok ps fst_v`,
  KPERMSAUX_RW[perms_ok_def; KPERMSAUX_FETCH "fst_v_def"; pat_bindings_def; perms_ok_env_def]);;
let _ = cake_add_simps [perms_ok_fst_v];;

let perms_ok_snd_v = prove
 (`!ps. perms_ok ps snd_v`,
  KPERMSAUX_RW[perms_ok_def; KPERMSAUX_FETCH "snd_v_def"; pat_bindings_def; perms_ok_env_def]);;
let _ = cake_add_simps [perms_ok_snd_v];;

let perms_ok_exists_v = prove
 (`!ps. perms_ok ps exists_v`,
  KPERMSAUX_RW[perms_ok_def; KPERMSAUX_FETCH "exists_v_def"; pat_bindings_def; perms_ok_env_def]);;
let _ = cake_add_simps [perms_ok_exists_v];;

let perms_ok_length_aux_v = prove
 (`!ps. perms_ok ps length_aux_v`,
  KPERMSAUX_RW[perms_ok_def; KPERMSAUX_FETCH "length_aux_v_def"; pat_bindings_def;
               perms_ok_env_def]);;
let _ = cake_add_simps [perms_ok_length_aux_v];;

let perms_ok_length_v = prove
 (`!ps. perms_ok ps length_v`,
  KPERMSAUX_RW[perms_ok_def; KPERMSAUX_FETCH "length_v_def"; pat_bindings_def;
               perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_length_v];;

let perms_ok_map_1_v = prove
 (`!ps. perms_ok ps map_1_v`,
  KPERMSAUX_RW[perms_ok_def; KPERMSAUX_FETCH "map_1_v_def"; pat_bindings_def; perms_ok_env_def]);;
let _ = cake_add_simps [perms_ok_map_1_v];;

let perms_ok_member_v = prove
 (`!ps. perms_ok ps member_v`,
  KPERMSAUX_RW[perms_ok_def; KPERMSAUX_FETCH "member_v_def"; pat_bindings_def; perms_ok_env_def]);;
let _ = cake_add_simps [perms_ok_member_v];;

let perms_ok_filter_v = prove
 (`!ps. perms_ok ps ListProg_filter_v`,
  KPERMSAUX_RW[perms_ok_def; KPERMSAUX_FETCH "ListProg_filter_v_def"; pat_bindings_def;
               perms_ok_env_def]);;
let _ = cake_add_simps [perms_ok_filter_v];;

let perms_ok_every_v = prove
 (`!ps. perms_ok ps every_v`,
  KPERMSAUX_RW[perms_ok_def; KPERMSAUX_FETCH "every_v_def"; pat_bindings_def; perms_ok_env_def]);;
let _ = cake_add_simps [perms_ok_every_v];;

let perms_ok_sort2_tail_v = prove
 (`!ps. perms_ok ps sort2_tail_v`,
  KPERMSAUX_RW[perms_ok_def; KPERMSAUX_FETCH "sort2_tail_v_def"; pat_bindings_def;
               perms_ok_env_def]);;
let _ = cake_add_simps [perms_ok_sort2_tail_v];;

let perms_ok_sort3_tail_v = prove
 (`!ps. perms_ok ps sort3_tail_v`,
  KPERMSAUX_RW[perms_ok_def; KPERMSAUX_FETCH "sort3_tail_v_def"; pat_bindings_def;
               perms_ok_env_def]);;
let _ = cake_add_simps [perms_ok_sort3_tail_v];;

let perms_ok_div2_v = prove
 (`!ps. perms_ok ps div2_v`,
  KPERMSAUX_RW[perms_ok_def; KPERMSAUX_FETCH "div2_v_def"; pat_bindings_def; perms_ok_env_def]);;
let _ = cake_add_simps [perms_ok_div2_v];;

let perms_ok_rev_1_v = prove
 (`!ps. perms_ok ps rev_1_v`,
  KPERMSAUX_RW[perms_ok_def; KPERMSAUX_FETCH "rev_1_v_def"; pat_bindings_def; perms_ok_env_def]);;
let _ = cake_add_simps [perms_ok_rev_1_v];;

let perms_ok_drop_1_v = prove
 (`!ps. perms_ok ps drop_1_v`,
  KPERMSAUX_RW[perms_ok_def; KPERMSAUX_FETCH "drop_1_v_def"; pat_bindings_def; perms_ok_env_def]);;
let _ = cake_add_simps [perms_ok_drop_1_v];;

let perms_ok_merge_tail = prove
 (`!ps. perms_ok ps merge_tail_v`,
  KPERMSAUX_RW[perms_ok_def; KPERMSAUX_FETCH "merge_tail_v_def"; pat_bindings_def;
               perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_merge_tail];;

let perms_ok_mergesortn_tail_v = prove
 (`!ps. perms_ok ps mergesortn_tail_v`,
  KPERMSAUX_RW[perms_ok_def; KPERMSAUX_FETCH "mergesortn_tail_v_def"; pat_bindings_def;
               perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_mergesortn_tail_v];;

let perms_ok_mergesort_tail_v = prove
 (`!ps. perms_ok ps mergesort_tail_v`,
  KPERMSAUX_RW[perms_ok_def; KPERMSAUX_FETCH "mergesort_tail_v_def"; pat_bindings_def;
               perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_mergesort_tail_v];;

let perms_ok_sort_v = prove
 (`!ps. perms_ok ps sort_v`,
  KPERMSAUX_RW[perms_ok_def; KPERMSAUX_FETCH "sort_v_def"; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_sort_v];;

let perms_ok_strcat_v = prove
 (`!ps. perms_ok ps strcat_v`,
  KPERMSAUX_RW[perms_ok_def; KPERMSAUX_FETCH "strcat_v_def"; perms_ok_env_def]);;
let _ = cake_add_simps [perms_ok_strcat_v];;

let perms_ok_string_lt_v = prove
 (`!ps. perms_ok ps ml_hol_kernel_funsProg_string_lt_v`,
  KPERMSAUX_RW[perms_ok_def; string_lt_v_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_string_lt_v];;

let perms_ok_string_le_v = prove
 (`!ps. perms_ok ps ml_hol_kernel_funsProg_string_le_v`,
  KPERMSAUX_RW[perms_ok_def; string_le_v_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_string_le_v];;

let perms_ok_mmap_1_v = prove
 (`!ps. perms_ok ps ml_hol_kernel_funsProg_map_1_v`,
  KPERMSAUX_RW[perms_ok_def; KPERMSAUX_FETCH "ml_hol_kernel_funsProg_map_1_v_def";
               perms_ok_env_def; pat_bindings_def]);;
let _ = cake_add_simps [perms_ok_mmap_1_v];;

let perms_ok_check_tm_v = prove
 (`!ps. perms_ok ps check_tm_v`,
  KPERMSAUX_RW[perms_ok_def; check_tm_v_def; pat_bindings_def; perms_ok_env_def]);;
let _ = cake_add_simps [perms_ok_check_tm_v];;

let perms_ok_check_thm_v = prove
 (`!ps. perms_ok ps check_thm_v`,
  KPERMSAUX_RW[perms_ok_def; check_thm_v_def; pat_bindings_def; perms_ok_env_def]);;
let _ = cake_add_simps [perms_ok_check_thm_v];;

let perms_ok_check_tm_tm_v = prove
 (`!ps. perms_ok ps check_tm_tm_v`,
  KPERMSAUX_RW[perms_ok_def; check_tm_tm_v_def; pat_bindings_def; perms_ok_env_def]);;
let _ = cake_add_simps [perms_ok_check_tm_tm_v];;

let perms_ok_check_ty_ty_v = prove
 (`!ps. perms_ok ps check_ty_ty_v`,
  KPERMSAUX_RW[perms_ok_def; check_ty_ty_v_def; pat_bindings_def; perms_ok_env_def]);;
let _ = cake_add_simps [perms_ok_check_ty_ty_v];;

let perms_ok_vfree_in_v = prove
 (`!ps. perms_ok ps vfree_in_v`,
  KPERMSAUX_RW[perms_ok_def; vfree_in_v_def; pat_bindings_def; perms_ok_env_def]);;
let _ = cake_add_simps [perms_ok_vfree_in_v];;

let perms_ok_call_vfree_in_v = prove
 (`!ps. perms_ok ps call_vfree_in_v`,
  KPERMSAUX_RW[perms_ok_def; call_vfree_in_v_def; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_call_vfree_in_v];;

let perms_ok_variant_v = prove
 (`!ps. perms_ok ps variant_v`,
  KPERMSAUX_RW[perms_ok_def; variant_v_def; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_variant_v];;

let perms_ok_call_variant_v = prove
 (`!ps. perms_ok ps call_variant_v`,
  KPERMSAUX_RW[perms_ok_def; call_variant_v_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_call_variant_v];;

let perms_ok_concl_v = prove
 (`!ps. perms_ok ps concl_v`,
  KPERMSAUX_RW[perms_ok_def; concl_v_def; pat_bindings_def; perms_ok_env_def]);;
let _ = cake_add_simps [perms_ok_concl_v];;

let perms_ok_assoc_v = prove
 (`!ps. perms_ok ps assoc_v`,
  KPERMSAUX_RW[perms_ok_def; assoc_v_def; perms_ok_env_def; pat_bindings_def]);;
let _ = cake_add_simps [perms_ok_assoc_v];;

let perms_ok_alphavars_v = prove
 (`!ps. perms_ok ps alphavars_v`,
  KPERMSAUX_RW[perms_ok_def; alphavars_v_def; pat_bindings_def; perms_ok_env_def]);;
let _ = cake_add_simps [perms_ok_alphavars_v];;

let perms_ok_raconv_v = prove
 (`!ps. perms_ok ps raconv_v`,
  KPERMSAUX_RW[perms_ok_def; raconv_v_def; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_raconv_v];;

let perms_ok_aconv_v = prove
 (`!ps. perms_ok ps aconv_v`,
  KPERMSAUX_RW[perms_ok_def; aconv_v_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_aconv_v];;

let perms_ok_try_v = prove
 (`!ps. perms_ok ps try_v`,
  KPERMSAUX_RW[perms_ok_def; try_v_def; pat_bindings_def; perms_ok_env_def]);;
let _ = cake_add_simps [perms_ok_try_v];;

let perms_ok_o_1_v = prove
 (`!ps. perms_ok ps o_1_v`,
  KPERMSAUX_RW[perms_ok_def; KPERMSAUX_FETCH "o_1_v_def"; pat_bindings_def; perms_ok_env_def]);;
let _ = cake_add_simps [perms_ok_o_1_v];;

let perms_ok_dest_vartype_v = prove
 (`!ps. perms_ok ps dest_vartype_v`,
  KPERMSAUX_RW[perms_ok_def; dest_vartype_v_def; pat_bindings_def; perms_ok_env_def]);;
let _ = cake_add_simps [perms_ok_dest_vartype_v];;

let perms_ok_dest_type_v = prove
 (`!ps. perms_ok ps dest_type_v`,
  KPERMSAUX_RW[perms_ok_def; dest_type_v_def; pat_bindings_def; perms_ok_env_def]);;
let _ = cake_add_simps [perms_ok_dest_type_v];;

let perms_ok_is_type_v = prove
 (`!ps. perms_ok ps is_type_v`,
  KPERMSAUX_RW[perms_ok_def; is_type_v_def; pat_bindings_def; perms_ok_env_def]);;
let _ = cake_add_simps [perms_ok_is_type_v];;

let perms_ok_is_vartype_v = prove
 (`!ps. perms_ok ps is_vartype_v`,
  KPERMSAUX_RW[perms_ok_def; is_vartype_v_def; pat_bindings_def; perms_ok_env_def]);;
let _ = cake_add_simps [perms_ok_is_vartype_v];;

let perms_ok_check_ty_v = prove
 (`!ps. perms_ok ps check_ty_v`,
  KPERMSAUX_RW[perms_ok_def; check_ty_v_def; pat_bindings_def; perms_ok_env_def]);;
let _ = cake_add_simps [perms_ok_check_ty_v];;

let perms_ok_rev_assocd_v = prove
 (`!ps. perms_ok ps rev_assocd_v`,
  KPERMSAUX_RW[perms_ok_def; rev_assocd_v_def; pat_bindings_def; perms_ok_env_def]);;
let _ = cake_add_simps [perms_ok_rev_assocd_v];;

let perms_ok_type_subst_v = prove
 (`!ps. perms_ok ps type_subst_v`,
  KPERMSAUX_RW[perms_ok_def; type_subst_v_def; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_type_subst_v];;

let perms_ok_call_type_subst_v = prove
 (`!ps. perms_ok ps call_type_subst_v`,
  KPERMSAUX_RW[perms_ok_def; call_type_subst_v_def; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_call_type_subst_v];;

let perms_ok_itlist_v = prove
 (`!ps. perms_ok ps itlist_v`,
  KPERMSAUX_RW[perms_ok_def; itlist_v_def; pat_bindings_def; perms_ok_env_def]);;
let _ = cake_add_simps [perms_ok_itlist_v];;

let perms_ok_insert_1_v = prove
 (`!ps. perms_ok ps ml_hol_kernel_funsProg_insert_1_v`,
  KPERMSAUX_RW[perms_ok_def; insert_1_v_def; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_insert_1_v];;

let perms_ok_union_1_v = prove
 (`!ps. perms_ok ps ml_hol_kernel_funsProg_union_1_v`,
  KPERMSAUX_RW[perms_ok_def; union_1_v_def; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_union_1_v];;

let perms_ok_subtract_v = prove
 (`!ps. perms_ok ps subtract_v`,
  KPERMSAUX_RW[perms_ok_def; subtract_v_def; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_subtract_v];;

let perms_ok_forall_v = prove
 (`!ps. perms_ok ps forall_v`,
  KPERMSAUX_RW[perms_ok_def; forall_v_def; pat_bindings_def; perms_ok_env_def]);;
let _ = cake_add_simps [perms_ok_forall_v];;

let perms_ok_tyvars_v = prove
 (`!ps. perms_ok ps tyvars_v`,
  KPERMSAUX_RW[perms_ok_def; tyvars_v_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_tyvars_v];;

let perms_ok_call_tyvars_v = prove
 (`!ps. perms_ok ps call_tyvars_v`,
  KPERMSAUX_RW[perms_ok_def; call_tyvars_v_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_call_tyvars_v];;

let perms_ok_frees_v = prove
 (`!ps. perms_ok ps frees_v`,
  KPERMSAUX_RW[perms_ok_def; frees_v_def; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_frees_v];;

let perms_ok_call_frees_v = prove
 (`!ps. perms_ok ps call_frees_v`,
  KPERMSAUX_RW[perms_ok_def; call_frees_v_def; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_call_frees_v];;

let perms_ok_freesl_v = prove
 (`!ps. perms_ok ps freesl_v`,
  KPERMSAUX_RW[perms_ok_def; freesl_v_def; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_freesl_v];;

let perms_ok_freesin_v = prove
 (`!ps. perms_ok ps freesin_v`,
  KPERMSAUX_RW[perms_ok_def; freesin_v_def; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_freesin_v];;

let perms_ok_call_freesin_v = prove
 (`!ps. perms_ok ps call_freesin_v`,
  KPERMSAUX_RW[perms_ok_def; call_freesin_v_def; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_call_freesin_v];;

let perms_ok_type_vars_in_term_v = prove
 (`!ps. perms_ok ps type_vars_in_term_v`,
  KPERMSAUX_RW[perms_ok_def; type_vars_in_term_v_def; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_type_vars_in_term_v];;

let perms_ok_call_type_vars_in_term_v = prove
 (`!ps. perms_ok ps call_type_vars_in_term_v`,
  KPERMSAUX_RW[perms_ok_def; call_type_vars_in_term_v_def; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_call_type_vars_in_term_v];;

let perms_ok_dest_var_v = prove
 (`!ps. perms_ok ps dest_var_v`,
  KPERMSAUX_RW[perms_ok_def; dest_var_v_def; pat_bindings_def; perms_ok_env_def]);;
let _ = cake_add_simps [perms_ok_dest_var_v];;

let perms_ok_dest_const_v = prove
 (`!ps. perms_ok ps dest_const_v`,
  KPERMSAUX_RW[perms_ok_def; dest_const_v_def; pat_bindings_def; perms_ok_env_def]);;
let _ = cake_add_simps [perms_ok_dest_const_v];;

let perms_ok_dest_comb_v = prove
 (`!ps. perms_ok ps dest_comb_v`,
  KPERMSAUX_RW[perms_ok_def; dest_comb_v_def; pat_bindings_def; perms_ok_env_def]);;
let _ = cake_add_simps [perms_ok_dest_comb_v];;

let perms_ok_dest_abs_v = prove
 (`!ps. perms_ok ps dest_abs_v`,
  KPERMSAUX_RW[perms_ok_def; dest_abs_v_def; pat_bindings_def; perms_ok_env_def]);;
let _ = cake_add_simps [perms_ok_dest_abs_v];;

let perms_ok_dest_thm_v = prove
 (`!ps. perms_ok ps dest_thm_v`,
  KPERMSAUX_RW[perms_ok_def; dest_thm_v_def; pat_bindings_def; perms_ok_env_def]);;
let _ = cake_add_simps [perms_ok_dest_thm_v];;

let perms_ok_hyp_v = prove
 (`!ps. perms_ok ps hyp_v`,
  KPERMSAUX_RW[perms_ok_def; hyp_v_def; pat_bindings_def; perms_ok_env_def]);;
let _ = cake_add_simps [perms_ok_hyp_v];;

let perms_ok_rand_v = prove
 (`!ps. perms_ok ps rand_v`,
  KPERMSAUX_RW[perms_ok_def; rand_v_def; pat_bindings_def; perms_ok_env_def]);;
let _ = cake_add_simps [perms_ok_rand_v];;

let perms_ok_rator_v = prove
 (`!ps. perms_ok ps rator_v`,
  KPERMSAUX_RW[perms_ok_def; rator_v_def; pat_bindings_def; perms_ok_env_def]);;
let _ = cake_add_simps [perms_ok_rator_v];;

let perms_ok_dest_eq_v = prove
 (`!ps. perms_ok ps dest_eq_v`,
  KPERMSAUX_RW[perms_ok_def; dest_eq_v_def; pat_bindings_def; perms_ok_env_def]);;
let _ = cake_add_simps [perms_ok_dest_eq_v];;

let perms_ok_is_var_v = prove
 (`!ps. perms_ok ps is_var_v`,
  KPERMSAUX_RW[perms_ok_def; is_var_v_def; pat_bindings_def; perms_ok_env_def]);;
let _ = cake_add_simps [perms_ok_is_var_v];;

let perms_ok_is_const_v = prove
 (`!ps. perms_ok ps is_const_v`,
  KPERMSAUX_RW[perms_ok_def; is_const_v_def; pat_bindings_def; perms_ok_env_def]);;
let _ = cake_add_simps [perms_ok_is_const_v];;

let perms_ok_is_comb_v = prove
 (`!ps. perms_ok ps is_comb_v`,
  KPERMSAUX_RW[perms_ok_def; is_comb_v_def; pat_bindings_def; perms_ok_env_def]);;
let _ = cake_add_simps [perms_ok_is_comb_v];;

let perms_ok_is_abs_v = prove
 (`!ps. perms_ok ps is_abs_v`,
  KPERMSAUX_RW[perms_ok_def; is_abs_v_def; pat_bindings_def; perms_ok_env_def]);;
let _ = cake_add_simps [perms_ok_is_abs_v];;

let perms_ok_vsubst_aux_v = prove
 (`!ps. perms_ok ps vsubst_aux_v`,
  KPERMSAUX_RW[perms_ok_def; vsubst_aux_v_def; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_vsubst_aux_v];;

let perms_ok_inst_aux_v = prove
 (`!ps. perms_ok ps inst_aux_v`,
  KPERMSAUX_RW[perms_ok_def; inst_aux_v_def; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_inst_aux_v];;

let perms_ok_inst_v = prove
 (`!ps. perms_ok ps inst_v`,
  KPERMSAUX_RW[perms_ok_def; inst_v_def; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_inst_v];;

let perms_ok_mk_vartype_v = prove
 (`!ps. perms_ok ps mk_vartype_v`,
  KPERMSAUX_RW[perms_ok_def; mk_vartype_v_def; pat_bindings_def; perms_ok_env_def]);;
let _ = cake_add_simps [perms_ok_mk_vartype_v];;

let perms_ok_mk_var_v = prove
 (`!ps. perms_ok ps mk_var_v`,
  KPERMSAUX_RW[perms_ok_def; mk_var_v_def; pat_bindings_def; perms_ok_env_def]);;
let _ = cake_add_simps [perms_ok_mk_var_v];;

let perms_ok_mk_abs_v = prove
 (`!ps. perms_ok ps mk_abs_v`,
  KPERMSAUX_RW[perms_ok_def; mk_abs_v_def; pat_bindings_def; perms_ok_env_def]);;
let _ = cake_add_simps [perms_ok_mk_abs_v];;

let perms_ok_compare_1_v = prove
 (`!ps. perms_ok ps compare_1_v`,
  KPERMSAUX_RW[perms_ok_def; KPERMSAUX_FETCH "compare_1_v_def"; pat_bindings_def;
               perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_compare_1_v];;

let perms_ok_type_cmp_v = prove
 (`!ps. perms_ok ps type_cmp_v`,
  KPERMSAUX_RW[perms_ok_def; type_cmp_v_def; pat_bindings_def; perms_ok_env_def] THEN
  RFS[] THEN
  KPERMSAUX_RW[] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_type_cmp_v];;

let perms_ok_term_cmp_v = prove
 (`!ps. perms_ok ps term_cmp_v`,
  KPERMSAUX_RW[perms_ok_def; term_cmp_v_def; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_term_cmp_v];;

let perms_ok_ordav_v = prove
 (`!ps. perms_ok ps ordav_v`,
  KPERMSAUX_RW[perms_ok_def; ordav_v_def; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_ordav_v];;

let perms_ok_codomain_v = prove
 (`!ps. perms_ok ps codomain_v`,
  KPERMSAUX_RW[perms_ok_def; codomain_v_def; pat_bindings_def; perms_ok_env_def]);;
let _ = cake_add_simps [perms_ok_codomain_v];;

let perms_ok_typeof_v = prove
 (`!ps. perms_ok ps typeof_v`,
  KPERMSAUX_RW[perms_ok_def; typeof_v_def; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_typeof_v];;

let perms_ok_orda_v = prove
 (`!ps. perms_ok ps orda_v`,
  KPERMSAUX_RW[perms_ok_def; orda_v_def; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_orda_v];;

let perms_ok_term_union_v = prove
 (`!ps. perms_ok ps term_union_v`,
  KPERMSAUX_RW[perms_ok_def; term_union_v_def; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_term_union_v];;

let perms_ok_image_v = prove
 (`!ps. perms_ok ps image_v`,
  KPERMSAUX_RW[perms_ok_def; image_v_def; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_image_v];;

let perms_ok_eq_mp_v = prove
 (`!ps. perms_ok ps eq_mp_v`,
  KPERMSAUX_RW[perms_ok_def; eq_mp_v_def; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_eq_mp_v];;

let perms_ok_inst_type_v = prove
 (`!ps. perms_ok ps inst_type_v`,
  KPERMSAUX_RW[perms_ok_def; inst_type_v_def; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_inst_type_v];;

let perms_ok_term_remove_v = prove
 (`!ps. perms_ok ps term_remove_v`,
  KPERMSAUX_RW[perms_ok_def; term_remove_v_def; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_term_remove_v];;

let perms_ok_can_v = prove
 (`!ps. perms_ok ps can_v`,
  KPERMSAUX_RW[perms_ok_def; can_v_def; pat_bindings_def; perms_ok_env_def]);;
let _ = cake_add_simps [perms_ok_can_v];;

let perms_ok_subset_v = prove
 (`!ps. perms_ok ps subset_v`,
  KPERMSAUX_RW[perms_ok_def; subset_v_def; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_subset_v];;

let perms_ok_flatten_v = prove
 (`!ps. perms_ok ps flatten_v`,
  KPERMSAUX_RW[perms_ok_def; KPERMSAUX_FETCH "flatten_v_def"; pat_bindings_def;
               perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[] THEN
  RFS[]);;
let _ = cake_add_simps [perms_ok_flatten_v];;

let perms_ok_get_size_v = prove
 (`!ps. perms_ok ps get_size_v`,
  KPERMSAUX_RW[perms_ok_def; KPERMSAUX_FETCH "get_size_v_def"; pat_bindings_def;
               perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[] THEN
  RFS[]);;
let _ = cake_add_simps [perms_ok_get_size_v];;

let perms_ok_get_next_size_v = prove
 (`!ps. perms_ok ps get_next_size_v`,
  KPERMSAUX_RW[perms_ok_def; KPERMSAUX_FETCH "get_next_size_v_def"; pat_bindings_def;
               perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[] THEN
  RFS[]);;
let _ = cake_add_simps [perms_ok_get_next_size_v];;

let perms_ok_remove_all_v = prove
 (`!ps. perms_ok ps remove_all_v`,
  KPERMSAUX_RW[perms_ok_def; KPERMSAUX_FETCH "remove_all_v_def"; pat_bindings_def;
               perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[] THEN
  RFS[]);;
let _ = cake_add_simps [perms_ok_remove_all_v];;

let perms_ok_smart_remove_v = prove
 (`!ps. perms_ok ps smart_remove_v`,
  KPERMSAUX_RW[perms_ok_def; KPERMSAUX_FETCH "smart_remove_v_def"; pat_bindings_def;
               perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[] THEN
  RFS[]);;
let _ = cake_add_simps [perms_ok_smart_remove_v];;

let perms_ok_annotate_v = prove
 (`!ps. perms_ok ps annotate_v`,
  KPERMSAUX_RW[perms_ok_def; KPERMSAUX_FETCH "annotate_v_def"; pat_bindings_def;
               perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[] THEN
  RFS[]);;
let _ = cake_add_simps [perms_ok_annotate_v];;

let perms_ok_exp_1_v = prove
 (`!ps. perms_ok ps exp_1_v`,
  KPERMSAUX_RW[perms_ok_def; KPERMSAUX_FETCH "exp_1_v_def"; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[] THEN
  RFS[] THEN
  KPERMSAUX_RW[perms_ok_def; KPERMSAUX_FETCH "exp_aux_v_def"; pat_bindings_def;
               perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[] THEN
  RFS[]);;
let _ = cake_add_simps [perms_ok_exp_1_v];;

let perms_ok_newlines_v = prove
 (`!ps. perms_ok ps newlines_v`,
  KPERMSAUX_RW[perms_ok_def; KPERMSAUX_FETCH "newlines_v_def"; pat_bindings_def;
               perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[] THEN
  RFS[]);;
let _ = cake_add_simps [perms_ok_newlines_v];;

let perms_ok_v2pretty_v = prove
 (`!ps. perms_ok ps v2pretty_v`,
  KPERMSAUX_RW[perms_ok_def; KPERMSAUX_FETCH "v2pretty_v_def"; pat_bindings_def;
               perms_ok_env_def] THEN
  GVS[] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[] THEN
  RFS[]);;
let _ = cake_add_simps [perms_ok_v2pretty_v];;

let perms_ok_str_tree_to_strs_v = prove
 (`!ps. perms_ok ps str_tree_to_strs_v`,
  KPERMSAUX_RW[perms_ok_def; KPERMSAUX_FETCH "str_tree_to_strs_v_def"; pat_bindings_def;
               perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[] THEN
  RFS[]);;
let _ = cake_add_simps [perms_ok_str_tree_to_strs_v];;

let perms_ok_null_v = prove
 (`!ps. perms_ok ps null_v`,
  KPERMSAUX_RW[perms_ok_def; KPERMSAUX_FETCH "null_v_def"; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[] THEN
  RFS[]);;
let _ = cake_add_simps [perms_ok_null_v];;

let perms_ok_flat_v = prove
 (`!ps. perms_ok ps flat_v`,
  KPERMSAUX_RW[perms_ok_def; KPERMSAUX_FETCH "flat_v_def"; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[] THEN
  RFS[]);;
let _ = cake_add_simps [perms_ok_flat_v];;

let perms_ok_exp_for_dec_enc_v = prove
 (`!ps. perms_ok ps exp_for_dec_enc_v`,
  SIMP[perms_ok_def;
       REWRITE_RULE[ml_NUM_def; ml_INT_def] (KPERMSAUX_FETCH "exp_for_dec_enc_v_thm")]);;
let _ = cake_add_simps [perms_ok_exp_for_dec_enc_v];;

let perms_ok_tochar_v = prove
 (`!ps. perms_ok ps tochar_v`,
  KPERMSAUX_RW[perms_ok_def; KPERMSAUX_FETCH "tochar_v_def"; pat_bindings_def;
               perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[] THEN
  RFS[]);;
let _ = cake_add_simps [perms_ok_tochar_v];;

let perms_ok_num_to_chars_v = prove
 (`!ps. perms_ok ps num_to_chars_v`,
  KPERMSAUX_RW[perms_ok_def; KPERMSAUX_FETCH "num_to_chars_v_def"; pat_bindings_def;
               perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[] THEN
  RFS[]);;
let _ = cake_add_simps [perms_ok_num_to_chars_v];;

let perms_ok_int_to_string_v = prove
 (`!ps. perms_ok ps int_to_string_v`,
  KPERMSAUX_RW[perms_ok_def; KPERMSAUX_FETCH "int_to_string_v_def"; pat_bindings_def;
               perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[] THEN
  RFS[]);;
let _ = cake_add_simps [perms_ok_int_to_string_v];;

let perms_ok_tostring_v = prove
 (`!ps. perms_ok ps tostring_v`,
  KPERMSAUX_RW[perms_ok_def; KPERMSAUX_FETCH "tostring_v_def"; pat_bindings_def;
               perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[] THEN
  RFS[]);;
let _ = cake_add_simps [perms_ok_tostring_v];;

let perms_ok_ty_to_v_v = prove
 (`!ps. perms_ok ps ty_to_v_v`,
  KPERMSAUX_RW[perms_ok_def; ty_to_v_v_def; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[] THEN
  RFS[]);;
let _ = cake_add_simps [perms_ok_ty_to_v_v];;

let perms_ok_term_to_v_v = prove
 (`!ps. perms_ok ps term_to_v_v`,
  KPERMSAUX_RW[perms_ok_def; term_to_v_v_def; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[] THEN
  RFS[]);;
let _ = cake_add_simps [perms_ok_term_to_v_v];;

let perms_ok_thm_to_v_v = prove
 (`!ps. perms_ok ps thm_to_v_v`,
  KPERMSAUX_RW[perms_ok_def; thm_to_v_v_def; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[] THEN
  RFS[]);;
let _ = cake_add_simps [perms_ok_thm_to_v_v];;

let perms_ok_update_to_v_v = prove
 (`!ps. perms_ok ps update_to_v_v`,
  KPERMSAUX_RW[perms_ok_def; update_to_v_v_def; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[] THEN
  RFS[]);;
let _ = cake_add_simps [perms_ok_update_to_v_v];;

let perms_ok_str_every_v = prove
 (`!ps. perms_ok ps str_every_v`,
  KPERMSAUX_RW[perms_ok_def; KPERMSAUX_FETCH "str_every_v_def"; pat_bindings_def;
               perms_ok_env_def] THEN
  GVS[] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[] THEN
  RFS[]);;
let _ = cake_add_simps [perms_ok_str_every_v];;

let perms_ok_isspace_v = prove
 (`!ps. perms_ok ps isspace_v`,
  KPERMSAUX_RW[perms_ok_def; KPERMSAUX_FETCH "isspace_v_def"; pat_bindings_def;
               perms_ok_env_def] THEN
  GVS[] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[] THEN
  RFS[]);;
let _ = cake_add_simps [perms_ok_isspace_v];;

let perms_ok_is_safe_char_v = prove
 (`!ps. perms_ok ps is_safe_char_v`,
  KPERMSAUX_RW[perms_ok_def; KPERMSAUX_FETCH "is_safe_char_v_def"; pat_bindings_def;
               perms_ok_env_def] THEN
  GVS[] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[] THEN
  RFS[]);;
let _ = cake_add_simps [perms_ok_is_safe_char_v];;

let perms_ok_char_escape_seq_v = prove
 (`!ps. perms_ok ps char_escape_seq_v`,
  KPERMSAUX_RW[perms_ok_def; KPERMSAUX_FETCH "char_escape_seq_v_def"; pat_bindings_def;
               perms_ok_env_def] THEN
  GVS[] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[] THEN
  RFS[]);;
let _ = cake_add_simps [perms_ok_char_escape_seq_v];;

let perms_ok_char_escaped_v = prove
 (`!ps. perms_ok ps char_escaped_v`,
  KPERMSAUX_RW[perms_ok_def; KPERMSAUX_FETCH "char_escaped_v_def"; pat_bindings_def;
               perms_ok_env_def] THEN
  GVS[] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[] THEN
  RFS[]);;
let _ = cake_add_simps [perms_ok_char_escaped_v];;

let perms_ok_escape_str_v = prove
 (`!ps. perms_ok ps escape_str_v`,
  KPERMSAUX_RW[perms_ok_def; KPERMSAUX_FETCH "escape_str_v_def"; pat_bindings_def;
               perms_ok_env_def] THEN
  GVS[] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[] THEN
  RFS[]);;
let _ = cake_add_simps [perms_ok_escape_str_v];;

let perms_ok_make_str_safe_v = prove
 (`!ps. perms_ok ps make_str_safe_v`,
  KPERMSAUX_RW[perms_ok_def; KPERMSAUX_FETCH "make_str_safe_v_def"; pat_bindings_def;
               perms_ok_env_def] THEN
  GVS[] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[] THEN
  RFS[]);;
let _ = cake_add_simps [perms_ok_make_str_safe_v];;

let perms_ok_sexp2tree_v = prove
 (`!ps. perms_ok ps sexp2tree_v`,
  KPERMSAUX_RW[perms_ok_def; KPERMSAUX_FETCH "sexp2tree_v_def"; pat_bindings_def;
               perms_ok_env_def] THEN
  GVS[] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[] THEN
  RFS[]);;
let _ = cake_add_simps [perms_ok_sexp2tree_v];;

let perms_ok_sexp_to_pretty_string_v = prove
 (`!ps. perms_ok ps sexp_to_pretty_string_v`,
  KPERMSAUX_RW[perms_ok_def; KPERMSAUX_FETCH "sexp_to_pretty_string_v_def"; pat_bindings_def;
               perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[] THEN
  RFS[]);;
let _ = cake_add_simps [perms_ok_sexp_to_pretty_string_v];;

let perms_ok_thm_to_string_v = prove
 (`!ps. perms_ok ps thm_to_string_v`,
  KPERMSAUX_RW[perms_ok_def; thm_to_string_v_def; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[] THEN
  RFS[]);;
let _ = cake_add_simps [perms_ok_thm_to_string_v];;

let perms_ok_funpow_v = prove
 (`!ps. perms_ok ps funpow_v`,
  KPERMSAUX_RW[perms_ok_def; KPERMSAUX_FETCH "funpow_v_def"; pat_bindings_def;
               perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_funpow_v];;

let perms_ok_app_type_v = prove
 (`!ps. perms_ok ps app_type_v`,
  KPERMSAUX_RW[perms_ok_def; app_type_v_def; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_app_type_v];;

let perms_ok_num2bit_v = prove
 (`!ps. perms_ok ps num2bit_v`,
  KPERMSAUX_RW[perms_ok_def; num2bit_v_def; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_num2bit_v];;

let perms_ok_cv2term_v = prove
 (`!ps. perms_ok ps cv2term_v`,
  KPERMSAUX_RW[perms_ok_def; cv2term_v_def; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_cv2term_v];;

let perms_ok_safemod_v = prove
 (`!ps. perms_ok ps safemod_v`,
  KPERMSAUX_RW[perms_ok_def; safemod_v_def; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_safemod_v];;

let perms_ok_safediv_v = prove
 (`!ps. perms_ok ps safediv_v`,
  KPERMSAUX_RW[perms_ok_def; safediv_v_def; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_safediv_v];;

let perms_ok_alookup_v = prove
 (`!ps. perms_ok ps alookup_v`,
  KPERMSAUX_RW[perms_ok_def; KPERMSAUX_FETCH "alookup_v_def"; pat_bindings_def;
               perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_alookup_v];;

let perms_ok_zip_v = prove
 (`!ps. perms_ok ps zip_v`,
  KPERMSAUX_RW[perms_ok_def; KPERMSAUX_FETCH "zip_v_def"; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_zip_v];;

let perms_ok_option_v = prove
 (`!ps. perms_ok ps option_v`,
  KPERMSAUX_RW[perms_ok_def; option_v_def; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_option_v];;

let perms_ok_check_v = prove
 (`!ps. perms_ok ps check_v`,
  KPERMSAUX_RW[perms_ok_def; check_v_def; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_check_v];;

let perms_ok_get_code_v = prove
 (`!ps. perms_ok ps get_code_v`,
  KPERMSAUX_RW[perms_ok_def; get_code_v_def; pat_bindings_def; perms_ok_env_def] THEN
  GVS[] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_get_code_v];;

let perms_ok_env_lookup_v = prove
 (`!ps. perms_ok ps env_lookup_v`,
  KPERMSAUX_RW[perms_ok_def; env_lookup_v_def; pat_bindings_def; perms_ok_env_def] THEN
  GVS[] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_env_lookup_v];;

let perms_ok_exec_v = prove
 (`!ps. perms_ok ps exec_v`,
  KPERMSAUX_RW[perms_ok_def; exec_v_def; pat_bindings_def; perms_ok_env_def] THEN
  GVS[] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_exec_v];;

let perms_ok_cv_t_v = prove
 (`!ps. perms_ok ps cv_t_v`,
  MP_TAC cv_t_v_thm THEN
  REWRITE_TAC[cv_T_def; KPERMSAUX_FETCH "CV_TYPE_def"; ml_NUM_def; ml_INT_def] THEN
  KPERMSAUX_RW[perms_ok_def; pat_bindings_def; perms_ok_env_def]);;
let _ = cake_add_simps [perms_ok_cv_t_v];;

let perms_ok_cv_f_v = prove
 (`!ps. perms_ok ps cv_f_v`,
  MP_TAC cv_f_v_thm THEN
  REWRITE_TAC[cv_F_def; KPERMSAUX_FETCH "CV_TYPE_def"; ml_NUM_def; ml_INT_def] THEN
  KPERMSAUX_RW[perms_ok_def; pat_bindings_def; perms_ok_env_def]);;
let _ = cake_add_simps [perms_ok_cv_f_v];;

let perms_ok_to_num_v = prove
 (`!ps. perms_ok ps to_num_v`,
  KPERMSAUX_RW[perms_ok_def; to_num_v_def; pat_bindings_def; perms_ok_env_def] THEN
  GVS[] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_to_num_v];;

let perms_ok_monop_fst_v = prove
 (`!ps. perms_ok ps monop_fst_v`,
  KPERMSAUX_RW[perms_ok_def; monop_fst_v_def; pat_bindings_def; perms_ok_env_def] THEN
  GVS[] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_monop_fst_v];;

let perms_ok_monop_snd_v = prove
 (`!ps. perms_ok ps monop_snd_v`,
  KPERMSAUX_RW[perms_ok_def; monop_snd_v_def; pat_bindings_def; perms_ok_env_def] THEN
  GVS[] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_monop_snd_v];;

let perms_ok_monop_ispair_v = prove
 (`!ps. perms_ok ps monop_ispair_v`,
  KPERMSAUX_RW[perms_ok_def; monop_ispair_v_def; pat_bindings_def; perms_ok_env_def] THEN
  GVS[] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_monop_ispair_v];;

let perms_ok_monop_v = prove
 (`!ps. perms_ok ps monop_v`,
  KPERMSAUX_RW[perms_ok_def; monop_v_def; pat_bindings_def; perms_ok_env_def] THEN
  GVS[] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_monop_v];;

let perms_ok_binop_add_v = prove
 (`!ps. perms_ok ps binop_add_v`,
  KPERMSAUX_RW[perms_ok_def; binop_add_v_def; pat_bindings_def; perms_ok_env_def] THEN
  GVS[] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_binop_add_v];;

let perms_ok_binop_sub_v = prove
 (`!ps. perms_ok ps binop_sub_v`,
  KPERMSAUX_RW[perms_ok_def; binop_sub_v_def; pat_bindings_def; perms_ok_env_def] THEN
  GVS[] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_binop_sub_v];;

let perms_ok_binop_mul_v = prove
 (`!ps. perms_ok ps binop_mul_v`,
  KPERMSAUX_RW[perms_ok_def; binop_mul_v_def; pat_bindings_def; perms_ok_env_def] THEN
  GVS[] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_binop_mul_v];;

let perms_ok_binop_div_v = prove
 (`!ps. perms_ok ps binop_div_v`,
  KPERMSAUX_RW[perms_ok_def; binop_div_v_def; pat_bindings_def; perms_ok_env_def] THEN
  GVS[] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_binop_div_v];;

let perms_ok_binop_mod_v = prove
 (`!ps. perms_ok ps binop_mod_v`,
  KPERMSAUX_RW[perms_ok_def; binop_mod_v_def; pat_bindings_def; perms_ok_env_def] THEN
  GVS[] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_binop_mod_v];;

let perms_ok_binop_eq_v = prove
 (`!ps. perms_ok ps binop_eq_v`,
  KPERMSAUX_RW[perms_ok_def; binop_eq_v_def; pat_bindings_def; perms_ok_env_def] THEN
  GVS[] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_binop_eq_v];;

let perms_ok_binop_less_v = prove
 (`!ps. perms_ok ps binop_less_v`,
  KPERMSAUX_RW[perms_ok_def; binop_less_v_def; pat_bindings_def; perms_ok_env_def] THEN
  GVS[] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_binop_less_v];;

let perms_ok_binop_v = prove
 (`!ps. perms_ok ps binop_v`,
  KPERMSAUX_RW[perms_ok_def; binop_v_def; pat_bindings_def; perms_ok_env_def] THEN
  GVS[] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_binop_v];;

let perms_ok_findi_1_v = prove
 (`!ps. perms_ok ps findi_1_v`,
  KPERMSAUX_RW[perms_ok_def; findi_1_v_def; pat_bindings_def; perms_ok_env_def] THEN
  GVS[] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_findi_1_v];;

let perms_ok_to_ce_v = prove
 (`!ps. perms_ok ps to_ce_v`,
  KPERMSAUX_RW[perms_ok_def; to_ce_v_def; pat_bindings_def; perms_ok_env_def] THEN
  GVS[] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_to_ce_v];;

let perms_ok_rev_v = prove
 (`!ps. perms_ok ps rev_v`,
  KPERMSAUX_RW[perms_ok_def; KPERMSAUX_FETCH "rev_v_def"; pat_bindings_def; perms_ok_env_def] THEN
  GVS[] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_rev_v];;

let perms_ok_reverse_v = prove
 (`!ps. perms_ok ps reverse_v`,
  KPERMSAUX_RW[perms_ok_def; KPERMSAUX_FETCH "reverse_v_def"; pat_bindings_def;
               perms_ok_env_def] THEN
  GVS[] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_reverse_v];;

let perms_ok_compile_to_ce_v = prove
 (`!ps. perms_ok ps compile_to_ce_v`,
  KPERMSAUX_RW[perms_ok_def; compile_to_ce_v_def; pat_bindings_def; perms_ok_env_def] THEN
  GVS[] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_compile_to_ce_v];;

let perms_ok_build_funs_v = prove
 (`!ps. perms_ok ps build_funs_v`,
  KPERMSAUX_RW[perms_ok_def; build_funs_v_def; pat_bindings_def; perms_ok_env_def] THEN
  GVS[] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_build_funs_v];;

let perms_ok_compute_thms_v = prove
 (`!ps. perms_ok ps compute_thms_v`,
  GEN_TAC THEN IRULE LIST_TYPE_THM_perms_ok THEN IRULE_AT Any compute_thms_v_thm);;
let _ = cake_add_simps [perms_ok_compute_thms_v];;

let perms_ok_compute_init_v = prove
 (`!ps. perms_ok ps compute_init_v`,
  KPERMSAUX_RW[perms_ok_def; compute_init_v_def; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_compute_init_v];;

let perms_ok_list_dest_comb_v = prove
 (`!ps. perms_ok ps list_dest_comb_v`,
  ONCE_REWRITE_TAC[list_dest_comb_v_def] THEN
  KPERMSAUX_RW[perms_ok_def; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_list_dest_comb_v];;

let perms_ok_mapoption_v = prove
 (`!ps. perms_ok ps mapoption_v`,
  KPERMSAUX_RW[perms_ok_def; mapoption_v_def; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_mapoption_v];;

let perms_ok_i_v = prove
 (`!ps. perms_ok ps i_v`,
  KPERMSAUX_RW[perms_ok_def; KPERMSAUX_FETCH "i_v_def"; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_i_v];;

let perms_ok_dest_num_v = prove
 (`!ps. perms_ok ps dest_num_v`,
  KPERMSAUX_RW[perms_ok_def; dest_num_v_def; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_dest_num_v];;

let perms_ok_dest_numeral_v = prove
 (`!ps. perms_ok ps dest_numeral_v`,
  KPERMSAUX_RW[perms_ok_def; dest_numeral_v_def; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_dest_numeral_v];;

let perms_ok_dest_binary_v = prove
 (`!ps. perms_ok ps dest_binary_v`,
  KPERMSAUX_RW[perms_ok_def; dest_binary_v_def; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_dest_binary_v];;

let perms_ok_dest_numeral_opt_v = prove
 (`!ps. perms_ok ps dest_numeral_opt_v`,
  KPERMSAUX_RW[perms_ok_def; dest_numeral_opt_v_def; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_dest_numeral_opt_v];;

let perms_ok_hd_v = prove
 (`!ps. perms_ok ps hd_v`,
  KPERMSAUX_RW[perms_ok_def; KPERMSAUX_FETCH "hd_v_def"; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_hd_v];;

let perms_ok_dest_cexp_v = prove
 (`!ps. perms_ok ps dest_cexp_v`,
  ONCE_REWRITE_TAC[dest_cexp_v_def] THEN
  KPERMSAUX_RW[perms_ok_def; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_dest_cexp_v];;

let perms_ok_check_cexp_closed_v = prove
 (`!ps. perms_ok ps check_cexp_closed_v`,
  KPERMSAUX_RW[perms_ok_def; check_cexp_closed_v_def; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_check_cexp_closed_v];;

let perms_ok_map_2_v = prove
 (`!ps. perms_ok ps map_2_v`,
  KPERMSAUX_RW[perms_ok_def; map_2_v_def; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_map_2_v];;

let perms_ok_all_distinct_v = prove
 (`!ps. perms_ok ps all_distinct_v`,
  KPERMSAUX_RW[perms_ok_def; KPERMSAUX_FETCH "all_distinct_v_def"; pat_bindings_def;
               perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_all_distinct_v];;

let perms_ok_check_var_v = prove
 (`!ps. perms_ok ps check_var_v`,
  KPERMSAUX_RW[perms_ok_def; check_var_v_def; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_check_var_v];;

let perms_ok_var_list_v = prove
 (`!ps. perms_ok ps var_list_v`,
  KPERMSAUX_RW[perms_ok_def; var_list_v_def; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_var_list_v];;

let perms_ok_check_eqn_v = prove
 (`!ps. perms_ok ps check_eqn_v`,
  KPERMSAUX_RW[perms_ok_def; check_eqn_v_def; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_check_eqn_v];;

let perms_ok_const_list_v = prove
 (`!ps. perms_ok ps const_list_v`,
  KPERMSAUX_RW[perms_ok_def; const_list_v_def; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_const_list_v];;

let perms_ok_check_consts_v = prove
 (`!ps. perms_ok ps check_consts_v`,
  KPERMSAUX_RW[perms_ok_def; check_consts_v_def; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_check_consts_v];;

let perms_ok_compute_default_clock_v = prove
 (`!ps. perms_ok ps compute_default_clock_v`,
  ASSUME_TAC compute_default_clock_v_thm THEN
  GVS[compute_default_clock; ml_NUM_def; ml_INT_def; perms_ok_def]);;
let _ = cake_add_simps [perms_ok_compute_default_clock_v];;

let perms_ok_bool_ty_v = prove
 (`perms_ok kernel_perms bool_ty_v`,
  ASSUME_TAC (REWRITE_RULE[holKernel_bool_ty_def; TYPE_TYPE_def; LIST_TYPE_def;
                           STRING_TYPE_def] bool_ty_v_thm) THEN
  RFS[] THEN RW[perms_ok_def]);;
let _ = cake_add_simps [perms_ok_bool_ty_v];;

let perms_ok_aty_v = prove
 (`perms_ok kernel_perms aty_v`,
  ASSUME_TAC (REWRITE_RULE[holKernel_aty_def; TYPE_TYPE_def; LIST_TYPE_def;
                           STRING_TYPE_def] aty_v_thm) THEN
  RFS[] THEN RW[perms_ok_def]);;
let _ = cake_add_simps [perms_ok_aty_v];;

(* ------------------------------------------------------------------------- *)
(* Functions translated with m_translate should be proved for kernel_perms  *)
(* ------------------------------------------------------------------------- *)

let perms_ok_the_type_constants = prove
 (`perms_ok kernel_perms the_type_constants`,
  KPERMSAUX_RW[perms_ok_def; the_type_constants_def] THEN
  KPERMSAUX_RW[kernel_perms_def; kernel_locs_def; the_type_constants_def]);;
let _ = cake_add_simps [perms_ok_the_type_constants];;

let perms_ok_the_term_constants = prove
 (`perms_ok kernel_perms the_term_constants`,
  KPERMSAUX_RW[perms_ok_def; the_term_constants_def] THEN
  KPERMSAUX_RW[kernel_perms_def; kernel_locs_def; the_term_constants_def]);;
let _ = cake_add_simps [perms_ok_the_term_constants];;

let perms_ok_the_axioms = prove
 (`perms_ok kernel_perms the_axioms`,
  KPERMSAUX_RW[perms_ok_def; the_axioms_def] THEN
  KPERMSAUX_RW[kernel_perms_def; kernel_locs_def; the_axioms_def]);;
let _ = cake_add_simps [perms_ok_the_axioms];;

let perms_ok_constants_v = prove
 (`perms_ok kernel_perms constants_v`,
  KPERMSAUX_RW[perms_ok_def; constants_v_def; pat_bindings_def] THEN
  KPERMSAUX_RW[perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_constants_v];;

let perms_ok_types_v = prove
 (`perms_ok kernel_perms types_v`,
  KPERMSAUX_RW[perms_ok_def; types_v_def; pat_bindings_def] THEN
  KPERMSAUX_RW[perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_types_v];;

let perms_ok_axioms_v = prove
 (`perms_ok kernel_perms axioms_v`,
  KPERMSAUX_RW[perms_ok_def; axioms_v_def; pat_bindings_def] THEN
  KPERMSAUX_RW[perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_axioms_v];;

let perms_ok_get_type_arity_v = prove
 (`perms_ok kernel_perms get_type_arity_v`,
  KPERMSAUX_RW[perms_ok_def; get_type_arity_v_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_get_type_arity_v];;

let perms_ok_mk_type_v = prove
 (`perms_ok kernel_perms mk_type_v`,
  KPERMSAUX_RW[perms_ok_def; mk_type_v_def; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_mk_type_v];;

let perms_ok_mk_fun_ty_v = prove
 (`perms_ok kernel_perms mk_fun_ty_v`,
  KPERMSAUX_RW[perms_ok_def; mk_fun_ty_v_def; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_mk_fun_ty_v];;

let perms_ok_type_of_v = prove
 (`perms_ok kernel_perms type_of_v`,
  KPERMSAUX_RW[perms_ok_def; type_of_v_def; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_type_of_v];;

let perms_ok_call_type_of_v = prove
 (`perms_ok kernel_perms call_type_of_v`,
  KPERMSAUX_RW[perms_ok_def; call_type_of_v_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_call_type_of_v];;

let perms_ok_get_const_type_v = prove
 (`perms_ok kernel_perms get_const_type_v`,
  KPERMSAUX_RW[perms_ok_def; get_const_type_v_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_get_const_type_v];;

let perms_ok_mk_const_v = prove
 (`perms_ok kernel_perms mk_const_v`,
  KPERMSAUX_RW[perms_ok_def; mk_const_v_def; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_mk_const_v];;

let perms_ok_mk_comb_v = prove
 (`perms_ok kernel_perms mk_comb_v`,
  KPERMSAUX_RW[perms_ok_def; mk_comb_v_def; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_mk_comb_v];;

let perms_ok_mk_eq_v = prove
 (`perms_ok kernel_perms mk_eq_v`,
  KPERMSAUX_RW[perms_ok_def; mk_eq_v_def; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_mk_eq_v];;

let perms_ok_safe_mk_eq_v = prove
 (`perms_ok kernel_perms safe_mk_eq_v`,
  KPERMSAUX_RW[perms_ok_def; safe_mk_eq_v_def; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_safe_mk_eq_v];;

let perms_ok_mk_comb_1_v = prove
 (`perms_ok kernel_perms mk_comb_1_v`,
  KPERMSAUX_RW[perms_ok_def; mk_comb_1_v_def; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_mk_comb_1_v];;

let perms_ok_refl_v = prove
 (`perms_ok kernel_perms refl_v`,
  KPERMSAUX_RW[perms_ok_def; refl_v_def; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_refl_v];;

let perms_ok_assume_v = prove
 (`perms_ok kernel_perms assume_v`,
  KPERMSAUX_RW[perms_ok_def; assume_v_def; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_assume_v];;

let perms_ok_deduct_antisym_rule_v = prove
 (`perms_ok kernel_perms deduct_antisym_rule_v`,
  KPERMSAUX_RW[perms_ok_def; deduct_antisym_rule_v_def; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_deduct_antisym_rule_v];;

let perms_ok_vsubst_v = prove
 (`perms_ok kernel_perms vsubst_v`,
  KPERMSAUX_RW[perms_ok_def; vsubst_v_def; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_vsubst_v];;

let perms_ok_inst_1_v = prove
 (`perms_ok kernel_perms inst_1_v`,
  KPERMSAUX_RW[perms_ok_def; inst_1_v_def; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_inst_1_v];;

let perms_ok_beta_v = prove
 (`perms_ok kernel_perms beta_v`,
  KPERMSAUX_RW[perms_ok_def; beta_v_def; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_beta_v];;

let perms_ok_trans_v = prove
 (`perms_ok kernel_perms trans_v`,
  KPERMSAUX_RW[perms_ok_def; trans_v_def; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_trans_v];;

let perms_ok_abs_v = prove
 (`perms_ok kernel_perms abs_v`,
  KPERMSAUX_RW[perms_ok_def; ml_hol_kernel_funsProg_abs_v_def; pat_bindings_def;
               perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_abs_v];;

let perms_ok_check_for_dups_v = prove
 (`!ps. perms_ok ps check_for_dups_v`,
  KPERMSAUX_RW[perms_ok_def; check_for_dups_v_def; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_check_for_dups_v];;

let perms_ok_add_constants_v = prove
 (`perms_ok kernel_perms add_constants_v`,
  KPERMSAUX_RW[perms_ok_def; add_constants_v_def; pat_bindings_def; perms_ok_env_def] THEN
  TRY(KPERMSAUX_LOOKUP_TAC) THEN
  KPERMSAUX_RW[] THEN
  KPERMSAUX_RW[kernel_perms_def]);;
let _ = cake_add_simps [perms_ok_add_constants_v];;

let perms_ok_the_context = prove
 (`perms_ok kernel_perms the_context`,
  KPERMSAUX_RW[the_context_def; perms_ok_def; kernel_perms_def; kernel_locs_def]);;
let _ = cake_add_simps [perms_ok_the_context];;

let perms_ok_add_def_v = prove
 (`perms_ok kernel_perms add_def_v`,
  KPERMSAUX_RW[perms_ok_def; add_def_v_def; pat_bindings_def; perms_ok_env_def] THEN
  TRY(KPERMSAUX_LOOKUP_TAC) THEN
  KPERMSAUX_RW[] THEN
  KPERMSAUX_RW[kernel_perms_def]);;
let _ = cake_add_simps [perms_ok_add_def_v];;

let perms_ok_new_constant_v = prove
 (`perms_ok kernel_perms new_constant_v`,
  KPERMSAUX_RW[perms_ok_def; new_constant_v_def; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_new_constant_v];;

let perms_ok_add_type_v = prove
 (`perms_ok kernel_perms add_type_v`,
  KPERMSAUX_RW[perms_ok_def; add_type_v_def; pat_bindings_def; perms_ok_env_def] THEN
  TRY(KPERMSAUX_LOOKUP_TAC) THEN
  KPERMSAUX_RW[] THEN
  KPERMSAUX_RW[kernel_perms_def]);;
let _ = cake_add_simps [perms_ok_add_type_v];;

let perms_ok_new_type_v = prove
 (`perms_ok kernel_perms new_type_v`,
  KPERMSAUX_RW[perms_ok_def; new_type_v_def; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_new_type_v];;

let perms_ok_call_new_type_v = prove
 (`perms_ok kernel_perms call_new_type_v`,
  KPERMSAUX_RW[perms_ok_def; call_new_type_v_def; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_call_new_type_v];;

let perms_ok_new_axiom_v = prove
 (`perms_ok kernel_perms new_axiom_v`,
  KPERMSAUX_RW[perms_ok_def; new_axiom_v_def; pat_bindings_def; perms_ok_env_def] THEN
  TRY(KPERMSAUX_LOOKUP_TAC) THEN
  KPERMSAUX_RW[] THEN
  KPERMSAUX_RW[kernel_perms_def]);;
let _ = cake_add_simps [perms_ok_new_axiom_v];;

let perms_ok_new_specification_v = prove
 (`perms_ok kernel_perms new_specification_v`,
  KPERMSAUX_RW[perms_ok_def; new_specification_v_def; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_new_specification_v];;

let perms_ok_new_basic_definition_v = prove
 (`perms_ok kernel_perms new_basic_definition_v`,
  KPERMSAUX_RW[perms_ok_def; new_basic_definition_v_def; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[] THEN
  KPERMSAUX_RW[kernel_perms_def]);;
let _ = cake_add_simps [perms_ok_new_basic_definition_v];;

let perms_ok_new_basic_type_definition_v = prove
 (`perms_ok kernel_perms new_basic_type_definition_v`,
  KPERMSAUX_RW[perms_ok_def; new_basic_type_definition_v_def; pat_bindings_def;
               perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_new_basic_type_definition_v];;

let perms_ok_compute_add_v = prove
 (`perms_ok kernel_perms compute_add_v`,
  KPERMSAUX_RW[perms_ok_def; compute_add_v_def; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_compute_add_v];;

let perms_ok_compute_v = prove
 (`perms_ok kernel_perms compute_v`,
  KPERMSAUX_RW[perms_ok_def; compute_v_def; pat_bindings_def; perms_ok_env_def] THEN
  KPERMSAUX_LOOKUP_TAC THEN
  KPERMSAUX_RW[]);;
let _ = cake_add_simps [perms_ok_compute_v];;

(* HOL4 [local] *)
let evaluate_kernel_perms_lemma = prove
 (`!ps (s:(FFI)state) env exp s' res.
     evaluate s env [exp] = (s',res) /\
     perms_ok_exp ps exp /\ perms_ok_env ps (freevars exp) env /\ perms_ok_state ps s /\
     ~(DoFFI IN ps) /\ ~(RefAlloc IN ps) /\ ~(W8Alloc IN ps) ==>
     LENGTH (state_refs s') = LENGTH (state_refs s) /\
     state_ffi s' = state_ffi s /\
     state_eval_state s' = state_eval_state s`,
  MESON_TAC[evaluate_perms_ok_exp]);;

(* HOL4: evaluate_kernel_perms_lemma |> Q.SPEC `kernel_perms`                 *)
(*         |> SIMP_RULE (srw_ss()) [kernel_perms_def]                          *)
(*         |> REWRITE_RULE [GSYM kernel_perms_def]                             *)
let evaluate_kernel_perms = prove
 (`!(s:(FFI)state) env exp s' res.
     evaluate s env [exp] = (s',res) /\
     perms_ok_exp kernel_perms exp /\ perms_ok_env kernel_perms (freevars exp) env /\
     perms_ok_state kernel_perms s ==>
     LENGTH (state_refs s') = LENGTH (state_refs s) /\
     state_ffi s' = state_ffi s /\
     state_eval_state s' = state_eval_state s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC (SPEC `kernel_perms` evaluate_kernel_perms_lemma) THEN
  EXISTS_TAC `env:v sem_env` THEN EXISTS_TAC `exp:exp` THEN EXISTS_TAC `res:(v list,v)result` THEN
  ASM_REWRITE_TAC[kernel_perms_def; IN_UNION; IN_IMAGE; IN_SING;
                  distinctness "permission"]);;

(* HOL4: evaluate_kernel_perms_lemma |> Q.SPEC `{}` |> SIMP_RULE (srw_ss()) [] *)
let evaluate_empty_perms = prove
 (`!(s:(FFI)state) env exp s' res.
     evaluate s env [exp] = (s',res) /\
     perms_ok_exp {} exp /\ perms_ok_env {} (freevars exp) env /\ perms_ok_state {} s ==>
     LENGTH (state_refs s') = LENGTH (state_refs s) /\
     state_ffi s' = state_ffi s /\
     state_eval_state s' = state_eval_state s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC (SPEC `{}:permission->bool` evaluate_kernel_perms_lemma) THEN
  EXISTS_TAC `env:v sem_env` THEN EXISTS_TAC `exp:exp` THEN EXISTS_TAC `res:(v list,v)result` THEN
  ASM_REWRITE_TAC[NOT_IN_EMPTY]);;
