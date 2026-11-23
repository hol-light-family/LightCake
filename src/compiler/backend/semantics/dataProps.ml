(* ========================================================================= *)
(* dataProps: port of HOL4 compiler/backend/semantics/dataPropsScript.sml    *)
(* (CakeML v3479).  Properties about dataLang and its semantics.             *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - HOL4 r with f := v is dataSem's data_state_f_fupd (K v) r; the HOL4      *)
(*   overloads do_space_safe, do_space_peak, do_app_safe and do_app_peak of  *)
(*   dataSem are written out (statements are built with DSEMAUX_expand).    *)
(* - DSEMAUX_ names are local helpers of this file.                         *)
(* ========================================================================= *)

needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "compiler/backend/dataLang.ml";;
needs "compiler/backend/semantics/dataSem.ml";;
needs "semantics/proofs/semanticsProps.ml";;
needs "compiler/backend/semantics/backendProps.ml";;

type_invention_error := true;;

(* HOL4 [local] *)
let data_OPTION_CASE_OPTION_MAP = prove
 (`!(f:A->B) (a:A option) (e:C) (g:B->C).
     option_CASE (OPTION_MAP f a) e g = option_CASE a e (g o f)`,
  GEN_TAC THEN GEN_TAC THEN CASES_ON `a:A option` THEN
  REWRITE_TAC[OPTION_MAP_DEF; option_CASE; o_THM]);;

(* HOL4's termination relation:                                              *)
(*   inv_image (measure I LEX measure (list_size v_size))                    *)
(*             (\(lims,vs,refs). (sptree$size refs,vs))                      *)

let approx_of_def = cake_def_wf
  `inv_image (MEASURE (I:num->num) LEX MEASURE (list_size data_v_size))
     (\x:limits # data_v list # ((data_v)bvl_ref)spt.
        sptree_size (SND (SND x)),FST (SND x))`
  DSEMAUX_SIZE_OF_TC_TAC
  `(approx_of (lims:limits) ([]:data_v list) (refs:((data_v)bvl_ref)spt) = 0) /\
   (approx_of lims (CONS x (CONS y ys)) refs =
      approx_of lims [x] refs + approx_of lims (CONS y ys) refs) /\
   (approx_of lims [data_Word64 _] refs = 3) /\
   (approx_of lims [data_Number i] refs =
      (if small_num (limits_arch_64_bit lims) i then 0
       else bignum_size (limits_arch_64_bit lims) i)) /\
   (approx_of lims [data_CodePtr _] refs = 0) /\
   (approx_of lims [data_RefPtr _ r] refs =
      match lookup r refs with
        NONE -> 0
      | SOME (bvl_ByteArray _ bs) -> LENGTH bs DIV (arch_size lims DIV 8) + 2
      | SOME (bvl_ValueArray vs) ->
          approx_of lims vs (delete r refs) + LENGTH vs + 1
      | SOME (bvl_Thunk _ v) ->
          approx_of lims [v] (delete r refs) + 2
      | SOME (MutBlock tg fin ls c rs) ->
          approx_of lims (APPEND (APPEND ls [c]) rs) (delete r refs) +
          LENGTH ls + LENGTH rs + 2) /\
   (approx_of lims [data_Block ts tag []] refs = 0) /\
   (approx_of lims [data_Block ts tag vs] refs =
      approx_of lims vs refs + LENGTH vs + 1)`;;

let approx_of_ind = cake_ind "approx_of";;

let DSEMAUX_subspt_delete2 = prove
 (`!(a:A spt) b r. subspt a b ==> subspt (delete r a) (delete r b)`,
  REWRITE_TAC[subspt_lookup; lookup_delete] THEN MESON_TAC[]);;

let DSEMAUX_subspt_delete_self = prove
 (`!(a:A spt) r. subspt (delete r a) a`,
  MESON_TAC[subspt_delete; subspt_refl]);;

let DSEMAUX_size_of_approx_of = prove
 (`!lims xs refs seen refsT n1 refs1 seen1.
     size_of lims xs refs seen = (n1,refs1,seen1) /\ subspt refs refsT ==>
     n1 <= approx_of lims xs refsT /\ subspt refs1 (refs:((data_v)bvl_ref)spt)`,
  MATCH_MP_TAC size_of_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[size_of_def; approx_of_def; PAIR_EQ] THEN
    MESON_TAC[LE_REFL; subspt_refl];
    STRIP_TAC THEN REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[size_of_def] THEN
    REPEAT PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
    GVS[] THEN REWRITE_TAC[approx_of_def] THEN
    SUBGOAL_THEN `n1' <= approx_of lims (CONS y ys) refsT /\
                  subspt refs1' (refs:((data_v)bvl_ref)spt)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `n2 <= approx_of lims [x] refsT /\
                  subspt refs1 (refs1':((data_v)bvl_ref)spt)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[subspt_trans]; ALL_TAC] THEN
    CONJ_TAC THENL
     [REPEAT(FIRST_X_ASSUM(MP_TAC o check (CLOSSEMAUX_is_num_fact o concl))) THEN
      ARITH_TAC;
      ASM_MESON_TAC[subspt_trans]];
    REWRITE_TAC[size_of_def; approx_of_def; PAIR_EQ] THEN
    MESON_TAC[LE_REFL; subspt_refl];
    REWRITE_TAC[size_of_def; approx_of_def; PAIR_EQ] THEN
    MESON_TAC[LE_REFL; subspt_refl];
    REWRITE_TAC[size_of_def; approx_of_def; PAIR_EQ] THEN
    MESON_TAC[LE_REFL; subspt_refl];
    STRIP_TAC THEN REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[size_of_def] THEN
    TOP_CASE_TAC THEN REWRITE_TAC[PAIR_EQ] THENL
     [MESON_TAC[LE_0; subspt_refl]; ALL_TAC] THEN
    TOP_CASE_TAC THEN REWRITE_TAC[PAIR_EQ] THEN REPEAT PAIRARG_TAC THEN
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN GVS[] THEN
    (SUBGOAL_THEN `lookup r (refsT:((data_v)bvl_ref)spt) = lookup r refs`
       ASSUME_TAC THENL [ASM_MESON_TAC[subspt_lookup]; ALL_TAC]) THEN
    ONCE_REWRITE_TAC[approx_of_def] THEN ASM_REWRITE_TAC[] THEN
    CASE_REWRITE_TAC[] THEN
    TRY (CONJ_TAC THENL [ARITH_TAC; MESON_TAC[DSEMAUX_subspt_delete_self]]) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `delete r (refsT:((data_v)bvl_ref)spt)`) THEN
    (ANTS_TAC THENL [ASM_MESON_TAC[DSEMAUX_subspt_delete2]; ALL_TAC]) THEN
    STRIP_TAC THEN
    (CONJ_TAC THENL
      [REPEAT(FIRST_X_ASSUM(MP_TAC o check (CLOSSEMAUX_is_num_fact o concl))) THEN
       ARITH_TAC;
       ASM_MESON_TAC[subspt_trans; DSEMAUX_subspt_delete_self]]);
    REWRITE_TAC[size_of_def; approx_of_def; PAIR_EQ] THEN
    MESON_TAC[LE_REFL; subspt_refl];
    STRIP_TAC THEN REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[size_of_def] THEN
    COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THENL
     [MESON_TAC[LE_0; subspt_refl]; ALL_TAC] THEN
    REPEAT PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN GVS[] THEN
    ONCE_REWRITE_TAC[approx_of_def] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `refsT:((data_v)bvl_ref)spt`) THEN
    ASM_REWRITE_TAC[LENGTH] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT2 th] THEN MP_TAC(CONJUNCT1 th)) THEN
    ARITH_TAC]);;

let size_of_approx_of = prove
 (`!lims xs refs seen n1 refs1 seen1.
     size_of lims xs refs seen = (n1,refs1,seen1) ==>
     n1 <= approx_of lims xs (refs:((data_v)bvl_ref)spt)`,
  MESON_TAC[DSEMAUX_size_of_approx_of; subspt_refl]);;

let OPTION_MAP2_ADD_SOME_0 = prove
 (`!x. OPTION_MAP2 (+) x (SOME 0) = x`,
  GEN_TAC THEN CASES_ON `x:num option` THEN
  REWRITE_TAC[OPTION_MAP2_DEF; IS_SOME_DEF; THE_DEF; ADD_CLAUSES]);;
let _ = cake_add_simps [OPTION_MAP2_ADD_SOME_0];;

let OPTION_MAP2_MAX_CANCEL = prove
 (`!x y. OPTION_MAP2 MAX (OPTION_MAP2 MAX x y) y = OPTION_MAP2 MAX x (y:num option)`,
  REPEAT GEN_TAC THEN CASES_ON `x:num option` THEN CASES_ON `y:num option` THEN
  REWRITE_TAC[OPTION_MAP2_DEF; IS_SOME_DEF; THE_DEF; option_INJ] THEN ARITH_TAC);;
let _ = cake_add_simps [OPTION_MAP2_MAX_CANCEL];;

(* ops that are not allowed_op have stack_consumed = NONE, which has to     *)
(* propagate through do_stack's safe_for_space computation                  *)

let data_OPTION_MAP2_NONE = prove
 (`!(f:A->B->C) x y. OPTION_MAP2 f NONE y = NONE /\ OPTION_MAP2 f x NONE = NONE`,
  REWRITE_TAC[OPTION_MAP2_DEF; IS_SOME_DEF]);;
let _ = cake_add_simps [data_OPTION_MAP2_NONE];;

let the_NONE = prove
 (`!x:A. misc_the x NONE = x`,
  REWRITE_TAC[misc_the_def]);;
let _ = cake_add_simps [the_NONE];;

let data_initial_state_simp = prove
 (`!(f:(FFI)ffi_state) c (co:num -> C # (num # num # data_prog) list) cc ts l ss k.
     data_state_clock (data_initial_state f c co cc ts l ss k) = k /\
     data_state_locals (data_initial_state f c co cc ts l ss k) = LN /\
     data_state_code (data_initial_state f c co cc ts l ss k) = c /\
     data_state_ffi (data_initial_state f c co cc ts l ss k) = f /\
     data_state_compile_oracle (data_initial_state f c co cc ts l ss k) = co /\
     data_state_compile (data_initial_state f c co cc ts l ss k) = cc /\
     data_state_stack (data_initial_state f c co cc ts l ss k) = [] /\
     data_state_peak_heap_length (data_initial_state f c co cc ts l ss k) = 0`,
  REWRITE_TAC[data_initial_state_def; data_state_INFO.ri_accessors]);;
let _ = cake_add_simps [data_initial_state_simp];;

let data_initial_state_with_simp = prove
 (`!(f:(FFI)ffi_state) c (co:num -> C # (num # num # data_prog) list) cc ts l ss k k'.
     data_state_clock_fupd (K k') (data_initial_state f c co cc ts l ss k) =
     data_initial_state f c co cc ts l ss k' /\
     data_state_stack_fupd (K []) (data_initial_state f c co cc ts l ss k) =
     data_initial_state f c co cc ts l ss k /\
     data_state_locals_fupd (K LN) (data_initial_state f c co cc ts l ss k) =
     data_initial_state f c co cc ts l ss k`,
  REWRITE_TAC[data_initial_state_def; data_state_INFO.ri_fupds; K_THM]);;
let _ = cake_add_simps [data_initial_state_with_simp];;

let do_stack_const = prove
 (`!op vs (s:(C,FFI)data_state).
     data_state_locals (do_stack op vs s) = data_state_locals s /\
     data_state_locals_size (do_stack op vs s) = data_state_locals_size s /\
     data_state_stack (do_stack op vs s) = data_state_stack s /\
     data_state_stack_frame_sizes (do_stack op vs s) = data_state_stack_frame_sizes s /\
     data_state_global (do_stack op vs s) = data_state_global s /\
     data_state_handler (do_stack op vs s) = data_state_handler s /\
     data_state_refs (do_stack op vs s) = data_state_refs s /\
     data_state_compile (do_stack op vs s) = data_state_compile s /\
     data_state_clock (do_stack op vs s) = data_state_clock s /\
     data_state_code (do_stack op vs s) = data_state_code s /\
     data_state_ffi (do_stack op vs s) = data_state_ffi s /\
     data_state_space (do_stack op vs s) = data_state_space s /\
     data_state_tstamps (do_stack op vs s) = data_state_tstamps s /\
     data_state_limits (do_stack op vs s) = data_state_limits s /\
     data_state_peak_heap_length (do_stack op vs s) = data_state_peak_heap_length s /\
     data_state_compile_oracle (do_stack op vs s) = data_state_compile_oracle s`,
  REWRITE_TAC[do_stack_def; LET_DEF; LET_END_DEF; data_state_INFO.ri_accfupds]);;
let _ = cake_add_simps [do_stack_const];;

let data_Boolv_11 = prove
 (`!b1 b2. data_Boolv b1 = data_Boolv b2 <=> b1 = b2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_Boolv_def; injectivity "data_v"] THEN
  REWRITE_TAC[bool_to_tag_def] THEN
  MAP_EVERY BOOL_CASES_TAC [`b1:bool`; `b2:bool`] THEN
  REWRITE_TAC[true_tag_def; false_tag_def] THEN ARITH_TAC);;
let _ = cake_add_simps [data_Boolv_11];;

let data_with_same_locals = prove
 (`!s:(C,FFI)data_state. data_state_locals_fupd (K (data_state_locals s)) s = s`,
  REWRITE_TAC[data_state_component_equality; data_state_INFO.ri_accfupds; K_THM]);;

let var_corr_def = cake_def
  `var_corr env corr (t:A spt) <=>
     ALL2 (\v x. data_get_var v t = SOME x) corr env`;;

let get_vars_thm = prove
 (`!vs a (t2:A spt). var_corr a vs t2 ==> data_get_vars vs t2 = SOME a`,
  LIST_INDUCT_TAC THEN GEN_TAC THEN CASES_ON `a:A list` THEN
  REWRITE_TAC[var_corr_def; ALL2; data_get_vars_def] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[var_corr_def]) THEN
  REPEAT STRIP_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]);;

let get_vars_append = prove
 (`!l1 l2 (s:A spt).
     data_get_vars (APPEND l1 l2) s =
     OPTION_BIND (data_get_vars l1 s)
       (\y1. OPTION_BIND (data_get_vars l2 s) (\y2. SOME (APPEND y1 y2)))`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND; data_get_vars_def] THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[OPTION_BIND_DEF; APPEND] THEN
    CASES_ON `data_get_vars l2 (s:A spt)` THEN REWRITE_TAC[OPTION_BIND_DEF];
    REPEAT GEN_TAC THEN ASM_REWRITE_TAC[] THEN
    CASES_ON `data_get_var h (s:A spt)` THEN CASE_REWRITE_TAC[OPTION_BIND_DEF] THEN
    CASES_ON `data_get_vars t (s:A spt)` THEN CASE_REWRITE_TAC[OPTION_BIND_DEF] THEN
    CASES_ON `data_get_vars l2 (s:A spt)` THEN CASE_REWRITE_TAC[OPTION_BIND_DEF; APPEND]]);;

let get_vars_reverse = prove
 (`!ls (s:A spt) ys.
     data_get_vars ls s = SOME ys ==> data_get_vars (REVERSE ls) s = SOME (REVERSE ys)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[data_get_vars_def; REVERSE; option_INJ] THENL
   [MESON_TAC[REVERSE]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  CASES_ON `data_get_var h (s:A spt)` THEN CASE_REWRITE_TAC[option_DISTINCT] THEN
  CASES_ON `data_get_vars t (s:A spt)` THEN CASE_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[get_vars_append; REVERSE] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`s:A spt`; `a':A list`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[OPTION_BIND_DEF; data_get_vars_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[OPTION_BIND_DEF]);;

let EVERY_get_vars = prove
 (`!args (s1:A spt) s2.
     ALL (\a. lookup a s1 = lookup a s2) args ==>
     data_get_vars args s1 = data_get_vars args s2`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; data_get_vars_def; data_get_var_def] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`s1:A spt`; `s2:A spt`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]);;

let data_get_vars_IMP_domain = prove
 (`!args x (s:A spt) vs.
     MEM x args /\ data_get_vars args s = SOME vs ==> x IN domain s`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; data_get_vars_def; data_get_var_def] THEN
  REPEAT GEN_TAC THEN
  CASES_ON `lookup h (s:A spt)` THEN CASE_REWRITE_TAC[option_DISTINCT] THEN
  CASES_ON `data_get_vars t (s:A spt)` THEN CASE_REWRITE_TAC[option_DISTINCT] THEN
  STRIP_TAC THENL
   [ASM_MESON_TAC[domain_lookup];
    ASM_MESON_TAC[]]);;

let cut_state_opt_with_const = prove
 (`!x (y:(C,FFI)data_state) z k lsz.
     data_cut_state_opt x (data_state_stack_fupd (K z) y) =
     OPTION_MAP (\s. data_state_stack_fupd (K z) s) (data_cut_state_opt x y) /\
     data_cut_state_opt x (data_state_clock_fupd (K k) y) =
     OPTION_MAP (\s. data_state_clock_fupd (K k) s) (data_cut_state_opt x y) /\
     data_cut_state_opt x (data_state_locals_size_fupd (K lsz) y) =
     OPTION_MAP (\s. data_state_locals_size_fupd (K lsz) s) (data_cut_state_opt x y)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[data_cut_state_opt_def; data_cut_state_def;
              data_state_INFO.ri_accfupds] THEN
  REPEAT TOP_CASE_TAC THEN
  REWRITE_TAC[OPTION_MAP_DEF; option_INJ; data_state_INFO.ri_fupdcanon]);;

(* INFO: only used in bvi_to_dataProof *)
let consume_space_add_space = prove
 (`!k (t:(C,FFI)data_state) env1.
     ?sf hp. consume_space k (add_space (data_state_locals_fupd (K env1) t) k) =
             SOME (data_state_locals_fupd (K env1)
                     (data_state_space_fupd (K 0)
                        (data_state_safe_for_space_fupd (K sf)
                           (data_state_peak_heap_length_fupd (K hp) t))))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[consume_space_def; add_space_def; data_state_INFO.ri_accfupds; K_THM;
              LT_REFL; SUB_REFL; option_INJ] THEN
  REWRITE_TAC[data_state_component_equality; data_state_INFO.ri_accfupds; K_THM] THEN
  MESON_TAC[]);;

(* HOL4 [local] *)
let consume_space_with_stack = prove
 (`!x (y:(C,FFI)data_state) z.
     consume_space x (data_state_stack_fupd (K z) y) =
     OPTION_MAP (\s. data_state_stack_fupd (K z) s) (consume_space x y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[consume_space_def; data_state_INFO.ri_accfupds] THEN
  COND_CASES_TAC THEN REWRITE_TAC[OPTION_MAP_DEF; option_INJ] THEN
  REWRITE_TAC[data_state_INFO.ri_fupdcanon]);;

(* HOL4 [local] *)
let consume_space_with_locals = prove
 (`!x (y:(C,FFI)data_state) z.
     consume_space x (data_state_locals_fupd (K z) y) =
     OPTION_MAP (\s. data_state_locals_fupd (K z) s) (consume_space x y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[consume_space_def; data_state_INFO.ri_accfupds] THEN
  COND_CASES_TAC THEN REWRITE_TAC[OPTION_MAP_DEF; option_INJ] THEN
  REWRITE_TAC[data_state_INFO.ri_fupdcanon]);;

(* ------------------------------------------------------------------------- *)
(* Helpers for the do_app lemmas: record normalisation, the HOL4 overloads   *)
(* of dataSem written out, and a case split of the operator.                *)
(* ------------------------------------------------------------------------- *)

let DSEMAUX_K_o = prove
 (`!(x:A) (g:B->C). (K x) o g = K x`,
  REWRITE_TAC[FUN_EQ_THM; o_THM; K_THM]);;

let DSEMAUX_rec_rws =
  [data_state_INFO.ri_accfupds; data_state_INFO.ri_fupdcanon;
   data_state_INFO.ri_fupdfupds; DSEMAUX_K_o; K_THM];;

(* HOL4's overloads do_space_safe, do_space_peak, do_app_safe, do_app_peak *)
(* (dataSem); DSEMAUX_expand tm replaces the variables of these names in   *)
(* tm by the overloaded terms and beta-reduces                              *)

let DSEMAUX_overload_defs =
  [`do_space_safe:clos_op->data_v list->(C,FFI)data_state->bool`,
   `\op vs (s:(C,FFI)data_state).
      if op_space_reset op
      then data_state_safe_for_space s /\ no_thunks_in_refs (data_state_refs s) /\
           size_of_heap_args vs s + space_consumed s op vs
             <= limits_heap_limit (data_state_limits s)
      else data_state_safe_for_space s`;
   `do_space_peak:clos_op->data_v list->(C,FFI)data_state->num`,
   `\op vs (s:(C,FFI)data_state).
      if op_space_reset op
      then MAX (data_state_peak_heap_length s)
               (size_of_heap_args vs s + space_consumed s op vs)
      else data_state_peak_heap_length s`;
   `do_app_safe:clos_op->data_v list->(C,FFI)data_state->bool`,
   `\op vs (s:(C,FFI)data_state).
      if allowed_op op (LENGTH vs)
      then ((do_space_safe:clos_op->data_v list->(C,FFI)data_state->bool) op vs s /\
            lim_safe (data_state_limits s) op vs /\
            misc_the F (OPTION_MAP ((>) (limits_stack_limit (data_state_limits s)))
                     (OPTION_MAP2 (+)
                        (stack_consumed (data_state_stack_frame_sizes s)
                           (data_state_limits s) op vs)
                        (OPTION_MAP2 (+) (size_of_stack (data_state_stack s))
                           (data_state_locals_size s)))))
      else F`;
   `do_app_peak:clos_op->data_v list->(C,FFI)data_state->num`,
   `\op vs (s:(C,FFI)data_state).
      if op = clos_Install then data_state_peak_heap_length s
      else if MEM op [IntOp Greater; IntOp GreaterEq]
      then data_state_peak_heap_length s
      else (do_space_peak:clos_op->data_v list->(C,FFI)data_state->num) op
             (vs:data_v list) s`];;

let DSEMAUX_expand tm =
  let sub = map (fun (v,l) -> (l,v)) DSEMAUX_overload_defs in
  let rec go t = let t' = subst sub t in if t' = t then t else go t' in
  rhs(concl(TOP_DEPTH_CONV BETA_CONV (go tm)));;

(* split the operator op (a variable of the goal) into its leaf            *)
(* constructors (HOL4's cases_on_op_fs); STRUCT_CASES_TAC rewrites the goal *)

let DSEMAUX_OP_CASES_TAC (op:term) : tactic =
  let subs = ["IntOp","int_op"; "WordOp","word_op"; "BlockOp","block_op";
              "GlobOp","glob_op"; "MemOp","mem_op"; "clos_ThunkOp","thunk_op"] in
  STRUCT_CASES_TAC (ISPEC op (cases "clos_op")) THEN
  (fun (asl,w as g) ->
     try let t = find_term (fun t -> is_comb t && is_const (rator t) &&
                                     mem (fst(dest_const(rator t))) (map fst subs) &&
                                     is_var (rand t)) w in
         let ty = assoc (fst(dest_const(rator t))) subs in
         STRUCT_CASES_TAC (ISPEC (rand t) (cases ty)) g
     with Failure _ -> ALL_TAC g);;

let DSEMAUX_fupd_id =
  let names = map (fun (f,_,_) -> f) data_state_INFO.ri_fields in
  let cl f = "data_state_" ^ f ^ "_fupd (K (data_state_" ^ f ^ " r)) r = r" in
  let tm = parse_term ("!r:(C,FFI)data_state. " ^
                       String.concat " /\\ " (map cl names)) in
  prove(tm, GEN_TAC THEN REWRITE_TAC[data_state_component_equality;
                                     data_state_INFO.ri_accfupds; K_THM]);;

let DSEMAUX_EXP_POS = prove
 (`!n. 0 < 2 EXP n /\ (2 EXP n = 0 <=> F)`,
  REWRITE_TAC[LT_NZ; EXP_EQ_0; ARITH_EQ]);;

let DSEMAUX_EXP_GT2 = prove
 (`!l. 2 < 2 EXP l <=> 1 < l`,
  GEN_TAC THEN MP_TAC(SPECL [`2`; `1`; `l:num`] LT_EXP) THEN
  REWRITE_TAC[EXP_1] THEN ARITH_TAC);;

let DSEMAUX_NOT_ALL_NEQ = prove
 (`!(a:num) (b:num). (!t i. ~(a = t /\ b = i)) <=> F`,
  MESON_TAC[]);;

(* the brute-force tactic of the do_app lemmas (HOL4: cases_on_op_fs and   *)
(* full_simp_tac with the definitions and the case_eq theorems): split the *)
(* operator, unfold do_app and its helpers, split every case and          *)
(* conditional, then normalise the records and the safe_for_space flags   *)

let DSEMAUX_DO_APP_DEFS =
  [data_do_app_def; data_do_install_def; do_space_def; consume_space_def;
   do_stack_def; do_lim_safe; data_do_app_aux_def; with_fresh_ts_def;
   check_lim_def; LET_DEF; LET_END_DEF];;

let DSEMAUX_DO_APP_RWS =
  [data_state_INFO.ri_accfupds; K_THM; distinctness "clos_op"; injectivity "clos_op";
   distinctness "int_op"; injectivity "int_op"; MEM; op_space_reset_def;
   op_space_req_def; allowed_op_def];;

let DSEMAUX_FINISH_RWS = DSEMAUX_rec_rws @
  [DSEMAUX_fupd_id; SUB_0; DSEMAUX_EXP_POS; DSEMAUX_EXP_GT2; LENGTH;
   DSEMAUX_NOT_ALL_NEQ; CONJ_ACI];;

let DSEMAUX_FINISH_RWS2 =
  [stack_consumed_def; lim_safe_def; allowed_op_def; injectivity "clos_op";
   injectivity "mem_op"; distinctness "clos_op"; distinctness "mem_op";
   data_OPTION_MAP2_NONE; OPTION_MAP_DEF; misc_the_def] @ DSEMAUX_FINISH_RWS;;

(* do_app is unfolded with CASE_REWRITE_TAC, so that the case on op reduces   *)
(* as it is unfolded instead of after every arm has been rewritten; the same  *)
(* holds for the other users of DSEMAUX_DO_APP_DEFS                           *)
let DSEMAUX_DO_APP_BRUTE_TAC (defs:thm list) : tactic =
   REPEAT GEN_TAC THEN CASE_REWRITE_TAC defs THEN
   CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
   CASE_REWRITE_TAC DSEMAUX_DO_APP_RWS THEN
   REPEAT ((COND_CASES_TAC ORELSE TOP_CASE_TAC) THEN
           CASE_REWRITE_TAC DSEMAUX_DO_APP_RWS) THEN
   REWRITE_TAC[map_result_def; map_error_result_I; I_THM] THEN
   CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
   ASM_REWRITE_TAC (lim_safe_def :: DSEMAUX_FINISH_RWS) THEN
   TRY (GVS DSEMAUX_FINISH_RWS2 THEN CASE_REWRITE_TAC [] THEN
        REWRITE_TAC[injectivity "result"; PAIR_EQ; data_state_component_equality] THEN
        ASM_REWRITE_TAC DSEMAUX_FINISH_RWS2 THEN NO_TAC);;

let DSEMAUX_DO_APP_TAC (defs:thm list) : tactic =
  X_GEN_TAC `op:clos_op` THEN DSEMAUX_OP_CASES_TAC `op:clos_op` THEN
  DSEMAUX_DO_APP_BRUTE_TAC defs;;

(*fs[] is slower than full_simp_tac(srw_ss())[]*)
(* HOL4 [local] *)
let do_app_with_stack = prove
 (DSEMAUX_expand
  `!op vs (s:(C,FFI)data_state) z.
     data_do_app op vs (data_state_stack_fupd (K z) s) =
     map_result
       (\(x,y). (x,data_state_stack_fupd (K z)
                     (data_state_safe_for_space_fupd
                        (K (do_app_safe op vs (data_state_stack_fupd (K z) s)))
                        (data_state_stack_max_fupd
                           (K (data_state_stack_max
                                 (do_stack op vs (data_state_stack_fupd (K z) s))))
                           (data_state_peak_heap_length_fupd
                              (K (do_app_peak op vs (data_state_stack_fupd (K z) s)))
                              y)))))
       I (data_do_app op vs s)`,
  DSEMAUX_DO_APP_TAC DSEMAUX_DO_APP_DEFS);;

(*fs[] is slower than full_simp_tac(srw_ss())[]*)
(* HOL4 [local] *)
let do_app_with_stack_and_locals = prove
 (DSEMAUX_expand
  `!op vs (s:(C,FFI)data_state) z lsz.
     data_do_app op vs
       (data_state_locals_size_fupd (K lsz) (data_state_stack_fupd (K z) s)) =
     map_result
       (\(x,y). (x,data_state_stack_fupd (K z)
                     (data_state_locals_size_fupd (K lsz)
                     (data_state_safe_for_space_fupd
                        (K (do_app_safe op vs (data_state_locals_size_fupd (K lsz)
                                                 (data_state_stack_fupd (K z) s))))
                        (data_state_stack_max_fupd
                           (K (data_state_stack_max
                                 (do_stack op vs (data_state_locals_size_fupd (K lsz)
                                                    (data_state_stack_fupd (K z) s)))))
                           (data_state_peak_heap_length_fupd
                              (K (do_app_peak op vs (data_state_locals_size_fupd (K lsz)
                                                       (data_state_stack_fupd (K z) s))))
                              y))))))
       I (data_do_app op vs s)`,
  DSEMAUX_DO_APP_TAC DSEMAUX_DO_APP_DEFS);;

(*fs[] is slower than full_simp_tac(srw_ss())[]*)
let do_app_aux_with_space = prove
 (`!op vs (s:(C,FFI)data_state) z.
     data_do_app_aux op vs (data_state_space_fupd (K z) s) =
     map_result (\(x,y). (x,data_state_space_fupd (K z) y)) I (data_do_app_aux op vs s)`,
  DSEMAUX_DO_APP_TAC [data_do_app_aux_def; with_fresh_ts_def; check_lim_def;
                      LET_DEF; LET_END_DEF]);;

(*fs[] is slower than full_simp_tac(srw_ss())[]*)
let do_app_aux_with_locals = prove
 (`!op vs (s:(C,FFI)data_state) z.
     data_do_app_aux op vs (data_state_locals_fupd (K z) s) =
     map_result (\(x,y). (x,data_state_locals_fupd (K z) y)) I (data_do_app_aux op vs s)`,
  DSEMAUX_DO_APP_TAC [data_do_app_aux_def; with_fresh_ts_def; check_lim_def;
                      LET_DEF; LET_END_DEF]);;

(*fs[] is slower than full_simp_tac(srw_ss())[]*)
let do_app_with_locals = prove
 (DSEMAUX_expand
  `!op vs (s:(C,FFI)data_state) z.
     data_do_app op vs (data_state_locals_fupd (K z) s) =
     map_result
       (\(x,y). (x,data_state_locals_fupd (K z)
                     (data_state_safe_for_space_fupd
                        (K (do_app_safe op vs (data_state_locals_fupd (K z) s)))
                        (data_state_stack_max_fupd
                           (K (data_state_stack_max
                                 (do_stack op vs (data_state_locals_fupd (K z) s))))
                           (data_state_peak_heap_length_fupd
                              (K (do_app_peak op vs (data_state_locals_fupd (K z) s)))
                              y)))))
       I (data_do_app op vs s)`,
  DSEMAUX_DO_APP_TAC DSEMAUX_DO_APP_DEFS);;

(* the brute force for implications from a do_app result: split, then     *)
(* strip the result equation and finish with the assumptions              *)

let DSEMAUX_DO_APP_IMP_TAC (defs:thm list) : tactic =
  X_GEN_TAC `op:clos_op` THEN DSEMAUX_OP_CASES_TAC `op:clos_op` THEN
  REPEAT GEN_TAC THEN CASE_REWRITE_TAC defs THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  CASE_REWRITE_TAC DSEMAUX_DO_APP_RWS THEN
  REPEAT ((COND_CASES_TAC ORELSE TOP_CASE_TAC) THEN
          CASE_REWRITE_TAC DSEMAUX_DO_APP_RWS) THEN
  REWRITE_TAC[injectivity "result"; distinctness "result"; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  ASM_REWRITE_TAC(injectivity "error_result" :: injectivity "abort" ::
                  DSEMAUX_FINISH_RWS) THEN
  TRY (DISJ2_TAC THEN MESON_TAC[]);;

let do_app_aux_err = prove
 (`!op vs (s:(C,FFI)data_state) e.
     data_do_app_aux op vs s = Rerr e ==>
     e = Rabort Rtype_error \/ (?i x. op = clos_FFI i /\ e = Rabort (Rffi_error x))`,
  DSEMAUX_DO_APP_IMP_TAC [data_do_app_aux_def; with_fresh_ts_def; check_lim_def;
                          LET_DEF; LET_END_DEF]);;

let data_do_app_aux_const = prove
 (`!op vs (x:(C,FFI)data_state) y z.
     data_do_app_aux op vs x = Rval (y,z) ==>
     data_state_stack z = data_state_stack x /\
     data_state_handler z = data_state_handler x /\
     data_state_locals z = data_state_locals x /\
     data_state_clock z = data_state_clock x /\
     data_state_compile z = data_state_compile x`,
  DSEMAUX_DO_APP_IMP_TAC [data_do_app_aux_def; with_fresh_ts_def; check_lim_def;
                          LET_DEF; LET_END_DEF]);;

let data_do_app_err = prove
 (`!op vs (s:(C,FFI)data_state) e.
     data_do_app op vs s = Rerr e ==>
     e = Rabort Rtype_error \/ (?i x. op = clos_FFI i /\ e = Rabort (Rffi_error x))`,
  DSEMAUX_DO_APP_IMP_TAC DSEMAUX_DO_APP_DEFS);;

let data_do_app_const = prove
 (`!op vs (x:(C,FFI)data_state) y z.
     data_do_app op vs x = Rval (y,z) ==>
     data_state_stack z = data_state_stack x /\
     data_state_handler z = data_state_handler x /\
     data_state_locals z = data_state_locals x /\
     data_state_clock z = data_state_clock x /\
     data_state_compile z = data_state_compile x`,
  DSEMAUX_DO_APP_IMP_TAC DSEMAUX_DO_APP_DEFS);;

let do_app_locals = prove
 (DSEMAUX_expand
  `!op x (s:(C,FFI)data_state) q r extra.
     data_do_app op x s = Rval (q,r) ==>
     data_do_app op x (data_state_locals_fupd (K extra) s) =
     Rval (q,data_state_locals_fupd (K extra)
               (data_state_safe_for_space_fupd
                  (K (do_app_safe op x (data_state_locals_fupd (K extra) s)))
                  (data_state_stack_max_fupd
                     (K (data_state_stack_max
                           (do_stack op x (data_state_locals_fupd (K extra) s))))
                     (data_state_peak_heap_length_fupd
                        (K (do_app_peak op x (data_state_locals_fupd (K extra) s)))
                        r))))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[do_app_with_locals; map_result_def] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[]);;

let do_space_alt = prove
 (DSEMAUX_expand
  `!op vs (s:(C,FFI)data_state).
     do_space op vs s =
     if op_space_reset op
     then SOME (data_state_space_fupd (K 0)
                  (data_state_safe_for_space_fupd (K (do_space_safe op vs s))
                     (data_state_peak_heap_length_fupd (K (do_space_peak op vs s)) s)))
     else consume_space (op_space_req op (LENGTH vs)) s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[do_space_def] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[consume_space_def; LT; SUB_0] THEN
  REWRITE_TAC[DSEMAUX_fupd_id]);;

let Seq_Skip = prove
 (`!c (s:(C,FFI)data_state).
     data_evaluate (data_Seq c data_Skip,s) = data_evaluate (c,s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_evaluate_def] THEN
  MP_TAC(ISPEC `data_evaluate (c,s:(C,FFI)data_state)` PAIR_SURJECTIVE) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[pair_CASE_def] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[data_evaluate_def]);;

let evaluate_safe_alt = prove
 (`!c (s:(C,FFI)data_state).
     evaluate_safe c s = data_state_safe_for_space (SND (data_evaluate (c,s)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[evaluate_safe_def] THEN
  MP_TAC(ISPEC `data_evaluate (c,s:(C,FFI)data_state)` PAIR_SURJECTIVE) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[pair_CASE_def; SND]);;

let evaluate_peak_alt = prove
 (`!c (s:(C,FFI)data_state).
     evaluate_peak c s = data_state_peak_heap_length (SND (data_evaluate (c,s)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[evaluate_peak_def] THEN
  MP_TAC(ISPEC `data_evaluate (c,s:(C,FFI)data_state)` PAIR_SURJECTIVE) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[pair_CASE_def; SND]);;

let size_of_heap_with_safe = prove
 (`!(s:(C,FFI)data_state) safe.
     size_of_heap (data_state_safe_for_space_fupd (K safe) s) = size_of_heap s`,
  REWRITE_TAC[size_of_heap_def; stack_to_vs_def; data_state_INFO.ri_accfupds]);;

(* for a goal ?v1 .. vn. Rval (q,L) = Rval (q,R) (or L = R) where R updates  *)
(* field Fi with K vi: take vi := data_state_Fi L (the field of the left   *)
(* state) and finish by component equality                                *)

let DSEMAUX_EXISTS_FIELDS_TAC : tactic = fun (asl,w as g) ->
  let vs,body = strip_exists w in
  let l,r = dest_eq body in
  let state_of t =
    if is_comb t && is_const (rator t) && fst(dest_const(rator t)) = "Rval"
    then snd(dest_pair(rand t)) else t in
  let ls = state_of l and rs = state_of r in
  let field_of v =
    let t = find_term (fun t ->
              is_comb t && is_comb (rator t) &&
              (let k = rand (rator t) in
               is_comb k && is_const (rator k) && fst(dest_const(rator k)) = "K" &&
               rand k = v)) rs in
    let upd = fst(dest_const(rator(rator t))) in
    let fname = String.sub upd 0 (String.length upd - 5) in
    let acc = mk_const(fname,[]) in
    let acc = inst (type_match (fst(dest_fun_ty(type_of acc))) (type_of ls) []) acc in
    mk_comb(acc,ls) in
  (MAP_EVERY (fun v -> EXISTS_TAC (field_of v)) vs THEN
   REWRITE_TAC[injectivity "result"; PAIR_EQ; data_state_component_equality] THEN
   ASM_REWRITE_TAC DSEMAUX_FINISH_RWS2) g;;

(* the brute force for do_app lemmas of the form                          *)
(*   do_app op vs s = Rval (q,s') ==> ?v1 .. vn. do_app op vs (f s) = ..   *)
(*   do_app op vs s = Rerr e ==> do_app op vs (f s) = Rerr e              *)

let DSEMAUX_DO_APP_SWAP_TAC (defs:thm list) : tactic =
  X_GEN_TAC `op:clos_op` THEN DSEMAUX_OP_CASES_TAC `op:clos_op` THEN
  REPEAT GEN_TAC THEN CASE_REWRITE_TAC defs THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  CASE_REWRITE_TAC DSEMAUX_DO_APP_RWS THEN
  REPEAT ((COND_CASES_TAC ORELSE TOP_CASE_TAC) THEN
          CASE_REWRITE_TAC DSEMAUX_DO_APP_RWS) THEN
  REWRITE_TAC[injectivity "result"; distinctness "result"; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  ASM_REWRITE_TAC(injectivity "error_result" :: injectivity "abort" ::
                  DSEMAUX_FINISH_RWS) THEN
  TRY DSEMAUX_EXISTS_FIELDS_TAC THEN
  TRY (GVS DSEMAUX_FINISH_RWS2 THEN CASE_REWRITE_TAC [] THEN
       TRY DSEMAUX_EXISTS_FIELDS_TAC THEN
       REWRITE_TAC[injectivity "result"; PAIR_EQ; data_state_component_equality] THEN
       ASM_REWRITE_TAC DSEMAUX_FINISH_RWS2 THEN NO_TAC);;

let do_app_aux_safe_peak_swap = prove
 (`!op vs (s:(C,FFI)data_state) q s' safe peak.
     data_do_app_aux op vs s = Rval (q,s') ==>
     ?safe' peak'.
       data_do_app_aux op vs
         (data_state_safe_for_space_fupd (K safe)
            (data_state_peak_heap_length_fupd (K peak) s)) =
       Rval (q,data_state_safe_for_space_fupd (K safe')
                 (data_state_peak_heap_length_fupd (K peak') s'))`,
  DSEMAUX_DO_APP_SWAP_TAC [data_do_app_aux_def; with_fresh_ts_def; check_lim_def;
                           LET_DEF; LET_END_DEF]);;

let do_app_safe_peak_swap = prove
 (`!op vs (s:(C,FFI)data_state) q s' safe peak.
     data_do_app op vs s = Rval (q,s') ==>
     ?new_safe new_peak.
       data_do_app op vs
         (data_state_safe_for_space_fupd (K safe)
            (data_state_peak_heap_length_fupd (K peak) s)) =
       Rval (q,data_state_safe_for_space_fupd (K new_safe)
                 (data_state_peak_heap_length_fupd (K new_peak) s'))`,
  DSEMAUX_DO_APP_SWAP_TAC DSEMAUX_DO_APP_DEFS);;

let do_app_err_safe_peak_swap = prove
 (`!op vs (s:(C,FFI)data_state) e safe peak.
     data_do_app op vs s = Rerr e ==>
     data_do_app op vs
       (data_state_safe_for_space_fupd (K safe)
          (data_state_peak_heap_length_fupd (K peak) s)) = Rerr e`,
  DSEMAUX_DO_APP_SWAP_TAC DSEMAUX_DO_APP_DEFS);;

(* HOL4 [local] *)
let do_app_lss_sm_safe_peak_swap_aux = prove
 (`!op vs (s:(C,FFI)data_state) q s' lss smx safe peak.
     data_do_app op vs s = Rval (q,s') ==>
     ?safe' peak' lss' smx'.
       data_do_app op vs
         (data_state_locals_size_fupd (K lss)
            (data_state_stack_max_fupd (K smx)
               (data_state_safe_for_space_fupd (K safe)
                  (data_state_peak_heap_length_fupd (K peak) s)))) =
       Rval (q,data_state_locals_size_fupd (K lss')
                 (data_state_stack_max_fupd (K smx')
                    (data_state_safe_for_space_fupd (K safe')
                       (data_state_peak_heap_length_fupd (K peak') s'))))`,
  DSEMAUX_DO_APP_SWAP_TAC DSEMAUX_DO_APP_DEFS);;

(* HOL4: do_app_lss_sm_safe_peak_swap_aux |> SIMP_RULE std_ss [LET_DEF] *)
let do_app_lss_sm_safe_peak_swap = do_app_lss_sm_safe_peak_swap_aux;;

(* HOL4 [local] *)
let do_app_sm_safe_peak_swap_aux = prove
 (`!op vs (s:(C,FFI)data_state) q s' smx safe peak.
     data_do_app op vs s = Rval (q,s') ==>
     ?safe' peak' smx'.
       data_do_app op vs
         (data_state_stack_max_fupd (K smx)
            (data_state_safe_for_space_fupd (K safe)
               (data_state_peak_heap_length_fupd (K peak) s))) =
       Rval (q,data_state_stack_max_fupd (K smx')
                 (data_state_safe_for_space_fupd (K safe')
                    (data_state_peak_heap_length_fupd (K peak') s')))`,
  DSEMAUX_DO_APP_SWAP_TAC DSEMAUX_DO_APP_DEFS);;

(* HOL4: do_app_sm_safe_peak_swap_aux |> SIMP_RULE std_ss [LET_DEF] *)
let do_app_sm_safe_peak_swap = do_app_sm_safe_peak_swap_aux;;

let do_app_aux_sm_safe_peak_swap = prove
 (`!op vs (s:(C,FFI)data_state) q s' smx safe peak.
     data_do_app_aux op vs s = Rval (q,s') ==>
     ?safe' peak' smx'.
       data_do_app_aux op vs
         (data_state_stack_max_fupd (K smx)
            (data_state_safe_for_space_fupd (K safe)
               (data_state_peak_heap_length_fupd (K peak) s))) =
       Rval (q,data_state_stack_max_fupd (K smx')
                 (data_state_safe_for_space_fupd (K safe')
                    (data_state_peak_heap_length_fupd (K peak') s')))`,
  DSEMAUX_DO_APP_SWAP_TAC [data_do_app_aux_def; with_fresh_ts_def; check_lim_def;
                           LET_DEF; LET_END_DEF]);;

let do_app_aux_lss_sm_safe_peak_swap = prove
 (`!op vs (s:(C,FFI)data_state) q s' lss smx safe peak.
     data_do_app_aux op vs s = Rval (q,s') ==>
     ?safe' peak' lss' smx'.
       data_do_app_aux op vs
         (data_state_locals_size_fupd (K lss)
            (data_state_stack_max_fupd (K smx)
               (data_state_safe_for_space_fupd (K safe)
                  (data_state_peak_heap_length_fupd (K peak) s)))) =
       Rval (q,data_state_locals_size_fupd (K lss')
                 (data_state_stack_max_fupd (K smx')
                    (data_state_safe_for_space_fupd (K safe')
                       (data_state_peak_heap_length_fupd (K peak') s'))))`,
  DSEMAUX_DO_APP_SWAP_TAC [data_do_app_aux_def; with_fresh_ts_def; check_lim_def;
                           LET_DEF; LET_END_DEF]);;

let do_app_err_lss_sm_safe_peak_swap = prove
 (`!op vs (s:(C,FFI)data_state) e lss smx safe peak.
     data_do_app op vs s = Rerr e ==>
     data_do_app op vs
       (data_state_locals_size_fupd (K lss)
          (data_state_stack_max_fupd (K smx)
             (data_state_safe_for_space_fupd (K safe)
                (data_state_peak_heap_length_fupd (K peak) s)))) = Rerr e`,
  DSEMAUX_DO_APP_SWAP_TAC DSEMAUX_DO_APP_DEFS);;

let do_app_err_sm_safe_peak_swap = prove
 (`!op vs (s:(C,FFI)data_state) e smx safe peak.
     data_do_app op vs s = Rerr e ==>
     data_do_app op vs
       (data_state_stack_max_fupd (K smx)
          (data_state_safe_for_space_fupd (K safe)
             (data_state_peak_heap_length_fupd (K peak) s))) = Rerr e`,
  DSEMAUX_DO_APP_SWAP_TAC DSEMAUX_DO_APP_DEFS);;

(* HOL4 [local] *)
let do_app_lss_stk_stfrm_swap_aux = prove
 (`!op vs (s:(C,FFI)data_state) q s' lss stk stfrm.
     data_do_app op vs s = Rval (q,s') ==>
     ?ss pk smx.
       data_do_app op vs
         (data_state_locals_size_fupd (K lss)
            (data_state_stack_fupd (K stk)
               (data_state_stack_frame_sizes_fupd (K stfrm) s))) =
       Rval (q,data_state_locals_size_fupd (K lss)
                 (data_state_stack_fupd (K stk)
                    (data_state_stack_frame_sizes_fupd
                       (K (if op = clos_Install then LN else stfrm))
                       (data_state_stack_max_fupd (K smx)
                          (data_state_safe_for_space_fupd (K ss)
                             (data_state_peak_heap_length_fupd (K pk) s'))))))`,
  DSEMAUX_DO_APP_SWAP_TAC DSEMAUX_DO_APP_DEFS);;

(* HOL4: do_app_lss_stk_stfrm_swap_aux |> SIMP_RULE std_ss [LET_DEF] *)
let do_app_lss_stk_stfrm_swap = do_app_lss_stk_stfrm_swap_aux;;

let do_app_err_lss_stk_stfrm_swap = prove
 (`!op vs (s:(C,FFI)data_state) e lss stk stfrm.
     data_do_app op vs s = Rerr e ==>
     data_do_app op vs
       (data_state_locals_size_fupd (K lss)
          (data_state_stack_fupd (K stk)
             (data_state_stack_frame_sizes_fupd (K stfrm) s))) = Rerr e`,
  DSEMAUX_DO_APP_SWAP_TAC DSEMAUX_DO_APP_DEFS);;

(* HOL4 [local] *)
let do_app_lim_swap_aux = prove
 (`!op vs (s:(C,FFI)data_state) q s' lim.
     data_do_app op vs s = Rval (q,s') ==>
     ?safe peak smx.
       data_do_app op vs (data_state_limits_fupd (K lim) s) =
       Rval (q,data_state_limits_fupd (K lim)
                 (data_state_stack_max_fupd (K smx)
                    (data_state_safe_for_space_fupd (K safe)
                       (data_state_peak_heap_length_fupd (K peak) s'))))`,
  DSEMAUX_DO_APP_SWAP_TAC DSEMAUX_DO_APP_DEFS);;

(* HOL4: do_app_lim_swap_aux |> SIMP_RULE std_ss [LET_DEF] *)
let do_app_lim_swap = do_app_lim_swap_aux;;

let do_app_err_lim_swap = prove
 (`!op vs (s:(C,FFI)data_state) e lim.
     data_do_app op vs s = Rerr e ==>
     data_do_app op vs (data_state_limits_fupd (K lim) s) = Rerr e`,
  DSEMAUX_DO_APP_SWAP_TAC DSEMAUX_DO_APP_DEFS);;

let size_of_stack_eq = prove
 (`(!n l stack. size_of_stack (CONS (data_Env n l) stack) =
                OPTION_MAP2 (+) n (size_of_stack stack)) /\
   (!n v1 v2 stack. size_of_stack (CONS (Exc n v1 v2) stack) =
                    OPTION_MAP2 (+) (OPTION_MAP ((+) 3) n) (size_of_stack stack)) /\
   size_of_stack [] = SOME 1`,
  REWRITE_TAC[size_of_stack_def; ITLIST; o_THM; size_of_stack_frame_def]);;

(* The field-swap (stack_max/safe_for_space/peak_heap_length) commutes      *)
(* through the narrow cut in evaluate(Assign), since cut_state_opt only     *)
(* touches locals.                                                          *)

(* HOL4 [local] *)
let cut_state_opt_with_swap = prove
 (`!names_opt (s:(C,FFI)data_state) smx safe peak.
     data_cut_state_opt names_opt
       (data_state_stack_max_fupd (K smx)
          (data_state_safe_for_space_fupd (K safe)
             (data_state_peak_heap_length_fupd (K peak) s))) =
     OPTION_MAP (\t. data_state_stack_max_fupd (K smx)
                       (data_state_safe_for_space_fupd (K safe)
                          (data_state_peak_heap_length_fupd (K peak) t)))
                (data_cut_state_opt names_opt s)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[data_cut_state_opt_def; data_cut_state_def;
              data_state_INFO.ri_accfupds] THEN
  REPEAT TOP_CASE_TAC THEN
  REWRITE_TAC[OPTION_MAP_DEF; option_INJ; data_state_INFO.ri_fupdcanon]);;

(* HOL4 [local] *)
let cut_state_opt_stack_max = prove
 (`!names_opt (s:(C,FFI)data_state) s2.
     data_cut_state_opt names_opt s = SOME s2 ==>
     data_state_stack_max s2 = data_state_stack_max s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_cut_state_opt_def; data_cut_state_def] THEN
  REPEAT TOP_CASE_TAC THEN REWRITE_TAC[option_INJ; option_DISTINCT] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[data_state_INFO.ri_accfupds]);;

(* When the swap leaves stack_max at its original value (the fl=F case),   *)
(* the merged input update collapses to just safe_for_space/                *)
(* peak_heap_length.                                                        *)

(* HOL4 [local] *)
let cut_state_opt_swap_input = prove
 (`!names_opt (s:(C,FFI)data_state) s2 safe peak.
     data_cut_state_opt names_opt s = SOME s2 ==>
     data_state_stack_max_fupd (K (data_state_stack_max s))
       (data_state_safe_for_space_fupd (K safe)
          (data_state_peak_heap_length_fupd (K peak) s2)) =
     data_state_safe_for_space_fupd (K safe)
       (data_state_peak_heap_length_fupd (K peak) s2)`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP cut_state_opt_stack_max) THEN
  REWRITE_TAC[data_state_component_equality; data_state_INFO.ri_accfupds; K_THM]);;

(* ------------------------------------------------------------------------- *)
(* The swap of stack_max, safe_for_space and peak_heap_length (the fields   *)
(* that never influence the result of evaluate): DSEMAUX_ssp smx sf pk s is *)
(* s with <| stack_max := smx; safe_for_space := sf;                       *)
(* peak_heap_length := pk |>, and the primitives of evaluate commute with  *)
(* it (a local helper for evaluate_fl_smx_safe_peak_swap_aux).              *)
(* ------------------------------------------------------------------------- *)

let DSEMAUX_ssp_def = new_definition
  `DSEMAUX_ssp smx sf pk (s:(C,FFI)data_state) =
     data_state_stack_max_fupd (K smx)
       (data_state_safe_for_space_fupd (K sf)
          (data_state_peak_heap_length_fupd (K pk) s))`;;

let DSEMAUX_ssp_acc =
  let names = map (fun (f,_,_) -> f) data_state_INFO.ri_fields in
  let names = filter (fun f -> not (mem f ["stack_max";"safe_for_space";
                                           "peak_heap_length"])) names in
  let cl f = "data_state_" ^ f ^ " (DSEMAUX_ssp smx sf pk s) = data_state_" ^ f ^ " s" in
  let tm = parse_term ("!smx sf pk (s:(C,FFI)data_state). " ^
             String.concat " /\\ " (map cl names) ^
             " /\\ data_state_stack_max (DSEMAUX_ssp smx sf pk s) = smx" ^
             " /\\ data_state_safe_for_space (DSEMAUX_ssp smx sf pk s) = sf" ^
             " /\\ data_state_peak_heap_length (DSEMAUX_ssp smx sf pk s) = pk") in
  prove(tm, REWRITE_TAC[DSEMAUX_ssp_def; data_state_INFO.ri_accfupds; K_THM]);;

let DSEMAUX_ssp_tac : tactic =
  REWRITE_TAC[DSEMAUX_ssp_def; data_state_component_equality;
              data_state_INFO.ri_accfupds; K_THM];;

let DSEMAUX_ssp_ssp = prove
 (`!smx sf pk smx' sf' pk' (s:(C,FFI)data_state).
     DSEMAUX_ssp smx sf pk (DSEMAUX_ssp smx' sf' pk' s) = DSEMAUX_ssp smx sf pk s`,
  DSEMAUX_ssp_tac);;

let DSEMAUX_ssp_id = prove
 (`!s:(C,FFI)data_state.
     DSEMAUX_ssp (data_state_stack_max s) (data_state_safe_for_space s)
                 (data_state_peak_heap_length s) s = s`,
  DSEMAUX_ssp_tac);;

let DSEMAUX_ssp_set_var = prove
 (`!v x smx sf pk (s:(C,FFI)data_state).
     data_set_var v x (DSEMAUX_ssp smx sf pk s) = DSEMAUX_ssp smx sf pk (data_set_var v x s)`,
  REWRITE_TAC[data_set_var_def] THEN DSEMAUX_ssp_tac);;

let DSEMAUX_ssp_set_vars = prove
 (`!ns vs smx sf pk (s:(C,FFI)data_state).
     data_set_vars ns vs (DSEMAUX_ssp smx sf pk s) =
     DSEMAUX_ssp smx sf pk (data_set_vars ns vs s)`,
  REWRITE_TAC[data_set_vars_def] THEN DSEMAUX_ssp_tac);;

let DSEMAUX_ssp_flush_state = prove
 (`!b smx sf pk (s:(C,FFI)data_state).
     data_flush_state b (DSEMAUX_ssp smx sf pk s) =
     DSEMAUX_ssp smx sf pk (data_flush_state b s)`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN
  REWRITE_TAC[data_flush_state_def] THEN DSEMAUX_ssp_tac);;

let DSEMAUX_ssp_install_sfs = prove
 (`!op smx sf pk (s:(C,FFI)data_state).
     install_sfs op (DSEMAUX_ssp smx sf pk s) =
     DSEMAUX_ssp smx (~(op = clos_Install) /\ sf) pk (install_sfs op s)`,
  REWRITE_TAC[install_sfs_def] THEN DSEMAUX_ssp_tac);;

let DSEMAUX_ssp_dec_clock = prove
 (`!smx sf pk (s:(C,FFI)data_state).
     data_dec_clock (DSEMAUX_ssp smx sf pk s) = DSEMAUX_ssp smx sf pk (data_dec_clock s)`,
  REWRITE_TAC[data_dec_clock_def] THEN DSEMAUX_ssp_tac);;

let DSEMAUX_ssp_fupds = prove
 (`!smx sf pk (s:(C,FFI)data_state) e x l.
     data_state_locals_fupd (K e) (DSEMAUX_ssp smx sf pk s) =
     DSEMAUX_ssp smx sf pk (data_state_locals_fupd (K e) s) /\
     data_state_stack_fupd (K x) (DSEMAUX_ssp smx sf pk s) =
     DSEMAUX_ssp smx sf pk (data_state_stack_fupd (K x) s) /\
     data_state_locals_size_fupd (K l) (DSEMAUX_ssp smx sf pk s) =
     DSEMAUX_ssp smx sf pk (data_state_locals_size_fupd (K l) s)`,
  DSEMAUX_ssp_tac);;

let DSEMAUX_ssp_size_of_heap = prove
 (`!smx sf pk (s:(C,FFI)data_state).
     size_of_heap (DSEMAUX_ssp smx sf pk s) = size_of_heap s`,
  REWRITE_TAC[size_of_heap_def; stack_to_vs_def; DSEMAUX_ssp_acc]);;

let DSEMAUX_ssp_add_space = prove
 (`!smx sf pk (s:(C,FFI)data_state) k.
     add_space (DSEMAUX_ssp smx sf pk s) k =
     DSEMAUX_ssp smx
       (sf /\ no_thunks_in_refs (data_state_refs s) /\
        size_of_heap s + k <= limits_heap_limit (data_state_limits s))
       (MAX pk (size_of_heap s + k)) (add_space s k)`,
  REWRITE_TAC[add_space_def; DSEMAUX_ssp_size_of_heap; DSEMAUX_ssp_acc] THEN
  DSEMAUX_ssp_tac);;

let DSEMAUX_ssp_jump_exc = prove
 (`!smx sf pk (s:(C,FFI)data_state).
     data_jump_exc (DSEMAUX_ssp smx sf pk s) =
     OPTION_MAP (DSEMAUX_ssp smx sf pk) (data_jump_exc s)`,
  REWRITE_TAC[data_jump_exc_def; DSEMAUX_ssp_acc] THEN REPEAT GEN_TAC THEN
  REPEAT (COND_CASES_TAC ORELSE TOP_CASE_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN TRY(FIRST_ASSUM CONTR_TAC) THEN
  REWRITE_TAC[OPTION_MAP_DEF; option_INJ] THEN DSEMAUX_ssp_tac);;

let DSEMAUX_ssp_pop_env = prove
 (`!smx sf pk (s:(C,FFI)data_state).
     data_pop_env (DSEMAUX_ssp smx sf pk s) =
     OPTION_MAP (DSEMAUX_ssp smx sf pk) (data_pop_env s)`,
  REWRITE_TAC[data_pop_env_def; DSEMAUX_ssp_acc] THEN REPEAT GEN_TAC THEN
  REPEAT TOP_CASE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN TRY(FIRST_ASSUM CONTR_TAC) THEN
  REWRITE_TAC[OPTION_MAP_DEF; option_INJ] THEN DSEMAUX_ssp_tac);;

let DSEMAUX_ssp_call_env = prove
 (`!args sz smx sf pk (s:(C,FFI)data_state).
     data_call_env args sz (DSEMAUX_ssp smx sf pk s) =
     DSEMAUX_ssp
       (OPTION_MAP2 MAX smx (OPTION_MAP2 (+) (size_of_stack (data_state_stack s)) sz))
       (sf /\ misc_the F (OPTION_MAP ((>) (limits_stack_limit (data_state_limits s)))
                       (OPTION_MAP2 MAX smx
                          (OPTION_MAP2 (+) (size_of_stack (data_state_stack s)) sz))))
       pk (data_call_env args sz s)`,
  REWRITE_TAC[data_call_env_def; LET_DEF; LET_END_DEF; DSEMAUX_ssp_acc] THEN
  DSEMAUX_ssp_tac);;

let DSEMAUX_ssp_push_env = prove
 (`!env b smx sf pk (s:(C,FFI)data_state).
     data_push_env env b (DSEMAUX_ssp smx sf pk s) =
     DSEMAUX_ssp
       (OPTION_MAP2 MAX smx (size_of_stack (data_state_stack (data_push_env env b s))))
       (sf /\ misc_the F (OPTION_MAP ((>) (limits_stack_limit (data_state_limits s)))
                       (OPTION_MAP2 MAX smx
                          (size_of_stack (data_state_stack (data_push_env env b s))))))
       pk (data_push_env env b s)`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN
  REWRITE_TAC[data_push_env_def; LET_DEF; LET_END_DEF; DSEMAUX_ssp_acc] THEN
  REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM] THEN DSEMAUX_ssp_tac);;

let DSEMAUX_ssp_cut_state_opt = prove
 (`!names smx sf pk (s:(C,FFI)data_state).
     data_cut_state_opt names (DSEMAUX_ssp smx sf pk s) =
     OPTION_MAP (DSEMAUX_ssp smx sf pk) (data_cut_state_opt names s)`,
  REWRITE_TAC[DSEMAUX_ssp_def; cut_state_opt_with_swap] THEN
  REPEAT GEN_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN REWRITE_TAC[DSEMAUX_ssp_def]);;

let DSEMAUX_ssp_do_app = prove
 (`!op vs (s:(C,FFI)data_state) q s' smx sf pk.
     data_do_app op vs s = Rval (q,s') ==>
     ?smx' sf' pk'. data_do_app op vs (DSEMAUX_ssp smx sf pk s) =
                    Rval (q,DSEMAUX_ssp smx' sf' pk' s')`,
  REWRITE_TAC[DSEMAUX_ssp_def] THEN MESON_TAC[do_app_sm_safe_peak_swap]);;

let DSEMAUX_ssp_do_app_same = prove
 (`!op vs (s:(C,FFI)data_state) q s' sf pk.
     data_do_app op vs s = Rval (q,s') ==>
     ?sf' pk'. data_do_app op vs (DSEMAUX_ssp (data_state_stack_max s) sf pk s) =
               Rval (q,DSEMAUX_ssp (data_state_stack_max s') sf' pk' s')`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o SPECL [`sf:bool`; `pk:num`] o MATCH_MP do_app_safe_peak_swap) THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  MATCH_MP_TAC(MESON[] `(a:(data_v # (C,FFI)data_state,data_v)result) = a' /\ b = b'
                        ==> a = b ==> a' = b'`) THEN
  REWRITE_TAC[injectivity "result"; PAIR_EQ] THEN CONJ_TAC THEN
  TRY AP_TERM_TAC THEN DSEMAUX_ssp_tac);;

let DSEMAUX_ssp_do_app_err = prove
 (`!op vs (s:(C,FFI)data_state) e smx sf pk.
     data_do_app op vs s = Rerr e ==>
     data_do_app op vs (DSEMAUX_ssp smx sf pk s) = Rerr e`,
  REWRITE_TAC[DSEMAUX_ssp_def] THEN MESON_TAC[do_app_err_sm_safe_peak_swap]);;

(* ------------------------------------------------------------------------- *)
(* Machinery for the proofs by induction on evaluate in which the state is  *)
(* changed in fields that commute with the primitives (DSEMAUX_ssp first):  *)
(* the main hypothesis evaluate (c,s) = (r,s') is unfolded once and split   *)
(* with the case_eq theorems; the goal (evaluate (c,s0) with the changed    *)
(* state s0) is unfolded once, the changed state is pushed through the     *)
(* primitives, the induction hypotheses are resolved with the facts of the  *)
(* branch and used to rewrite the recursive calls.                          *)
(* ------------------------------------------------------------------------- *)

let DSEMAUX_SSP_RWS =
  [DSEMAUX_ssp_acc; DSEMAUX_ssp_set_var; DSEMAUX_ssp_set_vars; DSEMAUX_ssp_flush_state;
   DSEMAUX_ssp_install_sfs; DSEMAUX_ssp_dec_clock; DSEMAUX_ssp_fupds;
   DSEMAUX_ssp_add_space; DSEMAUX_ssp_jump_exc; DSEMAUX_ssp_pop_env;
   DSEMAUX_ssp_call_env; DSEMAUX_ssp_push_env; DSEMAUX_ssp_cut_state_opt;
   data_OPTION_CASE_OPTION_MAP; OPTION_MAP_DEF; o_THM];;

let DSEMAUX_jump_exc_stack_max = prove
 (`!(s:(C,FFI)data_state) t.
     data_jump_exc s = SOME t ==> data_state_stack_max t = data_state_stack_max s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_jump_exc_def] THEN
  REPEAT (COND_CASES_TAC ORELSE TOP_CASE_TAC) THEN
  REWRITE_TAC[option_INJ; option_DISTINCT] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[data_state_INFO.ri_accfupds]);;

let DSEMAUX_pop_env_stack_max = prove
 (`!(s:(C,FFI)data_state) t.
     data_pop_env s = SOME t ==> data_state_stack_max t = data_state_stack_max s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_pop_env_def] THEN
  REPEAT TOP_CASE_TAC THEN
  REWRITE_TAC[option_INJ; option_DISTINCT] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[data_state_INFO.ri_accfupds]);;

let DSEMAUX_push_env_stack_max = prove
 (`!env b (s:(C,FFI)data_state).
     data_state_stack_max (data_push_env env b s) =
     OPTION_MAP2 MAX (data_state_stack_max s)
       (size_of_stack (data_state_stack (data_push_env env b s)))`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN
  REWRITE_TAC[data_push_env_def; LET_DEF; LET_END_DEF; data_state_INFO.ri_accfupds;
              K_THM]);;

let DSEMAUX_push_env_acc = prove
 (`!env b (s:(C,FFI)data_state).
     data_state_limits (data_push_env env b s) = data_state_limits s /\
     data_state_locals_size (data_push_env env b s) = data_state_locals_size s /\
     data_state_clock (data_push_env env b s) = data_state_clock s`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN
  REWRITE_TAC[data_push_env_def; LET_DEF; LET_END_DEF; data_state_INFO.ri_accfupds]);;

let DSEMAUX_stack_max_rws =
  [data_set_var_def; data_set_vars_def; data_flush_state_def; install_sfs_def;
   data_dec_clock_def; add_space_def; data_call_env_def; DSEMAUX_push_env_stack_max;
   DSEMAUX_push_env_acc; LET_DEF; LET_END_DEF; data_state_INFO.ri_accfupds; K_THM];;

(* witnesses for ?a b c. .. DSEMAUX_ssp A B C X = DSEMAUX_ssp a b c Y ..   *)

let DSEMAUX_SSP_EXISTS_TAC : tactic = fun (asl,w as g) ->
  let vs,body = strip_exists w in
  let is_ssp t = try fst(dest_const(fst(strip_comb t))) = "DSEMAUX_ssp" &&
                     length(snd(strip_comb t)) = 4 with Failure _ -> false in
  let eqs = find_terms (fun t -> is_eq t && is_ssp (lhs t) && is_ssp (rhs t) &&
                                 (let _,ra = strip_comb (rhs t) in
                                  subset (fst(chop_list 3 ra)) vs)) body in
  match eqs with
    e::_ -> let _,la = strip_comb (lhs e) and _,ra = strip_comb (rhs e) in
            let wit = map (fun v -> assoc v (zip (fst(chop_list 3 ra)) (fst(chop_list 3 la))))
                          vs in
            MAP_EVERY EXISTS_TAC wit g
  | [] -> failwith "DSEMAUX_SSP_EXISTS_TAC";;

(* the stack_max part: smx = stack_max s ==> smx' = stack_max s' (from the *)
(* implications of the induction hypotheses)                                *)

let DSEMAUX_SMX_MESON_TAC : tactic = fun (asl,w as g) ->
  let ok c = (is_imp c && is_eq (fst(dest_imp c)) && is_eq (snd(dest_imp c))) ||
             (is_eq c &&
              (try fst(dest_const(fst(strip_comb(lhs c)))) = "data_state_stack_max"
               with Failure _ -> false)) ||
             (is_neg c && is_eq (dest_neg c)) in
  let ths = filter (fun th -> ok (concl th)) (map snd asl) in
  MESON_TAC ths g;;

let DSEMAUX_SSP_SMX_TAC : tactic =
  TRY (DISCH_THEN SUBST_ALL_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE DSEMAUX_stack_max_rws) THEN
  ASM_REWRITE_TAC DSEMAUX_stack_max_rws THEN
  TRY (FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC DSEMAUX_stack_max_rws THEN NO_TAC) THEN
  TRY (FIRST_X_ASSUM (fun th -> if is_neg (concl th)
                                then MP_TAC th THEN ASM_REWRITE_TAC[] THEN NO_TAC
                                else NO_TAC)) THEN
  TRY DSEMAUX_SMX_MESON_TAC;;

let DSEMAUX_is_ssp_eval t =
  is_comb t &&
  (try fst(dest_const(rator t)) = "data_evaluate" with Failure _ -> false) &&
  (let p = rand t in is_pair p &&
   (try fst(dest_const(fst(strip_comb(snd(dest_pair p))))) = "DSEMAUX_ssp"
    with Failure _ -> false));;

(* rewrite a recursive call data_evaluate (P,DSEMAUX_ssp A B C X) of the     *)
(* goal with an assumption !smx sf pk. ?smx' sf' pk'. data_evaluate (P,     *)
(* DSEMAUX_ssp smx sf pk X) = .. /\ .. instantiated at A B C               *)

let DSEMAUX_SSP_IH_TAC : tactic = fun (asl,w as g) ->
  let targets = find_terms DSEMAUX_is_ssp_eval w in
  let try_one t =
    tryfind (fun (_,th) ->
      let vs,body = strip_forall (concl th) in
      if length vs <> 3 then failwith "" else
      let _,ex = strip_exists body in
      let eq = fst(dest_conj ex) in
      let (_,tmi,tyi) = term_match [] (lhs eq) t in
      if exists (fun (a,b) -> not (a = b)) tyi ||
         exists (fun (t,v) -> not (mem v vs) && not (t = v)) tmi
      then failwith "" else
      let insts = map (fun v -> try rev_assoc v tmi with Failure _ -> v) vs in
      SPECL insts th) asl in
  let th = tryfind try_one targets in
  let avoid = freesl (w :: map (concl o snd) asl) in
  let evs,_ = strip_exists (concl th) in
  let fresh = rev(itlist (fun v acc -> variant (acc @ avoid) v :: acc) (rev evs) []) in
  (MP_TAC th THEN
   MAP_EVERY (fun v -> DISCH_THEN(X_CHOOSE_THEN v MP_TAC)) fresh THEN
   DISCH_THEN(fun th -> STRIP_ASSUME_TAC th THEN REWRITE_TAC[CONJUNCT1 th])) g;;

(* rewrite data_do_app op xs (DSEMAUX_ssp A B C st) of the goal with the    *)
(* fact data_do_app op xs st = .. of the branch                            *)

let DSEMAUX_SSP_DO_APP_RW_TAC : tactic = fun (asl,w as g) ->
  let is_t t = is_comb t &&
    (try let h,args = strip_comb t in fst(dest_const h) = "data_do_app" &&
         length args = 3 && fst(dest_const(fst(strip_comb(el 2 args)))) = "DSEMAUX_ssp"
     with Failure _ -> false) in
  let t = find_term is_t w in
  let _,args = strip_comb t in
  let op = el 0 args and xs = el 1 args and sst = el 2 args in
  let _,sargs = strip_comb sst in
  let a = el 0 sargs and b = el 1 sargs and c = el 2 sargs and st = el 3 sargs in
  let th = snd(find (fun (_,th) -> is_eq (concl th) &&
                       (try let h,args = strip_comb (lhs(concl th)) in
                            fst(dest_const h) = "data_do_app" && args = [op;xs;st]
                        with Failure _ -> false)) asl) in
  let r = rhs(concl th) in
  let choose_all ex =
    let avoid = freesl (w :: map (concl o snd) asl) in
    let vs,_ = strip_exists (concl ex) in
    let vs' = rev(itlist (fun v acc -> variant (acc @ avoid) v :: acc) (rev vs) []) in
    let rec go vs th = match vs with
        [] -> ASSUME_TAC th THEN REWRITE_TAC[th]
      | v::rest -> X_CHOOSE_THEN v (go rest) th in
    go vs' ex in
  if fst(dest_const(fst(strip_comb r))) = "Rerr" then
    REWRITE_TAC[MATCH_MP DSEMAUX_ssp_do_app_err th] g
  else
    let smx_st = mk_comb(`data_state_stack_max:(C,FFI)data_state->num option`,st) in
    (ASM_CASES_TAC (mk_eq(a,smx_st)) THENL
      [FIRST_ASSUM(fun eqth -> if concl eqth = mk_eq(a,smx_st)
                               then REWRITE_TAC[eqth] else NO_TAC) THEN
       MP_TAC(SPECL [b;c] (MATCH_MP DSEMAUX_ssp_do_app_same th)) THEN
       DISCH_THEN choose_all;
       MP_TAC(SPECL [a;b;c] (MATCH_MP DSEMAUX_ssp_do_app th)) THEN
       DISCH_THEN choose_all]) g;;

(* resolve the implications among the assumptions (each resolvent is put  *)
(* in unwound form)                                                         *)

let DSEMAUX_RES_TAC : tactic = fun (asl,w) ->
  let ths = map snd asl in
  let imps = filter (fun th -> let _,b = strip_forall (concl th) in is_imp b) ths in
  let simp = REWRITE_RULE[RIGHT_FORALL_IMP_THM; FORALL_UNWIND_THM1; FORALL_UNWIND_THM2;
                          IMP_CONJ] in
  let new_ths = flat (map (fun ith -> mapfilter (fun th -> simp (MATCH_MP ith th)) ths)
                          imps) in
  let new_ths = filter (fun th -> not (exists (fun t -> aconv (concl t) (concl th)) ths) &&
                                  not (concl th = `T`)) new_ths in
  let rec nub l = match l with [] -> [] | h::t ->
    h :: nub (filter (fun x -> not (aconv (concl x) (concl h))) t) in
  let new_ths = nub new_ths in
  if new_ths = [] then failwith "DSEMAUX_RES_TAC" else MAP_EVERY ASSUME_TAC new_ths (asl,w);;

let DSEMAUX_SPLIT_CONJ_ASMS : tactic =
  REPEAT (FIRST_X_ASSUM (fun th -> if is_conj (concl th)
                                   then CONJUNCTS_THEN ASSUME_TAC th else NO_TAC));;

let DSEMAUX_EVAL_CASE_EQS =
  [pair_case_eq; option_case_eq; list_case_eq; COND_CASE_EQ] @
  map case_eq ["result"; "error_result"; "abort"; "data_dest_thunk_ret";
               "thunk_mode"; "data_v"];;

let DSEMAUX_is_main_hyp tm =
  is_eq tm &&
  (try fst(dest_const(fst(strip_comb(lhs tm)))) = "data_evaluate" with Failure _ -> false) &&
  is_pair (rhs tm) && (let r,s = dest_pair (rhs tm) in is_var r && is_var s);;

(* strip a clause of the induction: the IHs and the main hypothesis (split *)
(* into its branches) become assumptions; both evaluates are unfolded once  *)

let DSEMAUX_EVAL_CLAUSE_TAC (rws:thm list) : tactic =
  REPEAT GEN_TAC THEN
  (fun (asl,w as g) ->
     let a,_ = dest_imp w in
     if DSEMAUX_is_main_hyp a then ALL_TAC g
     else (DISCH_THEN STRIP_ASSUME_TAC THEN REPEAT GEN_TAC) g) THEN
  DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE DSEMAUX_EVAL_CASE_EQS o
             ONCE_REWRITE_RULE[data_evaluate_def]) THEN
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[data_evaluate_def] THEN
  REWRITE_TAC rws THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN DSEMAUX_SPLIT_CONJ_ASMS THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[option_INJ; IMP_CONJ; RIGHT_FORALL_IMP_THM;
                              FORALL_UNWIND_THM1; option_DISTINCT; PAIR_EQ]) THEN
  REPEAT DSEMAUX_RES_TAC;;

let DSEMAUX_SSP_LEAF_TAC : tactic =
  REWRITE_TAC DSEMAUX_SSP_RWS THEN
  REPEAT (CHANGED_TAC (CASE_REWRITE_TAC[] THEN
                       ASM_REWRITE_TAC (PAIR_EQ :: o_THM :: DSEMAUX_SSP_RWS)) ORELSE
          DSEMAUX_SSP_IH_TAC ORELSE DSEMAUX_SSP_DO_APP_RW_TAC) THEN
  IMP_RES_TAC DSEMAUX_jump_exc_stack_max THEN IMP_RES_TAC DSEMAUX_pop_env_stack_max THEN
  IMP_RES_TAC cut_state_opt_stack_max THEN
  DSEMAUX_SSP_EXISTS_TAC THEN ASM_REWRITE_TAC DSEMAUX_stack_max_rws THEN
  DSEMAUX_SSP_SMX_TAC;;

let DSEMAUX_evaluate_ssp = prove
 (`!p r (s':(C,FFI)data_state).
     data_evaluate p = (r,s') ==>
     !smx sf pk. ?smx' sf' pk'.
       data_evaluate (FST p,DSEMAUX_ssp smx sf pk (SND p)) =
       (r,DSEMAUX_ssp smx' sf' pk' s') /\
       (smx = data_state_stack_max (SND p) ==> smx' = data_state_stack_max s')`,
  MATCH_MP_TAC data_evaluate_ind THEN REWRITE_TAC[FST; SND] THEN REPEAT CONJ_TAC THEN
  DSEMAUX_EVAL_CLAUSE_TAC DSEMAUX_SSP_RWS THEN DSEMAUX_SSP_LEAF_TAC);;

(* HOL4 [local] *)
let evaluate_fl_smx_safe_peak_swap_aux = prove
 (`!c (s:(C,FFI)data_state) r s' fl smx safe peak.
     data_evaluate (c,s) = (r,s') ==>
     if fl
     then (let s0 = data_state_stack_max_fupd (K smx)
                      (data_state_safe_for_space_fupd (K safe)
                         (data_state_peak_heap_length_fupd (K peak) s)) in
           ?smx safe peak.
             data_evaluate (c,s0) =
             (r,data_state_stack_max_fupd (K smx)
                  (data_state_safe_for_space_fupd (K safe)
                     (data_state_peak_heap_length_fupd (K peak) s'))))
     else (let s0 = data_state_stack_max_fupd (K (data_state_stack_max s))
                      (data_state_safe_for_space_fupd (K safe)
                         (data_state_peak_heap_length_fupd (K peak) s)) in
           ?(smx:num option) safe peak.
             data_evaluate (c,s0) =
             (r,data_state_stack_max_fupd (K (data_state_stack_max s'))
                  (data_state_safe_for_space_fupd (K safe)
                     (data_state_peak_heap_length_fupd (K peak) s'))))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[FST; SND] o MATCH_MP DSEMAUX_evaluate_ssp) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; GSYM DSEMAUX_ssp_def] THEN
  BOOL_CASES_TAC `fl:bool` THEN REWRITE_TAC[] THEN
  FIRST
   [FIRST_ASSUM(MP_TAC o SPECL [`smx:num option`; `safe:bool`; `peak:num`]) THEN
    STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`smx':num option`; `sf':bool`; `pk':num`] THEN
    ASM_REWRITE_TAC[] THEN NO_TAC;
    FIRST_ASSUM(MP_TAC o SPECL [`data_state_stack_max (s:(C,FFI)data_state)`;
                                `safe:bool`; `peak:num`]) THEN
    REWRITE_TAC[] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`sf':bool`; `pk':num`] THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN ASM_REWRITE_TAC[]]);;

let evaluate_smx_safe_peak_swap_aux = prove
 (`!c (s:(C,FFI)data_state) r s' smx safe peak.
     data_evaluate (c,s) = (r,s') ==>
     (let s0 = data_state_stack_max_fupd (K smx)
                 (data_state_safe_for_space_fupd (K safe)
                    (data_state_peak_heap_length_fupd (K peak) s)) in
      ?smx safe peak.
        data_evaluate (c,s0) =
        (r,data_state_stack_max_fupd (K smx)
             (data_state_safe_for_space_fupd (K safe)
                (data_state_peak_heap_length_fupd (K peak) s'))))`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`c:data_prog`; `s:(C,FFI)data_state`; `r:((data_v list,data_v)result)option`;
                `s':(C,FFI)data_state`; `T`; `smx:num option`; `safe:bool`; `peak:num`]
               evaluate_fl_smx_safe_peak_swap_aux) THEN
  REWRITE_TAC[]);;

let evaluate_smx_safe_peak_swap = prove
 (`!c (s:(C,FFI)data_state) r s' smx safe peak.
     data_evaluate (c,s) = (r,s') ==>
     ?smx' safe' peak'.
       data_evaluate (c,data_state_stack_max_fupd (K smx)
                          (data_state_safe_for_space_fupd (K safe)
                             (data_state_peak_heap_length_fupd (K peak) s))) =
       (r,data_state_stack_max_fupd (K smx')
            (data_state_safe_for_space_fupd (K safe')
               (data_state_peak_heap_length_fupd (K peak') s')))`,
  REWRITE_TAC[REWRITE_RULE[LET_DEF; LET_END_DEF] evaluate_smx_safe_peak_swap_aux]);;

let evaluate_safe_peak_swap_aux = prove
 (`!c (s:(C,FFI)data_state) r s' safe peak.
     data_evaluate (c,s) = (r,s') ==>
     (let s0 = data_state_stack_max_fupd (K (data_state_stack_max s))
                 (data_state_safe_for_space_fupd (K safe)
                    (data_state_peak_heap_length_fupd (K peak) s)) in
      ?(smx:num option) safe peak.
        data_evaluate (c,s0) =
        (r,data_state_stack_max_fupd (K (data_state_stack_max s'))
             (data_state_safe_for_space_fupd (K safe)
                (data_state_peak_heap_length_fupd (K peak) s'))))`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`c:data_prog`; `s:(C,FFI)data_state`; `r:((data_v list,data_v)result)option`;
                `s':(C,FFI)data_state`; `F`; `smx:num option`; `safe:bool`; `peak:num`]
               evaluate_fl_smx_safe_peak_swap_aux) THEN
  REWRITE_TAC[]);;

let DSEMAUX_ssp_same_smx = prove
 (`!(t:(C,FFI)data_state) a b.
     DSEMAUX_ssp (data_state_stack_max t) a b t =
     data_state_safe_for_space_fupd (K a) (data_state_peak_heap_length_fupd (K b) t)`,
  DSEMAUX_ssp_tac);;

let evaluate_safe_peak_swap = prove
 (`!safe (s':(C,FFI)data_state) s r peak c.
     data_evaluate (c,s) = (r,s') ==>
     ?safe' peak'.
       data_evaluate (c,data_state_safe_for_space_fupd (K safe)
                          (data_state_peak_heap_length_fupd (K peak) s)) =
       (r,data_state_safe_for_space_fupd (K safe')
            (data_state_peak_heap_length_fupd (K peak') s'))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o SPECL [`data_state_stack_max (s:(C,FFI)data_state)`;
                             `safe:bool`; `peak:num`] o
             REWRITE_RULE[FST; SND] o MATCH_MP DSEMAUX_evaluate_ssp) THEN
  REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`sf':bool`; `pk':num`] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DSEMAUX_ssp_same_smx]) THEN ASM_REWRITE_TAC[]);;

let same_stack_size_def = cake_def
  `same_stack_size x y <=> size_of_stack_frame x = size_of_stack_frame y`;;

let same_stack_size_size_of_stack = prove
 (`!xs ys. ALL2 same_stack_size xs ys ==> size_of_stack xs = size_of_stack ys`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[ALL2; size_of_stack_def; ITLIST; o_THM; same_stack_size_def] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t':stack list`) THEN
  ASM_REWRITE_TAC[size_of_stack_def]);;

let s_peak_heap = prove
 (`!(s:(C,FFI)data_state) smnew clock ssnew plnnew.
     data_state_peak_heap_length_fupd (K (data_state_peak_heap_length s)) s = s /\
     data_state_safe_for_space_fupd (K (data_state_safe_for_space s)) s = s /\
     data_state_stack_max_fupd (K (data_state_stack_max s)) s = s /\
     data_state_locals_size_fupd (K (data_state_locals_size s)) s = s /\
     data_state_stack_fupd (K (data_state_stack s))
       (data_state_stack_max_fupd (K smnew)
          (data_state_clock_fupd (K clock)
             (data_state_safe_for_space_fupd (K ssnew) s))) =
     data_state_stack_max_fupd (K smnew)
       (data_state_clock_fupd (K clock)
          (data_state_safe_for_space_fupd (K ssnew) s)) /\
     data_state_handler_fupd (K (data_state_handler s))
       (data_state_safe_for_space_fupd (K ssnew)
          (data_state_peak_heap_length_fupd (K plnnew) s)) =
     data_state_safe_for_space_fupd (K ssnew)
       (data_state_peak_heap_length_fupd (K plnnew) s)`,
  REWRITE_TAC[data_state_component_equality; data_state_INFO.ri_accfupds; K_THM]);;
let _ = cake_add_simps [s_peak_heap];;
(* ------------------------------------------------------------------------- *)
(* The swap of the stack and locals_size (with the ssp fields) for           *)
(* evaluate_stack_and_locals_swap: DSEMAUX_sl xs lsz s is                    *)
(* s with <| stack := xs; locals_size := lsz |>.                             *)
(* ------------------------------------------------------------------------- *)

let DSEMAUX_sl_def = new_definition
  `DSEMAUX_sl xs lsz (s:(C,FFI)data_state) =
     data_state_stack_fupd (K xs) (data_state_locals_size_fupd (K lsz) s)`;;

let DSEMAUX_sl_tac : tactic =
  REWRITE_TAC[DSEMAUX_sl_def; DSEMAUX_ssp_def; data_state_component_equality;
              data_state_INFO.ri_accfupds; K_THM];;

let DSEMAUX_sl_acc =
  let names = map (fun (f,_,_) -> f) data_state_INFO.ri_fields in
  let names = filter (fun f -> not (mem f ["stack";"locals_size"])) names in
  let cl f = "data_state_" ^ f ^ " (DSEMAUX_sl xs lsz s) = data_state_" ^ f ^ " s" in
  let tm = parse_term ("!xs lsz (s:(C,FFI)data_state). " ^
             String.concat " /\\ " (map cl names) ^
             " /\\ data_state_stack (DSEMAUX_sl xs lsz s) = xs" ^
             " /\\ data_state_locals_size (DSEMAUX_sl xs lsz s) = lsz") in
  prove(tm, REWRITE_TAC[DSEMAUX_sl_def; data_state_INFO.ri_accfupds; K_THM]);;

let DSEMAUX_sl_set_var = prove
 (`!v x xs lsz (s:(C,FFI)data_state).
     data_set_var v x (DSEMAUX_sl xs lsz s) = DSEMAUX_sl xs lsz (data_set_var v x s)`,
  REWRITE_TAC[data_set_var_def] THEN DSEMAUX_sl_tac);;

let DSEMAUX_sl_set_vars = prove
 (`!ns vs xs lsz (s:(C,FFI)data_state).
     data_set_vars ns vs (DSEMAUX_sl xs lsz s) = DSEMAUX_sl xs lsz (data_set_vars ns vs s)`,
  REWRITE_TAC[data_set_vars_def] THEN DSEMAUX_sl_tac);;

let DSEMAUX_sl_flush_state = prove
 (`!xs lsz (s:(C,FFI)data_state).
     data_flush_state T (DSEMAUX_sl xs lsz s) = data_flush_state T s /\
     data_flush_state F (DSEMAUX_sl xs lsz s) =
     DSEMAUX_sl xs (SOME 0) (data_flush_state F s)`,
  REWRITE_TAC[data_flush_state_def] THEN DSEMAUX_sl_tac);;

let DSEMAUX_sl_install_sfs = prove
 (`!op xs lsz (s:(C,FFI)data_state).
     install_sfs op (DSEMAUX_sl xs lsz s) = DSEMAUX_sl xs lsz (install_sfs op s)`,
  REWRITE_TAC[install_sfs_def] THEN DSEMAUX_sl_tac);;

let DSEMAUX_sl_dec_clock = prove
 (`!xs lsz (s:(C,FFI)data_state).
     data_dec_clock (DSEMAUX_sl xs lsz s) = DSEMAUX_sl xs lsz (data_dec_clock s)`,
  REWRITE_TAC[data_dec_clock_def] THEN DSEMAUX_sl_tac);;

let DSEMAUX_sl_locals = prove
 (`!xs lsz (s:(C,FFI)data_state) e.
     data_state_locals_fupd (K e) (DSEMAUX_sl xs lsz s) =
     DSEMAUX_sl xs lsz (data_state_locals_fupd (K e) s)`,
  DSEMAUX_sl_tac);;

let DSEMAUX_sl_ssp = prove
 (`!xs lsz smx sf pk (s:(C,FFI)data_state).
     DSEMAUX_ssp smx sf pk (DSEMAUX_sl xs lsz s) = DSEMAUX_sl xs lsz (DSEMAUX_ssp smx sf pk s)`,
  DSEMAUX_sl_tac);;

let DSEMAUX_sl_sl = prove
 (`!xs lsz xs' lsz' (s:(C,FFI)data_state).
     DSEMAUX_sl xs lsz (DSEMAUX_sl xs' lsz' s) = DSEMAUX_sl xs lsz s`,
  DSEMAUX_sl_tac);;

let DSEMAUX_sl_cut_state_opt = prove
 (`!names xs lsz (s:(C,FFI)data_state).
     data_cut_state_opt names (DSEMAUX_sl xs lsz s) =
     OPTION_MAP (DSEMAUX_sl xs lsz) (data_cut_state_opt names s)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[data_cut_state_opt_def; data_cut_state_def; DSEMAUX_sl_acc] THEN
  REPEAT TOP_CASE_TAC THEN REWRITE_TAC[OPTION_MAP_DEF; option_INJ] THEN
  DSEMAUX_sl_tac);;

let DSEMAUX_sl_add_space = prove
 (`!xs lsz (s:(C,FFI)data_state) k.
     add_space (DSEMAUX_sl xs lsz s) k =
     DSEMAUX_sl xs lsz
       (DSEMAUX_ssp (data_state_stack_max s)
          (data_state_safe_for_space s /\ no_thunks_in_refs (data_state_refs s) /\
           size_of_heap (DSEMAUX_sl xs lsz s) + k <=
           limits_heap_limit (data_state_limits s))
          (MAX (data_state_peak_heap_length s) (size_of_heap (DSEMAUX_sl xs lsz s) + k))
          (add_space s k))`,
  REWRITE_TAC[add_space_def; DSEMAUX_sl_acc] THEN DSEMAUX_sl_tac);;

let DSEMAUX_sl_call_env = prove
 (`!args sz xs lsz (s:(C,FFI)data_state).
     data_call_env args sz (DSEMAUX_sl xs lsz s) =
     DSEMAUX_sl xs sz
       (DSEMAUX_ssp
          (OPTION_MAP2 MAX (data_state_stack_max s)
             (OPTION_MAP2 (+) (size_of_stack xs) sz))
          (data_state_safe_for_space s /\
           misc_the F (OPTION_MAP ((>) (limits_stack_limit (data_state_limits s)))
                    (OPTION_MAP2 MAX (data_state_stack_max s)
                       (OPTION_MAP2 (+) (size_of_stack xs) sz))))
          (data_state_peak_heap_length s)
          (data_call_env args sz s))`,
  REWRITE_TAC[data_call_env_def; LET_DEF; LET_END_DEF; DSEMAUX_sl_acc] THEN
  DSEMAUX_sl_tac);;

let DSEMAUX_sl_push_env = prove
 (`!env b xs lsz (s:(C,FFI)data_state).
     LENGTH xs = LENGTH (data_state_stack s) ==>
     data_push_env env b (DSEMAUX_sl xs lsz s) =
     DSEMAUX_sl (CONS (if b then Exc lsz env (data_state_handler s)
                       else data_Env lsz env) xs)
       lsz
       (DSEMAUX_ssp
          (OPTION_MAP2 MAX (data_state_stack_max s)
             (size_of_stack (CONS (if b then Exc lsz env (data_state_handler s)
                                   else data_Env lsz env) xs)))
          (data_state_safe_for_space s /\
           misc_the F (OPTION_MAP ((>) (limits_stack_limit (data_state_limits s)))
                    (OPTION_MAP2 MAX (data_state_stack_max s)
                       (size_of_stack (CONS (if b then Exc lsz env (data_state_handler s)
                                             else data_Env lsz env) xs)))))
          (data_state_peak_heap_length s)
          (data_push_env env b s))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN BOOL_CASES_TAC `b:bool` THEN
  REWRITE_TAC[data_push_env_def; LET_DEF; LET_END_DEF; DSEMAUX_sl_acc] THEN
  ASM_REWRITE_TAC[DSEMAUX_sl_def; DSEMAUX_ssp_def; data_state_component_equality;
                  data_state_INFO.ri_accfupds; K_THM]);;

let DSEMAUX_ASM_HEAD name th =
  is_eq (concl th) &&
  (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = name with Failure _ -> false);;

let DSEMAUX_jump_exc_shape = prove
 (`!(s:(C,FFI)data_state) t.
     data_jump_exc s = SOME t ==>
     t = data_state_handler_fupd (K (data_state_handler t))
           (data_state_locals_fupd (K (data_state_locals t))
              (data_state_stack_fupd (K (data_state_stack t))
                 (data_state_locals_size_fupd (K (data_state_locals_size t)) s)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_jump_exc_def] THEN
  REPEAT (COND_CASES_TAC ORELSE TOP_CASE_TAC) THEN
  REWRITE_TAC[option_INJ; option_DISTINCT] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[data_state_component_equality; data_state_INFO.ri_accfupds; K_THM]);;
let DSEMAUX_sl_ssp_jump_exc = prove
 (`!xs lsz smx sf pk (s:(C,FFI)data_state).
     data_jump_exc (DSEMAUX_sl xs lsz (DSEMAUX_ssp smx sf pk s)) =
     OPTION_MAP (DSEMAUX_ssp smx sf pk) (data_jump_exc (DSEMAUX_sl xs lsz s))`,
  REWRITE_TAC[GSYM DSEMAUX_sl_ssp; DSEMAUX_ssp_jump_exc]);;

let DSEMAUX_jump_exc_cong = prove
 (`!(s:(C,FFI)data_state) (t:(C,FFI)data_state).
     data_state_stack t = data_state_stack s /\
     data_state_handler t = data_state_handler s ==>
     data_jump_exc t =
     OPTION_MAP (\s'. data_state_handler_fupd (K (data_state_handler s'))
                        (data_state_locals_fupd (K (data_state_locals s'))
                           (data_state_stack_fupd (K (data_state_stack s'))
                              (data_state_locals_size_fupd (K (data_state_locals_size s')) t))))
                (data_jump_exc s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[data_jump_exc_def] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT (COND_CASES_TAC ORELSE TOP_CASE_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN TRY(FIRST_ASSUM CONTR_TAC) THEN
  REWRITE_TAC[OPTION_MAP_DEF; option_INJ] THEN
  REWRITE_TAC[data_state_component_equality; data_state_INFO.ri_accfupds; K_THM]);;

let DSEMAUX_sl_do_app = prove
 (DSEMAUX_expand
  `!op vs xs lsz (s:(C,FFI)data_state).
     data_do_app op vs (DSEMAUX_sl xs lsz s) =
     map_result
       (\(x,y). (x,DSEMAUX_sl xs lsz
                     (DSEMAUX_ssp
                        (data_state_stack_max (do_stack op vs (DSEMAUX_sl xs lsz s)))
                        (do_app_safe op vs (DSEMAUX_sl xs lsz s))
                        (do_app_peak op vs (DSEMAUX_sl xs lsz s)) y)))
       I (data_do_app op vs s)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `DSEMAUX_sl xs lsz (s:(C,FFI)data_state) =
                data_state_locals_size_fupd (K lsz) (data_state_stack_fupd (K xs) s)`
    SUBST1_TAC THENL [DSEMAUX_sl_tac; ALL_TAC] THEN
  REWRITE_TAC[do_app_with_stack_and_locals] THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[PAIR_EQ] THEN
  DSEMAUX_sl_tac);;

let DSEMAUX_cut_state_opt_stack = prove
 (`!names (s:(C,FFI)data_state) t.
     data_cut_state_opt names s = SOME t ==>
     data_state_stack t = data_state_stack s /\ data_state_handler t = data_state_handler s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_cut_state_opt_def; data_cut_state_def] THEN
  REPEAT TOP_CASE_TAC THEN REWRITE_TAC[option_INJ; option_DISTINCT] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[data_state_INFO.ri_accfupds]);;

(* tactics for the clauses of the stack and locals_size swap *)

let DSEMAUX_SL_RWS =
  [DSEMAUX_sl_do_app; map_result_def; map_error_result_I; I_THM;
   DSEMAUX_sl_acc; DSEMAUX_sl_set_var; DSEMAUX_sl_set_vars; DSEMAUX_sl_flush_state;
   DSEMAUX_sl_install_sfs; DSEMAUX_sl_dec_clock; DSEMAUX_sl_locals; DSEMAUX_sl_ssp;
   DSEMAUX_sl_sl; DSEMAUX_sl_cut_state_opt; DSEMAUX_sl_add_space; DSEMAUX_sl_call_env;
   DSEMAUX_ssp_ssp; DSEMAUX_sl_ssp_jump_exc] @ DSEMAUX_SSP_RWS;;

let DSEMAUX_SL_LOOP_TAC : tactic =
  REPEAT (CHANGED_TAC (CASE_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
                       ASM_REWRITE_TAC (PAIR_EQ :: DSEMAUX_SL_RWS)) ORELSE
          DSEMAUX_SSP_DO_APP_RW_TAC);;

(* witnesses for ?lss sfs smx' phl. .. L = DSEMAUX_sl xs lss (DSEMAUX_ssp   *)
(* smx' sfs phl Y) ..  where L is a DSEMAUX_sl or DSEMAUX_ssp term          *)

let DSEMAUX_SL_EXISTS_TAC : tactic = fun (asl,w as g) ->
  let vs,body = strip_exists w in
  let hd_is n t = try fst(dest_const(fst(strip_comb t))) = n with Failure _ -> false in
  let pairs = find_terms (fun t -> is_eq t && hd_is "DSEMAUX_sl" (rhs t) &&
                                   (hd_is "DSEMAUX_sl" (lhs t) || hd_is "DSEMAUX_ssp" (lhs t)))
                         body in
  match pairs with
    e::_ ->
      let l = lhs e and r = rhs e in
      let _,rargs = strip_comb r in
      let b2 = el 1 rargs and x2 = el 2 rargs in
      let b1,x1 = if hd_is "DSEMAUX_sl" l then let _,largs = strip_comb l in el 1 largs,el 2 largs
                  else let _,args = strip_comb l in
                       mk_comb(`data_state_locals_size:(C,FFI)data_state->num option`,
                               el 3 args), l in
      let sub1 = if mem b2 vs then [b2,b1] else [] in
      let sub2 = if hd_is "DSEMAUX_ssp" x1 && hd_is "DSEMAUX_ssp" x2 then
                   let _,la = strip_comb x1 and _,ra = strip_comb x2 in
                   filter (fun (v,_) -> mem v vs) (zip (fst(chop_list 3 ra)) (fst(chop_list 3 la)))
                 else [] in
      let sub = sub1 @ sub2 in
      let wit = map (fun v -> try assoc v sub with Failure _ -> v) vs in
      MAP_EVERY EXISTS_TAC wit g
  | [] -> failwith "DSEMAUX_SL_EXISTS_TAC";;

let DSEMAUX_SL_RECORD_TAC : tactic =
  REWRITE_TAC[DSEMAUX_sl_def; DSEMAUX_ssp_def; data_flush_state_def; install_sfs_def;
              data_set_var_def; data_set_vars_def; data_state_component_equality;
              data_state_INFO.ri_accfupds; K_THM] THEN
  ASM_REWRITE_TAC[];;

let DSEMAUX_SL_FINISH_TAC : tactic =
  DSEMAUX_SL_EXISTS_TAC THEN ASM_REWRITE_TAC DSEMAUX_SL_RWS THEN DSEMAUX_SL_RECORD_TAC;;

let DSEMAUX_SPLIT_DISJ_ASMS : tactic =
  REPEAT (FIRST_X_ASSUM (DISJ_CASES_THEN STRIP_ASSUME_TAC o check (is_disj o concl)));;

let DSEMAUX_SL_SIMPLE_TAC : tactic =
  REPEAT GEN_TAC THEN
  DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE DSEMAUX_EVAL_CASE_EQS o
             ONCE_REWRITE_RULE[data_evaluate_def]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN DSEMAUX_SPLIT_CONJ_ASMS THEN RVEQ_TAC THEN
  IMP_RES_TAC data_do_app_err THEN DSEMAUX_SPLIT_DISJ_ASMS THEN RVEQ_TAC THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN CASE_REWRITE_TAC[] THEN
  IMP_RES_TAC DSEMAUX_cut_state_opt_stack THEN IMP_RES_TAC data_do_app_const THEN
  REPEAT CONJ_TAC THEN
  TRY (ONCE_REWRITE_TAC[data_evaluate_def] THEN REWRITE_TAC DSEMAUX_SL_RWS THEN
       DSEMAUX_SL_LOOP_TAC THEN DSEMAUX_SL_FINISH_TAC THEN NO_TAC) THEN
  ASM_REWRITE_TAC DSEMAUX_stack_max_rws;;

let DSEMAUX_SL_RAISE_TAC : tactic =
  REPEAT GEN_TAC THEN
  DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE DSEMAUX_EVAL_CASE_EQS o
             ONCE_REWRITE_RULE[data_evaluate_def]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN DSEMAUX_SPLIT_CONJ_ASMS THEN RVEQ_TAC THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `s7:(C,FFI)data_state` THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[data_evaluate_def] THEN
  ASM_REWRITE_TAC DSEMAUX_SL_RWS THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC(PAIR_EQ :: DSEMAUX_SL_RWS) THEN
  MAP_EVERY EXISTS_TAC [`data_state_locals_size (s7:(C,FFI)data_state)`;
                        `sf:bool`; `smx:num option`; `pk:num`] THEN
  FIRST_ASSUM(fun th -> if DSEMAUX_ASM_HEAD "data_jump_exc" th &&
                           (try fst(dest_const(fst(strip_comb(rand(lhs(concl th)))))) =
                                "DSEMAUX_sl" with Failure _ -> false)
                        then ONCE_REWRITE_TAC[MATCH_MP DSEMAUX_jump_exc_shape th] else NO_TAC) THEN
  FIRST_ASSUM(fun th -> if DSEMAUX_ASM_HEAD "data_jump_exc" th &&
                           not (try fst(dest_const(fst(strip_comb(rand(lhs(concl th)))))) =
                                    "DSEMAUX_sl" with Failure _ -> false)
                        then ONCE_REWRITE_TAC[MATCH_MP DSEMAUX_jump_exc_shape th] else NO_TAC) THEN
  REWRITE_TAC[DSEMAUX_sl_def; DSEMAUX_ssp_def; data_state_component_equality;
              data_state_INFO.ri_accfupds; K_THM];;

let DSEMAUX_SL_GOAL = CASE_TERM
  `!p (r:((data_v list,data_v)result)option) (s1:(C,FFI)data_state).
     data_evaluate p = (r,s1) ==>
     !xs lsz smx sf pk.
       LENGTH xs = LENGTH (data_state_stack (SND p)) ==>
       (match r with
          SOME (Rerr (Rabort Rtype_error)) -> T
        | SOME (Rerr (Rabort a)) ->
            data_state_stack s1 = [] /\
            (?lss sfs smx' phl.
               data_evaluate (FST p,DSEMAUX_sl xs lsz (DSEMAUX_ssp smx sf pk (SND p))) =
               (r,DSEMAUX_sl [] lss (DSEMAUX_ssp smx' sfs phl s1)))
        | SOME (Rerr (Rraise v)) ->
            (?s2. data_jump_exc (SND p) = SOME s2 /\
                  data_state_locals s2 = data_state_locals s1 /\
                  data_state_stack s2 = data_state_stack s1 /\
                  data_state_handler s2 = data_state_handler s1) /\
            (!s7. data_jump_exc (DSEMAUX_sl xs lsz (SND p)) = SOME s7 ==>
                  ?lss sfs smx' phl.
                    data_evaluate (FST p,DSEMAUX_sl xs lsz (DSEMAUX_ssp smx sf pk (SND p))) =
                    (r,DSEMAUX_sl (data_state_stack s7) lss
                         (DSEMAUX_ssp smx' sfs phl
                            (data_state_handler_fupd (K (data_state_handler s7))
                               (data_state_locals_fupd (K (data_state_locals s7)) s1)))))
        | _ ->
            data_state_stack s1 = data_state_stack (SND p) /\
            data_state_handler s1 = data_state_handler (SND p) /\
            (?lss sfs smx' phl.
               data_evaluate (FST p,DSEMAUX_sl xs lsz (DSEMAUX_ssp smx sf pk (SND p))) =
               (r,DSEMAUX_sl xs lss (DSEMAUX_ssp smx' sfs phl s1))))`;;

let DSEMAUX_res_CASES = prove
 (`!P. P NONE /\ (!v. P (SOME (Rval v))) /\ (!v. P (SOME (Rerr (Rraise v)))) /\
       P (SOME (Rerr (Rabort Rtype_error))) /\ P (SOME (Rerr (Rabort Rtimeout_error))) /\
       (!f. P (SOME (Rerr (Rabort (Rffi_error f))))) ==>
       !r:((data_v list,data_v)result)option. P r`,
  REPEAT STRIP_TAC THEN
  STRUCT_CASES_TAC (ISPEC `r:((data_v list,data_v)result)option` (cases "option")) THEN
  ASM_REWRITE_TAC[] THEN
  STRUCT_CASES_TAC (ISPEC `a:(data_v list,data_v)result` (cases "result")) THEN
  ASM_REWRITE_TAC[] THEN
  STRUCT_CASES_TAC (ISPEC `a':(data_v)error_result` (cases "error_result")) THEN
  ASM_REWRITE_TAC[] THEN
  (fun (asl,w as g) -> let t = find_term (fun t -> is_var t && type_of t = `:abort`) w in
                       STRUCT_CASES_TAC (ISPEC t (cases "abort")) g) THEN
  ASM_REWRITE_TAC[]);;

let DSEMAUX_jump_exc_cong2 = prove
 (`!(s:(C,FFI)data_state) (t:(C,FFI)data_state) s2.
     data_state_stack t = data_state_stack s /\
     data_state_handler t = data_state_handler s /\
     data_jump_exc t = SOME s2 ==>
     ?s2'. data_jump_exc s = SOME s2' /\
           data_state_locals s2' = data_state_locals s2 /\
           data_state_stack s2' = data_state_stack s2 /\
           data_state_handler s2' = data_state_handler s2 /\
           data_state_locals_size s2' = data_state_locals_size s2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`s:(C,FFI)data_state`; `t:(C,FFI)data_state`] DSEMAUX_jump_exc_cong) THEN
  ASM_REWRITE_TAC[] THEN
  STRUCT_CASES_TAC(ISPEC `data_jump_exc (s:(C,FFI)data_state)` (cases "option")) THEN
  REWRITE_TAC[OPTION_MAP_DEF; option_DISTINCT; option_INJ] THEN
  DISCH_THEN SUBST_ALL_TAC THEN EXISTS_TAC `a:(C,FFI)data_state` THEN
  REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM]);;

let DSEMAUX_Seq_not_NONE = prove
 (`!c1 c2 (t:(C,FFI)data_state) x st.
     data_evaluate (c1,t) = (x,st) /\ ~(x = NONE) ==>
     data_evaluate (data_Seq c1 c2,t) = (x,st)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[data_evaluate_def] THEN
  ASM_REWRITE_TAC[pair_CASE_def]);;
let DSEMAUX_Seq_NONE = prove
 (`!c1 c2 (t:(C,FFI)data_state) st.
     data_evaluate (c1,t) = (NONE,st) ==>
     data_evaluate (data_Seq c1 c2,t) = data_evaluate (c2,st)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[data_evaluate_def] THEN
  ASM_REWRITE_TAC[pair_CASE_def]);;

let DSEMAUX_SL_SEQ_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE DSEMAUX_EVAL_CASE_EQS o
             ONCE_REWRITE_RULE[data_evaluate_def]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN DSEMAUX_SPLIT_CONJ_ASMS THEN RVEQ_TAC THEN
  REPEAT GEN_TAC THEN DISCH_TAC THENL
   [(* c1 returns NONE, then c2 *)
    USE_THEN "ih1" (fun ih -> MP_TAC (SPECL [`xs:stack list`; `lsz:num option`;
                                            `smx:num option`; `sf:bool`; `pk:num`]
       (MATCH_MP ih (ASSUME `data_evaluate (c1,s:(C,FFI)data_state) = NONE,y`)))) THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `lss1:num option` (X_CHOOSE_THEN `sfs1:bool`
        (X_CHOOSE_THEN `smx1:num option` (X_CHOOSE_THEN `phl1:num` ASSUME_TAC)))))) THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP DSEMAUX_Seq_NONE th]) THEN
    USE_THEN "ih2" (fun ih -> MP_TAC (SPECL [`xs:stack list`; `lss1:num option`;
                                            `smx1:num option`; `sfs1:bool`; `phl1:num`]
      (MATCH_MP (MATCH_MP ih (ASSUME `data_evaluate (c1,s:(C,FFI)data_state) = NONE,y`))
                (ASSUME `data_evaluate (c2,y:(C,FFI)data_state) = r,s1`)))) THEN
    ASM_REWRITE_TAC[] THEN
    REMOVE_THEN "ih1" (K ALL_TAC) THEN REMOVE_THEN "ih2" (K ALL_TAC) THEN
    SPEC_TAC (`r:((data_v list,data_v)result)option`,`r:((data_v list,data_v)result)option`) THEN
    MATCH_MP_TAC DSEMAUX_res_CASES THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
    CASE_REWRITE_TAC[option_DISTINCT] THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN CONJ_TAC THENL
     [MP_TAC (SPECL [`s:(C,FFI)data_state`; `y:(C,FFI)data_state`; `s2:(C,FFI)data_state`]
                    DSEMAUX_jump_exc_cong2) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN EXISTS_TAC `s2':(C,FFI)data_state` THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `s7:(C,FFI)data_state` THEN DISCH_TAC THEN
      MP_TAC (SPECL [`DSEMAUX_sl xs lss1 (y:(C,FFI)data_state)`;
                     `DSEMAUX_sl xs lsz (s:(C,FFI)data_state)`; `s7:(C,FFI)data_state`]
                    DSEMAUX_jump_exc_cong2) THEN
      ASM_REWRITE_TAC[DSEMAUX_sl_acc] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `s2':(C,FFI)data_state`) THEN ASM_REWRITE_TAC[]];
    (* c1 returns something else *)
    USE_THEN "ih1" (fun ih -> MP_TAC (SPECL [`xs:stack list`; `lsz:num option`;
                                            `smx:num option`; `sf:bool`; `pk:num`]
       (MATCH_MP ih (ASSUME `data_evaluate (c1,s:(C,FFI)data_state) = r,s1`)))) THEN
    ASM_REWRITE_TAC[] THEN
    REMOVE_THEN "ih1" (K ALL_TAC) THEN REMOVE_THEN "ih2" (K ALL_TAC) THEN
    UNDISCH_TAC `~(r:((data_v list,data_v)result)option = NONE)` THEN
    SPEC_TAC (`r:((data_v list,data_v)result)option`,`r:((data_v list,data_v)result)option`) THEN
    MATCH_MP_TAC DSEMAUX_res_CASES THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
    CASE_REWRITE_TAC[option_DISTINCT] THEN
    MESON_TAC[DSEMAUX_Seq_not_NONE; option_DISTINCT]];;

let DSEMAUX_SL_TYERR_TAC : tactic =
  REPEAT GEN_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) THEN
  CASE_REWRITE_TAC[];;
let DSEMAUX_SL_IH_TAC : tactic =
  FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `x:data_v` th) THEN ASM_REWRITE_TAC[] THEN NO_TAC);;
let DSEMAUX_SL_IF_TAC : tactic =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[data_evaluate_def] THEN REWRITE_TAC[DSEMAUX_sl_acc; DSEMAUX_ssp_acc] THEN
  DISJ_CASES_THEN2 (fun th -> REWRITE_TAC[th] THEN CASE_REWRITE_TAC[] THEN DSEMAUX_SL_TYERR_TAC)
    (X_CHOOSE_THEN `x:data_v` (fun th -> ASSUME_TAC th THEN REWRITE_TAC[th] THEN
                                         CASE_REWRITE_TAC[]))
    (ISPEC `data_get_var n (data_state_locals (s:(C,FFI)data_state))` (cases "option")) THEN
  ASM_CASES_TAC `isBool T x` THEN ASM_REWRITE_TAC[] THENL
   [DSEMAUX_SL_IH_TAC;
    ASM_CASES_TAC `isBool F x` THEN ASM_REWRITE_TAC[] THENL
     [DSEMAUX_SL_IH_TAC; DSEMAUX_SL_TYERR_TAC]];;

(* the property of the stack and locals_size swap, as a predicate          *)

let DSEMAUX_SLP_def = new_definition (CASE_TERM
  `DSEMAUX_SLP (c:data_prog) (s:(C,FFI)data_state) (r:((data_v list,data_v)result)option)
               (s1:(C,FFI)data_state) <=>
     !xs lsz smx sf pk.
       LENGTH xs = LENGTH (data_state_stack s) ==>
       (match r with
          SOME (Rerr (Rabort Rtype_error)) -> T
        | SOME (Rerr (Rabort a)) ->
            data_state_stack s1 = [] /\
            (?lss sfs smx' phl.
               data_evaluate (c,DSEMAUX_sl xs lsz (DSEMAUX_ssp smx sf pk s)) =
               (r,DSEMAUX_sl [] lss (DSEMAUX_ssp smx' sfs phl s1)))
        | SOME (Rerr (Rraise v)) ->
            (?s2. data_jump_exc s = SOME s2 /\
                  data_state_locals s2 = data_state_locals s1 /\
                  data_state_stack s2 = data_state_stack s1 /\
                  data_state_handler s2 = data_state_handler s1) /\
            (!s7. data_jump_exc (DSEMAUX_sl xs lsz s) = SOME s7 ==>
                  ?lss sfs smx' phl.
                    data_evaluate (c,DSEMAUX_sl xs lsz (DSEMAUX_ssp smx sf pk s)) =
                    (r,DSEMAUX_sl (data_state_stack s7) lss
                         (DSEMAUX_ssp smx' sfs phl
                            (data_state_handler_fupd (K (data_state_handler s7))
                               (data_state_locals_fupd (K (data_state_locals s7)) s1)))))
        | _ ->
            data_state_stack s1 = data_state_stack s /\
            data_state_handler s1 = data_state_handler s /\
            (?lss sfs smx' phl.
               data_evaluate (c,DSEMAUX_sl xs lsz (DSEMAUX_ssp smx sf pk s)) =
               (r,DSEMAUX_sl xs lss (DSEMAUX_ssp smx' sfs phl s1))))`);;

(* transfer of the swap property along a call that keeps the stack *)

(* tactics for the arms of the transfer lemmas: "tr" maps an evaluate     *)
(* of the inner program to an evaluate of the outer one                    *)

let DSEMAUX_TR_USE_TAC : tactic =
  USE_THEN "tr" (fun tr -> FIRST_ASSUM (fun th -> MP_TAC (MATCH_MP tr th))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[option_DISTINCT; GSYM option_DISTINCT]; ALL_TAC] THEN
  DISCH_THEN (fun th -> REWRITE_TAC[th]) THEN MESON_TAC[];;

let DSEMAUX_TR_PLAIN_TAC : tactic =
  REPEAT (FIRST_X_ASSUM (CHOOSE_THEN ASSUME_TAC o check (is_exists o concl))) THEN
  ASM_REWRITE_TAC[] THEN DSEMAUX_TR_USE_TAC;;

let DSEMAUX_is_jump_imp tm =
  let _,b = strip_forall tm in
  is_imp b &&
  (let a = fst (dest_imp b) in
   is_eq a && (try fst (dest_const (rator (lhs a))) = "data_jump_exc" with Failure _ -> false));;

let DSEMAUX_TR_RAISE_TAC : tactic =
  FIRST_X_ASSUM (X_CHOOSE_THEN `s2:(C,FFI)data_state` STRIP_ASSUME_TAC o
                 check (is_exists o concl)) THEN
  FIRST_X_ASSUM (LABEL_TAC "ih2" o check (DSEMAUX_is_jump_imp o concl)) THEN
  CONJ_TAC THENL
   [MP_TAC (SPECL [`s:(C,FFI)data_state`; `u:(C,FFI)data_state`; `s2:(C,FFI)data_state`]
                  DSEMAUX_jump_exc_cong2) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `s3:(C,FFI)data_state` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `s3:(C,FFI)data_state` THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `s7:(C,FFI)data_state` THEN DISCH_TAC THEN
    MP_TAC (SPECL [`DSEMAUX_sl xs lsz' (u:(C,FFI)data_state)`;
                   `DSEMAUX_sl xs lsz (s:(C,FFI)data_state)`; `s7:(C,FFI)data_state`]
                  DSEMAUX_jump_exc_cong2) THEN
    ASM_REWRITE_TAC[DSEMAUX_sl_acc] THEN
    DISCH_THEN(X_CHOOSE_THEN `s8:(C,FFI)data_state` STRIP_ASSUME_TAC) THEN
    REMOVE_THEN "ih2" (MP_TAC o SPEC `s8:(C,FFI)data_state`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN DSEMAUX_TR_USE_TAC];;

let DSEMAUX_SLP_SAME = prove
 (`!c prog (s:(C,FFI)data_state) u r s1 b.
     data_state_stack u = data_state_stack s /\
     data_state_handler u = data_state_handler s /\
     (r = NONE ==> b) /\ DSEMAUX_SLP prog u r s1 /\
     (!xs lsz smx sf pk. LENGTH xs = LENGTH (data_state_stack s) ==>
        ?lsz' smx' sf' pk'. !r' s'.
          data_evaluate (prog,DSEMAUX_sl xs lsz' (DSEMAUX_ssp smx' sf' pk' u)) = (r',s') ==>
          (r' = NONE ==> b) ==>
          data_evaluate (c,DSEMAUX_sl xs lsz (DSEMAUX_ssp smx sf pk s)) = (r',s'))
     ==> DSEMAUX_SLP c s r s1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[DSEMAUX_SLP_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "ih") (LABEL_TAC "tr"))))) THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REMOVE_THEN "tr" (MP_TAC o SPECL [`xs:stack list`; `lsz:num option`; `smx:num option`;
                                    `sf:bool`; `pk:num`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `lsz':num option` (X_CHOOSE_THEN `smx':num option`
    (X_CHOOSE_THEN `sf':bool` (X_CHOOSE_THEN `pk':num` (LABEL_TAC "tr"))))) THEN
  REMOVE_THEN "ih" (MP_TAC o SPECL [`xs:stack list`; `lsz':num option`; `smx':num option`;
                                    `sf':bool`; `pk':num`]) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(r:((data_v list,data_v)result)option) = NONE ==> b` THEN
  SPEC_TAC (`r:((data_v list,data_v)result)option`,`r:((data_v list,data_v)result)option`) THEN
  MATCH_MP_TAC DSEMAUX_res_CASES THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  CASE_REWRITE_TAC[option_DISTINCT] THEN REWRITE_TAC[] THEN
  REPEAT DISCH_TAC THEN
  DSEMAUX_SPLIT_CONJ_ASMS THEN
  FIRST [DSEMAUX_TR_PLAIN_TAC; DSEMAUX_TR_RAISE_TAC]);;

(* accessors of call_env, dec_clock and push_env; jump_exc and pop_env    *)
(* through a pushed frame                                                  *)

let DSEMAUX_call_env_sh = prove
 (`!args sz (s:(C,FFI)data_state).
     data_state_stack (data_call_env args sz s) = data_state_stack s /\
     data_state_handler (data_call_env args sz s) = data_state_handler s`,
  REWRITE_TAC[data_call_env_def; LET_DEF; LET_END_DEF; data_state_INFO.ri_accfupds; K_THM]);;

let DSEMAUX_dec_clock_sh = prove
 (`!(s:(C,FFI)data_state).
     data_state_stack (data_dec_clock s) = data_state_stack s /\
     data_state_handler (data_dec_clock s) = data_state_handler s /\
     data_state_locals_size (data_dec_clock s) = data_state_locals_size s`,
  REWRITE_TAC[data_dec_clock_def; data_state_INFO.ri_accfupds; K_THM]);;

let DSEMAUX_push_env_sh = prove
 (`!env b (s:(C,FFI)data_state).
     data_state_stack (data_push_env env b s) =
       CONS (if b then Exc (data_state_locals_size s) env (data_state_handler s)
             else data_Env (data_state_locals_size s) env) (data_state_stack s) /\
     data_state_handler (data_push_env env b s) =
       (if b then LENGTH (data_state_stack s) else data_state_handler s)`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN
  REWRITE_TAC[data_push_env_def; LET_DEF; LET_END_DEF; data_state_INFO.ri_accfupds; K_THM]);;

let DSEMAUX_set_var_sh = prove
 (`!n v (s:(C,FFI)data_state).
     data_state_stack (data_set_var n v s) = data_state_stack s /\
     data_state_handler (data_set_var n v s) = data_state_handler s`,
  REWRITE_TAC[data_set_var_def; data_state_INFO.ri_accfupds; K_THM]);;

let DSEMAUX_set_vars_sh = prove
 (`!ns vs (s:(C,FFI)data_state).
     data_state_stack (data_set_vars ns vs s) = data_state_stack s /\
     data_state_handler (data_set_vars ns vs s) = data_state_handler s`,
  REWRITE_TAC[data_set_vars_def; data_state_INFO.ri_accfupds; K_THM]);;

let DSEMAUX_ssp_handler_fupd = prove
 (`!smx sf pk (s:(C,FFI)data_state) h.
     data_state_handler_fupd (K h) (DSEMAUX_ssp smx sf pk s) =
     DSEMAUX_ssp smx sf pk (data_state_handler_fupd (K h) s)`,
  DSEMAUX_ssp_tac);;

let DSEMAUX_hl_fupd_id = prove
 (`!h e (s:(C,FFI)data_state).
     data_state_handler s = h /\ data_state_locals s = e ==>
     data_state_handler_fupd (K h) (data_state_locals_fupd (K e) s) = s`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN (SUBST1_TAC o SYM)) THEN
  REWRITE_TAC[data_state_component_equality; data_state_INFO.ri_accfupds; K_THM]);;

let DSEMAUX_jump_exc_Env_cons = prove
 (`!(s:(C,FFI)data_state) (t:(C,FFI)data_state) l e.
     data_state_stack t = CONS (data_Env l e) (data_state_stack s) ==>
     data_state_handler t = data_state_handler s ==>
     data_jump_exc t =
     OPTION_MAP (\s'. data_state_handler_fupd (K (data_state_handler s'))
                        (data_state_locals_fupd (K (data_state_locals s'))
                           (data_state_stack_fupd (K (data_state_stack s'))
                              (data_state_locals_size_fupd (K (data_state_locals_size s')) t))))
                (data_jump_exc s)`,
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN REWRITE_TAC[data_jump_exc_def] THEN
  ASM_REWRITE_TAC[LENGTH] THEN
  ASM_CASES_TAC `data_state_handler (s:(C,FFI)data_state) < LENGTH (data_state_stack s)` THENL
   [ASM_SIMP_TAC[LASTN_TL; ARITH_RULE `n < m ==> n < SUC m`] THEN
    REPEAT (COND_CASES_TAC ORELSE TOP_CASE_TAC) THEN
    REWRITE_TAC[OPTION_MAP_DEF] THEN
    REWRITE_TAC[data_state_component_equality; data_state_INFO.ri_accfupds; K_THM];
    ASM_REWRITE_TAC[OPTION_MAP_DEF] THEN
    ASM_CASES_TAC `data_state_handler (s:(C,FFI)data_state) = LENGTH (data_state_stack s)` THENL
     [ASM_REWRITE_TAC[LASTN_LEMMA; ARITH_RULE `n < SUC n`] THEN CASE_REWRITE_TAC[];
      ASM_SIMP_TAC[ARITH_RULE `~(n < m) /\ ~(n = m) ==> ~(n < SUC m)`]]]);;

let DSEMAUX_jump_exc_Env_cons2 = prove
 (`!(s:(C,FFI)data_state) (t:(C,FFI)data_state) l e s2.
     data_state_stack t = CONS (data_Env l e) (data_state_stack s) /\
     data_state_handler t = data_state_handler s /\
     data_jump_exc t = SOME s2 ==>
     ?s2'. data_jump_exc s = SOME s2' /\
           data_state_locals s2' = data_state_locals s2 /\
           data_state_stack s2' = data_state_stack s2 /\
           data_state_handler s2' = data_state_handler s2 /\
           data_state_locals_size s2' = data_state_locals_size s2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(MATCH_MP (MATCH_MP DSEMAUX_jump_exc_Env_cons
    (ASSUME `data_state_stack (t:(C,FFI)data_state) = CONS (data_Env l e) (data_state_stack (s:(C,FFI)data_state))`))
    (ASSUME `data_state_handler (t:(C,FFI)data_state) = data_state_handler (s:(C,FFI)data_state)`)) THEN
  ASM_REWRITE_TAC[] THEN
  STRUCT_CASES_TAC(ISPEC `data_jump_exc (s:(C,FFI)data_state)` (cases "option")) THEN
  REWRITE_TAC[OPTION_MAP_DEF; option_DISTINCT; option_INJ] THEN
  DISCH_THEN SUBST_ALL_TAC THEN EXISTS_TAC `a:(C,FFI)data_state` THEN
  REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM]);;

let DSEMAUX_jump_exc_Env_cons3 = prove
 (`!(s:(C,FFI)data_state) (t:(C,FFI)data_state) l e s7.
     data_state_stack t = CONS (data_Env l e) (data_state_stack s) /\
     data_state_handler t = data_state_handler s /\
     data_jump_exc s = SOME s7 ==>
     ?s7'. data_jump_exc t = SOME s7' /\
           data_state_locals s7' = data_state_locals s7 /\
           data_state_stack s7' = data_state_stack s7 /\
           data_state_handler s7' = data_state_handler s7 /\
           data_state_locals_size s7' = data_state_locals_size s7`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(MATCH_MP (MATCH_MP DSEMAUX_jump_exc_Env_cons
    (ASSUME `data_state_stack (t:(C,FFI)data_state) = CONS (data_Env l e) (data_state_stack (s:(C,FFI)data_state))`))
    (ASSUME `data_state_handler (t:(C,FFI)data_state) = data_state_handler (s:(C,FFI)data_state)`)) THEN
  ASM_REWRITE_TAC[OPTION_MAP_DEF] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[option_INJ; UNWIND_THM1] THEN
  REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM]);;

let DSEMAUX_jump_exc_Exc_top = prove
 (`!(t:(C,FFI)data_state) l e h xs.
     data_state_stack t = CONS (Exc l e h) xs /\ data_state_handler t = LENGTH xs ==>
     data_jump_exc t =
     SOME (data_state_handler_fupd (K h) (data_state_locals_fupd (K e)
             (data_state_stack_fupd (K xs) (data_state_locals_size_fupd (K l) t))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[data_jump_exc_def] THEN
  ASM_REWRITE_TAC[LENGTH; LASTN_LEMMA; ARITH_RULE `n < SUC n`] THEN CASE_REWRITE_TAC[]);;

let DSEMAUX_sl_pop_env = prove
 (`(!l e xs lss (s:(C,FFI)data_state).
      data_pop_env (DSEMAUX_sl (CONS (data_Env l e) xs) lss s) =
      SOME (DSEMAUX_sl xs l (data_state_locals_fupd (K e) s))) /\
   (!l e h xs lss (s:(C,FFI)data_state).
      data_pop_env (DSEMAUX_sl (CONS (Exc l e h) xs) lss s) =
      SOME (DSEMAUX_sl xs l (data_state_locals_fupd (K e) (data_state_handler_fupd (K h) s))))`,
  REWRITE_TAC[data_pop_env_def; DSEMAUX_sl_acc] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[option_INJ] THEN DSEMAUX_sl_tac);;

let DSEMAUX_pop_env_frame = prove
 (`(!l e xs (s:(C,FFI)data_state).
      data_state_stack s = CONS (data_Env l e) xs ==>
      data_pop_env s = SOME (DSEMAUX_sl xs l (data_state_locals_fupd (K e) s))) /\
   (!l e h xs (s:(C,FFI)data_state).
      data_state_stack s = CONS (Exc l e h) xs ==>
      data_pop_env s =
      SOME (DSEMAUX_sl xs l (data_state_locals_fupd (K e) (data_state_handler_fupd (K h) s))))`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[data_pop_env_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[option_INJ] THEN DSEMAUX_sl_tac);;

(* witnesses for ?v1 .. vn. L = R by matching R against L *)

let DSEMAUX_EQ_EXISTS_TAC : tactic = fun (asl,w as g) ->
  let vs,body = strip_exists w in
  let l,r = dest_eq body in
  let (_,tmi,_) = term_match [] r l in
  let wit = map (fun v -> try rev_assoc v tmi with Failure _ -> v) vs in
  (MAP_EVERY EXISTS_TAC wit THEN REFL_TAC) g;;

let DSEMAUX_sl_call_push = prove
 (`!xs (s:(C,FFI)data_state). LENGTH xs = LENGTH (data_state_stack s) ==>
     !args1 ss env b lsz smx sf pk.
       ?smx' sf'.
         data_call_env args1 ss (data_push_env env b
            (data_dec_clock (DSEMAUX_sl xs lsz (DSEMAUX_ssp smx sf pk s)))) =
         DSEMAUX_sl (CONS (if b then Exc lsz env (data_state_handler s) else data_Env lsz env) xs) ss
           (DSEMAUX_ssp smx' sf' pk
              (data_call_env args1 ss (data_push_env env b (data_dec_clock s))))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[DSEMAUX_sl_dec_clock; DSEMAUX_ssp_dec_clock] THEN
  MP_TAC (ISPECL [`env:data_v spt`; `b:bool`; `xs:stack list`; `lsz:num option`;
                  `DSEMAUX_ssp smx sf pk (data_dec_clock (s:(C,FFI)data_state))`]
                 DSEMAUX_sl_push_env) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[DSEMAUX_ssp_acc; DSEMAUX_dec_clock_sh]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[DSEMAUX_sl_call_env; DSEMAUX_ssp_call_env; DSEMAUX_ssp_push_env; DSEMAUX_ssp_ssp;
              DSEMAUX_ssp_acc; DSEMAUX_dec_clock_sh] THEN
  DSEMAUX_EQ_EXISTS_TAC);;

let DSEMAUX_sl_call_dec = prove
 (`!xs (s:(C,FFI)data_state) args1 ss lsz smx sf pk.
     ?smx' sf'.
       data_call_env args1 ss (data_dec_clock (DSEMAUX_sl xs lsz (DSEMAUX_ssp smx sf pk s))) =
       DSEMAUX_sl xs ss (DSEMAUX_ssp smx' sf' pk (data_call_env args1 ss (data_dec_clock s)))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[DSEMAUX_sl_dec_clock; DSEMAUX_ssp_dec_clock; DSEMAUX_sl_call_env;
              DSEMAUX_ssp_call_env; DSEMAUX_ssp_ssp; DSEMAUX_ssp_acc] THEN
  DSEMAUX_EQ_EXISTS_TAC);;

(* the swap property through the calls of Force and Call *)

let DSEMAUX_SLP_TAIL = prove
 (`!c prog args1 ss (s:(C,FFI)data_state) r s1.
     ~(r = NONE) /\ DSEMAUX_SLP prog (data_call_env args1 ss (data_dec_clock s)) r s1 /\
     (!xs lsz smx sf pk. LENGTH xs = LENGTH (data_state_stack s) ==>
        !r' s'. data_evaluate (prog,data_call_env args1 ss
                  (data_dec_clock (DSEMAUX_sl xs lsz (DSEMAUX_ssp smx sf pk s)))) = (r',s') ==>
                ~(r' = NONE) ==>
                data_evaluate (c,DSEMAUX_sl xs lsz (DSEMAUX_ssp smx sf pk s)) = (r',s'))
     ==> DSEMAUX_SLP c s r s1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC DSEMAUX_SLP_SAME THEN
  MAP_EVERY EXISTS_TAC [`prog:data_prog`;
                        `data_call_env args1 ss (data_dec_clock (s:(C,FFI)data_state))`; `F`] THEN
  ASM_REWRITE_TAC[DSEMAUX_call_env_sh; DSEMAUX_dec_clock_sh] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM (MP_TAC o SPECL [`xs:stack list`; `lsz:num option`; `smx:num option`;
                                 `sf:bool`; `pk:num`] o check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC (SPECL [`xs:stack list`; `s:(C,FFI)data_state`; `args1:data_v list`; `ss:num option`;
                 `lsz:num option`; `smx:num option`; `sf:bool`; `pk:num`] DSEMAUX_sl_call_dec) THEN
  DISCH_THEN (X_CHOOSE_THEN `smx1:num option` (X_CHOOSE_THEN `sf1:bool` SUBST1_TAC)) THEN
  DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC [`ss:num option`; `smx1:num option`; `sf1:bool`; `pk:num`] THEN
  FIRST_ASSUM ACCEPT_TAC);;

let DSEMAUX_SLP_FRAME_ABORT = prove
 (`!c prog args1 ss env b (s:(C,FFI)data_state) a s1.
     DSEMAUX_SLP prog (data_call_env args1 ss (data_push_env env b (data_dec_clock s)))
       (SOME (Rerr (Rabort a))) s1 /\
     (!xs lsz smx sf pk. LENGTH xs = LENGTH (data_state_stack s) ==>
        !a' s'. data_evaluate (prog,data_call_env args1 ss (data_push_env env b
                  (data_dec_clock (DSEMAUX_sl xs lsz (DSEMAUX_ssp smx sf pk s))))) =
                (SOME (Rerr (Rabort a')),s') ==>
                data_evaluate (c,DSEMAUX_sl xs lsz (DSEMAUX_ssp smx sf pk s)) =
                (SOME (Rerr (Rabort a')),s'))
     ==> DSEMAUX_SLP c s (SOME (Rerr (Rabort a))) s1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[DSEMAUX_SLP_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih") (LABEL_TAC "tr")) THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REMOVE_THEN "tr" (MP_TAC o SPECL [`xs:stack list`; `lsz:num option`; `smx:num option`;
                                    `sf:bool`; `pk:num`]) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM (fun th -> MP_TAC (SPECL [`args1:data_v list`; `ss:num option`; `env:data_v spt`;
                 `b:bool`; `lsz:num option`; `smx:num option`; `sf:bool`; `pk:num`]
                 (MATCH_MP DSEMAUX_sl_call_push th))) THEN
  DISCH_THEN (X_CHOOSE_THEN `smx1:num option` (X_CHOOSE_THEN `sf1:bool` SUBST1_TAC)) THEN
  DISCH_THEN (LABEL_TAC "tr") THEN
  REMOVE_THEN "ih" (MP_TAC o SPECL
    [`CONS (if b then Exc lsz env (data_state_handler (s:(C,FFI)data_state))
            else data_Env lsz env) xs`;
     `ss:num option`; `smx1:num option`; `sf1:bool`; `pk:num`]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[LENGTH; DSEMAUX_call_env_sh; DSEMAUX_push_env_sh; DSEMAUX_dec_clock_sh] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  STRUCT_CASES_TAC (ISPEC `a:abort` (cases "abort")) THEN
  CASE_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "tr" (fun tr -> FIRST_ASSUM (fun th -> MP_TAC (MATCH_MP tr th))) THEN
  DISCH_THEN (fun th -> REWRITE_TAC[th; PAIR_EQ]) THEN DSEMAUX_EQ_EXISTS_TAC);;

let DSEMAUX_SLP_FRAME_RAISE = prove
 (`!c prog args1 ss env (s:(C,FFI)data_state) v s1.
     DSEMAUX_SLP prog (data_call_env args1 ss (data_push_env env F (data_dec_clock s)))
       (SOME (Rerr (Rraise v))) s1 /\
     (!xs lsz smx sf pk. LENGTH xs = LENGTH (data_state_stack s) ==>
        !s'. data_evaluate (prog,data_call_env args1 ss (data_push_env env F
               (data_dec_clock (DSEMAUX_sl xs lsz (DSEMAUX_ssp smx sf pk s))))) =
             (SOME (Rerr (Rraise v)),s') ==>
             data_evaluate (c,DSEMAUX_sl xs lsz (DSEMAUX_ssp smx sf pk s)) =
             (SOME (Rerr (Rraise v)),s'))
     ==> DSEMAUX_SLP c s (SOME (Rerr (Rraise v))) s1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[DSEMAUX_SLP_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih") (LABEL_TAC "tr")) THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REMOVE_THEN "tr" (MP_TAC o SPECL [`xs:stack list`; `lsz:num option`; `smx:num option`;
                                    `sf:bool`; `pk:num`]) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM (fun th -> MP_TAC (SPECL [`args1:data_v list`; `ss:num option`; `env:data_v spt`;
                 `F`; `lsz:num option`; `smx:num option`; `sf:bool`; `pk:num`]
                 (MATCH_MP DSEMAUX_sl_call_push th))) THEN
  REWRITE_TAC[] THEN
  DISCH_THEN (X_CHOOSE_THEN `smx1:num option` (X_CHOOSE_THEN `sf1:bool` SUBST1_TAC)) THEN
  DISCH_THEN (LABEL_TAC "tr") THEN
  REMOVE_THEN "ih" (MP_TAC o SPECL
    [`CONS (data_Env lsz env) xs`; `ss:num option`; `smx1:num option`; `sf1:bool`; `pk:num`]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[LENGTH; DSEMAUX_call_env_sh; DSEMAUX_push_env_sh; DSEMAUX_dec_clock_sh] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CASE_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `s2:(C,FFI)data_state` STRIP_ASSUME_TAC)
                             (LABEL_TAC "ih2")) THEN
  CONJ_TAC THENL
   [MP_TAC (SPECL [`s:(C,FFI)data_state`;
                   `data_call_env args1 ss (data_push_env env F (data_dec_clock (s:(C,FFI)data_state)))`;
                   `data_state_locals_size (s:(C,FFI)data_state)`; `env:data_v spt`;
                   `s2:(C,FFI)data_state`] DSEMAUX_jump_exc_Env_cons2) THEN
    REWRITE_TAC[DSEMAUX_call_env_sh; DSEMAUX_push_env_sh; DSEMAUX_dec_clock_sh] THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `s3:(C,FFI)data_state` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `s3:(C,FFI)data_state` THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `s7:(C,FFI)data_state` THEN DISCH_TAC THEN
    MP_TAC (SPECL [`DSEMAUX_sl xs lsz (s:(C,FFI)data_state)`;
                   `DSEMAUX_sl (CONS (data_Env lsz env) xs) ss
                      (data_call_env args1 ss (data_push_env env F (data_dec_clock (s:(C,FFI)data_state))))`;
                   `lsz:num option`; `env:data_v spt`; `s7:(C,FFI)data_state`]
                  DSEMAUX_jump_exc_Env_cons3) THEN
    REWRITE_TAC[DSEMAUX_sl_acc; DSEMAUX_call_env_sh; DSEMAUX_push_env_sh; DSEMAUX_dec_clock_sh] THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `s8:(C,FFI)data_state` STRIP_ASSUME_TAC) THEN
    REMOVE_THEN "ih2" (MP_TAC o SPEC `s8:(C,FFI)data_state`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN
    USE_THEN "tr" (fun tr -> FIRST_ASSUM (fun th -> MP_TAC (MATCH_MP tr th))) THEN
    DISCH_THEN (fun th -> REWRITE_TAC[th; PAIR_EQ]) THEN DSEMAUX_EQ_EXISTS_TAC]);;

(* the IH of a transfer lemma at the state that its "tr" hypothesis uses *)

let DSEMAUX_sl_ssp_args t =
  let h,args = strip_comb t in
  if fst(dest_const h) <> "DSEMAUX_sl" || length args <> 3 then failwith "sl_ssp_args" else
  let sp = el 2 args in
  let h2,args2 = strip_comb sp in
  if fst(dest_const h2) <> "DSEMAUX_ssp" || length args2 <> 4 then failwith "sl_ssp_args" else
  [el 0 args; el 1 args; el 0 args2; el 1 args2; el 2 args2], el 3 args2;;

let DSEMAUX_IH_FROM_TR_TAC : tactic = fun (asl,w as g) ->
  let tr = concl (assoc "tr" asl) in
  let is_target t =
    is_comb t && (try fst(dest_const(rator t)) = "data_evaluate" with Failure _ -> false) &&
    is_pair (rand t) &&
    (try let _,inner = DSEMAUX_sl_ssp_args (snd (dest_pair (rand t))) in not (is_var inner)
     with Failure _ -> false) in
  let t = find_term is_target tr in
  let insts,_ = DSEMAUX_sl_ssp_args (snd (dest_pair (rand t))) in
  (REMOVE_THEN "ih" (MP_TAC o SPECL insts) THEN
   ANTS_TAC THENL
    [REWRITE_TAC[LENGTH; DSEMAUX_call_env_sh; DSEMAUX_push_env_sh; DSEMAUX_dec_clock_sh] THEN
     ASM_REWRITE_TAC[];
     ALL_TAC]) g;;

let DSEMAUX_POP_RW_TAC : tactic =
  FIRST_ASSUM (fun th -> REWRITE_TAC[MATCH_MP (CONJUNCT1 DSEMAUX_pop_env_frame) th]) ORELSE
  FIRST_ASSUM (fun th -> REWRITE_TAC[MATCH_MP (CONJUNCT2 DSEMAUX_pop_env_frame) th]);;

let DSEMAUX_SLP_POP = prove
 (`!c prog args1 ss env b (s:(C,FFI)data_state) vs s2 s3
    (f:(C,FFI)data_state->(C,FFI)data_state).
     DSEMAUX_SLP prog (data_call_env args1 ss (data_push_env env b (data_dec_clock s)))
       (SOME (Rval vs)) s2 /\
     data_pop_env s2 = SOME s3 /\
     (!xs lsz st. f (DSEMAUX_sl xs lsz st) = DSEMAUX_sl xs lsz (f st)) /\
     (!smx sf pk st. f (DSEMAUX_ssp smx sf pk st) = DSEMAUX_ssp smx sf pk (f st)) /\
     (!st. data_state_stack (f st) = data_state_stack st /\
           data_state_handler (f st) = data_state_handler st) /\
     (!xs lsz smx sf pk. LENGTH xs = LENGTH (data_state_stack s) ==>
        !s2' s3'. data_evaluate (prog,data_call_env args1 ss (data_push_env env b
                    (data_dec_clock (DSEMAUX_sl xs lsz (DSEMAUX_ssp smx sf pk s))))) =
                  (SOME (Rval vs),s2') ==>
                  data_pop_env s2' = SOME s3' ==>
                  data_evaluate (c,DSEMAUX_sl xs lsz (DSEMAUX_ssp smx sf pk s)) = (NONE,f s3'))
     ==> DSEMAUX_SLP c s NONE (f s3)`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[DSEMAUX_SLP_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "tr")))))) THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN CASE_REWRITE_TAC[] THEN
  REMOVE_THEN "tr" (MP_TAC o SPECL [`xs:stack list`; `lsz:num option`; `smx:num option`;
                                    `sf:bool`; `pk:num`]) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM (fun th -> MP_TAC (REWRITE_RULE[SKOLEM_THM] (MATCH_MP DSEMAUX_sl_call_push th))) THEN
  DISCH_THEN (CHOOSE_THEN (CHOOSE_THEN (fun th -> REWRITE_TAC[th]))) THEN
  DISCH_THEN (LABEL_TAC "tr") THEN
  DSEMAUX_IH_FROM_TR_TAC THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[DSEMAUX_call_env_sh; DSEMAUX_push_env_sh; DSEMAUX_dec_clock_sh] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `lss0:num option` (X_CHOOSE_THEN `sfs0:bool`
      (X_CHOOSE_THEN `smx0:num option` (X_CHOOSE_THEN `phl0:num` ASSUME_TAC)))))) THEN
  FIRST_X_ASSUM (MP_TAC o check (fun th -> try fst(dest_const(rator(lhs(concl th)))) =
                                              "data_pop_env" with Failure _ -> false)) THEN
  DSEMAUX_POP_RW_TAC THEN REWRITE_TAC[option_INJ] THEN
  DISCH_THEN (SUBST_ALL_TAC o SYM) THEN
  USE_THEN "tr" (fun tr -> FIRST_ASSUM (fun th ->
    MP_TAC (REWRITE_RULE[DSEMAUX_sl_pop_env; option_INJ; FORALL_UNWIND_THM1; FORALL_UNWIND_THM2] (MATCH_MP tr th)))) THEN
  DISCH_THEN (fun th -> REWRITE_TAC[th]) THEN
  ASM_REWRITE_TAC[DSEMAUX_sl_acc; data_state_INFO.ri_accfupds; K_THM; PAIR_EQ;
                  DSEMAUX_ssp_handler_fupd; DSEMAUX_ssp_fupds; DSEMAUX_sl_ssp; DSEMAUX_sl_sl] THEN
  DSEMAUX_EQ_EXISTS_TAC);;

let DSEMAUX_SLP_HANDLE = prove
 (`!c prog args1 ss env (s:(C,FFI)data_state) x s2 n h r s1.
     DSEMAUX_SLP prog (data_call_env args1 ss (data_push_env env T (data_dec_clock s)))
       (SOME (Rerr (Rraise x))) s2 /\
     DSEMAUX_SLP h (data_set_var n x s2) r s1 /\
     (!xs lsz smx sf pk. LENGTH xs = LENGTH (data_state_stack s) ==>
        !s2'. data_evaluate (prog,data_call_env args1 ss (data_push_env env T
                (data_dec_clock (DSEMAUX_sl xs lsz (DSEMAUX_ssp smx sf pk s))))) =
              (SOME (Rerr (Rraise x)),s2') ==>
              data_evaluate (c,DSEMAUX_sl xs lsz (DSEMAUX_ssp smx sf pk s)) =
              data_evaluate (h,data_set_var n x s2'))
     ==> DSEMAUX_SLP c s r s1`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih") (CONJUNCTS_THEN2 (LABEL_TAC "ihh")
                                                               (LABEL_TAC "tr0"))) THEN
  SUBGOAL_THEN `data_state_stack (s2:(C,FFI)data_state) = data_state_stack (s:(C,FFI)data_state) /\
                data_state_handler s2 = data_state_handler s /\ data_state_locals s2 = env`
    STRIP_ASSUME_TAC THENL
   [USE_THEN "ih" (MP_TAC o SPECL
      [`data_state_stack (data_call_env args1 ss (data_push_env env T
          (data_dec_clock (s:(C,FFI)data_state))))`;
       `NONE:num option`; `NONE:num option`; `F`; `0`] o REWRITE_RULE[DSEMAUX_SLP_def]) THEN
    REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    DISCH_THEN (X_CHOOSE_THEN `s3:(C,FFI)data_state` STRIP_ASSUME_TAC o CONJUNCT1) THEN
    MP_TAC (SPECL [`data_call_env args1 ss (data_push_env env T (data_dec_clock (s:(C,FFI)data_state)))`;
                   `data_state_locals_size (s:(C,FFI)data_state)`; `env:data_v spt`;
                   `data_state_handler (s:(C,FFI)data_state)`; `data_state_stack (s:(C,FFI)data_state)`]
                  DSEMAUX_jump_exc_Exc_top) THEN
    REWRITE_TAC[DSEMAUX_call_env_sh; DSEMAUX_push_env_sh; DSEMAUX_dec_clock_sh] THEN
    ASM_REWRITE_TAC[option_INJ] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC (REWRITE_RULE[data_state_INFO.ri_accfupds; K_THM]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC DSEMAUX_SLP_SAME THEN
  MAP_EVERY EXISTS_TAC [`h:data_prog`; `data_set_var n x (s2:(C,FFI)data_state)`; `T`] THEN
  ASM_REWRITE_TAC[DSEMAUX_set_var_sh] THEN
  REPEAT STRIP_TAC THEN
  REMOVE_THEN "tr0" (MP_TAC o SPECL [`xs:stack list`; `lsz:num option`; `smx:num option`;
                                     `sf:bool`; `pk:num`]) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM (fun th -> MP_TAC (SPECL [`args1:data_v list`; `ss:num option`; `env:data_v spt`;
                 `T`; `lsz:num option`; `smx:num option`; `sf:bool`; `pk:num`]
                 (MATCH_MP DSEMAUX_sl_call_push th))) THEN
  REWRITE_TAC[] THEN
  DISCH_THEN (X_CHOOSE_THEN `smx1:num option` (X_CHOOSE_THEN `sf1:bool` SUBST1_TAC)) THEN
  DISCH_THEN (LABEL_TAC "tr0") THEN
  REMOVE_THEN "ih" (MP_TAC o SPECL
    [`CONS (Exc lsz env (data_state_handler (s:(C,FFI)data_state))) xs`; `ss:num option`;
     `smx1:num option`; `sf1:bool`; `pk:num`] o REWRITE_RULE[DSEMAUX_SLP_def]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[LENGTH; DSEMAUX_call_env_sh; DSEMAUX_push_env_sh; DSEMAUX_dec_clock_sh] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CASE_REWRITE_TAC[] THEN DISCH_THEN (MP_TAC o CONJUNCT2) THEN
  MP_TAC (SPECL [`DSEMAUX_sl (CONS (Exc lsz env (data_state_handler (s:(C,FFI)data_state))) xs) ss
                    (data_call_env args1 ss (data_push_env env T (data_dec_clock s)))`;
                 `lsz:num option`; `env:data_v spt`; `data_state_handler (s:(C,FFI)data_state)`;
                 `xs:stack list`] DSEMAUX_jump_exc_Exc_top) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[DSEMAUX_sl_acc; DSEMAUX_call_env_sh; DSEMAUX_push_env_sh; DSEMAUX_dec_clock_sh] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN (fun th -> DISCH_THEN (MP_TAC o C MATCH_MP th)) THEN
  REWRITE_TAC[DSEMAUX_sl_acc; data_state_INFO.ri_accfupds; K_THM] THEN
  MP_TAC (SPECL [`data_state_handler (s:(C,FFI)data_state)`; `env:data_v spt`;
                 `s2:(C,FFI)data_state`] DSEMAUX_hl_fupd_id) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  DISCH_THEN (X_CHOOSE_THEN `lss0:num option` (X_CHOOSE_THEN `sfs0:bool`
    (X_CHOOSE_THEN `smx0:num option` (X_CHOOSE_THEN `phl0:num` ASSUME_TAC)))) THEN
  USE_THEN "tr0" (fun tr -> FIRST_ASSUM (fun th -> MP_TAC (MATCH_MP tr th))) THEN
  REWRITE_TAC[DSEMAUX_sl_set_var; DSEMAUX_ssp_set_var] THEN DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC [`lss0:num option`; `smx0:num option`; `sfs0:bool`; `phl0:num`] THEN
  ASM_REWRITE_TAC[]);;

(* the transfer lemmas with their DSEMAUX_SLP hypothesis first, for         *)
(* MATCH_MP with an induction hypothesis                                     *)

let DSEMAUX_is_slp t =
  try fst(dest_const(fst(strip_comb t))) = "DSEMAUX_SLP" with Failure _ -> false;;

let DSEMAUX_SLP_FIRST th =
  let th1 = SPEC_ALL th in
  let ant,con = dest_imp (concl th1) in
  let cjs = conjuncts ant in
  let aks = filter DSEMAUX_is_slp cjs in
  let rest = filter (fun t -> not (mem t aks)) cjs in
  let rest_tm = list_mk_conj rest in
  let rths = CONJUNCTS (ASSUME rest_tm) in
  let th2 = MP th1 (end_itlist CONJ
                      (map (fun t -> if mem t aks then ASSUME t
                                     else find (fun th -> concl th = t) rths) cjs)) in
  GEN_ALL (itlist DISCH aks (DISCH rest_tm th2));;

(* all instances of a rule by its DSEMAUX_SLP antecedents and assumptions *)

let rec DSEMAUX_RULE_MPS asl th =
  let _,b = strip_forall (concl th) in
  if is_imp b && DSEMAUX_is_slp (fst (dest_imp b)) then
    flat (map (fun (_,ath) -> try DSEMAUX_RULE_MPS asl (MATCH_MP th ath) with Failure _ -> [])
              asl)
  else [th];;

let DSEMAUX_SLP_RULES =
  map DSEMAUX_SLP_FIRST
    [DSEMAUX_SLP_TAIL; DSEMAUX_SLP_FRAME_ABORT; DSEMAUX_SLP_FRAME_RAISE;
     DSEMAUX_SLP_POP; DSEMAUX_SLP_HANDLE];;

let DSEMAUX_sl_stack_fupd = prove
 (`!x xs lsz (s:(C,FFI)data_state).
     data_state_stack_fupd (K x) (DSEMAUX_sl xs lsz s) = DSEMAUX_sl x lsz s`,
  DSEMAUX_sl_tac);;

(* rewrite data_push_env e b (DSEMAUX_sl X Y S) of the goal *)

let DSEMAUX_SL_PUSH_TAC : tactic = fun (asl,w as g) ->
  let is_t t = is_comb t &&
    (try let h,args = strip_comb t in fst(dest_const h) = "data_push_env" && length args = 3 &&
         fst(dest_const(fst(strip_comb(el 2 args)))) = "DSEMAUX_sl"
     with Failure _ -> false) in
  let t = find_term is_t w in
  let _,args = strip_comb t in
  let _,sargs = strip_comb (el 2 args) in
  (MP_TAC (ISPECL [el 0 args; el 1 args; el 0 sargs; el 1 sargs; el 2 sargs] DSEMAUX_sl_push_env) THEN
   ANTS_TAC THENL
    [REWRITE_TAC[DSEMAUX_ssp_acc; DSEMAUX_sl_acc; DSEMAUX_dec_clock_sh] THEN ASM_REWRITE_TAC[];
     DISCH_THEN (fun th -> REWRITE_TAC[th])]) g;;

let DSEMAUX_SL_RWS2 = DSEMAUX_sl_stack_fupd :: DSEMAUX_SL_RWS;;

let DSEMAUX_SL_LOOP2_TAC : tactic =
  REPEAT (CHANGED_TAC (CASE_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
                       ASM_REWRITE_TAC (PAIR_EQ :: IS_SOME_DEF :: DSEMAUX_SL_RWS2)) ORELSE
          DSEMAUX_SSP_DO_APP_RW_TAC ORELSE DSEMAUX_SL_PUSH_TAC);;

(* a branch without a recursive call *)

let DSEMAUX_SL_LEAF_TAC : tactic =
  REWRITE_TAC[DSEMAUX_SLP_def] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN CASE_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY (ONCE_REWRITE_TAC[data_evaluate_def] THEN REWRITE_TAC DSEMAUX_SL_RWS2 THEN
       DSEMAUX_SL_LOOP2_TAC THEN DSEMAUX_SL_FINISH_TAC THEN NO_TAC) THEN
  ASM_REWRITE_TAC DSEMAUX_stack_max_rws;;

(* the "tr" goal of a transfer lemma: unfold the outer evaluate once and   *)
(* run it on the facts of the branch                                        *)

let DSEMAUX_TR_GOAL_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  REPEAT (DISCH_THEN (fun th -> if is_eq (concl th) then ASSUME_TAC th else failwith "")) THEN
  ONCE_REWRITE_TAC[data_evaluate_def] THEN
  REPEAT (CHANGED_TAC (ASM_REWRITE_TAC[DSEMAUX_sl_acc; DSEMAUX_ssp_acc; IS_SOME_DEF] THEN
                       CASE_REWRITE_TAC[])) THEN
  REPEAT (TOP_CASE_TAC THEN ASM_REWRITE_TAC[option_DISTINCT] THEN CASE_REWRITE_TAC[]);;

let DSEMAUX_ERR_SPLIT_TAC : tactic = fun (asl,w as g) ->
  let e = find (fun v -> type_of v = `:(data_v)error_result`) (frees w) in
  DISJ_CASES_THEN2 (CHOOSE_THEN SUBST_ALL_TAC) (CHOOSE_THEN SUBST_ALL_TAC)
    (ISPEC e (cases "error_result")) g;;

(* a branch with a recursive call: one of the transfer lemmas *)

let DSEMAUX_SL_REC_TAC : tactic =
  TRY DSEMAUX_ERR_SPLIT_TAC THEN
  (fun (asl,w as g) ->
     FIRST (map MATCH_MP_TAC (flat (map (DSEMAUX_RULE_MPS asl) DSEMAUX_SLP_RULES))) g) THEN
  REPEAT CONJ_TAC THEN
  TRY (ASM_REWRITE_TAC[option_DISTINCT; DSEMAUX_sl_set_var; DSEMAUX_ssp_set_var;
                       DSEMAUX_set_var_sh; DSEMAUX_sl_set_vars; DSEMAUX_ssp_set_vars;
                       DSEMAUX_set_vars_sh] THEN NO_TAC) THEN
  DSEMAUX_TR_GOAL_TAC;;

let DSEMAUX_SL_CALL_CLAUSE_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[IS_SOME_DEF]) THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE DSEMAUX_EVAL_CASE_EQS o
             ONCE_REWRITE_RULE[data_evaluate_def]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN DSEMAUX_SPLIT_CONJ_ASMS THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[option_INJ; IMP_CONJ; RIGHT_FORALL_IMP_THM;
                              FORALL_UNWIND_THM1; option_DISTINCT; PAIR_EQ; IS_SOME_DEF]) THEN
  REPEAT DSEMAUX_RES_TAC THEN
  FIRST [DSEMAUX_SL_REC_TAC THEN NO_TAC; DSEMAUX_SL_LEAF_TAC];;

(* the generalised stack and locals_size swap (with the ssp fields) *)

let DSEMAUX_evaluate_sl = prove
 (DSEMAUX_SL_GOAL,
  MATCH_MP_TAC data_evaluate_ind THEN REWRITE_TAC[FST; SND] THEN REPEAT CONJ_TAC THENL
   [DSEMAUX_SL_SIMPLE_TAC; DSEMAUX_SL_SIMPLE_TAC; DSEMAUX_SL_SIMPLE_TAC;
    DSEMAUX_SL_SIMPLE_TAC; DSEMAUX_SL_SIMPLE_TAC; DSEMAUX_SL_RAISE_TAC;
    DSEMAUX_SL_SIMPLE_TAC; DSEMAUX_SL_SEQ_TAC; DSEMAUX_SL_IF_TAC;
    REWRITE_TAC[GSYM DSEMAUX_SLP_def] THEN DSEMAUX_SL_CALL_CLAUSE_TAC;
    REWRITE_TAC[GSYM DSEMAUX_SLP_def] THEN DSEMAUX_SL_CALL_CLAUSE_TAC]);;
(* HOL4's statement: the instance smx = stack_max s, sf = safe_for_space s, *)
(* pk = peak_heap_length s of DSEMAUX_evaluate_sl                            *)

let DSEMAUX_ARM_EX_TAC : tactic =
  DISCH_THEN (X_CHOOSE_THEN `lss0:num option` (X_CHOOSE_THEN `sfs0:bool`
    (X_CHOOSE_THEN `smx0:num option` (X_CHOOSE_THEN `phl0:num`
      (fun th -> MAP_EVERY EXISTS_TAC [`lss0:num option`; `sfs0:bool`; `smx0:num option`;
                                       `phl0:num`] THEN
                 REWRITE_TAC[REWRITE_RULE[DSEMAUX_sl_def; DSEMAUX_ssp_def] th]))))) THEN
  ASM_REWRITE_TAC[PAIR_EQ; data_state_component_equality; data_state_INFO.ri_accfupds; K_THM];;

(* the instance at xs lsz of the swap fact "m" (avoiding the collapse of *)
(* an MP_TAC'd instance of an assumption by ASM_REWRITE_TAC)              *)

let DSEMAUX_M_INST_TAC : tactic =
  USE_THEN "m" (fun m -> FIRST_ASSUM (fun th ->
    MP_TAC (MATCH_MP (SPECL [`xs:stack list`; `lsz:num option`] m) (SYM th))));;

let evaluate_stack_and_locals_swap = prove
 (CASE_TERM
  `!c (s:(C,FFI)data_state).
     match data_evaluate (c,s) with
       (SOME (Rerr (Rabort Rtype_error)),s1) -> T
     | (SOME (Rerr (Rabort a)),s1) ->
         data_state_stack s1 = [] /\
         (!xs lsz. LENGTH (data_state_stack s) = LENGTH xs ==>
            ?lss sfs smx phl.
              data_evaluate (c,data_state_stack_fupd (K xs)
                                 (data_state_locals_size_fupd (K lsz) s)) =
              (SOME (Rerr (Rabort a)),
               data_state_locals_size_fupd (K lss)
                 (data_state_safe_for_space_fupd (K sfs)
                    (data_state_stack_max_fupd (K smx)
                       (data_state_peak_heap_length_fupd (K phl) s1)))))
     | (SOME (Rerr (Rraise t)),s1) ->
         (?s2. data_jump_exc s = SOME s2 /\
               data_state_locals s2 = data_state_locals s1 /\
               data_state_stack s2 = data_state_stack s1 /\
               data_state_handler s2 = data_state_handler s1 /\
               (!xs s7 lsz.
                  data_jump_exc (data_state_stack_fupd (K xs)
                                   (data_state_locals_size_fupd (K lsz) s)) = SOME s7 /\
                  LENGTH (data_state_stack s) = LENGTH xs ==>
                  ?lss sfs smx phl.
                    data_evaluate (c,data_state_stack_fupd (K xs)
                                       (data_state_locals_size_fupd (K lsz) s)) =
                    (SOME (Rerr (Rraise t)),
                     data_state_stack_fupd (K (data_state_stack s7))
                       (data_state_handler_fupd (K (data_state_handler s7))
                          (data_state_locals_fupd (K (data_state_locals s7))
                             (data_state_locals_size_fupd (K lss)
                                (data_state_safe_for_space_fupd (K sfs)
                                   (data_state_stack_max_fupd (K smx)
                                      (data_state_peak_heap_length_fupd (K phl) s1)))))))))
     | (res,s1) ->
         data_state_stack s1 = data_state_stack s /\
         data_state_handler s1 = data_state_handler s /\
         (!xs lsz. LENGTH (data_state_stack s) = LENGTH xs ==>
            ?lss sfs smx phl.
              data_evaluate (c,data_state_stack_fupd (K xs)
                                 (data_state_locals_size_fupd (K lsz) s)) =
              (res,
               data_state_locals_size_fupd (K lss)
                 (data_state_stack_fupd (K xs)
                    (data_state_safe_for_space_fupd (K sfs)
                       (data_state_stack_max_fupd (K smx)
                          (data_state_peak_heap_length_fupd (K phl) s1))))))`,
  REPEAT GEN_TAC THEN
  MP_TAC (ISPEC `(c:data_prog,s:(C,FFI)data_state)` DSEMAUX_evaluate_sl) THEN
  REWRITE_TAC[FST; SND] THEN
  MP_TAC (ISPEC `data_evaluate (c,s:(C,FFI)data_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN (X_CHOOSE_THEN `r:((data_v list,data_v)result)option`
    (X_CHOOSE_THEN `s1:(C,FFI)data_state` SUBST1_TAC)) THEN
  DISCH_THEN (MP_TAC o SPECL [`r:((data_v list,data_v)result)option`; `s1:(C,FFI)data_state`]) THEN
  REWRITE_TAC[] THEN
  DISCH_THEN (fun th ->
    MP_TAC (GEN `xs:stack list` (GEN `lsz:num option`
      (SPECL [`xs:stack list`; `lsz:num option`;
              `data_state_stack_max (s:(C,FFI)data_state)`;
              `data_state_safe_for_space (s:(C,FFI)data_state)`;
              `data_state_peak_heap_length (s:(C,FFI)data_state)`] th)))) THEN
  REWRITE_TAC[DSEMAUX_ssp_id] THEN
  SPEC_TAC (`r:((data_v list,data_v)result)option`,`r:((data_v list,data_v)result)option`) THEN
  MATCH_MP_TAC DSEMAUX_res_CASES THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  CASE_REWRITE_TAC[] THEN DISCH_THEN (LABEL_TAC "m") THEN
  TRY (USE_THEN "m" (MP_TAC o SPECL [`data_state_stack (s:(C,FFI)data_state)`;
                                    `data_state_locals_size (s:(C,FFI)data_state)`]) THEN
       REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
       REPEAT STRIP_TAC THEN
       DSEMAUX_M_INST_TAC THEN DISCH_THEN (MP_TAC o last o CONJUNCTS) THEN
       DSEMAUX_ARM_EX_TAC THEN NO_TAC) THEN
  (* the raise arm *)
  USE_THEN "m" (MP_TAC o SPECL [`data_state_stack (s:(C,FFI)data_state)`;
                                `data_state_locals_size (s:(C,FFI)data_state)`]) THEN
  REWRITE_TAC[] THEN
  DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_THEN `s2:(C,FFI)data_state` STRIP_ASSUME_TAC)
                              (K ALL_TAC)) THEN
  EXISTS_TAC `s2:(C,FFI)data_state` THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN
  DSEMAUX_M_INST_TAC THEN
  DISCH_THEN (MP_TAC o SPEC `s7:(C,FFI)data_state` o last o CONJUNCTS) THEN
  ASM_REWRITE_TAC[DSEMAUX_sl_def] THEN
  DSEMAUX_ARM_EX_TAC);;
let data_evaluate_stack_swap = prove
 (CASE_TERM
  `!c (s:(C,FFI)data_state).
     match data_evaluate (c,s) with
       (SOME (Rerr (Rabort Rtype_error)),s1) -> T
     | (SOME (Rerr (Rabort a)),s1) ->
         data_state_stack s1 = [] /\
         (!xs. LENGTH (data_state_stack s) = LENGTH xs ==>
            ?lss sfs smx phl.
              data_evaluate (c,data_state_stack_fupd (K xs) s) =
              (SOME (Rerr (Rabort a)),
               data_state_locals_size_fupd (K lss)
                 (data_state_safe_for_space_fupd (K sfs)
                    (data_state_stack_max_fupd (K smx)
                       (data_state_peak_heap_length_fupd (K phl) s1)))))
     | (SOME (Rerr (Rraise t)),s1) ->
         (?s2. data_jump_exc s = SOME s2 /\
               data_state_locals s2 = data_state_locals s1 /\
               data_state_stack s2 = data_state_stack s1 /\
               data_state_handler s2 = data_state_handler s1 /\
               (!xs s7.
                  data_jump_exc (data_state_stack_fupd (K xs) s) = SOME s7 /\
                  LENGTH (data_state_stack s) = LENGTH xs ==>
                  ?lss sfs smx phl.
                    data_evaluate (c,data_state_stack_fupd (K xs) s) =
                    (SOME (Rerr (Rraise t)),
                     data_state_stack_fupd (K (data_state_stack s7))
                       (data_state_handler_fupd (K (data_state_handler s7))
                          (data_state_locals_fupd (K (data_state_locals s7))
                             (data_state_locals_size_fupd (K lss)
                                (data_state_safe_for_space_fupd (K sfs)
                                   (data_state_stack_max_fupd (K smx)
                                      (data_state_peak_heap_length_fupd (K phl) s1)))))))))
     | (res,s1) ->
         data_state_stack s1 = data_state_stack s /\
         data_state_handler s1 = data_state_handler s /\
         (!xs. LENGTH (data_state_stack s) = LENGTH xs ==>
            ?lss sfs smx phl.
              data_evaluate (c,data_state_stack_fupd (K xs) s) =
              (res,
               data_state_locals_size_fupd (K lss)
                 (data_state_stack_fupd (K xs)
                    (data_state_safe_for_space_fupd (K sfs)
                       (data_state_stack_max_fupd (K smx)
                          (data_state_peak_heap_length_fupd (K phl) s1))))))`,
  REPEAT GEN_TAC THEN
  MP_TAC (SPECL [`c:data_prog`; `s:(C,FFI)data_state`] evaluate_stack_and_locals_swap) THEN
  MP_TAC (ISPEC `data_evaluate (c,s:(C,FFI)data_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN (X_CHOOSE_THEN `r:((data_v list,data_v)result)option`
    (X_CHOOSE_THEN `s1:(C,FFI)data_state` SUBST1_TAC)) THEN
  SPEC_TAC (`r:((data_v list,data_v)result)option`,`r:((data_v list,data_v)result)option`) THEN
  MATCH_MP_TAC DSEMAUX_res_CASES THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  CASE_REWRITE_TAC[] THEN
  TRY (STRIP_TAC THEN ASM_REWRITE_TAC[] THEN GEN_TAC THEN
       FIRST_X_ASSUM (MP_TAC o SPECL [`xs:stack list`;
                                      `data_state_locals_size (s:(C,FFI)data_state)`] o
                      check (is_forall o concl)) THEN
       REWRITE_TAC[DSEMAUX_fupd_id] THEN NO_TAC) THEN
  DISCH_THEN (X_CHOOSE_THEN `s2:(C,FFI)data_state` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `s2:(C,FFI)data_state` THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN
  FIRST_X_ASSUM (MP_TAC o SPECL [`xs:stack list`; `s7:(C,FFI)data_state`;
                                 `data_state_locals_size (s:(C,FFI)data_state)`] o
                 check (is_forall o concl)) THEN
  REWRITE_TAC[DSEMAUX_fupd_id]);;

let evaluate_stack = prove
 (CASE_TERM
  `!c (s:(C,FFI)data_state).
     match data_evaluate (c,s) with
       (SOME (Rerr (Rabort Rtype_error)),s1) -> T
     | (SOME (Rerr (Rabort _)),s1) -> data_state_stack s1 = []
     | (SOME (Rerr _),s1) ->
         (?s2. data_jump_exc s = SOME s2 /\
               data_state_locals s2 = data_state_locals s1 /\
               data_state_stack s2 = data_state_stack s1 /\
               data_state_handler s2 = data_state_handler s1)
     | (_,s1) ->
         data_state_stack s1 = data_state_stack s /\
         data_state_handler s1 = data_state_handler s`,
  REPEAT GEN_TAC THEN
  MP_TAC (SPECL [`c:data_prog`; `s:(C,FFI)data_state`] data_evaluate_stack_swap) THEN
  MP_TAC (ISPEC `data_evaluate (c,s:(C,FFI)data_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN (X_CHOOSE_THEN `r:((data_v list,data_v)result)option`
    (X_CHOOSE_THEN `s1:(C,FFI)data_state` SUBST1_TAC)) THEN
  SPEC_TAC (`r:((data_v list,data_v)result)option`,`r:((data_v list,data_v)result)option`) THEN
  MATCH_MP_TAC DSEMAUX_res_CASES THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  CASE_REWRITE_TAC[] THEN MESON_TAC[]);;

let evaluate_NONE_jump_exc = prove
 (`!c (s:(C,FFI)data_state) u1 x.
     data_evaluate (c,s) = (NONE,u1) /\ data_jump_exc u1 = SOME x ==>
     data_jump_exc s =
     SOME (data_state_stack_fupd (K (data_state_stack x))
             (data_state_handler_fupd (K (data_state_handler x))
                (data_state_locals_fupd (K (data_state_locals x))
                   (data_state_locals_size_fupd (K (data_state_locals_size x)) s))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`c:data_prog`; `s:(C,FFI)data_state`] evaluate_stack) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC (SPECL [`u1:(C,FFI)data_state`; `s:(C,FFI)data_state`] DSEMAUX_jump_exc_cong) THEN
  ASM_REWRITE_TAC[OPTION_MAP_DEF; option_INJ] THEN DISCH_THEN SUBST1_TAC THEN
  CONV_TAC (DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[option_INJ; data_state_component_equality; data_state_INFO.ri_accfupds; K_THM]);;

let evaluate_NONE_jump_exc_ALT = prove
 (`!c (s:(C,FFI)data_state) u1 x.
     data_evaluate (c,s) = (NONE,u1) /\ data_jump_exc s = SOME x ==>
     data_jump_exc u1 =
     SOME (data_state_stack_fupd (K (data_state_stack x))
             (data_state_handler_fupd (K (data_state_handler x))
                (data_state_locals_fupd (K (data_state_locals x))
                   (data_state_locals_size_fupd (K (data_state_locals_size x)) u1))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`c:data_prog`; `s:(C,FFI)data_state`] evaluate_stack) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC (SPECL [`s:(C,FFI)data_state`; `u1:(C,FFI)data_state`] DSEMAUX_jump_exc_cong) THEN
  ASM_REWRITE_TAC[OPTION_MAP_DEF; option_INJ] THEN DISCH_THEN SUBST1_TAC THEN
  CONV_TAC (DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[option_INJ; data_state_component_equality; data_state_INFO.ri_accfupds; K_THM]);;
(* the final locals are LN unless the result is NONE, a type error or an  *)
(* exception                                                                *)

let DSEMAUX_LN_CLAUSE_TAC : tactic =
  REPEAT GEN_TAC THEN
  (fun (asl,w as g) ->
     let a,_ = dest_imp w in
     if DSEMAUX_is_main_hyp a then ALL_TAC g
     else (DISCH_THEN STRIP_ASSUME_TAC THEN REPEAT GEN_TAC) g) THEN
  DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE DSEMAUX_EVAL_CASE_EQS o
             ONCE_REWRITE_RULE[data_evaluate_def]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN DSEMAUX_SPLIT_CONJ_ASMS THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[option_INJ; IMP_CONJ; RIGHT_FORALL_IMP_THM;
                              FORALL_UNWIND_THM1; option_DISTINCT; PAIR_EQ]) THEN
  REPEAT DSEMAUX_RES_TAC THEN
  ASM_REWRITE_TAC[option_DISTINCT; option_INJ; injectivity "result"; distinctness "result";
                  injectivity "error_result"; distinctness "error_result";
                  data_flush_state_def; data_state_INFO.ri_accfupds; K_THM; EXISTS_REFL;
                  TPROPSAUX_EXISTS_REFL'];;

let DSEMAUX_evaluate_LN = prove
 (`!p (r:((data_v list,data_v)result)option) (s1:(C,FFI)data_state).
     data_evaluate p = (r,s1) ==> ~(r = NONE) ==>
     ~(r = SOME (Rerr (Rabort Rtype_error))) ==>
     data_state_locals s1 = LN \/ ?t. r = SOME (Rerr (Rraise t))`,
  MATCH_MP_TAC data_evaluate_ind THEN REWRITE_TAC[FST; SND] THEN REPEAT CONJ_TAC THEN
  DSEMAUX_LN_CLAUSE_TAC);;

let evaluate_locals_LN_lemma = prove
 (`!c (s:(C,FFI)data_state).
     ~(FST (data_evaluate (c,s)) = NONE) /\
     ~(FST (data_evaluate (c,s)) = SOME (Rerr (Rabort Rtype_error))) ==>
     data_state_locals (SND (data_evaluate (c,s))) = LN \/
     ?t. FST (data_evaluate (c,s)) = SOME (Rerr (Rraise t))`,
  REPEAT GEN_TAC THEN
  MP_TAC (ISPEC `data_evaluate (c,s:(C,FFI)data_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN (X_CHOOSE_THEN `r:((data_v list,data_v)result)option`
    (X_CHOOSE_THEN `s1:(C,FFI)data_state` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[FST; SND] THEN ASM_MESON_TAC[DSEMAUX_evaluate_LN]);;

let evaluate_locals_LN = prove
 (`!c (s:(C,FFI)data_state) res t.
     data_evaluate (c,s) = (res,t) /\ ~(res = NONE) /\
     ~(res = SOME (Rerr (Rabort Rtype_error))) ==>
     data_state_locals t = LN \/ ?t. res = SOME (Rerr (Rraise t))`,
  MESON_TAC[DSEMAUX_evaluate_LN]);;

let locals_ok_def = cake_def
  `locals_ok (l1:A spt) (l2:A spt) <=>
     !v x. lookup v l1 = SOME x ==> lookup v l2 = SOME x`;;

let locals_ok_IMP = prove
 (`!l1 l2:A spt. locals_ok l1 l2 ==> domain l1 SUBSET domain l2`,
  REWRITE_TAC[locals_ok_def; SUBSET; domain_lookup] THEN MESON_TAC[]);;

let locals_ok_refl = prove
 (`!l:A spt. locals_ok l l`,
  REWRITE_TAC[locals_ok_def]);;

let locals_ok_cut_env = prove
 (`!l1 l2 names (x:A spt).
     locals_ok l1 l2 /\ data_cut_env names l1 = SOME x ==> data_cut_env names l2 = SOME x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_cut_env_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN STRIP_TAC THEN
  SUBGOAL_THEN `domain (names:num_set) SUBSET domain (l2:A spt)` ASSUME_TAC THENL
   [ASM_MESON_TAC[locals_ok_IMP; SUBSET_TRANS]; ALL_TAC] THEN
  ASM_REWRITE_TAC[option_INJ] THEN FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN
  REWRITE_TAC[mk_wf_eq; lookup_inter_alt] THEN GEN_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  RULE_ASSUM_TAC (REWRITE_RULE[SUBSET; domain_lookup; locals_ok_def]) THEN
  ASM_MESON_TAC[]);;

let locals_ok_get_var = prove
 (`!s l x (w:A). locals_ok s l /\ data_get_var x s = SOME w ==> data_get_var x l = SOME w`,
  REWRITE_TAC[locals_ok_def; data_get_var_def] THEN MESON_TAC[]);;

let locals_ok_get_vars = prove
 (`!x (w:A list) s l.
     locals_ok s l /\ data_get_vars x s = SOME w ==> data_get_vars x l = SOME w`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[data_get_vars_def] THEN REPEAT GEN_TAC THEN
  DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISJ_CASES_THEN2 (fun th -> REWRITE_TAC[th] THEN CASE_REWRITE_TAC[option_DISTINCT])
    (X_CHOOSE_THEN `a:A` (fun th -> ASSUME_TAC th THEN REWRITE_TAC[th]))
    (ISPEC `data_get_var h (s:A spt)` (cases "option")) THEN
  CASE_REWRITE_TAC[] THEN
  DISJ_CASES_THEN2 (fun th -> REWRITE_TAC[th] THEN CASE_REWRITE_TAC[option_DISTINCT])
    (X_CHOOSE_THEN `b:A list` (fun th -> ASSUME_TAC th THEN REWRITE_TAC[th]))
    (ISPEC `data_get_vars t (s:A spt)` (cases "option")) THEN
  CASE_REWRITE_TAC[option_INJ] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN `data_get_var h (l:A spt) = SOME a /\ data_get_vars t l = SOME b`
    (fun th -> REWRITE_TAC[th]) THENL
   [ASM_MESON_TAC[locals_ok_get_var]; CASE_REWRITE_TAC[]]);;

(* HOL4 [local] *)
let locals_ok_insert = prove
 (`!a b k (v:A). locals_ok a b ==> locals_ok (insert k v a) (insert k v b)`,
  REWRITE_TAC[locals_ok_def; lookup_insert] THEN REPEAT STRIP_TAC THEN
  POP_ASSUM MP_TAC THEN COND_CASES_TAC THEN ASM_MESON_TAC[]);;

(* HOL4 [local]: under locals_ok, the narrow cut in evaluate (Assign)      *)
(* succeeds on the larger locals and yields a state equal up to (and       *)
(* locals_ok on) its locals                                                *)
let cut_state_opt_locals_ok = prove
 (`!names_opt (s:(C,FFI)data_state) l s1.
     locals_ok (data_state_locals s) l /\ data_cut_state_opt names_opt s = SOME s1 ==>
     ?l'. data_cut_state_opt names_opt (data_state_locals_fupd (K l) s) =
          SOME (data_state_locals_fupd (K l') s1) /\
          locals_ok (data_state_locals s1) l'`,
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `names_opt:num_set option` (cases "option")) THEN
  REWRITE_TAC[data_cut_state_opt_def; data_cut_state_def] THEN CASE_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THENL
   [REWRITE_TAC[option_INJ] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
    EXISTS_TAC `l:data_v spt` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM] THEN
  DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISJ_CASES_THEN2 (fun th -> REWRITE_TAC[th] THEN CASE_REWRITE_TAC[option_DISTINCT])
    (X_CHOOSE_THEN `env:data_v spt` (fun th -> ASSUME_TAC th THEN REWRITE_TAC[th]))
    (ISPEC `data_cut_env a (data_state_locals (s:(C,FFI)data_state))` (cases "option")) THEN
  CASE_REWRITE_TAC[option_INJ] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN `data_cut_env a (l:data_v spt) = SOME env` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_MESON_TAC[locals_ok_cut_env]; ALL_TAC] THEN
  CASE_REWRITE_TAC[option_INJ] THEN EXISTS_TAC `env:data_v spt` THEN
  REWRITE_TAC[data_state_INFO.ri_fupdfupds; data_state_INFO.ri_accfupds; K_THM; DSEMAUX_K_o;
              locals_ok_refl]);;

(* ------------------------------------------------------------------------- *)
(* evaluate_locals: running with larger locals, generalised over the ssp    *)
(* fields                                                                    *)
(* ------------------------------------------------------------------------- *)

let DSEMAUX_l_rws = prove
 (`(!args sz (l:data_v spt) (s:(C,FFI)data_state).
      data_call_env args sz (data_state_locals_fupd (K l) s) = data_call_env args sz s) /\
   (!(l:data_v spt) (s:(C,FFI)data_state).
      data_dec_clock (data_state_locals_fupd (K l) s) =
      data_state_locals_fupd (K l) (data_dec_clock s)) /\
   (!env b (l:data_v spt) (s:(C,FFI)data_state).
      data_push_env env b (data_state_locals_fupd (K l) s) =
      data_state_locals_fupd (K l) (data_push_env env b s)) /\
   (!b (l:data_v spt) (s:(C,FFI)data_state).
      data_flush_state b (data_state_locals_fupd (K l) s) = data_flush_state b s) /\
   (!n v (l:data_v spt) (s:(C,FFI)data_state).
      data_set_var n v (data_state_locals_fupd (K l) s) =
      data_state_locals_fupd (K (insert n v l)) s) /\
   (!op (l:data_v spt) (s:(C,FFI)data_state).
      install_sfs op (data_state_locals_fupd (K l) s) =
      data_state_locals_fupd (K l) (install_sfs op s)) /\
   (!(l:data_v spt) (s:(C,FFI)data_state).
      data_jump_exc (data_state_locals_fupd (K l) s) = data_jump_exc s) /\
   (!e (l:data_v spt) (s:(C,FFI)data_state).
      data_state_locals_fupd (K e) (data_state_locals_fupd (K l) s) =
      data_state_locals_fupd (K e) s)`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  TRY (BOOL_CASES_TAC `b:bool`) THEN
  REWRITE_TAC[data_call_env_def; data_dec_clock_def; data_push_env_def; data_flush_state_def;
              data_set_var_def; install_sfs_def; LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM] THEN
  TRY (REWRITE_TAC[data_jump_exc_def; data_state_INFO.ri_accfupds; K_THM] THEN
       REPEAT (COND_CASES_TAC ORELSE TOP_CASE_TAC) THEN
       RULE_ASSUM_TAC(REWRITE_RULE[]) THEN TRY(FIRST_ASSUM CONTR_TAC) THEN
       REWRITE_TAC[option_INJ]) THEN
  REWRITE_TAC[data_state_component_equality; data_state_INFO.ri_accfupds; K_THM]);;

let DSEMAUX_l_cut_state_opt = prove
 (`!names_opt (s:(C,FFI)data_state) l s1.
     locals_ok (data_state_locals s) l /\ data_cut_state_opt names_opt s = SOME s1 ==>
     data_cut_state_opt names_opt (data_state_locals_fupd (K l) s) =
     SOME (data_state_locals_fupd
             (K (if names_opt = NONE then l else data_state_locals s1)) s1)`,
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `names_opt:num_set option` (cases "option")) THEN
  REWRITE_TAC[data_cut_state_opt_def; data_cut_state_def; option_DISTINCT] THEN
  CASE_REWRITE_TAC[] THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[option_INJ] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
    REFL_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM] THEN
  DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISJ_CASES_THEN2 (fun th -> REWRITE_TAC[th] THEN CASE_REWRITE_TAC[option_DISTINCT])
    (X_CHOOSE_THEN `env:data_v spt` (fun th -> ASSUME_TAC th THEN REWRITE_TAC[th]))
    (ISPEC `data_cut_env a (data_state_locals (s:(C,FFI)data_state))` (cases "option")) THEN
  CASE_REWRITE_TAC[option_INJ] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN `data_cut_env a (l:data_v spt) = SOME env` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_MESON_TAC[locals_ok_cut_env]; ALL_TAC] THEN
  CASE_REWRITE_TAC[option_INJ] THEN
  REWRITE_TAC[data_state_INFO.ri_fupdfupds; data_state_INFO.ri_accfupds; K_THM; DSEMAUX_K_o]);;

let DSEMAUX_L_GOAL =
 `!p (r:((data_v list,data_v)result)option) (s1:(C,FFI)data_state).
     data_evaluate p = (r,s1) ==> ~(r = SOME (Rerr (Rabort Rtype_error))) ==>
     !l smx sf pk. locals_ok (data_state_locals (SND p)) l ==>
       ?w safe peak sm.
         data_evaluate (FST p,DSEMAUX_ssp smx sf pk (data_state_locals_fupd (K l) (SND p))) =
         (r,if r = NONE then DSEMAUX_ssp sm safe peak (data_state_locals_fupd (K w) s1)
            else DSEMAUX_ssp sm safe peak s1) /\
         locals_ok (data_state_locals s1) w`;;

let DSEMAUX_ssp_l_do_app = prove
 (DSEMAUX_expand
  `!op vs smx sf pk z (s:(C,FFI)data_state).
     data_do_app op vs (DSEMAUX_ssp smx sf pk (data_state_locals_fupd (K z) s)) =
     map_result
       (\(x,y). (x,data_state_locals_fupd (K z)
                     (data_state_safe_for_space_fupd
                        (K (do_app_safe op vs
                              (data_state_locals_fupd (K z) (DSEMAUX_ssp smx sf pk s))))
                        (data_state_stack_max_fupd
                           (K (data_state_stack_max
                                 (do_stack op vs
                                    (data_state_locals_fupd (K z) (DSEMAUX_ssp smx sf pk s)))))
                           (data_state_peak_heap_length_fupd
                              (K (do_app_peak op vs
                                    (data_state_locals_fupd (K z) (DSEMAUX_ssp smx sf pk s))))
                              y)))))
       I (data_do_app op vs (DSEMAUX_ssp smx sf pk s))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM DSEMAUX_ssp_fupds] THEN REWRITE_TAC[do_app_with_locals]);;

let DSEMAUX_l_cut_state_opt2 = prove
 (`!names_opt (s:(C,FFI)data_state) l s1.
     locals_ok (data_state_locals s) l /\ data_cut_state_opt names_opt s = SOME s1 ==>
     locals_ok (data_state_locals s1) (if names_opt = NONE then l else data_state_locals s1)`,
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `names_opt:num_set option` (cases "option")) THEN
  REWRITE_TAC[data_cut_state_opt_def; option_DISTINCT; locals_ok_refl] THEN
  CASE_REWRITE_TAC[option_INJ] THEN MESON_TAC[]);;

let DSEMAUX_L_RWS =
  [DSEMAUX_ssp_acc; data_state_INFO.ri_accfupds; K_THM; DSEMAUX_l_rws;
   DSEMAUX_ssp_l_do_app; DSEMAUX_ssp_handler_fupd; map_error_result_I; I_THM;
   injectivity "result"; injectivity "error_result"] @ DSEMAUX_SSP_RWS;;

let DSEMAUX_L_LOOP_TAC : tactic =
  REPEAT (CHANGED_TAC (CASE_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
                       ASM_REWRITE_TAC (PAIR_EQ :: IS_SOME_DEF :: option_DISTINCT ::
                                        map_result_def :: DSEMAUX_L_RWS)) ORELSE
          DSEMAUX_SSP_DO_APP_RW_TAC ORELSE DSEMAUX_SSP_IH_TAC);;

(* witnesses: the fields of the final state of the run with the larger locals *)

let DSEMAUX_L_WIT_TAC : tactic = fun (asl,w as g) ->
  let vs,body = strip_exists w in
  if length vs <> 4 then failwith "DSEMAUX_L_WIT_TAC" else
  let eq,lok = dest_conj body in
  let l,r = dest_eq eq in
  let x = if is_pair l then snd (dest_pair l) else l in
  let locs1 = rand (rator lok) in
  let rr = if is_pair r then snd (dest_pair r) else r in
  let wv = hd vs in
  let loc = `data_state_locals:(C,FFI)data_state->data_v spt` in
  let wwit = if vfree_in wv rr then mk_comb(loc,x) else locs1 in
  MAP_EVERY EXISTS_TAC
    [wwit; mk_comb(`data_state_safe_for_space:(C,FFI)data_state->bool`,x);
     mk_comb(`data_state_peak_heap_length:(C,FFI)data_state->num`,x);
     mk_comb(`data_state_stack_max:(C,FFI)data_state->num option`,x)] g;;

(* split on R = NONE when the result R of the goal is not concrete *)

let DSEMAUX_L_RCASES_TAC : tactic = fun (asl,w as g) ->
  let vs,body = strip_exists w in
  let eq = fst (dest_conj body) in
  let r = rhs eq in
  let rr = if is_pair r then snd (dest_pair r) else r in
  if is_cond rr then
    let c,_ = dest_cond rr in
    (ASM_CASES_TAC c THEN POP_ASSUM (fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th)) g
  else ALL_TAC g;;

let DSEMAUX_L_ACC_RWS =
  [DSEMAUX_ssp_def; data_state_INFO.ri_accfupds; K_THM; data_set_var_def; data_set_vars_def;
   install_sfs_def; data_flush_state_def; data_dec_clock_def; data_call_env_def;
   LET_DEF; LET_END_DEF; DSEMAUX_push_env_acc];;

let DSEMAUX_L_FINISH_TAC : tactic =
  REWRITE_TAC[PAIR_EQ] THEN CONJ_TAC THENL
   [REWRITE_TAC (data_state_component_equality :: DSEMAUX_L_ACC_RWS) THEN
    IMP_RES_TAC data_do_app_const THEN ASM_REWRITE_TAC DSEMAUX_L_ACC_RWS;
    REWRITE_TAC DSEMAUX_L_ACC_RWS THEN
    IMP_RES_TAC data_do_app_const THEN ASM_REWRITE_TAC (locals_ok_refl :: DSEMAUX_L_ACC_RWS) THEN
    TRY (MATCH_MP_TAC locals_ok_insert) THEN ASM_REWRITE_TAC[locals_ok_refl]];;

(* IMP_RES_TAC keeping only the fully resolved facts *)

let DSEMAUX_FULL_RES_TAC (th:thm) : tactic =
  IMP_RES_THEN (fun th -> if is_imp (snd (strip_forall (concl th))) then ALL_TAC
                          else STRIP_ASSUME_TAC th) th;;

let DSEMAUX_L_LEAF_TAC : tactic =
  REPEAT GEN_TAC THEN
  (fun (asl,w as g) ->
     let a,_ = dest_imp w in
     if DSEMAUX_is_main_hyp a then ALL_TAC g
     else (DISCH_THEN STRIP_ASSUME_TAC THEN REPEAT GEN_TAC) g) THEN
  DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE DSEMAUX_EVAL_CASE_EQS o
             ONCE_REWRITE_RULE[data_evaluate_def]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN DSEMAUX_SPLIT_CONJ_ASMS THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IS_SOME_DEF]) THEN
  REWRITE_TAC[] THEN DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  MAP_EVERY DSEMAUX_FULL_RES_TAC
    [locals_ok_get_var; locals_ok_get_vars; locals_ok_cut_env; DSEMAUX_l_cut_state_opt;
     DSEMAUX_l_cut_state_opt2] THEN
  IMP_RES_TAC DSEMAUX_evaluate_ssp THEN RULE_ASSUM_TAC (REWRITE_RULE[FST; SND]) THEN
  ONCE_REWRITE_TAC[data_evaluate_def] THEN
  REWRITE_TAC DSEMAUX_L_RWS THEN DSEMAUX_L_LOOP_TAC THEN
  DSEMAUX_L_RCASES_TAC THEN DSEMAUX_L_WIT_TAC THEN DSEMAUX_L_FINISH_TAC;;

let DSEMAUX_NONE_NOT_TYERR = prove
 (`~((NONE:((data_v list,data_v)result)option) = SOME (Rerr (Rabort Rtype_error)))`,
  REWRITE_TAC[option_DISTINCT]);;

let DSEMAUX_L_SEQ_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE DSEMAUX_EVAL_CASE_EQS o
             ONCE_REWRITE_RULE[data_evaluate_def]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN DSEMAUX_SPLIT_CONJ_ASMS THEN RVEQ_TAC THEN
  DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THENL
   [(* c1 returns NONE, then c2 *)
    USE_THEN "ih1" (fun ih -> MP_TAC (MP (SPECL [`l:data_v spt`; `smx:num option`; `sf:bool`;
                                                 `pk:num`]
       (MP (MATCH_MP ih (ASSUME `data_evaluate (c1,s:(C,FFI)data_state) = NONE,y`))
           DSEMAUX_NONE_NOT_TYERR))
       (ASSUME `locals_ok (data_state_locals (s:(C,FFI)data_state)) l`))) THEN
    REWRITE_TAC[] THEN
    DISCH_THEN (X_CHOOSE_THEN `w1:data_v spt` (X_CHOOSE_THEN `safe1:bool`
      (X_CHOOSE_THEN `peak1:num` (X_CHOOSE_THEN `sm1:num option` STRIP_ASSUME_TAC)))) THEN
    FIRST_ASSUM (fun th -> REWRITE_TAC[MATCH_MP DSEMAUX_Seq_NONE th]) THEN
    USE_THEN "ih2" (fun ih -> ACCEPT_TAC (MP (SPECL [`w1:data_v spt`; `sm1:num option`;
                                                     `safe1:bool`; `peak1:num`]
      (MP (MATCH_MP (MATCH_MP ih (ASSUME `data_evaluate (c1,s:(C,FFI)data_state) = NONE,y`))
                    (ASSUME `data_evaluate (c2,y:(C,FFI)data_state) = r,s1`))
          (ASSUME `~((r:((data_v list,data_v)result)option) = SOME (Rerr (Rabort Rtype_error)))`)))
      (ASSUME `locals_ok (data_state_locals (y:(C,FFI)data_state)) w1`)));
    (* c1 returns something else *)
    USE_THEN "ih1" (fun ih -> MP_TAC (MP (SPECL [`l:data_v spt`; `smx:num option`; `sf:bool`;
                                                 `pk:num`]
       (MP (MATCH_MP ih (ASSUME `data_evaluate (c1,s:(C,FFI)data_state) = r,s1`))
           (ASSUME `~((r:((data_v list,data_v)result)option) = SOME (Rerr (Rabort Rtype_error)))`)))
       (ASSUME `locals_ok (data_state_locals (s:(C,FFI)data_state)) l`))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN (X_CHOOSE_THEN `w1:data_v spt` (X_CHOOSE_THEN `safe1:bool`
      (X_CHOOSE_THEN `peak1:num` (X_CHOOSE_THEN `sm1:num option` STRIP_ASSUME_TAC)))) THEN
    MP_TAC (SPECL [`c1:data_prog`; `c2:data_prog`;
                   `DSEMAUX_ssp smx sf pk (data_state_locals_fupd (K l) (s:(C,FFI)data_state))`;
                   `r:((data_v list,data_v)result)option`;
                   `DSEMAUX_ssp sm1 safe1 peak1 (s1:(C,FFI)data_state)`] DSEMAUX_Seq_not_NONE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MAP_EVERY EXISTS_TAC [`w1:data_v spt`; `safe1:bool`; `peak1:num`; `sm1:num option`] THEN
    ASM_REWRITE_TAC[]];;

let DSEMAUX_L_IF_TAC : tactic =
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE DSEMAUX_EVAL_CASE_EQS o
             ONCE_REWRITE_RULE[data_evaluate_def]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN DSEMAUX_SPLIT_CONJ_ASMS THEN RVEQ_TAC THEN
  REWRITE_TAC[] THEN DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  DSEMAUX_FULL_RES_TAC locals_ok_get_var THEN
  ONCE_REWRITE_TAC[data_evaluate_def] THEN
  ASM_REWRITE_TAC[DSEMAUX_ssp_acc; data_state_INFO.ri_accfupds; K_THM] THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[option_INJ; IMP_CONJ; RIGHT_FORALL_IMP_THM;
                              FORALL_UNWIND_THM1]) THEN
  REPEAT DSEMAUX_RES_TAC THEN
  FIRST_ASSUM (fun th -> ACCEPT_TAC (SPECL [`smx:num option`; `sf:bool`; `pk:num`] th));;

let DSEMAUX_evaluate_l = prove
 (DSEMAUX_L_GOAL,
  MATCH_MP_TAC data_evaluate_ind THEN REWRITE_TAC[FST; SND] THEN REPEAT CONJ_TAC THENL
   [DSEMAUX_L_LEAF_TAC; DSEMAUX_L_LEAF_TAC; DSEMAUX_L_LEAF_TAC; DSEMAUX_L_LEAF_TAC;
    DSEMAUX_L_LEAF_TAC; DSEMAUX_L_LEAF_TAC; DSEMAUX_L_LEAF_TAC; DSEMAUX_L_SEQ_TAC;
    DSEMAUX_L_IF_TAC; DSEMAUX_L_LEAF_TAC; DSEMAUX_L_LEAF_TAC]);;

let evaluate_locals = prove
 (`!c (s:(C,FFI)data_state) res s2 l.
     ~(res = SOME (Rerr (Rabort Rtype_error))) /\ data_evaluate (c,s) = (res,s2) /\
     locals_ok (data_state_locals s) l ==>
     ?w safe peak sm.
       data_evaluate (c,data_state_locals_fupd (K l) s) =
       (res,if res = NONE
            then data_state_locals_fupd (K w)
                   (data_state_safe_for_space_fupd (K safe)
                      (data_state_stack_max_fupd (K sm)
                         (data_state_peak_heap_length_fupd (K peak) s2)))
            else data_state_safe_for_space_fupd (K safe)
                   (data_state_stack_max_fupd (K sm)
                      (data_state_peak_heap_length_fupd (K peak) s2))) /\
       locals_ok (data_state_locals s2) w`,
  REPEAT STRIP_TAC THEN
  MP_TAC (ISPECL [`(c:data_prog,s:(C,FFI)data_state)`;
                  `res:((data_v list,data_v)result)option`; `s2:(C,FFI)data_state`]
                 DSEMAUX_evaluate_l) THEN
  ASM_REWRITE_TAC[FST; SND] THEN
  DISCH_THEN (MP_TAC o SPECL [`l:data_v spt`; `data_state_stack_max (s:(C,FFI)data_state)`;
                              `data_state_safe_for_space (s:(C,FFI)data_state)`;
                              `data_state_peak_heap_length (s:(C,FFI)data_state)`]) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `DSEMAUX_ssp (data_state_stack_max s) (data_state_safe_for_space s)
                  (data_state_peak_heap_length s) (data_state_locals_fupd (K l) s) =
                data_state_locals_fupd (K l) (s:(C,FFI)data_state)` SUBST1_TAC THENL
   [REWRITE_TAC[DSEMAUX_ssp_def; data_state_component_equality; data_state_INFO.ri_accfupds;
                K_THM];
    ALL_TAC] THEN
  REWRITE_TAC[DSEMAUX_ssp_def; data_state_INFO.ri_fupdcanon]);;

let funpow_dec_clock_clock = prove
 (`!n (s:(C,FFI)data_state).
     ITER n data_dec_clock s = data_state_clock_fupd (K (data_state_clock s - n)) s`,
  INDUCT_TAC THEN REWRITE_TAC[ITER] THENL
   [REWRITE_TAC[SUB_0; DSEMAUX_fupd_id];
    ASM_REWRITE_TAC[data_dec_clock_def; data_state_INFO.ri_accfupds;
                    data_state_INFO.ri_fupdfupds; K_THM; DSEMAUX_K_o] THEN
    REWRITE_TAC[ARITH_RULE `x - n - 1 = x - SUC n`]]);;

let DSEMAUX_fromList_NIL = prove
 (`fromList ([]:A list) = LN`,
  REWRITE_TAC[fromList_def; FOLDL]);;

let evaluate_mk_ticks = prove
 (`!p (s:(C,FFI)data_state) n.
     data_evaluate (mk_ticks n p,s) =
     if data_state_clock s < n then
       (SOME (Rerr (Rabort Rtimeout_error)),
        data_state_clock_fupd (K 0)
          (data_state_locals_fupd (K (fromList []))
             (data_state_stack_fupd (K [])
                (data_state_locals_size_fupd (K (SOME 0)) s))))
     else data_evaluate (p,ITER n data_dec_clock s)`,
  SUBGOAL_THEN
   `!n p (s:(C,FFI)data_state).
     data_evaluate (mk_ticks n p,s) =
     if data_state_clock s < n then
       (SOME (Rerr (Rabort Rtimeout_error)),
        data_state_clock_fupd (K 0)
          (data_state_locals_fupd (K (fromList []))
             (data_state_stack_fupd (K [])
                (data_state_locals_size_fupd (K (SOME 0)) s))))
     else data_evaluate (p,ITER n data_dec_clock s)` (fun th -> REWRITE_TAC[th]) THEN
  INDUCT_TAC THEN REWRITE_TAC[mk_ticks_def; ITER_ALT; CONJUNCT1 LT] THEN
  REWRITE_TAC[GSYM mk_ticks_def] THEN ASM_REWRITE_TAC[funpow_dec_clock_clock] THEN
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `data_state_clock (s:(C,FFI)data_state) < n` THENL
   [ASM_SIMP_TAC[ARITH_RULE `x < n ==> x < SUC n`]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[data_evaluate_def] THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  ONCE_REWRITE_TAC[data_evaluate_def] THEN
  REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM] THEN
  ASM_CASES_TAC `data_state_clock (s:(C,FFI)data_state) = n` THENL
   [ASM_REWRITE_TAC[SUB_REFL; ARITH_RULE `n < SUC n`] THEN
    CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
    REWRITE_TAC[option_DISTINCT] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[PAIR_EQ; data_flush_state_def; DSEMAUX_fromList_NIL;
                data_state_component_equality; data_state_INFO.ri_accfupds; K_THM] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(data_state_clock (s:(C,FFI)data_state) - n = 0) /\ ~(data_state_clock s < SUC n)` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[data_dec_clock_def; data_state_INFO.ri_accfupds; data_state_INFO.ri_fupdfupds;
              K_THM; DSEMAUX_K_o; ARITH_RULE `x - n - 1 = x - SUC n`;
              ARITH_RULE `x - 1 - n = x - SUC n`]);;

let FUNPOW_dec_clock_code = prove
 (`!n (t:(C,FFI)data_state).
     data_state_code (ITER n data_dec_clock t) = data_state_code t /\
     data_state_stack (ITER n data_dec_clock t) = data_state_stack t /\
     data_state_handler (ITER n data_dec_clock t) = data_state_handler t /\
     data_state_refs (ITER n data_dec_clock t) = data_state_refs t /\
     data_state_ffi (ITER n data_dec_clock t) = data_state_ffi t /\
     data_state_safe_for_space (ITER n data_dec_clock t) = data_state_safe_for_space t /\
     data_state_global (ITER n data_dec_clock t) = data_state_global t /\
     data_state_locals (ITER n data_dec_clock t) = data_state_locals t /\
     data_state_compile (ITER n data_dec_clock t) = data_state_compile t /\
     data_state_compile_oracle (ITER n data_dec_clock t) = data_state_compile_oracle t /\
     data_state_peak_heap_length (ITER n data_dec_clock t) = data_state_peak_heap_length t /\
     data_state_stack_frame_sizes (ITER n data_dec_clock t) = data_state_stack_frame_sizes t /\
     data_state_locals_size (ITER n data_dec_clock t) = data_state_locals_size t /\
     data_state_clock (ITER n data_dec_clock t) = data_state_clock t - n`,
  REWRITE_TAC[funpow_dec_clock_clock; data_state_INFO.ri_accfupds; K_THM]);;
let _ = cake_add_simps [FUNPOW_dec_clock_code];;

let jump_exc_NONE = prove
 (`!(t:(C,FFI)data_state) x c sm ls safe.
     (data_jump_exc (data_state_locals_fupd (K x) t) = NONE <=> data_jump_exc t = NONE) /\
     (data_jump_exc (data_state_clock_fupd (K c) t) = NONE <=> data_jump_exc t = NONE) /\
     (data_jump_exc (data_state_stack_max_fupd (K sm) t) = NONE <=> data_jump_exc t = NONE) /\
     (data_jump_exc (data_state_locals_size_fupd (K ls) t) = NONE <=>
      data_jump_exc t = NONE) /\
     (data_jump_exc (data_state_safe_for_space_fupd (K safe) t) = NONE <=>
      data_jump_exc t = NONE)`,
  REPEAT GEN_TAC THEN REPEAT CONJ_TAC THEN
  W(fun (_,w) -> MP_TAC (SPECL [`t:(C,FFI)data_state`; rand(lhs(lhs w))]
                                DSEMAUX_jump_exc_cong)) THEN
  REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[OPTION_MAP_EQ_NONE]);;

let jump_exc_IMP = prove
 (`!(s:(C,FFI)data_state) t.
     data_jump_exc s = SOME t ==>
     data_state_handler s < LENGTH (data_state_stack s) /\
     ?n e ls xs. LASTN (data_state_handler s + 1) (data_state_stack s) = CONS (Exc ls e n) xs /\
                 t = data_state_handler_fupd (K n)
                       (data_state_locals_size_fupd (K ls)
                          (data_state_locals_fupd (K e)
                             (data_state_stack_fupd (K xs) s)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_jump_exc_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
  REPEAT TOP_CASE_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN (SUBST1_TAC o SYM) THEN
  MAP_EVERY EXISTS_TAC [`a2:num`; `a1':data_v spt`; `a0':num option`; `a1:stack list`] THEN
  REWRITE_TAC[data_state_component_equality; data_state_INFO.ri_accfupds; K_THM]);;

let do_app_Rerr = prove
 (`!op vs (s:(C,FFI)data_state) e.
     data_do_app op vs s = Rerr e ==>
     e = Rabort Rtype_error \/ (?i x. op = clos_FFI i /\ e = Rabort (Rffi_error x))`,
  REWRITE_TAC[data_do_app_err]);;

let size_of_heap_with_clock = prove
 (`!(s:(C,FFI)data_state) z. size_of_heap (data_state_clock_fupd (K z) s) = size_of_heap s`,
  REWRITE_TAC[size_of_heap_def; stack_to_vs_def; data_state_INFO.ri_accfupds; K_THM]);;

let size_of_heap_args_with_clock = prove
 (`!(s:(C,FFI)data_state) z a.
     size_of_heap_args a (data_state_clock_fupd (K z) s) = size_of_heap_args a s`,
  REWRITE_TAC[size_of_heap_args_def; stack_to_vs_def; data_state_INFO.ri_accfupds; K_THM]);;

let space_consumed_with_clock = prove
 (`!(s:(C,FFI)data_state) op vs z.
     space_consumed (data_state_clock_fupd (K z) s) op vs = space_consumed s op vs`,
  MATCH_MP_TAC space_consumed_ind THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[space_consumed_def; data_state_INFO.ri_accfupds; K_THM]);;

(*fs[] is slower than full_simp_tac(srw_ss())[]*)
let do_app_with_clock = prove
 (`!op vs (s:(C,FFI)data_state) z.
     data_do_app op vs (data_state_clock_fupd (K z) s) =
     map_result (\(x,y). (x,data_state_clock_fupd (K z) y)) I (data_do_app op vs s)`,
  DSEMAUX_DO_APP_TAC (DSEMAUX_DO_APP_DEFS @
                      [size_of_heap_with_clock; size_of_heap_args_with_clock;
                       space_consumed_with_clock]));;

let data_do_app_change_clock = prove
 (`!op args (s1:(C,FFI)data_state) res s2 ck.
     data_do_app op args s1 = Rval (res,s2) ==>
     data_do_app op args (data_state_clock_fupd (K ck) s1) =
     Rval (res,data_state_clock_fupd (K ck) s2)`,
  SIMP_TAC[do_app_with_clock; map_result_def] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[]);;

let data_do_app_change_clock_err = prove
 (`!op args (s1:(C,FFI)data_state) e ck.
     data_do_app op args s1 = Rerr e ==>
     data_do_app op args (data_state_clock_fupd (K ck) s1) = Rerr e`,
  SIMP_TAC[do_app_with_clock; map_result_def; map_error_result_I; I_THM]);;

let cut_state_eq_some = prove
 (`!names (s:(C,FFI)data_state) y.
     data_cut_state names s = SOME y <=>
     ?z. data_cut_env names (data_state_locals s) = SOME z /\
         y = data_state_locals_fupd (K z) s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_cut_state_def] THEN
  DISJ_CASES_THEN2 (fun th -> REWRITE_TAC[th] THEN CASE_REWRITE_TAC[option_DISTINCT])
    (X_CHOOSE_THEN `env:data_v spt` (fun th -> REWRITE_TAC[th]))
    (ISPEC `data_cut_env names (data_state_locals (s:(C,FFI)data_state))` (cases "option")) THEN
  CASE_REWRITE_TAC[option_INJ] THEN MESON_TAC[]);;

let data_set_var_const = prove
 (`!x y (z:(C,FFI)data_state).
     data_state_ffi (data_set_var x y z) = data_state_ffi z /\
     data_state_clock (data_set_var x y z) = data_state_clock z`,
  REWRITE_TAC[data_set_var_def; data_state_INFO.ri_accfupds; K_THM]);;
let _ = cake_add_simps [data_set_var_const];;

let data_set_var_with_const = prove
 (`!x y (z:(C,FFI)data_state) k.
     data_set_var x y (data_state_clock_fupd (K k) z) =
     data_state_clock_fupd (K k) (data_set_var x y z)`,
  REWRITE_TAC[data_set_var_def; data_state_component_equality; data_state_INFO.ri_accfupds;
              K_THM]);;

let data_set_vars_const = prove
 (`!xs ys (z:(C,FFI)data_state).
     data_state_ffi (data_set_vars xs ys z) = data_state_ffi z /\
     data_state_clock (data_set_vars xs ys z) = data_state_clock z`,
  REWRITE_TAC[data_set_vars_def; data_state_INFO.ri_accfupds; K_THM]);;
let _ = cake_add_simps [data_set_vars_const];;

let data_set_vars_with_const = prove
 (`!xs ys (z:(C,FFI)data_state) k.
     data_set_vars xs ys (data_state_clock_fupd (K k) z) =
     data_state_clock_fupd (K k) (data_set_vars xs ys z)`,
  REWRITE_TAC[data_set_vars_def; data_state_component_equality; data_state_INFO.ri_accfupds;
              K_THM]);;
let _ = cake_add_simps [data_set_vars_with_const];;

let data_call_env_const = prove
 (`!x s (y:(C,FFI)data_state).
     data_state_ffi (data_call_env x s y) = data_state_ffi y /\
     data_state_clock (data_call_env x s y) = data_state_clock y`,
  REWRITE_TAC[data_call_env_def; LET_DEF; LET_END_DEF; data_state_INFO.ri_accfupds; K_THM]);;
let _ = cake_add_simps [data_call_env_const];;

let data_call_env_with_const = prove
 (`!x s (y:(C,FFI)data_state) z.
     data_call_env x s (data_state_clock_fupd (K z) y) =
     data_state_clock_fupd (K z) (data_call_env x s y)`,
  REWRITE_TAC[data_call_env_def; LET_DEF; LET_END_DEF; data_state_component_equality;
              data_state_INFO.ri_accfupds; K_THM]);;

let data_push_env_const = prove
 (`!x y (z:(C,FFI)data_state).
     data_state_ffi (data_push_env x y z) = data_state_ffi z /\
     data_state_clock (data_push_env x y z) = data_state_clock z /\
     data_state_code (data_push_env x y z) = data_state_code z /\
     data_state_compile_oracle (data_push_env x y z) = data_state_compile_oracle z /\
     data_state_compile (data_push_env x y z) = data_state_compile z /\
     data_state_refs (data_push_env x y z) = data_state_refs z /\
     data_state_global (data_push_env x y z) = data_state_global z`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `y:bool` THEN
  REWRITE_TAC[data_push_env_def; LET_DEF; LET_END_DEF; data_state_INFO.ri_accfupds; K_THM]);;
let _ = cake_add_simps [data_push_env_const];;

let data_push_env_with_const = prove
 (`!x y (z:(C,FFI)data_state) k.
     data_push_env x y (data_state_clock_fupd (K k) z) =
     data_state_clock_fupd (K k) (data_push_env x y z)`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `y:bool` THEN
  REWRITE_TAC[data_push_env_def; LET_DEF; LET_END_DEF; data_state_component_equality;
              data_state_INFO.ri_accfupds; K_THM]);;

let data_pop_env_with_const = prove
 (`!(z:(C,FFI)data_state) k.
     data_pop_env (data_state_clock_fupd (K k) z) =
     OPTION_MAP (\z. data_state_clock_fupd (K k) z) (data_pop_env z)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_pop_env_def; data_state_INFO.ri_accfupds; K_THM] THEN
  REPEAT TOP_CASE_TAC THEN REWRITE_TAC[OPTION_MAP_DEF; option_INJ] THEN
  REWRITE_TAC[data_state_component_equality; data_state_INFO.ri_accfupds; K_THM]);;

let data_pop_env_const = prove
 (`!(a:(C,FFI)data_state) b.
     data_pop_env a = SOME b ==>
     data_state_ffi b = data_state_ffi a /\
     data_state_clock b = data_state_clock a /\
     data_state_stack_max b = data_state_stack_max a`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_pop_env_def] THEN
  REPEAT TOP_CASE_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN (SUBST1_TAC o SYM) THEN REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM]);;

let cut_state_eq_none = prove
 (`!names (s:(C,FFI)data_state).
     data_cut_state names s = NONE <=> data_cut_env names (data_state_locals s) = NONE`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_cut_state_def] THEN
  DISJ_CASES_THEN2 (fun th -> REWRITE_TAC[th] THEN CASE_REWRITE_TAC[])
    (X_CHOOSE_THEN `env:data_v spt` (fun th -> REWRITE_TAC[th]))
    (ISPEC `data_cut_env names (data_state_locals (s:(C,FFI)data_state))` (cases "option")) THEN
  CASE_REWRITE_TAC[option_DISTINCT]);;

let data_with_same_clock = prove
 (`!s:(C,FFI)data_state. data_state_clock_fupd (K (data_state_clock s)) s = s`,
  REWRITE_TAC[DSEMAUX_fupd_id]);;
let _ = cake_add_simps [data_with_same_clock];;

(* ------------------------------------------------------------------------- *)
(* data_evaluate_add_clock: DSEMAUX_ck k s is s with clock := s.clock + k         *)
(* ------------------------------------------------------------------------- *)

let DSEMAUX_ck_def = new_definition
  `DSEMAUX_ck k (s:(C,FFI)data_state) =
     data_state_clock_fupd (K (data_state_clock s + k)) s`;;

let DSEMAUX_ck_tac : tactic =
  REWRITE_TAC[DSEMAUX_ck_def; data_state_component_equality; data_state_INFO.ri_accfupds;
              K_THM];;

let DSEMAUX_ck_acc =
  let names = map (fun (f,_,_) -> f) data_state_INFO.ri_fields in
  let names = filter (fun f -> f <> "clock") names in
  let cl f = "data_state_" ^ f ^ " (DSEMAUX_ck k s) = data_state_" ^ f ^ " s" in
  let tm = parse_term ("!k (s:(C,FFI)data_state). " ^
             String.concat " /\\ " (map cl names) ^
             " /\\ data_state_clock (DSEMAUX_ck k s) = data_state_clock s + k") in
  prove(tm, REWRITE_TAC[DSEMAUX_ck_def; data_state_INFO.ri_accfupds; K_THM]);;

let DSEMAUX_ck_rws = prove
 (`(!n v k (s:(C,FFI)data_state).
      data_set_var n v (DSEMAUX_ck k s) = DSEMAUX_ck k (data_set_var n v s)) /\
   (!ns vs k (s:(C,FFI)data_state).
      data_set_vars ns vs (DSEMAUX_ck k s) = DSEMAUX_ck k (data_set_vars ns vs s)) /\
   (!b k (s:(C,FFI)data_state).
      data_flush_state b (DSEMAUX_ck k s) = DSEMAUX_ck k (data_flush_state b s)) /\
   (!op k (s:(C,FFI)data_state).
      install_sfs op (DSEMAUX_ck k s) = DSEMAUX_ck k (install_sfs op s)) /\
   (!args sz k (s:(C,FFI)data_state).
      data_call_env args sz (DSEMAUX_ck k s) = DSEMAUX_ck k (data_call_env args sz s)) /\
   (!env b k (s:(C,FFI)data_state).
      data_push_env env b (DSEMAUX_ck k s) = DSEMAUX_ck k (data_push_env env b s)) /\
   (!e k (s:(C,FFI)data_state).
      data_state_locals_fupd (K e) (DSEMAUX_ck k s) =
      DSEMAUX_ck k (data_state_locals_fupd (K e) s)) /\
   (!x k (s:(C,FFI)data_state).
      data_state_stack_fupd (K x) (DSEMAUX_ck k s) =
      DSEMAUX_ck k (data_state_stack_fupd (K x) s)) /\
   (!x k (s:(C,FFI)data_state).
      data_state_locals_size_fupd (K x) (DSEMAUX_ck k s) =
      DSEMAUX_ck k (data_state_locals_size_fupd (K x) s)) /\
   (!k n (s:(C,FFI)data_state).
      add_space (DSEMAUX_ck k s) n = DSEMAUX_ck k (add_space s n))`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN TRY (BOOL_CASES_TAC `b:bool`) THEN
  REWRITE_TAC[data_set_var_def; data_set_vars_def; data_flush_state_def; install_sfs_def;
              data_call_env_def; data_push_env_def; add_space_def; LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[DSEMAUX_ck_acc; size_of_heap_with_clock;
              GSYM DSEMAUX_ck_def; data_state_INFO.ri_accfupds; K_THM] THEN
  REWRITE_TAC[DSEMAUX_ck_def; size_of_heap_with_clock; data_state_component_equality;
              data_state_INFO.ri_accfupds; K_THM]);;

let DSEMAUX_ck_dec_clock = prove
 (`!k (s:(C,FFI)data_state).
     ~(data_state_clock s = 0) ==>
     data_dec_clock (DSEMAUX_ck k s) = DSEMAUX_ck k (data_dec_clock s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[data_dec_clock_def] THEN DSEMAUX_ck_tac THEN
  ASM_ARITH_TAC);;

let DSEMAUX_ck_opt = prove
 (`(!k (s:(C,FFI)data_state).
      data_pop_env (DSEMAUX_ck k s) = OPTION_MAP (DSEMAUX_ck k) (data_pop_env s)) /\
   (!k (s:(C,FFI)data_state).
      data_jump_exc (DSEMAUX_ck k s) = OPTION_MAP (DSEMAUX_ck k) (data_jump_exc s)) /\
   (!names k (s:(C,FFI)data_state).
      data_cut_state_opt names (DSEMAUX_ck k s) =
      OPTION_MAP (DSEMAUX_ck k) (data_cut_state_opt names s))`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[data_pop_env_def; data_jump_exc_def; data_cut_state_opt_def;
              data_cut_state_def; DSEMAUX_ck_acc] THEN
  REPEAT (COND_CASES_TAC ORELSE TOP_CASE_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN TRY(FIRST_ASSUM CONTR_TAC) THEN
  REWRITE_TAC[OPTION_MAP_DEF; option_INJ] THEN DSEMAUX_ck_tac);;

let DSEMAUX_ck_do_app = prove
 (`!op vs k (s:(C,FFI)data_state).
     data_do_app op vs (DSEMAUX_ck k s) =
     map_result (\(x,y). (x,DSEMAUX_ck k y)) I (data_do_app op vs s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[DSEMAUX_ck_def; do_app_with_clock] THEN
  MP_TAC (ISPECL [`op:clos_op`; `vs:data_v list`; `s:(C,FFI)data_state`] data_do_app_const) THEN
  STRUCT_CASES_TAC (ISPEC `data_do_app op vs (s:(C,FFI)data_state)` (cases "result")) THEN
  REWRITE_TAC[map_result_def; injectivity "result"; distinctness "result"] THEN
  STRUCT_CASES_TAC (ISPEC `a:data_v#(C,FFI)data_state` PAIR_SURJECTIVE) THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[injectivity "result"; PAIR_EQ] THEN MESON_TAC[]);;

let DSEMAUX_CK_RWS =
  [DSEMAUX_ck_acc; DSEMAUX_ck_rws; DSEMAUX_ck_opt; DSEMAUX_ck_do_app; OPTION_MAP_DEF;
   map_result_def; map_error_result_I; I_THM; ADD_EQ_0];;

let DSEMAUX_CK_DEC_TAC : tactic =
  FIRST_ASSUM (fun th -> CHANGED_TAC (REWRITE_TAC[MATCH_MP DSEMAUX_ck_dec_clock th]));;

let DSEMAUX_CK_SIMP_RWS =
  [option_INJ; option_DISTINCT; injectivity "result"; distinctness "result";
   injectivity "error_result"; distinctness "error_result"; injectivity "abort";
   distinctness "abort"; IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_UNWIND_THM1;
   FORALL_UNWIND_THM2; PAIR_EQ];;

let DSEMAUX_CK_SIMP_ASMS : tactic =
  RULE_ASSUM_TAC (REWRITE_RULE DSEMAUX_CK_SIMP_RWS);;

(* DSEMAUX_RES_TAC with the resolvents simplified by DSEMAUX_CK_SIMP_RWS *)

let DSEMAUX_CK_RES_TAC : tactic = fun (asl,w) ->
  let ths = map snd asl in
  let imps = filter (fun th -> let _,b = strip_forall (concl th) in is_imp b) ths in
  let simp = REWRITE_RULE DSEMAUX_CK_SIMP_RWS in
  let new_ths = flat (map (fun ith -> mapfilter (fun th -> simp (MATCH_MP ith th)) ths)
                          imps) in
  let new_ths = filter (fun th -> not (exists (fun t -> aconv (concl t) (concl th)) ths) &&
                                  not (concl th = `T`)) new_ths in
  let rec nub l = match l with [] -> [] | h::t ->
    h :: nub (filter (fun x -> not (aconv (concl x) (concl h))) t) in
  let new_ths = nub new_ths in
  if new_ths = [] then failwith "DSEMAUX_CK_RES_TAC" else MAP_EVERY ASSUME_TAC new_ths (asl,w);;

let DSEMAUX_CK_CLAUSE_TAC : tactic =
  REPEAT GEN_TAC THEN
  (fun (asl,w as g) ->
     let a,_ = dest_imp w in
     if DSEMAUX_is_main_hyp a then ALL_TAC g
     else (DISCH_THEN STRIP_ASSUME_TAC THEN REPEAT GEN_TAC) g) THEN
  DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE DSEMAUX_EVAL_CASE_EQS o
             ONCE_REWRITE_RULE[data_evaluate_def]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN DSEMAUX_SPLIT_CONJ_ASMS THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IS_SOME_DEF]) THEN
  REWRITE_TAC[] THEN DISCH_TAC THEN GEN_TAC THEN
  DSEMAUX_CK_SIMP_ASMS THEN REPEAT DSEMAUX_CK_RES_TAC THEN
  ONCE_REWRITE_TAC[data_evaluate_def] THEN
  REWRITE_TAC DSEMAUX_CK_RWS THEN
  REPEAT (CHANGED_TAC (CASE_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
                       ASM_REWRITE_TAC (PAIR_EQ :: IS_SOME_DEF :: DSEMAUX_CK_RWS)) ORELSE
          DSEMAUX_CK_DEC_TAC);;

let DSEMAUX_CK_GOAL =
 `!p (r:((data_v list,data_v)result)option) (s2:(C,FFI)data_state).
     data_evaluate p = (r,s2) ==> ~(r = SOME (Rerr (Rabort Rtimeout_error))) ==>
     !k. data_evaluate (FST p,DSEMAUX_ck k (SND p)) = (r,DSEMAUX_ck k s2)`;;
let DSEMAUX_CK_GOAL =
 `!p (r:((data_v list,data_v)result)option) (s2:(C,FFI)data_state).
     data_evaluate p = (r,s2) ==> ~(r = SOME (Rerr (Rabort Rtimeout_error))) ==>
     !k. data_evaluate (FST p,DSEMAUX_ck k (SND p)) = (r,DSEMAUX_ck k s2)`;;

let DSEMAUX_evaluate_ck = prove
 (DSEMAUX_CK_GOAL,
  MATCH_MP_TAC data_evaluate_ind THEN REWRITE_TAC[FST; SND] THEN REPEAT CONJ_TAC THEN
  DSEMAUX_CK_CLAUSE_TAC);;

let data_evaluate_add_clock = prove
 (`!exps (s1:(C,FFI)data_state) res s2.
     data_evaluate (exps,s1) = (res,s2) /\ ~(res = SOME (Rerr (Rabort Rtimeout_error))) ==>
     !ck. data_evaluate (exps,data_state_clock_fupd (K (data_state_clock s1 + ck)) s1) =
          (res,data_state_clock_fupd (K (data_state_clock s2 + ck)) s2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC (ISPECL [`(exps:data_prog,s1:(C,FFI)data_state)`;
                  `res:((data_v list,data_v)result)option`; `s2:(C,FFI)data_state`]
                 DSEMAUX_evaluate_ck) THEN
  ASM_REWRITE_TAC[FST; SND; DSEMAUX_ck_def] THEN DISCH_THEN (ACCEPT_TAC o SPEC `ck:num`));;

let cut_state_opt_const = prove
 (`!x (y:(C,FFI)data_state) z.
     data_cut_state_opt x y = SOME z ==>
     data_state_ffi z = data_state_ffi y /\ data_state_global z = data_state_global y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_cut_state_opt_def; data_cut_state_def] THEN
  REPEAT TOP_CASE_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN (SUBST1_TAC o SYM) THEN REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM]);;

let data_do_app_io_events_mono = prove
 (`!x y (z:(C,FFI)data_state) a b.
     data_do_app x y z = Rval (a,b) ==>
     ffi_state_io_events (data_state_ffi z) <<= ffi_state_io_events (data_state_ffi b)`,
  X_GEN_TAC `x:clos_op` THEN DSEMAUX_OP_CASES_TAC `x:clos_op` THEN
  REPEAT GEN_TAC THEN CASE_REWRITE_TAC DSEMAUX_DO_APP_DEFS THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  CASE_REWRITE_TAC DSEMAUX_DO_APP_RWS THEN
  REPEAT ((COND_CASES_TAC ORELSE TOP_CASE_TAC) THEN CASE_REWRITE_TAC DSEMAUX_DO_APP_RWS) THEN
  REWRITE_TAC[injectivity "result"; distinctness "result"; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  ASM_REWRITE_TAC(IS_PREFIX_REFL :: DSEMAUX_FINISH_RWS) THEN
  TRY (FIRST_ASSUM (MATCH_ACCEPT_TAC o MATCH_MP SEM2AUX_call_FFI_io_events)));;

let data_dec_clock_const = prove
 (`!s:(C,FFI)data_state.
     data_state_ffi (data_dec_clock s) = data_state_ffi s /\
     data_state_code (data_dec_clock s) = data_state_code s /\
     data_state_compile_oracle (data_dec_clock s) = data_state_compile_oracle s /\
     data_state_compile (data_dec_clock s) = data_state_compile s /\
     data_state_refs (data_dec_clock s) = data_state_refs s /\
     data_state_global (data_dec_clock s) = data_state_global s`,
  REWRITE_TAC[data_dec_clock_def; data_state_INFO.ri_accfupds; K_THM]);;
let _ = cake_add_simps [data_dec_clock_const];;

let add_space_const = prove
 (`!(s:(C,FFI)data_state) k. data_state_ffi (add_space s k) = data_state_ffi s`,
  REWRITE_TAC[add_space_def; data_state_INFO.ri_accfupds; K_THM]);;
let _ = cake_add_simps [add_space_const];;

(* the ffi of the states the primitives of evaluate produce *)

let DSEMAUX_jump_exc_ffi = prove
 (`!(s:(C,FFI)data_state) t. data_jump_exc s = SOME t ==> data_state_ffi t = data_state_ffi s`,
  REPEAT GEN_TAC THEN DISCH_THEN (MP_TAC o MATCH_MP jump_exc_IMP) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM]);;

let DSEMAUX_FFI_RWS =
  [data_set_var_const; data_set_vars_const; data_call_env_const; data_push_env_const;
   data_dec_clock_const; add_space_const; data_flush_state_def; install_sfs_def;
   data_state_INFO.ri_accfupds; K_THM; DSEMAUX_ck_acc];;

let data_evaluate_io_events_mono = prove
 (`!exps (s1:(C,FFI)data_state) res s2.
     data_evaluate (exps,s1) = (res,s2) ==>
     ffi_state_io_events (data_state_ffi s1) <<= ffi_state_io_events (data_state_ffi s2)`,
  SUBGOAL_THEN
   `!p (res:((data_v list,data_v)result)option) (s2:(C,FFI)data_state).
      data_evaluate p = (res,s2) ==>
      ffi_state_io_events (data_state_ffi (SND p)) <<= ffi_state_io_events (data_state_ffi s2)`
   (fun th -> MESON_TAC[th; SND]) THEN
  MATCH_MP_TAC data_evaluate_ind THEN REWRITE_TAC[FST; SND] THEN REPEAT CONJ_TAC THEN
  REPEAT GEN_TAC THEN
  (fun (asl,w as g) ->
     let a,_ = dest_imp w in
     if DSEMAUX_is_main_hyp a then ALL_TAC g
     else (DISCH_THEN STRIP_ASSUME_TAC THEN REPEAT GEN_TAC) g) THEN
  DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE DSEMAUX_EVAL_CASE_EQS o
             ONCE_REWRITE_RULE[data_evaluate_def]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN DSEMAUX_SPLIT_CONJ_ASMS THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IS_SOME_DEF]) THEN
  DSEMAUX_CK_SIMP_ASMS THEN REPEAT DSEMAUX_CK_RES_TAC THEN
  IMP_RES_TAC data_do_app_io_events_mono THEN IMP_RES_TAC data_do_app_const THEN
  IMP_RES_TAC cut_state_opt_const THEN IMP_RES_TAC data_pop_env_const THEN
  IMP_RES_TAC DSEMAUX_jump_exc_ffi THEN
  RULE_ASSUM_TAC (REWRITE_RULE DSEMAUX_FFI_RWS) THEN
  ASM_REWRITE_TAC (IS_PREFIX_REFL :: DSEMAUX_FFI_RWS) THEN
  ASM_MESON_TAC[IS_PREFIX_TRANS; IS_PREFIX_REFL]);;

let data_with_clock_ffi = prove
 (`!(s:(C,FFI)data_state) y. data_state_ffi (data_state_clock_fupd (K y) s) = data_state_ffi s`,
  REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM]);;

let data_jump_exc_with_const = prove
 (`!(s:(C,FFI)data_state) k.
     data_jump_exc (data_state_clock_fupd (K k) s) =
     OPTION_MAP (\s. data_state_clock_fupd (K k) s) (data_jump_exc s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_jump_exc_def; data_state_INFO.ri_accfupds; K_THM] THEN
  REPEAT (COND_CASES_TAC ORELSE TOP_CASE_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN TRY(FIRST_ASSUM CONTR_TAC) THEN
  REWRITE_TAC[OPTION_MAP_DEF; option_INJ] THEN
  REWRITE_TAC[data_state_component_equality; data_state_INFO.ri_accfupds; K_THM]);;

(* io_events with more clock: both runs are split, the first one by the    *)
(* induction, the second one (with DSEMAUX_ck k) afterwards                *)

let DSEMAUX_is_ck_hyp tm =
  is_eq tm &&
  (try fst(dest_const(fst(strip_comb(lhs tm)))) = "data_evaluate" with Failure _ -> false) &&
  (try let p = rand (lhs tm) in
       fst(dest_const(fst(strip_comb(snd(dest_pair p))))) = "DSEMAUX_ck"
   with Failure _ -> false) &&
  is_pair (rhs tm) && (let r,s = dest_pair (rhs tm) in is_var r && is_var s);;

let DSEMAUX_IOCK_CLAUSE_TAC : tactic =
  REPEAT GEN_TAC THEN
  (fun (asl,w as g) ->
     let a,_ = dest_imp w in
     if DSEMAUX_is_main_hyp a then ALL_TAC g
     else (DISCH_THEN STRIP_ASSUME_TAC THEN REPEAT GEN_TAC) g) THEN
  DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE DSEMAUX_EVAL_CASE_EQS o
             ONCE_REWRITE_RULE[data_evaluate_def]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN DSEMAUX_SPLIT_CONJ_ASMS THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IS_SOME_DEF]) THEN
  DSEMAUX_CK_SIMP_ASMS THEN REPEAT DSEMAUX_CK_RES_TAC THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  IMP_RES_THEN (fun th -> ASSUME_TAC (REWRITE_RULE DSEMAUX_CK_SIMP_RWS th)) DSEMAUX_evaluate_ck THEN
  FIRST_X_ASSUM (MP_TAC o ONCE_REWRITE_RULE[data_evaluate_def] o
                 check (DSEMAUX_is_ck_hyp o concl)) THEN
  REWRITE_TAC DSEMAUX_CK_RWS THEN
  REPEAT (CHANGED_TAC (CASE_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
                       ASM_REWRITE_TAC (PAIR_EQ :: IS_SOME_DEF :: DSEMAUX_CK_RWS)) ORELSE
          DSEMAUX_CK_DEC_TAC) THEN
  TRY (DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE DSEMAUX_EVAL_CASE_EQS) THEN
       RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN DSEMAUX_SPLIT_CONJ_ASMS THEN RVEQ_TAC THEN
       DSEMAUX_CK_SIMP_ASMS THEN REPEAT DSEMAUX_CK_RES_TAC) THEN
  IMP_RES_TAC data_evaluate_io_events_mono THEN
  IMP_RES_TAC data_do_app_io_events_mono THEN IMP_RES_TAC data_do_app_const THEN
  IMP_RES_TAC cut_state_opt_const THEN IMP_RES_TAC data_pop_env_const THEN
  IMP_RES_TAC DSEMAUX_jump_exc_ffi THEN
  RULE_ASSUM_TAC (REWRITE_RULE DSEMAUX_FFI_RWS) THEN
  ASM_REWRITE_TAC (IS_PREFIX_REFL :: DSEMAUX_FFI_RWS) THEN
  ASM_MESON_TAC[IS_PREFIX_TRANS; IS_PREFIX_REFL];;

let DSEMAUX_IOCK_GOAL =
 `!p (r:((data_v list,data_v)result)option) (s2:(C,FFI)data_state).
     data_evaluate p = (r,s2) ==>
     !k r' s2'. data_evaluate (FST p,DSEMAUX_ck k (SND p)) = (r',s2') ==>
       ffi_state_io_events (data_state_ffi s2) <<= ffi_state_io_events (data_state_ffi s2')`;;

let DSEMAUX_evaluate_io_ck = prove
 (DSEMAUX_IOCK_GOAL,
  MATCH_MP_TAC data_evaluate_ind THEN REWRITE_TAC[FST; SND] THEN REPEAT CONJ_TAC THEN
  DSEMAUX_IOCK_CLAUSE_TAC);;

let data_evaluate_add_clock_io_events_mono = prove
 (`!exps (s:(C,FFI)data_state) extra.
     ffi_state_io_events (data_state_ffi (SND (data_evaluate (exps,s)))) <<=
     ffi_state_io_events (data_state_ffi (SND (data_evaluate
       (exps,data_state_clock_fupd (K (data_state_clock s + extra)) s))))`,
  REPEAT GEN_TAC THEN
  MP_TAC (ISPECL [`(exps:data_prog,s:(C,FFI)data_state)`;
                  `FST (data_evaluate (exps,s:(C,FFI)data_state))`;
                  `SND (data_evaluate (exps,s:(C,FFI)data_state))`] DSEMAUX_evaluate_io_ck) THEN
  REWRITE_TAC[FST; SND; PAIR] THEN
  DISCH_THEN (MP_TAC o SPECL [`extra:num`;
     `FST (data_evaluate (exps,DSEMAUX_ck extra (s:(C,FFI)data_state)))`;
     `SND (data_evaluate (exps,DSEMAUX_ck extra (s:(C,FFI)data_state)))`]) THEN
  REWRITE_TAC[PAIR; DSEMAUX_ck_def]);;

(* the first run of the semantics (clock 0) keeps the ffi *)

let DSEMAUX_semantics_clock0 = prove
 (`!(ffi:(FFI)ffi_state) prog (co:num -> C # (num # num # data_prog) list) cc lim ss start.
     data_state_ffi (SND (data_evaluate (data_Call NONE (SOME start) [] NONE,
                                         data_initial_state ffi prog co cc T lim ss 0))) = ffi`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[data_evaluate_def] THEN
  REWRITE_TAC[data_get_vars_def; data_initial_state_simp] THEN CASE_REWRITE_TAC[] THEN
  REPEAT (COND_CASES_TAC ORELSE TOP_CASE_TAC) THEN
  REWRITE_TAC[SND; data_flush_state_def; data_state_INFO.ri_accfupds; K_THM;
              data_initial_state_simp]);;

let semantics_Div_IMP_LPREFIX = prove
 (`!(ffi:(FFI)ffi_state) prog (co:num -> C # (num # num # data_prog) list) cc lim ss start l.
     data_semantics ffi prog co cc lim ss start = Diverge l ==>
     LPREFIX (llist_fromList (ffi_state_io_events ffi)) l`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_semantics_def; LET_DEF; LET_END_DEF] THEN
  COND_CASES_TAC THEN REWRITE_TAC[distinctness "behaviour"] THEN
  REWRITE_TAC[some_def] THEN COND_CASES_TAC THEN CASE_REWRITE_TAC[] THENL
   [DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o SELECT_RULE) THEN
    ASM_REWRITE_TAC[distinctness "behaviour"];
    ALL_TAC] THEN
  REWRITE_TAC[injectivity "behaviour"] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC (MESON[lprefix_lub_def; build_lprefix_lub_thm]
    `!ls (l:A llist). lprefix_chain ls /\ l IN ls ==> LPREFIX l (build_lprefix_lub ls)`) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM o_DEF; IMAGE_o] THEN MATCH_MP_TAC prefix_chain_lprefix_chain THEN
    REWRITE_TAC[prefix_chain_def; FORALL_IN_IMAGE_2; IN_UNIV] THEN
    MATCH_MP_TAC (MESON[LE_CASES; LE_EXISTS]
      `(!m d. P m (m + d:num)) ==> !k1 k2. P k1 k2 \/ P k2 k1`) THEN
    REPEAT GEN_TAC THEN
    MP_TAC (ISPECL [`data_Call NONE (SOME start) [] NONE`;
                    `data_initial_state (ffi:(FFI)ffi_state) prog
                       (co:num -> C # (num # num # data_prog) list) cc T lim ss m`; `d:num`]
                   data_evaluate_add_clock_io_events_mono) THEN
    REWRITE_TAC[data_initial_state_simp; data_initial_state_with_simp];
    REWRITE_TAC[IN_IMAGE; IN_UNIV] THEN EXISTS_TAC `0` THEN
    REWRITE_TAC[DSEMAUX_semantics_clock0]]);;

let semantics_Term_IMP_PREFIX = prove
 (`!(ffi:(FFI)ffi_state) prog (co:num -> C # (num # num # data_prog) list) cc lim ss start tt l.
     data_semantics ffi prog co cc lim ss start = Terminate tt l ==>
     ffi_state_io_events ffi <<= l`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_semantics_def; LET_DEF; LET_END_DEF] THEN
  COND_CASES_TAC THEN REWRITE_TAC[distinctness "behaviour"] THEN
  REWRITE_TAC[some_def] THEN COND_CASES_TAC THEN CASE_REWRITE_TAC[distinctness "behaviour"] THEN
  DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o SELECT_RULE) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[injectivity "behaviour"] THEN STRIP_TAC THEN
  FIRST_X_ASSUM (MP_TAC o MATCH_MP data_evaluate_io_events_mono) THEN
  ASM_REWRITE_TAC[data_initial_state_simp]);;

let data_Resource_limit_hit_implements_semantics = prove
 (`!(ffi:(FFI)ffi_state) prog (co:num -> C # (num # num # data_prog) list) cc lim ss start.
     implements {Terminate Resource_limit_hit (ffi_state_io_events ffi)}
                {data_semantics ffi (fromAList prog) co cc lim ss start}`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[implements_def; extend_with_resource_limit_def; SING_SUBSET; IN_UNION;
              IN_SING; IN_ELIM_THM] THEN
  MP_TAC (ISPEC `data_semantics (ffi:(FFI)ffi_state) (fromAList prog)
                   (co:num -> C # (num # num # data_prog) list) cc lim ss start`
                (cases "behaviour")) THEN
  STRIP_TAC THEN
  TRY (FIRST_ASSUM (ASSUME_TAC o MATCH_MP semantics_Div_IMP_LPREFIX)) THEN
  TRY (FIRST_ASSUM (ASSUME_TAC o MATCH_MP semantics_Term_IMP_PREFIX)) THEN
  ASM_REWRITE_TAC[distinctness "behaviour"; injectivity "behaviour"] THEN
  ASM_MESON_TAC[]);;

let data_get_code_labels_def = sem1aux_def (list_mk_conj
 [`(data_get_code_labels:data_prog->num->bool) (data_Call r d a h) =
     (match d with SOME x -> {x} | _ -> {}) UNION
     (match h with SOME (n,p) -> data_get_code_labels p | _ -> {})`;
  `(data_get_code_labels:data_prog->num->bool) (data_Force _ loc _) = {loc}`;
  `(data_get_code_labels:data_prog->num->bool) (data_Seq p1 p2) =
     data_get_code_labels p1 UNION data_get_code_labels p2`;
  `(data_get_code_labels:data_prog->num->bool) (data_If _ p1 p2) =
     data_get_code_labels p1 UNION data_get_code_labels p2`;
  `(data_get_code_labels:data_prog->num->bool) (data_Assign _ op _ _) =
     assign_get_code_label op`;
  `(data_get_code_labels:data_prog->num->bool) _ = {}`]);;
let _ = cake_add_simps [data_get_code_labels_def];;

let data_good_code_labels_def = cake_def
  `data_good_code_labels (p:(num # num # data_prog) list) elabs <=>
     UNIONS (set_of_list (MAP (\(n,m,pp). data_get_code_labels pp) p)) SUBSET
     (set_of_list (MAP FST p) UNION elabs)`;;

let get_code_labels_mk_ticks = prove
 (`!n m. data_get_code_labels (mk_ticks n m) SUBSET data_get_code_labels m`,
  INDUCT_TAC THEN REWRITE_TAC[mk_ticks_def; ITER; SUBSET_REFL] THEN
  REWRITE_TAC[GSYM mk_ticks_def; data_get_code_labels_def; UNION_EMPTY] THEN
  ASM_REWRITE_TAC[]);;

let v_to_list_SOME_NIL_IFF = prove
 (`!v. data_v_to_list v = SOME [] <=> ?ts. v = data_Block ts nil_tag []`,
  MATCH_MP_TAC (cake_ind "data_v_to_list") THEN
  REWRITE_TAC[data_v_to_list_def; injectivity "data_v"; distinctness "data_v";
              NOT_CONS_NIL; option_DISTINCT] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN TRY DISCH_TAC THEN
  REPEAT (COND_CASES_TAC ORELSE TOP_CASE_TAC) THEN
  ASM_REWRITE_TAC[option_DISTINCT; option_INJ; NOT_CONS_NIL; TPROPSAUX_EXISTS_REFL']);;

let v_to_list_SOME_CONS_IMP = prove
 (`!v x xs. data_v_to_list v = SOME (CONS x xs) ==>
            ?ts' ys. v = data_Block ts' cons_tag [x; ys] /\ data_v_to_list ys = SOME xs`,
  MATCH_MP_TAC (cake_ind "data_v_to_list") THEN
  REWRITE_TAC[data_v_to_list_def; injectivity "data_v"; distinctness "data_v";
              option_DISTINCT] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  TRY (DISCH_THEN (fun th -> if is_imp (concl th) then ALL_TAC else MP_TAC th)) THEN
  REPEAT GEN_TAC THEN
  REPEAT (COND_CASES_TAC ORELSE TOP_CASE_TAC) THEN
  REWRITE_TAC[option_DISTINCT; option_INJ; NOT_CONS_NIL; NOT_NIL_CONS; CONS_11] THEN
  STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`ts:num`; `bt:data_v`] THEN ASM_REWRITE_TAC[]);;

(*fs[] is slower than full_simp_tac(srw_ss())[]*)
let do_app_safe_for_space_mono = prove
 (`!op xs (s:(C,FFI)data_state) r s1.
     data_do_app op xs s = Rval (r,s1) /\ data_state_safe_for_space s1 ==>
     data_state_safe_for_space s`,
  X_GEN_TAC `op:clos_op` THEN DSEMAUX_OP_CASES_TAC `op:clos_op` THEN
  REPEAT GEN_TAC THEN CASE_REWRITE_TAC DSEMAUX_DO_APP_DEFS THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  CASE_REWRITE_TAC DSEMAUX_DO_APP_RWS THEN
  REPEAT ((COND_CASES_TAC ORELSE TOP_CASE_TAC) THEN CASE_REWRITE_TAC DSEMAUX_DO_APP_RWS) THEN
  REWRITE_TAC[injectivity "result"; distinctness "result"; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC (REWRITE_RULE DSEMAUX_FINISH_RWS) THEN DSEMAUX_SPLIT_CONJ_ASMS THEN
  TRY (FIRST_ASSUM CONTR_TAC) THEN ASM_REWRITE_TAC[]);;

let DSEMAUX_safe_imps = prove
 (`(!n v (s:(C,FFI)data_state).
      data_state_safe_for_space (data_set_var n v s) <=> data_state_safe_for_space s) /\
   (!ns vs (s:(C,FFI)data_state).
      data_state_safe_for_space (data_set_vars ns vs s) <=> data_state_safe_for_space s) /\
   (!b (s:(C,FFI)data_state).
      data_state_safe_for_space (data_flush_state b s) <=> data_state_safe_for_space s) /\
   (!(s:(C,FFI)data_state).
      data_state_safe_for_space (data_dec_clock s) <=> data_state_safe_for_space s) /\
   (!op (s:(C,FFI)data_state).
      data_state_safe_for_space (install_sfs op s) ==> data_state_safe_for_space s) /\
   (!args sz (s:(C,FFI)data_state).
      data_state_safe_for_space (data_call_env args sz s) ==> data_state_safe_for_space s) /\
   (!env b (s:(C,FFI)data_state).
      data_state_safe_for_space (data_push_env env b s) ==> data_state_safe_for_space s) /\
   (!(s:(C,FFI)data_state) k.
      data_state_safe_for_space (add_space s k) ==> data_state_safe_for_space s) /\
   (!(s:(C,FFI)data_state) t.
      data_pop_env s = SOME t ==> data_state_safe_for_space t = data_state_safe_for_space s) /\
   (!(s:(C,FFI)data_state) t.
      data_jump_exc s = SOME t ==> data_state_safe_for_space t = data_state_safe_for_space s) /\
   (!names (s:(C,FFI)data_state) t.
      data_cut_state_opt names s = SOME t ==>
      data_state_safe_for_space t = data_state_safe_for_space s)`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN TRY (BOOL_CASES_TAC `b:bool`) THEN
  REWRITE_TAC[data_set_var_def; data_set_vars_def; data_flush_state_def; data_dec_clock_def;
              install_sfs_def; data_call_env_def; data_push_env_def; add_space_def;
              LET_DEF; LET_END_DEF; data_state_INFO.ri_accfupds; K_THM] THEN
  TRY (MESON_TAC[]) THEN
  REWRITE_TAC[data_pop_env_def; data_jump_exc_def; data_cut_state_opt_def;
              data_cut_state_def] THEN
  REPEAT (COND_CASES_TAC ORELSE TOP_CASE_TAC) THEN
  REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN (SUBST1_TAC o SYM) THEN REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM]);;

let DSEMAUX_push_env_safe = prove
 (`!env b (s:(C,FFI)data_state).
     data_state_safe_for_space (data_push_env env b s) <=>
     data_state_safe_for_space s /\
     misc_the F (OPTION_MAP ((>) (limits_stack_limit (data_state_limits s)))
              (OPTION_MAP2 MAX (data_state_stack_max s)
                 (size_of_stack (data_state_stack (data_push_env env b s)))))`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN
  REWRITE_TAC[data_push_env_def; LET_DEF; LET_END_DEF; data_state_INFO.ri_accfupds; K_THM]);;

let DSEMAUX_SAFE_RWS =
  [data_set_var_def; data_set_vars_def; data_flush_state_def; data_dec_clock_def;
   install_sfs_def; data_call_env_def; LET_DEF; LET_END_DEF; add_space_def;
   DSEMAUX_push_env_safe; data_state_INFO.ri_accfupds; K_THM];;

let DSEMAUX_safe_eqs = prove
 (`(!(s:(C,FFI)data_state) t.
      data_pop_env s = SOME t ==> data_state_safe_for_space t = data_state_safe_for_space s) /\
   (!(s:(C,FFI)data_state) t.
      data_jump_exc s = SOME t ==> data_state_safe_for_space t = data_state_safe_for_space s) /\
   (!names (s:(C,FFI)data_state) t.
      data_cut_state_opt names s = SOME t ==>
      data_state_safe_for_space t = data_state_safe_for_space s)`,
  REWRITE_TAC[DSEMAUX_safe_imps]);;

let DSEMAUX_SAFE_CLAUSE_TAC : tactic =
  REPEAT GEN_TAC THEN
  (fun (asl,w as g) ->
     let a,_ = dest_imp w in
     if DSEMAUX_is_main_hyp a then ALL_TAC g
     else (DISCH_THEN STRIP_ASSUME_TAC THEN REPEAT GEN_TAC) g) THEN
  DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE DSEMAUX_EVAL_CASE_EQS o
             ONCE_REWRITE_RULE[data_evaluate_def]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN DSEMAUX_SPLIT_CONJ_ASMS THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IS_SOME_DEF]) THEN
  DSEMAUX_CK_SIMP_ASMS THEN REPEAT DSEMAUX_CK_RES_TAC THEN
  MAP_EVERY (fun th -> TRY (DSEMAUX_FULL_RES_TAC th)) (CONJUNCTS DSEMAUX_safe_eqs) THEN
  RULE_ASSUM_TAC (REWRITE_RULE DSEMAUX_SAFE_RWS) THEN
  REWRITE_TAC DSEMAUX_SAFE_RWS THEN
  ASM_MESON_TAC[do_app_safe_for_space_mono];;

let evaluate_safe_for_space_mono = prove
 (`!prog (s:(C,FFI)data_state) res s1.
     data_evaluate (prog,s) = (res,s1) /\ data_state_safe_for_space s1 ==>
     data_state_safe_for_space s`,
  SUBGOAL_THEN
   `!p (res:((data_v list,data_v)result)option) (s1:(C,FFI)data_state).
      data_evaluate p = (res,s1) ==> data_state_safe_for_space s1 ==>
      data_state_safe_for_space (SND p)`
   (fun th -> MESON_TAC[th; SND]) THEN
  MATCH_MP_TAC data_evaluate_ind THEN REWRITE_TAC[FST; SND] THEN REPEAT CONJ_TAC THEN
  DSEMAUX_SAFE_CLAUSE_TAC);;

let zero_limits_def = cake_def
  `zero_limits =
     limits_heap_limit_fupd (K 0)
       (limits_length_limit_fupd (K 0) (limits_stack_limit_fupd (K 0) (ARB:limits)))`;;

(* HOL4 [local]: the limits-swap commutes through the narrow cut in       *)
(* evaluate (Assign)                                                       *)
let cut_state_opt_with_lim = prove
 (`!names_opt (s:(C,FFI)data_state) lim.
     data_cut_state_opt names_opt (data_state_limits_fupd (K lim) s) =
     OPTION_MAP (\t. data_state_limits_fupd (K lim) t) (data_cut_state_opt names_opt s)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[data_cut_state_opt_def; data_cut_state_def; data_state_INFO.ri_accfupds; K_THM] THEN
  REPEAT TOP_CASE_TAC THEN REWRITE_TAC[OPTION_MAP_DEF; option_INJ] THEN
  REWRITE_TAC[data_state_component_equality; data_state_INFO.ri_accfupds; K_THM]);;

(* the limits swap through the primitives of evaluate *)

let DSEMAUX_lim_tac : tactic =
  REWRITE_TAC[DSEMAUX_ssp_def; data_state_component_equality; data_state_INFO.ri_accfupds;
              K_THM];;

let DSEMAUX_lim_rws = prove
 (`(!n v lim (s:(C,FFI)data_state).
      data_set_var n v (data_state_limits_fupd (K lim) s) =
      data_state_limits_fupd (K lim) (data_set_var n v s)) /\
   (!ns vs lim (s:(C,FFI)data_state).
      data_set_vars ns vs (data_state_limits_fupd (K lim) s) =
      data_state_limits_fupd (K lim) (data_set_vars ns vs s)) /\
   (!b lim (s:(C,FFI)data_state).
      data_flush_state b (data_state_limits_fupd (K lim) s) =
      data_state_limits_fupd (K lim) (data_flush_state b s)) /\
   (!op lim (s:(C,FFI)data_state).
      install_sfs op (data_state_limits_fupd (K lim) s) =
      data_state_limits_fupd (K lim) (install_sfs op s)) /\
   (!lim (s:(C,FFI)data_state).
      data_dec_clock (data_state_limits_fupd (K lim) s) =
      data_state_limits_fupd (K lim) (data_dec_clock s)) /\
   (!e lim (s:(C,FFI)data_state).
      data_state_locals_fupd (K e) (data_state_limits_fupd (K lim) s) =
      data_state_limits_fupd (K lim) (data_state_locals_fupd (K e) s)) /\
   (!x lim (s:(C,FFI)data_state).
      data_state_stack_fupd (K x) (data_state_limits_fupd (K lim) s) =
      data_state_limits_fupd (K lim) (data_state_stack_fupd (K x) s)) /\
   (!smx sf pk lim (s:(C,FFI)data_state).
      data_state_limits_fupd (K lim) (DSEMAUX_ssp smx sf pk s) =
      DSEMAUX_ssp smx sf pk (data_state_limits_fupd (K lim) s)) /\
   (!lim (s:(C,FFI)data_state).
      data_jump_exc (data_state_limits_fupd (K lim) s) =
      OPTION_MAP (data_state_limits_fupd (K lim)) (data_jump_exc s)) /\
   (!lim (s:(C,FFI)data_state).
      data_pop_env (data_state_limits_fupd (K lim) s) =
      OPTION_MAP (data_state_limits_fupd (K lim)) (data_pop_env s)) /\
   (!args sz lim (s:(C,FFI)data_state).
      data_call_env args sz (data_state_limits_fupd (K lim) s) =
      DSEMAUX_ssp (data_state_stack_max (data_call_env args sz s))
        (data_state_safe_for_space s /\
         misc_the F (OPTION_MAP ((>) (limits_stack_limit lim))
                  (data_state_stack_max (data_call_env args sz s))))
        (data_state_peak_heap_length s)
        (data_state_limits_fupd (K lim) (data_call_env args sz s))) /\
   (!env b lim (s:(C,FFI)data_state).
      data_push_env env b (data_state_limits_fupd (K lim) s) =
      DSEMAUX_ssp (data_state_stack_max (data_push_env env b s))
        (data_state_safe_for_space s /\
         misc_the F (OPTION_MAP ((>) (limits_stack_limit lim))
                  (data_state_stack_max (data_push_env env b s))))
        (data_state_peak_heap_length s)
        (data_state_limits_fupd (K lim) (data_push_env env b s))) /\
   (!lim (s:(C,FFI)data_state) k.
      add_space (data_state_limits_fupd (K lim) s) k =
      DSEMAUX_ssp (data_state_stack_max s)
        (data_state_safe_for_space s /\ no_thunks_in_refs (data_state_refs s) /\
         size_of_heap (data_state_limits_fupd (K lim) s) + k <= limits_heap_limit lim)
        (MAX (data_state_peak_heap_length s) (size_of_heap (data_state_limits_fupd (K lim) s) + k))
        (data_state_limits_fupd (K lim) (add_space s k)))`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN TRY (BOOL_CASES_TAC `b:bool`) THEN
  REWRITE_TAC[data_set_var_def; data_set_vars_def; data_flush_state_def; install_sfs_def;
              data_dec_clock_def; data_call_env_def; data_push_env_def; add_space_def;
              LET_DEF; LET_END_DEF; data_state_INFO.ri_accfupds; K_THM] THEN
  TRY (REWRITE_TAC[data_jump_exc_def; data_pop_env_def; data_state_INFO.ri_accfupds; K_THM] THEN
       REPEAT (COND_CASES_TAC ORELSE TOP_CASE_TAC) THEN
       RULE_ASSUM_TAC(REWRITE_RULE[]) THEN TRY(FIRST_ASSUM CONTR_TAC) THEN
       REWRITE_TAC[OPTION_MAP_DEF; option_INJ]) THEN
  DSEMAUX_lim_tac);;

let DSEMAUX_LIM_INST_TAC : tactic =
  REPEAT (FIRST_X_ASSUM (fun th ->
    let vs,_ = strip_forall (concl th) in
    if length vs = 1 && type_of (hd vs) = `:limits`
    then STRIP_ASSUME_TAC (SPEC `lim:limits` th) else NO_TAC));;

let DSEMAUX_LIM_RWS =
  DSEMAUX_lim_rws :: cut_state_opt_with_lim :: data_state_INFO.ri_accfupds :: K_THM ::
  DSEMAUX_ssp_ssp ::
  DSEMAUX_SSP_RWS;;

(* witnesses for ?smx sf pk. .. L = DSEMAUX_ssp smx sf pk Y ..: the ssp     *)
(* arguments of L, or the fields of L                                        *)

let DSEMAUX_SSP_WIT_TAC : tactic = fun (asl,w as g) ->
  let vs,body = strip_exists w in
  let is_ssp t = try fst(dest_const(fst(strip_comb t))) = "DSEMAUX_ssp" &&
                     length(snd(strip_comb t)) = 4 with Failure _ -> false in
  let eqs = find_terms (fun t -> is_eq t && is_ssp (rhs t) &&
                                 (let _,ra = strip_comb (rhs t) in
                                  subset (fst(chop_list 3 ra)) vs)) body in
  let e = hd eqs in
  let l = lhs e in
  let wl = if is_ssp l then fst(chop_list 3 (snd(strip_comb l)))
           else [mk_comb(`data_state_stack_max:(C,FFI)data_state->num option`,l);
                 mk_comb(`data_state_safe_for_space:(C,FFI)data_state->bool`,l);
                 mk_comb(`data_state_peak_heap_length:(C,FFI)data_state->num`,l)] in
  let _,ra = strip_comb (rhs e) in
  let wit = map (fun v -> assoc v (zip (fst(chop_list 3 ra)) wl)) vs in
  MAP_EVERY EXISTS_TAC wit g;;

let DSEMAUX_LIM_CLAUSE_TAC : tactic =
  REPEAT GEN_TAC THEN
  (fun (asl,w as g) ->
     let a,_ = dest_imp w in
     if DSEMAUX_is_main_hyp a then ALL_TAC g
     else (DISCH_THEN STRIP_ASSUME_TAC THEN REPEAT GEN_TAC) g) THEN
  DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE DSEMAUX_EVAL_CASE_EQS o
             ONCE_REWRITE_RULE[data_evaluate_def]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN DSEMAUX_SPLIT_CONJ_ASMS THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IS_SOME_DEF]) THEN
  DSEMAUX_CK_SIMP_ASMS THEN REPEAT DSEMAUX_CK_RES_TAC THEN
  X_GEN_TAC `lim:limits` THEN DSEMAUX_LIM_INST_TAC THEN
  TRY (IMP_RES_THEN (fun th -> STRIP_ASSUME_TAC (SPEC `lim:limits` th)) do_app_lim_swap) THEN
  TRY (IMP_RES_THEN (fun th -> ASSUME_TAC (SPEC `lim:limits` th)) do_app_err_lim_swap) THEN
  RULE_ASSUM_TAC (REWRITE_RULE [GSYM DSEMAUX_ssp_def]) THEN
  RULE_ASSUM_TAC (REWRITE_RULE [DSEMAUX_lim_rws]) THEN
  IMP_RES_TAC DSEMAUX_evaluate_ssp THEN RULE_ASSUM_TAC (REWRITE_RULE[FST; SND]) THEN
  ONCE_REWRITE_TAC[data_evaluate_def] THEN
  REWRITE_TAC DSEMAUX_LIM_RWS THEN
  REPEAT (CHANGED_TAC (CASE_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
                       ASM_REWRITE_TAC (PAIR_EQ :: IS_SOME_DEF :: DSEMAUX_LIM_RWS)) ORELSE
          DSEMAUX_SSP_IH_TAC ORELSE DSEMAUX_SSP_DO_APP_RW_TAC) THEN
  REWRITE_TAC DSEMAUX_LIM_RWS THEN
  DSEMAUX_SSP_WIT_TAC THEN
  REWRITE_TAC[DSEMAUX_ssp_def; data_state_component_equality; data_state_INFO.ri_accfupds;
              K_THM; data_set_var_def; data_set_vars_def; data_flush_state_def; install_sfs_def;
              data_dec_clock_def; data_call_env_def; LET_DEF; LET_END_DEF] THEN
  ASM_REWRITE_TAC[];;

let DSEMAUX_LIM_GOAL =
 `!p (r:((data_v list,data_v)result)option) (s':(C,FFI)data_state).
     data_evaluate p = (r,s') ==>
     !lim. ?smx sf pk.
       data_evaluate (FST p,data_state_limits_fupd (K lim) (SND p)) =
       (r,DSEMAUX_ssp smx sf pk (data_state_limits_fupd (K lim) s'))`;;

let DSEMAUX_evaluate_lim = prove
 (DSEMAUX_LIM_GOAL,
  MATCH_MP_TAC data_evaluate_ind THEN REWRITE_TAC[FST; SND] THEN REPEAT CONJ_TAC THEN
  DSEMAUX_LIM_CLAUSE_TAC);;

let evaluate_swap_limits = prove
 (`!c (s:(C,FFI)data_state) r s' limits.
     data_evaluate (c,s) = (r,s') ==>
     ?smx safe peak.
       data_evaluate (c,data_state_limits_fupd (K limits) s) =
       (r,data_state_limits_fupd (K limits)
            (data_state_stack_max_fupd (K smx)
               (data_state_safe_for_space_fupd (K safe)
                  (data_state_peak_heap_length_fupd (K peak) s'))))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM (MP_TAC o SPEC `limits:limits` o REWRITE_RULE[FST; SND] o
               MATCH_MP DSEMAUX_evaluate_lim) THEN
  DISCH_THEN (X_CHOOSE_THEN `smx:num option` (X_CHOOSE_THEN `sf:bool`
    (X_CHOOSE_THEN `pk:num` SUBST1_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`smx:num option`; `sf:bool`; `pk:num`] THEN
  REWRITE_TAC[PAIR_EQ; DSEMAUX_ssp_def; data_state_component_equality;
              data_state_INFO.ri_accfupds; K_THM]);;

(* HOL4 [local] *)
let evaluate_zero_limits_FST = prove
 (`!c (s:(C,FFI)data_state).
     FST (data_evaluate (c,s)) =
     FST (data_evaluate (c,data_state_limits_fupd (K zero_limits) s))`,
  REPEAT GEN_TAC THEN
  MP_TAC (ISPEC `data_evaluate (c,s:(C,FFI)data_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN (X_CHOOSE_THEN `r:((data_v list,data_v)result)option`
    (X_CHOOSE_THEN `s1:(C,FFI)data_state` ASSUME_TAC)) THEN
  FIRST_ASSUM (MP_TAC o SPEC `zero_limits` o MATCH_MP evaluate_swap_limits) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;

(* HOL4 [local] *)
let evaluate_zero_limits_ffi = prove
 (`!c (s:(C,FFI)data_state).
     data_state_ffi (SND (data_evaluate (c,s))) =
     data_state_ffi (SND (data_evaluate (c,data_state_limits_fupd (K zero_limits) s)))`,
  REPEAT GEN_TAC THEN
  MP_TAC (ISPEC `data_evaluate (c,s:(C,FFI)data_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN (X_CHOOSE_THEN `r:((data_v list,data_v)result)option`
    (X_CHOOSE_THEN `s1:(C,FFI)data_state` ASSUME_TAC)) THEN
  FIRST_ASSUM (MP_TAC o SPEC `zero_limits` o MATCH_MP evaluate_swap_limits) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM]);;

(* Stack frames equal up-to size component *)
let stack_frame_size_rel_def = cake_def
  `(stack_frame_size_rel (Exc opt spt num) (Exc opt' spt' num') <=>
      spt = spt' /\ num = num') /\
   (stack_frame_size_rel (data_Env opt spt) (data_Env opt' spt') <=> spt = spt') /\
   (stack_frame_size_rel _ _ <=> F)`;;

let find_code_upto_size = prove
 (`!dest (x:data_v list) (code:(num # A) spt) (sizes:B spt) foo (other_sizes:C spt).
     data_find_code dest x code sizes = foo ==>
     ?other_size.
       data_find_code dest x code other_sizes =
       OPTION_MAP (\(args,exp,size'). (args,exp,other_size)) foo`,
  REPEAT GEN_TAC THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
  STRUCT_CASES_TAC (ISPEC `dest:num option` (cases "option")) THEN
  REWRITE_TAC[data_find_code_def] THEN
  REPEAT (COND_CASES_TAC ORELSE TOP_CASE_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN TRY(FIRST_ASSUM CONTR_TAC) THEN
  REWRITE_TAC[OPTION_MAP_DEF] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[option_INJ; PAIR_EQ; TPROPSAUX_EXISTS_REFL']);;

let do_app_stack_eq = prove
 (`!op vs (s:(C,FFI)data_state) q s'.
     data_do_app op vs s = Rval (q,s') ==> data_state_stack s = data_state_stack s'`,
  MESON_TAC[data_do_app_const]);;

let do_app_stack_frame_size_rel = prove
 (`!op vs (s:(C,FFI)data_state) q s' stk.
     data_do_app op vs s = Rval (q,s') /\ ALL2 stack_frame_size_rel (data_state_stack s) stk ==>
     ALL2 stack_frame_size_rel (data_state_stack s') stk`,
  MESON_TAC[do_app_stack_eq]);;

(* HOL4 [local]: the locals_size/stack/stack_frame_sizes-swap commutes      *)
(* through the narrow cut in evaluate (Assign), and the cut preserves the   *)
(* stack                                                                     *)
let cut_state_opt_with_sfs = prove
 (`!names_opt (s:(C,FFI)data_state) lsz xs sfs.
     data_cut_state_opt names_opt
       (data_state_locals_size_fupd (K lsz) (data_state_stack_fupd (K xs)
          (data_state_stack_frame_sizes_fupd (K sfs) s))) =
     OPTION_MAP (\t. data_state_locals_size_fupd (K lsz) (data_state_stack_fupd (K xs)
                       (data_state_stack_frame_sizes_fupd (K sfs) t)))
                (data_cut_state_opt names_opt s)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[data_cut_state_opt_def; data_cut_state_def; data_state_INFO.ri_accfupds; K_THM] THEN
  REPEAT TOP_CASE_TAC THEN REWRITE_TAC[OPTION_MAP_DEF; option_INJ] THEN
  REWRITE_TAC[data_state_component_equality; data_state_INFO.ri_accfupds; K_THM]);;

(* HOL4 [local] *)
let cut_state_opt_stack = prove
 (`!names_opt (s:(C,FFI)data_state) s1.
     data_cut_state_opt names_opt s = SOME s1 ==> data_state_stack s1 = data_state_stack s`,
  MESON_TAC[DSEMAUX_cut_state_opt_stack]);;

(* ------------------------------------------------------------------------- *)
(* evaluate_swap_stack_frame_sizes_aux: the stack (up to the frame sizes),   *)
(* locals_size, stack_frame_sizes and the ssp fields are swapped;            *)
(* DSEMAUX_sfs sfs s is s with stack_frame_sizes := sfs                       *)
(* ------------------------------------------------------------------------- *)

let DSEMAUX_sfs_def = new_definition
  `DSEMAUX_sfs fsz (s:(C,FFI)data_state) = data_state_stack_frame_sizes_fupd (K fsz) s`;;

let DSEMAUX_sfs_tac : tactic =
  REWRITE_TAC[DSEMAUX_sfs_def; DSEMAUX_sl_def; DSEMAUX_ssp_def; data_state_component_equality;
              data_state_INFO.ri_accfupds; K_THM];;

let DSEMAUX_sfs_acc =
  let names = map (fun (f,_,_) -> f) data_state_INFO.ri_fields in
  let names = filter (fun f -> f <> "stack_frame_sizes") names in
  let cl f = "data_state_" ^ f ^ " (DSEMAUX_sfs fsz s) = data_state_" ^ f ^ " s" in
  let tm = parse_term ("!fsz (s:(C,FFI)data_state). " ^
             String.concat " /\\ " (map cl names) ^
             " /\\ data_state_stack_frame_sizes (DSEMAUX_sfs fsz s) = fsz") in
  prove(tm, REWRITE_TAC[DSEMAUX_sfs_def; data_state_INFO.ri_accfupds; K_THM]);;

let DSEMAUX_sfs_rws = prove
 (`(!n v fsz (s:(C,FFI)data_state).
      data_set_var n v (DSEMAUX_sfs fsz s) = DSEMAUX_sfs fsz (data_set_var n v s)) /\
   (!ns vs fsz (s:(C,FFI)data_state).
      data_set_vars ns vs (DSEMAUX_sfs fsz s) = DSEMAUX_sfs fsz (data_set_vars ns vs s)) /\
   (!b fsz (s:(C,FFI)data_state).
      data_flush_state b (DSEMAUX_sfs fsz s) = DSEMAUX_sfs fsz (data_flush_state b s)) /\
   (!op fsz (s:(C,FFI)data_state).
      install_sfs op (DSEMAUX_sfs fsz s) = DSEMAUX_sfs fsz (install_sfs op s)) /\
   (!fsz (s:(C,FFI)data_state).
      data_dec_clock (DSEMAUX_sfs fsz s) = DSEMAUX_sfs fsz (data_dec_clock s)) /\
   (!e fsz (s:(C,FFI)data_state).
      data_state_locals_fupd (K e) (DSEMAUX_sfs fsz s) =
      DSEMAUX_sfs fsz (data_state_locals_fupd (K e) s)) /\
   (!x fsz (s:(C,FFI)data_state).
      data_state_stack_fupd (K x) (DSEMAUX_sfs fsz s) =
      DSEMAUX_sfs fsz (data_state_stack_fupd (K x) s)) /\
   (!smx sf pk fsz (s:(C,FFI)data_state).
      DSEMAUX_ssp smx sf pk (DSEMAUX_sfs fsz s) = DSEMAUX_sfs fsz (DSEMAUX_ssp smx sf pk s)) /\
   (!xs lsz fsz (s:(C,FFI)data_state).
      DSEMAUX_sl xs lsz (DSEMAUX_sfs fsz s) = DSEMAUX_sfs fsz (DSEMAUX_sl xs lsz s)) /\
   (!fsz fsz' (s:(C,FFI)data_state).
      DSEMAUX_sfs fsz (DSEMAUX_sfs fsz' s) = DSEMAUX_sfs fsz s) /\
   (!args sz fsz (s:(C,FFI)data_state).
      data_call_env args sz (DSEMAUX_sfs fsz s) = DSEMAUX_sfs fsz (data_call_env args sz s)) /\
   (!env b fsz (s:(C,FFI)data_state).
      data_push_env env b (DSEMAUX_sfs fsz s) = DSEMAUX_sfs fsz (data_push_env env b s)) /\
   (!fsz (s:(C,FFI)data_state) k.
      add_space (DSEMAUX_sfs fsz s) k = DSEMAUX_sfs fsz (add_space s k)) /\
   (!fsz (s:(C,FFI)data_state).
      data_pop_env (DSEMAUX_sfs fsz s) = OPTION_MAP (DSEMAUX_sfs fsz) (data_pop_env s)) /\
   (!fsz (s:(C,FFI)data_state).
      data_jump_exc (DSEMAUX_sfs fsz s) = OPTION_MAP (DSEMAUX_sfs fsz) (data_jump_exc s)) /\
   (!names fsz (s:(C,FFI)data_state).
      data_cut_state_opt names (DSEMAUX_sfs fsz s) =
      OPTION_MAP (DSEMAUX_sfs fsz) (data_cut_state_opt names s))`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN TRY (BOOL_CASES_TAC `b:bool`) THEN
  REWRITE_TAC[data_set_var_def; data_set_vars_def; data_flush_state_def; install_sfs_def;
              data_dec_clock_def; data_call_env_def; data_push_env_def; add_space_def;
              size_of_heap_def; stack_to_vs_def; LET_DEF; LET_END_DEF;
              data_state_INFO.ri_accfupds; K_THM; DSEMAUX_sfs_acc] THEN
  TRY (REWRITE_TAC[data_jump_exc_def; data_pop_env_def; data_cut_state_opt_def;
                   data_cut_state_def; data_state_INFO.ri_accfupds; K_THM; DSEMAUX_sfs_acc] THEN
       REPEAT (COND_CASES_TAC ORELSE TOP_CASE_TAC) THEN
       RULE_ASSUM_TAC(REWRITE_RULE[]) THEN TRY(FIRST_ASSUM CONTR_TAC) THEN
       REWRITE_TAC[OPTION_MAP_DEF; option_INJ]) THEN
  DSEMAUX_sfs_tac);;

let DSEMAUX_sfs_do_app = prove
 (`!op vs (s:(C,FFI)data_state) q s' fsz.
     data_do_app op vs s = Rval (q,s') ==>
     ?smx sf pk.
       data_do_app op vs (DSEMAUX_sfs fsz s) =
       Rval (q,DSEMAUX_sl (data_state_stack s) (data_state_locals_size s)
                 (DSEMAUX_ssp smx sf pk
                    (DSEMAUX_sfs (if op = clos_Install then LN else fsz) s')))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN (MP_TAC o SPECL [`data_state_locals_size (s:(C,FFI)data_state)`;
                              `data_state_stack (s:(C,FFI)data_state)`; `fsz:num spt`] o
              MATCH_MP do_app_lss_stk_stfrm_swap) THEN
  SUBGOAL_THEN `data_state_locals_size_fupd (K (data_state_locals_size s))
                  (data_state_stack_fupd (K (data_state_stack s))
                     (data_state_stack_frame_sizes_fupd (K fsz) s)) =
                DSEMAUX_sfs fsz (s:(C,FFI)data_state)` SUBST1_TAC THENL
   [DSEMAUX_sfs_tac; ALL_TAC] THEN
  DISCH_THEN (X_CHOOSE_THEN `sf:bool` (X_CHOOSE_THEN `pk:num`
    (X_CHOOSE_THEN `smx:num option` SUBST1_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`smx:num option`; `sf:bool`; `pk:num`] THEN
  REWRITE_TAC[injectivity "result"; PAIR_EQ] THEN DSEMAUX_sfs_tac);;

let DSEMAUX_sfs_do_app_err = prove
 (`!op vs (s:(C,FFI)data_state) e fsz.
     data_do_app op vs s = Rerr e ==> data_do_app op vs (DSEMAUX_sfs fsz s) = Rerr e`,
  REPEAT GEN_TAC THEN
  DISCH_THEN (MP_TAC o SPECL [`data_state_locals_size (s:(C,FFI)data_state)`;
                              `data_state_stack (s:(C,FFI)data_state)`; `fsz:num spt`] o
              MATCH_MP do_app_err_lss_stk_stfrm_swap) THEN
  SUBGOAL_THEN `data_state_locals_size_fupd (K (data_state_locals_size s))
                  (data_state_stack_fupd (K (data_state_stack s))
                     (data_state_stack_frame_sizes_fupd (K fsz) s)) =
                DSEMAUX_sfs fsz (s:(C,FFI)data_state)` SUBST1_TAC THENL
   [DSEMAUX_sfs_tac; REWRITE_TAC[]]);;

let DSEMAUX_sfr_refl = prove
 (`!x. stack_frame_size_rel x x`,
  MATCH_MP_TAC stack_INDUCT THEN REWRITE_TAC[stack_frame_size_rel_def]);;

let DSEMAUX_ALL2_sfr_refl = prove
 (`!l. ALL2 stack_frame_size_rel l l`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ALL2; DSEMAUX_sfr_refl]);;

let DSEMAUX_sfr_cons = prove
 (`(!l e st xs.
      ALL2 stack_frame_size_rel (CONS (data_Env l e) st) xs <=>
      ?l' rest. xs = CONS (data_Env l' e) rest /\ ALL2 stack_frame_size_rel st rest) /\
   (!l e h st xs.
      ALL2 stack_frame_size_rel (CONS (Exc l e h) st) xs <=>
      ?l' rest. xs = CONS (Exc l' e h) rest /\ ALL2 stack_frame_size_rel st rest)`,
  CONJ_TAC THEN REPEAT GEN_TAC THEN
  DISJ_CASES_THEN2 SUBST1_TAC
    (X_CHOOSE_THEN `fr:stack` (X_CHOOSE_THEN `rest0:stack list` SUBST1_TAC))
    (ISPEC `xs:stack list` list_CASES) THEN
  REWRITE_TAC[ALL2; NOT_CONS_NIL; CONS_11] THEN
  STRUCT_CASES_TAC (ISPEC `fr:stack` (cases "stack")) THEN
  REWRITE_TAC[stack_frame_size_rel_def; injectivity "stack"; distinctness "stack"] THEN
  MESON_TAC[]);;

let DSEMAUX_sfr_push = prove
 (`!b l l' e h.
     stack_frame_size_rel (if b then Exc l e h else data_Env l e)
                          (if b then Exc l' e h else data_Env l' e)`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[stack_frame_size_rel_def]);;

(* jump_exc through related stacks *)

let DSEMAUX_jump_exc_rel = prove
 (`!(s:(C,FFI)data_state) (t:(C,FFI)data_state).
     ALL2 stack_frame_size_rel (data_state_stack s) (data_state_stack t) /\
     data_state_handler t = data_state_handler s ==>
     (data_jump_exc s = NONE ==> data_jump_exc t = NONE) /\
     (!s2. data_jump_exc s = SOME s2 ==>
           ?xs2 l2. data_jump_exc t =
                    SOME (data_state_handler_fupd (K (data_state_handler s2))
                            (data_state_locals_fupd (K (data_state_locals s2))
                               (data_state_stack_fupd (K xs2)
                                  (data_state_locals_size_fupd (K l2) t)))) /\
                    ALL2 stack_frame_size_rel (data_state_stack s2) xs2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM (ASSUME_TAC o MATCH_MP LIST_REL_LENGTH) THEN
  REWRITE_TAC[data_jump_exc_def] THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
  SUBGOAL_THEN `ALL2 stack_frame_size_rel
                  (LASTN (data_state_handler (s:(C,FFI)data_state) + 1) (data_state_stack s))
                  (LASTN (data_state_handler s + 1) (data_state_stack (t:(C,FFI)data_state)))`
    MP_TAC THENL
   [MATCH_MP_TAC list_rel_lastn THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SPEC_TAC (`LASTN (data_state_handler (s:(C,FFI)data_state) + 1)
                   (data_state_stack (t:(C,FFI)data_state))`,
            `m:stack list`) THEN
  SPEC_TAC (`LASTN (data_state_handler (s:(C,FFI)data_state) + 1) (data_state_stack s)`,
            `k:stack list`) THEN
  LIST_INDUCT_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `m:stack list` list_CASES) THEN
  REWRITE_TAC[ALL2; NOT_CONS_NIL] THEN CASE_REWRITE_TAC[] THEN
  STRUCT_CASES_TAC (ISPEC `h:stack` (cases "stack")) THEN
  STRUCT_CASES_TAC (ISPEC `h':stack` (cases "stack")) THEN
  REWRITE_TAC[stack_frame_size_rel_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[option_DISTINCT; option_INJ] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  GEN_TAC THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
  MAP_EVERY EXISTS_TAC [`t'':stack list`; `a0':num option`] THEN
  ASM_REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM]);;

(* the stack facts of evaluate (from evaluate_stack) *)

let DSEMAUX_eval_stack = prove
 (`(!c (s:(C,FFI)data_state) s1.
      data_evaluate (c,s) = (NONE,s1) ==>
      data_state_stack s1 = data_state_stack s /\ data_state_handler s1 = data_state_handler s) /\
   (!c (s:(C,FFI)data_state) v s1.
      data_evaluate (c,s) = (SOME (Rval v),s1) ==>
      data_state_stack s1 = data_state_stack s /\ data_state_handler s1 = data_state_handler s) /\
   (!c (s:(C,FFI)data_state) v s1.
      data_evaluate (c,s) = (SOME (Rerr (Rraise v)),s1) ==>
      ?s2. data_jump_exc s = SOME s2 /\ data_state_locals s2 = data_state_locals s1 /\
           data_state_stack s2 = data_state_stack s1 /\
           data_state_handler s2 = data_state_handler s1)`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  DISCH_THEN (fun th -> MP_TAC (SPECL [`c:data_prog`; `s:(C,FFI)data_state`] evaluate_stack) THEN
                        REWRITE_TAC[th]) THEN
  CASE_REWRITE_TAC[]);;

let DSEMAUX_sfs_in = prove
 (`(!fsz xs lsz (s:(C,FFI)data_state).
      DSEMAUX_sfs fsz (DSEMAUX_sl xs lsz s) = DSEMAUX_sl xs lsz (DSEMAUX_sfs fsz s)) /\
   (!fsz smx sf pk (s:(C,FFI)data_state).
      DSEMAUX_sfs fsz (DSEMAUX_ssp smx sf pk s) = DSEMAUX_ssp smx sf pk (DSEMAUX_sfs fsz s))`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN DSEMAUX_sfs_tac);;

let DSEMAUX_SFS_RWS =
  let cs = CONJUNCTS DSEMAUX_sfs_rws in
  let keep th = let tm = snd(strip_forall(concl th)) in
    not (is_eq tm &&
         (try let h = fst(dest_const(fst(strip_comb(lhs tm)))) in
              h = "DSEMAUX_ssp" || h = "DSEMAUX_sl"
          with Failure _ -> false)) in
  filter keep cs;;

let DSEMAUX_F_RWS =
  DSEMAUX_sfs_acc :: DSEMAUX_sfs_in :: DSEMAUX_dec_clock_sh :: DSEMAUX_sl_pop_env ::
  DSEMAUX_SFS_RWS @ DSEMAUX_SL_RWS2;;

(* the facts of the swapped run for find_code, do_app and jump_exc *)

let DSEMAUX_find_code_sizes = prove
 (`!dest (x:data_v list) (code:(num # data_prog) spt) (sizes:num spt) foo (other_sizes:num spt).
     data_find_code dest x code sizes = foo ==>
     ?other_size.
       data_find_code dest x code other_sizes =
       OPTION_MAP (\(args,exp,size'). (args,exp,other_size)) foo`,
  REWRITE_TAC[find_code_upto_size]);;

let DSEMAUX_F_FACTS_TAC : tactic =
  TRY (FIRST_ASSUM (fun th ->
    if is_eq (concl th) &&
       (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "data_find_code"
        with Failure _ -> false)
    then MP_TAC (SPEC `fsz:num spt` (MATCH_MP DSEMAUX_find_code_sizes th))
    else NO_TAC) THEN
    CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
    REWRITE_TAC[OPTION_MAP_DEF] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
    DISCH_THEN (fun th -> if is_exists (concl th)
                          then X_CHOOSE_THEN `osz:num option` ASSUME_TAC th
                          else ASSUME_TAC th)) THEN
  TRY (IMP_RES_THEN (fun th -> STRIP_ASSUME_TAC (SPEC `fsz:num spt` th)) DSEMAUX_sfs_do_app) THEN
  TRY (IMP_RES_THEN (fun th -> ASSUME_TAC (SPEC `fsz:num spt` th)) DSEMAUX_sfs_do_app_err) THEN
  ALL_TAC;;

(* apply an induction hypothesis !xs lsz fsz smx sf pk. ALL2 .. ==> ?... at a  *)
(* recursive call data_evaluate (P,DSEMAUX_sl X Y (DSEMAUX_ssp A B C           *)
(* (DSEMAUX_sfs Z T))) of the goal                                              *)

let DSEMAUX_F_args t =
  let h1,a1 = strip_comb t in
  if fst(dest_const h1) <> "DSEMAUX_sl" || length a1 <> 3 then failwith "F_args" else
  let h2,a2 = strip_comb (el 2 a1) in
  if fst(dest_const h2) <> "DSEMAUX_ssp" || length a2 <> 4 then failwith "F_args" else
  let h3,a3 = strip_comb (el 3 a2) in
  if fst(dest_const h3) <> "DSEMAUX_sfs" || length a3 <> 2 then failwith "F_args" else
  (el 0 a1, el 1 a1, el 0 a3, el 0 a2, el 1 a2, el 2 a2, el 1 a3);;

let DSEMAUX_is_F_eval t =
  is_comb t && (try fst(dest_const(rator t)) = "data_evaluate" with Failure _ -> false) &&
  is_pair (rand t) && can DSEMAUX_F_args (snd (dest_pair (rand t)));;

let DSEMAUX_F_ALL2_TAC : tactic =
  REWRITE_TAC[DSEMAUX_call_env_sh; DSEMAUX_push_env_sh; DSEMAUX_dec_clock_sh;
              DSEMAUX_set_var_sh; DSEMAUX_set_vars_sh; ALL2; DSEMAUX_sfr_push;
              stack_frame_size_rel_def; COND_CLAUSES] THEN
  ASM_REWRITE_TAC[];;

(* the size argument of a call_env under the swap does not matter *)

let DSEMAUX_sl_call_env_size = prove
 (`!xs l a b c f args sz1 sz2 (s:(C,FFI)data_state).
     DSEMAUX_sl xs l (DSEMAUX_ssp a b c (DSEMAUX_sfs f (data_call_env args sz1 s))) =
     DSEMAUX_sl xs l (DSEMAUX_ssp a b c (DSEMAUX_sfs f (data_call_env args sz2 s)))`,
  REWRITE_TAC[data_call_env_def; LET_DEF; LET_END_DEF] THEN DSEMAUX_sfs_tac);;

let DSEMAUX_is_call_env t =
  try fst(dest_const(fst(strip_comb t))) = "data_call_env" &&
      length (snd (strip_comb t)) = 3 with Failure _ -> false;;

let DSEMAUX_F_IH_TAC : tactic = fun (asl,w as g) ->
  let targets = find_terms DSEMAUX_is_F_eval w in
  let try_one t =
    let p,st = dest_pair (rand t) in
    let (x,y,z,a,b,c,tt) = DSEMAUX_F_args st in
    tryfind (fun (_,th) ->
      let vs1,body = strip_forall (concl th) in
      if not (is_imp body) then failwith "" else
      let ant,rest = dest_imp body in
      let vs2,ex = strip_forall rest in
      if length vs1 + length vs2 <> 6 then failwith "" else
      let _,eqs = strip_exists ex in
      let eq = fst (dest_conj eqs) in
      let lt = lhs eq in
      let p',st' = dest_pair (rand lt) in
      let (xv,yv,zv,av,bv,cv,tt') = DSEMAUX_F_args st' in
      let same_upto_size =
        DSEMAUX_is_call_env tt && DSEMAUX_is_call_env tt' &&
        (let _,a1 = strip_comb tt and _,a2 = strip_comb tt' in
         el 0 a1 = el 0 a2 && el 2 a1 = el 2 a2) in
      if not (p' = p && (tt' = tt || same_upto_size)) then failwith "" else
      let sub = [xv,x; yv,y; zv,z; av,a; bv,b; cv,c] in
      let inst v = assoc v sub in
      let fix = if tt' = tt then ALL_TAC else
        let _,a1 = strip_comb tt and _,a2 = strip_comb tt' in
        REWRITE_TAC[ISPECL [x;y;a;b;c;z;el 0 a1;el 1 a1;el 1 a2;el 2 a1]
                           DSEMAUX_sl_call_env_size] in
      (th, map inst vs1, map inst vs2, ex, fix)) asl in
  let (th,i1,i2,ex,fix) = tryfind try_one targets in
  let ex' = vsubst (zip i2 (fst (strip_forall (snd (dest_imp (snd (strip_forall (concl th)))))))) ex in
  let evs,_ = strip_exists ex' in
  let avoid = freesl (w :: map (concl o snd) asl) in
  let fresh = rev(itlist (fun v acc -> variant (acc @ avoid) v :: acc) (rev evs) []) in
  (fix THEN MP_TAC (SPECL i1 th) THEN ANTS_TAC THENL [DSEMAUX_F_ALL2_TAC; ALL_TAC] THEN
   DISCH_THEN (MP_TAC o SPECL i2) THEN
   MAP_EVERY (fun v -> DISCH_THEN(X_CHOOSE_THEN v MP_TAC)) fresh THEN
   DISCH_THEN (fun th -> STRIP_ASSUME_TAC th THEN REWRITE_TAC[CONJUNCT1 th])) g;;

(* a frame relation ALL2 .. (CONS fr st) v with v a variable: v = CONS fr' rest *)

let DSEMAUX_F_CONS_TAC : tactic = fun (asl,w as g) ->
  let is_c tm = (try let h,args = strip_comb tm in
                     fst(dest_const h) = "ALL2" && length args = 3 && is_var (el 2 args) &&
                     (let l = el 1 args in is_comb l &&
                      fst(dest_const(fst(strip_comb l))) = "CONS")
                 with Failure _ -> false) in
  let th = snd (find (fun (_,th) -> is_c (concl th)) asl) in
  (UNDISCH_TAC (concl th) THEN REWRITE_TAC[DSEMAUX_sfr_cons] THEN
   DISCH_THEN (X_CHOOSE_THEN `lfr:num option` (X_CHOOSE_THEN `xsr:stack list`
     (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)))) g;;

(* rewrite the ALL2 facts with the stack facts *)

let DSEMAUX_is_stack_eq th =
  let c = concl th in
  is_eq c && is_comb (lhs c) &&
  (try fst(dest_const(rator(lhs c))) = "data_state_stack" with Failure _ -> false) &&
  is_var (rand (lhs c)) && not (rhs c = lhs c);;

let DSEMAUX_F_STACK_TAC : tactic = fun (asl,w as g) ->
  let eqs = filter DSEMAUX_is_stack_eq (map snd asl) in
  RULE_ASSUM_TAC (fun th ->
    let c = concl th in
    if (try fst(dest_const(fst(strip_comb c))) = "ALL2" with Failure _ -> false)
    then REWRITE_RULE (eqs @ [DSEMAUX_call_env_sh; DSEMAUX_push_env_sh; DSEMAUX_dec_clock_sh;
                              DSEMAUX_set_var_sh; DSEMAUX_set_vars_sh; COND_CLAUSES]) th
    else th) g;;

(* witnesses: the fields of the final state of the swapped run *)

let DSEMAUX_F_WIT_TAC : tactic = fun (asl,w as g) ->
  let vs,body = strip_exists w in
  if length vs <> 6 then failwith "DSEMAUX_F_WIT_TAC" else
  let eq = fst (dest_conj body) in
  let l = lhs eq in
  let x = if is_pair l then snd (dest_pair l) else l in
  let acc s ty = mk_comb(mk_mconst("data_state_" ^ s, mk_fun_ty `:(C,FFI)data_state` ty), x) in
  MAP_EVERY EXISTS_TAC
    [acc "stack" `:stack list`; acc "locals_size" `:num option`;
     acc "stack_frame_sizes" `:num spt`; acc "stack_max" `:num option`;
     acc "safe_for_space" `:bool`; acc "peak_heap_length" `:num`] g;;

let DSEMAUX_F_ACC_RWS =
  [DSEMAUX_sl_acc; DSEMAUX_ssp_acc; DSEMAUX_sfs_acc; data_state_INFO.ri_accfupds; K_THM;
   data_set_var_def; data_set_vars_def; data_flush_state_def; install_sfs_def;
   data_dec_clock_def; data_call_env_def; LET_DEF; LET_END_DEF; DSEMAUX_push_env_acc;
   DSEMAUX_call_env_sh; DSEMAUX_push_env_sh; DSEMAUX_dec_clock_sh; add_space_def];;

let DSEMAUX_F_POP_CONTR_TAC : tactic =
  FIRST_X_ASSUM (MP_TAC o check (fun th ->
    let c = concl th in
    is_eq c && is_const (rhs c) && fst (dest_const (rhs c)) = "NONE" &&
    (try fst(dest_const(rator(lhs c))) = "data_pop_env" with Failure _ -> false))) THEN
  RULE_ASSUM_TAC (REWRITE_RULE DSEMAUX_F_ACC_RWS) THEN
  ASM_REWRITE_TAC (data_pop_env_def :: DSEMAUX_F_ACC_RWS) THEN
  CASE_REWRITE_TAC[option_DISTINCT];;

let DSEMAUX_F_FINISH_TAC : tactic =
  TRY (DSEMAUX_F_POP_CONTR_TAC THEN NO_TAC) THEN
  DSEMAUX_F_WIT_TAC THEN REWRITE_TAC[PAIR_EQ] THEN CONJ_TAC THENL
   [REWRITE_TAC[DSEMAUX_sl_def; DSEMAUX_ssp_def; DSEMAUX_sfs_def;
                data_state_component_equality] THEN
    REWRITE_TAC DSEMAUX_F_ACC_RWS THEN
    IMP_RES_TAC data_do_app_const THEN ASM_REWRITE_TAC DSEMAUX_F_ACC_RWS;
    REWRITE_TAC DSEMAUX_F_ACC_RWS THEN
    IMP_RES_TAC data_do_app_const THEN IMP_RES_TAC DSEMAUX_cut_state_opt_stack THEN
    RULE_ASSUM_TAC (REWRITE_RULE DSEMAUX_F_ACC_RWS) THEN
    REPEAT (FIRST_X_ASSUM (SUBST_ALL_TAC o check (fun th ->
      let c = concl th in
      is_eq c && is_comb (lhs c) &&
      (try fst(dest_const(rator(lhs c))) = "data_state_stack" with Failure _ -> false) &&
      is_var (rand (lhs c)) && not (rhs c = lhs c)))) THEN
    ASM_REWRITE_TAC (ALL2 :: DSEMAUX_ALL2_sfr_refl :: stack_frame_size_rel_def ::
                     DSEMAUX_sfr_push :: DSEMAUX_F_ACC_RWS)];;

let DSEMAUX_F_PUSH_TAC : tactic = fun (asl,w as g) ->
  let is_t t = is_comb t &&
    (try let h,args = strip_comb t in fst(dest_const h) = "data_push_env" && length args = 3 &&
         fst(dest_const(fst(strip_comb(el 2 args)))) = "DSEMAUX_sl"
     with Failure _ -> false) in
  let t = find_term is_t w in
  let _,args = strip_comb t in
  let _,sargs = strip_comb (el 2 args) in
  (MP_TAC (ISPECL [el 0 args; el 1 args; el 0 sargs; el 1 sargs; el 2 sargs] DSEMAUX_sl_push_env) THEN
   ANTS_TAC THENL
    [REWRITE_TAC[DSEMAUX_ssp_acc; DSEMAUX_sl_acc; DSEMAUX_sfs_acc; DSEMAUX_dec_clock_sh] THEN
     ASM_REWRITE_TAC[];
     DISCH_THEN (fun th -> REWRITE_TAC[th])]) g;;

let DSEMAUX_F_LOOP_TAC : tactic =
  REPEAT (CHANGED_TAC (CASE_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
                       ASM_REWRITE_TAC (PAIR_EQ :: IS_SOME_DEF :: DSEMAUX_F_RWS)) ORELSE
          DSEMAUX_SSP_DO_APP_RW_TAC ORELSE DSEMAUX_F_PUSH_TAC ORELSE
          (DSEMAUX_F_IH_TAC THEN DSEMAUX_F_STACK_TAC THEN REPEAT DSEMAUX_F_CONS_TAC));;

let DSEMAUX_F_JUMP_TAC : tactic = fun (asl,w as g) ->
  let js = filter (fun (_,th) -> DSEMAUX_ASM_HEAD "data_jump_exc" th &&
                                 is_var (rand (lhs (concl th)))) asl in
  match js with
    [] -> ALL_TAC g
  | (_,th)::_ ->
      let st = rand (lhs (concl th)) in
      let t = mk_comb(mk_comb(mk_comb(
                `DSEMAUX_sl:stack list->num option->(C,FFI)data_state->(C,FFI)data_state`,
                `xs:stack list`), `lsz:num option`),
                mk_comb(mk_comb(`DSEMAUX_sfs:num spt->(C,FFI)data_state->(C,FFI)data_state`,
                                `fsz:num spt`), st)) in
      (MP_TAC (ISPECL [st; t] DSEMAUX_jump_exc_rel) THEN
       ANTS_TAC THENL [REWRITE_TAC[DSEMAUX_sl_acc; DSEMAUX_sfs_acc] THEN ASM_REWRITE_TAC[];
                       ALL_TAC] THEN
       DISCH_THEN (CONJUNCTS_THEN2
         (fun th -> TRY (FIRST_ASSUM (ASSUME_TAC o MATCH_MP th)))
         (fun th -> TRY (FIRST_ASSUM (STRIP_ASSUME_TAC o MATCH_MP th)))) THEN
       TRY (FIRST_ASSUM (fun th -> if DSEMAUX_ASM_HEAD "data_jump_exc" th &&
                                      is_var (rand (lhs (concl th))) &&
                                      is_comb (rhs (concl th))
                                   then STRIP_ASSUME_TAC (MATCH_MP jump_exc_IMP th)
                                   else NO_TAC)) THEN
       RVEQ_TAC) g;;

(* the state after a pop_env of a state with a known top frame *)

let DSEMAUX_F_POPFACT_TAC : tactic = fun (asl,w as g) ->
  let is_pop th =
    let c = concl th in
    is_eq c && (try fst(dest_const(rator(lhs c))) = "data_pop_env" with Failure _ -> false) &&
    is_var (rand (lhs c)) &&
    (try fst(dest_const(rator(rhs c))) = "SOME" && is_var (rand (rhs c))
     with Failure _ -> false) in
  match filter (is_pop o snd) asl with
    [] -> ALL_TAC g
  | (_,th)::_ ->
      let v = rand (lhs (concl th)) in
      let (_,st) = find (fun (_,t) -> DSEMAUX_is_stack_eq t && rand (lhs (concl t)) = v) asl in
      let sth = REWRITE_RULE [DSEMAUX_call_env_sh; DSEMAUX_push_env_sh; DSEMAUX_dec_clock_sh;
                              DSEMAUX_set_var_sh; DSEMAUX_set_vars_sh; COND_CLAUSES] st in
      let pth = try MATCH_MP (CONJUNCT1 DSEMAUX_pop_env_frame) sth
                with Failure _ -> MATCH_MP (CONJUNCT2 DSEMAUX_pop_env_frame) sth in
      let eq = REWRITE_RULE [option_INJ] (TRANS (SYM th) pth) in
      SUBST_ALL_TAC eq g;;

(* split an unsplit Call handler (its frame is then concrete) *)

let DSEMAUX_F_HANDLER_TAC : tactic = fun (asl,w as g) ->
  let hv = `handler:(num # data_prog) option` in
  if mem hv (frees w) then
    (DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `hp:num # data_prog` SUBST_ALL_TAC)
       (ISPEC hv (cases "option")) THEN
     RULE_ASSUM_TAC (REWRITE_RULE[IS_SOME_DEF]) THEN REWRITE_TAC[IS_SOME_DEF]) g
  else ALL_TAC g;;

let DSEMAUX_F_CLAUSE_TAC : tactic =
  REPEAT GEN_TAC THEN
  (fun (asl,w as g) ->
     let a,_ = dest_imp w in
     if DSEMAUX_is_main_hyp a then ALL_TAC g
     else (DISCH_THEN STRIP_ASSUME_TAC THEN REPEAT GEN_TAC) g) THEN
  DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE DSEMAUX_EVAL_CASE_EQS o
             ONCE_REWRITE_RULE[data_evaluate_def]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN DSEMAUX_SPLIT_CONJ_ASMS THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IS_SOME_DEF]) THEN DSEMAUX_F_HANDLER_TAC THEN
  DSEMAUX_CK_SIMP_ASMS THEN TRY (FIRST_ASSUM CONTR_TAC) THEN REPEAT DSEMAUX_CK_RES_TAC THEN
  MAP_EVERY X_GEN_TAC [`xs:stack list`; `lsz:num option`; `fsz:num spt`;
                       `smx:num option`; `sf:bool`; `pk:num`] THEN DISCH_TAC THEN
  FIRST_ASSUM (ASSUME_TAC o MATCH_MP LIST_REL_LENGTH) THEN
  DSEMAUX_F_FACTS_TAC THEN DSEMAUX_F_JUMP_TAC THEN
  MAP_EVERY (fun th -> TRY (DSEMAUX_FULL_RES_TAC th)) (CONJUNCTS DSEMAUX_eval_stack) THEN
  TRY DSEMAUX_F_POPFACT_TAC THEN
  ONCE_REWRITE_TAC[data_evaluate_def] THEN
  REWRITE_TAC DSEMAUX_F_RWS THEN DSEMAUX_F_LOOP_TAC THEN
  DSEMAUX_F_FINISH_TAC;;

let DSEMAUX_F_GOAL =
 `!p (r:((data_v list,data_v)result)option) (s1:(C,FFI)data_state).
     data_evaluate p = (r,s1) ==>
     !xs lsz fsz smx sf pk.
       ALL2 stack_frame_size_rel (data_state_stack (SND p)) xs ==>
       ?xs' lsz' fsz' smx' sf' pk'.
         data_evaluate (FST p,DSEMAUX_sl xs lsz (DSEMAUX_ssp smx sf pk (DSEMAUX_sfs fsz (SND p)))) =
         (r,DSEMAUX_sl xs' lsz' (DSEMAUX_ssp smx' sf' pk' (DSEMAUX_sfs fsz' s1))) /\
         ALL2 stack_frame_size_rel (data_state_stack s1) xs'`;;

let DSEMAUX_evaluate_F = prove
 (DSEMAUX_F_GOAL,
  MATCH_MP_TAC data_evaluate_ind THEN REWRITE_TAC[FST; SND] THEN REPEAT CONJ_TAC THEN
  DSEMAUX_F_CLAUSE_TAC);;

(* HOL4 [local] *)
let evaluate_swap_stack_frame_sizes_aux = prove
 (`!c (s:(C,FFI)data_state) r s' xs lsz sfs.
     data_evaluate (c,s) = (r,s') /\ ALL2 stack_frame_size_rel (data_state_stack s) xs ==>
     let s0 = data_state_locals_size_fupd (K lsz)
                (data_state_stack_fupd (K xs)
                   (data_state_stack_frame_sizes_fupd (K sfs) s)) in
     ?xs lsz smx safe peak sfs'.
       data_evaluate (c,s0) =
       (r,data_state_locals_size_fupd (K lsz)
            (data_state_safe_for_space_fupd (K safe)
               (data_state_stack_fupd (K xs)
                  (data_state_stack_frame_sizes_fupd (K sfs')
                     (data_state_stack_max_fupd (K smx)
                        (data_state_peak_heap_length_fupd (K peak) s')))))) /\
       ALL2 stack_frame_size_rel (data_state_stack s') xs`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  MP_TAC (SPECL [`xs:stack list`; `lsz:num option`; `sfs:num spt`;
                 `data_state_stack_max (s:(C,FFI)data_state)`;
                 `data_state_safe_for_space (s:(C,FFI)data_state)`;
                 `data_state_peak_heap_length (s:(C,FFI)data_state)`]
    (REWRITE_RULE[FST; SND] (MATCH_MP DSEMAUX_evaluate_F
       (ASSUME `data_evaluate (c,s:(C,FFI)data_state) = r,s'`)))) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `DSEMAUX_sl xs lsz (DSEMAUX_ssp (data_state_stack_max s)
                  (data_state_safe_for_space s) (data_state_peak_heap_length s)
                  (DSEMAUX_sfs sfs s)) =
                data_state_locals_size_fupd (K lsz) (data_state_stack_fupd (K xs)
                  (data_state_stack_frame_sizes_fupd (K sfs) (s:(C,FFI)data_state)))`
    SUBST1_TAC THENL [DSEMAUX_sfs_tac; ALL_TAC] THEN
  DISCH_THEN (X_CHOOSE_THEN `xs1:stack list` (X_CHOOSE_THEN `lsz1:num option`
    (X_CHOOSE_THEN `fsz1:num spt` (X_CHOOSE_THEN `smx1:num option`
      (X_CHOOSE_THEN `sf1:bool` (X_CHOOSE_THEN `pk1:num` STRIP_ASSUME_TAC)))))) THEN
  MAP_EVERY EXISTS_TAC [`xs1:stack list`; `lsz1:num option`; `smx1:num option`;
                        `sf1:bool`; `pk1:num`; `fsz1:num spt`] THEN
  ASM_REWRITE_TAC[PAIR_EQ] THEN DSEMAUX_sfs_tac);;

let evaluate_swap_local_sizes = prove
 (`!c (s:(C,FFI)data_state) r s' lss.
     data_evaluate (c,s) = (r,s') ==>
     ?xs lsz sfs smx safe peak.
       data_evaluate (c,data_state_locals_size_fupd (K lss) s) =
       (r,data_state_locals_size_fupd (K lsz)
            (data_state_safe_for_space_fupd (K safe)
               (data_state_stack_fupd (K xs)
                  (data_state_stack_frame_sizes_fupd (K sfs)
                     (data_state_stack_max_fupd (K smx)
                        (data_state_peak_heap_length_fupd (K peak) s')))))) /\
       ALL2 stack_frame_size_rel (data_state_stack s') xs`,
  REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`c:data_prog`; `s:(C,FFI)data_state`; `r:((data_v list,data_v)result)option`;
                 `s':(C,FFI)data_state`; `data_state_stack (s:(C,FFI)data_state)`;
                 `lss:num option`; `data_state_stack_frame_sizes (s:(C,FFI)data_state)`]
                evaluate_swap_stack_frame_sizes_aux) THEN
  ASM_REWRITE_TAC[DSEMAUX_ALL2_sfr_refl; LET_DEF; LET_END_DEF] THEN
  SUBGOAL_THEN `data_state_locals_size_fupd (K lss)
                  (data_state_stack_fupd (K (data_state_stack s))
                     (data_state_stack_frame_sizes_fupd (K (data_state_stack_frame_sizes s)) s)) =
                data_state_locals_size_fupd (K lss) (s:(C,FFI)data_state)` SUBST1_TAC THENL
   [REWRITE_TAC[data_state_component_equality; data_state_INFO.ri_accfupds; K_THM];
    ALL_TAC] THEN
  MESON_TAC[]);;

let evaluate_swap_stack_frame_sizes = prove
 (`!c (s:(C,FFI)data_state) r s' sfs.
     data_evaluate (c,s) = (r,s') ==>
     ?xs lsz smx safe peak sfs'.
       data_evaluate (c,data_state_stack_frame_sizes_fupd (K sfs) s) =
       (r,data_state_locals_size_fupd (K lsz)
            (data_state_safe_for_space_fupd (K safe)
               (data_state_stack_fupd (K xs)
                  (data_state_stack_frame_sizes_fupd (K sfs')
                     (data_state_stack_max_fupd (K smx)
                        (data_state_peak_heap_length_fupd (K peak) s')))))) /\
       ALL2 stack_frame_size_rel (data_state_stack s') xs`,
  REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`c:data_prog`; `s:(C,FFI)data_state`; `r:((data_v list,data_v)result)option`;
                 `s':(C,FFI)data_state`; `data_state_stack (s:(C,FFI)data_state)`;
                 `data_state_locals_size (s:(C,FFI)data_state)`; `sfs:num spt`]
                evaluate_swap_stack_frame_sizes_aux) THEN
  ASM_REWRITE_TAC[DSEMAUX_ALL2_sfr_refl; LET_DEF; LET_END_DEF] THEN
  SUBGOAL_THEN `data_state_locals_size_fupd (K (data_state_locals_size s))
                  (data_state_stack_fupd (K (data_state_stack s))
                     (data_state_stack_frame_sizes_fupd (K sfs) s)) =
                data_state_stack_frame_sizes_fupd (K sfs) (s:(C,FFI)data_state)` SUBST1_TAC THENL
   [REWRITE_TAC[data_state_component_equality; data_state_INFO.ri_accfupds; K_THM];
    ALL_TAC] THEN
  MESON_TAC[]);;

(* HOL4 [local] *)
let evaluate_stack_frame_sizes_FST = prove
 (`!c (s:(C,FFI)data_state).
     FST (data_evaluate (c,s)) =
     FST (data_evaluate (c,data_state_stack_frame_sizes_fupd (K LN) s))`,
  REPEAT GEN_TAC THEN
  MP_TAC (ISPEC `data_evaluate (c,s:(C,FFI)data_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN (X_CHOOSE_THEN `r:((data_v list,data_v)result)option`
    (X_CHOOSE_THEN `s1:(C,FFI)data_state` ASSUME_TAC)) THEN
  FIRST_ASSUM (MP_TAC o SPEC `LN:num spt` o MATCH_MP evaluate_swap_stack_frame_sizes) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;

(* HOL4 [local] *)
let evaluate_stack_frame_sizes_ffi = prove
 (`!c (s:(C,FFI)data_state).
     data_state_ffi (SND (data_evaluate (c,s))) =
     data_state_ffi (SND (data_evaluate (c,data_state_stack_frame_sizes_fupd (K LN) s)))`,
  REPEAT GEN_TAC THEN
  MP_TAC (ISPEC `data_evaluate (c,s:(C,FFI)data_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN (X_CHOOSE_THEN `r:((data_v list,data_v)result)option`
    (X_CHOOSE_THEN `s1:(C,FFI)data_state` ASSUME_TAC)) THEN
  FIRST_ASSUM (MP_TAC o SPEC `LN:num spt` o MATCH_MP evaluate_swap_stack_frame_sizes) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM]);;

let DSEMAUX_some_cong = prove
 (`!(E1:((data_v list,data_v)result)option # (C,FFI)data_state)
    (E2:((data_v list,data_v)result)option # (D,FFI)data_state) Q res.
     FST E1 = FST E2 /\ data_state_ffi (SND E1) = data_state_ffi (SND E2) ==>
     ((?s r outcome. E1 = (SOME r,s) /\ Q r outcome /\
                     res = Terminate outcome (ffi_state_io_events (data_state_ffi s))) <=>
      (?s r outcome. E2 = (SOME r,s) /\ Q r outcome /\
                     res = Terminate outcome (ffi_state_io_events (data_state_ffi s))))`,
  REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ; FST; SND] THEN
  MAP_EVERY X_GEN_TAC [`a1:((data_v list,data_v)result)option`; `b1:(C,FFI)data_state`;
                       `a2:((data_v list,data_v)result)option`; `b2:(D,FFI)data_state`] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THENL
   [MAP_EVERY EXISTS_TAC [`b2:(D,FFI)data_state`; `r:(data_v list,data_v)result`;
                         `outcome:outcome`];
    MAP_EVERY EXISTS_TAC [`b1:(C,FFI)data_state`; `r:(data_v list,data_v)result`;
                         `outcome:outcome`]] THEN
  REPEAT (FIRST_X_ASSUM (SUBST_ALL_TAC o check (fun th -> is_var (rhs (concl th))))) THEN
  ASM_REWRITE_TAC[]);;

let semantics_zero_limits = prove
 (`!(ffi:(FFI)ffi_state) code (co:num -> C # (num # num # data_prog) list) cc lim ss start.
     data_semantics ffi code co cc lim ss start =
     data_semantics ffi code co cc zero_limits LN start`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `!p k. FST (data_evaluate (p,data_initial_state (ffi:(FFI)ffi_state) code
                 (co:num -> C # (num # num # data_prog) list) cc T lim ss k)) =
          FST (data_evaluate (p,data_initial_state ffi code co cc T zero_limits LN k)) /\
          data_state_ffi (SND (data_evaluate (p,data_initial_state ffi code co cc T lim ss k))) =
          data_state_ffi (SND (data_evaluate
            (p,data_initial_state ffi code co cc T zero_limits LN k)))`
   ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    SUBGOAL_THEN
     `data_initial_state (ffi:(FFI)ffi_state) code
        (co:num -> C # (num # num # data_prog) list) cc T zero_limits LN k =
      data_state_stack_frame_sizes_fupd (K LN)
        (data_state_limits_fupd (K zero_limits)
           (data_initial_state ffi code co cc T lim ss k))` SUBST1_TAC THENL
     [REWRITE_TAC[data_initial_state_def; data_state_INFO.ri_fupds; K_THM]; ALL_TAC] THEN
    REWRITE_TAC[GSYM evaluate_stack_frame_sizes_FST; GSYM evaluate_stack_frame_sizes_ffi;
                GSYM evaluate_zero_limits_FST; GSYM evaluate_zero_limits_ffi];
    ALL_TAC] THEN
  REWRITE_TAC[data_semantics_def; LET_DEF; LET_END_DEF] THEN
  ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  (fun (asl,w as g) ->
     let is_some t = is_comb t && (try fst(dest_const(rator t)) = "some" with Failure _ -> false) in
     let l,r = dest_eq w in
     let p1 = rand (find_term is_some l) and p2 = rand (find_term is_some r) in
     SUBGOAL_THEN (mk_eq(p1,p2)) (fun th -> REWRITE_TAC[th]) g) THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `res:behaviour` THEN
  AP_TERM_TAC THEN ABS_TAC THEN
  MATCH_MP_TAC DSEMAUX_some_cong THEN ASM_REWRITE_TAC[]);;

let do_app_stack_max = prove
 (`!op xs (s1:(C,FFI)data_state) v s2.
     data_do_app op xs s1 = Rval (v,s2) ==>
     option_le (data_state_stack_max s1) (data_state_stack_max s2)`,
  X_GEN_TAC `op:clos_op` THEN DSEMAUX_OP_CASES_TAC `op:clos_op` THEN
  REPEAT GEN_TAC THEN CASE_REWRITE_TAC DSEMAUX_DO_APP_DEFS THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  CASE_REWRITE_TAC DSEMAUX_DO_APP_RWS THEN
  REPEAT ((COND_CASES_TAC ORELSE TOP_CASE_TAC) THEN CASE_REWRITE_TAC DSEMAUX_DO_APP_RWS) THEN
  REWRITE_TAC[injectivity "result"; distinctness "result"; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  ASM_REWRITE_TAC(option_le_refl :: option_le_max_right :: option_le_def :: DSEMAUX_FINISH_RWS));;

(* stack_max only grows during evaluate *)

let DSEMAUX_smx_imps = prove
 (`(!args sz (s:(C,FFI)data_state).
      option_le (data_state_stack_max s) (data_state_stack_max (data_call_env args sz s))) /\
   (!env b (s:(C,FFI)data_state).
      option_le (data_state_stack_max s) (data_state_stack_max (data_push_env env b s))) /\
   (!(s:(C,FFI)data_state) t.
      data_pop_env s = SOME t ==> data_state_stack_max t = data_state_stack_max s) /\
   (!(s:(C,FFI)data_state) t.
      data_jump_exc s = SOME t ==> data_state_stack_max t = data_state_stack_max s) /\
   (!names (s:(C,FFI)data_state) t.
      data_cut_state_opt names s = SOME t ==>
      data_state_stack_max t = data_state_stack_max s)`,
  REWRITE_TAC[DSEMAUX_pop_env_stack_max; DSEMAUX_jump_exc_stack_max; cut_state_opt_stack_max;
              DSEMAUX_push_env_stack_max; option_le_max_right; option_le_refl] THEN
  REWRITE_TAC[data_call_env_def; LET_DEF; LET_END_DEF; data_state_INFO.ri_accfupds; K_THM;
              option_le_max_right; option_le_refl]);;

let DSEMAUX_SMX_RWS =
  [data_set_var_def; data_set_vars_def; data_flush_state_def; data_dec_clock_def;
   install_sfs_def; add_space_def; data_call_env_def; LET_DEF; LET_END_DEF;
   DSEMAUX_push_env_stack_max; option_le_max; data_state_INFO.ri_accfupds; K_THM];;

let DSEMAUX_SMX_CLAUSE_TAC : tactic =
  REPEAT GEN_TAC THEN
  (fun (asl,w as g) ->
     let a,_ = dest_imp w in
     if DSEMAUX_is_main_hyp a then ALL_TAC g
     else (DISCH_THEN STRIP_ASSUME_TAC THEN REPEAT GEN_TAC) g) THEN
  DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE DSEMAUX_EVAL_CASE_EQS o
             ONCE_REWRITE_RULE[data_evaluate_def]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN DSEMAUX_SPLIT_CONJ_ASMS THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IS_SOME_DEF]) THEN
  DSEMAUX_CK_SIMP_ASMS THEN TRY (FIRST_ASSUM CONTR_TAC) THEN REPEAT DSEMAUX_CK_RES_TAC THEN
  MAP_EVERY (fun th -> TRY (DSEMAUX_FULL_RES_TAC th))
            (do_app_stack_max :: CONJUNCTS DSEMAUX_smx_imps) THEN
  RULE_ASSUM_TAC (REWRITE_RULE DSEMAUX_SMX_RWS) THEN DSEMAUX_SPLIT_CONJ_ASMS THEN
  REWRITE_TAC DSEMAUX_SMX_RWS THEN ASM_REWRITE_TAC[option_le_refl; option_le_max_right] THEN
  ASM_MESON_TAC[option_le_trans; option_le_refl; DSEMAUX_smx_imps];;

let evaluate_option_le_stack_max = prove
 (`!c2 (s:(C,FFI)data_state) res s1.
     data_evaluate (c2,s) = (res,s1) ==>
     option_le (data_state_stack_max s) (data_state_stack_max s1)`,
  SUBGOAL_THEN
   `!p (res:((data_v list,data_v)result)option) (s1:(C,FFI)data_state).
      data_evaluate p = (res,s1) ==>
      option_le (data_state_stack_max (SND p)) (data_state_stack_max s1)`
   (fun th -> MESON_TAC[th; SND]) THEN
  MATCH_MP_TAC data_evaluate_ind THEN REWRITE_TAC[FST; SND] THEN REPEAT CONJ_TAC THEN
  DSEMAUX_SMX_CLAUSE_TAC);;

(* defined this way to allow s and t to have different types *)
let cc_co_only_diff_def = cake_def
  `cc_co_only_diff (s:(C,FFI)data_state) (t:(D,FFI)data_state) <=>
     data_state_locals s = data_state_locals t /\
     data_state_locals_size s = data_state_locals_size t /\
     data_state_stack s = data_state_stack t /\
     data_state_stack_max s = data_state_stack_max t /\
     data_state_stack_frame_sizes s = data_state_stack_frame_sizes t /\
     data_state_global s = data_state_global t /\
     data_state_handler s = data_state_handler t /\
     data_state_refs s = data_state_refs t /\
     data_state_clock s = data_state_clock t /\
     data_state_code s = data_state_code t /\
     data_state_ffi s = data_state_ffi t /\
     data_state_space s = data_state_space t /\
     data_state_tstamps s = data_state_tstamps t /\
     data_state_limits s = data_state_limits t /\
     data_state_safe_for_space s = data_state_safe_for_space t /\
     data_state_peak_heap_length s = data_state_peak_heap_length t`;;

(* the accessors of t as the accessors of s *)

let DSEMAUX_CC_ASM_TAC : tactic =
  FIRST_X_ASSUM (fun th ->
    if (try fst(dest_const(fst(strip_comb(concl th)))) = "cc_co_only_diff"
        with Failure _ -> false)
    then ASSUME_TAC th THEN
         MAP_EVERY (ASSUME_TAC o GSYM) (CONJUNCTS (REWRITE_RULE[cc_co_only_diff_def] th))
    else NO_TAC);;

let DSEMAUX_space_consumed_limits = prove
 (`!(s:(C,FFI)data_state) op vs (t:(D,FFI)data_state).
     data_state_limits t = data_state_limits s ==>
     space_consumed t op vs = space_consumed s op vs`,
  MATCH_MP_TAC space_consumed_ind THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[space_consumed_def] THEN ASM_REWRITE_TAC[]);;

let DSEMAUX_CC_RWS =
  [size_of_heap_def; size_of_heap_args_def; stack_to_vs_def];;

(*fs[] is slower than full_simp_tac(srw_ss())[]*)
let do_app_cc_co_only_diff_rval = prove
 (`!op vs (s:(C,FFI)data_state) v s1 (t:(D,FFI)data_state).
     data_do_app op vs s = Rval (v,s1) /\ data_state_safe_for_space s1 /\
     cc_co_only_diff s t ==>
     ?t1. data_do_app op vs t = Rval (v,t1) /\ cc_co_only_diff s1 t1`,
  X_GEN_TAC `op:clos_op` THEN DSEMAUX_OP_CASES_TAC `op:clos_op` THEN
  REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
  DSEMAUX_CC_ASM_TAC THEN
  FIRST_ASSUM (fun th -> if (try fst(dest_const(rator(lhs(concl th)))) = "data_state_limits"
                             with Failure _ -> false)
                         then ASSUME_TAC (GEN_ALL (MATCH_MP DSEMAUX_space_consumed_limits th))
                         else NO_TAC) THEN
  CASE_REWRITE_TAC (DSEMAUX_CC_RWS @ DSEMAUX_DO_APP_DEFS) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  CASE_REWRITE_TAC DSEMAUX_DO_APP_RWS THEN ASM_REWRITE_TAC[] THEN
  REPEAT ((COND_CASES_TAC ORELSE TOP_CASE_TAC) THEN CASE_REWRITE_TAC DSEMAUX_DO_APP_RWS THEN
          ASM_REWRITE_TAC[]) THEN
  REWRITE_TAC[injectivity "result"; distinctness "result"; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[GSYM CONJ_ASSOC; RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
  RULE_ASSUM_TAC (REWRITE_RULE DSEMAUX_FINISH_RWS) THEN TRY (FIRST_ASSUM CONTR_TAC) THEN
  ASM_REWRITE_TAC(cc_co_only_diff_def :: DSEMAUX_FINISH_RWS));;

let do_app_cc_co_only_diff_rerr = prove
 (`!op vs (s:(C,FFI)data_state) r (t:(D,FFI)data_state).
     data_do_app op vs s = Rerr r /\ ~(op = clos_Install) /\ cc_co_only_diff s t ==>
     data_do_app op vs t = Rerr r`,
  X_GEN_TAC `op:clos_op` THEN DSEMAUX_OP_CASES_TAC `op:clos_op` THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN (CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
  DSEMAUX_CC_ASM_TAC THEN
  FIRST_ASSUM (fun th -> if (try fst(dest_const(rator(lhs(concl th)))) = "data_state_limits"
                             with Failure _ -> false)
                         then ASSUME_TAC (GEN_ALL (MATCH_MP DSEMAUX_space_consumed_limits th))
                         else NO_TAC) THEN
  CASE_REWRITE_TAC (DSEMAUX_CC_RWS @ DSEMAUX_DO_APP_DEFS) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  CASE_REWRITE_TAC DSEMAUX_DO_APP_RWS THEN ASM_REWRITE_TAC[] THEN
  REPEAT ((COND_CASES_TAC ORELSE TOP_CASE_TAC) THEN CASE_REWRITE_TAC DSEMAUX_DO_APP_RWS THEN
          ASM_REWRITE_TAC[]) THEN
  REWRITE_TAC[injectivity "result"; distinctness "result"; PAIR_EQ]);;

let pop_env_safe_for_space = prove
 (`!(s2:(C,FFI)data_state) s1.
     data_pop_env s2 = SOME s1 ==> data_state_safe_for_space s1 = data_state_safe_for_space s2`,
  REWRITE_TAC[DSEMAUX_safe_imps]);;

let pop_env_cc_co_only_diff = prove
 (`!(s2:(C,FFI)data_state) (t2:(D,FFI)data_state) s1.
     cc_co_only_diff s2 t2 /\ data_pop_env s2 = SOME s1 ==>
     ?t1. data_pop_env t2 = SOME t1 /\ cc_co_only_diff s1 t1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cc_co_only_diff_def; data_pop_env_def] THEN
  STRIP_TAC THEN POP_ASSUM MP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT TOP_CASE_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN (SUBST1_TAC o SYM) THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM1; data_state_INFO.ri_accfupds; K_THM] THEN
  ASM_REWRITE_TAC[]);;

let cc_co_only_diff_call_env = prove
 (`!(s:(C,FFI)data_state) (t:(D,FFI)data_state) args1 ss x'' b.
     cc_co_only_diff s t ==>
     cc_co_only_diff (data_call_env args1 ss (data_push_env x'' b (data_dec_clock s)))
                     (data_call_env args1 ss (data_push_env x'' b (data_dec_clock t)))`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN
  REWRITE_TAC[cc_co_only_diff_def; data_call_env_def; data_push_env_def; data_dec_clock_def;
              LET_DEF; LET_END_DEF; data_state_INFO.ri_accfupds; K_THM] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;

(* HOL4 [local]: the narrow cut in evaluate (Assign) only depends on locals *)
(* (equal under cc_co_only_diff), so the t-side cut is determined by the    *)
(* s-side cut and preserves cc_co_only_diff                                 *)
let cut_state_opt_cc_co_full = prove
 (`!(s:(C,FFI)data_state) (t:(D,FFI)data_state) names_opt.
     data_state_locals t = data_state_locals s ==>
     data_cut_state_opt names_opt t =
     OPTION_MAP (\u. data_state_locals_fupd (K (data_state_locals u)) t)
                (data_cut_state_opt names_opt s)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[data_cut_state_opt_def; data_cut_state_def] THEN ASM_REWRITE_TAC[] THEN
  REPEAT TOP_CASE_TAC THEN REWRITE_TAC[OPTION_MAP_DEF; option_INJ] THEN
  REWRITE_TAC[data_state_component_equality; data_state_INFO.ri_accfupds; K_THM] THEN
  ASM_REWRITE_TAC[]);;

(* HOL4 [local] *)
let cut_cc_co = prove
 (`!(s:(C,FFI)data_state) (t:(D,FFI)data_state) names_opt s1.
     cc_co_only_diff s t /\ data_cut_state_opt names_opt s = SOME s1 ==>
     ?t1. data_cut_state_opt names_opt t = SOME t1 /\ cc_co_only_diff s1 t1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `data_state_locals (t:(D,FFI)data_state) = data_state_locals (s:(C,FFI)data_state)`
    (fun th -> REWRITE_TAC[MATCH_MP cut_state_opt_cc_co_full th]) THENL
   [ASM_MESON_TAC[cc_co_only_diff_def]; ALL_TAC] THEN
  ASM_REWRITE_TAC[OPTION_MAP_DEF; option_INJ; RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
  UNDISCH_TAC `data_cut_state_opt names_opt (s:(C,FFI)data_state) = SOME s1` THEN
  UNDISCH_TAC `cc_co_only_diff (s:(C,FFI)data_state) (t:(D,FFI)data_state)` THEN
  REWRITE_TAC[cc_co_only_diff_def; data_cut_state_opt_def; data_cut_state_def] THEN
  STRIP_TAC THEN REPEAT TOP_CASE_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN (SUBST1_TAC o SYM) THEN
  REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM] THEN ASM_REWRITE_TAC[]);;

(* jump_exc under cc_co_only_diff *)

let DSEMAUX_jump_exc_cc = prove
 (`!(s:(C,FFI)data_state) (t:(D,FFI)data_state).
     cc_co_only_diff s t ==>
     (data_jump_exc s = NONE ==> data_jump_exc t = NONE) /\
     (!s2. data_jump_exc s = SOME s2 ==>
           ?t2. data_jump_exc t = SOME t2 /\ cc_co_only_diff s2 t2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM (MP_TAC o REWRITE_RULE[cc_co_only_diff_def]) THEN
  STRIP_TAC THEN REWRITE_TAC[data_jump_exc_def] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THEN REPEAT (COND_CASES_TAC ORELSE TOP_CASE_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN TRY(FIRST_ASSUM CONTR_TAC) THEN
  REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN
  REWRITE_TAC[UNWIND_THM1; cc_co_only_diff_def; data_state_INFO.ri_accfupds; K_THM] THEN
  ASM_REWRITE_TAC[]);;

(* every cc_co_only_diff assumption as the equations of the t-fields *)

let DSEMAUX_is_cc th =
  try fst(dest_const(fst(strip_comb(concl th)))) = "cc_co_only_diff" with Failure _ -> false;;

let DSEMAUX_CC_FIELDS_TAC : tactic = fun (asl,w as g) ->
  let ccs = filter DSEMAUX_is_cc (map snd asl) in
  let eqs = flat (map (fun th -> map GSYM (CONJUNCTS (REWRITE_RULE[cc_co_only_diff_def] th))) ccs) in
  let eqs = filter (fun th -> not (exists (fun (_,a) -> aconv (concl a) (concl th)) asl)) eqs in
  MAP_EVERY ASSUME_TAC eqs g;;

let DSEMAUX_CC_ACC_RWS =
  [data_set_var_def; data_set_vars_def; data_flush_state_def; data_dec_clock_def;
   install_sfs_def; add_space_def; data_call_env_def; data_push_env_def; LET_DEF; LET_END_DEF;
   size_of_heap_def; stack_to_vs_def; data_state_INFO.ri_accfupds; K_THM; IS_SOME_DEF];;

let DSEMAUX_CC_PROVE_TAC : tactic =
  DSEMAUX_CC_FIELDS_TAC THEN
  REWRITE_TAC (cc_co_only_diff_def :: DSEMAUX_CC_ACC_RWS) THEN
  ASM_REWRITE_TAC DSEMAUX_CC_ACC_RWS;;


let DSEMAUX_is_D_eval t =
  is_comb t && (try fst(dest_const(rator t)) = "data_evaluate" with Failure _ -> false) &&
  is_pair (rand t) && type_of (snd (dest_pair (rand t))) = `:(D,FFI)data_state`;;

let DSEMAUX_CC_IH_TAC : tactic = fun (asl,w as g) ->
  let targets = filter (fun tg -> free_in tg w) (find_terms DSEMAUX_is_D_eval w) in
  let try_one tg =
    let p,st = dest_pair (rand tg) in
    tryfind (fun (_,th) ->
      let vs,body = strip_forall (concl th) in
      if length vs <> 1 || not (is_imp body) then failwith "" else
      let _,ex = dest_imp body in
      let _,eqs = strip_exists ex in
      let eq = fst (dest_conj eqs) in
      let p',_ = dest_pair (rand (lhs eq)) in
      if p' <> p then failwith "" else SPEC st th) asl in
  let ith = tryfind try_one targets in
  let evs,_ = strip_exists (snd (dest_imp (concl ith))) in
  let avoid = freesl (w :: map (concl o snd) asl) in
  let fresh = rev(itlist (fun v acc -> variant (acc @ avoid) v :: acc) (rev evs) []) in
  (MP_TAC ith THEN
   ANTS_TAC THENL
    [FIRST [FIRST_ASSUM ACCEPT_TAC;
            MATCH_MP_TAC cc_co_only_diff_call_env THEN FIRST_ASSUM ACCEPT_TAC;
            DSEMAUX_CC_PROVE_TAC];
     ALL_TAC] THEN
   MAP_EVERY (fun v -> DISCH_THEN(X_CHOOSE_THEN v MP_TAC)) fresh THEN
   DISCH_THEN (fun th -> STRIP_ASSUME_TAC th THEN REWRITE_TAC[CONJUNCT1 th])) g;;

let DSEMAUX_cut_cc_none = prove
 (`!(s:(C,FFI)data_state) (t:(D,FFI)data_state) names_opt.
     cc_co_only_diff s t /\ data_cut_state_opt names_opt s = NONE ==>
     data_cut_state_opt names_opt t = NONE`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `data_state_locals (t:(D,FFI)data_state) = data_state_locals (s:(C,FFI)data_state)`
    (fun th -> ASM_REWRITE_TAC[MATCH_MP cut_state_opt_cc_co_full th; OPTION_MAP_DEF]) THEN
  ASM_MESON_TAC[cc_co_only_diff_def]);;

let DSEMAUX_pop_env_cc_none = prove
 (`!(s:(C,FFI)data_state) (t:(D,FFI)data_state).
     cc_co_only_diff s t ==> data_pop_env s = NONE ==> data_pop_env t = NONE`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cc_co_only_diff_def] THEN STRIP_TAC THEN
  REWRITE_TAC[data_pop_env_def] THEN ASM_REWRITE_TAC[] THEN
  REPEAT TOP_CASE_TAC THEN REWRITE_TAC[option_DISTINCT]);;

(* the t-side facts: jump_exc, cut_state_opt, pop_env and do_app *)

let DSEMAUX_CC_FACTS_TAC : tactic =
  TRY (FIRST_ASSUM (fun th -> if DSEMAUX_is_cc th && is_var (rand (rator (concl th)))
                              then MP_TAC (MATCH_MP DSEMAUX_jump_exc_cc th) else NO_TAC) THEN
       DISCH_THEN (CONJUNCTS_THEN2
         (fun th -> TRY (FIRST_ASSUM (ASSUME_TAC o MATCH_MP th)))
         (fun th -> TRY (FIRST_ASSUM (STRIP_ASSUME_TAC o MATCH_MP th))))) THEN
  TRY (IMP_RES_THEN STRIP_ASSUME_TAC cut_cc_co) THEN
  TRY (IMP_RES_THEN ASSUME_TAC DSEMAUX_cut_cc_none) THEN
  TRY (IMP_RES_THEN STRIP_ASSUME_TAC pop_env_cc_co_only_diff) THEN
  TRY (IMP_RES_THEN ASSUME_TAC DSEMAUX_pop_env_cc_none) THEN
  TRY (IMP_RES_THEN STRIP_ASSUME_TAC do_app_cc_co_only_diff_rval) THEN
  TRY (IMP_RES_THEN ASSUME_TAC do_app_cc_co_only_diff_rerr);;

(* IMP_RES_TAC that adds only new fully resolved facts, failing otherwise *)

let DSEMAUX_NEW_RES_TAC (th:thm) : tactic = fun (asl,w as g) ->
  let news = ref [] in
  let collect t = if is_imp (snd (strip_forall (concl t))) ||
                     exists (fun (_,a) -> aconv (concl a) (concl t)) asl ||
                     exists (fun a -> aconv (concl a) (concl t)) (!news)
                  then ALL_TAC else (news := t :: !news; ALL_TAC) in
  let _ = try ignore (IMP_RES_THEN collect th g) with Failure _ -> () in
  if !news = [] then failwith "DSEMAUX_NEW_RES_TAC"
  else MAP_EVERY STRIP_ASSUME_TAC (!news) g;;

let DSEMAUX_safe_dir = prove
 (`(!(s:(C,FFI)data_state) t.
      data_pop_env s = SOME t /\ data_state_safe_for_space t ==> data_state_safe_for_space s) /\
   (!(s:(C,FFI)data_state) t.
      data_jump_exc s = SOME t /\ data_state_safe_for_space t ==> data_state_safe_for_space s) /\
   (!names (s:(C,FFI)data_state) t.
      data_cut_state_opt names s = SOME t /\ data_state_safe_for_space t ==>
      data_state_safe_for_space s)`,
  MESON_TAC[DSEMAUX_safe_eqs]);;

(* DSEMAUX_NEW_RES_TAC with the resolvents simplified (and split) before  *)
(* the novelty check, so that it terminates when the assumptions are kept  *)
(* simplified                                                              *)

let DSEMAUX_NEW_RES_SIMP_TAC (simp:thm->thm) (th:thm) : tactic = fun (asl,w as g) ->
  let news = ref [] in
  let known t = t = `T` || exists (fun (_,a) -> aconv (concl a) t) asl ||
                exists (fun a -> aconv (concl a) t) (!news) in
  let collect r =
    (if is_imp (snd (strip_forall (concl r))) then () else
     do_list (fun c -> if known (concl c) then () else news := c :: !news)
             (CONJUNCTS (simp r)));
    ALL_TAC in
  let _ = try ignore (IMP_RES_THEN collect th g) with Failure _ -> () in
  if !news = [] then failwith "DSEMAUX_NEW_RES_SIMP_TAC"
  else MAP_EVERY ASSUME_TAC (rev (!news)) g;;

(* backward propagation of safe_for_space through a clause *)

let DSEMAUX_SAFE_PROP_TAC : tactic =
  RULE_ASSUM_TAC (REWRITE_RULE DSEMAUX_SAFE_RWS) THEN DSEMAUX_SPLIT_CONJ_ASMS THEN
  REPEAT (FIRST (map (DSEMAUX_NEW_RES_SIMP_TAC (REWRITE_RULE DSEMAUX_SAFE_RWS))
                     (evaluate_safe_for_space_mono :: CONJUNCTS DSEMAUX_safe_dir)));;

let DSEMAUX_CC_CLAUSE_TAC : tactic =
  REPEAT GEN_TAC THEN
  (fun (asl,w as g) ->
     let a,_ = dest_imp w in
     if DSEMAUX_is_main_hyp a then ALL_TAC g
     else (DISCH_THEN STRIP_ASSUME_TAC THEN REPEAT GEN_TAC) g) THEN
  DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE DSEMAUX_EVAL_CASE_EQS o
             ONCE_REWRITE_RULE[data_evaluate_def]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN DSEMAUX_SPLIT_CONJ_ASMS THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IS_SOME_DEF]) THEN DSEMAUX_F_HANDLER_TAC THEN
  DSEMAUX_CK_SIMP_ASMS THEN TRY (FIRST_ASSUM CONTR_TAC) THEN
  DISCH_TAC THEN X_GEN_TAC `t:(D,FFI)data_state` THEN DISCH_TAC THEN
  (* safe facts for the results of the sub-evaluations *)
  DSEMAUX_SAFE_PROP_TAC THEN
  REPEAT DSEMAUX_CK_RES_TAC THEN
  DSEMAUX_CC_FIELDS_TAC THEN DSEMAUX_CC_FACTS_TAC THEN
  ONCE_REWRITE_TAC[data_evaluate_def] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT (CHANGED_TAC (CASE_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
                       ASM_REWRITE_TAC[PAIR_EQ; IS_SOME_DEF]) ORELSE
          (DSEMAUX_CC_IH_TAC THEN DSEMAUX_CC_FIELDS_TAC THEN DSEMAUX_CC_FACTS_TAC)) THEN
  REWRITE_TAC[PAIR_EQ; RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
  DSEMAUX_CC_PROVE_TAC;;

let DSEMAUX_CC_GOAL =
 `!p (res:((data_v list,data_v)result)option) (s1:(C,FFI)data_state).
     data_evaluate p = (res,s1) ==> data_state_safe_for_space s1 ==>
     !t:(D,FFI)data_state. cc_co_only_diff (SND p) t ==>
       ?t1. data_evaluate (FST p,t) = (res,t1) /\ cc_co_only_diff s1 t1`;;

let evaluate_cc_co_only_diff = prove
 (`!prog (s:(C,FFI)data_state) res s1 (t:(D,FFI)data_state).
     data_evaluate (prog,s) = (res,s1) /\ data_state_safe_for_space s1 /\
     cc_co_only_diff s t ==>
     ?t1. data_evaluate (prog,t) = (res,t1) /\ cc_co_only_diff s1 t1`,
  SUBGOAL_THEN DSEMAUX_CC_GOAL
   (fun th -> REPEAT GEN_TAC THEN
              MP_TAC (SPECL [`(prog:data_prog,s:(C,FFI)data_state)`;
                             `res:((data_v list,data_v)result)option`;
                             `s1:(C,FFI)data_state`] th) THEN
              REWRITE_TAC[FST; SND] THEN MESON_TAC[]) THEN
  MATCH_MP_TAC data_evaluate_ind THEN REWRITE_TAC[FST; SND] THEN REPEAT CONJ_TAC THEN
  DSEMAUX_CC_CLAUSE_TAC);;

let data_evaluate_stack_limit = prove
 (`!c2 (s:(C,FFI)data_state) res s1.
     data_evaluate (c2,s) = (res,s1) ==>
     limits_stack_limit (data_state_limits s1) = limits_stack_limit (data_state_limits s)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM (MP_TAC o SPEC `data_state_limits (s:(C,FFI)data_state)` o
               MATCH_MP evaluate_swap_limits) THEN
  REWRITE_TAC[DSEMAUX_fupd_id] THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN (X_CHOOSE_THEN `smx:num option` (X_CHOOSE_THEN `safe:bool`
    (X_CHOOSE_THEN `peak:num`
       (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [th])))) THEN
  REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM]);;

(* TODO: move *)
let the_le_IMP_option_le = prove
 (`!n m. misc_the F (OPTION_MAP ((>) n) m) ==> option_le m (SOME n)`,
  GEN_TAC THEN MATCH_MP_TAC option_INDUCT THEN
  REWRITE_TAC[OPTION_MAP_DEF; misc_the_def; option_le_def] THEN ARITH_TAC);;

(*fs[] is slower than full_simp_tac(srw_ss())[]*)
let do_app_stack_max_le_stack_limit = prove
 (`!op xs (s:(C,FFI)data_state) res s1.
     data_do_app op xs s = Rval (res,s1) /\ data_state_safe_for_space s1 /\
     option_le (data_state_stack_max s) (SOME (limits_stack_limit (data_state_limits s))) ==>
     option_le (data_state_stack_max s1) (SOME (limits_stack_limit (data_state_limits s1)))`,
  X_GEN_TAC `op:clos_op` THEN DSEMAUX_OP_CASES_TAC `op:clos_op` THEN
  REPEAT GEN_TAC THEN CASE_REWRITE_TAC DSEMAUX_DO_APP_DEFS THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  CASE_REWRITE_TAC DSEMAUX_DO_APP_RWS THEN
  REPEAT ((COND_CASES_TAC ORELSE TOP_CASE_TAC) THEN CASE_REWRITE_TAC DSEMAUX_DO_APP_RWS) THEN
  REWRITE_TAC[injectivity "result"; distinctness "result"; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC (REWRITE_RULE DSEMAUX_FINISH_RWS) THEN DSEMAUX_SPLIT_CONJ_ASMS THEN
  TRY (FIRST_ASSUM CONTR_TAC) THEN
  IMP_RES_TAC the_le_IMP_option_le THEN
  RULE_ASSUM_TAC (REWRITE_RULE [option_le_max]) THEN DSEMAUX_SPLIT_CONJ_ASMS THEN
  ASM_REWRITE_TAC (option_le_max :: DSEMAUX_FINISH_RWS));;

(* evaluate_stack_max_le_stack_limit: helpers *)

let DSEMAUX_lim_imps = prove
 (`(!(s:(C,FFI)data_state) t.
      data_pop_env s = SOME t ==> data_state_limits t = data_state_limits s) /\
   (!(s:(C,FFI)data_state) t.
      data_jump_exc s = SOME t ==> data_state_limits t = data_state_limits s) /\
   (!names (s:(C,FFI)data_state) t.
      data_cut_state_opt names s = SOME t ==> data_state_limits t = data_state_limits s)`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[data_pop_env_def; data_jump_exc_def; data_cut_state_opt_def;
              data_cut_state_def] THEN
  REPEAT (COND_CASES_TAC ORELSE TOP_CASE_TAC) THEN
  REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN (SUBST1_TAC o SYM) THEN REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM]);;

let DSEMAUX_SL_RWS =
  [data_set_var_def; data_set_vars_def; data_flush_state_def; install_sfs_def;
   data_dec_clock_def; add_space_def; data_call_env_def; DSEMAUX_push_env_stack_max;
   DSEMAUX_push_env_acc; DSEMAUX_push_env_safe; LET_DEF; LET_END_DEF;
   data_state_INFO.ri_accfupds; K_THM; option_le_max];;

let DSEMAUX_is_sl_eq tm =
  is_eq tm &&
  (let l = lhs tm and r = rhs tm in
   is_comb l && is_comb r && is_var (rand l) && is_var (rand r) && rator l = rator r &&
   (try let c = fst(dest_const(rator l)) in
        c = "data_state_stack_max" || c = "data_state_limits"
    with Failure _ -> false));;

let DSEMAUX_sl_eqs (asl:(string*thm) list) =
  filter (fun th -> DSEMAUX_is_sl_eq (concl th)) (map snd asl);;

let DSEMAUX_do_app_sl = REWRITE_RULE[IMP_CONJ] do_app_stack_max_le_stack_limit;;

(* forward chaining: resolvents simplified with the clause rewrites and *)
(* the stack_max and limits equations among the assumptions             *)

let DSEMAUX_SL_RES_TAC : tactic = fun (asl,w) ->
  let ths = map snd asl in
  let eqs = DSEMAUX_sl_eqs asl in
  let simp = REWRITE_RULE (DSEMAUX_CK_SIMP_RWS @ DSEMAUX_SL_RWS @ eqs) in
  let imps = filter (fun th -> let _,b = strip_forall (concl th) in is_imp b)
               (the_le_IMP_option_le :: DSEMAUX_do_app_sl :: ths) in
  let new_ths = flat (map (fun ith -> mapfilter (fun th -> simp (MATCH_MP ith th)) ths)
                          imps) in
  let new_ths = flat (map CONJUNCTS new_ths) in
  let new_ths = filter (fun th -> not (exists (fun t -> aconv (concl t) (concl th)) ths) &&
                                  not (concl th = `T`)) new_ths in
  let rec nub l = match l with [] -> [] | h::t ->
    h :: nub (filter (fun x -> not (aconv (concl x) (concl h))) t) in
  let new_ths = nub new_ths in
  if new_ths = [] then failwith "DSEMAUX_SL_RES_TAC" else MAP_EVERY ASSUME_TAC new_ths (asl,w);;

let DSEMAUX_SL_SIMP_ASMS : tactic = fun (asl,w as g) ->
  let eqs = DSEMAUX_sl_eqs asl in
  RULE_ASSUM_TAC (fun th -> if DSEMAUX_is_sl_eq (concl th) then th
                            else REWRITE_RULE (DSEMAUX_SL_RWS @ eqs) th) g;;

let DSEMAUX_SL_CLAUSE_TAC : tactic =
  REPEAT GEN_TAC THEN
  (fun (asl,w as g) ->
     let a,_ = dest_imp w in
     if DSEMAUX_is_main_hyp a then ALL_TAC g
     else (DISCH_THEN STRIP_ASSUME_TAC THEN REPEAT GEN_TAC) g) THEN
  DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE DSEMAUX_EVAL_CASE_EQS o
             ONCE_REWRITE_RULE[data_evaluate_def]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN DSEMAUX_SPLIT_CONJ_ASMS THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IS_SOME_DEF]) THEN DSEMAUX_F_HANDLER_TAC THEN
  DSEMAUX_CK_SIMP_ASMS THEN TRY (FIRST_ASSUM CONTR_TAC) THEN
  DISCH_TAC THEN DISCH_TAC THEN
  DSEMAUX_SAFE_PROP_TAC THEN
  MAP_EVERY (fun th -> TRY (DSEMAUX_FULL_RES_TAC th))
            (CONJUNCTS DSEMAUX_lim_imps @ tl (tl (CONJUNCTS DSEMAUX_smx_imps))) THEN
  REPEAT (DSEMAUX_NEW_RES_TAC data_evaluate_stack_limit) THEN
  DSEMAUX_SL_SIMP_ASMS THEN DSEMAUX_SPLIT_CONJ_ASMS THEN
  REPEAT DSEMAUX_SL_RES_TAC THEN
  (fun (asl,w as g) -> REWRITE_TAC (DSEMAUX_SL_RWS @ DSEMAUX_sl_eqs asl) g) THEN
  ASM_REWRITE_TAC[option_le_refl] THEN
  TRY (FIRST_ASSUM CONTR_TAC) THEN
  ASM_MESON_TAC[option_le_trans];;

let DSEMAUX_SL_GOAL =
 `!p (res:((data_v list,data_v)result)option) (s1:(C,FFI)data_state).
    data_evaluate p = (res,s1) ==> data_state_safe_for_space s1 ==>
    option_le (data_state_stack_max (SND p))
              (SOME (limits_stack_limit (data_state_limits (SND p)))) ==>
    option_le (data_state_stack_max s1) (SOME (limits_stack_limit (data_state_limits s1)))`;;

let evaluate_stack_max_le_stack_limit = prove
 (`!prog (s:(C,FFI)data_state) res s1.
     data_evaluate (prog,s) = (res,s1) /\ data_state_safe_for_space s1 /\
     option_le (data_state_stack_max s) (SOME (limits_stack_limit (data_state_limits s))) ==>
     option_le (data_state_stack_max s1) (SOME (limits_stack_limit (data_state_limits s1)))`,
  SUBGOAL_THEN DSEMAUX_SL_GOAL
   (fun th -> REPEAT GEN_TAC THEN
              MP_TAC (SPECL [`(prog:data_prog,s:(C,FFI)data_state)`;
                             `res:((data_v list,data_v)result)option`;
                             `s1:(C,FFI)data_state`] th) THEN
              REWRITE_TAC[FST; SND] THEN MESON_TAC[]) THEN
  MATCH_MP_TAC data_evaluate_ind THEN REWRITE_TAC[FST; SND] THEN REPEAT CONJ_TAC THEN
  DSEMAUX_SL_CLAUSE_TAC);;
