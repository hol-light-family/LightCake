(* ========================================================================= *)
(* data_liveProof: port of HOL4 compiler/backend/proofs/                     *)
(* data_liveProofScript.sml (CakeML v3479).  Correctness proof for           *)
(* data_live.  DATAPAUX_ names are local helpers (not HOL4 names).           *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/data_live.ml";;
needs "compiler/backend/semantics/dataSem.ml";;
needs "compiler/backend/semantics/dataProps.ml";;

type_invention_error := true;;

(* HOL4 [local] *)
let SPLIT_PAIR = prove
 (`!(x:A#B) y z. x = (y,z) <=> y = FST x /\ z = SND x`,
  GEN_TAC THEN
  MP_TAC(ISPEC `x:A#B` PAIR_SURJECTIVE) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[PAIR_EQ; FST; SND] THEN MESON_TAC[]);;

let data_liveProof_state_rel_def = cake_def
  `data_liveProof_state_rel (s1:(C,FFI)data_state) (t1:(C,FFI)data_state)
                            (live:num_set) <=>
     data_state_code s1 = data_state_code t1 /\
     data_state_clock s1 = data_state_clock t1 /\
     data_state_space s1 = data_state_space t1 /\
     data_state_ffi s1 = data_state_ffi t1 /\
     data_state_refs s1 = data_state_refs t1 /\
     data_state_global s1 = data_state_global t1 /\
     data_state_handler s1 = data_state_handler t1 /\
     LENGTH (data_state_stack s1) = LENGTH (data_state_stack t1) /\
     data_state_compile s1 = data_state_compile t1 /\
     data_state_compile_oracle s1 = data_state_compile_oracle t1 /\
     data_state_tstamps s1 = data_state_tstamps t1 /\
     data_state_limits s1 = data_state_limits t1 /\
     data_state_stack_frame_sizes s1 = data_state_stack_frame_sizes t1 /\
     (!x. x IN domain live ==>
          lookup x (data_state_locals s1) = lookup x (data_state_locals t1))`;;

(* HOL4 [local] *)
let state_rel_ID = prove
 (`!(s:(C,FFI)data_state) live. data_liveProof_state_rel s s live`,
  REWRITE_TAC[data_liveProof_state_rel_def]);;

(* HOL4 [local] *)
let jump_exc_IMP_state_rel = prove
 (`!(s1:(C,FFI)data_state) t1 s2 t2.
     data_jump_exc s1 = SOME s2 /\ data_jump_exc t1 = SOME t2 /\
     data_liveProof_state_rel s1 t1 LN /\
     LENGTH (data_state_stack s2) = LENGTH (data_state_stack t2) ==>
     data_liveProof_state_rel
       (data_state_handler_fupd (K (data_state_handler s1)) s2)
       (data_state_handler_fupd (K (data_state_handler t1)) t2) LN`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_jump_exc_def] THEN
  EVERY_CASE_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  FS[data_liveProof_state_rel_def]);;

(* do_app_aux and do_app do not look at the fields that state_rel leaves  *)
(* free (locals, locals_size, stack, stack_max), up to the safe_for_space,  *)
(* peak_heap_length and stack_max fields they compute (HOL4 proves the      *)
(* lemmas below by cases on the operator; so do these frame lemmas)        *)

let DATAPAUX_LIVE_do_app_aux_frame = prove
 (`!op vs (s:(C,FFI)data_state) l lss stk smx.
     data_do_app_aux op vs
       (data_state_locals_fupd (K l) (data_state_locals_size_fupd (K lss)
          (data_state_stack_fupd (K stk) (data_state_stack_max_fupd (K smx) s)))) =
     map_result
       (\(x,y). (x,data_state_locals_fupd (K l) (data_state_locals_size_fupd (K lss)
                     (data_state_stack_fupd (K stk) (data_state_stack_max_fupd (K smx) y)))))
       I (data_do_app_aux op vs s)`,
  DSEMAUX_DO_APP_TAC [data_do_app_aux_def; with_fresh_ts_def; check_lim_def;
                      LET_DEF; LET_END_DEF]);;

let DATAPAUX_LIVE_do_app_frame = prove
 (`!op vs (s:(C,FFI)data_state) q s' l lss stk smx safe peak.
     data_do_app op vs s = Rval (q,s') ==>
     ?safe' peak' smx'.
       data_do_app op vs
         (data_state_locals_fupd (K l) (data_state_locals_size_fupd (K lss)
            (data_state_stack_fupd (K stk) (data_state_stack_max_fupd (K smx)
               (data_state_safe_for_space_fupd (K safe)
                  (data_state_peak_heap_length_fupd (K peak) s)))))) =
       Rval (q,data_state_locals_fupd (K l) (data_state_locals_size_fupd (K lss)
                 (data_state_stack_fupd (K stk) (data_state_stack_max_fupd (K smx')
                    (data_state_safe_for_space_fupd (K safe')
                       (data_state_peak_heap_length_fupd (K peak') s'))))))`,
  DSEMAUX_DO_APP_SWAP_TAC DSEMAUX_DO_APP_DEFS);;

let DATAPAUX_LIVE_do_app_err_frame = prove
 (`!op vs (s:(C,FFI)data_state) e l lss stk smx safe peak.
     data_do_app op vs s = Rerr e ==>
     data_do_app op vs
       (data_state_locals_fupd (K l) (data_state_locals_size_fupd (K lss)
          (data_state_stack_fupd (K stk) (data_state_stack_max_fupd (K smx)
             (data_state_safe_for_space_fupd (K safe)
                (data_state_peak_heap_length_fupd (K peak) s)))))) = Rerr e`,
  DSEMAUX_DO_APP_SWAP_TAC DSEMAUX_DO_APP_DEFS);;

let DATAPAUX_LIVE_do_app_aux_err_frame = prove
 (`!op vs (s:(C,FFI)data_state) e l lss stk smx safe peak.
     data_do_app_aux op vs s = Rerr e ==>
     data_do_app_aux op vs
       (data_state_locals_fupd (K l) (data_state_locals_size_fupd (K lss)
          (data_state_stack_fupd (K stk) (data_state_stack_max_fupd (K smx)
             (data_state_safe_for_space_fupd (K safe)
                (data_state_peak_heap_length_fupd (K peak) s)))))) = Rerr e`,
  DSEMAUX_DO_APP_SWAP_TAC [data_do_app_aux_def; with_fresh_ts_def; check_lim_def;
                           LET_DEF; LET_END_DEF]);;

(* t is s with the fields that state_rel leaves free replaced *)
let DATAPAUX_LIVE_rel_frame = prove
 (`!(s:(C,FFI)data_state) t l.
     data_liveProof_state_rel s t l ==>
     t = data_state_locals_fupd (K (data_state_locals t))
           (data_state_locals_size_fupd (K (data_state_locals_size t))
              (data_state_stack_fupd (K (data_state_stack t))
                 (data_state_stack_max_fupd (K (data_state_stack_max t))
                    (data_state_safe_for_space_fupd (K (data_state_safe_for_space t))
                       (data_state_peak_heap_length_fupd
                          (K (data_state_peak_heap_length t)) s)))))`,
  REWRITE_TAC[data_liveProof_state_rel_def; data_state_component_equality;
              data_state_INFO.ri_accfupds; K_THM] THEN
  MESON_TAC[]);;

(* HOL4 [local] *)
let state_rel_IMP_do_app_aux = prove
 (`!op args (s1:(C,FFI)data_state) v s2 t1 anything.
     data_do_app_aux op args s1 = Rval (v,s2) /\
     data_liveProof_state_rel s1 t1 anything ==>
     data_state_handler s1 = data_state_handler s2 /\
     data_state_stack s1 = data_state_stack s2 /\
     (?safe peak smx lss.
        data_do_app_aux op args t1 =
        Rval (v,data_state_locals_fupd (K (data_state_locals t1))
                  (data_state_locals_size_fupd (K lss)
                     (data_state_stack_fupd (K (data_state_stack t1))
                        (data_state_stack_max_fupd (K smx)
                           (data_state_handler_fupd (K (data_state_handler t1))
                              (data_state_safe_for_space_fupd (K safe)
                                 (data_state_peak_heap_length_fupd (K peak) s2))))))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP data_do_app_aux_const) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP DATAPAUX_LIVE_rel_frame) THEN
  REWRITE_TAC[DATAPAUX_LIVE_do_app_aux_frame] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`data_state_safe_for_space (t1:(C,FFI)data_state)`;
                              `data_state_peak_heap_length (t1:(C,FFI)data_state)`] o
              MATCH_MP do_app_aux_safe_peak_swap) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[map_result_def] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  MAP_EVERY EXISTS_TAC [`safe':bool`; `peak':num`;
                        `data_state_stack_max (t1:(C,FFI)data_state)`;
                        `data_state_locals_size (t1:(C,FFI)data_state)`] THEN
  REWRITE_TAC[injectivity "result"; PAIR_EQ; data_state_component_equality;
              data_state_INFO.ri_accfupds; K_THM] THEN
  FIRST_ASSUM(MP_TAC o last o CONJUNCTS o GEN_REWRITE_RULE I [data_liveProof_state_rel_def]) THEN
  FS[data_liveProof_state_rel_def]);;

(* HOL4 [local] *)
let state_rel_IMP_do_app = prove
 (`!op args (s1:(C,FFI)data_state) v s2 t1 anything.
     data_do_app op args s1 = Rval (v,s2) /\
     data_liveProof_state_rel s1 t1 anything ==>
     data_state_handler s1 = data_state_handler s2 /\
     data_state_stack s1 = data_state_stack s2 /\
     (?safe peak smx lss.
        data_do_app op args t1 =
        Rval (v,data_state_locals_fupd (K (data_state_locals t1))
                  (data_state_locals_size_fupd (K lss)
                     (data_state_stack_fupd (K (data_state_stack t1))
                        (data_state_stack_max_fupd (K smx)
                           (data_state_handler_fupd (K (data_state_handler t1))
                              (data_state_safe_for_space_fupd (K safe)
                                 (data_state_peak_heap_length_fupd (K peak) s2))))))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP data_do_app_const) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP DATAPAUX_LIVE_rel_frame) THEN
  FIRST_ASSUM(MP_TAC o SPECL
    [`data_state_locals (t1:(C,FFI)data_state)`;
     `data_state_locals_size (t1:(C,FFI)data_state)`;
     `data_state_stack (t1:(C,FFI)data_state)`;
     `data_state_stack_max (t1:(C,FFI)data_state)`;
     `data_state_safe_for_space (t1:(C,FFI)data_state)`;
     `data_state_peak_heap_length (t1:(C,FFI)data_state)`] o
    MATCH_MP DATAPAUX_LIVE_do_app_frame) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`safe':bool`; `peak':num`; `smx':num option`;
                        `data_state_locals_size (t1:(C,FFI)data_state)`] THEN
  REWRITE_TAC[injectivity "result"; PAIR_EQ; data_state_component_equality;
              data_state_INFO.ri_accfupds; K_THM] THEN
  FS[data_liveProof_state_rel_def]);;

(* HOL4 [local] *)
let state_rel_IMP_do_app_aux_err = prove
 (`!op args (s1:(C,FFI)data_state) e t1 anything.
     data_do_app_aux op args s1 = Rerr e /\
     data_liveProof_state_rel s1 t1 anything ==>
     data_do_app_aux op args t1 = Rerr e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP DATAPAUX_LIVE_rel_frame) THEN
  MATCH_MP_TAC DATAPAUX_LIVE_do_app_aux_err_frame THEN ASM_REWRITE_TAC[]);;

(* HOL4 [local] *)
let state_rel_IMP_do_app_err = prove
 (`!op args (s1:(C,FFI)data_state) e t1 anything.
     data_do_app op args s1 = Rerr e /\
     data_liveProof_state_rel s1 t1 anything ==>
     data_do_app op args t1 = Rerr e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP DATAPAUX_LIVE_rel_frame) THEN
  MATCH_MP_TAC DATAPAUX_LIVE_do_app_err_frame THEN ASM_REWRITE_TAC[]);;

(* HOL4 [local] *)
let state_rel_IMP_get_vars = prove
 (`!args (s1:(C,FFI)data_state) t1 t xs.
     data_liveProof_state_rel s1 t1 (list_insert args t) /\
     data_get_vars args (data_state_locals s1) = SOME xs ==>
     data_get_vars args (data_state_locals t1) = SOME xs`,
  MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
   [REWRITE_TAC[data_get_vars_def] THEN MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[data_get_vars_def; list_insert_def] THEN
  X_GEN_TAC `h:num` THEN X_GEN_TAC `rest:num list` THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `data_get_var h (data_state_locals (s1:(C,FFI)data_state)) =
                data_get_var h (data_state_locals (t1:(C,FFI)data_state))`
    ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o last o CONJUNCTS o
                GEN_REWRITE_RULE I [data_liveProof_state_rel_def]) THEN
    REWRITE_TAC[data_get_var_def; domain_list_insert; domain_insert; IN_INSERT] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`s1:(C,FFI)data_state`; `t1:(C,FFI)data_state`;
                                `insert h one t`]) THEN
  ASM_REWRITE_TAC[] THEN
  POP_ASSUM(SUBST1_TAC o SYM) THEN
  POP_ASSUM MP_TAC THEN
  TOP_CASE_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
  TOP_CASE_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_THEN(MP_TAC o SPEC `a':data_v list`) THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[option_CASE]);;

(* HOL4 [local] *)
let is_pure_do_app_Rerr_IMP = prove
 (`!op xs (s:(C,FFI)data_state) e.
     data_live_is_pure op /\ data_do_app op xs s = Rerr e ==> Rabort Rtype_error = e`,
  DSEMAUX_DO_APP_IMP_TAC (data_live_is_pure_def :: DSEMAUX_DO_APP_DEFS));;

(* HOL4 [local] *)
let is_pure_do_app_Rval_IMP = prove
 (`!op x (s:(C,FFI)data_state) q r.
     data_live_is_pure op /\ data_do_app op x s = Rval (q,r) ==>
     ?safe smax. r = data_state_stack_max_fupd (K smax)
                       (data_state_safe_for_space_fupd (K safe) s)`,
  DSEMAUX_DO_APP_SWAP_TAC (data_live_is_pure_def :: DSEMAUX_DO_APP_DEFS) THEN
  (* the word operations of either word size *)
  REPEAT (POP_ASSUM MP_TAC) THEN
  STRUCT_CASES_TAC (ISPEC `a0:word_size` (cases "word_size")) THEN
  REWRITE_TAC[data_live_is_pure_def; op_space_req_def] THEN ARITH_TAC);;

(* HOL4 [local] *)
let domain_list_delete = prove
 (`!xs (l:A spt). domain (list_delete xs l) = domain l DIFF set_of_list xs`,
  REWRITE_TAC[EXTENSION; domain_lookup; lookup_list_delete; IN_DIFF; IN_SET_OF_LIST] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT]);;

(* ------------------------------------------------------------------------- *)
(* evaluate_compile: helpers, then one theorem per case of HOL4's recInduct *)
(* proof (its suspend/Resume blocks), and the theorem itself.               *)
(* ------------------------------------------------------------------------- *)

let DATAPAUX_LIVE_rel_lookup = prove
 (`!(s:(C,FFI)data_state) t l x.
     data_liveProof_state_rel s t l /\ x IN domain l ==>
     lookup x (data_state_locals s) = lookup x (data_state_locals t)`,
  REWRITE_TAC[data_liveProof_state_rel_def] THEN MESON_TAC[]);;

let DATAPAUX_LIVE_rel_mono = prove
 (`!(s:(C,FFI)data_state) t l1 l2.
     data_liveProof_state_rel s t l1 /\ domain l2 SUBSET domain l1 ==>
     data_liveProof_state_rel s t l2`,
  REWRITE_TAC[data_liveProof_state_rel_def; SUBSET] THEN MESON_TAC[]);;

let DATAPAUX_LIVE_rel_set_var = prove
 (`!(s:(C,FFI)data_state) t l v x.
     data_liveProof_state_rel s t (delete v l) ==>
     data_liveProof_state_rel (data_set_var v x s) (data_set_var v x t) l`,
  REWRITE_TAC[data_liveProof_state_rel_def; data_set_var_def;
              data_state_INFO.ri_accfupds; K_THM; lookup_insert; domain_delete;
              IN_DELETE] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_MESON_TAC[]);;

let DATAPAUX_LIVE_rel_clock = prove
 (`!(s:(C,FFI)data_state) t l.
     data_liveProof_state_rel s t l ==> data_state_clock t = data_state_clock s`,
  SIMP_TAC[data_liveProof_state_rel_def]);;

let DATAPAUX_LIVE_rel_with_locals = prove
 (`!(s:(C,FFI)data_state) t l l' e1 e2.
     data_liveProof_state_rel s t l' /\
     (!x. x IN domain l ==> lookup x e1 = lookup x e2) ==>
     data_liveProof_state_rel (data_state_locals_fupd (K e1) s)
                              (data_state_locals_fupd (K e2) t) l`,
  REWRITE_TAC[data_liveProof_state_rel_def; data_state_INFO.ri_accfupds; K_THM] THEN
  MESON_TAC[]);;

let DATAPAUX_LIVE_rel_add_space = prove
 (`!(s:(C,FFI)data_state) t l k.
     data_liveProof_state_rel s t l ==>
     data_liveProof_state_rel (add_space s k) (add_space t k) l`,
  REWRITE_TAC[data_liveProof_state_rel_def; add_space_def;
              data_state_INFO.ri_accfupds; K_THM] THEN
  MESON_TAC[]);;

let DATAPAUX_LIVE_rel_do_app_result = prove
 (`!op a (s:(C,FFI)data_state) t l x y lss smx safe peak.
     data_liveProof_state_rel s t l /\ data_do_app op a s = Rval (x,y) ==>
     data_liveProof_state_rel y
       (data_state_locals_fupd (K (data_state_locals t))
          (data_state_locals_size_fupd (K lss)
             (data_state_stack_fupd (K (data_state_stack t))
                (data_state_stack_max_fupd (K smx)
                   (data_state_handler_fupd (K (data_state_handler t))
                      (data_state_safe_for_space_fupd (K safe)
                         (data_state_peak_heap_length_fupd (K peak) y))))))) l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP data_do_app_const) THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  REWRITE_TAC[data_liveProof_state_rel_def; data_state_INFO.ri_accfupds; K_THM] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let DATAPAUX_LIVE_rel_install_sfs = prove
 (`!op (s:(C,FFI)data_state) t l.
     data_liveProof_state_rel s t l ==>
     data_liveProof_state_rel (install_sfs op s) (install_sfs op t) l`,
  REWRITE_TAC[data_liveProof_state_rel_def; install_sfs_def;
              data_state_INFO.ri_accfupds; K_THM] THEN MESON_TAC[]);;

let DATAPAUX_LIVE_rel_flush_state = prove
 (`!b (s:(C,FFI)data_state) t l.
     data_liveProof_state_rel s t l ==>
     data_liveProof_state_rel (data_flush_state b s) (data_flush_state b t) LN`,
  GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN
  REWRITE_TAC[data_liveProof_state_rel_def; data_flush_state_def;
              data_state_INFO.ri_accfupds; K_THM] THEN
  SIMP_TAC[] THEN FS[]);;


(* evaluation on a state whose stack (of the same length), stack_max,      *)
(* safe_for_space and peak_heap_length are replaced: HOL4 uses           *)
(* evaluate_stack_swap and evaluate_smx_safe_peak_swap at each call      *)
let DATAPAUX_LIVE_RECORD_RWS =
  [data_state_INFO.ri_fupdcanon; data_state_INFO.ri_fupdfupds; K_o_THM;
   data_state_INFO.ri_accfupds; K_THM];;

let DATAPAUX_LIVE_swap_rval = prove
 (`!c (S:(C,FFI)data_state) v s2 xs sm sf pk.
     data_evaluate (c,S) = (SOME (Rval v),s2) /\ LENGTH xs = LENGTH (data_state_stack S) ==>
     data_state_stack s2 = data_state_stack S /\
     data_state_handler s2 = data_state_handler S /\
     ?lss sfs smx phl.
       data_evaluate (c,data_state_stack_fupd (K xs)
                          (data_state_stack_max_fupd (K sm)
                             (data_state_safe_for_space_fupd (K sf)
                                (data_state_peak_heap_length_fupd (K pk) S)))) =
       (SOME (Rval v),data_state_locals_size_fupd (K lss)
                        (data_state_stack_fupd (K xs)
                           (data_state_stack_max_fupd (K smx)
                              (data_state_safe_for_space_fupd (K sfs)
                                 (data_state_peak_heap_length_fupd (K phl) s2)))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:data_prog`; `S:(C,FFI)data_state`] data_evaluate_stack_swap) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `xs:stack list`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `lss0:num option` (X_CHOOSE_THEN `sfs0:bool`
    (X_CHOOSE_THEN `smx0:num option` (X_CHOOSE_THEN `phl0:num` ASSUME_TAC)))) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`sm:num option`; `sf:bool`; `pk:num`] o
                MATCH_MP evaluate_smx_safe_peak_swap) THEN
  REWRITE_TAC DATAPAUX_LIVE_RECORD_RWS THEN
  DISCH_THEN(X_CHOOSE_THEN `smx1:num option` (X_CHOOSE_THEN `sf1:bool`
    (X_CHOOSE_THEN `pk1:num` SUBST1_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`lss0:num option`; `sf1:bool`; `smx1:num option`; `pk1:num`] THEN
  REWRITE_TAC[]);;

let DATAPAUX_LIVE_swap_raise = prove
 (`!c (S:(C,FFI)data_state) v s2 xs sm sf pk.
     data_evaluate (c,S) = (SOME (Rerr (Rraise v)),s2) /\
     LENGTH xs = LENGTH (data_state_stack S) ==>
     (?s2'. data_jump_exc S = SOME s2' /\
            data_state_locals s2' = data_state_locals s2 /\
            data_state_stack s2' = data_state_stack s2 /\
            data_state_handler s2' = data_state_handler s2) /\
     (!s7. data_jump_exc (data_state_stack_fupd (K xs) S) = SOME s7 ==>
       ?lss sfs smx phl.
         data_evaluate (c,data_state_stack_fupd (K xs)
                            (data_state_stack_max_fupd (K sm)
                               (data_state_safe_for_space_fupd (K sf)
                                  (data_state_peak_heap_length_fupd (K pk) S)))) =
         (SOME (Rerr (Rraise v)),
          data_state_locals_fupd (K (data_state_locals s7))
            (data_state_locals_size_fupd (K lss)
               (data_state_stack_fupd (K (data_state_stack s7))
                  (data_state_stack_max_fupd (K smx)
                     (data_state_handler_fupd (K (data_state_handler s7))
                        (data_state_safe_for_space_fupd (K sfs)
                           (data_state_peak_heap_length_fupd (K phl) s2))))))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:data_prog`; `S:(C,FFI)data_state`] data_evaluate_stack_swap) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s2':(C,FFI)data_state` STRIP_ASSUME_TAC) THEN
  CONJ_TAC THENL [EXISTS_TAC `s2':(C,FFI)data_state` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `s7:(C,FFI)data_state` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`xs:stack list`; `s7:(C,FFI)data_state`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `lss0:num option` (X_CHOOSE_THEN `sfs0:bool`
    (X_CHOOSE_THEN `smx0:num option` (X_CHOOSE_THEN `phl0:num` ASSUME_TAC)))) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`sm:num option`; `sf:bool`; `pk:num`] o
                MATCH_MP evaluate_smx_safe_peak_swap) THEN
  REWRITE_TAC DATAPAUX_LIVE_RECORD_RWS THEN
  DISCH_THEN(X_CHOOSE_THEN `smx1:num option` (X_CHOOSE_THEN `sf1:bool`
    (X_CHOOSE_THEN `pk1:num` SUBST1_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`lss0:num option`; `sf1:bool`; `smx1:num option`; `pk1:num`] THEN
  REWRITE_TAC[]);;

let DATAPAUX_LIVE_swap_abort = prove
 (`!c (S:(C,FFI)data_state) a s2 xs sm sf pk.
     data_evaluate (c,S) = (SOME (Rerr (Rabort a)),s2) /\ ~(a = Rtype_error) /\
     LENGTH xs = LENGTH (data_state_stack S) ==>
     data_state_stack s2 = [] /\
     ?lss sfs smx phl.
       data_evaluate (c,data_state_stack_fupd (K xs)
                          (data_state_stack_max_fupd (K sm)
                             (data_state_safe_for_space_fupd (K sf)
                                (data_state_peak_heap_length_fupd (K pk) S)))) =
       (SOME (Rerr (Rabort a)),data_state_locals_size_fupd (K lss)
                                 (data_state_stack_max_fupd (K smx)
                                    (data_state_safe_for_space_fupd (K sfs)
                                       (data_state_peak_heap_length_fupd (K phl) s2))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:data_prog`; `S:(C,FFI)data_state`] data_evaluate_stack_swap) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `a:abort` (cases "abort")) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `xs:stack list`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `lss0:num option` (X_CHOOSE_THEN `sfs0:bool`
    (X_CHOOSE_THEN `smx0:num option` (X_CHOOSE_THEN `phl0:num` ASSUME_TAC)))) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`sm:num option`; `sf:bool`; `pk:num`] o
                MATCH_MP evaluate_smx_safe_peak_swap) THEN
  REWRITE_TAC DATAPAUX_LIVE_RECORD_RWS THEN
  DISCH_THEN(X_CHOOSE_THEN `smx1:num option` (X_CHOOSE_THEN `sf1:bool`
    (X_CHOOSE_THEN `pk1:num` SUBST1_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`lss0:num option`; `sf1:bool`; `smx1:num option`; `pk1:num`] THEN
  REWRITE_TAC[]);;

let DATAPAUX_LIVE_tail = prove
 (`!c (S:(C,FFI)data_state) res s2 xs sm sf pk.
     data_evaluate (c,S) = (SOME res,s2) /\ ~(res = Rerr (Rabort Rtype_error)) /\
     LENGTH xs = LENGTH (data_state_stack S) /\
     (!s3. data_jump_exc S = SOME s3 ==>
           ?t3. data_jump_exc (data_state_stack_fupd (K xs) S) = SOME t3 /\
                LENGTH (data_state_stack t3) = LENGTH (data_state_stack s3) /\
                data_state_handler t3 = data_state_handler s3) ==>
     ?t2. data_evaluate (c,data_state_stack_fupd (K xs)
                             (data_state_stack_max_fupd (K sm)
                                (data_state_safe_for_space_fupd (K sf)
                                   (data_state_peak_heap_length_fupd (K pk) S)))) =
          (SOME res,t2) /\
          data_liveProof_state_rel s2 t2 LN`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `res:(data_v list,data_v)result` (cases "result")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `v:data_v list` SUBST1_TAC)
    (X_CHOOSE_THEN `e:(data_v)error_result` SUBST1_TAC)) THENL
   [STRIP_TAC THEN
    MP_TAC(ISPECL [`c:data_prog`; `S:(C,FFI)data_state`; `v:data_v list`;
                   `s2:(C,FFI)data_state`; `xs:stack list`; `sm:num option`; `sf:bool`;
                   `pk:num`] DATAPAUX_LIVE_swap_rval) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[PAIR_EQ; UNWIND_THM1] THEN
    ASM_REWRITE_TAC[data_liveProof_state_rel_def; data_state_INFO.ri_accfupds; K_THM;
                    domain_def; NOT_IN_EMPTY];
    ALL_TAC] THEN
  MP_TAC(ISPEC `e:(data_v)error_result` (cases "error_result")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `v:data_v` SUBST1_TAC)
    (X_CHOOSE_THEN `a:abort` SUBST1_TAC)) THEN
  REWRITE_TAC[injectivity "result"; injectivity "error_result"; distinctness "error_result"] THEN
  STRIP_TAC THENL
   [MP_TAC(ISPECL [`c:data_prog`; `S:(C,FFI)data_state`; `v:data_v`;
                   `s2:(C,FFI)data_state`; `xs:stack list`; `sm:num option`; `sf:bool`;
                   `pk:num`] DATAPAUX_LIVE_swap_raise) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `s2':(C,FFI)data_state` STRIP_ASSUME_TAC)
                               MP_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s2':(C,FFI)data_state`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `t3:(C,FFI)data_state` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(MP_TAC o SPEC `t3:(C,FFI)data_state`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[PAIR_EQ; UNWIND_THM1] THEN
    ASM_REWRITE_TAC[data_liveProof_state_rel_def; data_state_INFO.ri_accfupds; K_THM;
                    domain_def; NOT_IN_EMPTY] THEN
    ASM_MESON_TAC[];
    MP_TAC(ISPECL [`c:data_prog`; `S:(C,FFI)data_state`; `a:abort`;
                   `s2:(C,FFI)data_state`; `xs:stack list`; `sm:num option`; `sf:bool`;
                   `pk:num`] DATAPAUX_LIVE_swap_abort) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[PAIR_EQ; UNWIND_THM1] THEN
    ASM_REWRITE_TAC[data_liveProof_state_rel_def; data_state_INFO.ri_accfupds; K_THM;
                    domain_def; NOT_IN_EMPTY]]);;

let DATAPAUX_LIVE_call_env_frame = prove
 (`!(s:(C,FFI)data_state) t l args ss.
     data_liveProof_state_rel s t l ==>
     data_call_env args ss (data_dec_clock t) =
     data_state_stack_fupd (K (data_state_stack t))
       (data_state_stack_max_fupd
          (K (data_state_stack_max (data_call_env args ss (data_dec_clock t))))
          (data_state_safe_for_space_fupd
             (K (data_state_safe_for_space (data_call_env args ss (data_dec_clock t))))
             (data_state_peak_heap_length_fupd (K (data_state_peak_heap_length t))
                (data_call_env args ss (data_dec_clock s)))))`,
  REWRITE_TAC[data_liveProof_state_rel_def] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[data_call_env_def; data_dec_clock_def; LET_DEF; LET_END_DEF;
              data_state_component_equality; data_state_INFO.ri_accfupds; K_THM] THEN
  ASM_REWRITE_TAC[]);;

let DATAPAUX_LIVE_jump_exc_frame = prove
 (`!(s:(C,FFI)data_state) (t:(C,FFI)data_state) (s0:(C,FFI)data_state)
      (t0:(C,FFI)data_state).
     (!s3. data_jump_exc s = SOME s3 ==>
           ?t3. data_jump_exc t = SOME t3 /\ data_liveProof_state_rel s3 t3 LN /\
                data_state_handler t3 = data_state_handler s3 /\
                LENGTH (data_state_stack t3) = LENGTH (data_state_stack s3)) /\
     data_state_stack s0 = data_state_stack s /\
     data_state_handler s0 = data_state_handler s /\
     data_state_stack t0 = data_state_stack t /\
     data_state_handler t0 = data_state_handler t ==>
     (!s3. data_jump_exc s0 = SOME s3 ==>
           ?t3. data_jump_exc t0 = SOME t3 /\
                LENGTH (data_state_stack t3) = LENGTH (data_state_stack s3) /\
                data_state_handler t3 = data_state_handler s3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `s3:(C,FFI)data_state` THEN
  MP_TAC(ISPECL [`s:(C,FFI)data_state`; `s0:(C,FFI)data_state`] DSEMAUX_jump_exc_cong) THEN
  MP_TAC(ISPECL [`t:(C,FFI)data_state`; `t0:(C,FFI)data_state`] DSEMAUX_jump_exc_cong) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPEC `data_jump_exc (s:(C,FFI)data_state)` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `s4:(C,FFI)data_state` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[OPTION_MAP_DEF; option_DISTINCT; option_INJ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s4:(C,FFI)data_state`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t4:(C,FFI)data_state` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[OPTION_MAP_DEF; option_INJ; UNWIND_THM1] THEN
  REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM] THEN ASM_REWRITE_TAC[]);;

let DATAPAUX_LIVE_rel_fields = prove
 (`!(s:(C,FFI)data_state) t l.
     data_liveProof_state_rel s t l ==>
     data_state_refs t = data_state_refs s /\ data_state_code t = data_state_code s /\
     data_state_stack_frame_sizes t = data_state_stack_frame_sizes s /\
     data_state_clock t = data_state_clock s /\
     data_state_handler t = data_state_handler s /\
     LENGTH (data_state_stack t) = LENGTH (data_state_stack s)`,
  SIMP_TAC[data_liveProof_state_rel_def]);;

let DATAPAUX_LIVE_cut_env = prove
 (`!(s:(C,FFI)data_state) t names (l:num_set) (l':num_set) env.
     data_liveProof_state_rel s t l' /\ domain (inter names l) SUBSET domain l' /\
     data_cut_env names (data_state_locals s) = SOME env ==>
     data_cut_env (inter names l) (data_state_locals t) =
     SOME (mk_wf (inter (data_state_locals t) (inter names l))) /\
     (!x. x IN domain l ==>
          lookup x env = lookup x (mk_wf (inter (data_state_locals t) (inter names l))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_cut_env_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THENL
   [SUBGOAL_THEN `domain (inter (names:num_set) (l:num_set)) SUBSET
                  domain (data_state_locals (t:(C,FFI)data_state))`
      (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[SUBSET; domain_inter; IN_INTER] THEN X_GEN_TAC `x:num` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`s:(C,FFI)data_state`; `t:(C,FFI)data_state`; `l':num_set`; `x:num`]
             DATAPAUX_LIVE_rel_lookup) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; domain_inter; IN_INTER]) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `!x. x IN domain (names:num_set) ==> x IN domain (data_state_locals (s:(C,FFI)data_state))` THEN
    DISCH_THEN(MP_TAC o SPEC `x:num`) THEN ASM_REWRITE_TAC[domain_lookup] THEN MESON_TAC[];
    REWRITE_TAC[lookup_mk_wf; lookup_inter_alt; domain_inter; IN_INTER] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC DATAPAUX_LIVE_rel_lookup THEN EXISTS_TAC `l':num_set` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; domain_inter; IN_INTER]) THEN ASM_MESON_TAC[]]);;

let DATAPAUX_LIVE_call_push_frame = prove
 (`!(s:(C,FFI)data_state) t l args ss env env' b.
     data_liveProof_state_rel s t l ==>
     data_call_env args ss (data_push_env env' b (data_dec_clock t)) =
     data_state_stack_fupd
       (K (data_state_stack (data_call_env args ss (data_push_env env' b (data_dec_clock t)))))
       (data_state_stack_max_fupd
          (K (data_state_stack_max
                (data_call_env args ss (data_push_env env' b (data_dec_clock t)))))
          (data_state_safe_for_space_fupd
             (K (data_state_safe_for_space
                   (data_call_env args ss (data_push_env env' b (data_dec_clock t)))))
             (data_state_peak_heap_length_fupd (K (data_state_peak_heap_length t))
                (data_call_env args ss (data_push_env env b (data_dec_clock s))))))`,
  REWRITE_TAC[data_liveProof_state_rel_def] THEN REPEAT STRIP_TAC THEN
  BOOL_CASES_TAC `b:bool` THEN
  REWRITE_TAC[data_call_env_def; data_push_env_def; data_dec_clock_def; LET_DEF; LET_END_DEF;
              data_state_component_equality; data_state_INFO.ri_accfupds; K_THM] THEN
  ASM_REWRITE_TAC[]);;

(* the statement of evaluate_compile (HOL4's case res of NONE => l2 | _ => *)
(* LN is option_CASE res l2 (\x. LN))                                      *)
let DATAPAUX_LIVE_GOAL =
 `!c (s1:(C,FFI)data_state) res s2 l2 t1 l1 d.
     data_evaluate (c,s1) = (res,s2) /\ data_liveProof_state_rel s1 t1 l1 /\
     data_live_compile c l2 = (d,l1) /\ ~(res = SOME (Rerr (Rabort Rtype_error))) /\
     (!s3. data_jump_exc s1 = SOME s3 ==>
           ?t3. data_jump_exc t1 = SOME t3 /\ data_liveProof_state_rel s3 t3 LN /\
                data_state_handler t3 = data_state_handler s3 /\
                LENGTH (data_state_stack t3) = LENGTH (data_state_stack s3)) ==>
     ?t2. data_evaluate (d,t1) = (res,t2) /\
          data_liveProof_state_rel s2 t2 (option_CASE res l2 (\x. LN))`;;

(* the instance of a pair induction theorem ind (conclusion !p. P p) for a *)
(* statement !c s. body: its antecedent conjuncts are the cases of HOL4's  *)
(* recInduct proof                                                          *)
let DATAPAUX_LIVE_IND_INST (goal:term) (ind:thm) =
  let c,b1 = dest_forall goal in
  let s,b = dest_forall b1 in
  let p = mk_var("p",mk_type("prod",[type_of c;type_of s])) in
  let fstp = mk_icomb(mk_const("FST",[]),p)
  and sndp = mk_icomb(mk_const("SND",[]),p) in
  let pred = mk_abs(p,vsubst [fstp,c; sndp,s] b) in
  CONV_RULE (DEPTH_CONV BETA_CONV THENC REWRITE_CONV[FST; SND]) (ISPEC pred ind);;

let DATAPAUX_LIVE_IND = DATAPAUX_LIVE_IND_INST DATAPAUX_LIVE_GOAL data_evaluate_ind;;
let DATAPAUX_LIVE_CASES = conjuncts (lhand (concl DATAPAUX_LIVE_IND));;

(* HOL4: evaluate_compile[Skip] *)
let DATAPAUX_LIVE_SKIP = prove
 (el 0 DATAPAUX_LIVE_CASES,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_evaluate_def; data_live_compile_def; PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  ASM_REWRITE_TAC[option_CASE; data_evaluate_def; PAIR_EQ; UNWIND_THM1]);;

(* HOL4: evaluate_compile[Move] *)
let DATAPAUX_LIVE_MOVE = prove
 (el 1 DATAPAUX_LIVE_CASES,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_evaluate_def; data_live_compile_def; PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[data_evaluate_def] THEN
  SUBGOAL_THEN `data_get_var src (data_state_locals (t1:(C,FFI)data_state)) =
                data_get_var src (data_state_locals (s:(C,FFI)data_state))` SUBST1_TAC THENL
   [REWRITE_TAC[data_get_var_def] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC DATAPAUX_LIVE_rel_lookup THEN
    EXISTS_TAC `insert src one (delete dest l2)` THEN
    ASM_REWRITE_TAC[domain_insert; IN_INSERT]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_eq o concl)) THEN
  TOP_CASE_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  FS[option_CASE; PAIR_EQ; UNWIND_THM1] THEN
  MATCH_MP_TAC DATAPAUX_LIVE_rel_set_var THEN MATCH_MP_TAC DATAPAUX_LIVE_rel_mono THEN
  EXISTS_TAC `insert src one (delete dest l2)` THEN
  ASM_REWRITE_TAC[domain_insert; SUBSET; IN_INSERT] THEN MESON_TAC[]);;

let DATAPAUX_LIVE_ASSIGN_PURE_TAC : tactic =
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  UNDISCH_TAC `data_evaluate (data_Assign dest op args NONE,s:(C,FFI)data_state) = res,s2` THEN
  REWRITE_TAC[data_evaluate_def; IS_NONE_DEF; data_cut_state_opt_def; option_CASE] THEN
  COND_CASES_TAC THENL [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN FS[]; ALL_TAC] THEN
  TOP_CASE_TAC THENL [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN FS[]; ALL_TAC] THEN
  TOP_CASE_TAC THEN TRY(TOP_CASE_TAC) THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THENL
   [MP_TAC(ISPECL [`op:clos_op`; `a:data_v list`; `s:(C,FFI)data_state`;
                   `x:data_v`; `y:(C,FFI)data_state`] is_pure_do_app_Rval_IMP) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN RVEQ_TAC THEN
    REWRITE_TAC[UNWIND_THM1; option_CASE] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IS_NONE_EQ_NONE; lookup_NONE_domain]) THEN
    FIRST_X_ASSUM(MP_TAC o check (is_conj o concl)) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [data_liveProof_state_rel_def]) THEN
    REWRITE_TAC[data_liveProof_state_rel_def; data_set_var_def; install_sfs_def;
                data_state_INFO.ri_accfupds; K_THM; lookup_insert] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_MESON_TAC[];
    MP_TAC(ISPECL [`op:clos_op`; `a:data_v list`; `s:(C,FFI)data_state`;
                   `a':(data_v)error_result`] is_pure_do_app_Rerr_IMP) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN FS[]];;

let DATAPAUX_LIVE_ASSIGN_NONE_TAC : tactic =
  REWRITE_TAC[LET_DEF; LET_END_DEF; PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  UNDISCH_TAC `data_evaluate (data_Assign dest op args NONE,s:(C,FFI)data_state) = res,s2` THEN
  REWRITE_TAC[data_evaluate_def; IS_NONE_DEF; data_cut_state_opt_def; option_CASE] THEN
  COND_CASES_TAC THENL [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN FS[]; ALL_TAC] THEN
  TOP_CASE_TAC THENL [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN FS[]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> FIRST_ASSUM(fun th2 ->
    ASSUME_TAC (MATCH_MP state_rel_IMP_get_vars (CONJ th th2)))) THEN
  ASM_REWRITE_TAC[option_CASE] THEN
  MP_TAC(ISPEC `data_do_app op a (s:(C,FFI)data_state)` (cases "result")) THEN
  DISCH_THEN(DISJ_CASES_THEN2
    (X_CHOOSE_THEN `xy:data_v#(C,FFI)data_state` ASSUME_TAC)
    (X_CHOOSE_THEN `e:(data_v)error_result` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL
   [MP_TAC(ISPEC `xy:data_v#(C,FFI)data_state` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `x:data_v` (X_CHOOSE_THEN `y:(C,FFI)data_state`
      SUBST_ALL_TAC)) THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    FIRST_ASSUM(fun th -> FIRST_ASSUM(fun th2 ->
      MP_TAC (MATCH_MP state_rel_IMP_do_app (CONJ th2 th)))) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[PAIR_EQ; UNWIND_THM1; option_CASE] THEN
    MATCH_MP_TAC DATAPAUX_LIVE_rel_set_var THEN
    MATCH_MP_TAC DATAPAUX_LIVE_rel_install_sfs THEN
    MATCH_MP_TAC DATAPAUX_LIVE_rel_mono THEN
    EXISTS_TAC `list_insert args (delete dest (l2:num_set))` THEN
    REWRITE_TAC[SUBSET; domain_list_insert] THEN CONJ_TAC THENL
     [MATCH_MP_TAC DATAPAUX_LIVE_rel_do_app_result THEN ASM_MESON_TAC[]; MESON_TAC[]];
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    FIRST_ASSUM(fun th -> FIRST_ASSUM(fun th2 ->
      MP_TAC (MATCH_MP state_rel_IMP_do_app_err (CONJ th2 th)))) THEN
    DISCH_THEN SUBST1_TAC THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[PAIR_EQ; UNWIND_THM1; option_CASE] THEN
    MATCH_MP_TAC DATAPAUX_LIVE_rel_flush_state THEN
    EXISTS_TAC `list_insert args (delete dest (l2:num_set))` THEN
    MATCH_MP_TAC DATAPAUX_LIVE_rel_install_sfs THEN ASM_REWRITE_TAC[]];;

let DATAPAUX_LIVE_ASSIGN_SOME_TAC : tactic =
  UNDISCH_TAC `data_live_compile (data_Assign dest op args (SOME a)) l2 = d,l1` THEN
   REWRITE_TAC[data_live_compile_def; LET_DEF; LET_END_DEF; PAIR_EQ] THEN
   STRIP_TAC THEN RVEQ_TAC THEN
   UNDISCH_TAC `data_evaluate (data_Assign dest op args (SOME a),s:(C,FFI)data_state) = res,s2` THEN
   REWRITE_TAC[data_evaluate_def; IS_NONE_DEF; data_cut_state_opt_def; data_cut_state_def;
               option_CASE] THEN
   COND_CASES_TAC THENL [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN FS[]; ALL_TAC] THEN
   TOP_CASE_TAC THENL [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN FS[]; ALL_TAC] THEN
   FIRST_ASSUM(fun th -> FIRST_ASSUM(fun th2 ->
     ASSUME_TAC (MATCH_MP state_rel_IMP_get_vars (CONJ th th2)))) THEN
   ASM_REWRITE_TAC[option_CASE] THEN
   MP_TAC(ISPEC `data_cut_env (a:num_set) (data_state_locals (s:(C,FFI)data_state))`
            (cases "option")) THEN
   DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC
     (X_CHOOSE_THEN `env:data_v spt` ASSUME_TAC)) THENL
    [REWRITE_TAC[option_CASE; PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN FS[]; ALL_TAC] THEN
   ASM_REWRITE_TAC[option_CASE] THEN
   SUBGOAL_THEN
     `data_cut_env (inter (a:num_set) (delete dest (l2:num_set))) (data_state_locals (t1:(C,FFI)data_state)) =
      SOME (mk_wf (inter (data_state_locals t1) (inter a (delete dest l2))))`
     SUBST1_TAC THENL
    [UNDISCH_TAC `data_cut_env (a:num_set) (data_state_locals (s:(C,FFI)data_state)) = SOME env` THEN
     REWRITE_TAC[data_cut_env_def] THEN COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
     DISCH_TAC THEN
     SUBGOAL_THEN `domain (inter (a:num_set) (delete dest (l2:num_set))) SUBSET
                   domain (data_state_locals (t1:(C,FFI)data_state))`
       (fun th -> REWRITE_TAC[th]) THEN
     REWRITE_TAC[SUBSET; domain_inter; IN_INTER] THEN X_GEN_TAC `x:num` THEN STRIP_TAC THEN
     MP_TAC(ISPECL [`s:(C,FFI)data_state`; `t1:(C,FFI)data_state`;
                    `list_insert args (inter (a:num_set) (delete dest (l2:num_set)))`; `x:num`]
              DATAPAUX_LIVE_rel_lookup) THEN
     ASM_REWRITE_TAC[domain_list_insert; domain_inter; IN_INTER] THEN
     RULE_ASSUM_TAC(REWRITE_RULE[SUBSET]) THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `x:num` o check (is_forall o concl)) THEN
     ASM_REWRITE_TAC[domain_lookup] THEN MESON_TAC[];
     ALL_TAC] THEN
   REWRITE_TAC[option_CASE] THEN
  SUBGOAL_THEN
     `data_liveProof_state_rel (data_state_locals_fupd (K env) (s:(C,FFI)data_state))
        (data_state_locals_fupd
           (K (mk_wf (inter (data_state_locals (t1:(C,FFI)data_state))
                            (inter (a:num_set) (delete dest (l2:num_set))))))
           t1)
        (delete dest l2)`
     ASSUME_TAC THENL
    [MATCH_MP_TAC DATAPAUX_LIVE_rel_with_locals THEN
     EXISTS_TAC `list_insert args (inter (a:num_set) (delete dest (l2:num_set)))` THEN
     ASM_REWRITE_TAC[] THEN
     UNDISCH_TAC `data_cut_env (a:num_set) (data_state_locals (s:(C,FFI)data_state)) = SOME env` THEN
     REWRITE_TAC[data_cut_env_def] THEN COND_CASES_TAC THEN
     REWRITE_TAC[option_DISTINCT; option_INJ] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
     X_GEN_TAC `x:num` THEN DISCH_TAC THEN
     REWRITE_TAC[lookup_mk_wf; lookup_inter_alt; domain_inter; IN_INTER] THEN
     COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC DATAPAUX_LIVE_rel_lookup THEN
     EXISTS_TAC `list_insert args (inter (a:num_set) (delete dest (l2:num_set)))` THEN
     ASM_REWRITE_TAC[domain_list_insert; domain_inter; IN_INTER];
     ALL_TAC] THEN
   MP_TAC(ISPEC `data_do_app op a' (data_state_locals_fupd (K env) (s:(C,FFI)data_state))`
            (cases "result")) THEN
   DISCH_THEN(DISJ_CASES_THEN2
     (X_CHOOSE_THEN `xy:data_v#(C,FFI)data_state` ASSUME_TAC)
     (X_CHOOSE_THEN `e:(data_v)error_result` ASSUME_TAC)) THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL
    [MP_TAC(ISPEC `xy:data_v#(C,FFI)data_state` PAIR_SURJECTIVE) THEN
     DISCH_THEN(X_CHOOSE_THEN `x:data_v` (X_CHOOSE_THEN `y:(C,FFI)data_state`
       SUBST_ALL_TAC)) THEN CASE_REWRITE_TAC[] THEN
     REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
     FIRST_ASSUM(fun th -> FIRST_ASSUM(fun th2 ->
       MP_TAC (MATCH_MP state_rel_IMP_do_app (CONJ th2 th)))) THEN
     STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
     REWRITE_TAC[PAIR_EQ; UNWIND_THM1; option_CASE] THEN
     MATCH_MP_TAC DATAPAUX_LIVE_rel_set_var THEN
     MATCH_MP_TAC DATAPAUX_LIVE_rel_install_sfs THEN
     MATCH_MP_TAC DATAPAUX_LIVE_rel_do_app_result THEN ASM_MESON_TAC[];
     REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
     FIRST_ASSUM(fun th -> FIRST_ASSUM(fun th2 ->
       MP_TAC (MATCH_MP state_rel_IMP_do_app_err (CONJ th2 th)))) THEN
     DISCH_THEN SUBST1_TAC THEN CASE_REWRITE_TAC[] THEN
     REWRITE_TAC[PAIR_EQ; UNWIND_THM1; option_CASE] THEN
     MATCH_MP_TAC DATAPAUX_LIVE_rel_flush_state THEN
     EXISTS_TAC `delete dest (l2:num_set)` THEN
     MATCH_MP_TAC DATAPAUX_LIVE_rel_install_sfs THEN ASM_REWRITE_TAC[]];;

(* HOL4: evaluate_compile[Assign] *)
let DATAPAUX_LIVE_ASSIGN = prove
 (el 2 DATAPAUX_LIVE_CASES,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  CASES_ON `names_opt:num_set option` THENL
   [UNDISCH_TAC `data_live_compile (data_Assign dest op args NONE) l2 = d,l1` THEN
    REWRITE_TAC[data_live_compile_def] THEN COND_CASES_TAC THENL
     [DATAPAUX_LIVE_ASSIGN_PURE_TAC; DATAPAUX_LIVE_ASSIGN_NONE_TAC];
    DATAPAUX_LIVE_ASSIGN_SOME_TAC]);;

(* HOL4: evaluate_compile[Tick] *)
let DATAPAUX_LIVE_TICK = prove
 (el 3 DATAPAUX_LIVE_CASES,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_evaluate_def; data_live_compile_def; PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[data_evaluate_def] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP DATAPAUX_LIVE_rel_clock) THEN
  FIRST_X_ASSUM(MP_TAC o check (is_eq o concl)) THEN
  COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  FS[option_CASE; PAIR_EQ; UNWIND_THM1] THEN
  FS[data_liveProof_state_rel_def; data_flush_state_def; data_dec_clock_def]);;

(* HOL4: evaluate_compile[MakeSpace] *)
let DATAPAUX_LIVE_MAKESPACE = prove
 (el 4 DATAPAUX_LIVE_CASES,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[data_evaluate_def; data_live_compile_def; PAIR_EQ; LET_DEF; LET_END_DEF] THEN
  STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[data_evaluate_def] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_eq o concl)) THEN
  TOP_CASE_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN FS[] THEN
  UNDISCH_TAC `data_cut_env names (data_state_locals (s:(C,FFI)data_state)) = SOME a` THEN
  REWRITE_TAC[data_cut_env_def] THEN COND_CASES_TAC THEN
  REWRITE_TAC[option_DISTINCT; option_INJ] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN `domain (inter (names:num_set) (l2:num_set)) SUBSET
                domain (data_state_locals (t1:(C,FFI)data_state))`
    (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[domain_inter; SUBSET; IN_INTER] THEN X_GEN_TAC `x:num` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`s:(C,FFI)data_state`; `t1:(C,FFI)data_state`;
                   `inter (names:num_set) (l2:num_set)`; `x:num`]
             DATAPAUX_LIVE_rel_lookup) THEN
    ASM_REWRITE_TAC[domain_inter; IN_INTER] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[SUBSET]) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:num` o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[domain_lookup] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[option_CASE; PAIR_EQ; UNWIND_THM1] THEN
  MATCH_MP_TAC DATAPAUX_LIVE_rel_add_space THEN MATCH_MP_TAC DATAPAUX_LIVE_rel_with_locals THEN
  EXISTS_TAC `inter (names:num_set) (l2:num_set)` THEN
  ASM_REWRITE_TAC[lookup_mk_wf; lookup_inter_alt; domain_inter; IN_INTER] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC DATAPAUX_LIVE_rel_lookup THEN
  EXISTS_TAC `inter (names:num_set) (l2:num_set)` THEN
  ASM_REWRITE_TAC[domain_inter; IN_INTER]);;

(* HOL4: evaluate_compile[Raise] *)
let DATAPAUX_LIVE_RAISE = prove
 (el 5 DATAPAUX_LIVE_CASES,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_evaluate_def; data_live_compile_def; PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[data_evaluate_def] THEN
  SUBGOAL_THEN `data_get_var n (data_state_locals (t1:(C,FFI)data_state)) =
                data_get_var n (data_state_locals (s:(C,FFI)data_state))` SUBST1_TAC THENL
   [REWRITE_TAC[data_get_var_def] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC DATAPAUX_LIVE_rel_lookup THEN
    EXISTS_TAC `insert n one LN` THEN
    ASM_REWRITE_TAC[domain_insert; IN_INSERT]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_eq o concl)) THEN
  TOP_CASE_TAC THEN REWRITE_TAC[PAIR_EQ] THENL
   [STRIP_TAC THEN RVEQ_TAC THEN FS[]; ALL_TAC] THEN
  TOP_CASE_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN FS[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `a':(C,FFI)data_state`) THEN REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[option_CASE; PAIR_EQ; UNWIND_THM1]);;

(* HOL4: evaluate_compile[Return] *)
let DATAPAUX_LIVE_RETURN = prove
 (el 6 DATAPAUX_LIVE_CASES,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_evaluate_def; data_live_compile_def; PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[data_evaluate_def] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_eq o concl)) THEN
  TOP_CASE_TAC THEN REWRITE_TAC[PAIR_EQ] THENL
   [STRIP_TAC THEN RVEQ_TAC THEN FS[]; ALL_TAC] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_ASSUM(fun th -> FIRST_ASSUM(fun th2 ->
    SUBST1_TAC (MATCH_MP state_rel_IMP_get_vars (CONJ th th2)))) THEN
  REWRITE_TAC[option_CASE; PAIR_EQ; UNWIND_THM1] THEN
  FS[data_liveProof_state_rel_def; data_flush_state_def]);;

(* the jump_exc hypothesis of evaluate_compile carries over a Seq whose *)
(* first part returned NONE (HOL4: evaluate_NONE_jump_exc and its ALT,  *)
(* then jump_exc_IMP_state_rel)                                          *)
let DATAPAUX_LIVE_jump_exc_seq = prove
 (`!c1 x1 (s:(C,FFI)data_state) t1 u1 t2 l.
     data_evaluate (c1,s) = (NONE,u1) /\ data_evaluate (x1,t1) = (NONE,t2) /\
     data_liveProof_state_rel u1 t2 l /\
     (!s3. data_jump_exc s = SOME s3 ==>
           ?t3. data_jump_exc t1 = SOME t3 /\ data_liveProof_state_rel s3 t3 LN /\
                data_state_handler t3 = data_state_handler s3 /\
                LENGTH (data_state_stack t3) = LENGTH (data_state_stack s3)) ==>
     (!s3. data_jump_exc u1 = SOME s3 ==>
           ?t3. data_jump_exc t2 = SOME t3 /\ data_liveProof_state_rel s3 t3 LN /\
                data_state_handler t3 = data_state_handler s3 /\
                LENGTH (data_state_stack t3) = LENGTH (data_state_stack s3))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `s3:(C,FFI)data_state` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`c1:data_prog`; `s:(C,FFI)data_state`; `u1:(C,FFI)data_state`;
                 `s3:(C,FFI)data_state`] evaluate_NONE_jump_exc) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
    `data_state_stack_fupd (K (data_state_stack (s3:(C,FFI)data_state)))
       (data_state_handler_fupd (K (data_state_handler s3))
          (data_state_locals_fupd (K (data_state_locals s3))
             (data_state_locals_size_fupd (K (data_state_locals_size s3))
                (s:(C,FFI)data_state))))`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t3:(C,FFI)data_state` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`x1:data_prog`; `t1:(C,FFI)data_state`; `t2:(C,FFI)data_state`;
                 `t3:(C,FFI)data_state`] evaluate_NONE_jump_exc_ALT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[option_INJ; UNWIND_THM1] THEN
  UNDISCH_TAC `data_jump_exc (u1:(C,FFI)data_state) = SOME s3` THEN
  DISCH_THEN(MP_TAC o MATCH_MP jump_exc_IMP) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `e:data_v spt`
      (X_CHOOSE_THEN `ls:num option` (X_CHOOSE_THEN `xs:stack list`
        (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)))))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[data_state_INFO.ri_accfupds; K_THM]) THEN
  ASM_REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM] THEN
  UNDISCH_TAC `LENGTH (data_state_stack (t3:(C,FFI)data_state)) = LENGTH (xs:stack list)` THEN
  UNDISCH_TAC `data_liveProof_state_rel (u1:(C,FFI)data_state) t2 l` THEN
  REWRITE_TAC[data_liveProof_state_rel_def; data_state_INFO.ri_accfupds; K_THM;
              domain_def; NOT_IN_EMPTY] THEN
  SIMP_TAC[]);;

(* HOL4: evaluate_compile[Seq] *)
let DATAPAUX_LIVE_SEQ = prove
 (el 7 DATAPAUX_LIVE_CASES,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
   REPEAT GEN_TAC THEN REWRITE_TAC[data_live_compile_def] THEN
   MP_TAC(ISPEC `data_live_compile c2 l2` PAIR_SURJECTIVE) THEN
   DISCH_THEN(X_CHOOSE_THEN `x2:data_prog` (X_CHOOSE_THEN `l5:num_set` ASSUME_TAC)) THEN
   MP_TAC(ISPEC `data_live_compile c1 l5` PAIR_SURJECTIVE) THEN
   DISCH_THEN(X_CHOOSE_THEN `x1:data_prog` (X_CHOOSE_THEN `l6:num_set` ASSUME_TAC)) THEN
   ASM_REWRITE_TAC[pair_CASE; PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
   MP_TAC(ISPEC `data_evaluate (c1,s:(C,FFI)data_state)` PAIR_SURJECTIVE) THEN
   DISCH_THEN(X_CHOOSE_THEN `res1:((data_v list,data_v)result)option`
     (X_CHOOSE_THEN `u1:(C,FFI)data_state` ASSUME_TAC)) THEN
   UNDISCH_TAC `data_evaluate (data_Seq c1 c2,s:(C,FFI)data_state) = res,s2` THEN
   ONCE_REWRITE_TAC[data_evaluate_def] THEN ASM_REWRITE_TAC[pair_CASE] THEN
   ONCE_REWRITE_TAC[data_evaluate_def] THEN
   ASM_CASES_TAC `res1:((data_v list,data_v)result)option = SOME (Rerr (Rabort Rtype_error))` THENL
    [ASM_REWRITE_TAC[option_DISTINCT; PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN FS[]; ALL_TAC] THEN
   REMOVE_THEN "ih1" (MP_TAC o SPECL [`res1:((data_v list,data_v)result)option`;
     `u1:(C,FFI)data_state`; `l5:num_set`; `t1:(C,FFI)data_state`; `l1:num_set`;
     `x1:data_prog`]) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `t2:(C,FFI)data_state` STRIP_ASSUME_TAC) THEN
   ASM_REWRITE_TAC[pair_CASE] THEN
  ASM_CASES_TAC `res1:((data_v list,data_v)result)option = NONE` THENL
    [POP_ASSUM SUBST_ALL_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[option_CASE]) THEN
     REWRITE_TAC[] THEN DISCH_TAC THEN
     REMOVE_THEN "ih2" (MP_TAC o SPEC `u1:(C,FFI)data_state`) THEN
     ASM_REWRITE_TAC[] THEN
     DISCH_THEN(MP_TAC o SPECL [`res:((data_v list,data_v)result)option`;
       `s2:(C,FFI)data_state`; `l2:num_set`; `t2:(C,FFI)data_state`; `l5:num_set`;
       `x2:data_prog`]) THEN
     ASM_REWRITE_TAC[] THEN
     ANTS_TAC THENL
      [MATCH_MP_TAC DATAPAUX_LIVE_jump_exc_seq THEN
       MAP_EVERY EXISTS_TAC [`c1:data_prog`; `x1:data_prog`; `s:(C,FFI)data_state`;
                             `t1:(C,FFI)data_state`; `l5:num_set`] THEN
       ASM_REWRITE_TAC[];
       REWRITE_TAC[]];
     ASM_REWRITE_TAC[] THEN
     DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM) o
                REWRITE_RULE[PAIR_EQ]) THEN
     EXISTS_TAC `t2:(C,FFI)data_state` THEN REWRITE_TAC[] THEN
     UNDISCH_TAC `data_liveProof_state_rel (u1:(C,FFI)data_state) (t2:(C,FFI)data_state) (option_CASE (res1:((data_v list,data_v)result)option) (l5:num_set) (\x. LN))` THEN
     MP_TAC(ISPEC `res1:((data_v list,data_v)result)option` (cases "option")) THEN
     ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[option_CASE]]);;

(* HOL4: evaluate_compile[If] *)
let DATAPAUX_LIVE_IF = prove
 (el 8 DATAPAUX_LIVE_CASES,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[data_live_compile_def] THEN
  MP_TAC(ISPEC `data_live_compile c2 l2` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `d3:data_prog` (X_CHOOSE_THEN `l3:num_set` ASSUME_TAC)) THEN
  MP_TAC(ISPEC `data_live_compile c1 l2` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:data_prog` (X_CHOOSE_THEN `l4:num_set` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[pair_CASE; PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  SUBGOAL_THEN `data_get_var n (data_state_locals (t1:(C,FFI)data_state)) =
                data_get_var n (data_state_locals (s:(C,FFI)data_state))` ASSUME_TAC THENL
   [REWRITE_TAC[data_get_var_def] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC DATAPAUX_LIVE_rel_lookup THEN
    EXISTS_TAC `insert n one (union l4 l3)` THEN
    ASM_REWRITE_TAC[domain_insert; IN_INSERT]; ALL_TAC] THEN
  UNDISCH_TAC `data_evaluate (data_If n c1 c2,s:(C,FFI)data_state) = res,s2` THEN
  REWRITE_TAC[data_evaluate_def] THEN ASM_REWRITE_TAC[] THEN
  TOP_CASE_TAC THEN REWRITE_TAC[PAIR_EQ] THENL
   [STRIP_TAC THEN RVEQ_TAC THEN FS[]; ALL_TAC] THEN
  COND_CASES_TAC THENL
   [REMOVE_THEN "ih1" (MP_TAC o SPEC `a:data_v`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `l4:num_set` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC DATAPAUX_LIVE_rel_mono THEN EXISTS_TAC `insert n one (union l4 l3)` THEN
    ASM_REWRITE_TAC[domain_insert; domain_union] THEN SET_TAC[];
    ALL_TAC] THEN
  COND_CASES_TAC THENL
   [REMOVE_THEN "ih2" (MP_TAC o SPEC `a:data_v`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `l3:num_set` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC DATAPAUX_LIVE_rel_mono THEN EXISTS_TAC `insert n one (union l4 l3)` THEN
    ASM_REWRITE_TAC[domain_insert; domain_union] THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN FS[]);;

let DATAPAUX_LIVE_ERR_TAC : tactic =
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN FS[];;

let DATAPAUX_LIVE_FORCE_NONE_TAC : tactic =
  UNDISCH_TAC `data_live_compile (data_Force NONE loc src) l2 = d,l1` THEN
  REWRITE_TAC[data_live_compile_def; PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  UNDISCH_TAC `data_evaluate (data_Force NONE loc src,s:(C,FFI)data_state) = res,s2` THEN
  SUBGOAL_THEN `data_get_var src (data_state_locals (t1:(C,FFI)data_state)) =
                data_get_var src (data_state_locals (s:(C,FFI)data_state))` ASSUME_TAC THENL
   [REWRITE_TAC[data_get_var_def] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC DATAPAUX_LIVE_rel_lookup THEN
    EXISTS_TAC `insert src one LN` THEN
    ASM_REWRITE_TAC[domain_insert; IN_INSERT]; ALL_TAC] THEN
  REWRITE_TAC[data_evaluate_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  TOP_CASE_TAC THENL [DATAPAUX_LIVE_ERR_TAC; ALL_TAC] THEN
  TOP_CASE_TAC THENL [DATAPAUX_LIVE_ERR_TAC; DATAPAUX_LIVE_ERR_TAC; ALL_TAC] THEN
  TOP_CASE_TAC THENL
   [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    REWRITE_TAC[UNWIND_THM1; option_CASE] THEN
    MATCH_MP_TAC DATAPAUX_LIVE_rel_flush_state THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  TOP_CASE_TAC THENL [DATAPAUX_LIVE_ERR_TAC; ALL_TAC] THEN
  TOP_CASE_TAC THEN TOP_CASE_TAC THEN
  COND_CASES_TAC THENL
   [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    REWRITE_TAC[UNWIND_THM1; option_CASE] THEN
    UNDISCH_TAC `data_liveProof_state_rel (s:(C,FFI)data_state) t1 (insert src one LN)` THEN
    REWRITE_TAC[data_liveProof_state_rel_def; data_state_INFO.ri_accfupds; K_THM;
                domain_def; NOT_IN_EMPTY] THEN SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN
  FIRST_ASSUM(fun th -> ONCE_REWRITE_TAC[MATCH_MP DATAPAUX_LIVE_call_env_frame th]) THEN
  MP_TAC(ISPEC `data_evaluate (x',data_call_env x y' (data_dec_clock (s:(C,FFI)data_state)))`
           PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:((data_v list,data_v)result)option`
    (X_CHOOSE_THEN `s3:(C,FFI)data_state` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[pair_CASE] THEN
  MP_TAC(ISPEC `r:((data_v list,data_v)result)option` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC
    (X_CHOOSE_THEN `res2:(data_v list,data_v)result` SUBST_ALL_TAC)) THEN
  CASE_REWRITE_TAC[] THENL [DATAPAUX_LIVE_ERR_TAC; ALL_TAC] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  MP_TAC(ISPECL [`x':data_prog`; `data_call_env x y' (data_dec_clock (s:(C,FFI)data_state))`;
                 `res2:(data_v list,data_v)result`; `s2:(C,FFI)data_state`;
                 `data_state_stack (t1:(C,FFI)data_state)`;
                 `data_state_stack_max (data_call_env x y' (data_dec_clock (t1:(C,FFI)data_state)))`;
                 `data_state_safe_for_space (data_call_env x y' (data_dec_clock (t1:(C,FFI)data_state)))`;
                 `data_state_peak_heap_length (t1:(C,FFI)data_state)`] DATAPAUX_LIVE_tail) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [FS[]; ALL_TAC] THEN
    REWRITE_TAC[data_call_env_def; data_dec_clock_def; LET_DEF; LET_END_DEF;
                data_state_INFO.ri_accfupds; K_THM] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC DATAPAUX_LIVE_jump_exc_frame THEN
    MAP_EVERY EXISTS_TAC [`s:(C,FFI)data_state`; `t1:(C,FFI)data_state`] THEN
    ASM_REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:(C,FFI)data_state` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[pair_CASE; option_CASE; PAIR_EQ; UNWIND_THM1];;

let DATAPAUX_LIVE_FORCE_CUT_TAC : tactic =
  MP_TAC(ISPEC `data_cut_env names (data_state_locals (s:(C,FFI)data_state))`
           (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `env:data_v spt` ASSUME_TAC)) THENL
   [ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN DATAPAUX_LIVE_ERR_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:(C,FFI)data_state`; `t1:(C,FFI)data_state`; `names:num_set`;
                 `delete dest (l2:num_set)`;
                 `insert src one (inter names (delete dest (l2:num_set)))`;
                 `env:data_v spt`] DATAPAUX_LIVE_cut_env) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[domain_insert] THEN SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[];;
let DATAPAUX_LIVE_FS_S = `data_call_env x y' (data_push_env env F (data_dec_clock (s:(C,FFI)data_state)))`;;
let DATAPAUX_LIVE_FS_T = `data_call_env x y' (data_push_env (mk_wf (inter (data_state_locals (t1:(C,FFI)data_state)) (inter (names:num_set) (delete dest (l2:num_set))))) F (data_dec_clock t1))`;;
let DATAPAUX_LIVE_FORCE_SOME_TAC : tactic =
  (MP_TAC(ISPEC `a:num#num_set` PAIR_SURJECTIVE) THEN
   DISCH_THEN(X_CHOOSE_THEN `dest:num` (X_CHOOSE_THEN `names:num_set` SUBST_ALL_TAC)) THEN
   UNDISCH_TAC `data_live_compile (data_Force (SOME (dest,names)) loc src) l2 = d,l1` THEN
   REWRITE_TAC[data_live_compile_def; LET_DEF; LET_END_DEF; PAIR_EQ] THEN
   STRIP_TAC THEN RVEQ_TAC) THEN
  (UNDISCH_TAC `data_evaluate (data_Force (SOME (dest,names)) loc src,s:(C,FFI)data_state) =
                res,s2` THEN
   SUBGOAL_THEN `data_get_var src (data_state_locals (t1:(C,FFI)data_state)) =
                 data_get_var src (data_state_locals (s:(C,FFI)data_state))` ASSUME_TAC THENL
    [REWRITE_TAC[data_get_var_def] THEN CONV_TAC SYM_CONV THEN
     MATCH_MP_TAC DATAPAUX_LIVE_rel_lookup THEN
     EXISTS_TAC `insert src one (inter names (delete dest (l2:num_set)))` THEN
     ASM_REWRITE_TAC[domain_insert; IN_INSERT]; ALL_TAC] THEN
   REWRITE_TAC[data_evaluate_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
   TOP_CASE_TAC THENL [DATAPAUX_LIVE_ERR_TAC; ALL_TAC] THEN
   TOP_CASE_TAC THENL [DATAPAUX_LIVE_ERR_TAC; DATAPAUX_LIVE_ERR_TAC; ALL_TAC]) THEN
  TOP_CASE_TAC THENL
   [DATAPAUX_LIVE_FORCE_CUT_TAC THEN (DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) THEN
   REWRITE_TAC[UNWIND_THM1; option_CASE] THEN
   MATCH_MP_TAC DATAPAUX_LIVE_rel_set_var THEN MATCH_MP_TAC DATAPAUX_LIVE_rel_with_locals THEN
   EXISTS_TAC `insert src one (inter names (delete dest (l2:num_set)))` THEN
   ASM_REWRITE_TAC[]);
    (TOP_CASE_TAC THENL [DATAPAUX_LIVE_ERR_TAC; ALL_TAC] THEN
   TOP_CASE_TAC THEN TOP_CASE_TAC THEN
   DATAPAUX_LIVE_FORCE_CUT_TAC THEN
   COND_CASES_TAC THENL
    [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
     REWRITE_TAC[UNWIND_THM1; option_CASE] THEN
     UNDISCH_TAC `data_liveProof_state_rel (s:(C,FFI)data_state) t1
                    (insert src one (inter names (delete dest (l2:num_set))))` THEN
     REWRITE_TAC[data_liveProof_state_rel_def; data_state_INFO.ri_accfupds; K_THM;
                 data_call_env_def; data_push_env_def; data_dec_clock_def; LET_DEF; LET_END_DEF;
                 domain_def; NOT_IN_EMPTY] THEN SIMP_TAC[];
     ALL_TAC]) THEN
  (REWRITE_TAC[] THEN
   FIRST_ASSUM(fun th -> ONCE_REWRITE_TAC[SPECL
     [`x:data_v list`; `y':num option`; `env:data_v spt`;
      `mk_wf (inter (data_state_locals (t1:(C,FFI)data_state))
                    (inter (names:num_set) (delete dest (l2:num_set))))`; `F`]
     (MATCH_MP DATAPAUX_LIVE_call_push_frame th)]) THEN
   MP_TAC(ISPEC `data_evaluate (x',data_call_env x y'
                   (data_push_env env F (data_dec_clock (s:(C,FFI)data_state))))`
            PAIR_SURJECTIVE) THEN
   DISCH_THEN(X_CHOOSE_THEN `r:((data_v list,data_v)result)option`
     (X_CHOOSE_THEN `s3:(C,FFI)data_state` ASSUME_TAC)) THEN
   ASM_REWRITE_TAC[pair_CASE] THEN
   MP_TAC(ISPEC `r:((data_v list,data_v)result)option` (cases "option")) THEN
   DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC
     (X_CHOOSE_THEN `res2:(data_v list,data_v)result` SUBST_ALL_TAC)) THEN
   CASE_REWRITE_TAC[] THENL [DATAPAUX_LIVE_ERR_TAC; ALL_TAC]) THEN
  (MP_TAC(ISPEC `res2:(data_v list,data_v)result` (cases "result")) THEN
   DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `vs:data_v list` SUBST_ALL_TAC)
     (X_CHOOSE_THEN `e:(data_v)error_result` SUBST_ALL_TAC)) THEN
   CASE_REWRITE_TAC[] THENL
    [MP_TAC(ISPECL [`x':data_prog`; DATAPAUX_LIVE_FS_S; `vs:data_v list`; `s3:(C,FFI)data_state`;
                    mk_icomb(`data_state_stack:(C,FFI)data_state->stack list`, DATAPAUX_LIVE_FS_T);
                    mk_icomb(`data_state_stack_max:(C,FFI)data_state->num option`, DATAPAUX_LIVE_FS_T);
                    mk_icomb(`data_state_safe_for_space:(C,FFI)data_state->bool`, DATAPAUX_LIVE_FS_T);
                    `data_state_peak_heap_length (t1:(C,FFI)data_state)`] DATAPAUX_LIVE_swap_rval) THEN
     ANTS_TAC THENL
      [ASM_REWRITE_TAC[data_call_env_def; data_push_env_def; data_dec_clock_def; LET_DEF;
                       LET_END_DEF; data_state_INFO.ri_accfupds; K_THM; LENGTH];
       ALL_TAC] THEN
     STRIP_TAC THEN ASM_REWRITE_TAC[pair_CASE] THEN CASE_REWRITE_TAC[] THEN
     (REWRITE_TAC[data_call_env_def; data_push_env_def; data_dec_clock_def;
               LET_DEF; LET_END_DEF; data_state_INFO.ri_accfupds; K_THM]) THEN
     (FIRST_X_ASSUM(fun th ->
     if is_eq (concl th) && lhs (concl th) = `data_state_stack (s3:(C,FFI)data_state)`
     then ASSUME_TAC (REWRITE_RULE[data_call_env_def; data_push_env_def; data_dec_clock_def;
                       LET_DEF; LET_END_DEF; data_state_INFO.ri_accfupds; K_THM] th)
     else failwith "no") THEN
   FIRST_X_ASSUM(fun th ->
     if is_eq (concl th) && lhs (concl th) = `data_state_handler (s3:(C,FFI)data_state)`
     then ASSUME_TAC (REWRITE_RULE[data_call_env_def; data_push_env_def; data_dec_clock_def;
                       LET_DEF; LET_END_DEF; data_state_INFO.ri_accfupds; K_THM] th)
     else failwith "no") THEN
   COND_CASES_TAC THENL [ALL_TAC; DATAPAUX_LIVE_ERR_TAC]) THEN
     (REWRITE_TAC[] THEN
   FIRST_ASSUM(fun th ->
     if is_eq (concl th) && lhs (concl th) = `data_state_stack (s3:(C,FFI)data_state)`
     then REWRITE_TAC[data_pop_env_def; th] else failwith "no") THEN
   REWRITE_TAC[data_pop_env_def; data_state_INFO.ri_accfupds; K_THM] THEN
   CASE_REWRITE_TAC[] THEN
   REWRITE_TAC[PAIR_EQ] THEN
   DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) THEN
   REWRITE_TAC[UNWIND_THM1; option_CASE]) THEN
     (MATCH_MP_TAC DATAPAUX_LIVE_rel_set_var THEN MATCH_MP_TAC DATAPAUX_LIVE_rel_with_locals THEN
   EXISTS_TAC `LN:num_set` THEN ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[data_liveProof_state_rel_def; data_state_INFO.ri_accfupds; K_THM;
               domain_def; NOT_IN_EMPTY] THEN
   ASM_REWRITE_TAC[]);
     MP_TAC(ISPEC `e:(data_v)error_result` (cases "error_result")) THEN
   DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `v:data_v` SUBST_ALL_TAC)
     (X_CHOOSE_THEN `a:abort` SUBST_ALL_TAC)) THEN
   CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
   DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) THENL
    [MP_TAC(ISPECL [`x':data_prog`; DATAPAUX_LIVE_FS_S; `v:data_v`; `s3:(C,FFI)data_state`;
                    mk_icomb(`data_state_stack:(C,FFI)data_state->stack list`, DATAPAUX_LIVE_FS_T);
                    mk_icomb(`data_state_stack_max:(C,FFI)data_state->num option`, DATAPAUX_LIVE_FS_T);
                    mk_icomb(`data_state_safe_for_space:(C,FFI)data_state->bool`, DATAPAUX_LIVE_FS_T);
                    `data_state_peak_heap_length (t1:(C,FFI)data_state)`] DATAPAUX_LIVE_swap_raise) THEN
     ANTS_TAC THENL
      [ASM_REWRITE_TAC[data_call_env_def; data_push_env_def; data_dec_clock_def; LET_DEF;
                       LET_END_DEF; data_state_INFO.ri_accfupds; K_THM; LENGTH];
       ALL_TAC] THEN
     DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `s4:(C,FFI)data_state` STRIP_ASSUME_TAC)
                                (LABEL_TAC "sw")) THEN
     (MP_TAC(ISPECL [`s:(C,FFI)data_state`; DATAPAUX_LIVE_FS_S;
                  `data_state_locals_size (s:(C,FFI)data_state)`; `env:data_v spt`;
                  `s4:(C,FFI)data_state`] DSEMAUX_jump_exc_Env_cons2) THEN
   ANTS_TAC THENL
    [ASM_REWRITE_TAC[data_call_env_def; data_push_env_def; data_dec_clock_def; LET_DEF;
                     LET_END_DEF; data_state_INFO.ri_accfupds; K_THM];
     ALL_TAC] THEN
   DISCH_THEN(X_CHOOSE_THEN `s5:(C,FFI)data_state` STRIP_ASSUME_TAC) THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `s5:(C,FFI)data_state` o
     check (fun th -> is_forall (concl th) &&
              can (find_term ((=) `data_jump_exc (s:(C,FFI)data_state)`)) (concl th))) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `t3:(C,FFI)data_state` STRIP_ASSUME_TAC) THEN
   MP_TAC(ISPECL [`t1:(C,FFI)data_state`;
                  mk_icomb(mk_icomb(`data_state_stack_fupd:(stack list->stack list)->(C,FFI)data_state->(C,FFI)data_state`,
                                    mk_icomb(`K:stack list->stack list->stack list`,
                                             mk_icomb(`data_state_stack:(C,FFI)data_state->stack list`, DATAPAUX_LIVE_FS_T))),
                           DATAPAUX_LIVE_FS_S);
                  `data_state_locals_size (t1:(C,FFI)data_state)`;
                  `mk_wf (inter (data_state_locals (t1:(C,FFI)data_state))
                                (inter (names:num_set) (delete dest (l2:num_set))))`;
                  `t3:(C,FFI)data_state`] DSEMAUX_jump_exc_Env_cons3) THEN
   ANTS_TAC THENL
    [ASM_REWRITE_TAC[data_call_env_def; data_push_env_def; data_dec_clock_def; LET_DEF;
                     LET_END_DEF; data_state_INFO.ri_accfupds; K_THM];
     ALL_TAC] THEN
   DISCH_THEN(X_CHOOSE_THEN `s7:(C,FFI)data_state` STRIP_ASSUME_TAC) THEN
   REMOVE_THEN "sw" (MP_TAC o SPEC `s7:(C,FFI)data_state`) THEN ASM_REWRITE_TAC[] THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[pair_CASE; option_CASE] THEN CASE_REWRITE_TAC[] THEN
   REWRITE_TAC[PAIR_EQ; UNWIND_THM1] THEN
   REWRITE_TAC[data_liveProof_state_rel_def; data_state_INFO.ri_accfupds; K_THM;
               domain_def; NOT_IN_EMPTY] THEN
   ASM_REWRITE_TAC[]);
     (MP_TAC(ISPECL [`x':data_prog`; DATAPAUX_LIVE_FS_S; `a:abort`; `s3:(C,FFI)data_state`;
                  mk_icomb(`data_state_stack:(C,FFI)data_state->stack list`, DATAPAUX_LIVE_FS_T);
                  mk_icomb(`data_state_stack_max:(C,FFI)data_state->num option`, DATAPAUX_LIVE_FS_T);
                  mk_icomb(`data_state_safe_for_space:(C,FFI)data_state->bool`, DATAPAUX_LIVE_FS_T);
                  `data_state_peak_heap_length (t1:(C,FFI)data_state)`] DATAPAUX_LIVE_swap_abort) THEN
   ANTS_TAC THENL
    [RULE_ASSUM_TAC(REWRITE_RULE[option_INJ; injectivity "result";
                                 injectivity "error_result"]) THEN
     ASM_REWRITE_TAC[data_call_env_def; data_push_env_def; data_dec_clock_def; LET_DEF;
                     LET_END_DEF; data_state_INFO.ri_accfupds; K_THM; LENGTH];
     ALL_TAC] THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[pair_CASE; option_CASE] THEN CASE_REWRITE_TAC[] THEN
   REWRITE_TAC[PAIR_EQ; UNWIND_THM1] THEN
   REWRITE_TAC[data_liveProof_state_rel_def; data_state_INFO.ri_accfupds; K_THM;
               domain_def; NOT_IN_EMPTY])]])];;

(* HOL4: evaluate_compile[Force] (Force_NONE and Force_SOME); the thunk   *)
(* code is not compiled by data_live, so the induction hypotheses are not *)
(* needed                                                                  *)
let DATAPAUX_LIVE_FORCE = prove
 (el 9 DATAPAUX_LIVE_CASES,
  REPEAT GEN_TAC THEN DISCH_THEN(K ALL_TAC) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP DATAPAUX_LIVE_rel_fields) THEN
  CASES_ON `ret:(num#num_set)option` THENL
   [DATAPAUX_LIVE_FORCE_NONE_TAC; DATAPAUX_LIVE_FORCE_SOME_TAC]);;

let DATAPAUX_LIVE_rel_set_vars = prove
 (`!(s:(C,FFI)data_state) t l ns xs.
     data_liveProof_state_rel s t (list_delete ns l) /\ LENGTH ns = LENGTH xs ==>
     data_liveProof_state_rel (data_set_vars ns xs s) (data_set_vars ns xs t) l`,
  REWRITE_TAC[data_liveProof_state_rel_def; data_set_vars_def;
              data_state_INFO.ri_accfupds; K_THM; lookup_union; lookup_fromAList;
              domain_list_delete; IN_DIFF; IN_SET_OF_LIST] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `ALOOKUP (ZIP (ns:num list) (xs:data_v list)) (x:num)` (cases "option")) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[option_CASE] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `ALOOKUP (ZIP (ns:num list) (xs:data_v list)) (x:num) = NONE` THEN
  ASM_SIMP_TAC[ALOOKUP_NONE; MAP_FST_ZIP]);;

let DATAPAUX_LIVE_jump_exc_frame2 = prove
 (`!(s:(C,FFI)data_state) (t:(C,FFI)data_state) (s0:(C,FFI)data_state)
    (t0:(C,FFI)data_state) l.
     (!s3. data_jump_exc s = SOME s3 ==>
           ?t3. data_jump_exc t = SOME t3 /\ data_liveProof_state_rel s3 t3 LN /\
                data_state_handler t3 = data_state_handler s3 /\
                LENGTH (data_state_stack t3) = LENGTH (data_state_stack s3)) /\
     data_state_stack s0 = data_state_stack s /\
     data_state_handler s0 = data_state_handler s /\
     data_state_stack t0 = data_state_stack t /\
     data_state_handler t0 = data_state_handler t /\
     data_liveProof_state_rel s0 t0 l ==>
     (!s3. data_jump_exc s0 = SOME s3 ==>
           ?t3. data_jump_exc t0 = SOME t3 /\ data_liveProof_state_rel s3 t3 LN /\
                data_state_handler t3 = data_state_handler s3 /\
                LENGTH (data_state_stack t3) = LENGTH (data_state_stack s3))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `s3:(C,FFI)data_state` THEN
  MP_TAC(ISPECL [`s:(C,FFI)data_state`; `s0:(C,FFI)data_state`] DSEMAUX_jump_exc_cong) THEN
  MP_TAC(ISPECL [`t:(C,FFI)data_state`; `t0:(C,FFI)data_state`] DSEMAUX_jump_exc_cong) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPEC `data_jump_exc (s:(C,FFI)data_state)` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `s4:(C,FFI)data_state` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[OPTION_MAP_DEF; option_DISTINCT; option_INJ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s4:(C,FFI)data_state`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t4:(C,FFI)data_state` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[OPTION_MAP_DEF; option_INJ; UNWIND_THM1] THEN
  REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM] THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `data_liveProof_state_rel (s0:(C,FFI)data_state) t0 l` THEN
  UNDISCH_TAC `LENGTH (data_state_stack (t4:(C,FFI)data_state)) =
               LENGTH (data_state_stack (s4:(C,FFI)data_state))` THEN
  REWRITE_TAC[data_liveProof_state_rel_def; data_state_INFO.ri_accfupds; K_THM;
              domain_def; NOT_IN_EMPTY] THEN
  SIMP_TAC[]);;

let DATAPAUX_LIVE_CUT_TAC (l:term) (l':term) : tactic =
  MP_TAC(ISPEC `data_cut_env names (data_state_locals (s:(C,FFI)data_state))`
           (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `env:data_v spt` ASSUME_TAC)) THENL
   [ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN DATAPAUX_LIVE_ERR_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:(C,FFI)data_state`; `t1:(C,FFI)data_state`; `names:num_set`;
                 l; l'; `env:data_v spt`] DATAPAUX_LIVE_cut_env) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[SUBSET; domain_insert; IN_INSERT; domain_list_insert] THEN
    MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[];;

let DATAPAUX_LIVE_CN_S = `data_call_env x y' (data_push_env env F (data_dec_clock (s:(C,FFI)data_state)))`;;
let DATAPAUX_LIVE_CN_T = `data_call_env x y' (data_push_env (mk_wf (inter (data_state_locals (t1:(C,FFI)data_state)) (inter (names:num_set) (list_delete ns (l2:num_set))))) F (data_dec_clock t1))`;;
let DATAPAUX_LIVE_CH_S = `data_call_env x y' (data_push_env env T (data_dec_clock (s:(C,FFI)data_state)))`;;
let DATAPAUX_LIVE_CH_T = `data_call_env x y' (data_push_env (mk_wf (inter (data_state_locals (t1:(C,FFI)data_state)) (inter (names:num_set) (union (list_delete ns (l2:num_set)) (delete var (l6:num_set)))))) T (data_dec_clock t1))`;;
let DATAPAUX_LIVE_CH_L0 = `union (list_delete ns (l2:num_set)) (delete var (l6:num_set))`;;

let DATAPAUX_LIVE_CALL_TAIL_TAC : tactic =
  UNDISCH_TAC `data_live_compile (data_Call NONE dest args handler) l2 = d,l1` THEN
     REWRITE_TAC[data_live_compile_def; PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
     UNDISCH_TAC `data_evaluate (data_Call NONE dest args handler,s:(C,FFI)data_state) = res,s2` THEN
     SUBGOAL_THEN `data_get_vars args (data_state_locals (t1:(C,FFI)data_state)) =
                   data_get_vars args (data_state_locals (s:(C,FFI)data_state))` ASSUME_TAC THENL
      [MATCH_MP_TAC EVERY_get_vars THEN REWRITE_TAC[GSYM ALL_MEM] THEN
       X_GEN_TAC `a:num` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
       MATCH_MP_TAC DATAPAUX_LIVE_rel_lookup THEN
       EXISTS_TAC `list_to_num_set args` THEN ASM_REWRITE_TAC[domain_list_to_num_set];
       ALL_TAC] THEN
     REWRITE_TAC[data_evaluate_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  TOP_CASE_TAC THENL [DATAPAUX_LIVE_ERR_TAC; ALL_TAC] THEN
   TOP_CASE_TAC THENL [DATAPAUX_LIVE_ERR_TAC; ALL_TAC] THEN
   TOP_CASE_TAC THEN TOP_CASE_TAC THEN
   COND_CASES_TAC THENL [ALL_TAC; DATAPAUX_LIVE_ERR_TAC] THEN
   COND_CASES_TAC THENL
    [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
     REWRITE_TAC[UNWIND_THM1; option_CASE] THEN
     MATCH_MP_TAC DATAPAUX_LIVE_rel_flush_state THEN ASM_MESON_TAC[];
     ALL_TAC] THEN
   REWRITE_TAC[] THEN
   FIRST_ASSUM(fun th -> ONCE_REWRITE_TAC[MATCH_MP DATAPAUX_LIVE_call_env_frame th]) THEN
   MP_TAC(ISPEC `data_evaluate (x',data_call_env x y' (data_dec_clock (s:(C,FFI)data_state)))`
            PAIR_SURJECTIVE) THEN
   DISCH_THEN(X_CHOOSE_THEN `r:((data_v list,data_v)result)option`
     (X_CHOOSE_THEN `s3:(C,FFI)data_state` ASSUME_TAC)) THEN
   ASM_REWRITE_TAC[pair_CASE] THEN
   MP_TAC(ISPEC `r:((data_v list,data_v)result)option` (cases "option")) THEN
   DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC
     (X_CHOOSE_THEN `res2:(data_v list,data_v)result` SUBST_ALL_TAC)) THEN
   CASE_REWRITE_TAC[] THENL [DATAPAUX_LIVE_ERR_TAC; ALL_TAC] THEN
   REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
   MP_TAC(ISPECL [`x':data_prog`; `data_call_env x y' (data_dec_clock (s:(C,FFI)data_state))`;
                  `res2:(data_v list,data_v)result`; `s2:(C,FFI)data_state`;
                  `data_state_stack (t1:(C,FFI)data_state)`;
                  `data_state_stack_max (data_call_env x y' (data_dec_clock (t1:(C,FFI)data_state)))`;
                  `data_state_safe_for_space (data_call_env x y' (data_dec_clock (t1:(C,FFI)data_state)))`;
                  `data_state_peak_heap_length (t1:(C,FFI)data_state)`] DATAPAUX_LIVE_tail) THEN
   ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN
     CONJ_TAC THENL [FS[]; ALL_TAC] THEN
     REWRITE_TAC[data_call_env_def; data_dec_clock_def; LET_DEF; LET_END_DEF;
                 data_state_INFO.ri_accfupds; K_THM] THEN
     ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC DATAPAUX_LIVE_jump_exc_frame THEN
     MAP_EVERY EXISTS_TAC [`s:(C,FFI)data_state`; `t1:(C,FFI)data_state`] THEN
     ASM_REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM];
     ALL_TAC] THEN
   DISCH_THEN(X_CHOOSE_THEN `t2:(C,FFI)data_state` STRIP_ASSUME_TAC) THEN
   ASM_REWRITE_TAC[pair_CASE; option_CASE; PAIR_EQ; UNWIND_THM1];;

let DATAPAUX_LIVE_CALL_RET_TAC : tactic =
  MP_TAC(ISPEC `a:num list#num_set` PAIR_SURJECTIVE) THEN
   DISCH_THEN(X_CHOOSE_THEN `ns:num list` (X_CHOOSE_THEN `names:num_set` SUBST_ALL_TAC)) THEN
   CASES_ON `handler:(num#data_prog)option` THENL 
   [(UNDISCH_TAC `data_live_compile (data_Call (SOME (ns,names)) dest args NONE) l2 = d,l1` THEN
   REWRITE_TAC[data_live_compile_def; LET_DEF; LET_END_DEF; PAIR_EQ] THEN
   STRIP_TAC THEN RVEQ_TAC THEN
   UNDISCH_TAC `data_evaluate (data_Call (SOME (ns,names)) dest args NONE,s:(C,FFI)data_state) =
                res,s2` THEN
   SUBGOAL_THEN `data_get_vars args (data_state_locals (t1:(C,FFI)data_state)) =
                 data_get_vars args (data_state_locals (s:(C,FFI)data_state))` ASSUME_TAC THENL
    [MATCH_MP_TAC EVERY_get_vars THEN REWRITE_TAC[GSYM ALL_MEM] THEN
     X_GEN_TAC `a:num` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
     MATCH_MP_TAC DATAPAUX_LIVE_rel_lookup THEN
     EXISTS_TAC `list_insert args (inter names (list_delete ns (l2:num_set)))` THEN
     ASM_REWRITE_TAC[domain_list_insert];
     ALL_TAC] THEN
   REWRITE_TAC[data_evaluate_def; IS_SOME_DEF] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
   TOP_CASE_TAC THENL [DATAPAUX_LIVE_ERR_TAC; ALL_TAC] THEN
   TOP_CASE_TAC THENL [DATAPAUX_LIVE_ERR_TAC; ALL_TAC] THEN
   TOP_CASE_TAC THEN TOP_CASE_TAC THEN
   COND_CASES_TAC THENL [DATAPAUX_LIVE_ERR_TAC; ALL_TAC]) THEN
  (REWRITE_TAC[] THEN
   DATAPAUX_LIVE_CUT_TAC `list_delete ns (l2:num_set)`
     `list_insert args (inter names (list_delete ns (l2:num_set)))` THEN
   COND_CASES_TAC THENL
    [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
     REWRITE_TAC[UNWIND_THM1; option_CASE] THEN
     UNDISCH_TAC `data_liveProof_state_rel (s:(C,FFI)data_state) t1
                    (list_insert args (inter names (list_delete ns (l2:num_set))))` THEN
     REWRITE_TAC[data_liveProof_state_rel_def; data_state_INFO.ri_accfupds; K_THM;
                 data_call_env_def; data_push_env_def; data_dec_clock_def; LET_DEF; LET_END_DEF;
                 domain_def; NOT_IN_EMPTY] THEN SIMP_TAC[];
     ALL_TAC] THEN
   REWRITE_TAC[] THEN
   FIRST_ASSUM(fun th -> ONCE_REWRITE_TAC[SPECL
     [`x:data_v list`; `y':num option`; `env:data_v spt`;
      `mk_wf (inter (data_state_locals (t1:(C,FFI)data_state))
                    (inter (names:num_set) (list_delete ns (l2:num_set))))`; `F`]
     (MATCH_MP DATAPAUX_LIVE_call_push_frame th)]) THEN
   MP_TAC(ISPEC `data_evaluate (x',data_call_env x y'
                   (data_push_env env F (data_dec_clock (s:(C,FFI)data_state))))`
            PAIR_SURJECTIVE) THEN
   DISCH_THEN(X_CHOOSE_THEN `r:((data_v list,data_v)result)option`
     (X_CHOOSE_THEN `s3:(C,FFI)data_state` ASSUME_TAC)) THEN
   ASM_REWRITE_TAC[pair_CASE] THEN
   MP_TAC(ISPEC `r:((data_v list,data_v)result)option` (cases "option")) THEN
   DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC
     (X_CHOOSE_THEN `res2:(data_v list,data_v)result` SUBST_ALL_TAC)) THEN
   CASE_REWRITE_TAC[] THENL [DATAPAUX_LIVE_ERR_TAC; ALL_TAC]) THEN
  (MP_TAC(ISPEC `res2:(data_v list,data_v)result` (cases "result")) THEN
   DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `vs:data_v list` SUBST_ALL_TAC)
     (X_CHOOSE_THEN `e:(data_v)error_result` SUBST_ALL_TAC)) THEN
   CASE_REWRITE_TAC[] THENL
    [MP_TAC(ISPECL [`x':data_prog`; DATAPAUX_LIVE_CN_S; `vs:data_v list`; `s3:(C,FFI)data_state`;
                    mk_icomb(`data_state_stack:(C,FFI)data_state->stack list`, DATAPAUX_LIVE_CN_T);
                    mk_icomb(`data_state_stack_max:(C,FFI)data_state->num option`, DATAPAUX_LIVE_CN_T);
                    mk_icomb(`data_state_safe_for_space:(C,FFI)data_state->bool`, DATAPAUX_LIVE_CN_T);
                    `data_state_peak_heap_length (t1:(C,FFI)data_state)`] DATAPAUX_LIVE_swap_rval) THEN
     ANTS_TAC THENL
      [ASM_REWRITE_TAC[data_call_env_def; data_push_env_def; data_dec_clock_def; LET_DEF;
                       LET_END_DEF; data_state_INFO.ri_accfupds; K_THM; LENGTH];
       ALL_TAC] THEN
     STRIP_TAC THEN ASM_REWRITE_TAC[pair_CASE] THEN CASE_REWRITE_TAC[] THEN
     (REWRITE_TAC[data_call_env_def; data_push_env_def; data_dec_clock_def;
               LET_DEF; LET_END_DEF; data_state_INFO.ri_accfupds; K_THM]) THEN
     (FIRST_X_ASSUM(fun th ->
     if is_eq (concl th) && lhs (concl th) = `data_state_stack (s3:(C,FFI)data_state)`
     then ASSUME_TAC (REWRITE_RULE[data_call_env_def; data_push_env_def; data_dec_clock_def;
                       LET_DEF; LET_END_DEF; data_state_INFO.ri_accfupds; K_THM] th)
     else failwith "no") THEN
   FIRST_X_ASSUM(fun th ->
     if is_eq (concl th) && lhs (concl th) = `data_state_handler (s3:(C,FFI)data_state)`
     then ASSUME_TAC (REWRITE_RULE[data_call_env_def; data_push_env_def; data_dec_clock_def;
                       LET_DEF; LET_END_DEF; data_state_INFO.ri_accfupds; K_THM] th)
     else failwith "no") THEN
   COND_CASES_TAC THENL [ALL_TAC; DATAPAUX_LIVE_ERR_TAC]) THEN
     (REWRITE_TAC[] THEN
   FIRST_ASSUM(fun th ->
     if is_eq (concl th) && lhs (concl th) = `data_state_stack (s3:(C,FFI)data_state)`
     then REWRITE_TAC[data_pop_env_def; th] else failwith "no") THEN
   REWRITE_TAC[data_pop_env_def; data_state_INFO.ri_accfupds; K_THM] THEN
   CASE_REWRITE_TAC[] THEN
   REWRITE_TAC[PAIR_EQ] THEN
   DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) THEN
   REWRITE_TAC[UNWIND_THM1; option_CASE]) THEN
     (MATCH_MP_TAC DATAPAUX_LIVE_rel_set_vars THEN
   CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
   MATCH_MP_TAC DATAPAUX_LIVE_rel_with_locals THEN
   EXISTS_TAC `LN:num_set` THEN ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[data_liveProof_state_rel_def; data_state_INFO.ri_accfupds; K_THM;
               domain_def; NOT_IN_EMPTY] THEN
   ASM_REWRITE_TAC[]);
     MP_TAC(ISPEC `e:(data_v)error_result` (cases "error_result")) THEN
   DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `v:data_v` SUBST_ALL_TAC)
     (X_CHOOSE_THEN `a:abort` SUBST_ALL_TAC)) THEN
   CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
   DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) THENL
    [MP_TAC(ISPECL [`x':data_prog`; DATAPAUX_LIVE_CN_S; `v:data_v`; `s3:(C,FFI)data_state`;
                    mk_icomb(`data_state_stack:(C,FFI)data_state->stack list`, DATAPAUX_LIVE_CN_T);
                    mk_icomb(`data_state_stack_max:(C,FFI)data_state->num option`, DATAPAUX_LIVE_CN_T);
                    mk_icomb(`data_state_safe_for_space:(C,FFI)data_state->bool`, DATAPAUX_LIVE_CN_T);
                    `data_state_peak_heap_length (t1:(C,FFI)data_state)`] DATAPAUX_LIVE_swap_raise) THEN
     ANTS_TAC THENL
      [ASM_REWRITE_TAC[data_call_env_def; data_push_env_def; data_dec_clock_def; LET_DEF;
                       LET_END_DEF; data_state_INFO.ri_accfupds; K_THM; LENGTH];
       ALL_TAC] THEN
     DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `s4:(C,FFI)data_state` STRIP_ASSUME_TAC)
                                (LABEL_TAC "sw")) THEN
     (MP_TAC(ISPECL [`s:(C,FFI)data_state`; DATAPAUX_LIVE_CN_S;
                  `data_state_locals_size (s:(C,FFI)data_state)`; `env:data_v spt`;
                  `s4:(C,FFI)data_state`] DSEMAUX_jump_exc_Env_cons2) THEN
   ANTS_TAC THENL
    [ASM_REWRITE_TAC[data_call_env_def; data_push_env_def; data_dec_clock_def; LET_DEF;
                     LET_END_DEF; data_state_INFO.ri_accfupds; K_THM];
     ALL_TAC] THEN
   DISCH_THEN(X_CHOOSE_THEN `s5:(C,FFI)data_state` STRIP_ASSUME_TAC) THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `s5:(C,FFI)data_state` o
     check (fun th -> is_forall (concl th) &&
              can (find_term ((=) `data_jump_exc (s:(C,FFI)data_state)`)) (concl th))) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `t3:(C,FFI)data_state` STRIP_ASSUME_TAC) THEN
   MP_TAC(ISPECL [`t1:(C,FFI)data_state`;
                  mk_icomb(mk_icomb(`data_state_stack_fupd:(stack list->stack list)->(C,FFI)data_state->(C,FFI)data_state`,
                                    mk_icomb(`K:stack list->stack list->stack list`,
                                             mk_icomb(`data_state_stack:(C,FFI)data_state->stack list`, DATAPAUX_LIVE_CN_T))),
                           DATAPAUX_LIVE_CN_S);
                  `data_state_locals_size (t1:(C,FFI)data_state)`;
                  `mk_wf (inter (data_state_locals (t1:(C,FFI)data_state))
                                (inter (names:num_set) (list_delete ns (l2:num_set))))`;
                  `t3:(C,FFI)data_state`] DSEMAUX_jump_exc_Env_cons3) THEN
   ANTS_TAC THENL
    [ASM_REWRITE_TAC[data_call_env_def; data_push_env_def; data_dec_clock_def; LET_DEF;
                     LET_END_DEF; data_state_INFO.ri_accfupds; K_THM];
     ALL_TAC] THEN
   DISCH_THEN(X_CHOOSE_THEN `s7:(C,FFI)data_state` STRIP_ASSUME_TAC) THEN
   REMOVE_THEN "sw" (MP_TAC o SPEC `s7:(C,FFI)data_state`) THEN ASM_REWRITE_TAC[] THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[pair_CASE; option_CASE] THEN CASE_REWRITE_TAC[] THEN
   REWRITE_TAC[PAIR_EQ; UNWIND_THM1] THEN
   REWRITE_TAC[data_liveProof_state_rel_def; data_state_INFO.ri_accfupds; K_THM;
               domain_def; NOT_IN_EMPTY] THEN
   ASM_REWRITE_TAC[]);
     (MP_TAC(ISPECL [`x':data_prog`; DATAPAUX_LIVE_CN_S; `a:abort`; `s3:(C,FFI)data_state`;
                  mk_icomb(`data_state_stack:(C,FFI)data_state->stack list`, DATAPAUX_LIVE_CN_T);
                  mk_icomb(`data_state_stack_max:(C,FFI)data_state->num option`, DATAPAUX_LIVE_CN_T);
                  mk_icomb(`data_state_safe_for_space:(C,FFI)data_state->bool`, DATAPAUX_LIVE_CN_T);
                  `data_state_peak_heap_length (t1:(C,FFI)data_state)`] DATAPAUX_LIVE_swap_abort) THEN
   ANTS_TAC THENL
    [RULE_ASSUM_TAC(REWRITE_RULE[option_INJ; injectivity "result";
                                 injectivity "error_result"]) THEN
     ASM_REWRITE_TAC[data_call_env_def; data_push_env_def; data_dec_clock_def; LET_DEF;
                     LET_END_DEF; data_state_INFO.ri_accfupds; K_THM; LENGTH];
     ALL_TAC] THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[pair_CASE; option_CASE] THEN CASE_REWRITE_TAC[] THEN
   REWRITE_TAC[PAIR_EQ; UNWIND_THM1] THEN
   REWRITE_TAC[data_liveProof_state_rel_def; data_state_INFO.ri_accfupds; K_THM;
               domain_def; NOT_IN_EMPTY])]]);
   (MP_TAC(ISPEC `a':num#data_prog` PAIR_SURJECTIVE) THEN
   DISCH_THEN(X_CHOOSE_THEN `var:num` (X_CHOOSE_THEN `handle:data_prog` SUBST_ALL_TAC)) THEN
   MP_TAC(ISPEC `data_live_compile handle l2` PAIR_SURJECTIVE) THEN
   DISCH_THEN(X_CHOOSE_THEN `d6:data_prog` (X_CHOOSE_THEN `l6:num_set` ASSUME_TAC)) THEN
   UNDISCH_TAC `data_live_compile (data_Call (SOME (ns,names)) dest args (SOME (var,handle))) l2 =
                d,l1` THEN
   ASM_REWRITE_TAC[data_live_compile_def; LET_DEF; LET_END_DEF; PAIR_EQ; pair_CASE] THEN
   STRIP_TAC THEN RVEQ_TAC THEN
   UNDISCH_TAC `data_evaluate (data_Call (SOME (ns,names)) dest args (SOME (var,handle)),
                               s:(C,FFI)data_state) = res,s2` THEN
   SUBGOAL_THEN `data_get_vars args (data_state_locals (t1:(C,FFI)data_state)) =
                 data_get_vars args (data_state_locals (s:(C,FFI)data_state))` ASSUME_TAC THENL
    [MATCH_MP_TAC EVERY_get_vars THEN REWRITE_TAC[GSYM ALL_MEM] THEN
     X_GEN_TAC `a:num` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
     MATCH_MP_TAC DATAPAUX_LIVE_rel_lookup THEN
     EXISTS_TAC (mk_icomb(mk_icomb(`list_insert`,`args:num list`),
                          mk_icomb(mk_icomb(`inter:num_set->num_set->num_set`,`names:num_set`),
                                   DATAPAUX_LIVE_CH_L0))) THEN
     ASM_REWRITE_TAC[domain_list_insert];
     ALL_TAC] THEN
   REWRITE_TAC[data_evaluate_def; IS_SOME_DEF] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
   TOP_CASE_TAC THENL [DATAPAUX_LIVE_ERR_TAC; ALL_TAC] THEN
   TOP_CASE_TAC THENL [DATAPAUX_LIVE_ERR_TAC; ALL_TAC] THEN
   TOP_CASE_TAC THEN TOP_CASE_TAC THEN
   COND_CASES_TAC THENL [DATAPAUX_LIVE_ERR_TAC; ALL_TAC] THEN
   REWRITE_TAC[] THEN
   DATAPAUX_LIVE_CUT_TAC DATAPAUX_LIVE_CH_L0
     (mk_icomb(mk_icomb(`list_insert`,`args:num list`),
               mk_icomb(mk_icomb(`inter:num_set->num_set->num_set`,`names:num_set`),
                        DATAPAUX_LIVE_CH_L0))) THEN
   COND_CASES_TAC THENL
    [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
     REWRITE_TAC[UNWIND_THM1; option_CASE] THEN
     FIRST_X_ASSUM(MP_TAC o check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) =
                                    "data_liveProof_state_rel" with _ -> false)) THEN
     REWRITE_TAC[data_liveProof_state_rel_def; data_state_INFO.ri_accfupds; K_THM;
                 data_call_env_def; data_push_env_def; data_dec_clock_def; LET_DEF; LET_END_DEF;
                 domain_def; NOT_IN_EMPTY] THEN SIMP_TAC[];
     ALL_TAC] THEN
   REWRITE_TAC[] THEN
   FIRST_ASSUM(fun th -> ONCE_REWRITE_TAC[SPECL
     [`x:data_v list`; `y':num option`; `env:data_v spt`;
      mk_icomb(`mk_wf:data_v spt->data_v spt`,
        mk_icomb(mk_icomb(`inter:data_v spt->num_set->data_v spt`,
                          `data_state_locals (t1:(C,FFI)data_state)`),
                 mk_icomb(mk_icomb(`inter:num_set->num_set->num_set`,`names:num_set`),
                          DATAPAUX_LIVE_CH_L0))); `T`]
     (MATCH_MP DATAPAUX_LIVE_call_push_frame th)]) THEN
   MP_TAC(ISPEC `data_evaluate (x',data_call_env x y'
                   (data_push_env env T (data_dec_clock (s:(C,FFI)data_state))))`
            PAIR_SURJECTIVE) THEN
   DISCH_THEN(X_CHOOSE_THEN `r:((data_v list,data_v)result)option`
     (X_CHOOSE_THEN `s3:(C,FFI)data_state` ASSUME_TAC)) THEN
   ASM_REWRITE_TAC[pair_CASE] THEN
   MP_TAC(ISPEC `r:((data_v list,data_v)result)option` (cases "option")) THEN
   DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC
     (X_CHOOSE_THEN `res2:(data_v list,data_v)result` SUBST_ALL_TAC)) THEN
   CASE_REWRITE_TAC[] THENL [DATAPAUX_LIVE_ERR_TAC; ALL_TAC]) THEN
  (MP_TAC(ISPEC `res2:(data_v list,data_v)result` (cases "result")) THEN
   DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `vs:data_v list` SUBST_ALL_TAC)
     (X_CHOOSE_THEN `e:(data_v)error_result` SUBST_ALL_TAC)) THEN
   CASE_REWRITE_TAC[] THENL
    [MP_TAC(ISPECL [`x':data_prog`; DATAPAUX_LIVE_CH_S; `vs:data_v list`; `s3:(C,FFI)data_state`;
                    mk_icomb(`data_state_stack:(C,FFI)data_state->stack list`, DATAPAUX_LIVE_CH_T);
                    mk_icomb(`data_state_stack_max:(C,FFI)data_state->num option`, DATAPAUX_LIVE_CH_T);
                    mk_icomb(`data_state_safe_for_space:(C,FFI)data_state->bool`, DATAPAUX_LIVE_CH_T);
                    `data_state_peak_heap_length (t1:(C,FFI)data_state)`] DATAPAUX_LIVE_swap_rval) THEN
     ANTS_TAC THENL
      [ASM_REWRITE_TAC[data_call_env_def; data_push_env_def; data_dec_clock_def; LET_DEF;
                       LET_END_DEF; data_state_INFO.ri_accfupds; K_THM; LENGTH];
       ALL_TAC] THEN
     STRIP_TAC THEN ASM_REWRITE_TAC[pair_CASE] THEN CASE_REWRITE_TAC[] THEN
     (REWRITE_TAC[data_call_env_def; data_push_env_def; data_dec_clock_def;
               LET_DEF; LET_END_DEF; data_state_INFO.ri_accfupds; K_THM]) THEN
     (FIRST_X_ASSUM(fun th ->
     if is_eq (concl th) && lhs (concl th) = `data_state_stack (s3:(C,FFI)data_state)`
     then ASSUME_TAC (REWRITE_RULE[data_call_env_def; data_push_env_def; data_dec_clock_def;
                       LET_DEF; LET_END_DEF; data_state_INFO.ri_accfupds; K_THM] th)
     else failwith "no") THEN
   FIRST_X_ASSUM(fun th ->
     if is_eq (concl th) && lhs (concl th) = `data_state_handler (s3:(C,FFI)data_state)`
     then ASSUME_TAC (REWRITE_RULE[data_call_env_def; data_push_env_def; data_dec_clock_def;
                       LET_DEF; LET_END_DEF; data_state_INFO.ri_accfupds; K_THM] th)
     else failwith "no") THEN
   COND_CASES_TAC THENL [ALL_TAC; DATAPAUX_LIVE_ERR_TAC]) THEN
     (REWRITE_TAC[] THEN
   FIRST_ASSUM(fun th ->
     if is_eq (concl th) && lhs (concl th) = `data_state_stack (s3:(C,FFI)data_state)`
     then REWRITE_TAC[data_pop_env_def; th] else failwith "no") THEN
   REWRITE_TAC[data_pop_env_def; data_state_INFO.ri_accfupds; K_THM] THEN
   CASE_REWRITE_TAC[] THEN
   REWRITE_TAC[PAIR_EQ] THEN
   DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) THEN
   REWRITE_TAC[UNWIND_THM1; option_CASE]) THEN
     (MATCH_MP_TAC DATAPAUX_LIVE_rel_set_vars THEN
   CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
   MATCH_MP_TAC DATAPAUX_LIVE_rel_with_locals THEN
   EXISTS_TAC `LN:num_set` THEN ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[data_liveProof_state_rel_def; data_state_INFO.ri_accfupds; K_THM;
               domain_def; NOT_IN_EMPTY] THEN
   ASM_REWRITE_TAC[]) THEN
     (X_GEN_TAC `z:num` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
   ASM_REWRITE_TAC[domain_union; IN_UNION]);
     MP_TAC(ISPEC `e:(data_v)error_result` (cases "error_result")) THEN
   DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `v:data_v` SUBST_ALL_TAC)
     (X_CHOOSE_THEN `a:abort` SUBST_ALL_TAC)) THEN
   CASE_REWRITE_TAC[] THENL [(DISCH_TAC THEN
   MP_TAC(ISPECL [`x':data_prog`; DATAPAUX_LIVE_CH_S; `v:data_v`; `s3:(C,FFI)data_state`;
                  mk_icomb(`data_state_stack:(C,FFI)data_state->stack list`, DATAPAUX_LIVE_CH_T);
                  mk_icomb(`data_state_stack_max:(C,FFI)data_state->num option`, DATAPAUX_LIVE_CH_T);
                  mk_icomb(`data_state_safe_for_space:(C,FFI)data_state->bool`, DATAPAUX_LIVE_CH_T);
                  `data_state_peak_heap_length (t1:(C,FFI)data_state)`] DATAPAUX_LIVE_swap_raise) THEN
   ANTS_TAC THENL
    [ASM_REWRITE_TAC[data_call_env_def; data_push_env_def; data_dec_clock_def; LET_DEF;
                     LET_END_DEF; data_state_INFO.ri_accfupds; K_THM; LENGTH];
     ALL_TAC] THEN
   DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `s4:(C,FFI)data_state` STRIP_ASSUME_TAC)
                              (LABEL_TAC "sw")) THEN
   MP_TAC(ISPECL [DATAPAUX_LIVE_CH_S; `data_state_locals_size (s:(C,FFI)data_state)`;
                  `env:data_v spt`; `data_state_handler (s:(C,FFI)data_state)`;
                  `data_state_stack (s:(C,FFI)data_state)`] DSEMAUX_jump_exc_Exc_top) THEN
   ANTS_TAC THENL
    [REWRITE_TAC[data_call_env_def; data_push_env_def; data_dec_clock_def; LET_DEF;
                 LET_END_DEF; data_state_INFO.ri_accfupds; K_THM];
     ALL_TAC] THEN
   ASM_REWRITE_TAC[option_INJ] THEN DISCH_THEN SUBST_ALL_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[data_state_INFO.ri_accfupds; K_THM]) THEN
   REMOVE_THEN "sw" (MP_TAC o SPEC
     (mk_icomb(mk_icomb(`data_state_handler_fupd:(num->num)->(C,FFI)data_state->(C,FFI)data_state`,
                        `K (data_state_handler (t1:(C,FFI)data_state)):num->num`),
      mk_icomb(mk_icomb(`data_state_locals_fupd:(data_v spt->data_v spt)->(C,FFI)data_state->(C,FFI)data_state`,
                        `K (mk_wf (inter (data_state_locals (t1:(C,FFI)data_state))
                               (inter (names:num_set) (union (list_delete ns (l2:num_set))
                                  (delete var (l6:num_set)))))):data_v spt->data_v spt`),
      mk_icomb(mk_icomb(`data_state_stack_fupd:(stack list->stack list)->(C,FFI)data_state->(C,FFI)data_state`,
                        `K (data_state_stack (t1:(C,FFI)data_state)):stack list->stack list`),
      mk_icomb(mk_icomb(`data_state_locals_size_fupd:(num option->num option)->(C,FFI)data_state->(C,FFI)data_state`,
                        `K (data_state_locals_size (t1:(C,FFI)data_state)):num option->num option`),
      mk_icomb(mk_icomb(`data_state_stack_fupd:(stack list->stack list)->(C,FFI)data_state->(C,FFI)data_state`,
                        mk_icomb(`K:stack list->stack list->stack list`,
                                 mk_icomb(`data_state_stack:(C,FFI)data_state->stack list`, DATAPAUX_LIVE_CH_T))),
               DATAPAUX_LIVE_CH_S))))))) THEN
   ANTS_TAC THENL
    [MATCH_MP_TAC DSEMAUX_jump_exc_Exc_top THEN
     ASM_REWRITE_TAC[data_call_env_def; data_push_env_def; data_dec_clock_def; LET_DEF;
                     LET_END_DEF; data_state_INFO.ri_accfupds; K_THM];
     ALL_TAC] THEN
   REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM] THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[pair_CASE; option_CASE] THEN CASE_REWRITE_TAC[]) THEN
     (REMOVE_THEN "ihh" (MP_TAC o SPECL
     [`a'':data_v list`; `ns:num list`; `names:num_set`; `x':data_prog`; `x:data_v list`;
      `y':num option`; `env:data_v spt`; `handle:data_prog`; `var:num`; `v:data_v`;
      `s3:(C,FFI)data_state`]) THEN
   REWRITE_TAC[IS_SOME_DEF] THEN ASM_REWRITE_TAC[] THEN
   DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `l6:num_set` THEN
   ASM_REWRITE_TAC[]) THEN
     (MATCH_MP_TAC(TAUT `!a b. a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
    [MATCH_MP_TAC DATAPAUX_LIVE_rel_set_var THEN
     REWRITE_TAC[data_liveProof_state_rel_def; data_state_INFO.ri_accfupds; K_THM] THEN
     FIRST_X_ASSUM(fun th -> if concl th = `env = data_state_locals (s3:(C,FFI)data_state)`
                             then SUBST_ALL_TAC(SYM th) else failwith "no") THEN
     ASM_REWRITE_TAC[] THEN
     (X_GEN_TAC `z:num` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[domain_delete; IN_DELETE]) THEN
   ASM_REWRITE_TAC[domain_union; IN_UNION; domain_delete; IN_DELETE]);
     (DISCH_TAC THEN MATCH_MP_TAC DATAPAUX_LIVE_jump_exc_frame2 THEN
   MAP_EVERY EXISTS_TAC [`s:(C,FFI)data_state`; `t1:(C,FFI)data_state`; `l6:num_set`] THEN
   ASM_REWRITE_TAC[data_set_var_def; data_state_INFO.ri_accfupds; K_THM])]);
     (REWRITE_TAC[PAIR_EQ] THEN
   DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) THEN
   MP_TAC(ISPECL [`x':data_prog`; DATAPAUX_LIVE_CH_S; `a:abort`; `s3:(C,FFI)data_state`;
                  mk_icomb(`data_state_stack:(C,FFI)data_state->stack list`, DATAPAUX_LIVE_CH_T);
                  mk_icomb(`data_state_stack_max:(C,FFI)data_state->num option`, DATAPAUX_LIVE_CH_T);
                  mk_icomb(`data_state_safe_for_space:(C,FFI)data_state->bool`, DATAPAUX_LIVE_CH_T);
                  `data_state_peak_heap_length (t1:(C,FFI)data_state)`] DATAPAUX_LIVE_swap_abort) THEN
   ANTS_TAC THENL
    [RULE_ASSUM_TAC(REWRITE_RULE[option_INJ; injectivity "result";
                                 injectivity "error_result"]) THEN
     ASM_REWRITE_TAC[data_call_env_def; data_push_env_def; data_dec_clock_def; LET_DEF;
                     LET_END_DEF; data_state_INFO.ri_accfupds; K_THM; LENGTH];
     ALL_TAC] THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[pair_CASE; option_CASE] THEN CASE_REWRITE_TAC[] THEN
   REWRITE_TAC[PAIR_EQ; UNWIND_THM1] THEN
   REWRITE_TAC[data_liveProof_state_rel_def; data_state_INFO.ri_accfupds; K_THM;
               domain_def; NOT_IN_EMPTY])]])];;

(* HOL4: evaluate_compile[Call] (Call_tail, Call_returning_no_handler and  *)
(* Call_returning_with_handler); only the induction hypothesis of the     *)
(* handler is needed (the called code is not compiled by data_live)       *)
let DATAPAUX_LIVE_CALL = prove
 (el 10 DATAPAUX_LIVE_CASES,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "ihh") (K ALL_TAC))) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP DATAPAUX_LIVE_rel_fields) THEN
  CASES_ON `ret:(num list#num_set)option` THENL
   [DATAPAUX_LIVE_CALL_TAIL_TAC; DATAPAUX_LIVE_CALL_RET_TAC]);;

(* HOL4: evaluate_compile [local] (Finalise of the cases above) *)
let data_liveProof_evaluate_compile = prove
 (CASE_TERM
  `!c (s1:(C,FFI)data_state) res s2 l2 t1 l1 d.
     data_evaluate (c,s1) = (res,s2) /\ data_liveProof_state_rel s1 t1 l1 /\
     data_live_compile c l2 = (d,l1) /\ ~(res = SOME (Rerr (Rabort Rtype_error))) /\
     (!s3. data_jump_exc s1 = SOME s3 ==>
           ?t3. data_jump_exc t1 = SOME t3 /\ data_liveProof_state_rel s3 t3 LN /\
                data_state_handler t3 = data_state_handler s3 /\
                LENGTH (data_state_stack t3) = LENGTH (data_state_stack s3)) ==>
     ?t2. data_evaluate (d,t1) = (res,t2) /\
          data_liveProof_state_rel s2 t2 (match res with NONE -> l2 | _ -> LN)`,
  MATCH_ACCEPT_TAC
    (REWRITE_RULE[FORALL_PAIR_THM; FST; SND]
       (MP DATAPAUX_LIVE_IND
          (end_itlist CONJ
             [DATAPAUX_LIVE_SKIP; DATAPAUX_LIVE_MOVE; DATAPAUX_LIVE_ASSIGN;
              DATAPAUX_LIVE_TICK; DATAPAUX_LIVE_MAKESPACE; DATAPAUX_LIVE_RAISE;
              DATAPAUX_LIVE_RETURN; DATAPAUX_LIVE_SEQ; DATAPAUX_LIVE_IF;
              DATAPAUX_LIVE_FORCE; DATAPAUX_LIVE_CALL]))));;

let data_liveProof_compile_correct = prove
 (`!c (s:(C,FFI)data_state).
     ~(FST (data_evaluate (c,s)) = SOME (Rerr (Rabort Rtype_error))) /\
     ~(FST (data_evaluate (c,s)) = NONE) ==>
     ?ls sm safe peak.
       data_evaluate (FST (data_live_compile c LN),s) =
       (I ## (\s. data_state_locals_size_fupd (K ls)
                    (data_state_stack_max_fupd (K sm)
                       (data_state_safe_for_space_fupd (K safe)
                          (data_state_peak_heap_length_fupd (K peak) s)))))
       (data_evaluate (c,s))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `data_evaluate (c,s:(C,FFI)data_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `res:((data_v list,data_v)result)option`
    (X_CHOOSE_THEN `s2:(C,FFI)data_state` ASSUME_TAC)) THEN
  MP_TAC(ISPEC `data_live_compile c LN` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:data_prog` (X_CHOOSE_THEN `l1:num_set` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[FST] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:data_prog`; `s:(C,FFI)data_state`;
                 `res:((data_v list,data_v)result)option`; `s2:(C,FFI)data_state`;
                 `LN:num_set`; `s:(C,FFI)data_state`; `l1:num_set`; `d:data_prog`]
                data_liveProof_evaluate_compile) THEN
  ASM_REWRITE_TAC[state_rel_ID] THEN
  ANTS_TAC THENL
   [X_GEN_TAC `s3:(C,FFI)data_state` THEN DISCH_TAC THEN
    EXISTS_TAC `s3:(C,FFI)data_state` THEN ASM_REWRITE_TAC[state_rel_ID];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:(C,FFI)data_state` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[PAIR_MAP_THM; I_THM; PAIR_EQ] THEN
  MAP_EVERY EXISTS_TAC [`data_state_locals_size (t2:(C,FFI)data_state)`;
                        `data_state_stack_max (t2:(C,FFI)data_state)`;
                        `data_state_safe_for_space (t2:(C,FFI)data_state)`;
                        `data_state_peak_heap_length (t2:(C,FFI)data_state)`] THEN
  SUBGOAL_THEN `data_state_locals (t2:(C,FFI)data_state) = data_state_locals (s2:(C,FFI)data_state) /\
                data_state_stack t2 = data_state_stack s2`
    STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:data_prog`; `s:(C,FFI)data_state`] evaluate_stack) THEN
    MP_TAC(ISPECL [`d:data_prog`; `s:(C,FFI)data_state`] evaluate_stack) THEN
    MP_TAC(ISPECL [`c:data_prog`; `s:(C,FFI)data_state`;
                   `res:((data_v list,data_v)result)option`; `s2:(C,FFI)data_state`]
                  evaluate_locals_LN) THEN
    MP_TAC(ISPECL [`d:data_prog`; `s:(C,FFI)data_state`;
                   `res:((data_v list,data_v)result)option`; `t2:(C,FFI)data_state`]
                  evaluate_locals_LN) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~(res:((data_v list,data_v)result)option = NONE)` THEN
    UNDISCH_TAC `~(res:((data_v list,data_v)result)option = SOME (Rerr (Rabort Rtype_error)))` THEN
    SPEC_TAC(`res:((data_v list,data_v)result)option`,
             `res:((data_v list,data_v)result)option`) THEN
    MATCH_MP_TAC DSEMAUX_res_CASES THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
    CASE_REWRITE_TAC[injectivity "result"; distinctness "result";
                     injectivity "error_result"; distinctness "error_result";
                     distinctness "abort"] THEN
    REPEAT STRIP_TAC THEN ASM_MESON_TAC[option_INJ];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [data_liveProof_state_rel_def]) THEN
  REWRITE_TAC[data_state_component_equality; data_state_INFO.ri_accfupds; K_THM] THEN
  ASM_SIMP_TAC[]);;

let data_liveProof_get_code_labels_compile = prove
 (`!x y. data_get_code_labels (FST (data_live_compile x y)) SUBSET data_get_code_labels x`,
  MATCH_MP_TAC data_live_compile_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[data_live_compile_def; LET_DEF; LET_END_DEF] THEN
  REPEAT (COND_CASES_TAC ORELSE PAIRARG_TAC) THEN
  REWRITE_TAC[FST; data_get_code_labels_def; option_CASE; pair_CASE] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_UNWIND_THM1] THEN
  REWRITE_TAC[SUBSET_REFL] THEN
  REPEAT STRIP_TAC THEN FS[] THEN ASM SET_TAC[]);;
