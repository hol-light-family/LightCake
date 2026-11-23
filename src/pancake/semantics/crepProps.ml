(* ========================================================================= *)
(* crepProps: port of HOL4 pancake/semantics/crepPropsScript.sml (CakeML    *)
(* v3479).  crepLang Properties.                                             *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - Names as doc/names.tsv says (crep_update_locals_not_vars_              *)
(*   eval_eq, crep_eval_upd_clock_eq, crep_evaluate_add_clock_eq, ...,       *)
(*   crep_exps_of, crep_every_exp); the other theorems keep their HOL4      *)
(*   names.                                                                  *)
(* - HOL4 binds update_locals_not_vars_eval_eq' twice: first a [local]       *)
(*   lemma (here PCREPAUX_update_locals_not_vars_eval_eq'), then the         *)
(*   theorem proved from it.                                                 *)
(* - HOL4 s.f is crep_state_f s, s with f := v is crep_state_f_fupd (K v) s; *)
(*   n2w is word, w2n is val, + on words is word_add, * is word_mul; ZIP     *)
(*   (xs,ys) is ZIP xs ys (with the equal lengths every statement assumes); *)
(*   GENLIST f n is list_of_seq f n; FOLDL is ITLIST's left fold FOLDL;      *)
(*   x <<= y is HOL4's x IS_PREFIX ... (isPREFIX); EVERY is ALL.             *)
(* - Local helpers that are not HOL4 theorems are PCREPAUX_.                 *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "pancake/semantics/panSem.ml";;
needs "pancake/panLang.ml";;
needs "pancake/pan_common.ml";;
needs "pancake/semantics/panProps.ml";;
needs "pancake/crepLang.ml";;
needs "pancake/semantics/crepSem.ml";;
needs "pancake/semantics/pan_commonProps.ml";;

prioritize_num();;
type_invention_error := true;;

let cexp_heads_simp_def = cake_def
  `cexp_heads_simp (es:(A list)list) =
     if MEM [] es then NONE else SOME (MAP HD es)`;;

let lookup_locals_eq_map_vars = prove
 (`!ns (t:(A,FFI)crep_state).
     OPT_MMAP (FLOOKUP (crep_state_locals t)) ns =
     OPT_MMAP (crep_eval t) (MAP crep_Var ns)`,
  RW[] THEN MATCH_MP_TAC IMP_OPT_MMAP_EQ THEN
  FS[MAP_MAP_o] THEN FS[MAP_EQ_f] THEN RW[] THEN FS[crep_eval_def; o_THM]);;

let length_load_shape_eq_shape = prove
 (`!n (a:A word) e. LENGTH (load_shape a n e) = n`,
  INDUCT_TAC THEN RW[] THEN ONCE_REWRITE_TAC[load_shape_def] THEN
  FS[] THEN EVERY_CASE_TAC THEN FS[]);;
let eval_load_shape_el_rel = prove
 (`!m n (a:A word) (t:(A,FFI)crep_state) e.
     n < m ==>
     crep_eval t (EL n (load_shape a m e)) =
     crep_eval t (crep_Load (crep_Op asm_Add
       [e; crep_Const (word_add a (word_mul bytes_in_word (word n)))]))`,
  INDUCT_TAC THENL [REWRITE_TAC[LT]; ALL_TAC] THEN
  RW[] THEN ONCE_REWRITE_TAC[load_shape_def] THEN
  NAMED_CASES_ON "n" ["";"n"] THEN FS[] THEN COND_CASES_TAC THEN
  FS[EL; HD; TL; WORD_MUL_0; WORD_ADD_0] THENL
   [REWRITE_TAC[crep_eval_def; OPT_MMAP_DEF] THEN TOP_CASE_TAC THEN FS[] THEN
    TOP_CASE_TAC THEN FS[OPTION_BIND_DEF; OPTION_MAP_DEF; word_op_def; ITLIST; WORD_ADD_0];
    ALL_TAC; ALL_TAC] THEN
  REWRITE_TAC[WORD_RULE `!b:A word. !n. word_mul b (word (SUC n)) =
                                        word_add b (word_mul b (word n))`;
              WORD_ADD_ASSOC]);;

(* mem_loads_flat_rel: the cases of pan_mem_load_ind in order: pan_mem_load *)
(* (One, Comb, Named), mem_loads [] and CONS, mem_load_flds (trivial)        *)

let PCREPAUX_word_offset_add = prove
 (`!(a:A word) b x y.
     word_add a (word_mul b (word (x + y))) =
     word_add (word_add a (word_mul b (word x))) (word_mul b (word y))`,
  REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE);;

let mem_loads_flat_rel = prove
 (`(!sh (adr:A word) dm (m:A word->(A)word_lab) stcs v.
      pan_mem_load sh adr dm m stcs = SOME v /\
      is_wf_shape ([]:(mlstring#struct_info)list) sh ==>
      !(s:(A,FFI)crep_state) n.
        n < LENGTH (flatten v) ==>
        dm = crep_state_memaddrs s ==>
        m = crep_state_memory s ==>
        crep_mem_load (word_add adr (word_mul bytes_in_word (word n))) s =
        SOME (EL n (flatten v))) /\
   (!shs (adr:A word) dm (m:A word->(A)word_lab) stcs v.
      mem_loads shs adr dm m stcs = SOME v /\
      ALL (is_wf_shape ([]:(mlstring#struct_info)list)) shs ==>
      !(s:(A,FFI)crep_state) n.
        n < LENGTH (FLAT (MAP flatten v)) ==>
        dm = crep_state_memaddrs s ==>
        m = crep_state_memory s ==>
        crep_mem_load (word_add adr (word_mul bytes_in_word (word n))) s =
        SOME (EL n (FLAT (MAP flatten v)))) /\
   (!flds (adr:A word) dm (m:A word->(A)word_lab) stcs vs.
      mem_load_flds flds adr dm m stcs = SOME vs ==> T)`,
  MATCH_MP_TAC pan_mem_load_ind THEN REPEAT CONJ_TAC THEN REWRITE_TAC[] THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
    REPEAT DISCH_TAC THEN RVEQ_TAC THEN
    QPAT_X_ASSUM "pan_mem_load _ _ _ _ _ = SOME _" (MP_TAC o ONCE_REWRITE_RULE[pan_mem_load_def]) THEN
    QCASES_ON "sh" THEN FS[is_wf_shape_def; ALOOKUP_DEF] THEN RW[] THEN
    FS[flatten_def; LENGTH; LT_SUC; LT; EL; HD; WORD_MUL_0; WORD_ADD_0; crep_mem_load_def] THEN
    GVS(all_case_eqs()) THEN FS[flatten_def] THEN ASM_MESON_TAC[];
    REPEAT GEN_TAC THEN STRIP_TAC THEN FS[pan_mem_load_def; MAP; FLAT; LENGTH; LT] THEN
    RVEQ_TAC THEN FS[MAP; FLAT; LENGTH; LT];
    REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
    REPEAT DISCH_TAC THEN RVEQ_TAC THEN
    QPAT_X_ASSUM "mem_loads _ _ _ _ _ = SOME _" (MP_TAC o ONCE_REWRITE_RULE[pan_mem_load_def]) THEN
    DISCH_TAC THEN GVS(all_case_eqs()) THEN FS[MAP; FLAT; ALL] THEN REWRITE_TAC[EL_APPEND] THEN
    RENAME1 "pan_mem_load shape _ _ _ _ = SOME v1" THEN
    RENAME1 "mem_loads shapes _ _ _ _ = SOME vs" THEN
    QBY "LENGTH (flatten v1) = size_of_sh_with_ctxt stcs shape"
      (IMP_RES_TAC mem_load_some_shape_eq THEN
       MP_TAC(ISPEC `v1:(A)pan_v` length_flatten_eq_size_of_shape) THEN
       ASM_SIMP_TAC[size_of_sh_with_ctxt_eq]) THEN
    COND_CASES_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`addr:A word`; `bytes_in_word:A word`; `LENGTH (flatten (v1:(A)pan_v))`;
                   `n - LENGTH (flatten (v1:(A)pan_v))`] PCREPAUX_word_offset_add) THEN
    ASM_SIMP_TAC[ARITH_RULE `~(n < l) ==> l + (n - l) = n`] THEN DISCH_THEN SUBST1_TAC THEN
    QPAT_X_ASSUM "LENGTH (flatten v1) = _" SUBST_ALL_TAC THEN
    FIRST_X_ASSUM IRULE THEN REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

let mem_load_flat_rel = prove
 (`!sh (adr:A word) (s:(A,FFI)crep_state) v n.
     pan_mem_load sh adr (crep_state_memaddrs s) (crep_state_memory s) stcs = SOME v /\
     n < LENGTH (flatten v) /\
     is_wf_shape ([]:(mlstring#struct_info)list) sh ==>
     crep_mem_load
       (word_add adr (word_mul bytes_in_word (word (LENGTH (TAKE n (flatten v)))))) s =
     SOME (EL n (flatten v))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `LENGTH (TAKE n (flatten (v:(A)pan_v))) = n` SUBST1_TAC THENL
   [ASM_SIMP_TAC[LENGTH_TAKE; LT_IMP_LE]; ALL_TAC] THEN
  MP_TAC(CONJUNCT1 mem_loads_flat_rel) THEN
  DISCH_THEN(MP_TAC o SPECL [`sh:shape`; `adr:A word`; `crep_state_memaddrs (s:(A,FFI)crep_state)`;
                             `crep_state_memory (s:(A,FFI)crep_state)`; `stcs:(mlstring#struct_info)list`;
                             `v:(A)pan_v`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`s:(A,FFI)crep_state`; `n:num`]) THEN
  ASM_REWRITE_TAC[]);;

(* HOL4: the first, [local], update_locals_not_vars_eval_eq'; proved here   *)
(* before crep_update_locals_not_vars_eval_eq, which follows from it        *)

let PCREPAUX_update_locals_not_vars_eval_eq' = prove
 (`!(s:(A,FFI)crep_state) e (v:B) n w res.
     ~MEM n (var_cexp e) /\ crep_eval s e = res ==>
     crep_eval (crep_state_locals_fupd (K (crep_state_locals s |+ (n,w))) s) e = res`,
  SUBGOAL_THEN
   `!(s:(A,FFI)crep_state) e n w. ~MEM n (var_cexp e) ==>
      crep_eval (crep_state_locals_fupd (K (crep_state_locals s |+ (n,w))) s) e =
      crep_eval s e`
   (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC crep_eval_ind THEN
  REWRITE_TAC[var_cexp_def; MEM_APPEND; DE_MORGAN_THM; MEM_FLAT; MEM_MAP; MEM] THEN
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[crep_eval_def] THEN
  SIMP[crep_mem_load_def; FLOOKUP_UPDATE] THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC OPT_MMAP_CONG THEN
  REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let crep_update_locals_not_vars_eval_eq = prove
 (`!(s:(A,FFI)crep_state) e v n w.
     ~MEM n (var_cexp e) /\ crep_eval s e = SOME v ==>
     crep_eval (crep_state_locals_fupd (K (crep_state_locals s |+ (n,w))) s) e =
     SOME v`,
  MESON_TAC[PCREPAUX_update_locals_not_vars_eval_eq']);;

let update_locals_not_vars_eval_eq' = prove
 (`!(s:(A,FFI)crep_state) e (v:B) n w.
     ~MEM n (var_cexp e) ==>
     crep_eval (crep_state_locals_fupd (K (crep_state_locals s |+ (n,w))) s) e =
     crep_eval s e`,
  MESON_TAC[PCREPAUX_update_locals_not_vars_eval_eq']);;

let update_locals_not_vars_eval_eq'' = prove
 (`!(s:(A,FFI)crep_state) e (v:B) n w locals.
     ~MEM n (var_cexp e) ==>
     crep_eval (crep_state_locals_fupd (K (locals |+ (n,w))) s) e =
     crep_eval (crep_state_locals_fupd (K locals) s) e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`crep_state_locals_fupd (K locals) (s:(A,FFI)crep_state)`;
                 `e:(A)crep_exp`; `v:B`; `n:num`; `w:(A)word_lab`]
                update_locals_not_vars_eval_eq') THEN
  ASM_REWRITE_TAC[] THEN SIMP[]);;

let var_exp_load_shape = prove
 (`!i (a:A word) e n. MEM n (load_shape a i e) ==> var_cexp n = var_cexp e`,
  INDUCT_TAC THEN RW[load_shape_def] THEN FS[var_cexp_def; FLAT; APPEND_NIL] THEN
  ASM_MESON_TAC[]);;

let map_var_cexp_eq_var = prove
 (`!vs. FLAT (MAP var_cexp (MAP (crep_Var:num->(A)crep_exp) vs)) = vs`,
  LIST_INDUCT_TAC THEN RW[var_cexp_def; MAP; FLAT] THEN FS[var_cexp_def]);;

let res_var_commutes = prove
 (`~(n = h) ==>
   crep_res_var (crep_res_var (lc:(K,V)fmap) (h,FLOOKUP lc' h)) (n,FLOOKUP lc' n) =
   crep_res_var (crep_res_var lc (n,FLOOKUP lc' n)) (h,FLOOKUP lc' h)`,
  RW[] THEN QCASES_ON "FLOOKUP (lc':(K,V)fmap) h" THEN
  QCASES_ON "FLOOKUP (lc':(K,V)fmap) n" THEN FS[crep_res_var_def] THEN
  FS[DOMSUB_COMMUTES; DOMSUB_FUPDATE_NEQ] THEN ASM_MESON_TAC[FUPDATE_COMMUTES]);;

let flookup_res_var_diff_eq = prove
 (`~(n = m) ==> FLOOKUP (crep_res_var (l:(K,V)fmap) (m,v)) n = FLOOKUP l n`,
  RW[] THEN QCASES_ON "v:V option" THEN
  FS[crep_res_var_def; FLOOKUP_UPDATE; DOMSUB_FLOOKUP_NEQ]);;

let flookup_res_var_thm = prove
 (`FLOOKUP (crep_res_var (l:(K,V)fmap) (m,v)) n =
   if n = m then v else FLOOKUP l n`,
  QCASES_ON "v:V option" THEN RW[crep_res_var_def; DOMSUB_FLOOKUP_THM; FLOOKUP_UPDATE] THEN
  FS[]);;

let dec_clock_simp = prove
 (`crep_state_locals (crep_dec_clock (s:(A,FFI)crep_state)) = crep_state_locals s /\
   crep_state_globals (crep_dec_clock s) = crep_state_globals s /\
   crep_state_code (crep_dec_clock s) = crep_state_code s /\
   crep_state_memory (crep_dec_clock s) = crep_state_memory s /\
   crep_state_memaddrs (crep_dec_clock s) = crep_state_memaddrs s /\
   crep_state_sh_memaddrs (crep_dec_clock s) = crep_state_sh_memaddrs s /\
   (crep_state_be (crep_dec_clock s) <=> crep_state_be s) /\
   crep_state_ffi (crep_dec_clock s) = crep_state_ffi s /\
   crep_state_base_addr (crep_dec_clock s) = crep_state_base_addr s /\
   crep_state_top_addr (crep_dec_clock s) = crep_state_top_addr s`,
  SIMP[crep_dec_clock_def]);;

let empty_locals_simp = prove
 (`crep_state_globals (crep_empty_locals (s:(A,FFI)crep_state)) = crep_state_globals s /\
   crep_state_code (crep_empty_locals s) = crep_state_code s /\
   crep_state_memory (crep_empty_locals s) = crep_state_memory s /\
   crep_state_memaddrs (crep_empty_locals s) = crep_state_memaddrs s /\
   crep_state_sh_memaddrs (crep_empty_locals s) = crep_state_sh_memaddrs s /\
   crep_state_clock (crep_empty_locals s) = crep_state_clock s /\
   (crep_state_be (crep_empty_locals s) <=> crep_state_be s) /\
   crep_state_ffi (crep_empty_locals s) = crep_state_ffi s /\
   crep_state_base_addr (crep_empty_locals s) = crep_state_base_addr s /\
   crep_state_top_addr (crep_empty_locals s) = crep_state_top_addr s`,
  SIMP[crep_empty_locals_def]);;

let FLOOKUP_set_globals = prove
 (`FLOOKUP (crep_state_locals (crep_set_globals gv w (s:(A,FFI)crep_state))) n =
   FLOOKUP (crep_state_locals s) n`,
  SIMP[crep_set_globals_def]);;

let _ = cake_add_simps [FLOOKUP_set_globals];;

let sh_mem_load_FLOOKUP_locals = prove
 (`crep_sh_mem_load v addr nb (s:(A,FFI)crep_state) = (res:((B)crep_result)option,t) /\
   ~(n = v) /\
   (res = NONE \/ res = SOME (crepSem_Continue k) \/ res = SOME (crepSem_Break k))
   ==> FLOOKUP (crep_state_locals t) n = FLOOKUP (crep_state_locals s) n`,
  RW(ONELINE crep_sh_mem_load_def :: all_case_eqs()) THEN
  SIMP[crep_set_var_def; crep_empty_locals_def; FLOOKUP_SIMP]);;

let sh_mem_store_FLOOKUP_locals = prove
 (`crep_sh_mem_store v addr nb (s:(A,FFI)crep_state) = (res:((B)crep_result)option,t)
   ==> FLOOKUP (crep_state_locals t) n = FLOOKUP (crep_state_locals s) n`,
  RW(ONELINE crep_sh_mem_store_def :: all_case_eqs()) THEN SIMP[]);;

let set_mem_op_FLOOKUP_locals = prove
 (`crep_sh_mem_op op r ad (s:(A,FFI)crep_state) = (res:((B)crep_result)option,t) /\
   ~(r = n) /\
   (res = NONE \/ res = SOME (crepSem_Continue k) \/ res = SOME (crepSem_Break k))
   ==> FLOOKUP (crep_state_locals t) n = FLOOKUP (crep_state_locals s) n`,
  RW(ONELINE crep_sh_mem_op_def :: all_case_eqs()) THEN
  IMP_RES_TAC sh_mem_load_FLOOKUP_locals THEN
  IMP_RES_TAC sh_mem_store_FLOOKUP_locals THEN SIMP[]);;

(* HOL4's >~ [pat] >- tac on the goals of an induction: tac (which must     *)
(* solve the goal) on the goals whose conclusion mentions the constant c   *)

let PCREPAUX_CASE_TAC (c:string) (tac:tactic) : tactic =
  fun (asl,w as g) ->
    if can (find_term (fun t -> is_const t && fst(dest_const t) = c)) w
    then (tac THEN NO_TAC) g else ALL_TAC g;;

let unassigned_free_vars_evaluate_same = prove
 (`!p (s:(A,FFI)crep_state) res t n k.
     crep_evaluate (p,s) = (res,t) /\
     (res = NONE \/ res = SOME (crepSem_Continue k) \/ res = SOME (crepSem_Break k)) /\
     ~MEM n (assigned_free_vars p) ==>
     FLOOKUP (crep_state_locals t) n = FLOOKUP (crep_state_locals s) n`,
  REC_IND_TAC crep_evaluate_ind THEN REPEAT CONJ_TAC THEN
  SIMP[assigned_free_vars_def; MEM_APPEND; NOT_ss] THEN
  PCREPAUX_CASE_TAC "crep_Dec"
   (RW(crep_evaluate_def :: all_case_eqs()) THEN
    REPEAT(PAIRARG_TAC THEN GVS[]) THEN
    SIMP[flookup_res_var_thm] THEN COND_CASES_TAC THEN
    GVS[MEM_FILTER; FLOOKUP_SIMP]) THEN
  PCREPAUX_CASE_TAC "crep_ShMem"
   (RW(crep_evaluate_def :: all_case_eqs()) THEN
    IMP_RES_TAC set_mem_op_FLOOKUP_locals THEN GVS[]) THEN
  PCREPAUX_CASE_TAC "crep_Seq"
   (RW(crep_evaluate_def :: all_case_eqs()) THEN
    REPEAT(PAIRARG_TAC THEN GVS[]) THEN GVS(all_case_eqs())) THEN
  PCREPAUX_CASE_TAC "crep_While"
   (RW[] THEN QPAT_X_ASSUM "crep_evaluate (crep_While _ _,_) = _" MP_TAC THEN
    ONCE_REWRITE_TAC[crep_evaluate_def] THEN RW(all_case_eqs()) THEN
    REPEAT(PAIRARG_TAC THEN GVS[]) THEN GVS(crep_dec_clock_def :: all_case_eqs())) THEN
  PCREPAUX_CASE_TAC "crep_Call"
   (RW[crep_evaluate_def] THEN EVERY_CASE_TAC THEN
    GVS[assigned_free_vars_def; FLOOKUP_SIMP; MEM_APPEND; NOT_ss] THEN
    ASM_MESON_TAC[flookup_fupdate_zip_not_mem; MEM; LENGTH]) THEN
  PCREPAUX_CASE_TAC "crep_If"
   (RW(crep_evaluate_def :: all_case_eqs()) THEN
    RENAME1 "if ~(w = word 0) then _ else _" THEN
    QCASES_ON "~(w = word 0)" THEN GVS[]) THEN
  RW(crep_evaluate_def :: all_case_eqs()) THEN
  SIMP[FLOOKUP_SIMP; NOT_MEM_FLOOKUP_ZIP; crep_dec_clock_def]);;

let assigned_free_vars_IMP_assigned_vars = prove
 (`!(prog:(A)crep_prog) x.
     MEM x (assigned_free_vars prog) ==> MEM x (crep_assigned_vars prog)`,
  REC_IND_TAC crep_assigned_vars_ind THEN
  RW[assigned_free_vars_def; crep_assigned_vars_def; MEM_FILTER; MEM_APPEND; MEM] THEN
  GVS[]);;

let crep_unassigned_vars_evaluate_same = prove
 (`!p (s:(A,FFI)crep_state) res t n k.
     crep_evaluate (p,s) = (res,t) /\
     (res = NONE \/ res = SOME (crepSem_Continue k) \/ res = SOME (crepSem_Break k)) /\
     ~MEM n (assigned_free_vars p) ==>
     FLOOKUP (crep_state_locals t) n = FLOOKUP (crep_state_locals s) n`,
  MESON_TAC[assigned_free_vars_IMP_assigned_vars; unassigned_free_vars_evaluate_same]);;

let assigned_vars_nested_decs_append = prove
 (`!ns es (p:(A)crep_prog).
     LENGTH ns = LENGTH es ==>
     crep_assigned_vars (nested_decs ns es p) = APPEND ns (crep_assigned_vars p)`,
  LIST_INDUCT_TAC THEN RW[] THEN FS[nested_decs_def] THEN QCASES_ON "es" THEN
  FS[nested_decs_def; crep_assigned_vars_def; LENGTH; SUC_INJ; APPEND] THEN
  FS[LENGTH; NOT_SUC]);;

let assigned_free_vars_nested_decs_append = prove
 (`!ns es (p:(A)crep_prog).
     LENGTH ns = LENGTH es ==>
     assigned_free_vars (nested_decs ns es p) =
     FILTER (\x. ~MEM x ns) (assigned_free_vars p)`,
  LIST_INDUCT_TAC THEN RW[] THEN FS[nested_decs_def; MEM; FILTER_T] THEN
  QCASES_ON "es" THEN
  FS[nested_decs_def; assigned_free_vars_def; FILTER_FILTER; LENGTH; NOT_SUC] THEN
  REPEAT(AP_TERM_TAC ORELSE AP_THM_TAC) THEN REWRITE_TAC[FUN_EQ_THM; MEM] THEN
  MESON_TAC[]);;

let nested_seq_assigned_vars_eq = prove
 (`!ns vs. LENGTH ns = LENGTH vs ==>
     crep_assigned_vars (crep_nested_seq (MAP2 crep_Assign ns vs:((A)crep_prog)list)) = ns`,
  LIST_INDUCT_TAC THEN RW[] THENL
   [FS[MAP2; crep_nested_seq_def; crep_assigned_vars_def]; ALL_TAC] THEN
  QCASES_ON "vs" THEN FS[MAP2; crep_nested_seq_def; crep_assigned_vars_def; LENGTH; NOT_SUC] THEN
  FS[APPEND]);;

let nested_seq_assigned_free_vars_eq = prove
 (`!ns vs. LENGTH ns = LENGTH vs ==>
     assigned_free_vars (crep_nested_seq (MAP2 crep_Assign ns vs:((A)crep_prog)list)) = ns`,
  LIST_INDUCT_TAC THEN RW[] THENL
   [FS[MAP2; crep_nested_seq_def; assigned_free_vars_def]; ALL_TAC] THEN
  QCASES_ON "vs" THEN FS[MAP2; crep_nested_seq_def; assigned_free_vars_def; LENGTH; NOT_SUC] THEN
  FS[APPEND]);;

let assigned_vars_seq_store_empty = prove
 (`!es (ad:(A)crep_exp) a.
     crep_assigned_vars (crep_nested_seq (stores ad es a)) = []`,
  LIST_INDUCT_TAC THEN RW[] THEN
  FS[stores_def; crep_assigned_vars_def; crep_nested_seq_def] THEN
  COND_CASES_TAC THEN FS[stores_def; crep_assigned_vars_def; crep_nested_seq_def; APPEND]);;

let assigned_free_vars_seq_store_empty = prove
 (`!es (ad:(A)crep_exp) a.
     assigned_free_vars (crep_nested_seq (stores ad es a)) = []`,
  LIST_INDUCT_TAC THEN RW[] THEN
  FS[stores_def; assigned_free_vars_def; crep_nested_seq_def] THEN
  COND_CASES_TAC THEN FS[stores_def; assigned_free_vars_def; crep_nested_seq_def; APPEND]);;

let assigned_vars_store_globals_empty = prove
 (`!es ad. crep_assigned_vars (crep_nested_seq (store_globals ad es:((A)crep_prog)list)) = []`,
  LIST_INDUCT_TAC THEN RW[] THEN
  FS[store_globals_def; crep_assigned_vars_def; crep_nested_seq_def] THEN
  FS[store_globals_def; crep_assigned_vars_def; crep_nested_seq_def; APPEND]);;

let assigned_free_vars_store_globals_empty = prove
 (`!es ad. assigned_free_vars (crep_nested_seq (store_globals ad es:((A)crep_prog)list)) = []`,
  LIST_INDUCT_TAC THEN RW[] THEN
  FS[store_globals_def; assigned_free_vars_def; crep_nested_seq_def] THEN
  FS[store_globals_def; assigned_free_vars_def; crep_nested_seq_def; APPEND]);;

let length_load_globals_eq_read_size = prove
 (`!ads a. LENGTH (load_globals a ads:((A)crep_exp)list) = ads`,
  INDUCT_TAC THEN RW[] THEN FS[load_globals_def; LENGTH]);;

let el_load_globals_elem = prove
 (`!ads a n. n < ads ==>
     EL n (load_globals a ads:((A)crep_exp)list) = LoadGlob (word_add a (word n))`,
  INDUCT_TAC THEN RW[] THEN FS[load_globals_def; LT] THEN
  NAMED_CASES_ON "n" ["";"n"] THEN FS[EL; HD; TL; WORD_ADD_0] THEN
  FS[n2w_SUC; LT_SUC; WORD_ADD_ASSOC] THEN CONV_TAC WORD_RULE);;

let evaluate_seq_stroes_locals_eq = prove
 (`!es (ad:(A)crep_exp) a (s:(A,FFI)crep_state) res t.
     crep_evaluate (crep_nested_seq (stores ad es a),s) = (res,t) ==>
     crep_state_locals t = crep_state_locals s`,
  LIST_INDUCT_TAC THEN RW[] THENL
   [FS[stores_def; crep_nested_seq_def; crep_evaluate_def]; ALL_TAC] THEN
  FS[stores_def] THEN QCASES_ON "a = word 0" THEN FS[] THEN
  FS[crep_nested_seq_def; crep_evaluate_def] THEN
  PAIRARG_TAC THEN FS[] THEN RVEQ_TAC THEN
  EVERY_CASE_TAC THEN FS[] THEN RVEQ_TAC THEN
  LAST_X_ASSUM DRULE THEN FS[pan_mem_store_def; crep_state_component_equality]);;

let evaluate_seq_stores_mem_state_rel = prove
 (`!es vs ad (a:A word) (s:(A,FFI)crep_state) res t addr m.
     LENGTH es = LENGTH vs /\ ~MEM ad es /\ ALL_DISTINCT es /\
     mem_stores (word_add addr a) vs (crep_state_memaddrs s) (crep_state_memory s) =
       SOME m /\
     crep_evaluate
       (crep_nested_seq (stores (crep_Var ad) (MAP crep_Var es) a),
        crep_state_locals_fupd
          (K (crep_state_locals s |++ CONS (ad,Word addr) (ZIP es vs))) s) = (res,t)
     ==> res = NONE /\ crep_state_memory t = m /\
         crep_state_memaddrs t = crep_state_memaddrs s /\
         crep_state_sh_memaddrs t = crep_state_sh_memaddrs s /\
         (crep_state_be t <=> crep_state_be s) /\
         crep_state_ffi t = crep_state_ffi s /\ crep_state_code t = crep_state_code s /\
         crep_state_clock t = crep_state_clock s /\
         crep_state_base_addr t = crep_state_base_addr s /\
         crep_state_top_addr t = crep_state_top_addr s`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN RFS[] THEN RVEQ_TAC THENL
   [FS[stores_def; crep_nested_seq_def; crep_evaluate_def; mem_stores_def;
       crep_state_component_equality] THEN RVEQ_TAC THEN SIMP[];
    ALL_TAC] THEN
  NAMED_CASES_ON "vs" ["";"v vs"] THEN FS[LENGTH; NOT_SUC; SUC_INJ] THEN
  FS(mem_stores_def :: all_case_eqs()) THEN
  RENAME1 "pan_mem_store _ _ _ _ = SOME m'" THEN
  FS[NOT_ss] THEN QBY "~(h = ad)" (ASM_MESON_TAC[]) THEN
  QBY "FLOOKUP (crep_state_locals s |++ CONS (ad,Word addr) (CONS (h,v) (ZIP t vs'))) h =
       SOME v"
    (REWRITE_TAC[FUPDATE_LIST_THM] THEN ASM_SIMP_TAC[NOT_MEM_FLOOKUP_ZIP; FLOOKUP_UPDATE]) THEN
  QBY "FLOOKUP (crep_state_locals s |++ CONS (ad,Word addr) (CONS (h,v) (ZIP t vs'))) ad =
       SOME (Word addr)"
    (REWRITE_TAC[FUPDATE_LIST_THM] THEN ASM_SIMP_TAC[NOT_MEM_FLOOKUP_ZIP; FLOOKUP_UPDATE]) THEN
  QBY "crep_state_locals s |++ CONS (ad,Word addr) (CONS (h,v) (ZIP t vs')) |++
         CONS (ad,Word addr) (ZIP t vs') =
       crep_state_locals s |++ CONS (ad,Word addr) (CONS (h,v) (ZIP t vs'))"
    (MATCH_MP_TAC fm_multi_update THEN ASM_REWRITE_TAC[]) THEN
  FS[stores_def] THEN QCASES_ON "a = word 0" THEN FS[] THEN
  FS[crep_nested_seq_def; crep_evaluate_def] THEN PAIRARG_TAC THEN FS[] THEN
  FS[crep_eval_def; OPT_MMAP_DEF; OPTION_BIND_DEF; OPTION_MAP_DEF; word_op_def;
     ITLIST; WORD_ADD_0] THEN
  GVS[] THENL
   [LAST_X_ASSUM(MP_TAC o SPECL
     [`vs':((A)word_lab)list`; `ad:num`; `bytes_in_word:A word`;
      `crep_state_locals_fupd
         (K (crep_state_locals s |++ CONS (ad,Word addr) (CONS (h,v) (ZIP t vs'))))
         (crep_state_memory_fupd (K m') s):(A,FFI)crep_state`;
      `res:((A)crep_result)option`; `t':(A,FFI)crep_state`; `addr:A word`;
      `m:A word->(A)word_lab`]);
    LAST_X_ASSUM(MP_TAC o SPECL
     [`vs':((A)word_lab)list`; `ad:num`; `word_add a bytes_in_word:A word`;
      `crep_state_locals_fupd
         (K (crep_state_locals s |++ CONS (ad,Word addr) (CONS (h,v) (ZIP t vs'))))
         (crep_state_memory_fupd (K m') s):(A,FFI)crep_state`;
      `res:((A)crep_result)option`; `t':(A,FFI)crep_state`; `addr:A word`;
      `m:A word->(A)word_lab`])] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_ADD_ASSOC]) THEN SIMP[GSYM WORD_ADD_ASSOC]);;

let evaluate_seq_store_globals_res = prove
 (`!vars vs (t:(A,FFI)crep_state) a.
     ALL_DISTINCT vars /\ LENGTH vars = LENGTH vs /\ val a + LENGTH vs <= 32 ==>
     crep_evaluate (crep_nested_seq (store_globals a (MAP crep_Var vars)),
                    crep_state_locals_fupd (K (crep_state_locals t |++ ZIP vars vs)) t) =
     (NONE,
      crep_state_globals_fupd
        (K (crep_state_globals t |++
            ZIP (list_of_seq (\x. word_add a (word x)) (LENGTH vs)) vs))
        (crep_state_locals_fupd (K (crep_state_locals t |++ ZIP vars vs)) t))`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THENL
   [FS[LENGTH; LENGTH_EQ_NIL] THEN RVEQ_TAC THEN
    FS[store_globals_def; MAP; crep_nested_seq_def; crep_evaluate_def; ZIP;
       FUPDATE_LIST_THM; GENLIST_CONS; LIST_OF_SEQ; crep_state_component_equality];
    ALL_TAC] THEN
  NAMED_CASES_ON "vs" ["";"v vs"] THEN FS[LENGTH; NOT_SUC; SUC_INJ; ALL_DISTINCT] THEN
  REWRITE_TAC[store_globals_def; MAP; crep_nested_seq_def] THEN
  ONCE_REWRITE_TAC[crep_evaluate_def] THEN REWRITE_TAC[ZIP; FUPDATE_LIST_THM] THEN
  REWRITE_TAC[crep_evaluate_def] THEN
  SIMP[crep_eval_def; NOT_MEM_FLOOKUP_ZIP; FLOOKUP_UPDATE; crep_set_globals_def] THEN
  SUBGOAL_THEN `(\x. word_add a (word x):5 word) o SUC =
                (\x. word_add (word_add a (word 1)) (word x))` ASSUME_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  LAST_X_ASSUM(MP_TAC o SPECL
   [`vs':((A)word_lab)list`;
    `crep_state_locals_fupd (K (crep_state_locals t' |+ (h,v)))
       (crep_state_globals_fupd (K (crep_state_globals t' |+ (a,v))) t'):(A,FFI)crep_state`;
    `word_add a (word 1):5 word`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `val (word_add a (word 1):5 word) <= val a + 1` MP_TAC THENL
     [REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_1] THEN MESON_TAC[MOD_LE]; ALL_TAC] THEN
    UNDISCH_TAC `val (a:5 word) + LENGTH (vs':((A)word_lab)list) < 32` THEN ARITH_TAC;
    ALL_TAC] THEN
  SIMP[GENLIST_CONS; ZIP; FUPDATE_LIST_THM; WORD_ADD_0]);;

let res_var_lookup_original_eq = prove
 (`!xs ys (lc:(K,V)fmap).
     ALL_DISTINCT xs /\ LENGTH xs = LENGTH ys ==>
     FOLDL crep_res_var (lc |++ ZIP xs ys) (ZIP xs (MAP (FLOOKUP lc) xs)) = lc`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THENL
   [FS[LENGTH; LENGTH_EQ_NIL] THEN RVEQ_TAC THEN
    REWRITE_TAC[ZIP; MAP; FUPDATE_LIST_THM; FOLDL];
    ALL_TAC] THEN
  NAMED_CASES_ON "ys" ["";"y ys"] THEN FS[LENGTH; NOT_SUC; SUC_INJ; ALL_DISTINCT] THEN
  REWRITE_TAC[ZIP; MAP; FUPDATE_LIST_THM; FOLDL] THEN
  SUBGOAL_THEN `(lc:(K,V)fmap) |+ (h,y) |++ ZIP t ys' = (lc |++ ZIP t ys') |+ (h,y)`
    SUBST1_TAC THENL
   [MATCH_MP_TAC FUPDATE_FUPDATE_LIST_COMMUTES THEN ASM_SIMP_TAC[MAP_ZIP]; ALL_TAC] THEN
  SUBGOAL_THEN
   `crep_res_var (((lc:(K,V)fmap) |++ ZIP t ys') |+ (h,y)) (h,FLOOKUP lc h) =
    lc |++ ZIP t ys'` SUBST1_TAC THENL
   [REWRITE_TAC[fmap_eq_flookup; flookup_res_var_thm; FLOOKUP_UPDATE] THEN
    GEN_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[NOT_MEM_FLOOKUP_ZIP];
    ASM_SIMP_TAC[]]);;

let eval_exps_not_load_global_eq = prove
 (`!(s:(A,FFI)crep_state) e v g.
     crep_eval s e = SOME v /\ (!ad. ~MEM (LoadGlob ad) (crep_exps e)) ==>
     crep_eval (crep_state_globals_fupd (K g) s) e = SOME v`,
  SUBGOAL_THEN
   `!(s:(A,FFI)crep_state) e g. (!ad. ~MEM (LoadGlob ad) (crep_exps e)) ==>
      crep_eval (crep_state_globals_fupd (K g) s) e = crep_eval s e`
   (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC crep_eval_ind THEN
  REWRITE_TAC[crep_exps_def; MEM_APPEND; DE_MORGAN_THM; MEM_FLAT; MEM_MAP; MEM] THEN
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[crep_eval_def] THEN
  SIMP[crep_mem_load_def] THEN
  TRY(AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC OPT_MMAP_CONG THEN
      REWRITE_TAC[]) THEN
  ASM_MESON_TAC[]);;

let load_glob_not_mem_load = prove
 (`!i (a:A word) h ad.
     ~MEM (LoadGlob ad) (crep_exps h) ==>
     ~MEM (LoadGlob ad) (FLAT (MAP crep_exps (load_shape a i h)))`,
  INDUCT_TAC THEN RW[] THENL [FS[load_shape_def; MAP; FLAT; MEM]; ALL_TAC] THEN
  FS[load_shape_def] THEN QCASES_ON "a = word 0" THEN
  FS[MAP; FLAT; MEM_APPEND; load_shape_def; crep_exps_def; APPEND_NIL; MEM] THEN
  ASM_MESON_TAC[]);;

let var_cexp_load_globals_empty = prove
 (`!ads a. FLAT (MAP var_cexp (load_globals a ads:((A)crep_exp)list)) = []`,
  INDUCT_TAC THEN RW[] THEN FS[var_cexp_def; load_globals_def; MAP; FLAT; APPEND]);;

let evaluate_seq_assign_load_globals = prove
 (`!ns (t:(A,FFI)crep_state) a.
     ALL_DISTINCT ns /\ val a + LENGTH ns <= 32 /\
     (!n. MEM n ns ==> ~(FLOOKUP (crep_state_locals t) n = NONE)) /\
     (!n. MEM n (list_of_seq (\x. word_add a (word x)) (LENGTH ns)) ==>
          ~(FLOOKUP (crep_state_globals t) n = NONE)) ==>
     crep_evaluate
       (crep_nested_seq (MAP2 crep_Assign ns (load_globals a (LENGTH ns))),t) =
     (NONE,
      crep_state_locals_fupd
        (K (crep_state_locals t |++
            ZIP ns (MAP (\n. THE (FLOOKUP (crep_state_globals t) n))
                        (list_of_seq (\x. word_add a (word x)) (LENGTH ns))))) t)`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THENL
   [REWRITE_TAC[LENGTH; load_globals_def; MAP2; crep_nested_seq_def; crep_evaluate_def;
                LIST_OF_SEQ; MAP; ZIP; FUPDATE_LIST_THM] THEN
    SIMP[crep_state_component_equality];
    ALL_TAC] THEN
  REWRITE_TAC[LENGTH; load_globals_def; MAP2; crep_nested_seq_def] THEN
  ONCE_REWRITE_TAC[crep_evaluate_def] THEN REWRITE_TAC[crep_evaluate_def] THEN
  FS[crep_eval_def; ALL_DISTINCT; MEM; LENGTH] THEN
  SUBGOAL_THEN `(\x. word_add a (word x):5 word) o SUC =
                (\x. word_add (word_add a (word 1)) (word x))`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[GENLIST_CONS; MEM; WORD_ADD_0; th]) THEN
              ASSUME_TAC th) THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  QCASES_ON "FLOOKUP (crep_state_globals t') a" THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  QCASES_ON "FLOOKUP (crep_state_locals t') h" THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN SIMP[] THEN
  LAST_X_ASSUM(MP_TAC o SPECL
   [`crep_state_locals_fupd (K (crep_state_locals t' |+ (h,a'))) t':(A,FFI)crep_state`;
    `word_add a (word 1):5 word`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN SIMP[FLOOKUP_UPDATE] THEN
    SUBGOAL_THEN `val (word_add a (word 1):5 word) <= val a + 1` MP_TAC THENL
     [REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_1] THEN MESON_TAC[MOD_LE]; ALL_TAC] THEN
    UNDISCH_TAC `val (a:5 word) + LENGTH (t:num list) < 32` THEN ARITH_TAC;
    DISCH_THEN SUBST1_TAC THEN
    SIMP[GENLIST_CONS; MAP; ZIP; FUPDATE_LIST_THM; WORD_ADD_0; THE_DEF]]);;

let flookup_res_var_distinct_eq = prove
 (`!xs x (fm:(K,V)fmap).
     ~MEM x (MAP FST xs) ==> FLOOKUP (FOLDL crep_res_var fm xs) x = FLOOKUP fm x`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[FOLDL; MAP; MEM; DE_MORGAN_THM] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  PAIR_CASES_ON `h:K#(V)option` THEN FS[flookup_res_var_thm]);;

let flookup_res_var_distinct_zip_eq = prove
 (`LENGTH (xs:K list) = LENGTH (ys:(V option)list) /\ ~MEM x xs ==>
   FLOOKUP (FOLDL crep_res_var (fm:(K,V)fmap) (ZIP xs ys)) x = FLOOKUP fm x`,
  STRIP_TAC THEN MATCH_MP_TAC flookup_res_var_distinct_eq THEN ASM_SIMP_TAC[MAP_ZIP]);;

let flookup_res_var_distinct = prove
 (`!ys (xs:K list) (zs:(V option)list) (fm:(K,V)fmap).
     distinct_lists xs ys /\ LENGTH xs = LENGTH zs ==>
     MAP (FLOOKUP (FOLDL crep_res_var fm (ZIP xs zs))) ys = MAP (FLOOKUP fm) ys`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MAP_EQ THEN REWRITE_TAC[GSYM ALL_MEM] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC flookup_res_var_distinct_zip_eq THEN
  FS[distinct_lists_def; GSYM ALL_MEM] THEN ASM_MESON_TAC[]);;

let flookup_res_var_zip_distinct = prove
 (`!ys (xs:K list) (as:V list) (cs:(V option)list) (fm:(K,V)fmap).
     distinct_lists xs ys /\ LENGTH xs = LENGTH as /\ LENGTH xs = LENGTH cs ==>
     MAP (FLOOKUP (FOLDL crep_res_var (fm |++ ZIP xs as) (ZIP xs cs))) ys =
     MAP (FLOOKUP fm) ys`,
  RW[] THEN DRULE flookup_res_var_distinct THEN
  DISCH_THEN(QSPECL_THEN ["cs"; "fm |++ ZIP xs as"] MP_TAC) THEN
  FS[] THEN ASM_MESON_TAC[map_flookup_fupdate_zip_not_mem]);;

let eval_some_var_cexp_local_lookup = prove
 (`!(s:(A,FFI)crep_state) e v n.
     crep_eval s e = SOME v /\ MEM n (var_cexp e) ==>
     ?w. FLOOKUP (crep_state_locals s) n = SOME w`,
  MATCH_MP_TAC crep_eval_ind THEN
  REWRITE_TAC[var_cexp_def; MEM_APPEND; MEM_FLAT; MEM_MAP; MEM] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[crep_eval_def]) THEN
  GVS(all_case_eqs()) THEN
  TRY(IMP_RES_TAC opt_mmap_mem_func) THEN ASM_MESON_TAC[]);;

let opt_mmap_eval_some_var_cexp_local_lookup = prove
 (`!(s:(A,FFI)crep_state) es vs n.
     OPT_MMAP (crep_eval s) es = SOME vs /\ MEM n (FLAT (MAP var_cexp es)) ==>
     ?w. FLOOKUP (crep_state_locals s) n = SOME w`,
  REPEAT STRIP_TAC THEN FS[MEM_FLAT; MEM_MAP] THEN
  IMP_RES_TAC opt_mmap_mem_func THEN GVS[] THEN
  IMP_RES_TAC eval_some_var_cexp_local_lookup THEN FS[] THEN ASM_MESON_TAC[]);;

let crep_eval_upd_clock_eq = prove
 (`!(t:(A,FFI)crep_state) e ck.
     crep_eval (crep_state_clock_fupd (K ck) t) e = crep_eval t e`,
  MATCH_MP_TAC crep_eval_ind THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[crep_eval_def] THEN SIMP[crep_mem_load_def] THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC OPT_MMAP_CONG THEN
  REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let crep_opt_mmap_eval_upd_clock_eq = prove
 (`!es (s:(A,FFI)crep_state) ck.
     OPT_MMAP (crep_eval (crep_state_clock_fupd (K (ck + crep_state_clock s)) s)) es =
     OPT_MMAP (crep_eval s) es`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC OPT_MMAP_CONG THEN
  REWRITE_TAC[crep_eval_upd_clock_eq]);;

(* clock lemmas used by crep_evaluate_add_clock_eq *)

let PCREPAUX_eval_upd_clock_fun = prove
 (`!(t:(A,FFI)crep_state) ck. crep_eval (crep_state_clock_fupd (K ck) t) = crep_eval t`,
  REWRITE_TAC[FUN_EQ_THM; crep_eval_upd_clock_eq]);;

let PCREPAUX_sh_mem_op_clock_upd = prove
 (`!op v a (s:(A,FFI)crep_state) (res:((B)crep_result)option) st c.
     crep_sh_mem_op op v a s = (res,st) ==>
     crep_sh_mem_op op v a (crep_state_clock_fupd (K c) s) =
     (res,crep_state_clock_fupd (K c) st)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ONELINE crep_sh_mem_op_def; crep_sh_mem_load_def; crep_sh_mem_store_def] THEN
  QCASES_ON "op" THEN SIMP[] THEN EVERY_CASE_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  SIMP[crep_set_var_def; crep_empty_locals_def]);;

let PCREPAUX_dec_clock_add = prove
 (`!(s:(A,FFI)crep_state) ck.
     ~(crep_state_clock s = 0) ==>
     crep_dec_clock (crep_state_clock_fupd (K (crep_state_clock s + ck)) s) =
     crep_state_clock_fupd (K (crep_state_clock (crep_dec_clock s) + ck))
       (crep_dec_clock s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[crep_dec_clock_def] THEN SIMP[] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

let crep_evaluate_add_clock_eq = prove
 (`!p (t:(A,FFI)crep_state) res st ck.
     crep_evaluate (p,t) = (res,st) /\ ~(res = SOME crep_TimeOut) ==>
     crep_evaluate (p,crep_state_clock_fupd (K (crep_state_clock t + ck)) t) =
     (res,crep_state_clock_fupd (K (crep_state_clock st + ck)) st)`,
  let simple_tac thl =
    REPEAT STRIP_TAC THEN
    FS([crep_evaluate_def; crep_eval_upd_clock_eq; crep_set_var_def; pan_mem_store_def;
        crep_set_globals_def; crep_dec_clock_def; crep_empty_locals_def] @ thl @
       all_case_eqs()) THEN
    RVEQ_TAC THEN FS[crep_state_component_equality] in
  REC_IND_TAC crep_evaluate_ind THEN REPEAT CONJ_TAC THEN
  PCREPAUX_CASE_TAC "crep_Dec"
   (REPEAT STRIP_TAC THEN
    QPAT_X_ASSUM "crep_evaluate (crep_Dec _ _ _,_) = _"
      (MP_TAC o ONCE_REWRITE_RULE[crep_evaluate_def]) THEN
    QCASES_ON "crep_eval s e" THEN SIMP[] THENL
     [STRIP_TAC THEN GVS[] THEN ONCE_REWRITE_TAC[crep_evaluate_def] THEN
      SIMP[crep_eval_upd_clock_eq];
      ALL_TAC] THEN
    PAIRARG_TAC THEN SIMP[] THEN STRIP_TAC THEN GVS[] THEN
    ONCE_REWRITE_TAC[crep_evaluate_def] THEN SIMP[crep_eval_upd_clock_eq]) THEN
  PCREPAUX_CASE_TAC "crep_ShMem"
   (REPEAT STRIP_TAC THEN
    FS([crep_evaluate_def; crep_eval_upd_clock_eq] @ all_case_eqs()) THEN RVEQ_TAC THEN
    IMP_RES_TAC crep_sh_mem_op_clock THEN IMP_RES_TAC PCREPAUX_sh_mem_op_clock_upd THEN
    ASM_REWRITE_TAC[]) THEN
  PCREPAUX_CASE_TAC "crep_Seq"
   (REPEAT STRIP_TAC THEN
    QPAT_X_ASSUM "crep_evaluate (crep_Seq _ _,_) = _"
      (MP_TAC o ONCE_REWRITE_RULE[crep_evaluate_def]) THEN
    PAIR_CASES_ON `crep_evaluate (c1:(A)crep_prog,s:(A,FFI)crep_state)` THEN
    SIMP[] THEN FS[PAIR_EQ] THEN COND_CASES_TAC THEN STRIP_TAC THEN GVS[] THEN
    ONCE_REWRITE_TAC[crep_evaluate_def] THEN GVS[]) THEN
  PCREPAUX_CASE_TAC "crep_If"
   (REPEAT STRIP_TAC THEN FS(crep_evaluate_def :: all_case_eqs()) THEN RVEQ_TAC THEN
    FS[crep_eval_upd_clock_eq]) THEN
  PCREPAUX_CASE_TAC "crep_While"
   (REPEAT STRIP_TAC THEN
    QPAT_X_ASSUM "crep_evaluate (crep_While _ _,_) = _"
      (MP_TAC o ONCE_REWRITE_RULE[crep_evaluate_def]) THEN
    QCASES_ON "crep_eval s e" THEN SIMP[] THENL
     [STRIP_TAC THEN GVS[] THEN ONCE_REWRITE_TAC[crep_evaluate_def] THEN
      SIMP[crep_eval_upd_clock_eq];
      ALL_TAC] THEN
    RENAME1 "crep_eval s e = SOME x" THEN QCASES_ON "x" THEN SIMP[] THEN
    COND_CASES_TAC THEN SIMP[] THENL
     [ALL_TAC;
      STRIP_TAC THEN GVS[] THEN ONCE_REWRITE_TAC[crep_evaluate_def] THEN
      SIMP[crep_eval_upd_clock_eq]] THEN
    COND_CASES_TAC THEN SIMP[] THEN
    PAIR_CASES_ON `crep_evaluate (c:(A)crep_prog,crep_dec_clock (s:(A,FFI)crep_state))` THEN
    SIMP[] THEN FS[PAIR_EQ] THEN DISCH_TAC THEN GVS(all_case_eqs()) THEN
    ONCE_REWRITE_TAC[crep_evaluate_def] THEN
    SIMP[crep_eval_upd_clock_eq; ADD_EQ_0; PCREPAUX_dec_clock_add]) THEN
  PCREPAUX_CASE_TAC "crep_Call"
   (REPEAT STRIP_TAC THEN
    QPAT_X_ASSUM "crep_evaluate (crep_Call _ _ _,_) = _"
      (MP_TAC o ONCE_REWRITE_RULE[crep_evaluate_def]) THEN
    DISCH_TAC THEN GVS(all_case_eqs()) THEN FULL_RES_TAC THEN
    RULE_ASSUM_TAC(CAKE_SIMP_RULE[]) THEN ONCE_REWRITE_TAC[crep_evaluate_def] THEN
    SIMP[PCREPAUX_eval_upd_clock_fun; ADD_EQ_0; PCREPAUX_dec_clock_add;
         crep_empty_locals_def]) THEN
  PCREPAUX_CASE_TAC "crep_ExtCall"
   (REPEAT STRIP_TAC THEN FS(crep_evaluate_def :: all_case_eqs()) THEN RVEQ_TAC THEN
    FS[]) THEN
  PCREPAUX_CASE_TAC "crep_Return" (simple_tac [PCREPAUX_eval_upd_clock_fun]) THEN
  PCREPAUX_CASE_TAC "crep_Tick" (simple_tac [] THEN DECIDE_TAC) THEN
  simple_tac []);;

let PCREPAUX_sh_mem_op_io = prove
 (`!op v a (s:(A,FFI)crep_state) (res:((B)crep_result)option) t.
     crep_sh_mem_op op v a s = (res,t) ==>
     isPREFIX (ffi_state_io_events (crep_state_ffi s))
              (ffi_state_io_events (crep_state_ffi t))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ONELINE crep_sh_mem_op_def; crep_sh_mem_load_def; crep_sh_mem_store_def] THEN
  QCASES_ON "op" THEN SIMP[] THEN EVERY_CASE_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  SIMP[crep_set_var_def; crep_empty_locals_def; IS_PREFIX_REFL] THEN
  ASM_MESON_TAC[SEM2AUX_call_FFI_io_events]);;

(* HOL4: evaluate_io_events_mono.  One tactic for every case: the evaluation *)
(* is unfolded once and split, the induction hypotheses are instantiated at *)
(* the facts found (FULL_RES_TAC), then the prefixes are chained.            *)

let crep_evaluate_io_events_mono = prove
 (`!exps (s1:(A,FFI)crep_state) res s2.
     crep_evaluate (exps,s1) = (res,s2) ==>
     isPREFIX (ffi_state_io_events (crep_state_ffi s1))
              (ffi_state_io_events (crep_state_ffi s2))`,
  REC_IND_TAC crep_evaluate_ind THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
  QPAT_X_ASSUM "crep_evaluate _ = _" (MP_TAC o ONCE_REWRITE_RULE[crep_evaluate_def]) THEN
  DISCH_TAC THEN GVS(all_case_eqs()) THEN FULL_RES_TAC THEN
  RULE_ASSUM_TAC(CAKE_SIMP_RULE[crep_empty_locals_def; crep_dec_clock_def;
                                crep_set_var_def; crep_set_globals_def]) THEN
  SIMP[crep_empty_locals_def; crep_dec_clock_def; crep_set_var_def;
       crep_set_globals_def; IS_PREFIX_REFL] THEN
  IMP_RES_TAC PCREPAUX_sh_mem_op_io THEN IMP_RES_TAC SEM2AUX_call_FFI_io_events THEN
  ASM_MESON_TAC[IS_PREFIX_TRANS; IS_PREFIX_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Tools for crep_evaluate_add_clock_io_events_mono (as in loopProps):       *)
(* add_clock_eq at the evaluation facts whose result is not a time out; the  *)
(* evaluations of the goal named one at a time; a goal isPREFIX x y from a   *)
(* chain of isPREFIX assumptions.                                            *)
(* ------------------------------------------------------------------------- *)

let PCREPAUX_is_eval_eq tm =
  try let l,r = dest_eq tm in
      fst(dest_const(fst(strip_comb l))) = "crep_evaluate" && is_pair r
  with Failure _ -> false;;

let PCREPAUX_is_clock_upd tm =
  try fst(dest_const(fst(strip_comb tm))) = "crep_state_clock_fupd"
  with Failure _ -> false;;

let PCREPAUX_add_clock_c = REWRITE_RULE[GSYM IMP_IMP] crep_evaluate_add_clock_eq;;

let PCREPAUX_result_rws =
  [option_DISTINCT; option_INJ; distinctness "crep_result"; injectivity "crep_result"];;

let PCREPAUX_ADD_CLOCK_FACTS_TAC (extra:term) : tactic = fun (asl,w as g) ->
  let evs = filter (fun th -> PCREPAUX_is_eval_eq (concl th) &&
                     not (PCREPAUX_is_clock_upd (snd(dest_pair(rand(lhs(concl th)))))))
                   (map snd asl) in
  MAP_EVERY (fun e (asl,w as g) ->
      try let th1 = SPEC extra (MATCH_MP PCREPAUX_add_clock_c e) in
          let ant = fst(dest_imp(concl th1)) in
          let nth = TAC_PROOF((asl,ant), ASM_REWRITE_TAC PCREPAUX_result_rws) in
          ASSUME_TAC (MP th1 nth) g
      with Failure _ -> ALL_TAC g) evs g;;

let PCREPAUX_SPLIT_GOAL_EVAL_TAC : tactic = fun (asl,w as g) ->
  let is_ev t =
    try fst(dest_const(fst(strip_comb t))) = "crep_evaluate" && is_pair(rand t)
    with Failure _ -> false in
  let fw = frees w in
  match filter (fun t -> subset (frees t) fw) (find_terms is_ev w) with
    [] -> failwith "PCREPAUX_SPLIT_GOAL_EVAL_TAC"
  | t::_ ->
      let ty1,ty2 = (match dest_type (type_of t) with (_,[a;b]) -> a,b | _ -> failwith "") in
      let av = freesl (w :: map (concl o snd) asl @ flat (map (hyp o snd) asl)) in
      let p0 = variant av (mk_var("q0",ty1)) in
      let p1 = variant (p0::av) (mk_var("q1",ty2)) in
      (MP_TAC(ISPEC t PAIR_SURJECTIVE) THEN
       DISCH_THEN(X_CHOOSE_THEN p0 (X_CHOOSE_THEN p1
         (fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th)))) g;;

let PCREPAUX_PREFIX_CHAIN_TAC : tactic = fun (asl,w as g) ->
  let is_pre t = try fst(dest_const(fst(strip_comb t))) = "isPREFIX" &&
                     length(snd(strip_comb t)) = 2 with Failure _ -> false in
  let args t = match snd(strip_comb t) with [a;b] -> a,b | _ -> failwith "" in
  if not (is_pre w) then failwith "PCREPAUX_PREFIX_CHAIN_TAC" else
  let x,y = args w in
  let facts = filter (fun th -> is_pre (concl th)) (map snd asl) in
  let rec search visited frontier =
    match frontier with
      [] -> failwith "PCREPAUX_PREFIX_CHAIN_TAC: no chain"
    | (a,th)::rest ->
        if aconv a y then th else
        let nexts = mapfilter (fun f ->
            let a',b' = args (concl f) in
            if aconv a' a && not (exists (aconv b') visited)
            then (b', MATCH_MP isPREFIX_TRANS (CONJ th f)) else failwith "") facts in
        search (map fst nexts @ visited) (rest @ nexts) in
  let th0 = ISPEC x IS_PREFIX_REFL in
  ACCEPT_TAC (search [x] [(x,th0)]) g;;

let PCREPAUX_sh_mem_op_res = prove
 (`!op v a (s:(A,FFI)crep_state) (res:((B)crep_result)option) t.
     crep_sh_mem_op op v a s = (res,t) ==>
     res = NONE \/ res = SOME crep_Error \/ ?e. res = SOME (crep_FinalFFI e)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ONELINE crep_sh_mem_op_def; crep_sh_mem_load_def; crep_sh_mem_store_def] THEN
  QCASES_ON "op" THEN SIMP[] THEN EVERY_CASE_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN MESON_TAC[]);;

(* the run that times out, by induction; one tactic for every case *)

let PCREPAUX_timeout_io = prove
 (`!extra p (s:(A,FFI)crep_state) t.
     crep_evaluate (p,s) = (SOME crep_TimeOut,t) ==>
     isPREFIX (ffi_state_io_events (crep_state_ffi t))
       (ffi_state_io_events (crep_state_ffi (SND (crep_evaluate
          (p,crep_state_clock_fupd (K (crep_state_clock s + extra)) s)))))`,
  GEN_TAC THEN REC_IND_TAC crep_evaluate_ind THEN REPEAT CONJ_TAC THEN
  REPEAT STRIP_TAC THEN
  QPAT_X_ASSUM "crep_evaluate _ = _" (MP_TAC o ONCE_REWRITE_RULE[crep_evaluate_def]) THEN
  DISCH_TAC THEN GVS(all_case_eqs()) THEN
  IMP_RES_TAC PCREPAUX_sh_mem_op_res THEN
  RULE_ASSUM_TAC(REWRITE_RULE PCREPAUX_result_rws) THEN TRY(FIRST_ASSUM CONTR_TAC) THEN
  FULL_RES_TAC THEN PCREPAUX_ADD_CLOCK_FACTS_TAC `extra:num` THEN
  ONCE_REWRITE_TAC[crep_evaluate_def] THEN
  SIMP[PCREPAUX_eval_upd_clock_fun; crep_eval_upd_clock_eq; ADD_EQ_0;
       PCREPAUX_dec_clock_add; crep_empty_locals_def; crep_dec_clock_def;
       IS_PREFIX_REFL] THEN
  REPEAT ((PCREPAUX_SPLIT_GOAL_EVAL_TAC THEN REWRITE_TAC[pair_CASE]) ORELSE
          CHANGED_TAC (TOP_CASE_TAC ORELSE COND_CASES_TAC)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SND; FST]) THEN
  IMP_RES_TAC crep_evaluate_io_events_mono THEN
  FS[crep_dec_clock_def; crep_empty_locals_def; IS_PREFIX_REFL] THEN
  RFS[] THEN PCREPAUX_PREFIX_CHAIN_TAC);;

(* HOL4: evaluate_add_clock_io_events_mono; a run that does not time out   *)
(* gives the same result with more clock (crep_evaluate_add_clock_eq)      *)

let crep_evaluate_add_clock_io_events_mono = prove
 (`!exps (s:(A,FFI)crep_state) extra.
     isPREFIX
       (ffi_state_io_events (crep_state_ffi (SND (crep_evaluate (exps,s)))))
       (ffi_state_io_events (crep_state_ffi (SND (crep_evaluate
          (exps,crep_state_clock_fupd (K (crep_state_clock s + extra)) s)))))`,
  REPEAT GEN_TAC THEN
  PAIR_CASES_ON `crep_evaluate (exps:(A)crep_prog,s:(A,FFI)crep_state)` THEN
  REWRITE_TAC[SND] THEN
  ASM_CASES_TAC `p0 = SOME (crep_TimeOut:(A)crep_result)` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_MESON_TAC[PCREPAUX_timeout_io];
    MP_TAC(SPECL [`exps:(A)crep_prog`; `s:(A,FFI)crep_state`;
                  `p0:((A)crep_result)option`; `p1:(A,FFI)crep_state`; `extra:num`]
                 crep_evaluate_add_clock_eq) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    SIMP[SND; IS_PREFIX_REFL]]);;

let PCREPAUX_sh_mem_op_code = prove
 (`!op v a (s:(A,FFI)crep_state) (res:((B)crep_result)option) t.
     crep_sh_mem_op op v a s = (res,t) ==> crep_state_code t = crep_state_code s`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ONELINE crep_sh_mem_op_def; crep_sh_mem_load_def; crep_sh_mem_store_def] THEN
  QCASES_ON "op" THEN SIMP[] THEN EVERY_CASE_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  SIMP[crep_set_var_def; crep_empty_locals_def]);;

let evaluate_code_invariant = prove
 (`!p (t:(A,FFI)crep_state) res st.
     crep_evaluate (p,t) = (res,st) ==> crep_state_code st = crep_state_code t`,
  REC_IND_TAC crep_evaluate_ind THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
  QPAT_X_ASSUM "crep_evaluate _ = _" (MP_TAC o ONCE_REWRITE_RULE[crep_evaluate_def]) THEN
  DISCH_TAC THEN GVS(all_case_eqs()) THEN FULL_RES_TAC THEN
  IMP_RES_TAC PCREPAUX_sh_mem_op_code THEN
  RULE_ASSUM_TAC(CAKE_SIMP_RULE[crep_empty_locals_def; crep_dec_clock_def;
                                crep_set_var_def; crep_set_globals_def]) THEN
  SIMP[crep_empty_locals_def; crep_dec_clock_def; crep_set_var_def;
       crep_set_globals_def] THEN
  ASM_MESON_TAC[]);;

(* crep_exps_of: the clauses for crep_Call are parsed apart (e is a function *)
(* name there and an expression elsewhere); HOL4 e::l1 ++ l2 is            *)
(* (e::l1) ++ l2                                                           *)

let crep_exps_of_def = cake_def
  (list_mk_conj
   [`(crep_exps_of (crep_Dec _ e p:(A)crep_prog) = CONS e (crep_exps_of p)) /\
     (crep_exps_of (crep_Seq p q) = APPEND (crep_exps_of p) (crep_exps_of q)) /\
     (crep_exps_of (crep_If e p q) =
        APPEND (CONS e (crep_exps_of p)) (crep_exps_of q)) /\
     (crep_exps_of (crep_While e p) = CONS e (crep_exps_of p))`;
    `(crep_exps_of (crep_Call NONE e es:(A)crep_prog) = es) /\
     (crep_exps_of (crep_Call (SOME (_,NONE)) e es) = es) /\
     (crep_exps_of (crep_Call (SOME (_,SOME (_,p'))) e es) =
        APPEND es (crep_exps_of p'))`;
    `(crep_exps_of (crep_Store e1 e2:(A)crep_prog) = [e1; e2]) /\
     (crep_exps_of (crep_Store32 e1 e2) = [e1; e2]) /\
     (crep_exps_of (crep_StoreByte e1 e2) = [e1; e2]) /\
     (crep_exps_of (StoreGlob _ e) = [e]) /\
     (crep_exps_of (crep_Return es) = es) /\
     (crep_exps_of (crep_Assign _ e) = [e]) /\
     (crep_exps_of (crep_ShMem _ _ e) = [e]) /\
     (crep_exps_of _ = [])`]);;

(* crep_every_exp: the clauses are parsed in two quotations (w is a word in  *)
(* crep_Const and a 5 word in LoadGlob); termination: HOL4 measure           *)
(* (exp_size ARB o SND), MEM_IMP_exp_size                                   *)

let crep_every_exp_def = cake_def_wf
  `MEASURE ((crep_exp_size ARB o SND):((A)crep_exp->bool)#(A)crep_exp->num)`
  (REWRITE_TAC[measure_THM; o_THM] THEN TERM_TAC)
  (list_mk_conj
   [`(crep_every_exp P (crep_Const (w:A word)) <=> P (crep_Const w)) /\
     (crep_every_exp P (crep_Var v) <=> P (crep_Var v)) /\
     (crep_every_exp P (crep_Load e) <=> P (crep_Load e) /\ crep_every_exp P e) /\
     (crep_every_exp P (crep_Load32 e) <=> P (crep_Load32 e) /\ crep_every_exp P e) /\
     (crep_every_exp P (crep_LoadByte e) <=> P (crep_LoadByte e) /\ crep_every_exp P e)`;
    `(crep_every_exp P (LoadGlob w:(A)crep_exp) <=> P (LoadGlob w)) /\
     (crep_every_exp P (crep_Op bop es) <=>
        P (crep_Op bop es) /\ ALL (crep_every_exp P) es) /\
     (crep_every_exp P (Crepop op es) <=>
        P (Crepop op es) /\ ALL (crep_every_exp P) es) /\
     (crep_every_exp P (crep_Cmp c e1 e2) <=>
        P (crep_Cmp c e1 e2) /\ crep_every_exp P e1 /\ crep_every_exp P e2) /\
     (crep_every_exp P (crep_Shift sh e1 e2) <=>
        P (crep_Shift sh e1 e2) /\ crep_every_exp P e1 /\ crep_every_exp P e2) /\
     (crep_every_exp P crep_BaseAddr <=> P crep_BaseAddr) /\
     (crep_every_exp P crep_TopAddr <=> P crep_TopAddr)`]);;

let crep_every_exp_ind = cake_ind "crep_every_exp";;
