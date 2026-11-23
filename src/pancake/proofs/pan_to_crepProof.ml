(* ========================================================================= *)
(* pan_to_crepProof: port of HOL4 pancake/proofs/pan_to_crepProofScript.sml  *)
(* (CakeML v3479).  Correctness proof for pan_to_crep.                       *)
(*                                                                           *)
(* Notes on the port:                                                        *)
(* - Names: doc/names.tsv; local helpers are PP2CAUX_ (PP2CAUX_A_ and        *)
(*   PP2CAUX_B_ in two parts of the file, marked below).                     *)
(* - HOL4 s.f is pan_state_f s / crep_state_f s, s with f := v is           *)
(*   ..._f_fupd (K v) s; GENLIST is list_of_seq; FOLDR MAX 0 l is            *)
(*   ITLIST MAX l 0; ZIP (xs,ys) is ZIP xs ys, always with equal lengths     *)
(*   (slc and tlc are only used that way); EVERY is ALL, LIST_REL is ALL2.   *)
(* - pc_compile_correct: HOL4 proves it by recInduct with suspend/Resume;    *)
(*   here PP2CAUX_pc_stmt is its statement, PP2CAUX_pc_cases the cases of    *)
(*   pan_evaluate_ind, each proved as PP2CAUX_pc_NAME, and pc_compile_correct *)
(*   is assembled where HOL4 has Finalise.  The Call case is split by the   *)
(*   shape of the call (PP2CAUX_pc_Call_none, _retnone, _ret) instead of     *)
(*   HOL4's labels Call_TailCall, Call_Ret_TimeOut, Call_Ret_Return,         *)
(*   Call_Ret_Exception and Call_Ret_FinalFFI.  HOL4's ML tactics            *)
(*   (clock_zero_tail_rt_tac, ...) are not ported as such.                   *)
(* - HOL4 binds locals_rel_wf_shape twice (the second one [local], an        *)
(*   FEVERY form); the second is PP2CAUX_locals_rel_wf_shape_fevery.         *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "pancake/proofs/crep_inlineProof.ml";;
needs "pancake/semantics/panSem.ml";;
needs "pancake/semantics/panProps.ml";;
needs "pancake/crepLang.ml";;
needs "pancake/semantics/crepSem.ml";;
needs "pancake/pan_common.ml";;
needs "pancake/semantics/crepProps.ml";;
needs "pancake/semantics/pan_commonProps.ml";;
needs "pancake/pan_to_crep.ml";;

prioritize_num();;
type_invention_error := true;;

(* state relation *)

let excp_rel_def = cake_def
  `excp_rel (ceids:(B,C)fmap) (seids:(B,D)fmap) <=>
     FDOM seids = FDOM ceids /\
     (!e e' n n'.
        FLOOKUP ceids e = SOME n /\
        FLOOKUP ceids e' = SOME n' /\
        n = n' ==> e = e')`;;

let pan_to_crepProof_ctxt_fc_def = cake_def
  `pan_to_crepProof_ctxt_fc cvs (em:(eid,A word)fmap) vs shs ns =
     pan_to_crep_context_REC
       (FEMPTY |++ ZIP vs (ZIP shs (with_shape shs ns))) cvs em (MAX_LIST ns)`;;

let pan_to_crepProof_code_rel_def = cake_def
  `pan_to_crepProof_code_rel (ctxt:(A)pan_to_crep_context) s_code t_code <=>
     !f vshs prog rsh.
       FLOOKUP s_code f = SOME (vshs,prog,rsh) ==>
       localised_prog prog /\
       FLOOKUP (pan_to_crep_context_funcs ctxt) f = SOME (vshs,rsh) /\
       (let vs = MAP FST vshs in
        let shs = MAP SND vshs in
        let ns = list_of_seq I (size_of_shape (Comb shs)) in
        let nctxt = pan_to_crepProof_ctxt_fc (pan_to_crep_context_funcs ctxt)
                      (pan_to_crep_context_eids ctxt) vs shs ns in
        FLOOKUP t_code f = SOME (ns,pan_to_crep_compile nctxt prog))`;;

let pan_to_crepProof_state_rel_def = cake_def
  `pan_to_crepProof_state_rel (s:(A,FFI)pan_state) (t:(A,FFI)crep_state) <=>
     pan_state_memory s = crep_state_memory t /\
     pan_state_memaddrs s = crep_state_memaddrs t /\
     pan_state_sh_memaddrs s = crep_state_sh_memaddrs t /\
     pan_state_structs s = [] /\
     pan_state_globals s = FEMPTY /\
     pan_state_clock s = crep_state_clock t /\
     pan_state_be s = crep_state_be t /\
     pan_state_ffi s = crep_state_ffi t /\
     pan_state_base_addr s = crep_state_base_addr t /\
     pan_state_top_addr s = crep_state_top_addr t`;;

(* HOL4 [local] *)

let pan_to_crepProof_state_rel_structs = prove
 (`pan_to_crepProof_state_rel (s:(A,FFI)pan_state) (t:(A,FFI)crep_state)
   ==> pan_state_structs s = []`,
  SIMP[pan_to_crepProof_state_rel_def]);;

(* HOL4 [local] *)

let state_rel_globals = prove
 (`pan_to_crepProof_state_rel (s:(A,FFI)pan_state) (t:(A,FFI)crep_state)
   ==> pan_state_globals s = FEMPTY`,
  SIMP[pan_to_crepProof_state_rel_def]);;

let pan_to_crepProof_locals_rel_def = cake_def
  `pan_to_crepProof_locals_rel (ctxt:(B)pan_to_crep_context)
     (s_locals:(mlstring,(A)pan_v)fmap) (t_locals:(num,(A)word_lab)fmap) <=>
     pan_commonProps_no_overlap (pan_to_crep_context_vars ctxt) /\
     pan_commonProps_ctxt_max (pan_to_crep_context_vmax ctxt)
       (pan_to_crep_context_vars ctxt) /\
     (!vname v.
        FLOOKUP s_locals vname = SOME v ==>
        ?ns vs. FLOOKUP (pan_to_crep_context_vars ctxt) vname =
                  SOME (shape_of v,ns) /\
                OPT_MMAP (FLOOKUP t_locals) ns = SOME vs /\
                flatten v = vs /\
                is_wf_shape ([]:(mlstring#struct_info)list) (shape_of v))`;;

let code_rel_imp = prove
 (`pan_to_crepProof_code_rel (ctxt:(A)pan_to_crep_context) s_code t_code ==>
   !f vshs prog.
     FLOOKUP s_code f = SOME (vshs,prog,rsh) ==>
     localised_prog prog /\
     FLOOKUP (pan_to_crep_context_funcs ctxt) f = SOME (vshs,rsh) /\
     (let vs = MAP FST vshs in
      let shs = MAP SND vshs in
      let ns = list_of_seq I (size_of_shape (Comb shs)) in
      let nctxt = pan_to_crepProof_ctxt_fc (pan_to_crep_context_funcs ctxt)
                    (pan_to_crep_context_eids ctxt) vs shs ns in
      FLOOKUP t_code f = SOME (ns,pan_to_crep_compile nctxt prog))`,
  REWRITE_TAC[pan_to_crepProof_code_rel_def] THEN MESON_TAC[]);;

let code_rel_empty_locals = prove
 (`pan_to_crepProof_code_rel (ctxt:(A)pan_to_crep_context)
     (pan_state_code (s:(A,FFI)pan_state)) (crep_state_code (t:(A,FFI)crep_state))
   ==> pan_to_crepProof_code_rel ctxt (pan_state_code (pan_empty_locals s))
         (crep_state_code (crep_empty_locals t))`,
  RW[pan_to_crepProof_code_rel_def; crep_empty_locals_def; pan_empty_locals_def] THEN
  ASM_MESON_TAC[]);;

let cexp_heads_eq = prove
 (`!es:(A list)list. cexp_heads es = cexp_heads_simp es`,
  LIST_INDUCT_TAC THEN RW[cexp_heads_def; cexp_heads_simp_def] THEN
  FS[] THEN EVERY_CASE_TAC THEN FS[]);;

(* HOL4: TODO: move to crepProps and (perhaps) replace eval_load_shape_el_rel *)

let load_shape_el_rel = prove
 (`!m n (a:A word) (t:B) e.
     n < m ==>
     EL n (load_shape a m e) =
     if word_add a (word_mul bytes_in_word (word n)) = word 0 then crep_Load e
     else crep_Load (crep_Op asm_Add
                       [e; crep_Const (word_add a (word_mul bytes_in_word (word n)))])`,
  INDUCT_TAC THENL [REWRITE_TAC[LT]; ALL_TAC] THEN
  INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[load_shape_def; EL; LT_SUC; LT_0] THENL
   [SUBGOAL_THEN `word_add (a:A word) (word_mul bytes_in_word (word 0)) = a`
      SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    COND_CASES_TAC THEN REWRITE_TAC[HD];
    DISCH_TAC THEN
    SUBGOAL_THEN `word_add (a:A word) (word_mul bytes_in_word (word (SUC n))) =
                  word_add (word_add a bytes_in_word) (word_mul bytes_in_word (word n))`
      SUBST1_TAC THENL [REWRITE_TAC[ADD1] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    REWRITE_TAC[COND_RAND; TL] THEN ASM_SIMP_TAC[COND_ID]]);;
let compile_exp_val_rel = prove
 (`!s e v (t:(A,B)crep_state) ct es sh.
     pan_eval s e = SOME v /\
     pan_to_crepProof_state_rel s t /\
     pan_to_crepProof_code_rel ct (pan_state_code s) (crep_state_code t) /\
     pan_to_crepProof_locals_rel ct (pan_state_locals s) (crep_state_locals t) /\
     localised_exp e /\
     pan_to_crep_compile_exp ct e = (es,sh) ==>
     MAP (crep_eval t) es = MAP SOME (flatten v) /\
     LENGTH es = size_of_shape sh /\
     shape_of v = sh /\
     is_wf_shape ([]:(mlstring#struct_info)list) sh`,
  MATCH_MP_TAC pan_eval_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN TRY DISCH_TAC THENL
  [
  (* Const *)
  GVS[pan_eval_def; pan_to_crep_compile_exp_def] THEN
  GVS[flatten_def; crep_eval_def; size_of_shape_def; shape_of_def; is_wf_shape_def];
  (* Var Local *)
  STRIP_TAC THEN RFS[pan_eval_def] THEN
  QPAT_X_ASSUM "pan_to_crepProof_locals_rel _ _ _"
    (STRIP_ASSUME_TAC o REWRITE_RULE[pan_to_crepProof_locals_rel_def]) THEN
  FIRST_X_ASSUM DRULE THEN STRIP_TAC THEN
  RFS[pan_to_crep_compile_exp_def] THEN RVEQ_TAC THEN
  RFS[lookup_locals_eq_map_vars] THEN RFS[opt_mmap_eq_some] THEN
  ASM_MESON_TAC[LENGTH_MAP; length_flatten_eq_size_of_shape];
  (* Var Global *)
  STRIP_TAC THEN FS[localised_exp_simps];
  (* RStruct *)
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RFS[pan_eval_def; option_case_eq; localised_exp_simps] THEN RVEQ_TAC THEN
  RFS[pan_to_crep_compile_exp_def] THEN RVEQ_TAC THEN
  REWRITE_TAC[size_of_shape_def; shape_of_def; is_wf_shape_def; flatten_def] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th ->
    free_in `es:((A)panLang_exp)list` (concl th)))) THEN
  SPEC_TAC(`a:((A)pan_v)list`,`a:((A)pan_v)list`) THEN
  SPEC_TAC(`es:((A)panLang_exp)list`,`es:((A)panLang_exp)list`) THEN
  LIST_INDUCT_TAC THEN GEN_TAC THEN REWRITE_TAC[OPT_MMAP_def] THENL
   [REPEAT STRIP_TAC THEN GVS[MAP; FLAT; LENGTH; SUM; ALL]; ALL_TAC] THEN
  REWRITE_TAC[MEM; ALL; TAUT `(a \/ b ==> c) <=> (a ==> c) /\ (b ==> c)`;
              FORALL_AND_THM; FORALL_UNWIND_THM2; OPTION_BIND_EQUALS_OPTION;
              option_INJ] THEN
  REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN RVEQ_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x':((A)pan_v)list`) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
    [`x:(A)pan_v`; `t:(A,B)crep_state`; `ct:(A)pan_to_crep_context`;
     `FST (pan_to_crep_compile_exp (ct:(A)pan_to_crep_context) (h:(A)panLang_exp))`;
     `SND (pan_to_crep_compile_exp (ct:(A)pan_to_crep_context) (h:(A)panLang_exp))`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[MAP; FLAT; MAP_APPEND; LENGTH_APPEND; SUM; ALL;
                  injectivity "shape"; CONS_11] THEN
  FS[injectivity "shape"];
  (* RField *)
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RFS[pan_eval_def; option_case_eq; case_eq "pan_v"; localised_exp_simps] THEN
  RVEQ_TAC THEN RFS[pan_to_crep_compile_exp_def] THEN
  PAIRARG_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL
    [`t:(A,B)crep_state`; `ct:(A)pan_to_crep_context`; `cexp:((A)crep_exp)list`;
     `shape:shape`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[shape_of_def; flatten_def; is_wf_shape_def;
                              case_def "shape"]) THEN
  SUBGOAL_THEN
   `!(a:((A)pan_v)list) index (cexp:((A)crep_exp)list) es sh.
      index < LENGTH a /\
      MAP (crep_eval (t:(A,B)crep_state)) cexp = MAP SOME (FLAT (MAP flatten a)) /\
      ALL (is_wf_shape ([]:(mlstring#struct_info)list)) (MAP shape_of a) /\
      comp_field index (MAP shape_of a) cexp = (es,sh)
      ==> MAP (crep_eval t) es = MAP SOME (flatten (EL index a)) /\
          LENGTH es = size_of_shape sh /\
          shape_of (EL index a) = sh /\
          is_wf_shape ([]:(mlstring#struct_info)list) sh`
    (fun th -> MATCH_MP_TAC th THEN EXISTS_TAC `cexp:((A)crep_exp)list` THEN
               ASM_REWRITE_TAC[]) THEN
  LIST_INDUCT_TAC THENL [REWRITE_TAC[LENGTH; LT]; ALL_TAC] THEN
  INDUCT_TAC THEN
  REWRITE_TAC[MAP; FLAT; ALL; comp_field_def; NOT_SUC; EL; HD; TL; SUC_SUB1;
              LENGTH; LT_SUC; LT_0; PAIR_EQ] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN RVEQ_TAC THEN
  (SUBGOAL_THEN `size_of_shape (shape_of (h:(A)pan_v)) = LENGTH (MAP SOME (flatten h))`
    ASSUME_TAC THENL
   [ASM_SIMP_TAC[length_flatten_eq_size_of_shape; LENGTH_MAP]; ALL_TAC]) THEN
  QPAT_ASSUM "MAP (crep_eval t) _ = _"
    (MP_TAC o AP_TERM `LENGTH:(((A)word_lab)option)list->num`) THEN
  ASM_REWRITE_TAC[MAP_APPEND; LENGTH_MAP; LENGTH_APPEND] THEN DISCH_TAC THENL
  [ASM_SIMP_TAC[LENGTH_TAKE; LENGTH_MAP; ARITH_RULE `n <= n + m`; MAP_TAKE; MAP_APPEND;
                TAKE_LENGTH_APPEND] THEN
   MESON_TAC[TAKE_LENGTH_APPEND; LENGTH_MAP];
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   EXISTS_TAC `DROP (size_of_shape (shape_of (h:(A)pan_v))) (cexp':((A)crep_exp)list)` THEN
   ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC map_append_eq_drop THEN ASM_REWRITE_TAC[GSYM MAP_APPEND]];
  (* NStruct *)
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  IMP_RES_TAC pan_to_crepProof_state_rel_structs THEN
  RFS[pan_eval_def; ALOOKUP_DEF] THEN PAIRARG_TAC THEN FS[];
  (* NField *)
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  IMP_RES_TAC pan_to_crepProof_state_rel_structs THEN
  RFS[pan_eval_def; option_case_eq; case_eq "pan_v"; ALOOKUP_DEF];
  (* Load *)
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  IMP_RES_TAC pan_to_crepProof_state_rel_structs THEN
  RFS[pan_eval_def; option_case_eq; case_eq "pan_v"; case_eq "word_lab"; COND_CASE_EQ;
      localised_exp_simps] THEN
  RVEQ_TAC THEN RFS[pan_to_crep_compile_exp_def] THEN PAIRARG_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`t:(A,B)crep_state`; `ct:(A)pan_to_crep_context`;
    `cexp:((A)crep_exp)list`; `shape':shape`]) THEN
  ASM_REWRITE_TAC[flatten_def; MAP; MAP_EQ_SING; shape_of_def] THEN STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[case_def "list"; PAIR_EQ]) THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM) o check (fun th ->
    is_conj(concl th) && is_eq(lhand(concl th)) &&
    rhs(lhand(concl th)) = `es:((A)crep_exp)list`)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP mem_load_some_shape_eq) THEN
  ASM_REWRITE_TAC[length_load_shape_eq_shape] THEN
  REWRITE_TAC[LIST_EQ; LENGTH_MAP; length_load_shape_eq_shape] THEN
  (SUBGOAL_THEN `LENGTH (flatten (v:(A)pan_v)) = size_of_shape shape` ASSUME_TAC THENL
    [MP_TAC(ISPEC `v:(A)pan_v` length_flatten_eq_size_of_shape) THEN ASM_REWRITE_TAC[];
     ALL_TAC]) THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[EL_MAP; length_load_shape_eq_shape; eval_load_shape_el_rel] THEN
  REWRITE_TAC[crep_eval_def; OPT_MMAP_def] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
    rhs(concl th) = `crep_eval (t:(A,B)crep_state) x0`)) THEN
  REWRITE_TAC[OPTION_BIND_def; case_def "option"; case_def "word_lab"; ALL; MAP;
              word_op_def; ITLIST; OPTION_MAP_DEF; WORD_ADD_0] THEN
  QPAT_X_ASSUM "pan_to_crepProof_state_rel s t" (STRIP_ASSUME_TAC o
    REWRITE_RULE[pan_to_crepProof_state_rel_def]) THEN
  MP_TAC(ISPECL [`shape:shape`; `a:A word`; `t:(A,B)crep_state`; `v:(A)pan_v`; `n:num`]
    (INST [`[]:(mlstring#struct_info)list`,`stcs:(mlstring#struct_info)list`]
       mem_load_flat_rel)) THEN
  ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE
    [ASSUME `pan_state_memaddrs (s:(A,B)pan_state) = crep_state_memaddrs (t:(A,B)crep_state)`;
     ASSUME `pan_state_memory (s:(A,B)pan_state) = crep_state_memory (t:(A,B)crep_state)`]) THEN
  ASM_SIMP_TAC[LENGTH_TAKE; LT_IMP_LE] THEN
  REWRITE_TAC[case_def "binop"; OPTION_MAP_DEF; case_def "option"; case_def "word_lab"] THEN
  DISCH_THEN ACCEPT_TAC;
  (* Load32 *)
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RFS[pan_eval_def; option_case_eq; case_eq "pan_v"; case_eq "word_lab";
      localised_exp_simps] THEN
  RVEQ_TAC THEN RFS[pan_to_crep_compile_exp_def] THEN PAIRARG_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`t:(A,B)crep_state`; `ct:(A)pan_to_crep_context`;
    `cexp:((A)crep_exp)list`; `shape:shape`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[shape_of_def; flatten_def]) THEN RVEQ_TAC THEN
  QCASES_ON "cexp" THEN
  FS[size_of_shape_def; LENGTH; MAP; CONS_11; NOT_CONS_NIL; case_def "shape"] THEN
  RVEQ_TAC THEN
  FS[flatten_def; shape_of_def; is_wf_shape_def; crep_eval_def; size_of_shape_def;
     LENGTH; MAP] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[pan_to_crepProof_state_rel_def]) THEN FS[] THEN RFS[];
  (* LoadByte *)
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RFS[pan_eval_def; option_case_eq; case_eq "pan_v"; case_eq "word_lab";
      localised_exp_simps] THEN
  RVEQ_TAC THEN RFS[pan_to_crep_compile_exp_def] THEN PAIRARG_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`t:(A,B)crep_state`; `ct:(A)pan_to_crep_context`;
    `cexp:((A)crep_exp)list`; `shape:shape`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[shape_of_def; flatten_def]) THEN RVEQ_TAC THEN
  QCASES_ON "cexp" THEN
  FS[size_of_shape_def; LENGTH; MAP; CONS_11; NOT_CONS_NIL; case_def "shape"] THEN
  RVEQ_TAC THEN
  FS[flatten_def; shape_of_def; is_wf_shape_def; crep_eval_def; size_of_shape_def;
     LENGTH; MAP] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[pan_to_crepProof_state_rel_def]) THEN FS[] THEN RFS[];
  (* Op *)
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RFS[pan_eval_def; option_case_eq; localised_exp_simps] THEN
  RVEQ_TAC THEN RFS[pan_to_crep_compile_exp_def; cexp_heads_eq; cexp_heads_simp_def] THEN
  SUBGOAL_THEN
   `~MEM [] (MAP FST (MAP (pan_to_crep_compile_exp (ct:(A)pan_to_crep_context))
                       (es:((A)panLang_exp)list))) /\
    MAP (crep_eval (t:(A,B)crep_state))
      (MAP HD (MAP FST (MAP (pan_to_crep_compile_exp ct) es))) =
    MAP SOME (MAP v2word (a:((A)pan_v)list))`
   STRIP_ASSUME_TAC THENL
   [QPAT_X_ASSUM "ALL localised_exp es" MP_TAC THEN
    QPAT_X_ASSUM "ALL _ a" MP_TAC THEN
    QPAT_X_ASSUM "OPT_MMAP _ es = SOME a" MP_TAC THEN
    QPAT_X_ASSUM "!y. MEM y es ==> _" MP_TAC THEN
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
      free_in `es:((A)panLang_exp)list` (concl th) ||
      free_in `a:((A)pan_v)list` (concl th)))) THEN
    SPEC_TAC(`a:((A)pan_v)list`,`a:((A)pan_v)list`) THEN
    SPEC_TAC(`es:((A)panLang_exp)list`,`es:((A)panLang_exp)list`) THEN
    LIST_INDUCT_TAC THEN GEN_TAC THEN REWRITE_TAC[OPT_MMAP_def] THENL
    [REPEAT STRIP_TAC THEN GVS[MAP; MEM]; ALL_TAC] THEN
    REWRITE_TAC[MEM; ALL; TAUT `(a \/ b ==> c) <=> (a ==> c) /\ (b ==> c)`;
                FORALL_AND_THM; FORALL_UNWIND_THM2; OPTION_BIND_EQUALS_OPTION;
                option_INJ] THEN
    REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN RVEQ_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ALL]) THEN FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x':((A)pan_v)list`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN
    QCASES_ON "x" THEN FS[case_def "pan_v"] THEN QCASES_ON "a" THEN
    FS[case_def "word_lab"] THEN
    FIRST_X_ASSUM (MP_TAC o SPECL
      [`pan_Val (Word a'):(A)pan_v`; `t:(A,B)crep_state`; `ct:(A)pan_to_crep_context`;
       `FST (pan_to_crep_compile_exp (ct:(A)pan_to_crep_context) (h:(A)panLang_exp))`;
       `SND (pan_to_crep_compile_exp (ct:(A)pan_to_crep_context) (h:(A)panLang_exp))`]) THEN
    ASM_REWRITE_TAC[flatten_def; MAP; MAP_EQ_SING] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[HD; NOT_CONS_NIL; v2word_def];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) && is_pair(rhs(concl th)))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o REWRITE_RULE[case_def "option"; PAIR_EQ]) THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[MAP; flatten_def; shape_of_def; size_of_shape_def; is_wf_shape_def; LENGTH] THEN
  REWRITE_TAC[crep_eval_def] THEN
  SUBGOAL_THEN `OPT_MMAP (crep_eval (t:(A,B)crep_state))
                  (MAP HD (MAP FST (MAP (pan_to_crep_compile_exp (ct:(A)pan_to_crep_context))
                    (es:((A)panLang_exp)list)))) =
                SOME (MAP v2word (a:((A)pan_v)list))` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[opt_mmap_eq_some]; ALL_TAC] THEN
  SUBGOAL_THEN `?ns. a = MAP (\n:A word. pan_Val (Word n)) ns` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `MAP theValWord (a:((A)pan_v)list)` THEN
    REWRITE_TAC[MAP_MAP_o; o_DEF] THEN CONV_TAC SYM_CONV THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM MAP_ID] THEN REWRITE_TAC[MAP_EQ_f] THEN
    QPAT_X_ASSUM "ALL _ a" MP_TAC THEN REWRITE_TAC[EVERY_MEM] THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `w:(A)pan_v` THEN
    DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC(UNDISCH th)) THEN
    QCASES_ON "w" THEN REWRITE_TAC[case_def "pan_v"] THEN
    QCASES_ON "a'" THEN REWRITE_TAC[theValWord_def];
    ALL_TAC] THEN
  RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MAP_MAP_o; o_DEF; case_def "pan_v"; case_def "word_lab"]) THEN
  ASM_REWRITE_TAC[MAP_MAP_o; o_DEF; v2word_def; case_def "option"; case_def "word_lab";
    ALL_T; MAP_ID; ETA_AX; OPTION_MAP_DEF; ONE; CONS_11] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MAP_ID]) THEN
  ASM_REWRITE_TAC[EVERY_MAP; case_def "word_lab"; ALL_T; OPTION_MAP_DEF];
  (* Panop *)
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RFS[pan_eval_def; option_case_eq; localised_exp_simps] THEN
  RVEQ_TAC THEN RFS[pan_to_crep_compile_exp_def; cexp_heads_eq; cexp_heads_simp_def] THEN
  SUBGOAL_THEN
   `~MEM [] (MAP FST (MAP (pan_to_crep_compile_exp (ct:(A)pan_to_crep_context))
                       (es:((A)panLang_exp)list))) /\
    MAP (crep_eval (t:(A,B)crep_state))
      (MAP HD (MAP FST (MAP (pan_to_crep_compile_exp ct) es))) =
    MAP SOME (MAP v2word (a:((A)pan_v)list))`
   STRIP_ASSUME_TAC THENL
   [QPAT_X_ASSUM "ALL localised_exp es" MP_TAC THEN
    QPAT_X_ASSUM "ALL _ a" MP_TAC THEN
    QPAT_X_ASSUM "OPT_MMAP _ es = SOME a" MP_TAC THEN
    QPAT_X_ASSUM "!y. MEM y es ==> _" MP_TAC THEN
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
      free_in `es:((A)panLang_exp)list` (concl th) ||
      free_in `a:((A)pan_v)list` (concl th)))) THEN
    SPEC_TAC(`a:((A)pan_v)list`,`a:((A)pan_v)list`) THEN
    SPEC_TAC(`es:((A)panLang_exp)list`,`es:((A)panLang_exp)list`) THEN
    LIST_INDUCT_TAC THEN GEN_TAC THEN REWRITE_TAC[OPT_MMAP_def] THENL
    [REPEAT STRIP_TAC THEN GVS[MAP; MEM]; ALL_TAC] THEN
    REWRITE_TAC[MEM; ALL; TAUT `(a \/ b ==> c) <=> (a ==> c) /\ (b ==> c)`;
                FORALL_AND_THM; FORALL_UNWIND_THM2; OPTION_BIND_EQUALS_OPTION;
                option_INJ] THEN
    REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN RVEQ_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ALL]) THEN FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x':((A)pan_v)list`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN
    QCASES_ON "x" THEN FS[case_def "pan_v"] THEN QCASES_ON "a" THEN
    FS[case_def "word_lab"] THEN
    FIRST_X_ASSUM (MP_TAC o SPECL
      [`pan_Val (Word a'):(A)pan_v`; `t:(A,B)crep_state`; `ct:(A)pan_to_crep_context`;
       `FST (pan_to_crep_compile_exp (ct:(A)pan_to_crep_context) (h:(A)panLang_exp))`;
       `SND (pan_to_crep_compile_exp (ct:(A)pan_to_crep_context) (h:(A)panLang_exp))`]) THEN
    ASM_REWRITE_TAC[flatten_def; MAP; MAP_EQ_SING] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[HD; NOT_CONS_NIL; v2word_def];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) && is_pair(rhs(concl th)))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o REWRITE_RULE[case_def "option"; PAIR_EQ]) THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[MAP; flatten_def; shape_of_def; size_of_shape_def; is_wf_shape_def; LENGTH] THEN
  REWRITE_TAC[crep_eval_def] THEN
  SUBGOAL_THEN `OPT_MMAP (crep_eval (t:(A,B)crep_state))
                  (MAP HD (MAP FST (MAP (pan_to_crep_compile_exp (ct:(A)pan_to_crep_context))
                    (es:((A)panLang_exp)list)))) =
                SOME (MAP v2word (a:((A)pan_v)list))` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[opt_mmap_eq_some]; ALL_TAC] THEN
  SUBGOAL_THEN `?ns. a = MAP (\n:A word. pan_Val (Word n)) ns` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `MAP theValWord (a:((A)pan_v)list)` THEN
    REWRITE_TAC[MAP_MAP_o; o_DEF] THEN CONV_TAC SYM_CONV THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM MAP_ID] THEN REWRITE_TAC[MAP_EQ_f] THEN
    QPAT_X_ASSUM "ALL _ a" MP_TAC THEN REWRITE_TAC[EVERY_MEM] THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `w:(A)pan_v` THEN
    DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC(UNDISCH th)) THEN
    QCASES_ON "w" THEN REWRITE_TAC[case_def "pan_v"] THEN
    QCASES_ON "a'" THEN REWRITE_TAC[theValWord_def];
    ALL_TAC] THEN
  RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MAP_MAP_o; o_DEF; case_def "pan_v"; case_def "word_lab"]) THEN
  ASM_REWRITE_TAC[MAP_MAP_o; o_DEF; v2word_def; case_def "option"; case_def "word_lab";
    ALL_T; MAP_ID; ETA_AX; OPTION_MAP_DEF; ONE; CONS_11] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MAP_ID])
  THEN
  SUBGOAL_THEN `crep_op (compile_panop op) (ns:(A word)list) = pan_op op ns` SUBST1_TAC THENL
   [QCASES_ON "op" THEN
    REWRITE_TAC[compile_panop_def; ONELINE crep_op_def; ONELINE pan_op_def;
                case_def "crepop"; case_def "panop"];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[EVERY_MAP; case_def "word_lab"; ALL_T; OPTION_MAP_DEF];
  (* Cmp *)
  POP_ASSUM(CONJUNCTS_THEN ASSUME_TAC) THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[localised_exp_simps]) THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)) THEN
  GVS_ASM(pan_eval_def :: all_case_eqs()) THEN
  MAP_EVERY (fun ex -> FIRST_X_ASSUM(MP_TAC o SPECL
     [`t:(A,B)crep_state`; `ct:(A)pan_to_crep_context`;
      mk_comb(`FST:((A)crep_exp)list#shape->((A)crep_exp)list`,
              mk_comb(`pan_to_crep_compile_exp (ct:(A)pan_to_crep_context):
                         (A)panLang_exp->((A)crep_exp)list#shape`, ex));
      mk_comb(`SND:((A)crep_exp)list#shape->shape`,
              mk_comb(`pan_to_crep_compile_exp (ct:(A)pan_to_crep_context):
                         (A)panLang_exp->((A)crep_exp)list#shape`, ex))]) THEN
     ASM_REWRITE_TAC[flatten_def; MAP; MAP_EQ_SING] THEN STRIP_TAC)
    [`e1:(A)panLang_exp`; `e2:(A)panLang_exp`] THEN
  QPAT_X_ASSUM "pan_to_crep_compile_exp ct (Cmp cmp e1 e2) = _" MP_TAC THEN
  ASM_REWRITE_TAC[pan_to_crep_compile_exp_def; LET_DEF; LET_END_DEF; case_def "list";
                  PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  ASM_REWRITE_TAC[MAP; crep_eval_def; case_def "option"; case_def "word_lab"; flatten_def;
    shape_of_def; size_of_shape_def; is_wf_shape_def; LENGTH; ONE; v2w_sing] THEN
  QPAT_X_ASSUM "SOME _ = crep_eval t x0" (ASSUME_TAC o SYM) THEN
  QPAT_X_ASSUM "SOME _ = crep_eval t x0'" (ASSUME_TAC o SYM) THEN
  ASM_REWRITE_TAC[CONS_11; UNWIND_THM1; crep_eval_def; case_def "option"; case_def "word_lab";
                  v2w_sing; ONE];
  (* Shift *)
  POP_ASSUM(CONJUNCTS_THEN ASSUME_TAC) THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[localised_exp_simps]) THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)) THEN
  GVS_ASM(pan_eval_def :: OPTION_MAP_EQ_SOME :: all_case_eqs()) THEN
  MAP_EVERY (fun ex -> FIRST_X_ASSUM(MP_TAC o SPECL
     [`t:(A,B)crep_state`; `ct:(A)pan_to_crep_context`;
      mk_comb(`FST:((A)crep_exp)list#shape->((A)crep_exp)list`,
              mk_comb(`pan_to_crep_compile_exp (ct:(A)pan_to_crep_context):
                         (A)panLang_exp->((A)crep_exp)list#shape`, ex));
      mk_comb(`SND:((A)crep_exp)list#shape->shape`,
              mk_comb(`pan_to_crep_compile_exp (ct:(A)pan_to_crep_context):
                         (A)panLang_exp->((A)crep_exp)list#shape`, ex))]) THEN
     ASM_REWRITE_TAC[flatten_def; MAP; MAP_EQ_SING] THEN STRIP_TAC)
    [`e1:(A)panLang_exp`; `e2:(A)panLang_exp`] THEN
  QPAT_X_ASSUM "pan_to_crep_compile_exp ct (panLang_Shift _ e1 e2) = _" MP_TAC THEN
  ASM_REWRITE_TAC[pan_to_crep_compile_exp_def; LET_DEF; LET_END_DEF; case_def "list";
                  PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  ASM_REWRITE_TAC[MAP; crep_eval_def; case_def "option"; case_def "word_lab"; flatten_def;
    shape_of_def; size_of_shape_def; is_wf_shape_def; LENGTH; ONE] THEN
  QPAT_X_ASSUM "SOME _ = crep_eval t x0" (ASSUME_TAC o SYM) THEN
  QPAT_X_ASSUM "SOME _ = crep_eval t x0'" (ASSUME_TAC o SYM) THEN
  ASM_REWRITE_TAC[CONS_11; UNWIND_THM1; crep_eval_def; case_def "option"; case_def "word_lab";
                  OPTION_MAP_DEF; ONE];
  (* BaseAddr, TopAddr, BytesInWord *)
  GVS[pan_eval_def; pan_to_crep_compile_exp_def] THEN
  GVS[flatten_def; crep_eval_def; size_of_shape_def; shape_of_def; is_wf_shape_def;
      pan_to_crepProof_state_rel_def];
  (* BaseAddr, TopAddr, BytesInWord *)
  GVS[pan_eval_def; pan_to_crep_compile_exp_def] THEN
  GVS[flatten_def; crep_eval_def; size_of_shape_def; shape_of_def; is_wf_shape_def;
      pan_to_crepProof_state_rel_def];
  (* BaseAddr, TopAddr, BytesInWord *)
  GVS[pan_eval_def; pan_to_crep_compile_exp_def] THEN
  GVS[flatten_def; crep_eval_def; size_of_shape_def; shape_of_def; is_wf_shape_def;
      pan_to_crepProof_state_rel_def]
  ]);;

let mem_comp_field_lem = prove
 (`!i l (es:((A)crep_exp)list) x.
     MEM x (FST (comp_field i l es)) ==> MEM x es \/ x = crep_Const (word 0)`,
  QINDUCT_ON "l" THEN REWRITE_TAC[comp_field_def; MEM] THEN
  REPEAT GEN_TAC THEN TRY (DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
  DISCH_TAC THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THENL
   [MESON_TAC[MEM_TAKE];
    DISCH_THEN(fun th -> FIRST_X_ASSUM(DISJ_CASES_TAC o C MATCH_MP th)) THEN
    ASM_MESON_TAC[MEM_DROP_IMP]]);;

(* the case of panLang_Op and Panop: a variable of an argument's head    *)

let PP2CAUX_MEM_VMAX_OP_TAC : tactic =
  QPAT_X_ASSUM "cexp_heads _ = SOME _"
    (MP_TAC o REWRITE_RULE[cexp_heads_eq; cexp_heads_simp_def]) THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_INJ; option_DISTINCT] THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MAP_MAP_o; o_DEF]) THEN
  QPAT_X_ASSUM "MEM x (MAP _ _)" (STRIP_ASSUME_TAC o REWRITE_RULE[MEM_MAP]) THEN
  RVEQ_TAC THEN
  QPAT_X_ASSUM "~MEM [] _" (MP_TAC o REWRITE_RULE[MEM_MAP]) THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN DISCH_THEN(MP_TAC o SPEC `x':(A)panLang_exp`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x':(A)panLang_exp`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  EXISTS_TAC `HD (FST (pan_to_crep_compile_exp (ctxt:(B)pan_to_crep_context)
                         (x':(A)panLang_exp)))` THEN
  ASM_REWRITE_TAC[] THEN
  QPAT_X_ASSUM "~([] = _)" MP_TAC THEN
  SPEC_TAC(`FST (pan_to_crep_compile_exp (ctxt:(B)pan_to_crep_context)
                   (x':(A)panLang_exp))`,`l:((A)crep_exp)list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[HD; MEM];;

let MEM_compile_exp_vmax = prove
 (`!ctxt (exp:(A)panLang_exp) n (e:(A)crep_exp).
     pan_commonProps_ctxt_max (pan_to_crep_context_vmax (ctxt:(B)pan_to_crep_context))
       (pan_to_crep_context_vars ctxt) /\
     MEM n (var_cexp e) /\
     MEM e (FST (pan_to_crep_compile_exp ctxt exp)) ==>
     n <= pan_to_crep_context_vmax ctxt`,
  REC_IND_TAC pan_to_crep_compile_exp_ind THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
  FS[pan_to_crep_compile_exp_def] THEN EVERY_CASE_TAC THEN
  GVS[var_cexp_def; MEM; MEM_MAP; MEM_FLAT] THEN RES_TAC THEN FS[] THENL
   [(* Var Local *)
    RULE_ASSUM_TAC(REWRITE_RULE[pan_commonProps_ctxt_max_def]) THEN ASM_MESON_TAC[];
    (* RField *)
    FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP mem_comp_field_lem) THEN GVS[var_cexp_def; MEM];
    (* Load *)
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP var_exp_load_shape) THEN RFS[] THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (is_forall o concl)) THEN
    EXISTS_TAC `a0:(A)crep_exp` THEN ASM_REWRITE_TAC[];
    (* Op *)
    PP2CAUX_MEM_VMAX_OP_TAC;
    (* Panop *)
    PP2CAUX_MEM_VMAX_OP_TAC]);;

let globals_lookup_def = cake_def
  `globals_lookup (t:(A,B)crep_state) (v:(A)pan_v) =
     OPT_MMAP (FLOOKUP (crep_state_globals t))
       (list_of_seq (\x. word x) (size_of_shape (shape_of v)))`;;

(* pc_compile_correct (HOL4 proves it case by case with suspend/Resume):  *)
(* PP2CAUX_pc_stmt is its statement; PP2CAUX_pc_cases are the cases of    *)
(* the induction with pan_evaluate_ind, in that theorem's order, each      *)
(* proved below as PP2CAUX_pc_NAME (NAME the HOL4 Resume label) before    *)
(* pc_compile_correct itself, where HOL4 has Finalise.                     *)

let PP2CAUX_pc_stmt = CASE_TERM
 `!(v:(A)panLang_prog) (v1:(A,B)pan_state) res s1 (t:(A,B)crep_state)
   (ctxt:(A)pan_to_crep_context).
    pan_evaluate (v,v1) = (res,s1) /\ ~(res = SOME pan_Error) /\
    pan_to_crepProof_state_rel v1 t /\
    pan_to_crepProof_code_rel ctxt (pan_state_code v1) (crep_state_code t) /\
    excp_rel (pan_to_crep_context_eids ctxt) (pan_state_eshapes v1) /\
    pan_to_crepProof_locals_rel ctxt (pan_state_locals v1) (crep_state_locals t) /\
    localised_prog v ==>
    ?res1 t1.
      crep_evaluate (pan_to_crep_compile ctxt v,t) = (res1,t1) /\
      pan_to_crepProof_state_rel s1 t1 /\
      pan_to_crepProof_code_rel ctxt (pan_state_code s1) (crep_state_code t1) /\
      excp_rel (pan_to_crep_context_eids ctxt) (pan_state_eshapes s1) /\
      (match res with
         NONE -> res1 = NONE /\
                 pan_to_crepProof_locals_rel ctxt (pan_state_locals s1)
                   (crep_state_locals t1)
       | SOME pan_Error -> F
       | SOME pan_TimeOut -> res1 = SOME crep_TimeOut
       | SOME pan_Break ->
           res1 = SOME (crepSem_Break 0) /\
           pan_to_crepProof_locals_rel ctxt (pan_state_locals s1)
             (crep_state_locals t1)
       | SOME pan_Continue ->
           res1 = SOME (crepSem_Continue 0) /\
           pan_to_crepProof_locals_rel ctxt (pan_state_locals s1)
             (crep_state_locals t1)
       | SOME (pan_Return v) -> res1 = SOME (crepSem_Return (flatten v))
       | SOME (pan_Exception eid v') ->
           (match FLOOKUP (pan_to_crep_context_eids ctxt) eid with
              NONE -> F
            | SOME n ->
                res1 = SOME (crep_Exception n) /\
                (1 <= size_of_shape (shape_of v') ==>
                 globals_lookup t1 v' = SOME (flatten v') /\
                 size_of_shape (shape_of v') <= 32))
       | SOME (pan_FinalFFI f) -> res1 = SOME (crep_FinalFFI f))`;;

let PP2CAUX_pc_cases =
  let _,gls,_ = (REC_IND_TAC pan_evaluate_ind THEN REPEAT CONJ_TAC) ([],PP2CAUX_pc_stmt) in
  if exists (fun (asl,_) -> asl <> []) gls then failwith "PP2CAUX_pc_cases" else
  map snd gls;;

let PP2CAUX_PC_TRIVIAL_TAC : tactic =
  REPEAT STRIP_TAC THEN
  FS[pan_evaluate_def; crep_evaluate_def; pan_to_crep_compile_def; localised_prog_def] THEN
  RVEQ_TAC THEN FS[];;

(* HOL4: Resume pc_compile_correct[Skip], [Break], [Continue], [Annot], [Tick] *)

let PP2CAUX_pc_Skip = prove(el 0 PP2CAUX_pc_cases, PP2CAUX_PC_TRIVIAL_TAC);;

let PP2CAUX_pc_Break = prove(el 11 PP2CAUX_pc_cases, PP2CAUX_PC_TRIVIAL_TAC);;

let PP2CAUX_pc_Continue = prove(el 12 PP2CAUX_pc_cases, PP2CAUX_PC_TRIVIAL_TAC);;

let PP2CAUX_pc_Annot = prove(el 17 PP2CAUX_pc_cases, PP2CAUX_PC_TRIVIAL_TAC);;

let PP2CAUX_pc_Tick = prove
 (el 16 PP2CAUX_pc_cases,
  REPEAT STRIP_TAC THEN
  FS[pan_evaluate_def; crep_evaluate_def; pan_to_crep_compile_def] THEN RVEQ_TAC THEN
  FS[] THEN EVERY_CASE_TAC THEN
  FS[pan_empty_locals_def; crep_empty_locals_def; pan_dec_clock_def; crep_dec_clock_def] THEN
  RVEQ_TAC THEN FS[pan_to_crepProof_state_rel_def]);;

let locals_rel_lookup_ctxt = prove
 (`pan_to_crepProof_locals_rel (ctxt:(B)pan_to_crep_context)
     (lcl:(mlstring,(A)pan_v)fmap) lcl' /\
   FLOOKUP lcl vr = SOME v ==>
   ?ns. FLOOKUP (pan_to_crep_context_vars ctxt) vr = SOME (shape_of v,ns) /\
        LENGTH ns = LENGTH (flatten v) /\
        OPT_MMAP (FLOOKUP lcl') ns = SOME (flatten v) /\
        is_wf_shape ([]:(mlstring#struct_info)list) (shape_of v)`,
  RW[pan_to_crepProof_locals_rel_def] THEN ASM_MESON_TAC[opt_mmap_length_eq]);;

let eval_nested_assign_distinct_eq = prove
 (`!es ns (t:(A,B)crep_state) ev vs.
     MAP (crep_eval t) es = MAP SOME ev /\
     OPT_MMAP (FLOOKUP (crep_state_locals t)) ns = SOME vs /\
     distinct_lists ns (FLAT (MAP var_cexp es)) /\
     ALL_DISTINCT ns /\
     LENGTH ns = LENGTH es ==>
     crep_evaluate (crep_nested_seq (MAP2 crep_Assign ns es),t) =
       (NONE,crep_state_locals_fupd (K (crep_state_locals t |++ ZIP ns ev)) t)`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN QCASES_ON "ns" THEN
  FS[LENGTH; NOT_SUC; MAP2; crep_nested_seq_def] THEN RVEQ_TAC THENL
   [SIMP[crep_evaluate_def; FUPDATE_LIST_THM; RECORD_SELFID_ss]; ALL_TAC] THEN
  QPAT_X_ASSUM "CONS _ _ = MAP SOME ev"
    (STRIP_ASSUME_TAC o REWRITE_RULE[MAP_EQ_CONS] o SYM) THEN
  RVEQ_TAC THEN
  SUBGOAL_THEN `~MEM (a0:num) (FLAT (MAP var_cexp (t:((A)crep_exp)list)))` ASSUME_TAC THENL
   [QPAT_X_ASSUM "distinct_lists _ _" MP_TAC THEN
    SIMP[distinct_lists_def; ALL; MEM_APPEND; DE_MORGAN_THM];
    ALL_TAC] THEN
  QPAT_ASSUM "distinct_lists _ _"
    (ASSUME_TAC o MATCH_MP distinct_lists_cons o ONCE_REWRITE_RULE[CONS_APPEND]) THEN
  ONCE_REWRITE_TAC[crep_evaluate_def] THEN ONCE_REWRITE_TAC[crep_evaluate_def] THEN
  ASM_REWRITE_TAC[case_def "option"; case_def "prod"] THEN
  SUBGOAL_THEN
   `MAP (crep_eval (crep_state_locals_fupd (K (crep_state_locals t' |+ (a0,x0)))
                      (t':(A,B)crep_state))) t =
    MAP SOME (t0:((A)word_lab)list)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
      rand(lhs(concl th)) = `t:((A)crep_exp)list`)) THEN
    REWRITE_TAC[MAP_EQ_f] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC update_locals_not_vars_eval_eq' THEN
    QPAT_X_ASSUM "~MEM a0 (FLAT _)" MP_TAC THEN
    REWRITE_TAC[MEM_FLAT; MEM_MAP] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun ih -> MP_TAC(ISPECL [`a1:num list`;
    `crep_state_locals_fupd (K (crep_state_locals t' |+ (a0,x0))) (t':(A,B)crep_state)`;
    `t0:((A)word_lab)list`; `x:((A)word_lab)list`] ih)) THEN
  ANTS_TAC THENL
   [SIMP[] THEN MATCH_MP_TAC opt_mmap_flookup_update THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC THEN SIMP[ZIP; FUPDATE_LIST_THM]]);;

(* the restoring res_var of a crep_Dec commutes with those of later         *)
(* variables (HOL4: the inner induction of eval_nested_decs_seq_res_var_eq) *)

let PP2CAUX_res_var_foldl_commutes = prove
 (`!ns (l:(num,V)fmap) lc n.
     ~MEM n ns ==>
     crep_res_var (FOLDL crep_res_var l (ZIP ns (MAP (FLOOKUP lc) ns))) (n,FLOOKUP lc n) =
     FOLDL crep_res_var (crep_res_var l (n,FLOOKUP lc n)) (ZIP ns (MAP (FLOOKUP lc) ns))`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; ZIP; FOLDL; MEM; DE_MORGAN_THM] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC res_var_commutes THEN ASM_MESON_TAC[]);;

let eval_nested_decs_seq_res_var_eq = prove
 (CASE_TERM `!es ns (t:(A,B)crep_state) ev (p:(A)crep_prog).
   MAP (crep_eval t) es = MAP SOME ev /\
   LENGTH ns = LENGTH es /\
   distinct_lists ns (FLAT (MAP var_cexp es)) /\
   ALL_DISTINCT ns ==>
   let (q,r) = crep_evaluate
                 (p,crep_state_locals_fupd (K (crep_state_locals t |++ ZIP ns ev)) t) in
   crep_evaluate (nested_decs ns es p,t) =
   (q,crep_state_locals_fupd
        (K (FOLDL crep_res_var (crep_state_locals r)
              (ZIP ns (MAP (FLOOKUP (crep_state_locals t)) ns)))) r)`,
  MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN QCASES_ON "ns" THEN REWRITE_TAC[LENGTH; NOT_SUC] THEN
    REWRITE_TAC[MAP; ZIP; FUPDATE_LIST_THM; FOLDL; nested_decs_def; list_MAP_EQ_NIL] THEN
    STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[ZIP; FUPDATE_LIST_THM] THEN
    SIMP[RECORD_SELFID_ss] THEN PAIRARG_TAC THEN SIMP[RECORD_SELFID_ss];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`e:(A)crep_exp`; `es:((A)crep_exp)list`] THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN QCASES_ON "ns" THEN REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ] THEN
  REWRITE_TAC[MAP; FLAT; ALL_DISTINCT] THEN STRIP_TAC THEN
  QPAT_X_ASSUM "CONS _ _ = MAP SOME ev"
    (STRIP_ASSUME_TAC o REWRITE_RULE[MAP_EQ_CONS] o SYM) THEN
  RVEQ_TAC THEN
  SUBGOAL_THEN `~MEM (a0:num) (FLAT (MAP var_cexp (es:((A)crep_exp)list)))` ASSUME_TAC THENL
   [QPAT_X_ASSUM "distinct_lists _ _" MP_TAC THEN
    SIMP[distinct_lists_def; ALL; MEM_APPEND; DE_MORGAN_THM];
    ALL_TAC] THEN
  QPAT_ASSUM "distinct_lists _ _"
    (ASSUME_TAC o MATCH_MP distinct_lists_cons o ONCE_REWRITE_RULE[CONS_APPEND]) THEN
  SUBGOAL_THEN
   `MAP (crep_eval (crep_state_locals_fupd (K (crep_state_locals t |+ (a0,x0)))
                      (t:(A,B)crep_state))) es =
    MAP SOME (t0:((A)word_lab)list)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
      rand(lhs(concl th)) = `es:((A)crep_exp)list`)) THEN
    REWRITE_TAC[MAP_EQ_f] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC update_locals_not_vars_eval_eq' THEN
    QPAT_X_ASSUM "~MEM a0 (FLAT _)" MP_TAC THEN
    REWRITE_TAC[MEM_FLAT; MEM_MAP] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun ih -> MP_TAC(ISPECL [`a1:num list`;
    `crep_state_locals_fupd (K (crep_state_locals t |+ (a0,x0))) (t:(A,B)crep_state)`;
    `t0:((A)word_lab)list`; `p:(A)crep_prog`] ih)) THEN
  ASM_REWRITE_TAC[] THEN SIMP[ZIP; FUPDATE_LIST_THM] THEN
  W(fun (_,w) -> PAIR_CASES_ON (rand(rator(lhand w)))) THEN
  ASM_REWRITE_TAC[case_def "prod"] THEN DISCH_TAC THEN
  REWRITE_TAC[nested_decs_def] THEN ONCE_REWRITE_TAC[crep_evaluate_def] THEN
  ASM_REWRITE_TAC[case_def "option"; case_def "prod"] THEN
  SUBGOAL_THEN `MAP (FLOOKUP (crep_state_locals t |+ (a0,x0))) a1 =
                MAP (FLOOKUP (crep_state_locals (t:(A,B)crep_state))) a1` SUBST1_TAC THENL
   [REWRITE_TAC[MAP_EQ_f; FLOOKUP_UPDATE] THEN REPEAT STRIP_TAC THEN
    COND_CASES_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SIMP[PP2CAUX_res_var_foldl_commutes]);;

let mem_comp_field = prove
 (`!sh i (e:((A)crep_exp)list) shp ce es (vs:((A)pan_v)list).
     i < LENGTH vs /\
     LENGTH e = size_of_shape (shape_of (pan_RStruct vs)) /\
     comp_field i sh e = (es,shp) /\
     Comb sh = shape_of (pan_RStruct vs) /\
     MEM ce es ==> MEM ce e`,
  QINDUCT_ON "sh" THEN REWRITE_TAC[comp_field_def; shape_of_def; injectivity "shape"] THEN
  REPEAT GEN_TAC THENL
   [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[list_MAP_EQ_NIL] o SYM o
      check (fun th -> is_eq (concl th) && is_const (lhs (concl th)))) THEN
    DISCH_THEN SUBST_ALL_TAC THEN FS[LENGTH; LT];
    ALL_TAC] THEN
  DISCH_TAC THEN REPEAT GEN_TAC THEN NAMED_CASES_ON "vs" ["";"v vs'"] THEN
  REWRITE_TAC[MAP; NOT_CONS_NIL; CONS_11; LENGTH] THEN STRIP_TAC THEN RVEQ_TAC THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THENL
   [MESON_TAC[MEM_TAKE]; ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC MEM_DROP_IMP THEN
  EXISTS_TAC `size_of_shape (shape_of (v:(A)pan_v))` THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`i - 1`; `shp:shape`; `es:((A)crep_exp)list`; `vs':((A)pan_v)list`] THEN
  ASM_REWRITE_TAC[LENGTH_DROP] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[size_of_shape_def; MAP; SUM]) THEN
  REWRITE_TAC[size_of_shape_def; MAP; SUM] THEN ASM_ARITH_TAC);;

(* HOL4 proves eval_var_cexp_present_ctxt by induction on eval; the        *)
(* evaluation is not needed: every variable of a compiled expression is one *)
(* of the context (the same induction as MEM_compile_exp_vmax)             *)

let PP2CAUX_compile_exp_vars = prove
 (`!ctxt (exp:(A)panLang_exp) n (e:(A)crep_exp).
     MEM n (var_cexp e) /\
     MEM e (FST (pan_to_crep_compile_exp (ctxt:(B)pan_to_crep_context) exp)) ==>
     ?v shp ns. FLOOKUP (pan_to_crep_context_vars ctxt) v = SOME (shp,ns) /\ MEM n ns`,
  REC_IND_TAC pan_to_crep_compile_exp_ind THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
  FS[pan_to_crep_compile_exp_def] THEN EVERY_CASE_TAC THEN
  GVS[var_cexp_def; MEM; MEM_MAP; MEM_FLAT] THEN RES_TAC THEN FS[] THEN
  TRY(ASM_EXISTS_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC) THENL
   [(* RField *)
    FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP mem_comp_field_lem) THEN
    GVS[var_cexp_def; MEM] THEN ASM_EXISTS_TAC THEN ASM_REWRITE_TAC[];
    (* Load *)
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP var_exp_load_shape) THEN RFS[] THEN
    TRY(ASM_EXISTS_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (is_forall o concl)) THEN
    EXISTS_TAC `a0:(A)crep_exp` THEN ASM_REWRITE_TAC[];
    (* Op *)
    PP2CAUX_MEM_VMAX_OP_TAC;
    (* Panop *)
    PP2CAUX_MEM_VMAX_OP_TAC]);;

let eval_var_cexp_present_ctxt = prove
 (`!(s:(A,B)pan_state) e v (t:(A,B)crep_state) ct es sh.
     pan_to_crepProof_state_rel s t /\
     pan_eval s e = SOME v /\
     pan_to_crepProof_code_rel ct (pan_state_code s) (crep_state_code t) /\
     pan_to_crepProof_locals_rel ct (pan_state_locals s) (crep_state_locals t) /\
     localised_exp e /\
     pan_to_crep_compile_exp ct e = (es,sh) ==>
     (!n. MEM n (FLAT (MAP var_cexp es)) ==>
          ?v shp ns. FLOOKUP (pan_to_crep_context_vars ct) v = SOME (shp,ns) /\
                     MEM n ns)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
  REWRITE_TAC[MEM_FLAT; MEM_MAP] THEN STRIP_TAC THEN RVEQ_TAC THEN
  MATCH_MP_TAC PP2CAUX_compile_exp_vars THEN
  MAP_EVERY EXISTS_TAC [`e:(A)panLang_exp`; `x:(A)crep_exp`] THEN ASM_REWRITE_TAC[FST]);;

(* locals_rel only looks at the target locals of the context's variables *)

let PP2CAUX_locals_rel_agree = prove
 (`!ctxt (sl:(mlstring,(A)pan_v)fmap) (tl:(num,(A)word_lab)fmap) tl'.
     pan_to_crepProof_locals_rel (ctxt:(B)pan_to_crep_context) sl tl /\
     (!v sh ns n. FLOOKUP (pan_to_crep_context_vars ctxt) v = SOME (sh,ns) /\ MEM n ns
                  ==> FLOOKUP tl' n = FLOOKUP tl n) ==>
     pan_to_crepProof_locals_rel ctxt sl tl'`,
  REWRITE_TAC[pan_to_crepProof_locals_rel_def] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP th o
    check (is_eq o concl))) THEN
  MAP_EVERY EXISTS_TAC [`ns:num list`; `vs:((A)word_lab)list`] THEN
  ASM_REWRITE_TAC[] THEN
  QPAT_X_ASSUM "OPT_MMAP (FLOOKUP tl) ns = SOME vs" (SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC OPT_MMAP_CONG THEN REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* assigning a source variable its new value: the target variables of its *)
(* context entry get the flattened value                                   *)

let PP2CAUX_locals_rel_update = prove
 (`!ctxt (sl:(mlstring,(A)pan_v)fmap) (tl:(num,(A)word_lab)fmap) vr v ev ns.
     pan_to_crepProof_locals_rel (ctxt:(B)pan_to_crep_context) sl tl /\
     FLOOKUP sl vr = SOME v /\
     FLOOKUP (pan_to_crep_context_vars ctxt) vr = SOME (shape_of v,ns) /\
     shape_of ev = shape_of v /\
     is_wf_shape ([]:(mlstring#struct_info)list) (shape_of ev) ==>
     pan_to_crepProof_locals_rel ctxt (sl |+ (vr,ev)) (tl |++ ZIP ns (flatten ev))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP locals_rel_lookup_ctxt o
    CONJ (ASSUME `pan_to_crepProof_locals_rel (ctxt:(B)pan_to_crep_context)
                    (sl:(mlstring,(A)pan_v)fmap) (tl:(num,(A)word_lab)fmap)`)) THEN
  ASM_REWRITE_TAC[injectivity "option"; PAIR_EQ] THEN
  DISCH_THEN(X_CHOOSE_THEN `ns':num list` STRIP_ASSUME_TAC) THEN RVEQ_TAC THEN
  SUBGOAL_THEN `LENGTH (ns':num list) = LENGTH (flatten (ev:(A)pan_v))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[length_flatten_eq_size_of_shape]; ALL_TAC] THEN
  QPAT_X_ASSUM "pan_to_crepProof_locals_rel _ _ _"
    (STRIP_ASSUME_TAC o REWRITE_RULE[pan_to_crepProof_locals_rel_def]) THEN
  SUBGOAL_THEN `ALL_DISTINCT (ns':num list)` ASSUME_TAC THENL
   [ASM_MESON_TAC[all_distinct_flookup_all_distinct]; ALL_TAC] THEN
  ASM_REWRITE_TAC[pan_to_crepProof_locals_rel_def; FLOOKUP_UPDATE] THEN
  MAP_EVERY X_GEN_TAC [`vname:mlstring`; `v':(A)pan_v`] THEN
  COND_CASES_TAC THENL
   [REWRITE_TAC[injectivity "option"] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    RVEQ_TAC THEN
    MAP_EVERY EXISTS_TAC [`ns':num list`; `flatten (ev:(A)pan_v)`] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC opt_mmap_some_eq_zip_flookup THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o C MATCH_MP
      (ASSUME `FLOOKUP (sl:(mlstring,(A)pan_v)fmap) vname = SOME v'`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `ms:num list` (X_CHOOSE_THEN `vs:((A)word_lab)list`
      STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`ms:num list`; `vs:((A)word_lab)list`] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `distinct_lists (ns':num list) ms` ASSUME_TAC THENL
     [ASM_MESON_TAC[no_overlap_flookup_distinct]; ALL_TAC] THEN
    QPAT_X_ASSUM "OPT_MMAP (FLOOKUP tl) ms = SOME vs" (SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC opt_mmap_disj_zip_flookup THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC]);;

let PP2CAUX_flookup_temps = prove
 (`!temps a c (f:(num,V)fmap) l k.
     ~MEM k temps /\ LENGTH temps = LENGTH a /\ LENGTH temps = LENGTH c ==>
     FLOOKUP (FOLDL crep_res_var ((f |++ ZIP temps a) |++ l) (ZIP temps c)) k =
     FLOOKUP (f |++ l) k`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC EQ_TRANS `FLOOKUP (((f:(num,V)fmap) |++ ZIP temps (a:V list)) |++ l) k` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC flookup_res_var_distinct_zip_eq THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC[FLOOKUP_FUPDATE_LIST] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[GSYM FLOOKUP_FUPDATE_LIST] THEN
    MATCH_MP_TAC flookup_fupdate_zip_not_mem THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC]);;

(* genlist_distinct_max with the temporaries as the compiler writes them *)

let PP2CAUX_genlist_distinct_max = prove
 (`!n ys m. (!y. MEM y ys ==> y <= m)
            ==> distinct_lists (list_of_seq (\x. m + SUC x) n) ys`,
  ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[genlist_distinct_max]);;

(* HOL4: Resume pc_compile_correct[Assign] *)

let PP2CAUX_pc_Assign = prove
 (el 2 PP2CAUX_pc_cases,
  REPEAT GEN_TAC THEN STRIP_TAC THEN QCASES_ON "vk" THEN
  FS[localised_prog_def] THEN
  QPAT_X_ASSUM "pan_evaluate _ = _" MP_TAC THEN
  REWRITE_TAC[pan_evaluate_def] THEN
  GVS[is_valid_value_simps; pan_set_kvar_def; option_case_eq; COND_CASE_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  QCASES_ON "FLOOKUP (pan_state_locals s) v" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[case_def "option"]) THEN ASM_REWRITE_TAC[] THEN
  TRY (FIRST_ASSUM CONTR_TAC) THEN
  RENAME_TAC ["pan_eval s src = SOME ev"; "FLOOKUP (pan_state_locals s) v = SOME w"] THEN
  DRULE locals_rel_lookup_ctxt THEN DISCH_THEN DRULE_ALL THEN
  DISCH_THEN(X_CHOOSE_THEN `ns:num list` STRIP_ASSUME_TAC) THEN
  PAIR_CASES_ON `pan_to_crep_compile_exp (ctxt:(A)pan_to_crep_context) (src:(A)panLang_exp)` THEN
  MP_TAC(ISPECL [`s:(A,B)pan_state`; `src:(A)panLang_exp`; `ev:(A)pan_v`; `t:(A,B)crep_state`;
                 `ctxt:(A)pan_to_crep_context`; `p0:((A)crep_exp)list`; `p1:shape`]
    compile_exp_val_rel) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `LENGTH (ns:num list) = LENGTH (p0:((A)crep_exp)list)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[length_flatten_eq_size_of_shape]; ALL_TAC] THEN
  REWRITE_TAC[pan_to_crep_compile_def] THEN
  QPAT_ASSUM "pan_to_crep_compile_exp ctxt src = _" SUBST1_TAC THEN
  QPAT_ASSUM "FLOOKUP (pan_to_crep_context_vars ctxt) v = _" SUBST1_TAC THEN
  REWRITE_TAC[case_def "prod"; case_def "option"] THEN
  QPAT_ASSUM "LENGTH ns = LENGTH p0" SUBST1_TAC THEN REWRITE_TAC[] THEN
  COND_CASES_TAC THENL
   [(* the assigned variables do not occur in the expressions *)
    SUBGOAL_THEN `ALL_DISTINCT (ns:num list)` ASSUME_TAC THENL
     [ASM_MESON_TAC[all_distinct_flookup_all_distinct; pan_to_crepProof_locals_rel_def];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`p0:((A)crep_exp)list`; `ns:num list`; `t:(A,B)crep_state`;
                   `flatten (ev:(A)pan_v)`; `flatten (w:(A)pan_v)`]
      eval_nested_assign_distinct_eq) THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    MAP_EVERY EXISTS_TAC [`NONE:((A)crep_result)option`;
      `crep_state_locals_fupd (K (crep_state_locals t |++ ZIP ns (flatten (ev:(A)pan_v))))
         (t:(A,B)crep_state)`] THEN
    REWRITE_TAC[] THEN
    QPAT_X_ASSUM "pan_to_crepProof_state_rel s t" MP_TAC THEN
    QPAT_X_ASSUM "pan_to_crepProof_code_rel _ _ _" MP_TAC THEN
    QPAT_X_ASSUM "excp_rel _ _" MP_TAC THEN
    SIMP[pan_set_var_def; pan_to_crepProof_state_rel_def] THEN REPEAT DISCH_TAC THEN
    MATCH_MP_TAC PP2CAUX_locals_rel_update THEN
    EXISTS_TAC `w:(A)pan_v` THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    (* through temporaries *)
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    ABBREV_TAC `temps = list_of_seq
                          (\x. pan_to_crep_context_vmax (ctxt:(A)pan_to_crep_context) + SUC x)
                          (LENGTH (p0:((A)crep_exp)list))` THEN
    QPAT_ASSUM "pan_to_crepProof_locals_rel _ _ _"
      (STRIP_ASSUME_TAC o REWRITE_RULE[pan_to_crepProof_locals_rel_def]) THEN
    SUBGOAL_THEN `ALL_DISTINCT (ns:num list)` ASSUME_TAC THENL
     [ASM_MESON_TAC[all_distinct_flookup_all_distinct]; ALL_TAC] THEN
    SUBGOAL_THEN
      `!n. MEM n (ns:num list) ==> n <= pan_to_crep_context_vmax (ctxt:(A)pan_to_crep_context)`
      ASSUME_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[pan_commonProps_ctxt_max_def]) THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `distinct_lists temps (FLAT (MAP var_cexp (p0:((A)crep_exp)list)))`
      ASSUME_TAC THENL
     [EXPAND_TAC "temps" THEN MATCH_MP_TAC PP2CAUX_genlist_distinct_max THEN
      REWRITE_TAC[MEM_FLAT; MEM_MAP] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
      MATCH_MP_TAC MEM_compile_exp_vmax THEN
      MAP_EVERY EXISTS_TAC [`src:(A)panLang_exp`; `x:(A)crep_exp`] THEN
      ASM_REWRITE_TAC[FST];
      ALL_TAC] THEN
    SUBGOAL_THEN `ALL_DISTINCT (temps:num list) /\ LENGTH temps = LENGTH (p0:((A)crep_exp)list)`
      STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "temps" THEN REWRITE_TAC[ALL_DISTINCT_GENLIST; LENGTH_LIST_OF_SEQ] THEN
      ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `distinct_lists (temps:num list) ns` ASSUME_TAC THENL
     [EXPAND_TAC "temps" THEN MATCH_MP_TAC PP2CAUX_genlist_distinct_max THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `LENGTH (flatten (ev:(A)pan_v)) = LENGTH (p0:((A)crep_exp)list)` ASSUME_TAC THENL
     [QPAT_ASSUM "MAP (crep_eval t) p0 = _"
        (MP_TAC o AP_TERM `LENGTH:(((A)word_lab)option)list->num`) THEN
      REWRITE_TAC[LENGTH_MAP] THEN MESON_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`p0:((A)crep_exp)list`; `temps:num list`; `t:(A,B)crep_state`;
                   `flatten (ev:(A)pan_v)`;
                   `crep_nested_seq (MAP2 crep_Assign ns (MAP crep_Var temps)):(A)crep_prog`]
      eval_nested_decs_seq_res_var_eq) THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `crep_evaluate
        (crep_nested_seq (MAP2 crep_Assign ns (MAP crep_Var temps)):(A)crep_prog,
         crep_state_locals_fupd
           (K (crep_state_locals t |++ ZIP temps (flatten (ev:(A)pan_v))))
           (t:(A,B)crep_state)) =
      (NONE,crep_state_locals_fupd
              (K ((crep_state_locals t |++ ZIP temps (flatten ev)) |++ ZIP ns (flatten ev))) t)`
      SUBST1_TAC THENL
     [MP_TAC(ISPECL [`MAP crep_Var temps:((A)crep_exp)list`; `ns:num list`;
        `crep_state_locals_fupd
           (K (crep_state_locals t |++ ZIP temps (flatten (ev:(A)pan_v))))
           (t:(A,B)crep_state)`;
        `flatten (ev:(A)pan_v)`; `flatten (w:(A)pan_v)`] eval_nested_assign_distinct_eq) THEN
      SIMP[] THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[MAP_MAP_o; o_DEF; crep_eval_def] THEN SIMP[] THEN
        REWRITE_TAC[ETA_AX; GSYM opt_mmap_eq_some] THEN
        MATCH_MP_TAC opt_mmap_some_eq_zip_flookup THEN CONJ_TAC THENL
         [FIRST_ASSUM ACCEPT_TAC; ASM_REWRITE_TAC[]];
        MP_TAC(ISPECL [`temps:num list`; `crep_state_locals (t:(A,B)crep_state)`;
                       `ns:num list`; `flatten (ev:(A)pan_v)`] opt_mmap_disj_zip_flookup) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC THEN FIRST_ASSUM ACCEPT_TAC];
        REWRITE_TAC[map_var_cexp_eq_var] THEN ONCE_REWRITE_TAC[distinct_lists_commutes] THEN
        FIRST_ASSUM ACCEPT_TAC;
        MP_TAC(ISPEC `w:(A)pan_v` length_flatten_eq_size_of_shape) THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[case_def "prod"] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[PAIR_EQ; RIGHT_EXISTS_AND_THM; UNWIND_THM1; EXISTS_REFL] THEN
    QPAT_X_ASSUM "pan_to_crepProof_state_rel s t" MP_TAC THEN
    QPAT_X_ASSUM "pan_to_crepProof_code_rel _ _ _" MP_TAC THEN
    QPAT_X_ASSUM "excp_rel _ _" MP_TAC THEN
    SIMP[pan_set_var_def; pan_to_crepProof_state_rel_def] THEN REPEAT DISCH_TAC THEN
    MATCH_MP_TAC PP2CAUX_locals_rel_agree THEN
    EXISTS_TAC `crep_state_locals (t:(A,B)crep_state) |++ ZIP ns (flatten (ev:(A)pan_v))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PP2CAUX_locals_rel_update THEN EXISTS_TAC `w:(A)pan_v` THEN
      ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`vn:mlstring`; `shn:shape`; `nsn:num list`; `n:num`] THEN
      STRIP_TAC THEN MATCH_MP_TAC PP2CAUX_flookup_temps THEN REWRITE_TAC[LENGTH_MAP] THEN
      CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
      SUBGOAL_THEN `n <= pan_to_crep_context_vmax (ctxt:(A)pan_to_crep_context)` MP_TAC THENL
       [RULE_ASSUM_TAC(REWRITE_RULE[pan_commonProps_ctxt_max_def]) THEN ASM_MESON_TAC[];
        ALL_TAC] THEN
      EXPAND_TAC "temps" THEN REWRITE_TAC[MEM_GENLIST] THEN ARITH_TAC]]);;

let eval_map_comp_exp_flat_eq = prove
 (`!argexps args (s:(A,B)pan_state) (t:(A,B)crep_state) ctxt.
     MAP (pan_eval s) argexps = MAP SOME args /\
     pan_to_crepProof_state_rel s t /\
     pan_to_crepProof_code_rel ctxt (pan_state_code s) (crep_state_code t) /\
     pan_to_crepProof_locals_rel ctxt (pan_state_locals s) (crep_state_locals t) /\
     ALL localised_exp argexps ==>
     MAP (crep_eval t) (FLAT (MAP FST (MAP (pan_to_crep_compile_exp ctxt) argexps))) =
     MAP SOME (FLAT (MAP flatten args))`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN QCASES_ON "args" THEN
  REWRITE_TAC[MAP; FLAT; NOT_CONS_NIL; CONS_11; ALL; MAP_APPEND] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`s:(A,B)pan_state`; `h:(A)panLang_exp`; `a0:(A)pan_v`; `t':(A,B)crep_state`;
                 `ctxt:(A)pan_to_crep_context`;
                 `FST (pan_to_crep_compile_exp (ctxt:(A)pan_to_crep_context) (h:(A)panLang_exp))`;
                 `SND (pan_to_crep_compile_exp (ctxt:(A)pan_to_crep_context) (h:(A)panLang_exp))`]
    compile_exp_val_rel) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]);;

let eval_map_var_cexp_present_ctxt = prove
 (`!es vs (s:(A,B)pan_state) (t:(A,B)crep_state) ctxt.
     MAP (pan_eval s) es = MAP SOME vs /\
     pan_to_crepProof_state_rel s t /\
     pan_to_crepProof_code_rel ctxt (pan_state_code s) (crep_state_code t) /\
     pan_to_crepProof_locals_rel ctxt (pan_state_locals s) (crep_state_locals t) /\
     ALL localised_exp es ==>
     !n. MEM n (FLAT (MAP var_cexp
                  (FLAT (MAP FST (MAP (pan_to_crep_compile_exp ctxt) es))))) ==>
         ?vname shp ns. FLOOKUP (pan_to_crep_context_vars ctxt) vname = SOME (shp,ns) /\
                        MEM n ns`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
  REWRITE_TAC[MEM_FLAT; MEM_MAP] THEN STRIP_TAC THEN RVEQ_TAC THEN
  MATCH_MP_TAC PP2CAUX_compile_exp_vars THEN ASM_MESON_TAC[]);;

let pan_primop_crep_primop = prove
 (`!pop (vs:((A)pan_v)list) value.
     pan_primop pop vs = SOME value ==>
     crep_primop pop (FLAT (MAP flatten vs)) = SOME (flatten value)`,
  GEN_TAC THEN QCASES_ON "pop" THEN REPEAT GEN_TAC THEN REWRITE_TAC[pan_primop_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN2 MP_TAC MP_TAC) THEN
  REWRITE_TAC[ARITH_RULE `3 = SUC(SUC(SUC 0))`; LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[ALL]) THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
  MAP_EVERY (fun v -> QCASES_ON v THEN REWRITE_TAC[isValWord_def] THEN
                      QCASES_ON "a:(A)word_lab" THEN REWRITE_TAC[isValWord_def])
    ["h:(A)pan_v"; "h':(A)pan_v"; "h'':(A)pan_v"] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC(DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[theValWord_def; MAP; flatten_def; FLAT; APPEND; crep_primop_def; LENGTH] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ALL; pan_isWord_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC(DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[pan_theWord_def] THEN
  PAIR_CASES_ON `word_add_carry (a':A word) a'' a'''` THEN
  ASM_REWRITE_TAC[case_def "prod"; option_INJ] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[flatten_def; MAP; FLAT; APPEND]);;

(* HOL4: Resume pc_compile_correct[Primitive] *)

let PP2CAUX_pc_Primitive = prove
 (el 3 PP2CAUX_pc_cases,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FS[localised_prog_def] THEN
  QPAT_X_ASSUM "pan_evaluate _ = _" MP_TAC THEN
  REWRITE_TAC[pan_evaluate_def] THEN
  GVS[is_valid_value_simps; option_case_eq; COND_CASE_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  QCASES_ON "FLOOKUP (pan_state_locals s) v" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[case_def "option"]) THEN ASM_REWRITE_TAC[] THEN
  TRY (FIRST_ASSUM CONTR_TAC) THEN
  RENAME_TAC ["OPT_MMAP (pan_eval s) es = SOME vs"; "pan_primop pop vs = SOME value";
              "FLOOKUP (pan_state_locals s) v = SOME oldv"] THEN
  DRULE locals_rel_lookup_ctxt THEN DISCH_THEN DRULE_ALL THEN
  DISCH_THEN(X_CHOOSE_THEN `ns:num list` STRIP_ASSUME_TAC) THEN
  QPAT_ASSUM "OPT_MMAP (pan_eval s) es = SOME vs"
    (ASSUME_TAC o REWRITE_RULE[opt_mmap_eq_some]) THEN
  MP_TAC(ISPECL [`es:((A)panLang_exp)list`; `vs:((A)pan_v)list`; `s:(A,B)pan_state`;
                 `t:(A,B)crep_state`; `ctxt:(A)pan_to_crep_context`]
    eval_map_comp_exp_flat_eq) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[pan_to_crep_compile_def] THEN
  QPAT_ASSUM "FLOOKUP (pan_to_crep_context_vars ctxt) v = _" SUBST1_TAC THEN
  REWRITE_TAC[case_def "prod"; case_def "option"] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ABBREV_TAC `ces = FLAT (MAP FST (MAP (pan_to_crep_compile_exp (ctxt:(A)pan_to_crep_context))
                                    (es:((A)panLang_exp)list)))` THEN
  ABBREV_TAC `temps = list_of_seq
                        (\x. pan_to_crep_context_vmax (ctxt:(A)pan_to_crep_context) + SUC x)
                        (LENGTH (ces:((A)crep_exp)list))` THEN
  QPAT_ASSUM "pan_to_crepProof_locals_rel _ _ _"
    (STRIP_ASSUME_TAC o REWRITE_RULE[pan_to_crepProof_locals_rel_def]) THEN
  SUBGOAL_THEN `ALL_DISTINCT (ns:num list)` ASSUME_TAC THENL
   [ASM_MESON_TAC[all_distinct_flookup_all_distinct]; ALL_TAC] THEN
  SUBGOAL_THEN
    `!n. MEM n (ns:num list) ==> n <= pan_to_crep_context_vmax (ctxt:(A)pan_to_crep_context)`
    ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[pan_commonProps_ctxt_max_def]) THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `distinct_lists temps (FLAT (MAP var_cexp (ces:((A)crep_exp)list)))`
    ASSUME_TAC THENL
   [EXPAND_TAC "temps" THEN MATCH_MP_TAC PP2CAUX_genlist_distinct_max THEN
    EXPAND_TAC "ces" THEN REWRITE_TAC[MEM_FLAT; MEM_MAP] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
    MATCH_MP_TAC MEM_compile_exp_vmax THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ALL_DISTINCT (temps:num list) /\ LENGTH temps = LENGTH (ces:((A)crep_exp)list)`
    STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "temps" THEN REWRITE_TAC[ALL_DISTINCT_GENLIST; LENGTH_LIST_OF_SEQ] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `distinct_lists (temps:num list) ns` ASSUME_TAC THENL
   [EXPAND_TAC "temps" THEN MATCH_MP_TAC PP2CAUX_genlist_distinct_max THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (FLAT (MAP flatten (vs:((A)pan_v)list))) = LENGTH (ces:((A)crep_exp)list)`
    ASSUME_TAC THENL
   [QPAT_ASSUM "MAP (crep_eval t) ces = _"
      (MP_TAC o AP_TERM `LENGTH:(((A)word_lab)option)list->num`) THEN
    REWRITE_TAC[LENGTH_MAP] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (ns:num list) = LENGTH (flatten (value:(A)pan_v))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `oldv:(A)pan_v` length_flatten_eq_size_of_shape) THEN
    MP_TAC(ISPEC `value:(A)pan_v` length_flatten_eq_size_of_shape) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ces:((A)crep_exp)list`; `temps:num list`; `t:(A,B)crep_state`;
                 `FLAT (MAP flatten (vs:((A)pan_v)list))`;
                 `crep_Primitive ns pop temps:(A)crep_prog`]
    eval_nested_decs_seq_res_var_eq) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `crep_evaluate
      (crep_Primitive ns pop temps:(A)crep_prog,
       crep_state_locals_fupd
         (K (crep_state_locals t |++ ZIP temps (FLAT (MAP flatten (vs:((A)pan_v)list)))))
         (t:(A,B)crep_state)) =
     (NONE,crep_state_locals_fupd
             (K ((crep_state_locals t |++ ZIP temps (FLAT (MAP flatten vs))) |++
                 ZIP ns (flatten (value:(A)pan_v)))) t)`
    SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[crep_evaluate_def] THEN SIMP[] THEN
    SUBGOAL_THEN `OPT_MMAP (FLOOKUP (crep_state_locals (t:(A,B)crep_state) |++
                                     ZIP temps (FLAT (MAP flatten (vs:((A)pan_v)list)))))
                    temps = SOME (FLAT (MAP flatten vs))` SUBST1_TAC THENL
     [MATCH_MP_TAC opt_mmap_some_eq_zip_flookup THEN CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC; ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP pan_primop_crep_primop th]) THEN
    REWRITE_TAC[case_def "option"] THEN
    SUBGOAL_THEN `OPT_MMAP (FLOOKUP (crep_state_locals (t:(A,B)crep_state) |++
                                     ZIP temps (FLAT (MAP flatten (vs:((A)pan_v)list)))))
                    ns = SOME (flatten (oldv:(A)pan_v))` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`temps:num list`; `crep_state_locals (t:(A,B)crep_state)`;
                     `ns:num list`; `FLAT (MAP flatten (vs:((A)pan_v)list))`]
        opt_mmap_disj_zip_flookup) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC THEN FIRST_ASSUM ACCEPT_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `ALL (\v. IS_SOME (FLOOKUP (crep_state_locals (t:(A,B)crep_state) |++
                               ZIP temps (FLAT (MAP flatten (vs:((A)pan_v)list)))) v)) ns`
      ASSUME_TAC THENL
     [REWRITE_TAC[EVERY_MEM] THEN REPEAT STRIP_TAC THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP opt_mmap_mem_func o C CONJ
        (ASSUME `MEM (e:num) ns`)) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[IS_SOME_DEF];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP pan_primop_crep_primop th]) THEN
    REWRITE_TAC[case_def "option"] THEN
    SUBGOAL_THEN `LENGTH (flatten (oldv:(A)pan_v)) = LENGTH (flatten (value:(A)pan_v))`
      (fun th -> REWRITE_TAC[th]) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[case_def "prod"] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[PAIR_EQ; RIGHT_EXISTS_AND_THM; UNWIND_THM1; EXISTS_REFL] THEN
  QPAT_X_ASSUM "pan_to_crepProof_state_rel s t" MP_TAC THEN
  QPAT_X_ASSUM "pan_to_crepProof_code_rel _ _ _" MP_TAC THEN
  QPAT_X_ASSUM "excp_rel _ _" MP_TAC THEN
  SIMP[pan_set_var_def; pan_to_crepProof_state_rel_def] THEN REPEAT DISCH_TAC THEN
  MATCH_MP_TAC PP2CAUX_locals_rel_agree THEN
  EXISTS_TAC `crep_state_locals (t:(A,B)crep_state) |++ ZIP ns (flatten (value:(A)pan_v))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PP2CAUX_locals_rel_update THEN EXISTS_TAC `oldv:(A)pan_v` THEN
    ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`vn:mlstring`; `shn:shape`; `nsn:num list`; `n:num`] THEN
    STRIP_TAC THEN MATCH_MP_TAC PP2CAUX_flookup_temps THEN REWRITE_TAC[LENGTH_MAP] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
    SUBGOAL_THEN `n <= pan_to_crep_context_vmax (ctxt:(A)pan_to_crep_context)` MP_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[pan_commonProps_ctxt_max_def]) THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    EXPAND_TAC "temps" THEN REWRITE_TAC[MEM_GENLIST] THEN ARITH_TAC]);;

(* helpers of not_mem_context_assigned_mem_gt and the cases of             *)
(* pc_compile_correct that declare variables                               *)

let PP2CAUX_not_mem_temps = prove
 (`!x m n. x <= m ==> ~MEM x (list_of_seq (\x. m + SUC x) n)`,
  REWRITE_TAC[MEM_GENLIST] THEN ARITH_TAC);;

let PP2CAUX_wrap_rt_some = prove
 (`!(n:(shape#A list)option) m. wrap_rt n = SOME m ==> n = SOME m`,
  REWRITE_TAC[wrap_rt_def] THEN REPEAT GEN_TAC THEN
  REPEAT (CHANGED_TAC TOP_CASE_TAC) THEN SIMP[]);;

let PP2CAUX_exp_hdl_afv = prove
 (`!(fm:(B,C#num list)fmap) v x.
     (!sh ns. FLOOKUP fm v = SOME (sh,ns) ==> ~MEM x ns) ==>
     ~MEM x (assigned_free_vars (exp_hdl fm v:(A)crep_prog))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[exp_hdl_def] THEN
  REPEAT (CHANGED_TAC TOP_CASE_TAC) THEN REWRITE_TAC[assigned_free_vars_def; MEM] THEN
  SIMP[nested_seq_assigned_free_vars_eq; length_load_globals_eq_read_size]);;

let PP2CAUX_ctxt_max_dec = prove
 (`!m (fm:(B,C#num list)fmap) v sh n.
     pan_commonProps_ctxt_max m fm ==>
     pan_commonProps_ctxt_max (m + n) (fm |+ (v,sh,list_of_seq (\x. m + SUC x) n))`,
  REWRITE_TAC[pan_commonProps_ctxt_max_def; FLOOKUP_UPDATE] THEN REPEAT STRIP_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[option_INJ; PAIR_EQ] THENL
   [DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (SUBST1_TAC o SYM)) THEN
    REWRITE_TAC[MEM_GENLIST] THEN ARITH_TAC;
    REPEAT DISCH_TAC THEN MATCH_MP_TAC(ARITH_RULE `x <= m ==> x <= m + n`) THEN
    ASM_MESON_TAC[]]);;

let PP2CAUX_dec_ctxt_not_mem = prove
 (`!(fm:(B,C#num list)fmap) m x v sh n.
     (!v sh ns'. FLOOKUP fm v = SOME (sh,ns') ==> ~MEM x ns') /\ x <= m ==>
     (!v' sh' ns'. FLOOKUP (fm |+ (v,sh,list_of_seq (\x. m + SUC x) n)) v' = SOME (sh',ns')
                   ==> ~MEM x ns')`,
  REWRITE_TAC[FLOOKUP_UPDATE] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[option_INJ; PAIR_EQ] THENL
   [DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN ASM_SIMP_TAC[PP2CAUX_not_mem_temps];
    ASM_MESON_TAC[]]);;

(* strip the variables and antecedents of a goal, not its negation *)

let PP2CAUX_INTRO_TAC : tactic =
  REPEAT (GEN_TAC ORELSE
          (fun (asl,w as g) -> if is_imp w then DISCH_THEN STRIP_ASSUME_TAC g
                               else failwith "PP2CAUX_INTRO_TAC"));;

(* the tactics of not_mem_context_assigned_mem_gt: the case Dec, then the   *)
(* other cases unfolded and split, the variables declared by nested_decs    *)
(* filtered out, and the induction hypothesis (the one quantified over x)   *)
(* used for the context of the recursive call                              *)

let PP2CAUX_NMC_IH_TAC : tactic =
  FIRST_X_ASSUM (MATCH_MP_TAC o check (fun th ->
    try fst(dest_var(fst(dest_forall(concl th)))) = "x" with Failure _ -> false)) THEN
  REWRITE_TAC[pan_to_crep_context_INFO.ri_accfupds; K_THM] THEN
  REPEAT CONJ_TAC THEN
  TRY (FIRST_ASSUM ACCEPT_TAC) THEN
  TRY (MATCH_MP_TAC PP2CAUX_ctxt_max_dec THEN FIRST_ASSUM ACCEPT_TAC) THEN
  TRY (MATCH_MP_TAC PP2CAUX_dec_ctxt_not_mem THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC) THEN
  TRY (MATCH_MP_TAC(ARITH_RULE `x <= m ==> x <= m + n`) THEN FIRST_ASSUM ACCEPT_TAC);;

let PP2CAUX_NMC_DEC_TAC : tactic =
  PP2CAUX_INTRO_TAC THEN REWRITE_TAC[pan_to_crep_compile_def] THEN
  PAIR_CASES_ON `pan_to_crep_compile_exp (ctxt:(A)pan_to_crep_context) (e:(A)panLang_exp)` THEN
  ASM_REWRITE_TAC[case_def "prod"] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  COND_CASES_TAC THEN REWRITE_TAC[assigned_free_vars_def; MEM] THEN
  DEP_REWRITE_TAC[assigned_free_vars_nested_decs_append] THEN
  REWRITE_TAC[LENGTH_LIST_OF_SEQ; MEM_FILTER; DE_MORGAN_THM] THEN
  ASM_REWRITE_TAC[] THEN DISJ2_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`p0:((A)crep_exp)list`; `p1:shape`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[pan_to_crep_context_INFO.ri_accfupds; K_THM] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PP2CAUX_ctxt_max_dec THEN FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC PP2CAUX_dec_ctxt_not_mem THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC(ARITH_RULE `x <= m ==> x <= m + n`) THEN FIRST_ASSUM ACCEPT_TAC];;

let PP2CAUX_NMC_TAC1 : tactic =
  REPEAT (CHANGED_TAC (DEP_REWRITE_TAC[assigned_free_vars_nested_decs_append])) THEN
  REWRITE_TAC[LENGTH_LIST_OF_SEQ; LENGTH_REPLICATE; LENGTH_MAP; LENGTH; MEM_FILTER;
              DE_MORGAN_THM; assigned_free_vars_def; MEM; MEM_APPEND;
              assigned_free_vars_seq_store_empty; assigned_free_vars_store_globals_empty];;

let PP2CAUX_NMC_TAC2 : tactic =
  ASM_SIMP_TAC[PP2CAUX_not_mem_temps] THEN
  REPEAT CONJ_TAC THEN
  TRY (FIRST_ASSUM(ASSUME_TAC o MATCH_MP PP2CAUX_wrap_rt_some o
         check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "wrap_rt"
                          with Failure _ -> false))) THEN
  TRY (DEP_REWRITE_TAC[nested_seq_assigned_free_vars_eq] THEN
       ASM_REWRITE_TAC[LENGTH_MAP; LENGTH_LIST_OF_SEQ] THEN NO_TAC);;

let PP2CAUX_NMC_FIN_TAC : tactic =
  TRY (MESON_TAC[] THEN NO_TAC) THEN
  TRY (MATCH_MP_TAC PP2CAUX_exp_hdl_afv THEN REPEAT GEN_TAC THEN
       FIRST_ASSUM MATCH_ACCEPT_TAC THEN NO_TAC) THEN
  TRY (RES_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[MEM; DE_MORGAN_THM]) THEN
       ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  TRY (DEP_REWRITE_TAC[nested_seq_assigned_free_vars_eq] THEN CONJ_TAC THENL
        [ASM_REWRITE_TAC[LENGTH_MAP; LENGTH_LIST_OF_SEQ]; RES_TAC THEN ASM_REWRITE_TAC[]] THEN
       NO_TAC) THEN
  TRY (PP2CAUX_NMC_IH_TAC THEN NO_TAC) THEN
  TRY (FS[] THEN RES_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN PP2CAUX_NMC_IH_TAC THEN NO_TAC);;

(* HOL4 proves the cases Call and DecCall with suspend/Resume *)

let pan_to_crepProof_not_mem_context_assigned_mem_gt = prove
 (`!ctxt (p:(A)panLang_prog) x.
     pan_commonProps_ctxt_max (pan_to_crep_context_vmax ctxt)
       (pan_to_crep_context_vars ctxt) /\
     (!v sh ns'. FLOOKUP (pan_to_crep_context_vars ctxt) v = SOME (sh,ns') ==> ~MEM x ns') /\
     x <= pan_to_crep_context_vmax ctxt ==>
     ~MEM x (assigned_free_vars (pan_to_crep_compile ctxt p))`,
  REC_IND_TAC pan_to_crep_compile_ind THEN REPEAT CONJ_TAC THEN
  TRY (PP2CAUX_NMC_DEC_TAC THEN NO_TAC) THEN
  PP2CAUX_INTRO_TAC THEN
  REWRITE_TAC[pan_to_crep_compile_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REPEAT (CHANGED_TAC TOP_CASE_TAC) THEN
  REWRITE_TAC[assigned_free_vars_def; nested_decs_def; MEM; APPEND; MEM_APPEND] THEN
  PP2CAUX_NMC_TAC1 THEN PP2CAUX_NMC_TAC2 THEN PP2CAUX_NMC_FIN_TAC);;

let filter_not_mem_self = prove
 (`FILTER (\x. ~MEM x l) (l:A list) = []`,
  REWRITE_TAC[FILTER_EQ_NIL; EVERY_MEM] THEN MESON_TAC[]);;

let rewritten_context_unassigned = prove
 (`!(p:(A)panLang_prog) nctxt v ctxt ns nvars sh sh'.
     nctxt = pan_to_crep_context_vars_fupd
               (K (pan_to_crep_context_vars ctxt |+ (v,sh,nvars)))
               (pan_to_crep_context_vmax_fupd
                  (K (pan_to_crep_context_vmax ctxt + size_of_shape sh)) ctxt) /\
     FLOOKUP (pan_to_crep_context_vars ctxt) v = SOME (sh',ns) /\
     pan_commonProps_no_overlap (pan_to_crep_context_vars ctxt) /\
     pan_commonProps_ctxt_max (pan_to_crep_context_vmax ctxt) (pan_to_crep_context_vars ctxt) /\
     pan_commonProps_no_overlap (pan_to_crep_context_vars nctxt) /\
     pan_commonProps_ctxt_max (pan_to_crep_context_vmax nctxt)
       (pan_to_crep_context_vars nctxt) /\
     distinct_lists nvars ns ==>
     distinct_lists ns (assigned_free_vars (pan_to_crep_compile nctxt p))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[distinct_lists_def; EVERY_MEM] THEN X_GEN_TAC `x:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC pan_to_crepProof_not_mem_context_assigned_mem_gt THEN
  ASM_REWRITE_TAC[] THEN RVEQ_TAC THEN
  REWRITE_TAC[pan_to_crep_context_INFO.ri_accfupds; K_THM; FLOOKUP_UPDATE] THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`v':mlstring`; `sh'':shape`; `ns':num list`] THEN
    COND_CASES_TAC THEN REWRITE_TAC[option_INJ; PAIR_EQ] THENL
     [DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[distinct_lists_def; EVERY_MEM]) THEN ASM_MESON_TAC[];
      DISCH_TAC THEN
      SUBGOAL_THEN `distinct_lists (ns:num list) ns'` MP_TAC THENL
       [ASM_MESON_TAC[no_overlap_flookup_distinct];
        REWRITE_TAC[distinct_lists_def; EVERY_MEM] THEN ASM_MESON_TAC[]]];
    MATCH_MP_TAC(ARITH_RULE `x <= m ==> x <= m + n`) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[pan_commonProps_ctxt_max_def]) THEN ASM_MESON_TAC[]]);;

let ctxt_max_el_leq = prove
 (`pan_commonProps_ctxt_max (pan_to_crep_context_vmax (ctxt:(A)pan_to_crep_context))
     (pan_to_crep_context_vars ctxt) /\
   FLOOKUP (pan_to_crep_context_vars ctxt) v = SOME (sh,ns) /\
   n < LENGTH ns ==> EL n ns <= pan_to_crep_context_vmax ctxt`,
  REWRITE_TAC[pan_commonProps_ctxt_max_def] THEN MESON_TAC[EL_MEM; MEM_EL]);;

(* code_rel looks at the functions and exceptions of the context only *)

let PP2CAUX_code_rel_vars_vmax = prove
 (`!(ctxt:(A)pan_to_crep_context) f g sc tc.
     pan_to_crepProof_code_rel
       (pan_to_crep_context_vars_fupd f (pan_to_crep_context_vmax_fupd g ctxt)) sc tc <=>
     pan_to_crepProof_code_rel ctxt sc tc`,
  REWRITE_TAC[pan_to_crepProof_code_rel_def; pan_to_crep_context_INFO.ri_accfupds]);;

let PP2CAUX_no_overlap_update = prove
 (`!(fm:(B,C#num list)fmap) v sh nvars.
     pan_commonProps_no_overlap fm /\ ALL_DISTINCT nvars /\
     (!v' sh' ns. FLOOKUP fm v' = SOME (sh',ns) ==> distinct_lists nvars ns) ==>
     pan_commonProps_no_overlap (fm |+ (v,sh,nvars))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pan_commonProps_no_overlap_def; FLOOKUP_UPDATE] THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[option_INJ; PAIR_EQ] THEN
    STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN REPEAT COND_CASES_TAC THEN REWRITE_TAC[option_INJ; PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[distinct_lists_eq_disjoint]) THEN
  RES_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[DISJOINT_SYM]) THEN ASM_MESON_TAC[]);;

(* declaring a source variable with a value: the context gets the next     *)
(* free target variables, holding the flattened value                      *)

let PP2CAUX_locals_rel_dec = prove
 (`!(ctxt:(B)pan_to_crep_context) (sl:(mlstring,(A)pan_v)fmap) (tl:(num,(A)word_lab)fmap)
    v value.
     pan_to_crepProof_locals_rel ctxt sl tl /\
     is_wf_shape ([]:(mlstring#struct_info)list) (shape_of value) ==>
     pan_to_crepProof_locals_rel
       (pan_to_crep_context_vars_fupd
          (K (pan_to_crep_context_vars ctxt |+
                (v,shape_of value,
                 list_of_seq (\x. pan_to_crep_context_vmax ctxt + SUC x)
                   (size_of_shape (shape_of value)))))
          (pan_to_crep_context_vmax_fupd
             (K (pan_to_crep_context_vmax ctxt + size_of_shape (shape_of value))) ctxt))
       (sl |+ (v,value))
       (tl |++ ZIP (list_of_seq (\x. pan_to_crep_context_vmax ctxt + SUC x)
                      (size_of_shape (shape_of value)))
                   (flatten value))`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC `nvars = list_of_seq
                        (\x. pan_to_crep_context_vmax (ctxt:(B)pan_to_crep_context) + SUC x)
                        (size_of_shape (shape_of (value:(A)pan_v)))` THEN
  REWRITE_TAC[pan_to_crepProof_locals_rel_def; pan_to_crep_context_INFO.ri_accfupds; K_THM] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `ALL_DISTINCT (nvars:num list) /\
                LENGTH nvars = LENGTH (flatten (value:(A)pan_v)) /\
                (!k. MEM k nvars ==> pan_to_crep_context_vmax (ctxt:(B)pan_to_crep_context) < k)`
    STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "nvars" THEN
    ASM_SIMP_TAC[ALL_DISTINCT_GENLIST; LENGTH_LIST_OF_SEQ; MEM_GENLIST;
                 length_flatten_eq_size_of_shape] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!v' sh ns. FLOOKUP (pan_to_crep_context_vars (ctxt:(B)pan_to_crep_context)) v' =
                           SOME (sh,ns) ==> distinct_lists (nvars:num list) ns` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[distinct_lists_def; EVERY_MEM] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[pan_commonProps_ctxt_max_def]) THEN
    ASM_MESON_TAC[ARITH_RULE `~(m < k /\ k <= m)`];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PP2CAUX_no_overlap_update THEN ASM_REWRITE_TAC[];
    EXPAND_TAC "nvars" THEN MATCH_MP_TAC PP2CAUX_ctxt_max_dec THEN FIRST_ASSUM ACCEPT_TAC;
    MAP_EVERY X_GEN_TAC [`vname:mlstring`; `v':(A)pan_v`] THEN
    REWRITE_TAC[FLOOKUP_UPDATE] THEN COND_CASES_TAC THEN REWRITE_TAC[option_INJ] THENL
     [DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
      MAP_EVERY EXISTS_TAC [`nvars:num list`; `flatten (value:(A)pan_v)`] THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC opt_mmap_some_eq_zip_flookup THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o C MATCH_MP
        (ASSUME `FLOOKUP (sl:(mlstring,(A)pan_v)fmap) vname = SOME v'`)) THEN
      DISCH_THEN(X_CHOOSE_THEN `ms:num list` (X_CHOOSE_THEN `vs:((A)word_lab)list`
        STRIP_ASSUME_TAC)) THEN
      MAP_EVERY EXISTS_TAC [`ms:num list`; `vs:((A)word_lab)list`] THEN ASM_REWRITE_TAC[] THEN
      QPAT_X_ASSUM "OPT_MMAP (FLOOKUP tl) ms = SOME vs" (SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC opt_mmap_disj_zip_flookup THEN CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN
        MAP_EVERY EXISTS_TAC [`vname:mlstring`; `shape_of (v':(A)pan_v)`] THEN
        FIRST_ASSUM ACCEPT_TAC;
        FIRST_ASSUM ACCEPT_TAC]]]);;

(* undeclaring the variable again: the source variable gets its old value,  *)
(* whose target variables the body did not change                          *)

let PP2CAUX_locals_rel_res_var = prove
 (`!(ctxt:(B)pan_to_crep_context) (sl0:(mlstring,(A)pan_v)fmap) (tl0:(num,(A)word_lab)fmap)
    sl tl v sh nvars n.
     pan_to_crepProof_locals_rel ctxt sl0 tl0 /\
     pan_to_crepProof_locals_rel
       (pan_to_crep_context_vars_fupd (K (pan_to_crep_context_vars ctxt |+ (v,sh,nvars)))
          (pan_to_crep_context_vmax_fupd (K (pan_to_crep_context_vmax ctxt + n)) ctxt))
       sl tl /\
     (!sh' ns k. FLOOKUP (pan_to_crep_context_vars ctxt) v = SOME (sh',ns) /\ MEM k ns ==>
                 FLOOKUP tl k = FLOOKUP tl0 k) ==>
     pan_to_crepProof_locals_rel ctxt (pan_res_var sl (v,FLOOKUP sl0 v)) tl`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[pan_to_crepProof_locals_rel_def; pan_to_crep_context_INFO.ri_accfupds; K_THM] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[FLOOKUP_pan_res_var_thm] THEN
  MAP_EVERY X_GEN_TAC [`vname:mlstring`; `v':(A)pan_v`] THEN
  COND_CASES_TAC THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o rhs o concl)) THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `FLOOKUP (sl0:(mlstring,(A)pan_v)fmap) v = SOME v'`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `ms:num list` (X_CHOOSE_THEN `vs:((A)word_lab)list`
      STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`ms:num list`; `vs:((A)word_lab)list`] THEN ASM_REWRITE_TAC[] THEN
    QPAT_X_ASSUM "OPT_MMAP (FLOOKUP tl0) ms = SOME vs" (SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC OPT_MMAP_CONG THEN REWRITE_TAC[] THEN ASM_MESON_TAC[];
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `FLOOKUP (sl:(mlstring,(A)pan_v)fmap) vname = SOME v'`)) THEN
    ASM_REWRITE_TAC[FLOOKUP_UPDATE]]);;

(* HOL4: Resume pc_compile_correct[Dec] *)

let PP2CAUX_pc_Dec = prove
 (el 1 PP2CAUX_pc_cases,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FS[localised_prog_def] THEN
  QPAT_X_ASSUM "pan_evaluate _ = _" MP_TAC THEN
  REWRITE_TAC[pan_evaluate_def] THEN
  GVS[option_case_eq; COND_CASE_EQ] THEN
  DISCH_THEN(X_CHOOSE_THEN `value:(A)pan_v` STRIP_ASSUME_TAC) THEN RVEQ_TAC THEN
  PAIR_CASES_ON `pan_evaluate (prog:(A)panLang_prog,
      pan_state_locals_fupd (K (pan_state_locals s |+ (v,value))) (s:(A,B)pan_state))` THEN
  QPAT_X_ASSUM "pair_CASE (p0,p1) _ = _" (MP_TAC o REWRITE_RULE[case_def "prod"; PAIR_EQ]) THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  PAIR_CASES_ON `pan_to_crep_compile_exp (ctxt:(A)pan_to_crep_context) (e:(A)panLang_exp)` THEN
  MP_TAC(ISPECL [`s:(A,B)pan_state`; `e:(A)panLang_exp`; `value:(A)pan_v`; `t:(A,B)crep_state`;
                 `ctxt:(A)pan_to_crep_context`; `p0':((A)crep_exp)list`; `p1':shape`]
    compile_exp_val_rel) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> rhs(concl th) = `p1':shape`)) THEN
  REWRITE_TAC[pan_to_crep_compile_def] THEN
  QPAT_ASSUM "pan_to_crep_compile_exp ctxt e = _" SUBST1_TAC THEN
  REWRITE_TAC[case_def "prod"] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  QPAT_ASSUM "LENGTH p0' = _" (fun th -> REWRITE_TAC[EQT_INTRO(SYM th)]) THEN
  ABBREV_TAC `nvars = list_of_seq
                        (\x. pan_to_crep_context_vmax (ctxt:(A)pan_to_crep_context) + SUC x)
                        (size_of_shape (shape_of (value:(A)pan_v)))` THEN
  ABBREV_TAC `nctxt = pan_to_crep_context_vars_fupd
       (K (pan_to_crep_context_vars ctxt |+ (v,shape_of value,nvars)))
      (pan_to_crep_context_vmax_fupd
       (K (pan_to_crep_context_vmax (ctxt:(A)pan_to_crep_context) +
           size_of_shape (shape_of (value:(A)pan_v)))) ctxt)` THEN
  QPAT_ASSUM "pan_to_crepProof_locals_rel _ _ _"
    (STRIP_ASSUME_TAC o REWRITE_RULE[pan_to_crepProof_locals_rel_def]) THEN
  SUBGOAL_THEN `ALL_DISTINCT (nvars:num list) /\
                LENGTH nvars = LENGTH (p0':((A)crep_exp)list) /\
                LENGTH nvars = LENGTH (flatten (value:(A)pan_v)) /\
                (!k. MEM k nvars ==> pan_to_crep_context_vmax (ctxt:(A)pan_to_crep_context) < k)`
    STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "nvars" THEN
    ASM_SIMP_TAC[ALL_DISTINCT_GENLIST; LENGTH_LIST_OF_SEQ; MEM_GENLIST;
                 length_flatten_eq_size_of_shape] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `distinct_lists nvars (FLAT (MAP var_cexp (p0':((A)crep_exp)list)))`
    ASSUME_TAC THENL
   [EXPAND_TAC "nvars" THEN MATCH_MP_TAC PP2CAUX_genlist_distinct_max THEN
    REWRITE_TAC[MEM_FLAT; MEM_MAP] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
    MATCH_MP_TAC MEM_compile_exp_vmax THEN
    MAP_EVERY EXISTS_TAC [`e:(A)panLang_exp`; `x:(A)crep_exp`] THEN
    ASM_REWRITE_TAC[FST];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p0':((A)crep_exp)list`; `nvars:num list`; `t:(A,B)crep_state`;
                 `flatten (value:(A)pan_v)`;
                 `pan_to_crep_compile nctxt (prog:(A)panLang_prog)`]
    eval_nested_decs_seq_res_var_eq) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `value:(A)pan_v`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`res:((A)pan_result)option`; `p1:(A,B)pan_state`;
    `crep_state_locals_fupd (K (crep_state_locals t |++ ZIP nvars (flatten (value:(A)pan_v))))
       (t:(A,B)crep_state)`; `nctxt:(A)pan_to_crep_context`]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [QPAT_ASSUM "pan_to_crepProof_state_rel s t" MP_TAC THEN
      REWRITE_TAC[pan_to_crepProof_state_rel_def; pan_state_INFO.ri_accfupds;
                  crep_state_INFO.ri_accfupds];
      EXPAND_TAC "nctxt" THEN REWRITE_TAC[PP2CAUX_code_rel_vars_vmax] THEN SIMP[];
      EXPAND_TAC "nctxt" THEN REWRITE_TAC[pan_to_crep_context_INFO.ri_accfupds] THEN
      FIRST_ASSUM ACCEPT_TAC;
      EXPAND_TAC "nctxt" THEN EXPAND_TAC "nvars" THEN
      REWRITE_TAC[crep_state_INFO.ri_accfupds; K_THM] THEN
      MATCH_MP_TAC PP2CAUX_locals_rel_dec THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `res1:((A)crep_result)option` (X_CHOOSE_THEN `t1:(A,B)crep_state`
    STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[case_def "prod"] THEN DISCH_THEN SUBST1_TAC THEN
  MAP_EVERY EXISTS_TAC [`res1:((A)crep_result)option`;
    `crep_state_locals_fupd
       (K (FOLDL crep_res_var (crep_state_locals t1)
             (ZIP nvars (MAP (FLOOKUP (crep_state_locals (t:(A,B)crep_state))) nvars))))
       (t1:(A,B)crep_state)`] THEN
  REWRITE_TAC[] THEN
  QPAT_X_ASSUM "pan_to_crepProof_code_rel nctxt _ _" MP_TAC THEN
  QPAT_X_ASSUM "excp_rel _ (pan_state_eshapes p1)" MP_TAC THEN
  QPAT_X_ASSUM "pan_to_crepProof_state_rel p1 t1" MP_TAC THEN
  EXPAND_TAC "nctxt" THEN
  REWRITE_TAC[PP2CAUX_code_rel_vars_vmax; pan_to_crep_context_INFO.ri_accfupds;
              pan_to_crepProof_state_rel_def; pan_state_INFO.ri_accfupds;
              crep_state_INFO.ri_accfupds; K_THM; globals_lookup_def] THEN
  REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(res1 = NONE \/ res1 = SOME (crepSem_Break 0) \/
     res1 = SOME (crepSem_Continue 0:(A)crep_result)) /\
    pan_to_crepProof_locals_rel (nctxt:(A)pan_to_crep_context)
      (pan_state_locals (p1:(A,B)pan_state))
      (crep_state_locals (t1:(A,B)crep_state))
    ==> pan_to_crepProof_locals_rel (ctxt:(A)pan_to_crep_context)
          (pan_res_var (pan_state_locals p1) (v,FLOOKUP (pan_state_locals (s:(A,B)pan_state)) v))
          (FOLDL crep_res_var (crep_state_locals t1)
             (ZIP nvars (MAP (FLOOKUP (crep_state_locals (t:(A,B)crep_state))) nvars)))`
    ASSUME_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
    MATCH_MP_TAC PP2CAUX_locals_rel_agree THEN
    EXISTS_TAC `crep_state_locals (t1:(A,B)crep_state)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC PP2CAUX_locals_rel_res_var THEN
      MAP_EVERY EXISTS_TAC [`crep_state_locals (t:(A,B)crep_state)`; `shape_of (value:(A)pan_v)`;
                            `nvars:num list`; `size_of_shape (shape_of (value:(A)pan_v))`] THEN
      ASM_REWRITE_TAC[] THEN
      MAP_EVERY X_GEN_TAC [`sh':shape`; `ns:num list`; `k:num`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `k <= pan_to_crep_context_vmax (ctxt:(A)pan_to_crep_context)` ASSUME_TAC THENL
       [RULE_ASSUM_TAC(REWRITE_RULE[pan_commonProps_ctxt_max_def]) THEN ASM_MESON_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `~MEM (k:num) nvars` ASSUME_TAC THENL
       [ASM_MESON_TAC[ARITH_RULE `~(m < k /\ k <= m)`]; ALL_TAC] THEN
      TRANS_TAC EQ_TRANS
        `FLOOKUP (crep_state_locals (t:(A,B)crep_state) |++ ZIP nvars (flatten (value:(A)pan_v)))
           k` THEN
      CONJ_TAC THENL
       [SUBGOAL_THEN `distinct_lists (ns:num list)
                        (assigned_free_vars (pan_to_crep_compile (nctxt:(A)pan_to_crep_context)
                                               (prog:(A)panLang_prog)))` MP_TAC THENL
         [MATCH_MP_TAC rewritten_context_unassigned THEN
          MAP_EVERY EXISTS_TAC [`v:mlstring`; `ctxt:(A)pan_to_crep_context`; `nvars:num list`;
                                `shape_of (value:(A)pan_v)`; `sh':shape`] THEN
          ASM_REWRITE_TAC[] THEN
          QPAT_X_ASSUM "pan_to_crepProof_locals_rel nctxt _ _"
            (STRIP_ASSUME_TAC o REWRITE_RULE[pan_to_crepProof_locals_rel_def]) THEN
          ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[distinct_lists_def; EVERY_MEM] THEN X_GEN_TAC `y:num` THEN
          REPEAT DISCH_TAC THEN
          QPAT_X_ASSUM "pan_commonProps_ctxt_max (pan_to_crep_context_vmax ctxt) _"
            (MP_TAC o SPECL [`v:mlstring`; `sh':shape`; `ns:num list`] o CONJUNCT2 o
             REWRITE_RULE[pan_commonProps_ctxt_max_def]) THEN
          ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `y:num`) THEN ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC(ARITH_RULE `m < y ==> ~(y <= m)`) THEN ASM_MESON_TAC[];
          REWRITE_TAC[distinct_lists_def; EVERY_MEM] THEN
          DISCH_THEN(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
          MP_TAC(ISPECL
            [`pan_to_crep_compile (nctxt:(A)pan_to_crep_context) (prog:(A)panLang_prog)`;
             `crep_state_locals_fupd
                (K (crep_state_locals t |++ ZIP nvars (flatten (value:(A)pan_v))))
                (t:(A,B)crep_state)`;
             `res1:((A)crep_result)option`; `t1:(A,B)crep_state`; `k:num`; `0`]
            crep_unassigned_vars_evaluate_same) THEN
          ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
          REWRITE_TAC[crep_state_INFO.ri_accfupds; K_THM]];
        MATCH_MP_TAC flookup_fupdate_zip_not_mem THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC];
      MAP_EVERY X_GEN_TAC [`vn:mlstring`; `shn:shape`; `nsn:num list`; `n:num`] THEN
      STRIP_TAC THEN
      MATCH_MP_TAC flookup_res_var_distinct_zip_eq THEN REWRITE_TAC[LENGTH_MAP] THEN
      SUBGOAL_THEN `n <= pan_to_crep_context_vmax (ctxt:(A)pan_to_crep_context)` MP_TAC THENL
       [RULE_ASSUM_TAC(REWRITE_RULE[pan_commonProps_ctxt_max_def]) THEN ASM_MESON_TAC[];
        ASM_MESON_TAC[ARITH_RULE `~(m < k /\ k <= m)`]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `pan_to_crep_context_eids (nctxt:(A)pan_to_crep_context) =
                pan_to_crep_context_eids (ctxt:(A)pan_to_crep_context)` ASSUME_TAC THENL
   [EXPAND_TAC "nctxt" THEN REWRITE_TAC[pan_to_crep_context_INFO.ri_accfupds]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_case_app (concl th))) THEN
  ASM_REWRITE_TAC[globals_lookup_def] THEN
  QCASES_ON "res" THEN REWRITE_TAC[case_def "option"] THENL
   [STRIP_TAC THEN ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  QCASES_ON "a:(A)pan_result" THEN REWRITE_TAC[case_def "pan_result"] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  TRY (FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC));;

(* HOL4: Resume pc_compile_correct[Store] *)

let PP2CAUX_pc_Store = prove
 (el 4 PP2CAUX_pc_cases,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FS[localised_prog_def] THEN
  QPAT_X_ASSUM "pan_evaluate _ = _" MP_TAC THEN
  REWRITE_TAC[pan_evaluate_def] THEN
  GVS(option_case_eq :: COND_CASE_EQ :: all_case_eqs()) THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  RENAME_TAC ["pan_eval s dst = SOME (pan_Val (Word addr))"; "pan_eval s src = SOME value";
              "mem_stores addr (flatten value) _ _ = SOME m"] THEN
  PAIR_CASES_ON `pan_to_crep_compile_exp (ctxt:(A)pan_to_crep_context) (dst:(A)panLang_exp)` THEN
  MP_TAC(ISPECL [`s:(A,B)pan_state`; `dst:(A)panLang_exp`; `pan_Val (Word addr):(A)pan_v`;
                 `t:(A,B)crep_state`; `ctxt:(A)pan_to_crep_context`;
                 `p0:((A)crep_exp)list`; `p1:shape`] compile_exp_val_rel) THEN
  ASM_REWRITE_TAC[flatten_def; MAP; MAP_EQ_SING; shape_of_def] THEN STRIP_TAC THEN RVEQ_TAC THEN
  PAIR_CASES_ON `pan_to_crep_compile_exp (ctxt:(A)pan_to_crep_context) (src:(A)panLang_exp)` THEN
  MP_TAC(ISPECL [`s:(A,B)pan_state`; `src:(A)panLang_exp`; `value:(A)pan_v`;
                 `t:(A,B)crep_state`; `ctxt:(A)pan_to_crep_context`;
                 `p0':((A)crep_exp)list`; `p1':shape`] compile_exp_val_rel) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> rhs(concl th) = `p1':shape`)) THEN
  REWRITE_TAC[pan_to_crep_compile_def] THEN
  QPAT_ASSUM "pan_to_crep_compile_exp ctxt dst = _" SUBST1_TAC THEN
  QPAT_ASSUM "pan_to_crep_compile_exp ctxt src = _" SUBST1_TAC THEN
  REWRITE_TAC[case_def "prod"; case_def "list"] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  QPAT_ASSUM "LENGTH p0' = _" (fun th -> REWRITE_TAC[EQT_INTRO(SYM th)]) THEN
  ABBREV_TAC `temps = list_of_seq
    (\x. (pan_to_crep_context_vmax (ctxt:(A)pan_to_crep_context) + 1) + SUC x)
    (size_of_shape (shape_of (value:(A)pan_v)))` THEN
  QPAT_ASSUM "pan_to_crepProof_locals_rel _ _ _"
    (STRIP_ASSUME_TAC o REWRITE_RULE[pan_to_crepProof_locals_rel_def]) THEN
  SUBGOAL_THEN
    `ALL_DISTINCT (CONS (pan_to_crep_context_vmax (ctxt:(A)pan_to_crep_context) + 1) temps) /\
     LENGTH (CONS (pan_to_crep_context_vmax ctxt + 1) temps) =
     LENGTH (CONS (x0:(A)crep_exp) p0') /\
     LENGTH temps = LENGTH (flatten (value:(A)pan_v)) /\
     (!k. MEM k (CONS (pan_to_crep_context_vmax ctxt + 1) temps) ==>
          pan_to_crep_context_vmax ctxt < k)`
    STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "temps" THEN
    ASM_SIMP_TAC[ALL_DISTINCT; ALL_DISTINCT_GENLIST; LENGTH_LIST_OF_SEQ; MEM_GENLIST; LENGTH;
                 length_flatten_eq_size_of_shape; MEM] THEN
    REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
    `distinct_lists (CONS (pan_to_crep_context_vmax (ctxt:(A)pan_to_crep_context) + 1) temps)
       (FLAT (MAP var_cexp (CONS (x0:(A)crep_exp) p0')))` ASSUME_TAC THENL
   [REWRITE_TAC[distinct_lists_def; EVERY_MEM] THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    REWRITE_TAC[MEM_FLAT; MEM_MAP; MEM; NOT_EXISTS_THM] THEN
    REWRITE_TAC[LEFT_AND_EXISTS_THM; NOT_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`l:num list`; `y:(A)crep_exp`] THEN
    REWRITE_TAC[DE_MORGAN_THM; TAUT `~(a /\ b) <=> a ==> ~b`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THEN DISCH_TAC THEN
    SUBGOAL_THEN `k <= pan_to_crep_context_vmax (ctxt:(A)pan_to_crep_context)` MP_TAC THENL
     [MATCH_MP_TAC MEM_compile_exp_vmax THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM DISJ_CASES_TAC THENL
       [MAP_EVERY EXISTS_TAC [`dst:(A)panLang_exp`; `x0:(A)crep_exp`] THEN
        FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `y:(A)crep_exp`)) THEN
        ASM_REWRITE_TAC[MEM];
        MAP_EVERY EXISTS_TAC [`src:(A)panLang_exp`; `y:(A)crep_exp`] THEN
        ASM_REWRITE_TAC[]];
      ASM_MESON_TAC[ARITH_RULE `~(m < k /\ k <= m)`]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`CONS (x0:(A)crep_exp) p0'`;
                 `CONS (pan_to_crep_context_vmax (ctxt:(A)pan_to_crep_context) + 1) temps`;
                 `t:(A,B)crep_state`; `CONS (Word addr) (flatten (value:(A)pan_v))`;
                 `crep_nested_seq
                    (stores (crep_Var (pan_to_crep_context_vmax (ctxt:(A)pan_to_crep_context) + 1))
                       (MAP crep_Var temps) (word 0)):(A)crep_prog`]
    eval_nested_decs_seq_res_var_eq) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[MAP; CONS_11] THEN
    QPAT_X_ASSUM "SOME (Word addr) = crep_eval t x0" (ACCEPT_TAC o SYM);
    ALL_TAC] THEN
  W(fun (_,w) -> PAIR_CASES_ON (rand(rator(lhand w)))) THEN
  ASM_REWRITE_TAC[case_def "prod"] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`temps:num list`; `flatten (value:(A)pan_v)`;
                 `pan_to_crep_context_vmax (ctxt:(A)pan_to_crep_context) + 1`;
                 `word 0:A word`; `t:(A,B)crep_state`; `p0'':((A)crep_result)option`;
                 `p1'':(A,B)crep_state`; `addr:A word`; `m:A word->(A)word_lab`]
    evaluate_seq_stores_mem_state_rel) THEN
  ANTS_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[ALL_DISTINCT; ZIP; HD; TL]) THEN ASM_REWRITE_TAC[WORD_ADD_0] THEN
    QPAT_X_ASSUM "pan_to_crepProof_state_rel s t" MP_TAC THEN
    REWRITE_TAC[pan_to_crepProof_state_rel_def] THEN STRIP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE
      [ASSUME `pan_state_memory (s:(A,B)pan_state) = crep_state_memory (t:(A,B)crep_state)`;
       ASSUME `pan_state_memaddrs (s:(A,B)pan_state) = crep_state_memaddrs (t:(A,B)crep_state)`]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP evaluate_seq_stroes_locals_eq o
    check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "crep_evaluate"
                     with Failure _ -> false)) THEN
  SUBGOAL_THEN
   `FOLDL crep_res_var (crep_state_locals (p1'':(A,B)crep_state))
      (ZIP (CONS (pan_to_crep_context_vmax (ctxt:(A)pan_to_crep_context) + 1) temps)
           (MAP (FLOOKUP (crep_state_locals (t:(A,B)crep_state)))
                (CONS (pan_to_crep_context_vmax ctxt + 1) temps))) =
    crep_state_locals t` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[crep_state_INFO.ri_accfupds; K_THM] THEN
    MATCH_MP_TAC res_var_lookup_original_eq THEN
    ASM_SIMP_TAC[LENGTH; length_flatten_eq_size_of_shape];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[case_def "option"] THEN
  MAP_EVERY EXISTS_TAC [`NONE:((A)crep_result)option`;
    `crep_state_locals_fupd (K (crep_state_locals (t:(A,B)crep_state))) (p1'':(A,B)crep_state)`] THEN
  QPAT_X_ASSUM "pan_to_crepProof_state_rel s t" MP_TAC THEN
  ASM_REWRITE_TAC[pan_to_crepProof_state_rel_def; pan_state_INFO.ri_accfupds;
                  crep_state_INFO.ri_accfupds; K_THM] THEN
  SIMP[]);;

(* HOL4: Resume pc_compile_correct[Store32] and [StoreByte]; storefn is   *)
(* the name of the store function of the case                              *)

let PP2CAUX_PC_STORE_W_TAC (storefn:string) : tactic =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FS[localised_prog_def] THEN
  QPAT_X_ASSUM "pan_evaluate _ = _" MP_TAC THEN
  REWRITE_TAC[pan_evaluate_def] THEN
  GVS(option_case_eq :: COND_CASE_EQ :: all_case_eqs()) THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  RENAME_TAC ["pan_eval s dst = SOME (pan_Val (Word adr))";
              "pan_eval s src = SOME (pan_Val (Word w))";
              storefn ^ " _ _ _ _ _ = SOME m"] THEN
  MAP_EVERY (fun (ex,wd) ->
      let ce = mk_comb(`pan_to_crep_compile_exp (ctxt:(A)pan_to_crep_context):
                          (A)panLang_exp->((A)crep_exp)list#shape`, ex) in
      MP_TAC(ISPECL [`s:(A,B)pan_state`; ex;
                     mk_comb(`pan_Val:(A)word_lab->(A)pan_v`,
                             mk_comb(`Word:A word->(A)word_lab`, wd));
                     `t:(A,B)crep_state`; `ctxt:(A)pan_to_crep_context`;
                     mk_comb(`FST:((A)crep_exp)list#shape->((A)crep_exp)list`, ce);
                     mk_comb(`SND:((A)crep_exp)list#shape->shape`, ce)]
               compile_exp_val_rel) THEN
      ASM_REWRITE_TAC[flatten_def; MAP; MAP_EQ_SING; shape_of_def; PAIR] THEN STRIP_TAC)
   [`dst:(A)panLang_exp`,`adr:A word`; `src:(A)panLang_exp`,`w:A word`] THEN
  ONCE_REWRITE_TAC[pan_to_crep_compile_def] THEN
  SUBGOAL_THEN `pan_to_crep_compile_exp (ctxt:(A)pan_to_crep_context) (dst:(A)panLang_exp) =
                ([x0],One) /\
                pan_to_crep_compile_exp ctxt (src:(A)panLang_exp) = ([x0'],One)`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
   [ONCE_REWRITE_TAC[GSYM PAIR] THEN ASM_REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[case_def "prod"; case_def "list"; crep_evaluate_def] THEN
  QPAT_X_ASSUM "SOME (Word adr) = crep_eval t x0" (SUBST1_TAC o SYM) THEN
  QPAT_X_ASSUM "SOME (Word w) = crep_eval t x0'" (SUBST1_TAC o SYM) THEN
  REWRITE_TAC[case_def "option"; case_def "word_lab"; case_def "prod"] THEN
  QPAT_X_ASSUM "pan_to_crepProof_state_rel s t" (STRIP_ASSUME_TAC o
    REWRITE_RULE[pan_to_crepProof_state_rel_def]) THEN
  QPAT_X_ASSUM (storefn ^ " _ _ _ _ _ = SOME m") MP_TAC THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[case_def "option"] THEN
  MAP_EVERY EXISTS_TAC [`NONE:((A)crep_result)option`;
    `crep_state_memory_fupd (K m) (t:(A,B)crep_state)`] THEN
  ASM_REWRITE_TAC[pan_to_crepProof_state_rel_def; pan_state_INFO.ri_accfupds;
                  crep_state_INFO.ri_accfupds; K_THM];;

let PP2CAUX_pc_Store32 = prove
 (el 5 PP2CAUX_pc_cases, PP2CAUX_PC_STORE_W_TAC "pan_mem_store_32");;

let PP2CAUX_pc_StoreByte = prove
 (el 6 PP2CAUX_pc_cases, PP2CAUX_PC_STORE_W_TAC "pan_mem_store_byte");;

let shape_of_alt = prove
 (`!x:(A)word_lab. shape_of (pan_Val x) = One`,
  GEN_TAC THEN QCASES_ON "x" THEN REWRITE_TAC[shape_of_def]);;

let PP2CAUX_sh_mem_op_load_store = prove
 (`(!op r (ad:A word) (s:(A,B)crep_state).
      crep_sh_mem_op (load_op op) r ad s =
      (crep_sh_mem_load r ad (nb_op op) s:((C)crep_result)option#(A,B)crep_state)) /\
   (!op r (ad:A word) (s:(A,B)crep_state).
      crep_sh_mem_op (store_op op) r ad s =
      (crep_sh_mem_store r ad (nb_op op) s:((C)crep_result)option#(A,B)crep_state)) /\
   (!op. is_load (load_op op)) /\ (!op. ~is_load (store_op op))`,
  REPEAT CONJ_TAC THEN GEN_TAC THEN QCASES_ON "op" THEN
  REWRITE_TAC[load_op_def; store_op_def; crep_sh_mem_op_def; nb_op_def; is_load_def]);;

(* witnesses for goals ?x1 .. xn. ... /\ e_i = x_i /\ ... *)

let PP2CAUX_EXISTS_EQ_TAC : tactic = fun (asl,w as g) ->
  let xs,body = strip_exists w in
  let cjs = conjuncts body in
  let find x =
    tryfind (fun c ->
      if is_eq c && rhs c = x && not (free_in x (lhs c)) then lhs c
      else if is_eq c && lhs c = x && not (free_in x (rhs c)) then rhs c
      else failwith "find") cjs in
  MAP_EVERY (fun x -> EXISTS_TAC (find x)) xs g;;

let PP2CAUX_locals_rel_update_word = prove
 (`!ctxt (sl:(mlstring,(A)pan_v)fmap) (tl:(num,(A)word_lab)fmap) vr h w0 w.
     pan_to_crepProof_locals_rel (ctxt:(B)pan_to_crep_context) sl tl /\
     FLOOKUP sl vr = SOME (pan_Val (Word w0)) /\
     FLOOKUP (pan_to_crep_context_vars ctxt) vr = SOME (One,[h]) ==>
     pan_to_crepProof_locals_rel ctxt (sl |+ (vr,pan_Val (Word w))) (tl |+ (h,Word w))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`ctxt:(B)pan_to_crep_context`; `sl:(mlstring,(A)pan_v)fmap`;
                 `tl:(num,(A)word_lab)fmap`; `vr:mlstring`;
                 `pan_Val (Word (w0:A word))`; `pan_Val (Word (w:A word))`; `[h:num]`]
         PP2CAUX_locals_rel_update) THEN
  ASM_REWRITE_TAC[shape_of_def; flatten_def; ZIP; FUPDATE_LIST_THM] THEN
  DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[is_wf_shape_def]);;

(* the two outcomes of the shared memory read *)

let PP2CAUX_SHL_RET_TAC =
  STRIP_TAC THEN RVEQ_TAC THEN PP2CAUX_EXISTS_EQ_TAC THEN
  REWRITE_TAC[case_def "option"; case_def "pan_result"] THEN
  REWRITE_TAC[kvar_simps; pan_set_var_def; crep_set_var_def; pan_state_INFO.ri_accfupds;
              crep_state_INFO.ri_accfupds; K_THM; pan_to_crepProof_state_rel_def] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PP2CAUX_locals_rel_update_word THEN
  ASM_REWRITE_TAC[injectivity "option"; injectivity "pan_v"; injectivity "word_lab"] THEN
  MESON_TAC[];;

let PP2CAUX_SHL_FIN_TAC =
  STRIP_TAC THEN RVEQ_TAC THEN PP2CAUX_EXISTS_EQ_TAC THEN
  REWRITE_TAC[case_def "option"; case_def "pan_result"] THEN
  ASM_REWRITE_TAC[pan_empty_locals_def; crep_empty_locals_def; pan_to_crepProof_state_rel_def;
                  pan_state_INFO.ri_accfupds; crep_state_INFO.ri_accfupds; K_THM];;

let PP2CAUX_pc_ShMemLoad = prove
 (el 7 PP2CAUX_pc_cases,
  REPEAT GEN_TAC THEN STRIP_TAC THEN QCASES_ON "vk" THEN
  FS[localised_prog_def] THEN
  QPAT_X_ASSUM "pan_evaluate _ = _" MP_TAC THEN
  REWRITE_TAC[pan_evaluate_def] THEN
  GVS(option_case_eq :: COND_CASE_EQ :: kvar_simps :: all_case_eqs()) THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  RENAME_TAC ["pan_eval s ad = SOME (pan_Val (Word addr))";
              "FLOOKUP (pan_state_locals s) v = SOME (pan_Val (Word w0))"] THEN
  MP_TAC(ISPECL [`s:(A,B)pan_state`; `ad:(A)panLang_exp`; `pan_Val (Word addr):(A)pan_v`;
                 `t:(A,B)crep_state`; `ctxt:(A)pan_to_crep_context`;
                 `FST (pan_to_crep_compile_exp (ctxt:(A)pan_to_crep_context) (ad:(A)panLang_exp))`;
                 `SND (pan_to_crep_compile_exp (ctxt:(A)pan_to_crep_context) (ad:(A)panLang_exp))`]
    compile_exp_val_rel) THEN
  ASM_REWRITE_TAC[flatten_def; MAP; MAP_EQ_SING; shape_of_def; PAIR] THEN STRIP_TAC THEN
  DRULE locals_rel_lookup_ctxt THEN DISCH_THEN DRULE_ALL THEN
  REWRITE_TAC[shape_of_def; flatten_def; LENGTH_EQ_CONS; LENGTH_EQ_NIL; ONE; LENGTH] THEN
  DISCH_THEN(X_CHOOSE_THEN `ns:num list` STRIP_ASSUME_TAC) THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[opt_mmap_eq_some; MAP; CONS_11]) THEN
  ONCE_REWRITE_TAC[pan_to_crep_compile_def] THEN
  (SUBGOAL_THEN `pan_to_crep_compile_exp (ctxt:(A)pan_to_crep_context) (ad:(A)panLang_exp) =
                 ([x0],One)` SUBST1_TAC THENL
    [ONCE_REWRITE_TAC[GSYM PAIR] THEN ASM_REWRITE_TAC[PAIR_EQ]; ALL_TAC]) THEN
  ASM_REWRITE_TAC[case_def "prod"; case_def "list"; case_def "option"] THEN
  ONCE_REWRITE_TAC[crep_evaluate_def] THEN
  QPAT_X_ASSUM "SOME (Word addr) = crep_eval t x0" (SUBST1_TAC o SYM) THEN
  ASM_REWRITE_TAC[case_def "option"; case_def "word_lab"; PP2CAUX_sh_mem_op_load_store] THEN
  QPAT_X_ASSUM "pan_to_crepProof_state_rel s t" (STRIP_ASSUME_TAC o
    REWRITE_RULE[pan_to_crepProof_state_rel_def]) THEN
  QPAT_X_ASSUM "pan_sh_mem_load _ _ _ _ _ = _" MP_TAC THEN
  ASM_REWRITE_TAC[pan_sh_mem_load_def; crep_sh_mem_load_def] THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
  TRY (STRIP_TAC THEN RVEQ_TAC THEN FS[] THEN NO_TAC) THEN
  TRY (POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN REWRITE_TAC[] THEN NO_TAC) THEN
  (TOP_CASE_TAC THENL [PP2CAUX_SHL_RET_TAC; PP2CAUX_SHL_FIN_TAC]));;

let PP2CAUX_res_var_update_same = prove
 (`!(lc:(K,V)fmap) n w. crep_res_var (lc |+ (n,w)) (n,FLOOKUP lc n) = lc`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`[n:K]`; `[w:V]`; `lc:(K,V)fmap`] res_var_lookup_original_eq) THEN
  REWRITE_TAC[ALL_DISTINCT; MEM; LENGTH; ZIP; MAP; FOLDL; FUPDATE_LIST_THM]);;

(* the two outcomes of the shared memory write *)

let PP2CAUX_SHS_FFI_TAC =
  TOP_CASE_TAC THEN REWRITE_TAC[case_def "prod"; PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN PP2CAUX_EXISTS_EQ_TAC THEN
  REWRITE_TAC[case_def "option"; case_def "pan_result"] THEN
  REWRITE_TAC[pan_to_crepProof_state_rel_def; pan_state_INFO.ri_accfupds;
              crep_state_INFO.ri_accfupds; K_THM; PP2CAUX_res_var_update_same] THEN
  ASM_REWRITE_TAC[];;

(* HOL4: Resume pc_compile_correct[ShMemStore] *)

let PP2CAUX_pc_ShMemStore = prove
 (el 8 PP2CAUX_pc_cases,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FS[localised_prog_def] THEN
  QPAT_X_ASSUM "pan_evaluate _ = _" MP_TAC THEN
  REWRITE_TAC[pan_evaluate_def] THEN
  GVS(option_case_eq :: COND_CASE_EQ :: all_case_eqs()) THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  RENAME_TAC ["pan_eval s ad = SOME (pan_Val (Word addr))";
              "pan_eval s e = SOME (pan_Val (Word bytes))"] THEN
  MAP_EVERY (fun (ex,wd) ->
     let ce = mk_comb(`pan_to_crep_compile_exp (ctxt:(A)pan_to_crep_context):
                         (A)panLang_exp->((A)crep_exp)list#shape`, ex) in
     MP_TAC(ISPECL [`s:(A,B)pan_state`; ex;
                    mk_comb(`pan_Val:(A)word_lab->(A)pan_v`,
                            mk_comb(`Word:A word->(A)word_lab`, wd));
                    `t:(A,B)crep_state`; `ctxt:(A)pan_to_crep_context`;
                    mk_comb(`FST:((A)crep_exp)list#shape->((A)crep_exp)list`, ce);
                    mk_comb(`SND:((A)crep_exp)list#shape->shape`, ce)]
              compile_exp_val_rel) THEN
     ASM_REWRITE_TAC[flatten_def; MAP; MAP_EQ_SING; shape_of_def; PAIR] THEN STRIP_TAC)
  [`ad:(A)panLang_exp`,`addr:A word`; `e:(A)panLang_exp`,`bytes:A word`] THEN
  ONCE_REWRITE_TAC[pan_to_crep_compile_def] THEN
  (SUBGOAL_THEN `pan_to_crep_compile_exp (ctxt:(A)pan_to_crep_context) (ad:(A)panLang_exp) =
                 ([x0],One) /\
                 pan_to_crep_compile_exp ctxt (e:(A)panLang_exp) = ([x0'],One)`
     (CONJUNCTS_THEN SUBST1_TAC) THENL
    [ONCE_REWRITE_TAC[GSYM PAIR] THEN ASM_REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[];
     ALL_TAC]) THEN
  REWRITE_TAC[case_def "prod"; case_def "list"] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ABBREV_TAC `tmp = ITLIST MAX (var_cexp (x0:(A)crep_exp)) 0 + 1` THEN
  (SUBGOAL_THEN `~MEM tmp (var_cexp (x0:(A)crep_exp))` ASSUME_TAC THENL
    [EXPAND_TAC "tmp" THEN REWRITE_TAC[FOLDR_MAX_0_MAX_LIST; MAX_LIST_add_not_mem];
     ALL_TAC]) THEN
  ONCE_REWRITE_TAC[crep_evaluate_def] THEN
  QPAT_X_ASSUM "SOME (Word bytes) = crep_eval t x0'" (SUBST1_TAC o SYM) THEN
  REWRITE_TAC[case_def "option"] THEN
  ONCE_REWRITE_TAC[crep_evaluate_def] THEN
  MP_TAC(ISPECL [`t:(A,B)crep_state`; `x0:(A)crep_exp`; `ARB:num`; `tmp:num`;
                 `Word bytes:(A)word_lab`] update_locals_not_vars_eval_eq') THEN
  (ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC]) THEN
  QPAT_X_ASSUM "SOME (Word addr) = crep_eval t x0" (SUBST1_TAC o SYM) THEN
  REWRITE_TAC[case_def "option"; case_def "word_lab"; PP2CAUX_sh_mem_op_load_store;
              crep_state_INFO.ri_accfupds; K_THM; FLOOKUP_UPDATE; crep_sh_mem_store_def] THEN
  QPAT_X_ASSUM "pan_to_crepProof_state_rel s t" (STRIP_ASSUME_TAC o
    REWRITE_RULE[pan_to_crepProof_state_rel_def]) THEN
  QPAT_X_ASSUM "pan_sh_mem_store _ _ _ _ = _" MP_TAC THEN
  ASM_REWRITE_TAC[pan_sh_mem_store_def] THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[PAIR_EQ; case_def "prod"] THEN
  TRY (STRIP_TAC THEN RVEQ_TAC THEN FS[] THEN NO_TAC) THEN
  TRY (POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN REWRITE_TAC[] THEN NO_TAC) THEN
  PP2CAUX_SHS_FFI_TAC);;

(* the expressions compile_exp produces read no global variable           *)

let PP2CAUX_cexp_heads_mem = prove
 (`!(g:B->(A)list#C) (es:B list) es1 e.
     cexp_heads (MAP FST (MAP g es)) = SOME es1 /\ MEM e es1 ==>
     ?x. MEM x es /\ MEM e (FST (g x))`,
  REWRITE_TAC[cexp_heads_eq; cexp_heads_simp_def] THEN REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_INJ; option_DISTINCT] THEN
  DISCH_THEN(fun th -> MP_TAC(CONJUNCT2 th) THEN REWRITE_TAC[SYM(CONJUNCT1 th)]) THEN
  REWRITE_TAC[MAP_MAP_o] THEN REWRITE_TAC[MEM_MAP; o_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:B` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `x:B` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(FST ((g:B->(A)list#C) x) = [])` MP_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[MAP_MAP_o]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MEM_MAP; o_THM]) THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SPEC_TAC(`FST ((g:B->(A)list#C) x)`,`l:(A)list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[HD; MEM]);;

let PP2CAUX_NLG_OP_TAC =
  MP_TAC(ISPECL [`pan_to_crep_compile_exp (ctxt:(B)pan_to_crep_context):
                    (A)panLang_exp->((A)crep_exp)list#shape`;
                 `es:((A)panLang_exp)list`; `a:((A)crep_exp)list`; `x:(A)crep_exp`]
         PP2CAUX_cexp_heads_mem) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];;

let PP2CAUX_NLG_LOAD_TAC =
  FIRST_X_ASSUM(MP_TAC o MATCH_MP load_glob_not_mem_load o REWRITE_RULE[] o
                SPECL [`a0:(A)crep_exp`; `ad:5 word`]) THEN
  REWRITE_TAC[MEM_FLAT; MEM_MAP] THEN ASM_MESON_TAC[];;

let PP2CAUX_NLG_FIELD_TAC =
  FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP mem_comp_field_lem) THEN
  GVS[crep_exps_def; MEM] THEN ASM_MESON_TAC[];;

let PP2CAUX_compile_exp_no_load_glob = prove
 (`!ctxt (exp:(A)panLang_exp) (e:(A)crep_exp) ad.
     MEM e (FST (pan_to_crep_compile_exp (ctxt:(B)pan_to_crep_context) exp)) ==>
     ~MEM (LoadGlob ad) (crep_exps e)`,
  REC_IND_TAC pan_to_crep_compile_exp_ind THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
  FS[pan_to_crep_compile_exp_def] THEN EVERY_CASE_TAC THEN
  GVS[crep_exps_def; MEM; MEM_MAP; MEM_FLAT; MEM_APPEND] THEN RES_TAC THEN FS[] THENL
   [ASM_MESON_TAC[]; PP2CAUX_NLG_FIELD_TAC; PP2CAUX_NLG_LOAD_TAC;
    PP2CAUX_NLG_OP_TAC; PP2CAUX_NLG_OP_TAC]);;

let compile_exp_not_mem_load_glob = prove
 (`!ct (e:(A)panLang_exp) (s:(A,FFI)pan_state) (t:(A,FFI)crep_state) es sh ad.
     pan_to_crep_compile_exp ct e = (es,sh) /\
     pan_to_crepProof_state_rel s t /\
     pan_to_crepProof_code_rel ct (pan_state_code s) (crep_state_code t) /\
     pan_to_crepProof_locals_rel ct (pan_state_locals s) (crep_state_locals t)
     ==> ~MEM (LoadGlob ad) (FLAT (MAP crep_exps es))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[MEM_FLAT; MEM_MAP; NOT_EXISTS_THM] THEN
  MP_TAC(ISPECL [`ct:(A)pan_to_crep_context`; `e:(A)panLang_exp`]
    PP2CAUX_compile_exp_no_load_glob) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

(* HOL4: Resume pc_compile_correct[Return] *)

let PP2CAUX_pc_Return = prove
 (el 14 PP2CAUX_pc_cases,
  REPEAT GEN_TAC THEN STRIP_TAC THEN FS[localised_prog_def] THEN
  QPAT_X_ASSUM "pan_evaluate _ = _" MP_TAC THEN
  REWRITE_TAC[pan_evaluate_def] THEN
  GVS(option_case_eq :: COND_CASE_EQ :: all_case_eqs()) THEN STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[case_def "option"; case_def "pan_result"] THEN
  MP_TAC(ISPECL [`s:(A,B)pan_state`; `e:(A)panLang_exp`; `a:(A)pan_v`;
                 `t:(A,B)crep_state`; `ctxt:(A)pan_to_crep_context`;
                 `FST (pan_to_crep_compile_exp (ctxt:(A)pan_to_crep_context) (e:(A)panLang_exp))`;
                 `SND (pan_to_crep_compile_exp (ctxt:(A)pan_to_crep_context) (e:(A)panLang_exp))`]
    compile_exp_val_rel) THEN
  ASM_REWRITE_TAC[PAIR] THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[pan_to_crep_compile_def] THEN
  ONCE_REWRITE_TAC[GSYM PAIR] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[PAIR] THEN
  (SUBGOAL_THEN `pan_to_crep_compile_exp (ctxt:(A)pan_to_crep_context) (e:(A)panLang_exp) =
     (FST (pan_to_crep_compile_exp ctxt e), SND (pan_to_crep_compile_exp ctxt e))`
     SUBST1_TAC THENL [REWRITE_TAC[PAIR]; ALL_TAC]) THEN
  REWRITE_TAC[case_def "prod"] THEN
  (SUBGOAL_THEN `LENGTH (flatten (a:(A)pan_v)) =
     size_of_shape (SND (pan_to_crep_compile_exp (ctxt:(A)pan_to_crep_context)
                          (e:(A)panLang_exp)))` ASSUME_TAC THENL
    [MP_TAC(ISPEC `a:(A)pan_v` length_flatten_eq_size_of_shape) THEN ASM_REWRITE_TAC[];
     ALL_TAC]) THEN
  QPAT_X_ASSUM "pan_to_crepProof_state_rel s t" (STRIP_ASSUME_TAC o
    REWRITE_RULE[pan_to_crepProof_state_rel_def]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM opt_mmap_eq_some]) THEN
  (COND_CASES_TAC THENL
    [SUBGOAL_THEN `flatten (a:(A)pan_v) = []` SUBST1_TAC THENL
      [REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN ASM_REWRITE_TAC[]; ALL_TAC];
     ALL_TAC]) THEN
  ASM_REWRITE_TAC[crep_evaluate_def; OPT_MMAP_def; case_def "option"; PAIR_EQ] THEN
  PP2CAUX_EXISTS_EQ_TAC THEN
  REWRITE_TAC[pan_empty_locals_def; crep_empty_locals_def; pan_to_crepProof_state_rel_def;
              pan_state_INFO.ri_accfupds; crep_state_INFO.ri_accfupds; K_THM] THEN
  ASM_REWRITE_TAC[]);;

(* fresh temporaries (above vmax) do not occur in compiled expressions     *)

let PP2CAUX_temps_distinct_compile_exp = prove
 (`!ctxt (e:(A)panLang_exp) es sh temps.
     pan_commonProps_ctxt_max (pan_to_crep_context_vmax (ctxt:(B)pan_to_crep_context))
       (pan_to_crep_context_vars ctxt) /\
     pan_to_crep_compile_exp ctxt e = (es,sh) /\
     (!k. MEM k temps ==> pan_to_crep_context_vmax ctxt < k) ==>
     distinct_lists temps (FLAT (MAP var_cexp es))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[distinct_lists_def; EVERY_MEM; MEM_FLAT; MEM_MAP] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `l:num list` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `y:(A)crep_exp` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `l:num list`)) THEN
  SUBGOAL_THEN `k <= pan_to_crep_context_vmax (ctxt:(B)pan_to_crep_context)` MP_TAC THENL
   [MATCH_MP_TAC MEM_compile_exp_vmax THEN
    MAP_EVERY EXISTS_TAC [`e:(A)panLang_exp`; `y:(A)crep_exp`] THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN ARITH_TAC]);;

(* the global addresses 0 .. n - 1 (5-bit words) are distinct            *)

let PP2CAUX_all_distinct_glob_addrs = prove
 (`!n. n <= 32 ==> ALL_DISTINCT (list_of_seq (\x. word x:5 word) n)`,
  REWRITE_TAC[ALL_DISTINCT_GENLIST] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `val:5 word->num`) THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_CONV `dimindex(:5)`] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `m1 MOD 32 = m1 /\ m2 MOD 32 = m2` (fun th -> REWRITE_TAC[th]) THEN
  CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC);;

(* HOL4: Resume pc_compile_correct[Raise] *)

let PP2CAUX_pc_Raise = prove
 (el 15 PP2CAUX_pc_cases,
  REPEAT GEN_TAC THEN STRIP_TAC THEN FS[localised_prog_def] THEN
  QPAT_X_ASSUM "pan_evaluate _ = _" MP_TAC THEN
  REWRITE_TAC[pan_evaluate_def] THEN
  GVS(option_case_eq :: COND_CASE_EQ :: all_case_eqs()) THEN STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[case_def "option"; case_def "pan_result"] THEN
  RENAME_TAC ["pan_eval s e = SOME value"] THEN
  MP_TAC(ISPECL [`pan_state_eshapes (s:(A,B)pan_state)`;
                 `pan_to_crep_context_eids (ctxt:(A)pan_to_crep_context)`; `eid:mlstring`;
                 `shape_of (value:(A)pan_v)`; `ARB:num`] fdoms_eq_flookup_some_none) THEN
  QPAT_ASSUM "excp_rel _ _" (fun th -> REWRITE_TAC[REWRITE_RULE[excp_rel_def] th]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `n:A word`) THEN
  ASM_REWRITE_TAC[case_def "option"] THEN
  ONCE_REWRITE_TAC[pan_to_crep_compile_def] THEN ASM_REWRITE_TAC[case_def "option"] THEN
  PAIR_CASES_ON `pan_to_crep_compile_exp (ctxt:(A)pan_to_crep_context) (e:(A)panLang_exp)` THEN
  MP_TAC(ISPECL [`s:(A,B)pan_state`; `e:(A)panLang_exp`; `value:(A)pan_v`;
                 `t:(A,B)crep_state`; `ctxt:(A)pan_to_crep_context`;
                 `p0:((A)crep_exp)list`; `p1:shape`] compile_exp_val_rel) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> rhs(concl th) = `p1:shape`)) THEN
  ASM_REWRITE_TAC[case_def "prod"] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ABBREV_TAC `temps = list_of_seq (\x. pan_to_crep_context_vmax (ctxt:(A)pan_to_crep_context) + SUC x)
                        (size_of_shape (shape_of (value:(A)pan_v)))` THEN
  QPAT_ASSUM "pan_to_crepProof_locals_rel _ _ _"
    (STRIP_ASSUME_TAC o REWRITE_RULE[pan_to_crepProof_locals_rel_def]) THEN
  (SUBGOAL_THEN `LENGTH (flatten (value:(A)pan_v)) = size_of_shape (shape_of value)` ASSUME_TAC THENL
    [MATCH_MP_TAC length_flatten_eq_size_of_shape THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC]) THEN
  (SUBGOAL_THEN `size_of_shape (shape_of (value:(A)pan_v)) <= 32` ASSUME_TAC THENL
    [MP_TAC(ISPECL [`shape_of (value:(A)pan_v)`; `pan_state_structs (s:(A,B)pan_state)`]
       size_of_sh_with_ctxt_eq) THEN
     ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN FIRST_ASSUM ACCEPT_TAC;
     ALL_TAC]) THEN
  (SUBGOAL_THEN `ALL_DISTINCT (temps:num list) /\ LENGTH temps = LENGTH (p0:((A)crep_exp)list) /\
                 LENGTH temps = LENGTH (flatten (value:(A)pan_v)) /\
                 (!k. MEM k temps ==> pan_to_crep_context_vmax (ctxt:(A)pan_to_crep_context) < k)`
     STRIP_ASSUME_TAC THENL
    [EXPAND_TAC "temps" THEN
     ASM_SIMP_TAC[ALL_DISTINCT_GENLIST; LENGTH_LIST_OF_SEQ; MEM_GENLIST] THEN
     REPEAT STRIP_TAC THEN ASM_ARITH_TAC;
     ALL_TAC]) THEN
  MP_TAC(ISPECL [`ctxt:(A)pan_to_crep_context`; `e:(A)panLang_exp`; `p0:((A)crep_exp)list`;
                 `shape_of (value:(A)pan_v)`; `temps:num list`]
    PP2CAUX_temps_distinct_compile_exp) THEN
  (ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC]) THEN
  MP_TAC(ISPECL [`p0:((A)crep_exp)list`; `temps:num list`; `t:(A,B)crep_state`;
                 `flatten (value:(A)pan_v)`;
                 `crep_nested_seq (store_globals (word 0) (MAP crep_Var temps)):(A)crep_prog`]
    eval_nested_decs_seq_res_var_eq) THEN
  (ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
  MP_TAC(ISPECL [`temps:num list`; `flatten (value:(A)pan_v)`; `t:(A,B)crep_state`;
                 `word 0:5 word`] evaluate_seq_store_globals_res) THEN
  (ANTS_TAC THENL [ASM_REWRITE_TAC[VAL_WORD_0; ADD_CLAUSES]; DISCH_THEN SUBST1_TAC]) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[case_def "prod"; crep_state_INFO.ri_accfupds; K_THM]) THEN
  MP_TAC(ISPECL [`temps:num list`; `flatten (value:(A)pan_v)`;
                 `crep_state_locals (t:(A,B)crep_state)`] res_var_lookup_original_eq) THEN
  (ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC]) THEN
  ONCE_REWRITE_TAC[crep_evaluate_def] THEN
  QPAT_X_ASSUM "crep_evaluate (nested_decs _ _ _,t) = _" SUBST1_TAC THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[crep_evaluate_def; PAIR_EQ] THEN
  REWRITE_TAC[case_def "prod"; PAIR_EQ] THEN PP2CAUX_EXISTS_EQ_TAC THEN
  REWRITE_TAC[pan_empty_locals_def; crep_empty_locals_def; pan_to_crepProof_state_rel_def;
              pan_state_INFO.ri_accfupds; crep_state_INFO.ri_accfupds; K_THM] THEN
  QPAT_X_ASSUM "pan_to_crepProof_state_rel s t" (STRIP_ASSUME_TAC o
    REWRITE_RULE[pan_to_crepProof_state_rel_def]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  REWRITE_TAC[globals_lookup_def; crep_state_INFO.ri_accfupds; K_THM; WORD_ADD_0] THEN
  MATCH_MP_TAC opt_mmap_some_eq_zip_flookup THEN
  ASM_SIMP_TAC[PP2CAUX_all_distinct_glob_addrs; LENGTH_LIST_OF_SEQ]);;

(* HOL4: Resume pc_compile_correct[Seq] *)

let PP2CAUX_pc_Seq = prove
 (el 9 PP2CAUX_pc_cases,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FS[localised_prog_def] THEN
  QPAT_X_ASSUM "pan_evaluate (panLang_Seq _ _,_) = _" MP_TAC THEN
  ONCE_REWRITE_TAC[pan_evaluate_def] THEN
  PAIR_CASES_ON `pan_evaluate (c1:(A)panLang_prog,s:(A,B)pan_state)` THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[case_def "prod"] THEN
  ONCE_REWRITE_TAC[pan_to_crep_compile_def] THEN ONCE_REWRITE_TAC[crep_evaluate_def] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`p0:((A)pan_result)option`; `p1:(A,B)pan_state`;
                                `t:(A,B)crep_state`; `ctxt:(A)pan_to_crep_context`] o
    check (fun th -> is_forall(concl th) && length(fst(strip_forall(concl th))) = 4)) THEN
  ASM_CASES_TAC `p0:((A)pan_result)option = NONE` THEN
  ASM_REWRITE_TAC[distinctness "option"] THENL
   [(* c1 finishes normally: continue with c2 *)
    REWRITE_TAC[case_def "option"] THEN
    DISCH_THEN(X_CHOOSE_THEN `r1:((A)crep_result)option`
      (X_CHOOSE_THEN `t1:(A,B)crep_state` STRIP_ASSUME_TAC)) THEN
    DISCH_TAC THEN
    ASM_REWRITE_TAC[case_def "prod"] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `p1:(A,B)pan_state` o
      check (fun th -> is_forall(concl th) && length(fst(strip_forall(concl th))) = 1)) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`res:((A)pan_result)option`; `s1:(A,B)pan_state`;
                               `t1:(A,B)crep_state`; `ctxt:(A)pan_to_crep_context`]) THEN
    ASM_REWRITE_TAC[];
    (* c1 ends abruptly: so does the compiled sequence *)
    REWRITE_TAC[PAIR_EQ] THEN DISCH_TAC THEN DISCH_THEN(CONJUNCTS_THEN SUBST_ALL_TAC) THEN
    FIRST_X_ASSUM(K ALL_TAC o
      check (fun th -> is_forall(concl th) && length(fst(strip_forall(concl th))) = 1)) THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) && is_neg(lhand(concl th)))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `r1:((A)crep_result)option`
      (X_CHOOSE_THEN `t1:(A,B)crep_state` STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[case_def "prod"] THEN
    (SUBGOAL_THEN `~(r1:((A)crep_result)option = NONE)` ASSUME_TAC THENL
      [DISCH_TAC THEN POP_ASSUM SUBST_ALL_TAC THEN
       POP_ASSUM MP_TAC THEN
       MAP_EVERY UNDISCH_TAC [`~(res:((A)pan_result)option = NONE)`;
                              `~(res:((A)pan_result)option = SOME pan_Error)`] THEN
       QCASES_ON "res" THEN REWRITE_TAC[case_def "option"; distinctness "option"] THEN
       QCASES_ON "a" THEN REWRITE_TAC[case_def "pan_result"; distinctness "option"] THEN
       TOP_CASE_TAC THEN REWRITE_TAC[];
       ALL_TAC]) THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`r1:((A)crep_result)option`; `t1:(A,B)crep_state`] THEN
    ASM_REWRITE_TAC[]]);;

(* HOL4: Resume pc_compile_correct[If] *)

let PP2CAUX_pc_If = prove
 (el 10 PP2CAUX_pc_cases,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FS[localised_prog_def] THEN
  QPAT_X_ASSUM "pan_evaluate (panLang_If _ _ _,_) = _" MP_TAC THEN
  ONCE_REWRITE_TAC[pan_evaluate_def] THEN
  GVS(option_case_eq :: all_case_eqs()) THEN STRIP_TAC THEN
  RVEQ_TAC THEN
  RENAME_TAC ["pan_evaluate ((if ~(w = word 0) then c1 else c2),s) = res,s1"] THEN
  MP_TAC(ISPECL [`s:(A,B)pan_state`; `e:(A)panLang_exp`; `pan_Val (Word w):(A)pan_v`;
                 `t:(A,B)crep_state`; `ctxt:(A)pan_to_crep_context`;
                 `FST (pan_to_crep_compile_exp (ctxt:(A)pan_to_crep_context) (e:(A)panLang_exp))`;
                 `SND (pan_to_crep_compile_exp (ctxt:(A)pan_to_crep_context) (e:(A)panLang_exp))`]
    compile_exp_val_rel) THEN
  ASM_REWRITE_TAC[flatten_def; MAP; MAP_EQ_SING; shape_of_def; PAIR] THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[pan_to_crep_compile_def] THEN
  (SUBGOAL_THEN `pan_to_crep_compile_exp (ctxt:(A)pan_to_crep_context) (e:(A)panLang_exp) =
                 ([x0],One)` SUBST1_TAC THENL
    [ONCE_REWRITE_TAC[GSYM PAIR] THEN ASM_REWRITE_TAC[PAIR_EQ]; ALL_TAC]) THEN
  REWRITE_TAC[case_def "prod"; case_def "list"] THEN
  ONCE_REWRITE_TAC[crep_evaluate_def] THEN
  QPAT_X_ASSUM "SOME (Word w) = crep_eval t x0" (SUBST1_TAC o SYM) THEN
  REWRITE_TAC[case_def "option"; case_def "word_lab"] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `w:A word` o check (is_forall o concl)) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`res:((A)pan_result)option`; `s1:(A,B)pan_state`;
                             `t:(A,B)crep_state`; `ctxt:(A)pan_to_crep_context`]) THEN
  ASM_CASES_TAC `w:A word = word 0` THEN ASM_REWRITE_TAC[]);;

(* the While case: helper tactics *)

let PP2CAUX_PAN_ERR_TAC : tactic =
  REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    is_neg (concl th) && is_eq (dest_neg (concl th)) &&
    lhs(dest_neg(concl th)) = rhs(dest_neg(concl th)))) THEN
  REWRITE_TAC[];;

let PP2CAUX_WHL_SPLIT_TAC : tactic =
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)));;

(* body ended normally or with Continue: the loop goes on (IH)           *)

let PP2CAUX_WHL_LOOP_TAC : tactic =
  RULE_ASSUM_TAC(REWRITE_RULE[case_def "option"; case_def "pan_result"]) THEN
  FIRST_X_ASSUM(fun th ->
    if is_forall(concl th) && length(fst(strip_forall(concl th))) = 2 then
      MP_TAC(SPECL [`cw:A word`; `p1:(A,B)pan_state`] th) THEN
      (ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN NO_TAC; ALL_TAC])
    else NO_TAC) THEN
  DISCH_THEN(MP_TAC o SPECL [`res:((A)pan_result)option`; `s1:(A,B)pan_state`;
                             `t1:(A,B)crep_state`; `ctxt:(A)pan_to_crep_context`]) THEN
  (ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
  QPAT_ASSUM "pan_to_crep_compile ctxt (While e c) = _" (fun th -> REWRITE_TAC[th]) THEN
  PP2CAUX_WHL_SPLIT_TAC THEN
  ASM_REWRITE_TAC[case_def "option"; case_def "crep_result"];;

let PP2CAUX_WHL_ERR_TAC : tactic =
  RULE_ASSUM_TAC(REWRITE_RULE[distinctness "option"; injectivity "option"]) THEN
  FIRST_ASSUM(CONTR_TAC o check (fun th -> concl th = `F`));;

(* body ended with Break, TimeOut, Return or FinalFFI: the loop stops     *)

let PP2CAUX_WHL_EXIT_TAC : tactic =
  RULE_ASSUM_TAC(REWRITE_RULE[case_def "option"; case_def "pan_result"; PAIR_EQ]) THEN
  PP2CAUX_WHL_SPLIT_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[case_def "option"; case_def "crep_result"; crep_exit_loop_def; PAIR_EQ] THEN
  PP2CAUX_EXISTS_EQ_TAC THEN
  ASM_REWRITE_TAC[case_def "option"; case_def "pan_result"];;

(* body raised an exception *)

let PP2CAUX_WHL_EXN_TAC : tactic =
  RULE_ASSUM_TAC(REWRITE_RULE[case_def "option"; case_def "pan_result"; PAIR_EQ]) THEN
  PP2CAUX_WHL_SPLIT_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    free_in `r1:((A)crep_result)option` (concl th) && not (is_eq (concl th)))) THEN
  TOP_CASE_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[case_def "option"; case_def "crep_result"; crep_exit_loop_def; PAIR_EQ] THEN
  PP2CAUX_EXISTS_EQ_TAC THEN
  ASM_REWRITE_TAC[case_def "option"; case_def "pan_result"];;

(* HOL4: Resume pc_compile_correct[While] *)

let PP2CAUX_pc_While = prove
 (el 13 PP2CAUX_pc_cases,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FS[localised_prog_def] THEN
  QPAT_X_ASSUM "pan_evaluate (While _ _,_) = _" MP_TAC THEN
  ONCE_REWRITE_TAC[pan_evaluate_def] THEN
  (TOP_CASE_TAC THENL [PP2CAUX_PAN_ERR_TAC; ALL_TAC]) THEN
  (TOP_CASE_TAC THENL [ALL_TAC; PP2CAUX_PAN_ERR_TAC; PP2CAUX_PAN_ERR_TAC]) THEN
  TOP_CASE_TAC THEN
  RENAME_TAC ["pan_eval s e = SOME (pan_Val (Word cw))"] THEN
  MP_TAC(ISPECL [`s:(A,B)pan_state`; `e:(A)panLang_exp`; `pan_Val (Word cw):(A)pan_v`;
                 `t:(A,B)crep_state`; `ctxt:(A)pan_to_crep_context`;
                 `FST (pan_to_crep_compile_exp (ctxt:(A)pan_to_crep_context) (e:(A)panLang_exp))`;
                 `SND (pan_to_crep_compile_exp (ctxt:(A)pan_to_crep_context) (e:(A)panLang_exp))`]
    compile_exp_val_rel) THEN
  ASM_REWRITE_TAC[flatten_def; MAP; MAP_EQ_SING; shape_of_def; PAIR] THEN STRIP_TAC THEN
  (SUBGOAL_THEN `pan_to_crep_compile (ctxt:(A)pan_to_crep_context) (While e c) =
                 crep_While x0 (pan_to_crep_compile ctxt c)` ASSUME_TAC THENL
    [ONCE_REWRITE_TAC[pan_to_crep_compile_def] THEN
     (SUBGOAL_THEN `pan_to_crep_compile_exp (ctxt:(A)pan_to_crep_context) (e:(A)panLang_exp) =
                    ([x0],One)` SUBST1_TAC THENL
       [ONCE_REWRITE_TAC[GSYM PAIR] THEN ASM_REWRITE_TAC[PAIR_EQ]; ALL_TAC]) THEN
     REWRITE_TAC[case_def "prod"; case_def "list"];
     ALL_TAC]) THEN
  QPAT_ASSUM "pan_to_crep_compile ctxt (While e c) = _" SUBST1_TAC THEN
  ONCE_REWRITE_TAC[crep_evaluate_def] THEN
  QPAT_X_ASSUM "SOME (Word cw) = crep_eval t x0" (SUBST1_TAC o SYM) THEN
  REWRITE_TAC[case_def "option"; case_def "word_lab"] THEN
  QPAT_X_ASSUM "pan_to_crepProof_state_rel s t" (fun th ->
    ASSUME_TAC th THEN STRIP_ASSUME_TAC(REWRITE_RULE[pan_to_crepProof_state_rel_def] th)) THEN
  (ASM_CASES_TAC `cw:A word = word 0` THENL
    [ASM_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN PP2CAUX_EXISTS_EQ_TAC THEN
     ASM_REWRITE_TAC[case_def "option"];
     ALL_TAC]) THEN
  ASM_REWRITE_TAC[] THEN
  (ASM_CASES_TAC `crep_state_clock (t:(A,B)crep_state) = 0` THENL
    [ASM_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN PP2CAUX_EXISTS_EQ_TAC THEN
     REWRITE_TAC[case_def "option"; case_def "pan_result"] THEN
     REWRITE_TAC[pan_empty_locals_def; crep_empty_locals_def; pan_to_crepProof_state_rel_def;
                 pan_state_INFO.ri_accfupds; crep_state_INFO.ri_accfupds; K_THM] THEN
     ASM_REWRITE_TAC[];
     ALL_TAC]) THEN
  ASM_REWRITE_TAC[] THEN
  PAIR_CASES_ON `pan_evaluate (c:(A)panLang_prog, pan_dec_clock (s:(A,B)pan_state))` THEN
  REWRITE_TAC[case_def "prod"] THEN DISCH_TAC THEN
  (SUBGOAL_THEN `~(p0 = SOME (pan_Error:(A)pan_result))` ASSUME_TAC THENL
    [DISCH_THEN SUBST_ALL_TAC THEN
     FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
       rand(concl th) = `res:((A)pan_result)option,s1:(A,B)pan_state`)) THEN
     REWRITE_TAC[case_def "option"; case_def "pan_result"] THEN
     REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
     FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
       rhs(concl th) = `res:((A)pan_result)option`)) THEN
     FIRST_X_ASSUM(MP_TAC o check (fun th ->
       concl th = `~(SOME (pan_Error:(A)pan_result) = SOME pan_Error)`)) THEN
     REWRITE_TAC[];
     ALL_TAC]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `cw:A word` o
    check (fun th -> is_forall(concl th) && length(fst(strip_forall(concl th))) = 1)) THEN
  (ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
  DISCH_THEN(MP_TAC o SPECL [`p0:((A)pan_result)option`; `p1:(A,B)pan_state`;
                             `crep_dec_clock (t:(A,B)crep_state)`; `ctxt:(A)pan_to_crep_context`]) THEN
  (ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[pan_dec_clock_def; crep_dec_clock_def; pan_to_crepProof_state_rel_def;
                 pan_state_INFO.ri_accfupds; crep_state_INFO.ri_accfupds; K_THM] THEN
     ASM_REWRITE_TAC[];
     DISCH_THEN(X_CHOOSE_THEN `r1:((A)crep_result)option`
       (X_CHOOSE_THEN `t1:(A,B)crep_state` STRIP_ASSUME_TAC))]) THEN
  QPAT_ASSUM "crep_evaluate (pan_to_crep_compile ctxt c,crep_dec_clock t) = _" SUBST1_TAC THEN
  REWRITE_TAC[case_def "prod"] THEN
  NAMED_CASES_ON "p0" ["";"pr"] THENL
   [PP2CAUX_WHL_LOOP_TAC;
    QCASES_ON "pr" THENL
     [PP2CAUX_WHL_ERR_TAC; PP2CAUX_WHL_EXIT_TAC; PP2CAUX_WHL_EXIT_TAC; PP2CAUX_WHL_LOOP_TAC;
      PP2CAUX_WHL_EXIT_TAC; PP2CAUX_WHL_EXN_TAC; PP2CAUX_WHL_EXIT_TAC]]);;

let local_rel_gt_vmax_preserved = prove
 (`!ct (l:(mlstring,(A)pan_v)fmap) (l':(num,(A)word_lab)fmap) n v.
     pan_to_crepProof_locals_rel (ct:(B)pan_to_crep_context) l l' /\
     pan_to_crep_context_vmax ct < n ==>
     pan_to_crepProof_locals_rel ct l (l' |+ (n,v))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pan_to_crepProof_locals_rel_def] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`vn:mlstring`; `pv:(A)pan_v`] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`vn:mlstring`; `pv:(A)pan_v`]) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`ns:num list`; `vs:((A)word_lab)list`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC opt_mmap_flookup_update THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[pan_commonProps_ctxt_max_def]) THEN
  ASM_MESON_TAC[ARITH_RULE `~(m < n /\ n <= m)`]);;

let local_rel_le_zip_update_preserved = prove
 (`!ct (l:(mlstring,(A)pan_v)fmap) (l':(num,(A)word_lab)fmap) x v sh ns v'.
     pan_to_crepProof_locals_rel (ct:(B)pan_to_crep_context) l l' /\
     FLOOKUP l x = SOME v /\
     FLOOKUP (pan_to_crep_context_vars ct) x = SOME (sh,ns) /\
     shape_of v = shape_of v' /\ ALL_DISTINCT ns ==>
     pan_to_crepProof_locals_rel ct (l |+ (x,v')) (l' |++ ZIP ns (flatten v'))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP locals_rel_lookup_ctxt o
    CONJ (ASSUME `pan_to_crepProof_locals_rel (ct:(B)pan_to_crep_context)
                    (l:(mlstring,(A)pan_v)fmap) (l':(num,(A)word_lab)fmap)`)) THEN
  ASM_REWRITE_TAC[injectivity "option"; PAIR_EQ] THEN STRIP_TAC THEN
  MATCH_MP_TAC PP2CAUX_locals_rel_update THEN EXISTS_TAC `v:(A)pan_v` THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let ctxt_fc_funcs_eq = prove
 (`pan_to_crep_context_funcs
     (pan_to_crepProof_ctxt_fc cvs (em:(eid,A word)fmap) vs shs ns) = cvs`,
  REWRITE_TAC[pan_to_crepProof_ctxt_fc_def; pan_to_crep_context_INFO.ri_accessors]);;

let ctxt_fc_eids_eq = prove
 (`pan_to_crep_context_eids
     (pan_to_crepProof_ctxt_fc cvs (em:(eid,A word)fmap) vs shs ns) = em`,
  REWRITE_TAC[pan_to_crepProof_ctxt_fc_def; pan_to_crep_context_INFO.ri_accessors]);;

let ctxt_fc_vmax = prove
 (`pan_to_crep_context_vmax
     (pan_to_crepProof_ctxt_fc (pan_to_crep_context_funcs (ctxt:(A)pan_to_crep_context))
        (em:(eid,A word)fmap) vs shs ns) = MAX_LIST ns`,
  REWRITE_TAC[pan_to_crepProof_ctxt_fc_def; pan_to_crep_context_INFO.ri_accessors]);;

(* HOL4 ZIP (xs,ys) is ZIP xs ys; every use has LENGTH (MAP FST vshs) =    *)
(* LENGTH args and LENGTH ns = LENGTH (FLAT (MAP flatten args))           *)

let slc_def = cake_def
  `slc (vshs:(K#B)list) (args:V list) = FEMPTY |++ ZIP (MAP FST vshs) args`;;

let tlc_def = cake_def
  `tlc (ns:K list) (args:((A)pan_v)list) = FEMPTY |++ ZIP ns (FLAT (MAP flatten args))`;;

let slc_tlc_rw = prove
 (`FEMPTY |++ ZIP (MAP FST (vsh:(K#B)list)) (args:V list) = slc vsh args /\
   FEMPTY |++ ZIP (ns:C list) (FLAT (MAP flatten (args':((A)pan_v)list))) = tlc ns args'`,
  REWRITE_TAC[slc_def; tlc_def]);;

let opt_mmap_eval_is_wf_shape_v = prove
 (`OPT_MMAP (pan_eval (s:(A,FFI)pan_state)) es = SOME vs /\
   pan_to_crepProof_state_rel s (t:(A,FFI)crep_state) /\
   pan_to_crepProof_locals_rel (ctxt:(B)pan_to_crep_context) (pan_state_locals s) t_locs ==>
   ALL (is_wf_shape_v ([]:(mlstring#struct_info)list)) vs`,
  REWRITE_TAC[GSYM ALL_MEM] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP OPT_MMAP_MEM_IMP o
    CONJ (ASSUME `OPT_MMAP (pan_eval (s:(A,FFI)pan_state)) es = SOME vs`)) THEN
  STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[pan_to_crepProof_state_rel_def; pan_to_crepProof_locals_rel_def]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  MP_TAC(ISPECL [`s:(A,FFI)pan_state`; `x':(A)panLang_exp`; `x:(A)pan_v`] eval_is_wf_shape_v) THEN
  ASM_REWRITE_TAC[FEVERY_FEMPTY; FEVERY_ALL_FLOOKUP; FLOOKUP_EMPTY; distinctness "option"] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  MAP_EVERY X_GEN_TAC [`k:mlstring`; `w:(A)pan_v`] THEN DISCH_TAC THEN
  REWRITE_TAC[case_def "prod"] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`k:mlstring`; `w:(A)pan_v`]) THEN ASM_REWRITE_TAC[] THEN
  MESON_TAC[is_wf_shape_v_nil]);;

let locals_rel_wf_shape = prove
 (`pan_to_crepProof_locals_rel (ctxt:(B)pan_to_crep_context)
     (s_locs:(mlstring,(A)pan_v)fmap) t_locs /\
   FLOOKUP s_locs nm = SOME v ==>
   is_wf_shape_v ([]:(mlstring#struct_info)list) v`,
  REWRITE_TAC[pan_to_crepProof_locals_rel_def] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`nm:mlstring`; `v:(A)pan_v`]) THEN ASM_REWRITE_TAC[] THEN
  MESON_TAC[is_wf_shape_v_nil]);;

(* the antecedents of the with_shape lemmas from the call's assumptions   *)

let PP2CAUX_WS_ANTS_TAC : tactic =
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN TRY REFL_TAC THEN
  TRY(FIRST_ASSUM(ACCEPT_TAC o SYM)) THEN
  REWRITE_TAC[LENGTH_MAP] THEN FIRST_ASSUM(ACCEPT_TAC o SYM);;

let PP2CAUX_ALIST_REWR_TAC : tactic =
  FIRST_ASSUM(fun th ->
    if is_eq(concl th) &&
       (try fst(dest_const(rator(rhs(concl th)))) = "alist_to_fmap" with Failure _ -> false)
    then REWRITE_TAC[th] else NO_TAC);;

let pan_to_crepProof_call_preserve_state_code_locals_rel = prove
 (`!rshape.
   ALL_DISTINCT (MAP FST (vshs:(mlstring#shape)list)) /\
   ALL2 (\vshape arg. SND vshape = shape_of arg) vshs (args:((A)pan_v)list) /\
   pan_to_crepProof_state_rel (s:(A,FFI)pan_state) (t:(A,FFI)crep_state) /\
   pan_to_crepProof_code_rel (ctxt:(A)pan_to_crep_context) (pan_state_code s)
     (crep_state_code t) /\
   excp_rel (pan_to_crep_context_eids ctxt) (pan_state_eshapes s) /\
   pan_to_crepProof_locals_rel ctxt (pan_state_locals s) (crep_state_locals t) /\
   FLOOKUP (pan_state_code s) fname = SOME (vshs,prog,rshape) /\
   FLOOKUP (pan_to_crep_context_funcs ctxt) fname = SOME (vshs,rshape) /\
   ALL_DISTINCT ns /\
   size_of_shape (Comb (MAP SND vshs)) = LENGTH (FLAT (MAP flatten args)) /\
   FLOOKUP (crep_state_code t) fname =
     SOME (ns,pan_to_crep_compile
                (pan_to_crepProof_ctxt_fc (pan_to_crep_context_funcs ctxt)
                   (pan_to_crep_context_eids ctxt) (MAP FST vshs) (MAP SND vshs) ns)
                prog) /\
   LENGTH ns = LENGTH (FLAT (MAP flatten args)) /\
   ALL (is_wf_shape_v ([]:(mlstring#struct_info)list)) args ==>
   pan_to_crepProof_state_rel
     (pan_state_locals_fupd (K (slc vshs args)) (pan_dec_clock s))
     (crep_state_locals_fupd (K (tlc ns args)) (crep_dec_clock t)) /\
   pan_to_crepProof_code_rel
     (pan_to_crepProof_ctxt_fc (pan_to_crep_context_funcs ctxt)
        (pan_to_crep_context_eids ctxt) (MAP FST vshs) (MAP SND vshs) ns)
     (pan_state_code (pan_dec_clock s)) (crep_state_code (crep_dec_clock t)) /\
   excp_rel
     (pan_to_crep_context_eids
       (pan_to_crepProof_ctxt_fc (pan_to_crep_context_funcs ctxt)
          (pan_to_crep_context_eids ctxt) (MAP FST vshs) (MAP SND vshs) ns))
     (pan_state_eshapes (pan_dec_clock s)) /\
   pan_to_crepProof_locals_rel
     (pan_to_crepProof_ctxt_fc (pan_to_crep_context_funcs ctxt)
        (pan_to_crep_context_eids ctxt) (MAP FST vshs) (MAP SND vshs) ns)
     (slc vshs args) (tlc ns args)`,
  GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[pan_dec_clock_def; crep_dec_clock_def; pan_state_INFO.ri_accfupds;
              crep_state_INFO.ri_accfupds; K_THM; ctxt_fc_eids_eq] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [QPAT_X_ASSUM "pan_to_crepProof_state_rel s t" MP_TAC THEN
    REWRITE_TAC[pan_to_crepProof_state_rel_def; pan_state_INFO.ri_accfupds;
                crep_state_INFO.ri_accfupds; K_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [QPAT_X_ASSUM "pan_to_crepProof_code_rel _ _ _" MP_TAC THEN
    REWRITE_TAC[pan_to_crepProof_code_rel_def; ctxt_fc_funcs_eq; ctxt_fc_eids_eq];
    ALL_TAC] THEN
  REWRITE_TAC[pan_to_crepProof_locals_rel_def; pan_to_crepProof_ctxt_fc_def;
              pan_to_crep_context_INFO.ri_accessors] THEN
  (SUBGOAL_THEN `LENGTH (vshs:(mlstring#shape)list) = LENGTH (args:((A)pan_v)list)` ASSUME_TAC THENL
    [FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP EVERY2_LENGTH); ALL_TAC]) THEN
  (SUBGOAL_THEN `LENGTH (ns:num list) = size_of_shape (Comb (MAP SND (vshs:(mlstring#shape)list)))`
     ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
  (SUBGOAL_THEN `LENGTH (vshs:(mlstring#shape)list) =
                 LENGTH (with_shape (MAP SND vshs) (ns:num list))` ASSUME_TAC THENL
    [ONCE_REWRITE_TAC[GSYM (ISPECL [`vshs:(mlstring#shape)list`; `SND:mlstring#shape->shape`]
                              LENGTH_MAP)] THEN
     MATCH_MP_TAC length_with_shape_eq_shape THEN ASM_REWRITE_TAC[];
     ALL_TAC]) THEN
  (SUBGOAL_THEN
    `FEMPTY |++ ZIP (MAP FST (vshs:(mlstring#shape)list))
                    (ZIP (MAP SND vshs) (with_shape (MAP SND vshs) (ns:num list))) =
     alist_to_fmap (ZIP (MAP FST vshs) (ZIP (MAP SND vshs) (with_shape (MAP SND vshs) ns)))`
    ASSUME_TAC THENL
    [MATCH_MP_TAC fm_empty_zip_alist THEN ASM_REWRITE_TAC[] THEN
     MP_TAC(ISPECL [`MAP SND (vshs:(mlstring#shape)list)`;
                    `with_shape (MAP SND (vshs:(mlstring#shape)list)) (ns:num list)`] LENGTH_ZIP) THEN
     REWRITE_TAC[LENGTH_MAP] THEN
     (ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC THEN FIRST_ASSUM ACCEPT_TAC]);
     ALL_TAC]) THEN
  CONJ_TAC THENL
   [PP2CAUX_ALIST_REWR_TAC THEN MATCH_MP_TAC all_distinct_alist_no_overlap THEN
    REWRITE_TAC[LENGTH_MAP] THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [PP2CAUX_ALIST_REWR_TAC THEN MATCH_MP_TAC all_distinct_alist_ctxt_max THEN
    REWRITE_TAC[LENGTH_MAP] THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`vname:mlstring`; `v:(A)pan_v`] THEN REWRITE_TAC[slc_def] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`MAP FST (vshs:(mlstring#shape)list)`; `args:((A)pan_v)list`;
                 `vname:mlstring`; `v:(A)pan_v`] fm_empty_zip_flookup) THEN
  (ANTS_TAC THENL
    [REWRITE_TAC[LENGTH_MAP] THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC]) THEN
  REWRITE_TAC[LENGTH_MAP] THEN DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`MAP FST (vshs:(mlstring#shape)list)`; `args:((A)pan_v)list`; `n:num`] EL_ZIP) THEN
  (ANTS_TAC THENL
    [REWRITE_TAC[LENGTH_MAP] THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC]) THEN
  FIRST_X_ASSUM(fun th -> if is_eq(concl th) && is_pair(rhs(concl th)) then
    (REWRITE_TAC[th] THEN ASSUME_TAC th) else NO_TAC) THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  (SUBGOAL_THEN `n < LENGTH (args:((A)pan_v)list)` ASSUME_TAC THENL
    [FIRST_X_ASSUM(fun th ->
       if concl th = `LENGTH (vshs:(mlstring#shape)list) = LENGTH (args:((A)pan_v)list)`
       then SUBST1_TAC(SYM th) THEN ASSUME_TAC th else NO_TAC) THEN FIRST_ASSUM ACCEPT_TAC;
     ALL_TAC]) THEN
  (SUBGOAL_THEN `ALL2 (\sh (arg:(A)pan_v). sh = shape_of arg) (MAP SND (vshs:(mlstring#shape)list)) args`
     ASSUME_TAC THENL [ASM_REWRITE_TAC[EVERY2_MAP]; ALL_TAC]) THEN
  (SUBGOAL_THEN `SND (EL n (vshs:(mlstring#shape)list)) = shape_of (v:(A)pan_v)` ASSUME_TAC THENL
    [QPAT_X_ASSUM "ALL2 (\\vshape arg. SND vshape = shape_of arg) vshs args"
       (MP_TAC o REWRITE_RULE[LIST_REL_EL_EQN]) THEN
     STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[];
     ALL_TAC]) THEN
  (SUBGOAL_THEN `is_wf_shape_v ([]:(mlstring#struct_info)list) (v:(A)pan_v)` ASSUME_TAC THENL
    [QPAT_X_ASSUM "ALL (is_wf_shape_v []) args" (MP_TAC o REWRITE_RULE[GSYM ALL_MEM]) THEN
     DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MEM_EL THEN
     FIRST_ASSUM ACCEPT_TAC;
     ALL_TAC]) THEN
  MAP_EVERY EXISTS_TAC [`EL n (with_shape (MAP SND (vshs:(mlstring#shape)list)) (ns:num list))`;
                        `flatten (v:(A)pan_v)`] THEN
  REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`MAP FST (vshs:(mlstring#shape)list)`; `MAP SND (vshs:(mlstring#shape)list)`;
                   `with_shape (MAP SND (vshs:(mlstring#shape)list)) (ns:num list)`; `n:num`;
                   `vname:mlstring`] fm_empty_zip_flookup_el) THEN
    (ANTS_TAC THENL
      [REWRITE_TAC[LENGTH_MAP] THEN REPEAT CONJ_TAC THEN
       TRY (FIRST_ASSUM ACCEPT_TAC) THEN FIRST_ASSUM(ACCEPT_TAC o SYM);
       DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[EL_MAP]]);
    ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[is_wf_shape_v_nil]] THEN
  (SUBGOAL_THEN `LENGTH (EL n (with_shape (MAP SND (vshs:(mlstring#shape)list)) (ns:num list))) =
                 LENGTH (flatten (v:(A)pan_v))` ASSUME_TAC THENL
    [MATCH_MP_TAC list_rel_flatten_with_shape_length THEN
     EXISTS_TAC `args:((A)pan_v)list` THEN PP2CAUX_WS_ANTS_TAC;
     ALL_TAC]) THEN
  REWRITE_TAC[tlc_def; opt_mmap_eq_some; LIST_EQ; LENGTH_MAP] THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  (SUBGOAL_THEN `m < LENGTH (EL n (with_shape (MAP SND (vshs:(mlstring#shape)list)) (ns:num list)))`
     ASSUME_TAC THENL
    [FIRST_ASSUM(fun th -> if concl th =
        `LENGTH (EL n (with_shape (MAP SND (vshs:(mlstring#shape)list)) (ns:num list))) =
         LENGTH (flatten (v:(A)pan_v))` then SUBST1_TAC th else NO_TAC) THEN
     FIRST_ASSUM ACCEPT_TAC;
     ALL_TAC]) THEN
  ASM_SIMP_TAC[EL_MAP] THEN
  MATCH_MP_TAC list_rel_flatten_with_shape_flookup THEN REPEAT CONJ_TAC THEN
  TRY(FIRST_ASSUM ACCEPT_TAC) THEN TRY REFL_TAC THEN
  TRY(REWRITE_TAC[LENGTH_MAP] THEN FIRST_ASSUM(ACCEPT_TAC o SYM) THEN NO_TAC) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `v:(A)pan_v = EL n args`)) THEN
  FIRST_ASSUM ACCEPT_TAC);;

let no_overlap_wrap_rt_some_all_distinct = prove
 (`pan_commonProps_no_overlap (fm:(K,shape#(A)list)fmap) /\
   wrap_rt (FLOOKUP fm r) = SOME (vsh,ns) ==> ALL_DISTINCT ns`,
  REWRITE_TAC[pan_commonProps_no_overlap_def] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP PP2CAUX_wrap_rt_some) THEN ASM_MESON_TAC[]);;

let is_wf_shape_nil_length_flatten = prove
 (`is_wf_shape ([]:(mlstring#struct_info)list) (shape_of (v:(A)pan_v)) /\
   (size_of_shape (shape_of v) = 0 ==> l = []) /\
   (0 < size_of_shape (shape_of v) ==> l = flatten v) ==>
   LENGTH l = size_of_shape (shape_of v)`,
  STRIP_TAC THEN ASM_CASES_TAC `size_of_shape (shape_of (v:(A)pan_v)) = 0` THENL
   [RES_TAC THEN ASM_REWRITE_TAC[LENGTH];
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ASM_SIMP_TAC[ARITH_RULE `0 < n <=> ~(n = 0)`] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC length_flatten_eq_size_of_shape THEN FIRST_ASSUM ACCEPT_TAC]);;

(* HOL4 [local] *)

let flatten_nil_no_size = prove
 (`is_wf_shape ([]:(mlstring#struct_info)list) (shape_of (x:(A)pan_v)) ==>
   (flatten x = [] <=> size_of_shape (shape_of x) = 0)`,
  DISCH_TAC THEN REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN
  ASM_SIMP_TAC[length_flatten_eq_size_of_shape]);;

(* HOL4 [local] locals_rel_wf_shape, the second theorem of that name (it   *)
(* rebinds the first); here under the helper prefix                        *)

let PP2CAUX_locals_rel_wf_shape_fevery = prove
 (CASE_TERM `pan_to_crepProof_locals_rel (ctxt:(B)pan_to_crep_context)
     (s_locs:(mlstring,(A)pan_v)fmap) t_locs /\
   ss = TAKE 0 (pan_state_structs (s:(A,FFI)pan_state)) ==>
   FEVERY (\p. match p with (nm,v) -> is_wf_shape_v ss v) s_locs`,
  STRIP_TAC THEN ASM_REWRITE_TAC[TAKE; FEVERY_ALL_FLOOKUP] THEN
  MAP_EVERY X_GEN_TAC [`k:mlstring`; `w:(A)pan_v`] THEN DISCH_TAC THEN
  REWRITE_TAC[case_def "prod"] THEN
  MATCH_ACCEPT_TAC(MATCH_MP locals_rel_wf_shape
    (CONJ (ASSUME `pan_to_crepProof_locals_rel (ctxt:(B)pan_to_crep_context)
                     (s_locs:(mlstring,(A)pan_v)fmap) (t_locs:(num,(A)word_lab)fmap)`)
          (ASSUME `FLOOKUP (s_locs:(mlstring,(A)pan_v)fmap) k = SOME w`))));;

(* HOL4 [local] *)

let evaluate_shape_invariant_ret_inst = prove
 (CASE_TERM `pan_evaluate (p,s) = (SOME v,(s':(A,FFI)pan_state)) /\
   pan_to_crepProof_state_rel s (t:(A,FFI)crep_state) /\
   pan_to_crepProof_locals_rel (ctxt:(B)pan_to_crep_context) (pan_state_locals s) t_locs ==>
   match v with
     pan_Return retv -> is_wf_shape_v ([]:(mlstring#struct_info)list) retv
   | pan_Exception eid exn -> is_wf_shape_v ([]:(mlstring#struct_info)list) exn
   | _ -> T`,
  STRIP_TAC THEN
  MP_TAC(ISPECL [`p:(A)panLang_prog`; `s:(A,FFI)pan_state`; `SOME (v:(A)pan_result)`;
                 `s':(A,FFI)pan_state`] evaluate_is_wf_shape_invariant) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP pan_to_crepProof_state_rel_structs) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP state_rel_globals) THEN
  ASM_REWRITE_TAC[FEVERY_FEMPTY] THEN
  MP_TAC(ISPECL [`ctxt:(B)pan_to_crep_context`; `pan_state_locals (s:(A,FFI)pan_state)`;
                 `t_locs:(num,(A)word_lab)fmap`; `[]:(mlstring#struct_info)list`;
                 `s:(A,FFI)pan_state`] (GENL [`ctxt:(B)pan_to_crep_context`;
                    `s_locs:(mlstring,(A)pan_v)fmap`; `t_locs:(num,(A)word_lab)fmap`;
                    `ss:(mlstring#struct_info)list`; `s:(A,FFI)pan_state`]
                    PP2CAUX_locals_rel_wf_shape_fevery)) THEN
  ASM_REWRITE_TAC[TAKE] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  QCASES_ON "v" THEN REWRITE_TAC[case_def "option"; case_def "pan_result"] THEN MESON_TAC[]);;

(* HOL4 [local] *)

let evaluate_shape_invariant_ret_inst2 = prove
 (CASE_TERM `OPT_MMAP (pan_eval s) argexps = SOME args /\
   pan_lookup_code (pan_state_code (s:(A,FFI)pan_state)) fname args =
     SOME (p2,newlocals,rsh) /\
   pan_evaluate (p,pan_state_locals_fupd (K newlocals) (pan_dec_clock s)) =
     (SOME v,(s':(A,FFI)pan_state)) /\
   pan_to_crepProof_state_rel s (t:(A,FFI)crep_state) /\
   pan_to_crepProof_locals_rel (ctxt:(B)pan_to_crep_context) (pan_state_locals s) t_locs ==>
   match v with
     pan_Return retv -> is_wf_shape_v ([]:(mlstring#struct_info)list) retv
   | pan_Exception eid exn -> is_wf_shape_v ([]:(mlstring#struct_info)list) exn
   | _ -> T`,
  STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP pan_to_crepProof_state_rel_structs) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP state_rel_globals) THEN
  MP_TAC(ISPECL [`ctxt:(B)pan_to_crep_context`; `pan_state_locals (s:(A,FFI)pan_state)`;
                 `t_locs:(num,(A)word_lab)fmap`; `[]:(mlstring#struct_info)list`;
                 `s:(A,FFI)pan_state`] (GENL [`ctxt:(B)pan_to_crep_context`;
                    `s_locs:(mlstring,(A)pan_v)fmap`; `t_locs:(num,(A)word_lab)fmap`;
                    `ss:(mlstring#struct_info)list`; `s:(A,FFI)pan_state`]
                    PP2CAUX_locals_rel_wf_shape_fevery)) THEN
  ASM_REWRITE_TAC[TAKE] THEN DISCH_TAC THEN
  MP_TAC(INST [`p2:(A)panLang_prog`,`prog:(A)panLang_prog`; `rsh:shape`,`return_sh:shape`]
    lookup_code_wf_shape_invariant_step) THEN ASM_REWRITE_TAC[FEVERY_FEMPTY] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`p:(A)panLang_prog`;
                 `pan_state_locals_fupd (K newlocals) (pan_dec_clock (s:(A,FFI)pan_state))`;
                 `SOME (v:(A)pan_result)`; `s':(A,FFI)pan_state`] evaluate_is_wf_shape_invariant) THEN
  ASM_REWRITE_TAC[pan_dec_clock_def; pan_state_INFO.ri_accfupds; K_THM; FEVERY_FEMPTY] THEN
  QCASES_ON "v" THEN REWRITE_TAC[case_def "option"; case_def "pan_result"] THEN MESON_TAC[]);;

let pan_to_crepProof_evaluate_replicate_const = prove
 (`!n (s:(A,B)crep_state).
     OPT_MMAP (crep_eval s) (REPLICATE n (crep_Const (word 0))) =
     SOME (REPLICATE n (Word (word 0)))`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[REPLICATE; OPT_MMAP_def; crep_eval_def] THEN
  REWRITE_TAC[OPTION_BIND_def]);;

let eval_distinct_lists_not_affect' = prove
 (`!vs (s:(A,B)crep_state) e w nvals.
     crep_eval s e = SOME w /\
     LENGTH vs = LENGTH nvals /\
     distinct_lists vs (var_cexp e) ==>
     crep_eval (crep_state_locals_fupd (K (crep_state_locals s |++ ZIP vs nvals)) s) e =
     SOME w`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THENL
   [NAMED_CASES_ON "nvals" ["";"nv nvs"] THEN REWRITE_TAC[LENGTH; NOT_SUC] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[ZIP; FUPDATE_LIST_THM] THEN
    SUBGOAL_THEN `crep_state_locals_fupd (K (crep_state_locals s)) s = (s:(A,B)crep_state)`
      SUBST1_TAC THENL
     [REWRITE_TAC[crep_state_component_equality; crep_state_INFO.ri_accfupds; K_THM];
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  NAMED_CASES_ON "nvals" ["";"nv nvs"] THEN
  REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ; ZIP; FUPDATE_LIST_THM; distinct_lists_def; ALL] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`s:(A,B)crep_state`; `e:(A)crep_exp`; `ARB:num`; `h:num`; `nv:(A)word_lab`]
    update_locals_not_vars_eval_eq') THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
    [`crep_state_locals_fupd (K (crep_state_locals s |+ (h,nv))) (s:(A,B)crep_state)`;
     `e:(A)crep_exp`; `w:(A)word_lab`; `nvs:((A)word_lab)list`]) THEN
  ASM_REWRITE_TAC[distinct_lists_def; crep_state_INFO.ri_accfupds;
                  crep_state_INFO.ri_fupdfupds; K_THM; o_DEF] THEN
  REWRITE_TAC[K_DEF]);;

let opt_mmap_eval_distinct_lists_not_affect = prove
 (`!es (s:(A,B)crep_state) ws vs nvals.
     OPT_MMAP (crep_eval s) es = SOME ws /\
     LENGTH vs = LENGTH nvals /\
     distinct_lists vs (FLAT (MAP var_cexp es)) ==>
     OPT_MMAP (crep_eval (crep_state_locals_fupd
                            (K (crep_state_locals s |++ ZIP vs nvals)) s)) es = SOME ws`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[OPT_MMAP_def; MAP; FLAT] THEN REPEAT GEN_TAC THENL
   [MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[OPTION_BIND_EQUALS_OPTION] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP distinct_lists_append_right_elim) THEN
  EXISTS_TAC `x:(A)word_lab` THEN CONJ_TAC THENL
   [MATCH_MP_TAC eval_distinct_lists_not_affect' THEN ASM_REWRITE_TAC[];
    EXISTS_TAC `x':((A)word_lab)list` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let genlist_vmax_distinct_lists_compiled_exps = prove
 (`!(ctxt:(B)pan_to_crep_context) n (argexps:((A)panLang_exp)list).
     pan_commonProps_ctxt_max (pan_to_crep_context_vmax ctxt) (pan_to_crep_context_vars ctxt)
     ==> distinct_lists (list_of_seq (\x. SUC x + pan_to_crep_context_vmax ctxt) n)
           (FLAT (MAP var_cexp (FLAT (MAP FST (MAP (pan_to_crep_compile_exp ctxt) argexps)))))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[distinct_lists_def; GSYM ALL_MEM; MEM_FLAT; MEM_MAP] THEN
  X_GEN_TAC `k:num` THEN DISCH_THEN(MP_TAC o MATCH_MP mem_genlist_add_suc_val) THEN
  STRIP_TAC THEN REWRITE_TAC[NOT_EXISTS_THM] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  SUBGOAL_THEN `k <= pan_to_crep_context_vmax (ctxt:(B)pan_to_crep_context)` MP_TAC THENL
   [MATCH_MP_TAC MEM_compile_exp_vmax THEN ASM_MESON_TAC[]; ASM_ARITH_TAC]);;

(* the common part of the Call cases: the callee is found on both sides,  *)
(* its arguments agree and the relations hold for the callee's states      *)

let PP2CAUX_call_setup = prove
 (`!(s:(A,FFI)pan_state) (t:(A,FFI)crep_state) ctxt argexps args fname prog newlocals rsh.
     OPT_MMAP (pan_eval s) argexps = SOME args /\
     pan_lookup_code (pan_state_code s) fname args = SOME (prog,newlocals,rsh) /\
     pan_to_crepProof_state_rel s t /\
     pan_to_crepProof_code_rel ctxt (pan_state_code s) (crep_state_code t) /\
     excp_rel (pan_to_crep_context_eids ctxt) (pan_state_eshapes s) /\
     pan_to_crepProof_locals_rel ctxt (pan_state_locals s) (crep_state_locals t) /\
     ALL localised_exp argexps ==>
     ?vshs ns nctxt.
       FLOOKUP (pan_to_crep_context_funcs ctxt) fname = SOME (vshs,rsh) /\
       localised_prog prog /\
       newlocals = slc vshs args /\
       ns = list_of_seq I (size_of_shape (Comb (MAP SND vshs))) /\
       nctxt = pan_to_crepProof_ctxt_fc (pan_to_crep_context_funcs ctxt)
                 (pan_to_crep_context_eids ctxt) (MAP FST vshs) (MAP SND vshs) ns /\
       OPT_MMAP (crep_eval t)
         (FLAT (MAP FST (MAP (pan_to_crep_compile_exp ctxt) argexps))) =
         SOME (FLAT (MAP flatten args)) /\
       crep_lookup_code (crep_state_code t) fname (FLAT (MAP flatten args))
         (LENGTH (FLAT (MAP flatten args))) =
         SOME (pan_to_crep_compile nctxt prog, tlc ns args) /\
       pan_to_crepProof_state_rel
         (pan_state_locals_fupd (K newlocals) (pan_dec_clock s))
         (crep_state_locals_fupd (K (tlc ns args)) (crep_dec_clock t)) /\
       pan_to_crepProof_code_rel nctxt
         (pan_state_code (pan_state_locals_fupd (K newlocals) (pan_dec_clock s)))
         (crep_state_code (crep_state_locals_fupd (K (tlc ns args)) (crep_dec_clock t))) /\
       excp_rel (pan_to_crep_context_eids nctxt)
         (pan_state_eshapes (pan_state_locals_fupd (K newlocals) (pan_dec_clock s))) /\
       pan_to_crepProof_locals_rel nctxt
         (pan_state_locals (pan_state_locals_fupd (K newlocals) (pan_dec_clock s)))
         (crep_state_locals (crep_state_locals_fupd (K (tlc ns args)) (crep_dec_clock t)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  QPAT_X_ASSUM "pan_lookup_code _ _ _ = _" (MP_TAC o REWRITE_RULE[pan_lookup_code_def]) THEN
  GVS(option_case_eq :: COND_CASE_EQ :: all_case_eqs()) THEN STRIP_TAC THEN RVEQ_TAC THEN
  EXISTS_TAC `x:(mlstring#shape)list` THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP code_rel_imp) THEN
  DISCH_THEN(MP_TAC o SPECL [`fname:mlstring`; `x:(mlstring#shape)list`; `prog:(A)panLang_prog`]) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[slc_def] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP opt_mmap_eval_is_wf_shape_v o
    CONJ (ASSUME `OPT_MMAP (pan_eval (s:(A,FFI)pan_state)) argexps = SOME args`) o
    CONJ (ASSUME `pan_to_crepProof_state_rel (s:(A,FFI)pan_state) (t:(A,FFI)crep_state)`)) THEN
  MP_TAC(ISPECL [`x:(mlstring#shape)list`; `args:((A)pan_v)list`] list_rel_length_shape_of_flatten) THEN
  (ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_TAC]) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[opt_mmap_eq_some] THEN MATCH_MP_TAC eval_map_comp_exp_flat_eq THEN
    EXISTS_TAC `s:(A,FFI)pan_state` THEN ASM_REWRITE_TAC[GSYM opt_mmap_eq_some];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[crep_lookup_code_def; case_def "option"; case_def "prod";
                    LENGTH_LIST_OF_SEQ; ALL_DISTINCT_GENLIST; I_THM; tlc_def] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[pan_state_INFO.ri_accfupds; crep_state_INFO.ri_accfupds; K_THM] THEN
  MP_TAC(SPEC `rsh:shape` (INST [`x:(mlstring#shape)list`,`vshs:(mlstring#shape)list`;
     `list_of_seq I (size_of_shape (Comb (MAP SND (x:(mlstring#shape)list)))):num list`,
     `ns:num list`] pan_to_crepProof_call_preserve_state_code_locals_rel)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[ALL_DISTINCT_GENLIST; I_THM; LENGTH_LIST_OF_SEQ] THEN SIMP_TAC[];
    REWRITE_TAC[slc_def; pan_dec_clock_def; crep_dec_clock_def; pan_state_INFO.ri_accfupds;
                crep_state_INFO.ri_accfupds; K_THM] THEN SIMP_TAC[]]);;

(* fresh temporaries above vmax keep the locals relation *)

let PP2CAUX_locals_rel_gt_vmax_zip = prove
 (`!rts vals (ct:(B)pan_to_crep_context) (l:(mlstring,(A)pan_v)fmap) (l':(num,(A)word_lab)fmap).
     pan_to_crepProof_locals_rel ct l l' /\
     (!k. MEM k rts ==> pan_to_crep_context_vmax ct < k) /\ LENGTH rts = LENGTH vals ==>
     pan_to_crepProof_locals_rel ct l (l' |++ ZIP rts vals)`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THENL
   [NAMED_CASES_ON "vals" ["";"v vs"] THEN
    REWRITE_TAC[LENGTH; NOT_SUC; ZIP; FUPDATE_LIST_THM] THEN MESON_TAC[];
    NAMED_CASES_ON "vals" ["";"v vs"] THEN
    REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ; ZIP; FUPDATE_LIST_THM; MEM] THEN
    STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC local_rel_gt_vmax_preserved THEN ASM_MESON_TAC[]; ASM_MESON_TAC[]]]);;

(* declaring temporaries initialised to 0 around a program *)

let PP2CAUX_nested_decs_zeros = prove
 (CASE_TERM `!rts (t:(A,B)crep_state) (p:(A)crep_prog).
     ALL_DISTINCT rts ==>
     let (q,r) = crep_evaluate
                   (p,crep_state_locals_fupd
                        (K (crep_state_locals t |++
                            ZIP rts (REPLICATE (LENGTH rts) (Word (word 0))))) t) in
     crep_evaluate (nested_decs rts (REPLICATE (LENGTH rts) (crep_Const (word 0))) p,t) =
     (q,crep_state_locals_fupd
          (K (FOLDL crep_res_var (crep_state_locals r)
                (ZIP rts (MAP (FLOOKUP (crep_state_locals t)) rts)))) r)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC eval_nested_decs_seq_res_var_eq THEN
  ASM_REWRITE_TAC[LENGTH_REPLICATE; GSYM opt_mmap_eq_some;
                  pan_to_crepProof_evaluate_replicate_const] THEN
  REWRITE_TAC[distinct_lists_def; ALL_MEM; MEM_FLAT; MEM_MAP; MEM_REPLICATE] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN FS[var_cexp_def; MEM]);;

(* the Call case split by the shape of the call's return/handler part:   *)
(* NONE (tail call), SOME (NONE,hdl) and SOME (SOME (rk,rt),hdl)        *)

let PP2CAUX_call_stmt (ct:term) (vs:term list) =
  let tm = el 18 PP2CAUX_pc_cases in
  let cv,bod = dest_forall tm in
  list_mk_forall(vs, vsubst [ct,cv] bod);;

let PP2CAUX_call_stmt_none = PP2CAUX_call_stmt
  `NONE:((varkind#mlstring)option#(mlstring#mlstring#(A)panLang_prog)option)option` [];;

let PP2CAUX_call_stmt_retnone = PP2CAUX_call_stmt
  `SOME (NONE:(varkind#mlstring)option, hdl:(mlstring#mlstring#(A)panLang_prog)option)`
  [`hdl:(mlstring#mlstring#(A)panLang_prog)option`];;

let PP2CAUX_call_stmt_ret = PP2CAUX_call_stmt
  `SOME (SOME (rk:varkind,rt:mlstring), hdl:(mlstring#mlstring#(A)panLang_prog)option)`
  [`rk:varkind`; `rt:mlstring`; `hdl:(mlstring#mlstring#(A)panLang_prog)option`];;

let PP2CAUX_code_rel_ctxt_fc = prove
 (`pan_to_crepProof_code_rel
     (pan_to_crepProof_ctxt_fc (pan_to_crep_context_funcs (ctxt:(A)pan_to_crep_context))
        (pan_to_crep_context_eids ctxt) vs shs ns) c1 c2 <=>
   pan_to_crepProof_code_rel ctxt c1 c2`,
  REWRITE_TAC[pan_to_crepProof_code_rel_def; ctxt_fc_funcs_eq; ctxt_fc_eids_eq]);;

let PP2CAUX_state_rel_clock = prove
 (`pan_to_crepProof_state_rel (s:(A,FFI)pan_state) (t:(A,FFI)crep_state) ==>
   crep_state_clock t = pan_state_clock s`,
  SIMP_TAC[pan_to_crepProof_state_rel_def]);;

let PP2CAUX_globals_lookup_locals_fupd = prove
 (`!f (t:(A,B)crep_state) (v:(A)pan_v).
     globals_lookup (crep_state_locals_fupd f t) v = globals_lookup t v`,
  REWRITE_TAC[globals_lookup_def; crep_state_INFO.ri_accfupds]);;

(* the pan result of a call from the callee's result: the error cases     *)

let PP2CAUX_CALL_PAN_RES_TAC : tactic =
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
    rand(concl th) = `res:((A)pan_result)option,s1:(A,B)pan_state`)) THEN
  REWRITE_TAC[case_def "option"; case_def "pan_result"] THEN
  TRY COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  TRY (FIRST_X_ASSUM(MP_TAC o check (fun th ->
         concl th = `~(SOME (pan_Error:(A)pan_result) = SOME pan_Error)`)) THEN
       REWRITE_TAC[] THEN NO_TAC);;

(* a tail call (and every call whose callee ends in TimeOut, FinalFFI or  *)
(* an uncaught exception) returns the callee's result with empty locals   *)

let PP2CAUX_TAIL_CREP_TAC : tactic =
  PP2CAUX_CALL_PAN_RES_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> free_in `r1:((A)crep_result)option` (concl th) &&
     not (is_eq (concl th) &&
          (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "crep_evaluate"
           with Failure _ -> false)))) THEN
  REWRITE_TAC[case_def "option"; case_def "pan_result"; ctxt_fc_eids_eq] THEN
  TRY (TOP_CASE_TAC THEN REWRITE_TAC[]) THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[case_def "option"; case_def "crep_result"; PAIR_EQ] THEN
  PP2CAUX_EXISTS_EQ_TAC THEN
  REWRITE_TAC[case_def "option"; case_def "pan_result"] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PP2CAUX_code_rel_ctxt_fc; ctxt_fc_eids_eq]) THEN
  REWRITE_TAC[pan_empty_locals_def; crep_empty_locals_def; pan_state_INFO.ri_accfupds;
              crep_state_INFO.ri_accfupds; K_THM; PP2CAUX_globals_lookup_locals_fupd] THEN
  QPAT_X_ASSUM "pan_to_crepProof_state_rel st t1" MP_TAC THEN
  REWRITE_TAC[pan_to_crepProof_state_rel_def] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[pan_state_INFO.ri_accfupds; crep_state_INFO.ri_accfupds; K_THM];;

(* HOL4: Resume pc_compile_correct[Call] for caltyp = NONE, the clock    *)
(* zero part, and Resume pc_compile_correct[Call_TailCall]               *)

let PP2CAUX_pc_Call_none = prove
 (PP2CAUX_call_stmt_none,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FS[localised_prog_def] THEN
  QPAT_X_ASSUM "pan_evaluate (panLang_Call _ _ _,_) = _" MP_TAC THEN
  ONCE_REWRITE_TAC[pan_evaluate_def] THEN
  (TOP_CASE_TAC THENL [PP2CAUX_PAN_ERR_TAC; ALL_TAC]) THEN
  (TOP_CASE_TAC THENL [PP2CAUX_PAN_ERR_TAC; ALL_TAC]) THEN
  PAIR_CASES_ON `a':(A)panLang_prog#(mlstring,(A)pan_v)fmap#shape` THEN
  REWRITE_TAC[case_def "prod"] THEN
  RENAME_TAC ["OPT_MMAP (pan_eval s) argexps = SOME args";
              "pan_lookup_code (pan_state_code s) fname args = SOME (prog,newlocals,rsh)"] THEN
  MP_TAC(ISPECL [`s:(A,B)pan_state`; `t:(A,B)crep_state`; `ctxt:(A)pan_to_crep_context`;
                 `argexps:((A)panLang_exp)list`; `args:((A)pan_v)list`; `fname:mlstring`;
                 `prog:(A)panLang_prog`; `newlocals:(mlstring,(A)pan_v)fmap`; `rsh:shape`]
    PP2CAUX_call_setup) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `vshs:(mlstring#shape)list` (X_CHOOSE_THEN `ns:num list`
    (X_CHOOSE_THEN `nctxt:(A)pan_to_crep_context` STRIP_ASSUME_TAC))) THEN
  ONCE_REWRITE_TAC[pan_to_crep_compile_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[case_def "option"] THEN
  ONCE_REWRITE_TAC[crep_evaluate_def] THEN ASM_REWRITE_TAC[case_def "option"; case_def "prod"] THEN
  SUBST1_TAC(MATCH_MP PP2CAUX_state_rel_clock
    (ASSUME `pan_to_crepProof_state_rel (s:(A,B)pan_state) (t:(A,B)crep_state)`)) THEN
  (COND_CASES_TAC THENL
    [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN PP2CAUX_EXISTS_EQ_TAC THEN
     REWRITE_TAC[case_def "option"; case_def "pan_result"] THEN
     REWRITE_TAC[pan_empty_locals_def; crep_empty_locals_def; pan_state_INFO.ri_accfupds;
                 crep_state_INFO.ri_accfupds; K_THM] THEN
     QPAT_X_ASSUM "pan_to_crepProof_state_rel s t" MP_TAC THEN
     REWRITE_TAC[pan_to_crepProof_state_rel_def; pan_state_INFO.ri_accfupds;
                 crep_state_INFO.ri_accfupds; K_THM] THEN SIMP_TAC[] THEN
     DISCH_TAC THEN ASM_REWRITE_TAC[];
     ALL_TAC]) THEN
  PAIR_CASES_ON `pan_evaluate (prog:(A)panLang_prog,
    pan_state_locals_fupd (K (slc (vshs:(mlstring#shape)list) (args:((A)pan_v)list)))
      (pan_dec_clock (s:(A,B)pan_state)))` THEN
  REWRITE_TAC[case_def "prod"] THEN DISCH_TAC THEN
  RENAME_TAC ["pan_evaluate (prog,pan_state_locals_fupd (K (slc vshs args)) (pan_dec_clock s)) = r,st"] THEN
  (SUBGOAL_THEN `~(r = SOME (pan_Error:(A)pan_result))` ASSUME_TAC THENL
    [DISCH_THEN SUBST_ALL_TAC THEN
     FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
       rand(concl th) = `res:((A)pan_result)option,s1:(A,B)pan_state`)) THEN
     REWRITE_TAC[case_def "option"; case_def "pan_result"; PAIR_EQ] THEN STRIP_TAC THEN
     FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
       rhs(concl th) = `res:((A)pan_result)option`)) THEN
     FIRST_X_ASSUM(MP_TAC o check (fun th ->
       concl th = `~(SOME (pan_Error:(A)pan_result) = SOME pan_Error)`)) THEN
     REWRITE_TAC[];
     ALL_TAC]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[pan_state_INFO.ri_accfupds; crep_state_INFO.ri_accfupds; K_THM]) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`args:((A)pan_v)list`; `rsh:shape`; `prog:(A)panLang_prog`;
                                `newlocals:(mlstring,(A)pan_v)fmap`] o
    check (fun th -> is_forall(concl th) && length(fst(strip_forall(concl th))) = 4)) THEN
  (ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
  DISCH_THEN(MP_TAC o SPECL [`r:((A)pan_result)option`; `st:(A,B)pan_state`;
    `crep_state_locals_fupd (K (tlc (ns:num list) (args:((A)pan_v)list)))
       (crep_dec_clock (t:(A,B)crep_state))`; `nctxt:(A)pan_to_crep_context`]) THEN
  (ANTS_TAC THENL
    [REWRITE_TAC[crep_state_INFO.ri_accfupds; K_THM] THEN ASM_REWRITE_TAC[];
     DISCH_THEN(X_CHOOSE_THEN `r1:((A)crep_result)option`
       (X_CHOOSE_THEN `t1:(A,B)crep_state` STRIP_ASSUME_TAC))]) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `nctxt:(A)pan_to_crep_context`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `ns:num list`)) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  FIRST_ASSUM(fun th -> if is_eq(concl th) && is_comb(lhs(concl th)) &&
     (try fst(dest_const(rator(lhs(concl th)))) = "crep_evaluate" with Failure _ -> false)
     then REWRITE_TAC[th] else NO_TAC) THEN
  REWRITE_TAC[case_def "prod"] THEN
  NAMED_CASES_ON "r" ["";"pr"] THENL
   [PP2CAUX_CALL_PAN_RES_TAC;
    QCASES_ON "pr" THENL
     [PP2CAUX_CALL_PAN_RES_TAC; PP2CAUX_TAIL_CREP_TAC; PP2CAUX_CALL_PAN_RES_TAC;
      PP2CAUX_CALL_PAN_RES_TAC; PP2CAUX_TAIL_CREP_TAC; PP2CAUX_TAIL_CREP_TAC;
      PP2CAUX_TAIL_CREP_TAC]]);;

let PP2CAUX_CALL_CLOCK0_TAC : tactic =
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN PP2CAUX_EXISTS_EQ_TAC THEN
  REWRITE_TAC[case_def "option"; case_def "pan_result"] THEN
  REWRITE_TAC[pan_empty_locals_def; crep_empty_locals_def; pan_state_INFO.ri_accfupds;
              crep_state_INFO.ri_accfupds; K_THM] THEN
  QPAT_X_ASSUM "pan_to_crepProof_state_rel s t" MP_TAC THEN
  REWRITE_TAC[pan_to_crepProof_state_rel_def; pan_state_INFO.ri_accfupds;
              crep_state_INFO.ri_accfupds; K_THM] THEN SIMP_TAC[] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[];;

(* from the unfolded crep call to the cases of the callee's result, with  *)
(* the callee's induction hypothesis applied                               *)

let PP2CAUX_CALL_COMMON_TAC : tactic =
  ONCE_REWRITE_TAC[crep_evaluate_def] THEN
  ASM_REWRITE_TAC[case_def "option"; case_def "prod"; ALL_DISTINCT] THEN
  SUBST1_TAC(MATCH_MP PP2CAUX_state_rel_clock
    (ASSUME `pan_to_crepProof_state_rel (s:(A,B)pan_state) (t:(A,B)crep_state)`)) THEN
  (COND_CASES_TAC THENL [PP2CAUX_CALL_CLOCK0_TAC; ALL_TAC]) THEN
  PAIR_CASES_ON `pan_evaluate (prog:(A)panLang_prog,
    pan_state_locals_fupd (K (slc (vshs:(mlstring#shape)list) (args:((A)pan_v)list)))
      (pan_dec_clock (s:(A,B)pan_state)))` THEN
  REWRITE_TAC[case_def "prod"] THEN DISCH_TAC THEN
  RENAME_TAC ["pan_evaluate (prog,pan_state_locals_fupd (K (slc vshs args)) (pan_dec_clock s)) = r,st"] THEN
  (SUBGOAL_THEN `~(r = SOME (pan_Error:(A)pan_result))` ASSUME_TAC THENL
    [DISCH_THEN SUBST_ALL_TAC THEN
     FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
       rand(concl th) = `res:((A)pan_result)option,s1:(A,B)pan_state`)) THEN
     REWRITE_TAC[case_def "option"; case_def "pan_result"; PAIR_EQ] THEN STRIP_TAC THEN
     FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
       rhs(concl th) = `res:((A)pan_result)option`)) THEN
     FIRST_X_ASSUM(MP_TAC o check (fun th ->
       concl th = `~(SOME (pan_Error:(A)pan_result) = SOME pan_Error)`)) THEN
     REWRITE_TAC[];
     ALL_TAC]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[pan_state_INFO.ri_accfupds; crep_state_INFO.ri_accfupds; K_THM]) THEN
  FIRST_ASSUM(MP_TAC o SPECL [`args:((A)pan_v)list`; `rsh:shape`; `prog:(A)panLang_prog`;
              `slc (vshs:(mlstring#shape)list) (args:((A)pan_v)list)`] o
    check (fun th -> is_forall(concl th) && length(fst(strip_forall(concl th))) = 4)) THEN
  (ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
  DISCH_THEN(MP_TAC o SPECL [`r:((A)pan_result)option`; `st:(A,B)pan_state`;
    `crep_state_locals_fupd
       (K (tlc (list_of_seq I (size_of_shape (Comb (MAP SND (vshs:(mlstring#shape)list)))))
               (args:((A)pan_v)list)))
       (crep_dec_clock (t:(A,B)crep_state))`;
    `pan_to_crepProof_ctxt_fc (pan_to_crep_context_funcs (ctxt:(A)pan_to_crep_context))
       (pan_to_crep_context_eids ctxt) (MAP FST (vshs:(mlstring#shape)list)) (MAP SND vshs)
       (list_of_seq I (size_of_shape (Comb (MAP SND vshs))))`]) THEN
  (ANTS_TAC THENL
    [REWRITE_TAC[crep_state_INFO.ri_accfupds; K_THM] THEN ASM_REWRITE_TAC[];
     DISCH_THEN(X_CHOOSE_THEN `r1:((A)crep_result)option`
       (X_CHOOSE_THEN `t1:(A,B)crep_state` STRIP_ASSUME_TAC))]) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  FIRST_ASSUM(fun th -> if is_eq(concl th) && is_comb(lhs(concl th)) &&
     (try fst(dest_const(rator(lhs(concl th)))) = "crep_evaluate" with Failure _ -> false)
     then REWRITE_TAC[th] else NO_TAC) THEN
  REWRITE_TAC[case_def "prod"] THEN
  NAMED_CASES_ON "r" ["";"pr"] THENL [ALL_TAC; QCASES_ON "pr"];;

(* the return variables of a call are distinct *)

let PP2CAUX_WRAP_RT_DISTINCT_TAC : tactic =
  FIRST_ASSUM(fun th ->
    if is_eq(concl th) &&
       (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "wrap_rt" with Failure _ -> false) &&
       is_comb(rhs(concl th)) && fst(dest_const(rator(rhs(concl th)))) = "SOME"
    then MATCH_ACCEPT_TAC(MATCH_MP no_overlap_wrap_rt_some_all_distinct
           (CONJ (CONJUNCT1(REWRITE_RULE[pan_to_crepProof_locals_rel_def]
                    (ASSUME `pan_to_crepProof_locals_rel (ctxt:(A)pan_to_crep_context)
                               (pan_state_locals (s:(A,B)pan_state))
                               (crep_state_locals (t:(A,B)crep_state))`))) th))
    else NO_TAC);;

let PP2CAUX_valid_local = prove
 (`pan_is_valid_value (s:(A,FFI)pan_state) panLang_Local v value <=>
   ?w. FLOOKUP (pan_state_locals s) v = SOME w /\ shape_of value = shape_of w`,
  REWRITE_TAC[is_valid_value_simps] THEN
  QCASES_ON "FLOOKUP (pan_state_locals (s:(A,FFI)pan_state)) v" THEN
  REWRITE_TAC[case_def "option"; distinctness "option"; injectivity "option"] THEN
  MESON_TAC[]);;

let PP2CAUX_excp_rel_none = prove
 (`excp_rel (ceids:(B,C)fmap) (seids:(B,D)fmap) /\ FLOOKUP ceids e = NONE ==>
   FLOOKUP seids e = NONE`,
  REWRITE_TAC[excp_rel_def; flookup_thm] THEN MESON_TAC[]);;

let PP2CAUX_excp_rel_inj = prove
 (`excp_rel (ceids:(B,C)fmap) (seids:(B,D)fmap) /\
   FLOOKUP ceids e = SOME n /\ FLOOKUP ceids e' = SOME n' /\ ~(e = e') ==> ~(n = n')`,
  REWRITE_TAC[excp_rel_def] THEN MESON_TAC[]);;

(* the pan result of a call with a return variable *)

let PP2CAUX_RET_PAN_TAC : tactic =
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
    rand(concl th) = `res:((A)pan_result)option,s1:(A,B)pan_state`)) THEN
  REWRITE_TAC[case_def "option"; case_def "pan_result"] THEN
  REPEAT COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  TRY (FIRST_X_ASSUM(MP_TAC o check (fun th ->
         concl th = `~(SOME (pan_Error:(A)pan_result) = SOME pan_Error)`)) THEN
       REWRITE_TAC[] THEN NO_TAC);;

(* the callee returned into the variable rt (crep return variables wr1)  *)

let PP2CAUX_RET_TAC : tactic =
  PP2CAUX_RET_PAN_TAC THEN
  RENAME_TAC ["pan_is_valid_value s panLang_Local rt retv"] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `w:(A)pan_v` STRIP_ASSUME_TAC o REWRITE_RULE[PP2CAUX_valid_local] o
    check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "pan_is_valid_value"
                     with Failure _ -> false)) THEN
  MP_TAC(MATCH_MP locals_rel_lookup_ctxt (CONJ
    (ASSUME `pan_to_crepProof_locals_rel (ctxt:(A)pan_to_crep_context)
               (pan_state_locals (s:(A,B)pan_state)) (crep_state_locals (t:(A,B)crep_state))`)
    (ASSUME `FLOOKUP (pan_state_locals (s:(A,B)pan_state)) rt = SOME (w:(A)pan_v)`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `nsr:num list` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP PP2CAUX_wrap_rt_some o check (fun th -> is_eq(concl th) &&
    (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "wrap_rt" with Failure _ -> false))) THEN
  ASM_REWRITE_TAC[injectivity "option"; PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> free_in `r1:((A)crep_result)option` (concl th) &&
    not (is_eq (concl th) &&
         (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "crep_evaluate"
          with Failure _ -> false)))) THEN
  REWRITE_TAC[case_def "option"; case_def "pan_result"] THEN DISCH_THEN SUBST_ALL_TAC THEN
  REWRITE_TAC[case_def "option"; case_def "crep_result"] THEN
  (SUBGOAL_THEN `LENGTH (flatten (retv:(A)pan_v)) = LENGTH (nsr:num list)` SUBST1_TAC THENL
    [MP_TAC(ISPEC `retv:(A)pan_v` length_flatten_eq_size_of_shape) THEN
     MP_TAC(ISPEC `w:(A)pan_v` length_flatten_eq_size_of_shape) THEN
     ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[];
     ALL_TAC]) THEN
  ASM_REWRITE_TAC[case_def "option"; PAIR_EQ] THEN PP2CAUX_EXISTS_EQ_TAC THEN
  REWRITE_TAC[case_def "option"; kvar_simps; pan_set_var_def; pan_state_INFO.ri_accfupds;
              crep_state_INFO.ri_accfupds; K_THM] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PP2CAUX_code_rel_ctxt_fc; ctxt_fc_eids_eq]) THEN
  QPAT_X_ASSUM "pan_to_crepProof_state_rel st t1" MP_TAC THEN
  REWRITE_TAC[pan_to_crepProof_state_rel_def] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[pan_state_INFO.ri_accfupds; crep_state_INFO.ri_accfupds; K_THM] THEN
  MATCH_MP_TAC local_rel_le_zip_update_preserved THEN
  MAP_EVERY EXISTS_TAC [`w:(A)pan_v`; `shape_of (w:(A)pan_v)`] THEN ASM_REWRITE_TAC[];;

(* an exception that no handler of the call catches; the handler's       *)
(* exception id h0 is unknown on both sides (FLOOKUP eshapes h0 = NONE)    *)

let PP2CAUX_EXN_NOHDL_TAC : tactic =
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
    rand(concl th) = `res:((A)pan_result)option,s1:(A,B)pan_state`)) THEN
  REWRITE_TAC[case_def "option"; case_def "pan_result"; case_def "prod"] THEN
  COND_CASES_TAC THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) && is_var(lhs(concl th)))) THEN
    ASM_REWRITE_TAC[case_def "option"; PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      concl th = `~(SOME (pan_Error:(A)pan_result) = SOME pan_Error)`)) THEN
    REWRITE_TAC[];
    DISCH_TAC THEN PP2CAUX_TAIL_CREP_TAC];;

(* entering an exception handler: exp_hdl copies the exception value from *)
(* the globals into the handler variable's crep variables                  *)

let PP2CAUX_exp_hdl_eval = prove
 (`!(ctxt:(A)pan_to_crep_context) (sl:(mlstring,(A)pan_v)fmap) (tl:(num,(A)word_lab)fmap)
    evar w exn (t1:(A,B)crep_state).
    pan_to_crepProof_locals_rel ctxt sl tl /\
    FLOOKUP sl evar = SOME w /\ shape_of exn = shape_of w /\
    (1 <= size_of_shape (shape_of exn) ==>
     globals_lookup t1 exn = SOME (flatten exn) /\ size_of_shape (shape_of exn) <= 32) ==>
    ?ns. FLOOKUP (pan_to_crep_context_vars ctxt) evar = SOME (shape_of w,ns) /\
         crep_evaluate (exp_hdl (pan_to_crep_context_vars ctxt) evar,
                        crep_state_locals_fupd (K tl) t1) =
         (NONE,crep_state_locals_fupd (K (tl |++ ZIP ns (flatten exn))) t1) /\
         pan_to_crepProof_locals_rel ctxt (sl |+ (evar,exn)) (tl |++ ZIP ns (flatten exn))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(MATCH_MP locals_rel_lookup_ctxt (CONJ
    (ASSUME `pan_to_crepProof_locals_rel (ctxt:(A)pan_to_crep_context)
               (sl:(mlstring,(A)pan_v)fmap) (tl:(num,(A)word_lab)fmap)`)
    (ASSUME `FLOOKUP (sl:(mlstring,(A)pan_v)fmap) evar = SOME w`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `ns:num list` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `ns:num list` THEN ASM_REWRITE_TAC[] THEN
  (SUBGOAL_THEN `ALL_DISTINCT (ns:num list)` ASSUME_TAC THENL
    [ACCEPT_TAC(MATCH_MP all_distinct_flookup_all_distinct (CONJ
       (CONJUNCT1(REWRITE_RULE[pan_to_crepProof_locals_rel_def]
          (ASSUME `pan_to_crepProof_locals_rel (ctxt:(A)pan_to_crep_context)
                     (sl:(mlstring,(A)pan_v)fmap) (tl:(num,(A)word_lab)fmap)`)))
       (ASSUME `FLOOKUP (pan_to_crep_context_vars (ctxt:(A)pan_to_crep_context)) evar =
                SOME (shape_of (w:(A)pan_v),ns)`)));
     ALL_TAC]) THEN
  (SUBGOAL_THEN `LENGTH (ns:num list) = size_of_shape (shape_of (exn:(A)pan_v))` ASSUME_TAC THENL
    [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC length_flatten_eq_size_of_shape THEN
     FIRST_ASSUM ACCEPT_TAC;
     ALL_TAC]) THEN
  CONJ_TAC THENL [ALL_TAC;
    MATCH_MP_TAC local_rel_le_zip_update_preserved THEN
    MAP_EVERY EXISTS_TAC [`w:(A)pan_v`; `shape_of (w:(A)pan_v)`] THEN ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[exp_hdl_def;
    ASSUME `FLOOKUP (pan_to_crep_context_vars (ctxt:(A)pan_to_crep_context)) evar =
            SOME (shape_of (w:(A)pan_v),ns)`; case_def "option"; case_def "prod"] THEN
  MP_TAC(ISPECL [`ns:num list`;
                 `crep_state_locals_fupd (K (tl:(num,(A)word_lab)fmap)) (t1:(A,B)crep_state)`;
                 `word 0:5 word`] evaluate_seq_assign_load_globals) THEN
  REWRITE_TAC[crep_state_INFO.ri_accfupds; K_THM; WORD_ADD_0; VAL_WORD_0; ADD_CLAUSES] THEN
  (ASM_CASES_TAC `size_of_shape (shape_of (exn:(A)pan_v)) = 0` THENL
    [SUBGOAL_THEN `ns:num list = []` SUBST_ALL_TAC THENL
      [ASM_MESON_TAC[LENGTH_EQ_NIL]; ALL_TAC] THEN
     SUBGOAL_THEN `flatten (exn:(A)pan_v) = []` SUBST1_TAC THENL
      [REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN
       MP_TAC(ISPEC `exn:(A)pan_v` length_flatten_eq_size_of_shape) THEN
       ASM_REWRITE_TAC[] THEN SIMP_TAC[];
       ALL_TAC] THEN
     REWRITE_TAC[ALL_DISTINCT; MEM; LENGTH; LIST_OF_SEQ; MAP; ZIP; ARITH] THEN
     DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[crep_state_INFO.ri_fupdfupds; o_DEF; K_THM] THEN
     REWRITE_TAC[K_DEF];
     ALL_TAC]) THEN
  (SUBGOAL_THEN `globals_lookup (t1:(A,B)crep_state) (exn:(A)pan_v) = SOME (flatten exn) /\
                 size_of_shape (shape_of exn) <= 32` STRIP_ASSUME_TAC THENL
    [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[globals_lookup_def]) THEN
  (ANTS_TAC THENL
    [REPEAT CONJ_TAC THENL
      [FIRST_ASSUM ACCEPT_TAC;
       UNDISCH_TAC `size_of_shape (shape_of (exn:(A)pan_v)) <= 32` THEN
       UNDISCH_TAC `LENGTH (ns:num list) = size_of_shape (shape_of (exn:(A)pan_v))` THEN
       ARITH_TAC;
       X_GEN_TAC `n:num` THEN DISCH_TAC THEN
       MP_TAC(ISPECL [`ns:num list`; `FLOOKUP (tl:(num,(A)word_lab)fmap)`;
                      `flatten (w:(A)pan_v)`; `n:num`] opt_mmap_mem_func) THEN
       ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[distinctness "option"];
       X_GEN_TAC `n:5 word` THEN
       REWRITE_TAC[ASSUME `LENGTH (ns:num list) = size_of_shape (shape_of (exn:(A)pan_v))`] THEN
       DISCH_TAC THEN
       MP_TAC(ISPECL [`list_of_seq (\x. (word x):5 word) (size_of_shape (shape_of (exn:(A)pan_v)))`;
                      `FLOOKUP (crep_state_globals (t1:(A,B)crep_state))`;
                      `flatten (exn:(A)pan_v)`; `n:5 word`] opt_mmap_mem_func) THEN
       ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[distinctness "option"]];
     ALL_TAC]) THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[crep_state_INFO.ri_fupdfupds; o_DEF; K_THM] THEN REWRITE_TAC[K_DEF] THEN
  SUBGOAL_THEN `MAP (\n. THE (FLOOKUP (crep_state_globals (t1:(A,B)crep_state)) n))
                  (list_of_seq (\x. (word x):5 word) (LENGTH (ns:num list))) = flatten (exn:(A)pan_v)`
    (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[ASSUME `LENGTH (ns:num list) = size_of_shape (shape_of (exn:(A)pan_v))`] THEN
  QPAT_X_ASSUM "OPT_MMAP (FLOOKUP (crep_state_globals t1)) _ = _"
    (MP_TAC o AP_TERM `MAP (THE:((A)word_lab)option->(A)word_lab)` o REWRITE_RULE[opt_mmap_eq_some]) THEN
  REWRITE_TAC[MAP_MAP_o; map_the_some_cancel] THEN
  REWRITE_TAC[o_DEF] THEN DISCH_THEN ACCEPT_TAC);;

let PP2CAUX_wrap_rt_none = prove
 (`!(w:(A)pan_v) (ns:num list).
     wrap_rt (SOME (shape_of w,ns)) = NONE /\ LENGTH ns = LENGTH (flatten w) ==> F`,
  GEN_TAC THEN QCASES_ON "w" THEN
  REWRITE_TAC[shape_of_def; wrap_rt_def; flatten_def] THEN
  TRY (QCASES_ON "a:(A)word_lab") THEN REWRITE_TAC[shape_of_def; flatten_def] THEN
  GEN_TAC THEN QCASES_ON "ns" THEN
  REWRITE_TAC[case_def "option"; case_def "prod"; case_def "shape"; case_def "list";
              distinctness "option"; LENGTH; NOT_SUC]);;

(* a call that should return into rt, where wrap_rt finds no crep        *)
(* variables for rt: impossible once the callee returns                  *)

let PP2CAUX_RET_WRAPNONE_TAC : tactic =
  PP2CAUX_RET_PAN_TAC THEN
  RENAME_TAC ["pan_is_valid_value s panLang_Local rt retv"] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `w:(A)pan_v` STRIP_ASSUME_TAC o REWRITE_RULE[PP2CAUX_valid_local] o
    check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "pan_is_valid_value"
                     with Failure _ -> false)) THEN
  MP_TAC(MATCH_MP locals_rel_lookup_ctxt (CONJ
    (ASSUME `pan_to_crepProof_locals_rel (ctxt:(A)pan_to_crep_context)
               (pan_state_locals (s:(A,B)pan_state)) (crep_state_locals (t:(A,B)crep_state))`)
    (ASSUME `FLOOKUP (pan_state_locals (s:(A,B)pan_state)) rt = SOME (w:(A)pan_v)`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `nsr:num list` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
    (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "wrap_rt" with Failure _ -> false))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC(TAUT `F ==> p`) THEN MATCH_MP_TAC PP2CAUX_wrap_rt_none THEN
  MAP_EVERY EXISTS_TAC [`w:(A)pan_v`; `nsr:num list`] THEN ASM_REWRITE_TAC[];;

(* an exception caught by the call's handler h0 (crep id neid)          *)

let PP2CAUX_EXN_HDL_TAC : tactic =
  RENAME_TAC ["pan_evaluate (prog,_) = SOME (pan_Exception eid exn),st"] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> free_in `r1:((A)crep_result)option` (concl th) &&
    not (is_eq (concl th) &&
         (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "crep_evaluate"
          with Failure _ -> false)))) THEN
  REWRITE_TAC[case_def "option"; case_def "pan_result"; ctxt_fc_eids_eq] THEN
  TOP_CASE_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN RVEQ_TAC THEN
  RENAME_TAC ["FLOOKUP (pan_to_crep_context_eids ctxt) eid = SOME n"] THEN
  REWRITE_TAC[case_def "option"; case_def "crep_result"] THEN
  ASM_CASES_TAC `eid:mlstring = h0` THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `eid:mlstring = h0`)) THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th =
      `FLOOKUP (pan_to_crep_context_eids (ctxt:(A)pan_to_crep_context)) eid = SOME (neid:A word)`)) THEN
    ASM_REWRITE_TAC[injectivity "option"] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
      rand(concl th) = `res:((A)pan_result)option,s1:(A,B)pan_state`)) THEN
    REWRITE_TAC[case_def "option"; case_def "pan_result"] THEN
    (TOP_CASE_TAC THENL [PP2CAUX_PAN_ERR_TAC; ALL_TAC]) THEN
    (COND_CASES_TAC THENL [ALL_TAC; PP2CAUX_PAN_ERR_TAC]) THEN
    DISCH_TAC THEN
    FIRST_X_ASSUM(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) MP_TAC) THEN
    REWRITE_TAC[PP2CAUX_valid_local] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:(A)pan_v` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`ctxt:(A)pan_to_crep_context`; `pan_state_locals (s:(A,B)pan_state)`;
                   `crep_state_locals (t:(A,B)crep_state)`; `h1:mlstring`; `w:(A)pan_v`;
                   `exn:(A)pan_v`; `t1:(A,B)crep_state`] PP2CAUX_exp_hdl_eval) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `nse:num list` STRIP_ASSUME_TAC) THEN
    ONCE_REWRITE_TAC[crep_evaluate_def] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[case_def "prod"] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`args:((A)pan_v)list`; `rsh:shape`; `prog:(A)panLang_prog`;
        `slc (vshs:(mlstring#shape)list) (args:((A)pan_v)list)`; `eid:mlstring`;
        `h2:(A)panLang_prog`; `h1:mlstring`; `exn:(A)pan_v`; `st:(A,B)pan_state`] o
      check (fun th -> is_forall(concl th) && length(fst(strip_forall(concl th))) = 9)) THEN
    (ANTS_TAC THENL [ASM_REWRITE_TAC[PP2CAUX_valid_local] THEN ASM_MESON_TAC[]; ALL_TAC]) THEN
    DISCH_THEN(MP_TAC o SPECL [`res:((A)pan_result)option`; `s1:(A,B)pan_state`;
      `crep_state_locals_fupd (K (crep_state_locals (t:(A,B)crep_state) |++
          ZIP nse (flatten (exn:(A)pan_v)))) (t1:(A,B)crep_state)`;
      `ctxt:(A)pan_to_crep_context`]) THEN
    (ANTS_TAC THENL
      [RULE_ASSUM_TAC(REWRITE_RULE[PP2CAUX_code_rel_ctxt_fc; ctxt_fc_eids_eq]) THEN
       REWRITE_TAC[pan_set_var_def; pan_state_INFO.ri_accfupds; crep_state_INFO.ri_accfupds;
                   K_THM] THEN
       ASM_REWRITE_TAC[] THEN
       QPAT_X_ASSUM "pan_to_crepProof_state_rel st t1" MP_TAC THEN
       REWRITE_TAC[pan_to_crepProof_state_rel_def; pan_state_INFO.ri_accfupds;
                   crep_state_INFO.ri_accfupds; K_THM] THEN SIMP_TAC[] THEN
       DISCH_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[pan_set_var_def; pan_state_INFO.ri_accfupds;
         K_THM; case_def "option"; case_def "prod"]) THEN
       ASM_REWRITE_TAC[pan_state_INFO.ri_fupdfupds; o_DEF; K_THM] THEN REWRITE_TAC[K_DEF] THEN
       ASM_REWRITE_TAC[];
       REWRITE_TAC[]]);
    (SUBGOAL_THEN `~(n:A word = neid)` ASSUME_TAC THENL
      [MP_TAC(INST [`pan_to_crep_context_eids (ctxt:(A)pan_to_crep_context)`,`ceids:(mlstring,A word)fmap`;
                    `pan_state_eshapes (s:(A,B)pan_state)`,`seids:(mlstring,shape)fmap`;
                    `eid:mlstring`,`e:mlstring`; `h0:mlstring`,`e':mlstring`;
                    `n:A word`,`n:A word`; `neid:A word`,`n':A word`]
         (INST_TYPE [`:mlstring`,`:B`; `:A word`,`:C`; `:shape`,`:D`] PP2CAUX_excp_rel_inj)) THEN
       ASM_REWRITE_TAC[];
       ALL_TAC]) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
      rand(concl th) = `res:((A)pan_result)option,s1:(A,B)pan_state`)) THEN
    ASM_REWRITE_TAC[case_def "option"; case_def "pan_result"; PAIR_EQ] THEN
    STRIP_TAC THEN RVEQ_TAC THEN
    REWRITE_TAC[PAIR_EQ] THEN PP2CAUX_EXISTS_EQ_TAC THEN
    REWRITE_TAC[case_def "option"; case_def "pan_result"] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[PP2CAUX_code_rel_ctxt_fc; ctxt_fc_eids_eq]) THEN
    ASM_REWRITE_TAC[pan_empty_locals_def; crep_empty_locals_def; pan_state_INFO.ri_accfupds;
                    crep_state_INFO.ri_accfupds; K_THM; PP2CAUX_globals_lookup_locals_fupd] THEN
    QPAT_X_ASSUM "pan_to_crepProof_state_rel st t1" MP_TAC THEN
    REWRITE_TAC[pan_to_crepProof_state_rel_def] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[pan_state_INFO.ri_accfupds; crep_state_INFO.ri_accfupds; K_THM;
                    case_def "option"]];;

(* the results of a call, given the tactics for Return and Exception     *)

let PP2CAUX_CALL_RES_TAC (rett:tactic) (exnt:tactic) : tactic =
  PP2CAUX_CALL_COMMON_TAC THENL
   [PP2CAUX_CALL_PAN_RES_TAC; PP2CAUX_CALL_PAN_RES_TAC; PP2CAUX_TAIL_CREP_TAC;
    PP2CAUX_CALL_PAN_RES_TAC; PP2CAUX_CALL_PAN_RES_TAC; rett; exnt; PP2CAUX_TAIL_CREP_TAC];;

let PP2CAUX_HDL_EIDS_SPLIT_TAC : tactic =
  PAIR_CASES_ON `h:mlstring#mlstring#(A)panLang_prog` THEN REWRITE_TAC[case_def "prod"] THEN
  DISJ_CASES_THEN2 (fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th)
    (X_CHOOSE_THEN `neid:A word` (fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th))
    (ISPEC `FLOOKUP (pan_to_crep_context_eids (ctxt:(A)pan_to_crep_context)) h0`
       (cases "option")) THEN
  REWRITE_TAC[case_def "option"];;

let PP2CAUX_ESHAPES_NONE_TAC : tactic =
  SUBGOAL_THEN `FLOOKUP (pan_state_eshapes (s:(A,B)pan_state)) h0 = NONE` ASSUME_TAC THENL
   [ACCEPT_TAC(MATCH_MP PP2CAUX_excp_rel_none (CONJ
      (ASSUME `excp_rel (pan_to_crep_context_eids (ctxt:(A)pan_to_crep_context))
                 (pan_state_eshapes (s:(A,B)pan_state))`)
      (ASSUME `FLOOKUP (pan_to_crep_context_eids (ctxt:(A)pan_to_crep_context)) h0 = NONE`)));
    ALL_TAC];;

let PP2CAUX_WR_DISTINCT_TAC : tactic =
  SUBGOAL_THEN `ALL_DISTINCT (wr1:num list)` ASSUME_TAC THENL
   [PP2CAUX_WRAP_RT_DISTINCT_TAC; ALL_TAC];;

(* HOL4: Resume pc_compile_correct[Call] for caltyp = SOME (SOME (rk,rt),hdl) *)
(* and the Call_Ret cases                                                    *)

let PP2CAUX_pc_Call_ret = prove
 (PP2CAUX_call_stmt_ret,
REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FS[localised_prog_def] THEN
  QPAT_X_ASSUM "pan_evaluate (panLang_Call _ _ _,_) = _" MP_TAC THEN
  ONCE_REWRITE_TAC[pan_evaluate_def] THEN
  (TOP_CASE_TAC THENL [PP2CAUX_PAN_ERR_TAC; ALL_TAC]) THEN
  (TOP_CASE_TAC THENL [PP2CAUX_PAN_ERR_TAC; ALL_TAC]) THEN
  PAIR_CASES_ON `a':(A)panLang_prog#(mlstring,(A)pan_v)fmap#shape` THEN
  REWRITE_TAC[case_def "prod"] THEN
  RENAME_TAC ["OPT_MMAP (pan_eval s) argexps = SOME args";
              "pan_lookup_code (pan_state_code s) fname args = SOME (prog,newlocals,rsh)"] THEN
  QCASES_ON "rk" THEN RULE_ASSUM_TAC(REWRITE_RULE[case_def "varkind"]) THEN
  TRY(FIRST_ASSUM(CONTR_TAC o check (fun th -> concl th = `F`)) THEN NO_TAC) THEN
  MP_TAC(ISPECL [`s:(A,B)pan_state`; `t:(A,B)crep_state`; `ctxt:(A)pan_to_crep_context`;
                 `argexps:((A)panLang_exp)list`; `args:((A)pan_v)list`; `fname:mlstring`;
                 `prog:(A)panLang_prog`; `newlocals:(mlstring,(A)pan_v)fmap`; `rsh:shape`]
    PP2CAUX_call_setup) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `vshs:(mlstring#shape)list` (X_CHOOSE_THEN `ns:num list`
    (X_CHOOSE_THEN `nctxt:(A)pan_to_crep_context` STRIP_ASSUME_TAC))) THEN
  ONCE_REWRITE_TAC[pan_to_crep_compile_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[case_def "option"; case_def "prod"] THEN
  MAP_EVERY (fun v -> FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
     lhs(concl th) = v)))
   [`nctxt:(A)pan_to_crep_context`; `ns:num list`; `newlocals:(mlstring,(A)pan_v)fmap`] THEN
  DISJ_CASES_THEN2 (fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th)
    (X_CHOOSE_THEN `wr:shape#num list` (fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th))
    (ISPEC `wrap_rt (FLOOKUP (pan_to_crep_context_vars (ctxt:(A)pan_to_crep_context)) rt)`
       (cases "option")) THEN
  REWRITE_TAC[case_def "option"] THENL
   [(* no crep variables for rt *)
    NAMED_CASES_ON "hdl" ["";"h"] THEN REWRITE_TAC[case_def "option"] THENL
     [PP2CAUX_CALL_RES_TAC PP2CAUX_RET_WRAPNONE_TAC PP2CAUX_TAIL_CREP_TAC;
      PP2CAUX_HDL_EIDS_SPLIT_TAC THENL
       [PP2CAUX_ESHAPES_NONE_TAC THEN
        PP2CAUX_CALL_RES_TAC PP2CAUX_RET_WRAPNONE_TAC PP2CAUX_EXN_NOHDL_TAC;
        PP2CAUX_CALL_RES_TAC PP2CAUX_RET_WRAPNONE_TAC PP2CAUX_EXN_HDL_TAC]];
    (* rt has the crep variables wr1 *)
    PAIR_CASES_ON `wr:shape#num list` THEN REWRITE_TAC[case_def "prod"] THEN
    NAMED_CASES_ON "hdl" ["";"h"] THEN REWRITE_TAC[case_def "option"] THENL
     [PP2CAUX_WR_DISTINCT_TAC THEN
      PP2CAUX_CALL_RES_TAC PP2CAUX_RET_TAC PP2CAUX_TAIL_CREP_TAC;
      PP2CAUX_HDL_EIDS_SPLIT_TAC THENL
       [PP2CAUX_WR_DISTINCT_TAC THEN PP2CAUX_ESHAPES_NONE_TAC THEN
        PP2CAUX_CALL_RES_TAC PP2CAUX_RET_TAC PP2CAUX_EXN_NOHDL_TAC;
        PP2CAUX_WR_DISTINCT_TAC THEN
        PP2CAUX_CALL_RES_TAC PP2CAUX_RET_TAC PP2CAUX_EXN_HDL_TAC]]]);;

(* the callee returned into the call's temporaries rts *)

let PP2CAUX_RETN_TAC : tactic =
  PP2CAUX_RET_PAN_TAC THEN
  RENAME_TAC ["pan_evaluate (prog,_) = SOME (pan_Return retv),st"] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> free_in `r1:((A)crep_result)option` (concl th) &&
    not (is_eq (concl th) &&
         (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "crep_evaluate"
          with Failure _ -> false)))) THEN
  REWRITE_TAC[case_def "option"; case_def "pan_result"] THEN DISCH_THEN SUBST_ALL_TAC THEN
  REWRITE_TAC[case_def "option"; case_def "crep_result"] THEN
  (SUBGOAL_THEN `is_wf_shape ([]:(mlstring#struct_info)list) (shape_of (retv:(A)pan_v))`
     ASSUME_TAC THENL
    [MP_TAC(INST [`slc (vshs:(mlstring#shape)list) (args:((A)pan_v)list)`,
                  `newlocals:(mlstring,(A)pan_v)fmap`;
                  `prog:(A)panLang_prog`,`p2:(A)panLang_prog`; `prog:(A)panLang_prog`,`p:(A)panLang_prog`;
                  `pan_Return (retv:(A)pan_v)`,`v:(A)pan_result`; `st:(A,B)pan_state`,`s':(A,B)pan_state`;
                  `crep_state_locals (t:(A,B)crep_state)`,`t_locs:(num,(A)word_lab)fmap`;
                  `shape_of (retv:(A)pan_v)`,`rsh:shape`]
       (INST_TYPE [`:B`,`:FFI`; `:A`,`:B`] evaluate_shape_invariant_ret_inst2)) THEN
     ASM_REWRITE_TAC[case_def "pan_result"] THEN MESON_TAC[is_wf_shape_v_nil];
     ALL_TAC]) THEN
  (SUBGOAL_THEN `LENGTH (flatten (retv:(A)pan_v)) = LENGTH (rts:num list)` SUBST1_TAC THENL
    [MP_TAC(ISPEC `retv:(A)pan_v` length_flatten_eq_size_of_shape) THEN ASM_REWRITE_TAC[] THEN
     DISCH_THEN SUBST1_TAC THEN
     FIRST_X_ASSUM(MP_TAC o SPECL [`vshs:(mlstring#shape)list`; `shape_of (retv:(A)pan_v)`] o
       check (fun th -> is_forall(concl th) && length(fst(strip_forall(concl th))) = 2 &&
              free_in `rts:num list` (concl th))) THEN
     ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
     ALL_TAC]) THEN
  REWRITE_TAC[] THEN
  DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_TAC `vv:((A)word_lab)list`)
    (ISPEC `OPT_MMAP (FLOOKUP (crep_state_locals (t:(A,B)crep_state))) (rts:num list)`
       (cases "option")) THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg(concl th) &&
      free_in `rts:num list` (concl th))) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[case_def "option"; PAIR_EQ] THEN PP2CAUX_EXISTS_EQ_TAC THEN
  REWRITE_TAC[case_def "option"; pan_state_INFO.ri_accfupds;
              crep_state_INFO.ri_accfupds; K_THM] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PP2CAUX_code_rel_ctxt_fc; ctxt_fc_eids_eq]) THEN
  QPAT_X_ASSUM "pan_to_crepProof_state_rel st t1" MP_TAC THEN
  REWRITE_TAC[pan_to_crepProof_state_rel_def] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[pan_state_INFO.ri_accfupds; crep_state_INFO.ri_accfupds; K_THM] THEN
  MATCH_MP_TAC PP2CAUX_locals_rel_gt_vmax_zip THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `retv:(A)pan_v` length_flatten_eq_size_of_shape) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`vshs:(mlstring#shape)list`; `shape_of (retv:(A)pan_v)`] o
    check (fun th -> is_forall(concl th) && length(fst(strip_forall(concl th))) = 2 &&
           free_in `rts:num list` (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];;

(* the Call case SOME (NONE,hdl) at the crep level: the call itself with *)
(* return variables rts (declared by the compiled program around it)     *)

let PP2CAUX_call_retnone_core_stmt =
  let tm = PP2CAUX_call_stmt_retnone in
  let vs1,bod1 = strip_forall tm in
  let ihs,rest = dest_imp bod1 in
  let vs2,bod2 = strip_forall rest in
  let hyps,concl = dest_imp bod2 in
  let rts = `rts:num list` in
  let ct2 = CASE_TERM
   `(match hdl:(mlstring#mlstring#(A)panLang_prog)option with
       NONE -> NONE
     | SOME (eid,evar,p) ->
         (match FLOOKUP (pan_to_crep_context_eids (ctxt:(A)pan_to_crep_context)) eid with
            NONE -> NONE
          | SOME neid ->
              SOME (neid,crep_Seq (exp_hdl (pan_to_crep_context_vars ctxt) evar)
                                  (pan_to_crep_compile ctxt p))))` in
  let call = mk_icomb(mk_icomb(mk_icomb(`crep_Call:((num)list#(A word#(A)crep_prog)option)option->
                                           mlstring->((A)crep_exp)list->(A)crep_prog`,
                    mk_icomb(`SOME:(num)list#(A word#(A)crep_prog)option->((num)list#(A word#(A)crep_prog)option)option`,
                             mk_pair(rts,ct2))),
                    `fname:mlstring`),
                    `FLAT (MAP FST (MAP (pan_to_crep_compile_exp (ctxt:(A)pan_to_crep_context))
                                      (argexps:((A)panLang_exp)list)))`) in
  let old = find_term (fun t -> try fst(dest_const(fst(strip_comb t))) = "pan_to_crep_compile"
                                    && is_comb t with Failure _ -> false) concl in
  let concl' = subst [call,old] concl in
  let extra = list_mk_conj
   [`ALL_DISTINCT (rts:num list)`;
    `!k. MEM k (rts:num list) ==> pan_to_crep_context_vmax (ctxt:(A)pan_to_crep_context) < k`;
    `~(OPT_MMAP (FLOOKUP (crep_state_locals (t:(A,B)crep_state))) (rts:num list) = NONE)`;
    `!vshs rshape. FLOOKUP (pan_to_crep_context_funcs (ctxt:(A)pan_to_crep_context)) fname =
                   SOME (vshs,rshape) ==> LENGTH (rts:num list) = size_of_shape rshape`] in
  list_mk_forall(vs1, mk_imp(ihs, list_mk_forall(vs2 @ [rts],
    mk_imp(mk_conj(hyps,extra), concl'))));;

let PP2CAUX_call_retnone_core = prove
 (PP2CAUX_call_retnone_core_stmt,
REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FS[localised_prog_def] THEN
  QPAT_X_ASSUM "pan_evaluate (panLang_Call _ _ _,_) = _" MP_TAC THEN
  ONCE_REWRITE_TAC[pan_evaluate_def] THEN
  (TOP_CASE_TAC THENL [PP2CAUX_PAN_ERR_TAC; ALL_TAC]) THEN
  (TOP_CASE_TAC THENL [PP2CAUX_PAN_ERR_TAC; ALL_TAC]) THEN
  PAIR_CASES_ON `a':(A)panLang_prog#(mlstring,(A)pan_v)fmap#shape` THEN
  REWRITE_TAC[case_def "prod"] THEN
  RENAME_TAC ["OPT_MMAP (pan_eval s) argexps = SOME args";
              "pan_lookup_code (pan_state_code s) fname args = SOME (prog,newlocals,rsh)"] THEN
  MP_TAC(ISPECL [`s:(A,B)pan_state`; `t:(A,B)crep_state`; `ctxt:(A)pan_to_crep_context`;
                 `argexps:((A)panLang_exp)list`; `args:((A)pan_v)list`; `fname:mlstring`;
                 `prog:(A)panLang_prog`; `newlocals:(mlstring,(A)pan_v)fmap`; `rsh:shape`]
    PP2CAUX_call_setup) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `vshs:(mlstring#shape)list` (X_CHOOSE_THEN `ns:num list`
    (X_CHOOSE_THEN `nctxt:(A)pan_to_crep_context` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY (fun v -> FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
     lhs(concl th) = v)))
   [`nctxt:(A)pan_to_crep_context`; `ns:num list`; `newlocals:(mlstring,(A)pan_v)fmap`] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  NAMED_CASES_ON "hdl" ["";"h"] THEN REWRITE_TAC[case_def "option"] THENL
   [PP2CAUX_CALL_RES_TAC PP2CAUX_RETN_TAC PP2CAUX_TAIL_CREP_TAC;
    PP2CAUX_HDL_EIDS_SPLIT_TAC THENL
     [PP2CAUX_ESHAPES_NONE_TAC THEN
      PP2CAUX_CALL_RES_TAC PP2CAUX_RETN_TAC PP2CAUX_EXN_NOHDL_TAC;
      PP2CAUX_CALL_RES_TAC PP2CAUX_RETN_TAC PP2CAUX_EXN_HDL_TAC]]);;

(* restoring temporaries above vmax keeps the locals relation *)

let PP2CAUX_locals_rel_res_var_temps = prove
 (`!(ct:(B)pan_to_crep_context) (l:(mlstring,(A)pan_v)fmap) (L:(num,(A)word_lab)fmap)
    rts (ys:(((A)word_lab)option)list).
     pan_to_crepProof_locals_rel ct l L /\
     (!k. MEM k rts ==> pan_to_crep_context_vmax ct < k) /\ LENGTH rts = LENGTH ys ==>
     pan_to_crepProof_locals_rel ct l (FOLDL crep_res_var L (ZIP rts ys))`,
  REWRITE_TAC[pan_to_crepProof_locals_rel_def] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`vn:mlstring`; `pv:(A)pan_v`] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`vn:mlstring`; `pv:(A)pan_v`]) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`ns:num list`; `vs:((A)word_lab)list`] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`ns:num list`; `rts:num list`; `ys:(((A)word_lab)option)list`;
                 `L:(num,(A)word_lab)fmap`] flookup_res_var_distinct) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[distinct_lists_def; GSYM ALL_MEM] THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN DISCH_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[pan_commonProps_ctxt_max_def]) THEN
    ASM_MESON_TAC[ARITH_RULE `~(m < k /\ k <= m)`];
    DISCH_TAC THEN ONCE_REWRITE_TAC[opt_mmap_eq_some] THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[GSYM opt_mmap_eq_some]]);;

(* the relations of pc_compile_correct survive restoring temporaries      *)

let PP2CAUX_res_rel_temps_stmt =
  let vs,bod = strip_forall PP2CAUX_pc_stmt in
  let ex = rand bod in
  let _,cbod = strip_exists ex in
  let cs = tl (conjuncts cbod) in
  let t1 = `t1:(A,B)crep_state` in
  let t1' = `crep_state_locals_fupd
               (K (FOLDL crep_res_var (crep_state_locals (t1:(A,B)crep_state))
                     (ZIP rts (ys:(((A)word_lab)option)list)))) t1` in
  let hyp = list_mk_conj
    ([`!k. MEM k rts ==> pan_to_crep_context_vmax (ctxt:(A)pan_to_crep_context) < k`;
      `LENGTH (rts:num list) = LENGTH (ys:(((A)word_lab)option)list)`] @ cs) in
  let concl = list_mk_conj (map (subst [t1',t1]) cs) in
  list_mk_forall([`ctxt:(A)pan_to_crep_context`; `s1:(A,B)pan_state`;
                  `res:((A)pan_result)option`; `res1:((A)crep_result)option`; t1;
                  `rts:num list`; `ys:(((A)word_lab)option)list`],
                 mk_imp(hyp,concl));;

let PP2CAUX_res_rel_temps = prove
 (PP2CAUX_res_rel_temps_stmt,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[PP2CAUX_globals_lookup_locals_fupd; crep_state_INFO.ri_accfupds; K_THM] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [QPAT_X_ASSUM "pan_to_crepProof_state_rel s1 t1" MP_TAC THEN
    REWRITE_TAC[pan_to_crepProof_state_rel_def; crep_state_INFO.ri_accfupds; K_THM];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> free_in `res:((A)pan_result)option` (concl th))) THEN
  NAMED_CASES_ON "res" ["";"r"] THEN REWRITE_TAC[case_def "option"] THENL
   [STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PP2CAUX_locals_rel_res_var_temps THEN
    ASM_REWRITE_TAC[];
    QCASES_ON "r" THEN REWRITE_TAC[case_def "pan_result"] THEN
    TRY (STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PP2CAUX_locals_rel_res_var_temps THEN
         ASM_REWRITE_TAC[] THEN NO_TAC) THEN
    REWRITE_TAC[PP2CAUX_globals_lookup_locals_fupd]]);;

(* the compiled form of a call SOME (NONE,hdl): the call with return      *)
(* variables rts inside declarations of rts                               *)

let PP2CAUX_rn_call =
  find_term (fun t -> is_comb t &&
    (try fst(dest_const(fst(strip_comb t))) = "crep_Call" with Failure _ -> false))
    PP2CAUX_call_retnone_core_stmt;;

let PP2CAUX_rn_rts =
  `list_of_seq (\x. pan_to_crep_context_vmax (ctxt:(A)pan_to_crep_context) + SUC x)
     (size_of_shape rsh)`;;

let PP2CAUX_rn_prog =
  let call = vsubst [PP2CAUX_rn_rts,`rts:num list`] PP2CAUX_rn_call in
  mk_icomb(mk_icomb(mk_icomb(`nested_decs:(num)list->((A)crep_exp)list->(A)crep_prog->(A)crep_prog`,
             PP2CAUX_rn_rts),
             `REPLICATE (LENGTH (list_of_seq (\x. pan_to_crep_context_vmax
                 (ctxt:(A)pan_to_crep_context) + SUC x) (size_of_shape rsh)))
                 (crep_Const (word 0):(A)crep_exp)`), call);;

(* HOL4: Resume pc_compile_correct[Call] for caltyp = SOME (NONE,hdl)    *)

let PP2CAUX_pc_Call_retnone = prove
 (PP2CAUX_call_stmt_retnone,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  (SUBGOAL_THEN `?vshs prog rsh. FLOOKUP (pan_state_code (s:(A,B)pan_state)) fname =
                   SOME (vshs:(mlstring#shape)list,prog:(A)panLang_prog,rsh:shape)`
     STRIP_ASSUME_TAC THENL
    [QPAT_ASSUM "pan_evaluate (panLang_Call _ _ _,_) = _" MP_TAC THEN
     ONCE_REWRITE_TAC[pan_evaluate_def] THEN
     (TOP_CASE_TAC THENL [PP2CAUX_PAN_ERR_TAC; ALL_TAC]) THEN
     (TOP_CASE_TAC THENL [PP2CAUX_PAN_ERR_TAC; ALL_TAC]) THEN
     DISCH_THEN(K ALL_TAC) THEN
     QPAT_X_ASSUM "pan_lookup_code _ _ _ = _" (MP_TAC o REWRITE_RULE[pan_lookup_code_def]) THEN
     GVS(option_case_eq :: COND_CASE_EQ :: all_case_eqs()) THEN STRIP_TAC THEN
     ASM_MESON_TAC[];
     ALL_TAC]) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP code_rel_imp o
    check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "pan_to_crepProof_code_rel"
                     with Failure _ -> false)) THEN
  DISCH_THEN(MP_TAC o SPECL [`fname:mlstring`; `vshs:(mlstring#shape)list`; `prog:(A)panLang_prog`]) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN
  (SUBGOAL_THEN (mk_eq(`pan_to_crep_compile (ctxt:(A)pan_to_crep_context)
                          (panLang_Call (SOME (NONE,hdl)) fname argexps)`, PP2CAUX_rn_prog))
     SUBST1_TAC THENL
    [ONCE_REWRITE_TAC[pan_to_crep_compile_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
     ASM_REWRITE_TAC[case_def "option"; case_def "prod"] THEN
     NAMED_CASES_ON "hdl" ["";"h"] THEN REWRITE_TAC[case_def "option"] THEN
     PAIR_CASES_ON `h:mlstring#mlstring#(A)panLang_prog` THEN REWRITE_TAC[case_def "prod"] THEN
     TOP_CASE_TAC THEN REWRITE_TAC[case_def "option"];
     ALL_TAC]) THEN
  ABBREV_TAC `rts = list_of_seq (\x. pan_to_crep_context_vmax (ctxt:(A)pan_to_crep_context) + SUC x)
                      (size_of_shape rsh)` THEN
  (SUBGOAL_THEN `ALL_DISTINCT (rts:num list) /\
                 (!k. MEM k rts ==> pan_to_crep_context_vmax (ctxt:(A)pan_to_crep_context) < k) /\
                 LENGTH rts = size_of_shape rsh` STRIP_ASSUME_TAC THENL
    [EXPAND_TAC "rts" THEN
     REWRITE_TAC[ALL_DISTINCT_GENLIST; LENGTH_LIST_OF_SEQ; MEM_GENLIST] THEN
     REPEAT STRIP_TAC THEN ASM_ARITH_TAC;
     ALL_TAC]) THEN
  W(fun (_,w) ->
    let c1 = hd(conjuncts(snd(strip_exists w))) in
    let call = rand(fst(dest_pair(rand(lhand c1)))) in
    MP_TAC(ISPECL [`rts:num list`; `t:(A,B)crep_state`; call] PP2CAUX_nested_decs_zeros)) THEN
  ASM_REWRITE_TAC[] THEN
  W(fun (_,w) -> PAIR_CASES_ON (rand(rator(lhand w)))) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[case_def "prod"] THEN
  DISCH_THEN SUBST1_TAC THEN
  RENAME_TAC ["crep_evaluate (_,_) = q,r"] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (SPECL [`hdl:(mlstring#mlstring#(A)panLang_prog)option`;
      `fname:mlstring`; `argexps:((A)panLang_exp)list`; `s:(A,B)pan_state`]
      PP2CAUX_call_retnone_core) o
    check (fun th -> is_conj(concl th) && is_forall(lhand(concl th)))) THEN
  DISCH_THEN(MP_TAC o SPECL [`res:((A)pan_result)option`; `s1:(A,B)pan_state`;
    `crep_state_locals_fupd
       (K (crep_state_locals (t:(A,B)crep_state) |++
           ZIP (rts:num list) (REPLICATE (size_of_shape rsh) (Word (word 0):(A)word_lab)))) t`;
    `ctxt:(A)pan_to_crep_context`; `rts:num list`]) THEN
  (ANTS_TAC THENL
    [REWRITE_TAC[crep_state_INFO.ri_accfupds; K_THM] THEN ASM_REWRITE_TAC[] THEN
     REPEAT CONJ_TAC THENL
      [QPAT_X_ASSUM "pan_to_crepProof_state_rel s t" MP_TAC THEN
       REWRITE_TAC[pan_to_crepProof_state_rel_def; crep_state_INFO.ri_accfupds; K_THM];
       MATCH_MP_TAC PP2CAUX_locals_rel_gt_vmax_zip THEN
       ASM_REWRITE_TAC[LENGTH_REPLICATE];
       MP_TAC(ISPECL [`rts:num list`; `crep_state_locals (t:(A,B)crep_state)`;
                      `REPLICATE (size_of_shape rsh) (Word (word 0):(A)word_lab)`]
         opt_mmap_some_eq_zip_flookup) THEN
       ASM_REWRITE_TAC[LENGTH_REPLICATE] THEN DISCH_THEN SUBST1_TAC THEN
       REWRITE_TAC[distinctness "option"];
       ASM_REWRITE_TAC[injectivity "option"; PAIR_EQ] THEN MESON_TAC[]];
     ALL_TAC]) THEN
  FIRST_ASSUM(fun th -> if is_eq(concl th) && rand(concl th) = `q:((A)crep_result)option,r:(A,B)crep_state`
    then REWRITE_TAC[th] else NO_TAC) THEN
  REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:((A)crep_result)option` (X_CHOOSE_THEN `t1:(A,B)crep_state`
    STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `q:((A)crep_result)option = r1`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `r:(A,B)crep_state = t1`)) THEN
  MP_TAC(ISPECL [`ctxt:(A)pan_to_crep_context`; `s1:(A,B)pan_state`; `res:((A)pan_result)option`;
                 `q:((A)crep_result)option`; `r:(A,B)crep_state`; `rts:num list`;
                 `MAP (FLOOKUP (crep_state_locals (t:(A,B)crep_state))) (rts:num list)`]
    PP2CAUX_res_rel_temps) THEN
  ASM_REWRITE_TAC[LENGTH_MAP] THEN STRIP_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN PP2CAUX_EXISTS_EQ_TAC THEN ASM_REWRITE_TAC[]);;

(* HOL4: Resume pc_compile_correct[Call] and its sub-cases, combined     *)

let PP2CAUX_pc_Call = prove
 (el 18 PP2CAUX_pc_cases,
  GEN_TAC THEN NAMED_CASES_ON "caltyp" ["";"ct"] THENL
   [ACCEPT_TAC PP2CAUX_pc_Call_none;
    PAIR_CASES_ON `ct:(varkind#mlstring)option#(mlstring#mlstring#(A)panLang_prog)option` THEN
    NAMED_CASES_ON "ct0" ["";"rkrt"] THENL
     [MP_TAC(SPEC `ct1:(mlstring#mlstring#(A)panLang_prog)option` PP2CAUX_pc_Call_retnone) THEN
      REWRITE_TAC[];
      PAIR_CASES_ON `rkrt:varkind#mlstring` THEN
      MP_TAC(SPECL [`rkrt0:varkind`; `rkrt1:mlstring`;
                    `ct1:(mlstring#mlstring#(A)panLang_prog)option`] PP2CAUX_pc_Call_ret) THEN
      REWRITE_TAC[]]]);;

(* HOL4: between Call_Ret_Return and Call_Ret_Exception *)

let not_none_then_some = prove
 (`~((x:A option) = NONE) <=> ?a. x = SOME a`,
  QCASES_ON "x:A option" THEN
  REWRITE_TAC[distinctness "option"; injectivity "option"] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* HOL4 pan_to_crepProofScript.sml lines 4054-4554 without the Call cases:   *)
(* the lemmas before the DecCall case, the DecCall and ExtCall cases of      *)
(* pc_compile_correct (PP2CAUX_pc_DecCall, PP2CAUX_pc_ExtCall) and the       *)
(* MAX_LIST lemmas.  Local helpers are PP2CAUX_A_.                           *)
(* ------------------------------------------------------------------------- *)

(* HOL4 [local] *)

let locals_id_update = prove
 (`crep_state_locals_fupd (K (crep_state_locals (t:(A,B)crep_state))) t = t`,
  REWRITE_TAC[crep_state_component_equality; crep_state_INFO.ri_accfupds; K_THM]);;

(* HOL4's statement binds r vacuously *)

let MAP_SOME_MEM_lemma = prove
 (`MAP (f:A->B option) (FLAT xs) = MAP SOME (FLAT ys) /\
   MEM zs xs /\ MEM z zs ==> ?(r:C) y. f z = SOME y /\ MEM y (FLAT ys)`,
  STRIP_TAC THEN
  SUBGOAL_THEN `MEM ((f:A->B option) z) (MAP SOME (FLAT (ys:(B list)list)))` MP_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_eq o concl)) THEN
    REWRITE_TAC[MEM_MAP; MEM_FLAT] THEN EXISTS_TAC `z:A` THEN REWRITE_TAC[] THEN
    EXISTS_TAC `zs:A list` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[MEM_MAP] THEN MESON_TAC[]]);;

let update_locals_not_vars_eval_mmap = prove
 (`(!n e. MEM e es /\ MEM n (var_cexp e) ==> ~(n = x)) ==>
   OPT_MMAP (crep_eval (crep_state_locals_fupd
                          (K (crep_state_locals (t:(A,B)crep_state) |+ (x,v))) t)) es =
   OPT_MMAP (crep_eval t) es`,
  DISCH_TAC THEN MATCH_MP_TAC OPT_MMAP_CONG THEN REWRITE_TAC[] THEN
  X_GEN_TAC `e:(A)crep_exp` THEN DISCH_TAC THEN
  MATCH_MP_TAC update_locals_not_vars_eval_eq' THEN ASM_MESON_TAC[]);;

let res_var_commutes' = prove
 (`~(n = h) ==>
   crep_res_var (crep_res_var (lc:(K,V)fmap) (h,v)) (n,v') =
   crep_res_var (crep_res_var lc (n,v')) (h,v)`,
  REWRITE_TAC[fmap_eq_flookup; flookup_res_var_thm] THEN DISCH_TAC THEN
  X_GEN_TAC `k:K` THEN REPEAT COND_CASES_TAC THEN ASM_MESON_TAC[]);;

let EL_load_globals = prove
 (`!n m (w:5 word). n < m ==>
     EL n (load_globals w m:((A)crep_exp)list) = LoadGlob (word_add w (word n))`,
  MESON_TAC[el_load_globals_elem]);;

(* HOL4's statement binds w vacuously *)

let eval_distinct_lists_not_affect = prove
 (`!vs (s:(A,B)crep_state) e (w:C) nvals.
     LENGTH vs = LENGTH nvals /\ distinct_lists vs (var_cexp e) ==>
     crep_eval (crep_state_locals_fupd (K (crep_state_locals s |++ ZIP vs nvals)) s) e =
     crep_eval s e`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THENL
   [NAMED_CASES_ON "nvals" ["";"nv nvs"] THEN REWRITE_TAC[LENGTH; NOT_SUC] THEN
    REWRITE_TAC[ZIP; FUPDATE_LIST_THM; locals_id_update];
    ALL_TAC] THEN
  NAMED_CASES_ON "nvals" ["";"nv nvs"] THEN
  REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ; ZIP; FUPDATE_LIST_THM; distinct_lists_def; ALL] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
    [`crep_state_locals_fupd (K (crep_state_locals s |+ (h,nv))) (s:(A,B)crep_state)`;
     `e:(A)crep_exp`; `w:C`; `nvs:((A)word_lab)list`]) THEN
  ASM_REWRITE_TAC[distinct_lists_def; crep_state_INFO.ri_accfupds;
                  crep_state_INFO.ri_fupdfupds; K_THM; K_o_THM] THEN
  DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC update_locals_not_vars_eval_eq' THEN FIRST_ASSUM ACCEPT_TAC);;

(* HOL4's statement binds ws vacuously *)

let opt_mmap_eval_distinct_lists_not_affect' = prove
 (`!es (s:(A,B)crep_state) (ws:C) vs nvals.
     LENGTH vs = LENGTH nvals /\ distinct_lists vs (FLAT (MAP var_cexp es)) ==>
     OPT_MMAP (crep_eval (crep_state_locals_fupd
                            (K (crep_state_locals s |++ ZIP vs nvals)) s)) es =
     OPT_MMAP (crep_eval s) es`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC OPT_MMAP_CONG THEN REWRITE_TAC[] THEN
  X_GEN_TAC `e:(A)crep_exp` THEN DISCH_TAC THEN
  MATCH_MP_TAC eval_distinct_lists_not_affect THEN
  ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[distinct_lists_def; GSYM ALL_MEM; MEM_FLAT; MEM_MAP]) THEN
  REWRITE_TAC[distinct_lists_def; GSYM ALL_MEM] THEN ASM_MESON_TAC[]);;

let evaluate_nested_decs_load_globals = prove
 (CASE_TERM `globals_lookup (s:(A,B)crep_state) (rv:(A)pan_v) = SOME rvs /\
   size_of_shape (shape_of rv) <= 32 /\
   ALL_DISTINCT (vs:num list) /\
   LENGTH vs = size_of_shape (shape_of rv) ==>
   crep_evaluate (nested_decs vs (load_globals (word 0) (size_of_shape (shape_of rv)))
                    (p:(A)crep_prog),s) =
   let (res,s') = crep_evaluate
                    (p,crep_state_locals_fupd (K (crep_state_locals s |++ ZIP vs rvs)) s) in
   (res,crep_state_locals_fupd
          (K (FOLDL crep_res_var (crep_state_locals s')
                (ZIP vs (MAP (FLOOKUP (crep_state_locals s)) vs)))) s')`,
  STRIP_TAC THEN
  MP_TAC(ISPECL [`load_globals (word 0) (size_of_shape (shape_of (rv:(A)pan_v))):((A)crep_exp)list`;
                 `vs:num list`; `s:(A,B)crep_state`; `rvs:((A)word_lab)list`; `p:(A)crep_prog`]
    eval_nested_decs_seq_res_var_eq) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[length_load_globals_eq_read_size; var_cexp_load_globals_empty;
                    distinct_lists_def; GSYM ALL_MEM; MEM] THEN
    QPAT_X_ASSUM "globals_lookup _ _ = _" (MP_TAC o REWRITE_RULE[globals_lookup_def]) THEN
    REWRITE_TAC[opt_mmap_eq_some] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[LIST_EQ; LENGTH_MAP; length_load_globals_eq_read_size; LENGTH_LIST_OF_SEQ] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[EL_MAP; length_load_globals_eq_read_size; LENGTH_LIST_OF_SEQ;
                 EL_load_globals; EL_LIST_OF_SEQ] THEN
    REWRITE_TAC[crep_eval_def; WORD_ADD_0];
    ALL_TAC] THEN
  PAIR_CASES_ON `crep_evaluate (p:(A)crep_prog,
                   crep_state_locals_fupd (K (crep_state_locals s |++ ZIP vs rvs))
                     (s:(A,B)crep_state))` THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[case_def "prod"]);;

(* adding an entry whose variables lie above every variable of a context  *)

let PP2CAUX_A_no_overlap_update = prove
 (`!(fm:(K,B#(num)list)fmap) m ns x a.
   pan_commonProps_no_overlap fm /\
   pan_commonProps_ctxt_max m fm /\ ALL_DISTINCT ns /\ (!z. MEM z ns ==> m < z) ==>
   pan_commonProps_no_overlap (fm |+ (x,(a,ns)))`,
  REWRITE_TAC[pan_commonProps_no_overlap_def; pan_commonProps_ctxt_max_def; FLOOKUP_UPDATE;
              IN_DISJOINT; IN_SET_OF_LIST] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`k1:K`; `a1:B`; `l1:num list`] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[injectivity "option"; PAIR_EQ] THEN ASM_MESON_TAC[];
    MAP_EVERY X_GEN_TAC [`k1:K`; `k2:K`; `a1:B`; `a2:B`; `l1:num list`; `l2:num list`] THEN
    ASM_CASES_TAC `k1:K = x` THEN ASM_CASES_TAC `k2:K = x` THEN
    ASM_REWRITE_TAC[injectivity "option"; PAIR_EQ] THEN
    ASM_MESON_TAC[ARITH_RULE `~(m < z /\ z <= m)`]]);;

let PP2CAUX_A_ctxt_max_update = prove
 (`!m (fm:(K,B#(num)list)fmap) ns k x a.
   pan_commonProps_ctxt_max m fm /\ (!z. MEM z ns ==> z <= m + k) ==>
   pan_commonProps_ctxt_max (m + k) (fm |+ (x,(a,ns)))`,
  REWRITE_TAC[pan_commonProps_ctxt_max_def; FLOOKUP_UPDATE] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`k1:K`; `a1:B`; `l1:num list`] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[injectivity "option"; PAIR_EQ] THENL
   [STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN RES_TAC THEN ASM_ARITH_TAC]);;

(* HOL4 ct with <|vars := X; vmax := Y|> is written as in pan_to_crep's   *)
(* DecCall: pan_to_crep_context_vars_fupd (K X)                            *)
(* (pan_to_crep_context_vmax_fupd (K Y) ct)                                *)

let locals_rel_extend_new_var = prove
 (`!ct (s:(mlstring,(A)pan_v)fmap) (t:(num,(A)word_lab)fmap) v x ns.
     pan_to_crepProof_locals_rel (ct:(B)pan_to_crep_context) s t /\
     is_wf_shape ([]:(mlstring#struct_info)list) (shape_of v) /\
     ALL_DISTINCT ns /\
     (!x. MEM x ns ==> pan_to_crep_context_vmax ct < x /\
                       x <= pan_to_crep_context_vmax ct + size_of_shape (shape_of v)) /\
     LENGTH ns = size_of_shape (shape_of v) ==>
     pan_to_crepProof_locals_rel
       (pan_to_crep_context_vars_fupd
          (K (pan_to_crep_context_vars ct |+ (x,(shape_of v,ns))))
          (pan_to_crep_context_vmax_fupd
             (K (pan_to_crep_context_vmax ct + size_of_shape (shape_of v))) ct))
       (s |+ (x,v)) (t |++ ZIP ns (flatten v))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  QPAT_X_ASSUM "pan_to_crepProof_locals_rel _ _ _"
    (STRIP_ASSUME_TAC o REWRITE_RULE[pan_to_crepProof_locals_rel_def]) THEN
  REWRITE_TAC[pan_to_crepProof_locals_rel_def; pan_to_crep_context_INFO.ri_accfupds; K_THM] THEN
  SUBGOAL_THEN `LENGTH (ns:num list) = LENGTH (flatten (v:(A)pan_v))` ASSUME_TAC THENL
   [MP_TAC(ISPEC `v:(A)pan_v` length_flatten_eq_size_of_shape) THEN
    (ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC]) THEN
    DISCH_THEN SUBST1_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PP2CAUX_A_no_overlap_update THEN
    EXISTS_TAC `pan_to_crep_context_vmax (ct:(B)pan_to_crep_context)` THEN
    ASM_MESON_TAC[];
    MATCH_MP_TAC PP2CAUX_A_ctxt_max_update THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`vname:mlstring`; `w:(A)pan_v`] THEN
  REWRITE_TAC[FLOOKUP_UPDATE] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[injectivity "option"] THENL
   [DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    MAP_EVERY EXISTS_TAC [`ns:num list`; `flatten (v:(A)pan_v)`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC opt_mmap_some_eq_zip_flookup THEN
    CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`vname:mlstring`; `w:(A)pan_v`] o
      check (fun th -> is_forall(concl th) &&
                       length(fst(strip_forall(concl th))) = 2)) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `ns':num list` (X_CHOOSE_THEN `vs:((A)word_lab)list`
      STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`ns':num list`; `vs:((A)word_lab)list`] THEN
    ASM_REWRITE_TAC[] THEN
    TRANS_TAC EQ_TRANS `OPT_MMAP (FLOOKUP (t:(num,(A)word_lab)fmap)) ns'` THEN
    CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
    MATCH_MP_TAC opt_mmap_disj_zip_flookup THEN
    CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
    REWRITE_TAC[distinct_lists_def; GSYM ALL_MEM] THEN X_GEN_TAC `k:num` THEN
    DISCH_TAC THEN DISCH_TAC THEN
    QPAT_X_ASSUM "pan_commonProps_ctxt_max _ _"
      (MP_TAC o CONJUNCT2 o REWRITE_RULE[pan_commonProps_ctxt_max_def]) THEN
    DISCH_THEN(MP_TAC o SPECL [`vname:mlstring`; `shape_of (w:(A)pan_v)`; `ns':num list`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th ->
      try let v,b = dest_forall(concl th) in
          lhand b = mk_comb(mk_comb(`MEM:num->num list->bool`,v),`ns:num list`)
      with Failure _ -> false)) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC]);;

let flookup_res_var_thm_quant = prove
 (`!(l:(K,V)fmap) m v n.
     FLOOKUP (crep_res_var l (m,v)) n = if n = m then v else FLOOKUP l n`,
  REWRITE_TAC[flookup_res_var_thm]);;

(* the DecCall case: helpers *)

let PP2CAUX_A_var_cexp_replicate_const = prove
 (`!n (w:A word). FLAT (MAP var_cexp (REPLICATE n (crep_Const w))) = []`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[REPLICATE; MAP; FLAT; var_cexp_def; APPEND]);;

let PP2CAUX_A_dec_clock_locals = prove
 (`!(t:(A,B)crep_state) X Y.
     crep_state_locals_fupd (K X) (crep_dec_clock (crep_state_locals_fupd (K Y) t)) =
     crep_state_locals_fupd (K X) (crep_dec_clock t)`,
  REWRITE_TAC[crep_dec_clock_def; crep_state_component_equality;
              crep_state_INFO.ri_accfupds; K_THM]);;

let PP2CAUX_A_nvars_comm = prove
 (`!m n. list_of_seq (\x. m + SUC x) n = list_of_seq (\x. SUC x + m) n`,
  REPEAT GEN_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  ARITH_TAC);;

let PP2CAUX_A_all_distinct_seq_I = prove
 (`!n. ALL_DISTINCT (list_of_seq I n)`,
  REWRITE_TAC[ALL_DISTINCT_GENLIST; I_THM] THEN MESON_TAC[]);;

let PP2CAUX_A_HAS_CONST (c:string) (tm:term) : bool =
  can (find_term (fun t -> is_const t && fst(dest_const t) = c)) tm;;

(* rewrite the goal with the assumption whose left-hand side is tm *)

let PP2CAUX_A_REWR_LHS_TAC (tm:term) : tactic =
  FIRST_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = tm then REWRITE_TAC[th]
                        else NO_TAC);;

(* rewrite every other assumption with the assumption th (not th itself) *)

let PP2CAUX_A_REWR_OTHERS_TAC (th:thm) : tactic =
  RULE_ASSUM_TAC(fun th' -> if concl th' = concl th then th' else REWRITE_RULE[th] th');;

let PP2CAUX_A_SETVAR_SIMP_TAC : tactic =
  REWRITE_TAC[pan_set_var_def; pan_state_INFO.ri_accfupds; crep_state_INFO.ri_accfupds; K_THM;
              pan_state_INFO.ri_fupdfupds; K_o_THM];;

let PP2CAUX_A_CTXT_MAX_LE_TAC (v:term) (sh:term) (ns:term) : tactic =
  QPAT_ASSUM "pan_commonProps_ctxt_max (pan_to_crep_context_vmax ctxt) _"
    (MP_TAC o SPECL [v; sh; ns] o CONJUNCT2 o REWRITE_RULE[pan_commonProps_ctxt_max_def]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;;

let PP2CAUX_A_NVARS_HYP (th:thm) : bool =
  try let v,b = dest_forall(concl th) in
      lhand b = mk_comb(mk_comb(`MEM:num->num list->bool`,v),`nvars:num list`)
  with Failure _ -> false;;

let PP2CAUX_A_NOT_MEM_NVARS_TAC (k:term) : tactic =
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC k o check PP2CAUX_A_NVARS_HYP) THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;;

(* the callee's result: the source program fails (NONE, Break, Continue)  *)

let PP2CAUX_A_DC_PANERR_TAC : tactic =
  RULE_ASSUM_TAC(REWRITE_RULE[case_def "option"; case_def "pan_result"; PAIR_EQ]) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    concl th = `~(res = SOME (pan_Error:(A)pan_result))`)) THEN
  FIRST_X_ASSUM(fun th ->
    if is_conj(concl th) &&
       (try lhand(concl th) = `SOME (pan_Error:(A)pan_result) = res` with Failure _ -> false)
    then REWRITE_TAC[SYM(CONJUNCT1 th)] else NO_TAC);;

let PP2CAUX_A_DC_ERR_TAC : tactic =
  RULE_ASSUM_TAC(REWRITE_RULE[distinctness "option"; injectivity "option"]) THEN
  FIRST_ASSUM(CONTR_TAC o check (fun th -> concl th = `F`));;

(* the callee stopped with TimeOut, FinalFFI or (with the exception      *)
(* lookups done) Exception: so does the DecCall                           *)

let PP2CAUX_A_DC_FINISH_TAC : tactic =
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
    is_eq(concl th) && rhs(concl th) = `res:((A)pan_result)option`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
    is_eq(concl th) && rhs(concl th) = `s1:(A,B)pan_state`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    is_eq(concl th) && lhs(concl th) = `r1:((A)crep_result)option`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[case_def "option"; case_def "crep_result"; case_def "prod";
                              distinctness "option"]) THEN
  FIRST_X_ASSUM(fun th ->
    if is_eq(concl th) && PP2CAUX_A_HAS_CONST "nested_decs" (lhs(concl th))
    then REWRITE_TAC[th] else NO_TAC) THEN
  REWRITE_TAC[PAIR_EQ] THEN PP2CAUX_EXISTS_EQ_TAC THEN
  REWRITE_TAC[case_def "option"; case_def "pan_result"] THEN
  QPAT_X_ASSUM "pan_to_crepProof_state_rel p1 t1" MP_TAC THEN
  REWRITE_TAC[pan_to_crepProof_state_rel_def; pan_empty_locals_def; crep_empty_locals_def;
              pan_state_INFO.ri_accfupds; crep_state_INFO.ri_accfupds; K_THM;
              globals_lookup_def] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[case_def "option"];;

let PP2CAUX_A_DC_ABRUPT_TAC : tactic =
  RULE_ASSUM_TAC(REWRITE_RULE[case_def "option"; case_def "pan_result"; PAIR_EQ]) THEN
  PP2CAUX_WHL_SPLIT_TAC THEN PP2CAUX_A_DC_FINISH_TAC;;

let PP2CAUX_A_DC_EXN_TAC : tactic =
  RULE_ASSUM_TAC(REWRITE_RULE[case_def "option"; case_def "pan_result"; PAIR_EQ]) THEN
  PP2CAUX_WHL_SPLIT_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    free_in `r1:((A)crep_result)option` (concl th) && not (is_eq (concl th)) &&
    PP2CAUX_A_HAS_CONST "FLOOKUP" (concl th) &&
    not (PP2CAUX_A_HAS_CONST "crep_evaluate" (concl th)))) THEN
  QCASES_ON "FLOOKUP (pan_to_crep_context_eids (ctxt:(A)pan_to_crep_context)) a0" THEN
  REWRITE_TAC[case_def "option"] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[globals_lookup_def]) THEN
  PP2CAUX_A_DC_FINISH_TAC;;

(* DecCall: from the start to the evaluation of the callee (non-zero clock) *)

let PP2CAUX_A_DC_SETUP_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  QPAT_X_ASSUM "localised_prog (DecCall _ _ _ _ _)" (STRIP_ASSUME_TAC o
    REWRITE_RULE[localised_prog_def]) THEN
  QPAT_X_ASSUM "pan_evaluate (DecCall _ _ _ _ _,_) = _" MP_TAC THEN
  ONCE_REWRITE_TAC[pan_evaluate_def] THEN
  (TOP_CASE_TAC THENL [PP2CAUX_PAN_ERR_TAC; ALL_TAC]) THEN
  (TOP_CASE_TAC THENL [PP2CAUX_PAN_ERR_TAC; ALL_TAC]) THEN
  TOP_CASE_TAC THEN TOP_CASE_TAC THEN
  RENAME_TAC ["OPT_MMAP (pan_eval s) argexps = SOME args";
              "pan_lookup_code (pan_state_code s) fname args = SOME (prog,newlocals,return_sh)"] THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[pan_lookup_code_def] o check (fun th ->
    try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "pan_lookup_code"
    with Failure _ -> false)) THEN
  TOP_CASE_TAC THEN REWRITE_TAC[distinctness "option"] THEN
  TOP_CASE_TAC THEN TOP_CASE_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[distinctness "option"; injectivity "option"; PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  RENAME_TAC ["FLOOKUP (pan_state_code s) fname = SOME (vshapes,prog,return_sh)"] THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (fun th -> is_conj(concl th) &&
    (try fst(dest_const(rator(lhand(concl th)))) = "ALL_DISTINCT" with Failure _ -> false))) THEN
  REWRITE_TAC[slc_tlc_rw] THEN
  MP_TAC(MATCH_MP (MATCH_MP code_rel_imp (ASSUME
    `pan_to_crepProof_code_rel (ctxt:(A)pan_to_crep_context) (pan_state_code (s:(A,B)pan_state))
       (crep_state_code (t:(A,B)crep_state))`))
    (ASSUME `FLOOKUP (pan_state_code (s:(A,B)pan_state)) fname =
             SOME (vshapes,(prog:(A)panLang_prog),return_sh)`)) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN
  (SUBGOAL_THEN `MAP (crep_eval (t:(A,B)crep_state))
                   (FLAT (MAP FST (MAP (pan_to_crep_compile_exp (ctxt:(A)pan_to_crep_context))
                      (argexps:((A)panLang_exp)list)))) =
                 MAP SOME (FLAT (MAP flatten (args:((A)pan_v)list)))` ASSUME_TAC THENL
    [MATCH_MP_TAC eval_map_comp_exp_flat_eq THEN EXISTS_TAC `s:(A,B)pan_state` THEN
     ASM_REWRITE_TAC[GSYM opt_mmap_eq_some];
     ALL_TAC]) THEN
  ASSUME_TAC(MATCH_MP opt_mmap_eval_is_wf_shape_v
    (CONJ (ASSUME `OPT_MMAP (pan_eval (s:(A,B)pan_state)) argexps = SOME (args:((A)pan_v)list)`)
     (CONJ (ASSUME `pan_to_crepProof_state_rel (s:(A,B)pan_state) (t:(A,B)crep_state)`)
           (ASSUME `pan_to_crepProof_locals_rel (ctxt:(A)pan_to_crep_context)
                      (pan_state_locals (s:(A,B)pan_state)) (crep_state_locals (t:(A,B)crep_state))`)))) THEN
  (SUBGOAL_THEN `size_of_shape (Comb (MAP SND (vshapes:(mlstring#shape)list))) =
                 LENGTH (FLAT (MAP flatten (args:((A)pan_v)list)))` ASSUME_TAC THENL
    [MATCH_MP_TAC list_rel_length_shape_of_flatten THEN ASM_REWRITE_TAC[]; ALL_TAC]) THEN
  ONCE_REWRITE_TAC[pan_to_crep_compile_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ABBREV_TAC `nvars = list_of_seq (\x. pan_to_crep_context_vmax (ctxt:(A)pan_to_crep_context) + SUC x)
                        (size_of_shape shape)` THEN
  ABBREV_TAC `nctxt = pan_to_crep_context_vars_fupd
      (K (pan_to_crep_context_vars ctxt |+ (rt,shape,nvars)))
     (pan_to_crep_context_vmax_fupd
      (K (pan_to_crep_context_vmax (ctxt:(A)pan_to_crep_context) + size_of_shape shape)) ctxt)` THEN
  ABBREV_TAC `cargs = FLAT (MAP FST (MAP (pan_to_crep_compile_exp (ctxt:(A)pan_to_crep_context))
                                       (argexps:((A)panLang_exp)list)))` THEN
  (SUBGOAL_THEN `ALL_DISTINCT (nvars:num list) /\ LENGTH nvars = size_of_shape shape /\
                 (!k. MEM k nvars ==> pan_to_crep_context_vmax (ctxt:(A)pan_to_crep_context) < k /\
                                      k <= pan_to_crep_context_vmax ctxt + size_of_shape shape)`
     STRIP_ASSUME_TAC THENL
    [EXPAND_TAC "nvars" THEN
     REWRITE_TAC[ALL_DISTINCT_GENLIST; LENGTH_LIST_OF_SEQ; MEM_GENLIST] THEN ARITH_TAC;
     ALL_TAC]) THEN
  MP_TAC(ISPECL [`REPLICATE (LENGTH (nvars:num list)) (crep_Const (word 0)):((A)crep_exp)list`;
                 `nvars:num list`; `t:(A,B)crep_state`;
                 `REPLICATE (LENGTH (nvars:num list)) (Word (word 0)):((A)word_lab)list`;
                 `crep_Seq (crep_Call (SOME (nvars,NONE)) fname cargs)
                    (pan_to_crep_compile nctxt prog1):(A)crep_prog`]
    eval_nested_decs_seq_res_var_eq) THEN
  (ANTS_TAC THENL
    [REWRITE_TAC[LENGTH_REPLICATE; PP2CAUX_A_var_cexp_replicate_const; distinct_lists_def;
                 GSYM ALL_MEM; MEM] THEN
     ASM_REWRITE_TAC[GSYM opt_mmap_eq_some; pan_to_crepProof_evaluate_replicate_const];
     ALL_TAC]) THEN
  (SUBGOAL_THEN
    `OPT_MMAP (crep_eval (crep_state_locals_fupd
        (K (crep_state_locals t |++ ZIP nvars (REPLICATE (LENGTH nvars) (Word (word 0)))))
        (t:(A,B)crep_state))) cargs = SOME (FLAT (MAP flatten (args:((A)pan_v)list)))`
    ASSUME_TAC THENL
    [TRANS_TAC EQ_TRANS `OPT_MMAP (crep_eval (t:(A,B)crep_state)) cargs` THEN CONJ_TAC THENL
      [MATCH_MP_TAC opt_mmap_eval_distinct_lists_not_affect' THEN
       REWRITE_TAC[LENGTH_REPLICATE] THEN
       EXPAND_TAC "cargs" THEN EXPAND_TAC "nvars" THEN REWRITE_TAC[PP2CAUX_A_nvars_comm] THEN
       MATCH_MP_TAC genlist_vmax_distinct_lists_compiled_exps THEN
       QPAT_X_ASSUM "pan_to_crepProof_locals_rel _ _ _"
         (MP_TAC o REWRITE_RULE[pan_to_crepProof_locals_rel_def]) THEN
       SIMP_TAC[];
       ASM_REWRITE_TAC[opt_mmap_eq_some]];
     ALL_TAC]) THEN
  ONCE_REWRITE_TAC[crep_evaluate_def] THEN ONCE_REWRITE_TAC[crep_evaluate_def] THEN
  REWRITE_TAC[ASSUME
   `OPT_MMAP (crep_eval (crep_state_locals_fupd
       (K (crep_state_locals t |++ ZIP nvars (REPLICATE (LENGTH nvars) (Word (word 0)))))
       (t:(A,B)crep_state))) cargs = SOME (FLAT (MAP flatten (args:((A)pan_v)list)))`] THEN
  REWRITE_TAC[case_def "option"; crep_lookup_code_def; crep_state_INFO.ri_accfupds; K_THM] THEN
  PP2CAUX_A_REWR_LHS_TAC `FLOOKUP (crep_state_code (t:(A,B)crep_state)) fname` THEN
  REWRITE_TAC[case_def "option"; case_def "prod"; LENGTH_LIST_OF_SEQ; PP2CAUX_A_all_distinct_seq_I;
              PP2CAUX_A_dec_clock_locals] THEN
  PP2CAUX_A_REWR_LHS_TAC `size_of_shape (Comb (MAP SND (vshapes:(mlstring#shape)list)))` THEN
  ASM_REWRITE_TAC[slc_tlc_rw] THEN
  REWRITE_TAC[case_def "option"; case_def "prod"] THEN
  QPAT_ASSUM "pan_to_crepProof_state_rel s t" (fun th ->
    REWRITE_TAC[GSYM(CONJUNCT1(CONJUNCT2(CONJUNCT2(CONJUNCT2(CONJUNCT2(CONJUNCT2
      (REWRITE_RULE[pan_to_crepProof_state_rel_def] th)))))))]) THEN
  ASM_CASES_TAC `pan_state_clock (s:(A,B)pan_state) = 0` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[case_def "prod"; distinctness "option"] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    PP2CAUX_EXISTS_EQ_TAC THEN REWRITE_TAC[case_def "option"; case_def "pan_result"] THEN
    QPAT_X_ASSUM "pan_to_crepProof_state_rel s t" MP_TAC THEN
    REWRITE_TAC[pan_to_crepProof_state_rel_def; pan_empty_locals_def; crep_empty_locals_def;
                pan_state_INFO.ri_accfupds; crep_state_INFO.ri_accfupds; K_THM] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC];;

(* DecCall: the callee's evaluation (IH for the callee's body) *)

let PP2CAUX_A_DC_CALLEE_TAC : tactic =
  PAIR_CASES_ON `pan_evaluate (prog:(A)panLang_prog,
    pan_state_locals_fupd (K (slc (vshapes:(mlstring#shape)list) (args:((A)pan_v)list)))
      (pan_dec_clock (s:(A,B)pan_state)))` THEN
  REWRITE_TAC[case_def "prod"] THEN DISCH_TAC THEN DISCH_TAC THEN
  (SUBGOAL_THEN `~(p0 = SOME (pan_Error:(A)pan_result))` ASSUME_TAC THENL
    [DISCH_THEN SUBST_ALL_TAC THEN
     FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
       rand(concl th) = `res:((A)pan_result)option,s1:(A,B)pan_state`)) THEN
     REWRITE_TAC[case_def "option"; case_def "pan_result"; PAIR_EQ] THEN STRIP_TAC THEN
     FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
       rhs(concl th) = `res:((A)pan_result)option`)) THEN
     FIRST_X_ASSUM(MP_TAC o check (fun th ->
       concl th = `~(SOME (pan_Error:(A)pan_result) = SOME pan_Error)`)) THEN
     REWRITE_TAC[];
     ALL_TAC]) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`args:((A)pan_v)list`; `return_sh:shape`; `prog:(A)panLang_prog`;
    `slc (vshapes:(mlstring#shape)list) (args:((A)pan_v)list)`] o
    check (fun th -> is_forall(concl th) && length(fst(strip_forall(concl th))) = 4)) THEN
  (ANTS_TAC THENL [ASM_REWRITE_TAC[slc_def]; ALL_TAC]) THEN
  DISCH_THEN(MP_TAC o SPECL [`p0:((A)pan_result)option`; `p1:(A,B)pan_state`;
    `crep_state_locals_fupd (K (tlc (list_of_seq I (LENGTH (FLAT (MAP flatten (args:((A)pan_v)list)))))
                                   args)) (crep_dec_clock (t:(A,B)crep_state))`;
    `pan_to_crepProof_ctxt_fc (pan_to_crep_context_funcs (ctxt:(A)pan_to_crep_context))
       (pan_to_crep_context_eids ctxt) (MAP FST (vshapes:(mlstring#shape)list)) (MAP SND vshapes)
       (list_of_seq I (LENGTH (FLAT (MAP flatten (args:((A)pan_v)list)))))`]) THEN
  FIRST_X_ASSUM(ASSUME_TAC o REWRITE_RULE[ASSUME
    `size_of_shape (Comb (MAP SND (vshapes:(mlstring#shape)list))) =
     LENGTH (FLAT (MAP flatten (args:((A)pan_v)list)))`] o
    check (fun th -> is_eq(concl th) &&
                     lhs(concl th) = `FLOOKUP (crep_state_code (t:(A,B)crep_state)) fname`)) THEN
  MP_TAC(SPEC `return_sh:shape`
    (INST [`vshapes:(mlstring#shape)list`,`vshs:(mlstring#shape)list`;
           `list_of_seq I (LENGTH (FLAT (MAP flatten (args:((A)pan_v)list))))`,`ns:num list`]
      (INST_TYPE [`:B`,`:FFI`] pan_to_crepProof_call_preserve_state_code_locals_rel))) THEN
  (ANTS_TAC THENL
    [ASM_REWRITE_TAC[LENGTH_LIST_OF_SEQ; PP2CAUX_A_all_distinct_seq_I]; ALL_TAC]) THEN
  REWRITE_TAC[pan_state_INFO.ri_accfupds; crep_state_INFO.ri_accfupds; K_THM] THEN
  STRIP_TAC THEN
  REWRITE_TAC[pan_state_INFO.ri_accfupds; crep_state_INFO.ri_accfupds; K_THM] THEN
  (ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:((A)crep_result)option`
    (X_CHOOSE_THEN `t1:(A,B)crep_state` STRIP_ASSUME_TAC)) THEN
  QPAT_ASSUM "crep_evaluate (pan_to_crep_compile _ prog,_) = _" SUBST1_TAC THEN
  REWRITE_TAC[case_def "prod"] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PP2CAUX_code_rel_ctxt_fc; ctxt_fc_eids_eq]) THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    can (find_term (fun t -> t = `crep_dec_clock (t:(A,B)crep_state)`)) (concl th) &&
    not (PP2CAUX_A_HAS_CONST "crep_evaluate" (concl th))))) THEN
  FIRST_X_ASSUM(fun th -> if is_eq(concl th) &&
      PP2CAUX_A_HAS_CONST "crep_evaluate" (lhs(concl th)) &&
      rand(concl th) = `(r1:((A)crep_result)option),(t1:(A,B)crep_state)`
    then (ASSUME_TAC th THEN PP2CAUX_A_REWR_OTHERS_TAC th) else NO_TAC) THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[case_def "prod"]);;

(* DecCall: the callee returned; the returned value is stored in the     *)
(* fresh variables and the scoped body runs (IH for the scoped body)     *)

let PP2CAUX_A_DC_RETURN_TAC : tactic =
  RULE_ASSUM_TAC(REWRITE_RULE[case_def "option"; case_def "pan_result"]) THEN
  PP2CAUX_WHL_SPLIT_TAC THEN
  RENAME_TAC ["r1 = SOME (crepSem_Return (flatten retv))"] THEN
  ASM_CASES_TAC `shape_of (retv:(A)pan_v) = shape /\ shape_of retv = return_sh` THENL
   [ALL_TAC;
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME
      `~(shape_of (retv:(A)pan_v) = shape /\ shape_of retv = return_sh)`]) THEN
    PP2CAUX_A_DC_PANERR_TAC] THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (fun th -> concl th =
    `shape_of (retv:(A)pan_v) = shape /\ shape_of retv = return_sh`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
    concl th = `shape_of (retv:(A)pan_v) = shape`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
    concl th = `shape_of (retv:(A)pan_v) = return_sh`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[slc_tlc_rw]) THEN
  (SUBGOAL_THEN `is_wf_shape_v ([]:(mlstring#struct_info)list) (retv:(A)pan_v)` ASSUME_TAC THENL
    [MP_TAC(MATCH_MP evaluate_shape_invariant_ret_inst2
      (end_itlist CONJ
        [ASSUME `OPT_MMAP (pan_eval (s:(A,B)pan_state)) argexps = SOME (args:((A)pan_v)list)`;
         ASSUME `pan_lookup_code (pan_state_code (s:(A,B)pan_state)) fname args =
                 SOME (prog:(A)panLang_prog,slc (vshapes:(mlstring#shape)list) args,
                       shape_of (retv:(A)pan_v))`;
         ASSUME `pan_evaluate (prog:(A)panLang_prog,
                   pan_state_locals_fupd (K (slc (vshapes:(mlstring#shape)list) (args:((A)pan_v)list)))
                     (pan_dec_clock (s:(A,B)pan_state))) = SOME (pan_Return (retv:(A)pan_v)),p1`;
         ASSUME `pan_to_crepProof_state_rel (s:(A,B)pan_state) (t:(A,B)crep_state)`;
         ASSUME `pan_to_crepProof_locals_rel (ctxt:(A)pan_to_crep_context)
                   (pan_state_locals (s:(A,B)pan_state)) (crep_state_locals (t:(A,B)crep_state))`])) THEN
     REWRITE_TAC[case_def "pan_result"];
     ALL_TAC]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP is_wf_shape_of_v) THEN
  (SUBGOAL_THEN `LENGTH (flatten (retv:(A)pan_v)) = size_of_shape (shape_of retv)` ASSUME_TAC THENL
    [MATCH_MP_TAC length_flatten_eq_size_of_shape THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC]) THEN
  (SUBGOAL_THEN
    `OPT_MMAP (FLOOKUP (crep_state_locals (t:(A,B)crep_state) |++
        ZIP nvars (REPLICATE (size_of_shape (shape_of (retv:(A)pan_v))) (Word (word 0):(A)word_lab))))
        nvars = SOME (REPLICATE (size_of_shape (shape_of retv)) (Word (word 0)))` ASSUME_TAC THENL
    [MATCH_MP_TAC opt_mmap_some_eq_zip_flookup THEN ASM_REWRITE_TAC[LENGTH_REPLICATE];
     ALL_TAC]) THEN
  (SUBGOAL_THEN
    `crep_state_locals (t:(A,B)crep_state) |++
       ZIP nvars (REPLICATE (size_of_shape (shape_of (retv:(A)pan_v))) (Word (word 0):(A)word_lab)) |++
       ZIP nvars (flatten retv) =
     crep_state_locals t |++ ZIP nvars (flatten retv)` ASSUME_TAC THENL
    [MATCH_MP_TAC FUPDATE_LIST_CANCEL THEN
     SUBGOAL_THEN `MAP FST (ZIP (nvars:num list)
                     (REPLICATE (size_of_shape (shape_of (retv:(A)pan_v))) (Word (word 0):(A)word_lab))) = nvars /\
                   MAP FST (ZIP (nvars:num list) (flatten retv)) = nvars`
       (fun th -> REWRITE_TAC[th]) THEN
     ASM_SIMP_TAC[MAP_ZIP; LENGTH_REPLICATE];
     ALL_TAC]) THEN
  FIRST_X_ASSUM(fun th -> if concl th = `r1 = SOME (crepSem_Return (flatten (retv:(A)pan_v)))`
    then PP2CAUX_A_REWR_OTHERS_TAC th else NO_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[case_def "option"; case_def "crep_result"]) THEN
  FIRST_ASSUM(fun th ->
    if concl th = `LENGTH (flatten (retv:(A)pan_v)) = size_of_shape (shape_of retv)`
    then PP2CAUX_A_REWR_OTHERS_TAC th else NO_TAC) THEN
  FIRST_ASSUM(fun th ->
    if is_eq(concl th) && PP2CAUX_A_HAS_CONST "OPT_MMAP" (lhs(concl th)) &&
       rand(lhs(concl th)) = `nvars:num list`
    then PP2CAUX_A_REWR_OTHERS_TAC th else NO_TAC) THEN
  FIRST_ASSUM(fun th ->
    if is_eq(concl th) && PP2CAUX_A_HAS_CONST "REPLICATE" (lhs(concl th)) &&
       not (PP2CAUX_A_HAS_CONST "OPT_MMAP" (lhs(concl th))) &&
       PP2CAUX_A_HAS_CONST "flatten" (lhs(concl th))
    then PP2CAUX_A_REWR_OTHERS_TAC th else NO_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[case_def "option"; case_def "prod"]) THEN
  PAIR_CASES_ON `pan_evaluate (prog1:(A)panLang_prog,
    pan_set_var (rt:mlstring) (retv:(A)pan_v)
      (pan_state_locals_fupd (K (pan_state_locals (s:(A,B)pan_state))) (p1:(A,B)pan_state)))` THEN
  RENAME_TAC ["pan_evaluate (prog1,pan_set_var rt retv (pan_state_locals_fupd (K (pan_state_locals s)) p1)) = pres,pst"] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[case_def "prod"; PAIR_EQ]) THEN
  PP2CAUX_WHL_SPLIT_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`args:((A)pan_v)list`; `prog:(A)panLang_prog`;
    `slc (vshapes:(mlstring#shape)list) (args:((A)pan_v)list)`; `retv:(A)pan_v`;
    `p1:(A,B)pan_state`] o
    check (fun th -> is_forall(concl th) && length(fst(strip_forall(concl th))) = 5)) THEN
  (ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
  DISCH_THEN(MP_TAC o SPECL [`pres:((A)pan_result)option`; `pst:(A,B)pan_state`;
    `crep_state_locals_fupd (K (crep_state_locals (t:(A,B)crep_state) |++
                                ZIP nvars (flatten (retv:(A)pan_v))))
       (t1:(A,B)crep_state)`; `nctxt:(A)pan_to_crep_context`]) THEN
  (ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM(fun th -> if concl th = `pres:((A)pan_result)option = res` then SUBST1_TAC th
                            else NO_TAC) THEN FIRST_ASSUM ACCEPT_TAC;
      PP2CAUX_A_SETVAR_SIMP_TAC THEN
      QPAT_ASSUM "pan_to_crepProof_state_rel p1 t1" MP_TAC THEN
      REWRITE_TAC[pan_to_crepProof_state_rel_def; pan_state_INFO.ri_accfupds;
                  crep_state_INFO.ri_accfupds; K_THM];
      PP2CAUX_A_SETVAR_SIMP_TAC THEN
      EXPAND_TAC "nctxt" THEN REWRITE_TAC[PP2CAUX_code_rel_vars_vmax] THEN FIRST_ASSUM ACCEPT_TAC;
      PP2CAUX_A_SETVAR_SIMP_TAC THEN
      EXPAND_TAC "nctxt" THEN REWRITE_TAC[pan_to_crep_context_INFO.ri_accfupds] THEN
      FIRST_ASSUM ACCEPT_TAC;
      PP2CAUX_A_SETVAR_SIMP_TAC THEN
      EXPAND_TAC "nctxt" THEN EXPAND_TAC "nvars" THEN MATCH_MP_TAC PP2CAUX_locals_rel_dec THEN
      ASM_REWRITE_TAC[];
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC]) THEN
  DISCH_THEN(X_CHOOSE_THEN `r2:((A)crep_result)option` (X_CHOOSE_THEN `t3:(A,B)crep_state`
    STRIP_ASSUME_TAC));;

(* DecCall: the declarations restore the locals; the relations after the  *)
(* scoped body give the relations after the DecCall                       *)

let PP2CAUX_A_DC_TAIL_TAC : tactic =
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `pres:((A)pan_result)option = res`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq(concl th) &&
    rhs(concl th) = `s1:(A,B)pan_state`)) THEN
  FIRST_ASSUM(fun th -> if is_eq(concl th) && rand(concl th) =
      `(r2:((A)crep_result)option),(t3:(A,B)crep_state)`
    then PP2CAUX_A_REWR_OTHERS_TAC th else NO_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[case_def "prod"]) THEN
  FIRST_X_ASSUM(fun th ->
    if is_eq(concl th) && PP2CAUX_A_HAS_CONST "nested_decs" (lhs(concl th))
    then REWRITE_TAC[th] else NO_TAC) THEN
  MAP_EVERY EXISTS_TAC [`r2:((A)crep_result)option`;
    `crep_state_locals_fupd
       (K (FOLDL crep_res_var (crep_state_locals t3)
             (ZIP nvars (MAP (FLOOKUP (crep_state_locals (t:(A,B)crep_state))) nvars))))
       (t3:(A,B)crep_state)`] THEN
  REWRITE_TAC[] THEN
  QPAT_X_ASSUM "pan_to_crepProof_code_rel nctxt _ _" MP_TAC THEN
  QPAT_X_ASSUM "excp_rel _ (pan_state_eshapes pst)" MP_TAC THEN
  QPAT_X_ASSUM "pan_to_crepProof_state_rel pst t3" MP_TAC THEN
  EXPAND_TAC "nctxt" THEN
  REWRITE_TAC[PP2CAUX_code_rel_vars_vmax; pan_to_crep_context_INFO.ri_accfupds;
              pan_to_crepProof_state_rel_def; pan_state_INFO.ri_accfupds;
              crep_state_INFO.ri_accfupds; K_THM; globals_lookup_def] THEN
  REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  QPAT_ASSUM "pan_to_crepProof_locals_rel ctxt (pan_state_locals s) (crep_state_locals t)"
    (STRIP_ASSUME_TAC o REWRITE_RULE[pan_to_crepProof_locals_rel_def]) THEN
  (SUBGOAL_THEN
    `(r2 = NONE \/ r2 = SOME (crepSem_Break 0) \/
      r2 = SOME (crepSem_Continue 0:(A)crep_result)) /\
     pan_to_crepProof_locals_rel (nctxt:(A)pan_to_crep_context)
       (pan_state_locals (pst:(A,B)pan_state))
       (crep_state_locals (t3:(A,B)crep_state))
     ==> pan_to_crepProof_locals_rel (ctxt:(A)pan_to_crep_context)
           (pan_res_var (pan_state_locals pst) (rt,FLOOKUP (pan_state_locals (s:(A,B)pan_state)) rt))
           (FOLDL crep_res_var (crep_state_locals t3)
              (ZIP nvars (MAP (FLOOKUP (crep_state_locals (t:(A,B)crep_state))) nvars)))`
    ASSUME_TAC THENL
    [DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
     MATCH_MP_TAC PP2CAUX_locals_rel_agree THEN
     EXISTS_TAC `crep_state_locals (t3:(A,B)crep_state)` THEN CONJ_TAC THENL
      [MATCH_MP_TAC PP2CAUX_locals_rel_res_var THEN
       MAP_EVERY EXISTS_TAC [`crep_state_locals (t:(A,B)crep_state)`; `shape_of (retv:(A)pan_v)`;
                             `nvars:num list`; `size_of_shape (shape_of (retv:(A)pan_v))`] THEN
       ASM_REWRITE_TAC[] THEN
       MAP_EVERY X_GEN_TAC [`sh':shape`; `ns:num list`; `k:num`] THEN STRIP_TAC THEN
       (SUBGOAL_THEN `k <= pan_to_crep_context_vmax (ctxt:(A)pan_to_crep_context)` ASSUME_TAC THENL
         [PP2CAUX_A_CTXT_MAX_LE_TAC `rt:mlstring` `sh':shape` `ns:num list`; ALL_TAC]) THEN
       (SUBGOAL_THEN `~MEM (k:num) nvars` ASSUME_TAC THENL
         [PP2CAUX_A_NOT_MEM_NVARS_TAC `k:num`; ALL_TAC]) THEN
       (SUBGOAL_THEN `LENGTH (nvars:num list) = LENGTH (flatten (retv:(A)pan_v))` ASSUME_TAC THENL
         [MP_TAC(ISPEC `retv:(A)pan_v` length_flatten_eq_size_of_shape) THEN
          (ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC;
                           DISCH_THEN SUBST1_TAC THEN FIRST_ASSUM ACCEPT_TAC]);
          ALL_TAC]) THEN
       TRANS_TAC EQ_TRANS
         `FLOOKUP (crep_state_locals (t:(A,B)crep_state) |++ ZIP nvars (flatten (retv:(A)pan_v))) k` THEN
       CONJ_TAC THENL
        [ALL_TAC;
         MATCH_MP_TAC flookup_fupdate_zip_not_mem THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC] THEN
       (SUBGOAL_THEN `distinct_lists (ns:num list)
                        (assigned_free_vars (pan_to_crep_compile (nctxt:(A)pan_to_crep_context)
                                               (prog1:(A)panLang_prog)))` MP_TAC THENL
         [MATCH_MP_TAC rewritten_context_unassigned THEN
          MAP_EVERY EXISTS_TAC [`rt:mlstring`; `ctxt:(A)pan_to_crep_context`; `nvars:num list`;
                                `shape_of (retv:(A)pan_v)`; `sh':shape`] THEN
          ASM_REWRITE_TAC[] THEN
          QPAT_ASSUM "pan_to_crepProof_locals_rel nctxt _ _"
            (STRIP_ASSUME_TAC o REWRITE_RULE[pan_to_crepProof_locals_rel_def]) THEN
          ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[distinct_lists_def; EVERY_MEM] THEN X_GEN_TAC `y:num` THEN
          REPEAT DISCH_TAC THEN
          (SUBGOAL_THEN `y <= pan_to_crep_context_vmax (ctxt:(A)pan_to_crep_context)` MP_TAC THENL
            [PP2CAUX_A_CTXT_MAX_LE_TAC `rt:mlstring` `sh':shape` `ns:num list`; ALL_TAC]) THEN
          MATCH_MP_TAC(TAUT `~p ==> p ==> F`) THEN
          FIRST_X_ASSUM(MP_TAC o SPEC `y:num` o check PP2CAUX_A_NVARS_HYP) THEN
          ASM_REWRITE_TAC[] THEN ARITH_TAC;
          ALL_TAC]) THEN
       REWRITE_TAC[distinct_lists_def; EVERY_MEM] THEN
       DISCH_THEN(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
       MP_TAC(ISPECL
         [`pan_to_crep_compile (nctxt:(A)pan_to_crep_context) (prog1:(A)panLang_prog)`;
          `crep_state_locals_fupd
             (K (crep_state_locals (t:(A,B)crep_state) |++ ZIP nvars (flatten (retv:(A)pan_v))))
             (t1:(A,B)crep_state)`;
          `r2:((A)crep_result)option`; `t3:(A,B)crep_state`; `k:num`; `0`]
         crep_unassigned_vars_evaluate_same) THEN
       (ANTS_TAC THENL
         [ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC(TAUT `(a \/ b \/ c) ==> (a \/ c \/ b)`) THEN
          FIRST_ASSUM ACCEPT_TAC;
          ALL_TAC]) THEN
       REWRITE_TAC[crep_state_INFO.ri_accfupds; K_THM];
       MAP_EVERY X_GEN_TAC [`vn:mlstring`; `shn:shape`; `nsn:num list`; `n:num`] THEN
       STRIP_TAC THEN
       MATCH_MP_TAC flookup_res_var_distinct_zip_eq THEN REWRITE_TAC[LENGTH_MAP] THEN
       (SUBGOAL_THEN `n <= pan_to_crep_context_vmax (ctxt:(A)pan_to_crep_context)` ASSUME_TAC THENL
         [PP2CAUX_A_CTXT_MAX_LE_TAC `vn:mlstring` `shn:shape` `nsn:num list`; ALL_TAC]) THEN
       PP2CAUX_A_NOT_MEM_NVARS_TAC `n:num`];
     ALL_TAC]) THEN
  (SUBGOAL_THEN `pan_to_crep_context_eids (nctxt:(A)pan_to_crep_context) =
                 pan_to_crep_context_eids (ctxt:(A)pan_to_crep_context)` ASSUME_TAC THENL
    [EXPAND_TAC "nctxt" THEN REWRITE_TAC[pan_to_crep_context_INFO.ri_accfupds]; ALL_TAC]) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_case_app (concl th) &&
    free_in `r2:((A)crep_result)option` (concl th))) THEN
  ASM_REWRITE_TAC[globals_lookup_def] THEN
  NAMED_CASES_ON "res" ["";"rr"] THEN REWRITE_TAC[case_def "option"] THENL
   [STRIP_TAC THEN ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  QCASES_ON "rr" THEN REWRITE_TAC[case_def "pan_result"] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  TRY (FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC);;

(* HOL4: Resume pc_compile_correct[DecCall] *)

let PP2CAUX_pc_DecCall = prove
 (el 19 PP2CAUX_pc_cases,
  PP2CAUX_A_DC_SETUP_TAC THEN PP2CAUX_A_DC_CALLEE_TAC THEN
  NAMED_CASES_ON "p0" ["";"pr"] THENL
   [PP2CAUX_A_DC_PANERR_TAC;
    QCASES_ON "pr" THENL
     [PP2CAUX_A_DC_ERR_TAC; PP2CAUX_A_DC_ABRUPT_TAC; PP2CAUX_A_DC_PANERR_TAC;
      PP2CAUX_A_DC_PANERR_TAC; PP2CAUX_A_DC_RETURN_TAC THEN PP2CAUX_A_DC_TAIL_TAC;
      PP2CAUX_A_DC_EXN_TAC; PP2CAUX_A_DC_ABRUPT_TAC]]);;

let pan_to_crepProof_MAX_LIST_APPEND = prove
 (`MAX_LIST (APPEND a b) = MAX (MAX_LIST a) (MAX_LIST b)`,
  REWRITE_TAC[MAX_LIST_APPEND]);;

let MAX_LIST_NOT_MEM = prove
 (`x > MAX_LIST l ==> ~MEM x l`,
  REWRITE_TAC[GT] THEN DISCH_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP MAX_LIST_PROPERTY) THEN
  ASM_ARITH_TAC);;

(* the ExtCall case: rewrite with an assumption whose lhs has head c       *)

let PP2CAUX_A_REWR_ASM_HEAD_TAC (c:string) : tactic =
  REPEAT(FIRST_X_ASSUM(fun th ->
    if is_eq(concl th) &&
       (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = c with Failure _ -> false)
    then REWRITE_TAC[th] else NO_TAC));;

(* both outcomes of the FFI call: the four arguments are bound to fresh   *)
(* variables (nested_decs), the call is evaluated and the declarations    *)
(* restore the locals                                                      *)

let PP2CAUX_A_EXTCALL_TAC : tactic =
  RENAME_TAC ["pan_eval s ptr1 = SOME (pan_Val (Word w1))";
              "pan_eval s len1 = SOME (pan_Val (Word w2))";
              "pan_eval s ptr2 = SOME (pan_Val (Word w3))";
              "pan_eval s len2 = SOME (pan_Val (Word w4))"] THEN
  MAP_EVERY (fun (ex,wd) ->
     let ce = mk_comb(`pan_to_crep_compile_exp (ctxt:(A)pan_to_crep_context):
                         (A)panLang_exp->((A)crep_exp)list#shape`, ex) in
     MP_TAC(ISPECL [`s:(A,B)pan_state`; ex;
                    mk_comb(`pan_Val:(A)word_lab->(A)pan_v`,
                            mk_comb(`Word:A word->(A)word_lab`, wd));
                    `t:(A,B)crep_state`; `ctxt:(A)pan_to_crep_context`;
                    mk_comb(`FST:((A)crep_exp)list#shape->((A)crep_exp)list`, ce);
                    mk_comb(`SND:((A)crep_exp)list#shape->shape`, ce)]
              compile_exp_val_rel) THEN
     ASM_REWRITE_TAC[flatten_def; MAP; MAP_EQ_SING; shape_of_def; PAIR] THEN STRIP_TAC)
  [`ptr1:(A)panLang_exp`,`w1:A word`; `len1:(A)panLang_exp`,`w2:A word`;
   `ptr2:(A)panLang_exp`,`w3:A word`; `len2:(A)panLang_exp`,`w4:A word`] THEN
  ONCE_REWRITE_TAC[pan_to_crep_compile_def] THEN
  (SUBGOAL_THEN
    `pan_to_crep_compile_exp (ctxt:(A)pan_to_crep_context) (ptr1:(A)panLang_exp) = ([x0],One) /\
     pan_to_crep_compile_exp ctxt (len1:(A)panLang_exp) = ([x0'],One) /\
     pan_to_crep_compile_exp ctxt (ptr2:(A)panLang_exp) = ([x0''],One) /\
     pan_to_crep_compile_exp ctxt (len2:(A)panLang_exp) = ([x0'''],One)`
    (fun th -> REWRITE_TAC[th] THEN STRIP_ASSUME_TAC th) THENL
    [REPEAT CONJ_TAC THEN ONCE_REWRITE_TAC[GSYM PAIR] THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
     ASM_MESON_TAC[];
     ALL_TAC]) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[case_def "prod"; case_def "list"; case_def "shape"; FLAT; MAP; APPEND] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "pan_to_crep_compile_exp"))
        (concl th)))) THEN
  ABBREV_TAC `vl = APPEND (var_cexp (x0:(A)crep_exp)) (APPEND (var_cexp (x0':(A)crep_exp))
                     (APPEND (var_cexp (x0'':(A)crep_exp))
                        (APPEND (var_cexp (x0''':(A)crep_exp)) [])))` THEN
  ABBREV_TAC `n = ITLIST MAX (vl:num list) 0` THEN
  (SUBGOAL_THEN `!k. MEM k (vl:num list) ==> k <= n` ASSUME_TAC THENL
    [EXPAND_TAC "n" THEN REWRITE_TAC[FOLDR_MAX_0_MAX_LIST] THEN MESON_TAC[MAX_LIST_PROPERTY];
     ALL_TAC]) THEN
  (SUBGOAL_THEN
    `crep_Dec (n + 1) (x0:(A)crep_exp) (crep_Dec (n + 2) (x0':(A)crep_exp)
       (crep_Dec (n + 3) (x0'':(A)crep_exp)
       (crep_Dec (n + 4) (x0''':(A)crep_exp)
          (crep_ExtCall ffi_index (n + 1) (n + 2) (n + 3) (n + 4))))) =
     nested_decs [n + 1; n + 2; n + 3; n + 4] [x0; x0'; x0''; x0''']
       (crep_ExtCall ffi_index (n + 1) (n + 2) (n + 3) (n + 4):(A)crep_prog)`
    SUBST1_TAC THENL [REWRITE_TAC[nested_decs_def]; ALL_TAC]) THEN
  MP_TAC(ISPECL [`[x0;x0';x0'';x0''']:((A)crep_exp)list`; `[n + 1; n + 2; n + 3; n + 4]`;
                 `t:(A,B)crep_state`;
                 `[Word w1; Word w2; Word w3; Word w4]:((A)word_lab)list`;
                 `crep_ExtCall ffi_index (n + 1) (n + 2) (n + 3) (n + 4):(A)crep_prog`]
    eval_nested_decs_seq_res_var_eq) THEN
  (ANTS_TAC THENL
    [REWRITE_TAC[MAP; CONS_11; LENGTH; FLAT; ALL_DISTINCT; MEM] THEN ASM_REWRITE_TAC[] THEN
     CONJ_TAC THENL
      [REWRITE_TAC[distinct_lists_def; ALL] THEN REPEAT CONJ_TAC THEN DISCH_TAC THEN
       RES_TAC THEN ASM_ARITH_TAC;
       ARITH_TAC];
     ALL_TAC]) THEN
  ONCE_REWRITE_TAC[crep_evaluate_def] THEN
  REWRITE_TAC[crep_state_INFO.ri_accfupds; K_THM; ZIP; FUPDATE_LIST_THM; FLOOKUP_UPDATE;
              EQ_ADD_LCANCEL] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[case_def "option"; case_def "word_lab"; case_def "prod"] THEN
  QPAT_X_ASSUM "pan_to_crepProof_state_rel s t" (fun th ->
    ASSUME_TAC th THEN STRIP_ASSUME_TAC(REWRITE_RULE[pan_to_crepProof_state_rel_def] th)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
    [ASSUME `pan_state_memory (s:(A,B)pan_state) = crep_state_memory (t:(A,B)crep_state)`;
     ASSUME `pan_state_memaddrs (s:(A,B)pan_state) = crep_state_memaddrs (t:(A,B)crep_state)`;
     ASSUME `pan_state_be (s:(A,B)pan_state) <=> crep_state_be (t:(A,B)crep_state)`;
     ASSUME `pan_state_ffi (s:(A,B)pan_state) = crep_state_ffi (t:(A,B)crep_state)`]) THEN
  PP2CAUX_A_REWR_ASM_HEAD_TAC "read_bytearray" THEN
  REWRITE_TAC[case_def "option"] THEN
  PP2CAUX_A_REWR_ASM_HEAD_TAC "call_FFI" THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[case_def "ffi_result"; case_def "prod"] THEN
  REWRITE_TAC[crep_state_INFO.ri_accfupds; K_THM] THEN
  (SUBGOAL_THEN
    `FOLDL crep_res_var
       (crep_state_locals (t:(A,B)crep_state) |+ (n + 1,Word w1) |+ (n + 2,Word w2) |+
        (n + 3,Word w3) |+ (n + 4,Word w4))
       (ZIP [n + 1; n + 2; n + 3; n + 4]
          (MAP (FLOOKUP (crep_state_locals t)) [n + 1; n + 2; n + 3; n + 4])) =
     crep_state_locals t` SUBST1_TAC THENL
    [MP_TAC(ISPECL [`[n + 1; n + 2; n + 3; n + 4]`;
                    `[Word w1; Word w2; Word w3; Word w4]:((A)word_lab)list`;
                    `crep_state_locals (t:(A,B)crep_state)`] res_var_lookup_original_eq) THEN
     REWRITE_TAC[ZIP; FUPDATE_LIST_THM; ALL_DISTINCT; MEM; LENGTH] THEN
     ANTS_TAC THENL [ARITH_TAC; REWRITE_TAC[]];
     ALL_TAC]) THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[PAIR_EQ] THEN PP2CAUX_EXISTS_EQ_TAC THEN
  REWRITE_TAC[case_def "option"; case_def "pan_result"] THEN
  QPAT_X_ASSUM "pan_to_crepProof_state_rel s t" MP_TAC THEN
  REWRITE_TAC[pan_to_crepProof_state_rel_def; pan_empty_locals_def; pan_state_INFO.ri_accfupds;
              crep_state_INFO.ri_accfupds; K_THM] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[];;

(* HOL4: Resume pc_compile_correct[ExtCall] *)

let PP2CAUX_pc_ExtCall = prove
 (el 20 PP2CAUX_pc_cases,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FS[localised_prog_def] THEN
  QPAT_X_ASSUM "pan_evaluate _ = _" MP_TAC THEN
  REWRITE_TAC[pan_evaluate_def] THEN
  GVS(option_case_eq :: COND_CASE_EQ :: all_case_eqs()) THEN
  STRIP_TAC THEN RVEQ_TAC THEN PP2CAUX_A_EXTCALL_TAC);;

(* HOL4: Finalise pc_compile_correct *)

let pc_compile_correct = prove
 (PP2CAUX_pc_stmt,
  REC_IND_TAC pan_evaluate_ind THEN REPEAT CONJ_TAC THEN
  FIRST (map ACCEPT_TAC
   [PP2CAUX_pc_Skip; PP2CAUX_pc_Dec; PP2CAUX_pc_Assign; PP2CAUX_pc_Primitive;
    PP2CAUX_pc_Store; PP2CAUX_pc_Store32; PP2CAUX_pc_StoreByte; PP2CAUX_pc_ShMemLoad;
    PP2CAUX_pc_ShMemStore; PP2CAUX_pc_Seq; PP2CAUX_pc_If; PP2CAUX_pc_Break;
    PP2CAUX_pc_Continue; PP2CAUX_pc_While; PP2CAUX_pc_Return; PP2CAUX_pc_Raise;
    PP2CAUX_pc_Tick; PP2CAUX_pc_Annot; PP2CAUX_pc_Call; PP2CAUX_pc_DecCall;
    PP2CAUX_pc_ExtCall]));;

(* ========================================================================= *)
(* The top level of pan_to_crepProof (HOL4 pan_to_crepProofScript.sml after    *)
(* Finalise pc_compile_correct).                                               *)
(* HOL4 EVERY is ALL; s with structs := [] is pan_state_structs_fupd (K []) s; *)
(* the theorems that HOL4 states with free variables are quantified.  HOL4    *)
(* proves state_rel_imp_semantics_to_crep by the lprefix_lub argument; here   *)
(* pc_compile_correct relates the runs at every clock, which gives the same   *)
(* semantics by PP2CAUX_B_sem_eq.  Local helpers are PP2CAUX_B_.              *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Top level: compiling whole programs (HOL4 after Finalise                  *)
(* pc_compile_correct)                                                        *)
(* ------------------------------------------------------------------------- *)

(* the passes keep the function names *)

let PP2CAUX_B_map_fst_compile_to_crep = prove
 (`!prog:((A)decl)list. MAP FST (compile_to_crep prog) = MAP FST (functions prog)`,
  GEN_TAC THEN REWRITE_TAC[compile_to_crep_def; LET_DEF; LET_END_DEF] THEN
  SPEC_TAC(`pan_to_crep_comp_func (pan_to_crep_make_funcs (functions (prog:((A)decl)list)))
              (get_eids_from_decls prog)`,
           `cf:(mlstring#shape)list->(A)panLang_prog->(A)crep_prog`) THEN
  SPEC_TAC(`functions (prog:((A)decl)list)`,
           `l:(mlstring#(mlstring#shape)list#(A)panLang_prog#shape)list`) THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP] THEN
  SPEC_TAC(`h:mlstring#(mlstring#shape)list#(A)panLang_prog#shape`,
           `h:mlstring#(mlstring#shape)list#(A)panLang_prog#shape`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  ASM_REWRITE_TAC[]);;

let PP2CAUX_B_map_fst_compile_inl_prog = prove
 (`!(inl_fs:(mlstring,num list # (A)crep_prog)fmap) (l:(mlstring#B#(A)crep_prog)list).
     MAP FST (compile_inl_prog inl_fs l) = MAP FST l`,
  GEN_TAC THEN REWRITE_TAC[compile_inl_prog_def] THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[MAP] THEN
  SPEC_TAC(`h:mlstring#B#(A)crep_prog`,`h:mlstring#B#(A)crep_prog`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  ASM_REWRITE_TAC[]);;

let pan_to_crepProof_first_compile_prog_all_distinct = prove
 (`!prog:((A)decl)list.
     ALL_DISTINCT (MAP FST (functions prog)) ==>
     ALL_DISTINCT (MAP FST (pan_to_crep_compile_prog prog))`,
  REWRITE_TAC[pan_to_crep_compile_prog_def; compile_inl_top_def; LET_DEF; LET_END_DEF;
              PP2CAUX_B_map_fst_compile_inl_prog; PP2CAUX_B_map_fst_compile_to_crep]);;

let first_compile_to_crep_all_distinct = prove
 (`!prog:((A)decl)list.
     ALL_DISTINCT (MAP FST (functions prog)) ==>
     ALL_DISTINCT (MAP FST (compile_to_crep prog))`,
  REWRITE_TAC[PP2CAUX_B_map_fst_compile_to_crep]);;

(* the code of compile_to_crep *)

let PP2CAUX_B_alookup_compile_to_crep = prove
 (`!(pan_code:((A)decl)list) start.
     ALOOKUP (compile_to_crep pan_code) start =
     OPTION_MAP (\(params,body,return).
                   (crep_vars params,
                    pan_to_crep_comp_func (pan_to_crep_make_funcs (functions pan_code))
                      (get_eids_from_decls pan_code) params body))
                (ALOOKUP (functions pan_code) start)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[compile_to_crep_def; LET_DEF; LET_END_DEF] THEN
  SPEC_TAC(`pan_to_crep_comp_func (pan_to_crep_make_funcs (functions (pan_code:((A)decl)list)))
              (get_eids_from_decls pan_code)`,
           `cf:(mlstring#shape)list->(A)panLang_prog->(A)crep_prog`) THEN
  SPEC_TAC(`functions (pan_code:((A)decl)list)`,
           `l:(mlstring#(mlstring#shape)list#(A)panLang_prog#shape)list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; ALOOKUP_THM; OPTION_MAP_DEF] THEN
  SPEC_TAC(`h:mlstring#(mlstring#shape)list#(A)panLang_prog#shape`,
           `h:mlstring#(mlstring#shape)list#(A)panLang_prog#shape`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[ALOOKUP_THM] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[OPTION_MAP_DEF] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[]);;

let alookup_compile_prog_code = prove
 (`ALL_DISTINCT (MAP FST (functions (pan_code:((A)decl)list))) /\
   ALOOKUP (functions pan_code) start = SOME ([],prog,rshape) ==>
   ALOOKUP (compile_to_crep pan_code) start =
   SOME ([],pan_to_crep_comp_func (pan_to_crep_make_funcs (functions pan_code))
                                  (get_eids_from_decls pan_code) [] prog)`,
  STRIP_TAC THEN ASM_REWRITE_TAC[PP2CAUX_B_alookup_compile_to_crep; OPTION_MAP_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[crep_vars_def; LET_DEF; LET_END_DEF; MAP; size_of_shape_def; SUM;
              list_of_seq]);;

let pan_to_crepProof_el_compile_prog_el_prog_eq = prove
 (`!(prog:((A)decl)list) n start cprog p rshape.
     EL n (compile_to_crep prog) = (start,[],cprog) /\
     ALL_DISTINCT (MAP FST (functions prog)) /\ n < LENGTH (functions prog) /\
     ALOOKUP (functions prog) start = SOME ([],p,rshape) ==>
     EL n (functions prog) = (start,[],p,rshape)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `FST (EL n (functions (prog:((A)decl)list))) = start` ASSUME_TAC THENL
   [MP_TAC(AP_TERM `FST:mlstring#num list#(A)crep_prog->mlstring`
      (ASSUME `EL n (compile_to_crep (prog:((A)decl)list)) = (start,[],cprog)`)) THEN
    REWRITE_TAC[FST] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN `n < LENGTH (compile_to_crep (prog:((A)decl)list))` ASSUME_TAC THENL
     [REWRITE_TAC[compile_to_crep_def; LET_DEF; LET_END_DEF; LENGTH_MAP] THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM EL_MAP; PP2CAUX_B_map_fst_compile_to_crep];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`functions (prog:((A)decl)list)`; `start:mlstring`;
                 `SND (EL n (functions (prog:((A)decl)list)))`] ALOOKUP_ALL_DISTINCT_MEM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[PAIR] THEN
    MATCH_MP_TAC MEM_EL THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[injectivity "option"] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    lhs(concl th) = `FST (EL n (functions (prog:((A)decl)list)))`)) THEN
  FIRST_X_ASSUM(SUBST1_TAC o check (fun th ->
    rhs(concl th) = `SND (EL n (functions (prog:((A)decl)list)))`)) THEN
  REWRITE_TAC[PAIR]);;

(* the function table of make_funcs *)

let PP2CAUX_B_flookup_make_funcs = prove
 (`!(l:(K#B#C#D)list) f.
     FLOOKUP (pan_to_crep_make_funcs l) f = OPTION_MAP (\(p,b,r). (p,r)) (ALOOKUP l f)`,
  REWRITE_TAC[pan_to_crep_make_funcs_def; LET_DEF; LET_END_DEF;
              CONJUNCT1 ALOOKUP_EQ_FLOOKUP] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; MAP3_def; ALOOKUP_THM; OPTION_MAP_DEF] THEN
  SPEC_TAC(`h:K#B#C#D`,`h:K#B#C#D`) THEN REWRITE_TAC[FORALL_PAIR_THM; o_THM] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[ALOOKUP_THM] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[OPTION_MAP_DEF] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[]);;

let mk_ctxt_code_imp_code_rel = prove
 (`!pan_code:((A)decl)list.
     ALL_DISTINCT (MAP FST (functions pan_code)) /\
     ALL (localised_prog o FST o SND o SND) (functions pan_code) ==>
     pan_to_crepProof_code_rel
       (pan_to_crep_mk_ctxt FEMPTY (pan_to_crep_make_funcs (functions pan_code)) 0
          (get_eids_from_decls pan_code))
       (alist_to_fmap (functions pan_code))
       (alist_to_fmap (compile_to_crep pan_code))`,
  GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[pan_to_crepProof_code_rel_def; pan_to_crep_mk_ctxt_def;
              pan_to_crep_context_INFO.ri_accessors; CONJUNCT1 ALOOKUP_EQ_FLOOKUP] THEN
  MAP_EVERY X_GEN_TAC [`f:mlstring`; `vshs:(mlstring#shape)list`; `prog:(A)panLang_prog`;
                       `rsh:shape`] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC[PP2CAUX_B_flookup_make_funcs; CONJUNCT1 ALOOKUP_EQ_FLOOKUP;
                  PP2CAUX_B_alookup_compile_to_crep; OPTION_MAP_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  CONJ_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP ALOOKUP_MEM) THEN
    UNDISCH_TAC `ALL (localised_prog o FST o SND o SND)
                   (functions (pan_code:((A)decl)list))` THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN
    DISCH_THEN(fun th -> DISCH_THEN(MP_TAC o MATCH_MP th)) THEN REWRITE_TAC[o_THM];
    ALL_TAC] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[injectivity "option"; PAIR_EQ; crep_vars_def; LET_DEF; LET_END_DEF;
              pan_to_crep_comp_func_def; pan_to_crep_make_vmap_def; pan_to_crep_mk_ctxt_def;
              pan_to_crepProof_ctxt_fc_def; MAX_LIST_i_genlist]);;

let mod_eq_lt_eq = prove
 (`!n x m. n < x /\ m < x /\ n MOD x = m MOD x ==> n = m`,
  REPEAT STRIP_TAC THEN UNDISCH_TAC `n MOD x = m MOD x` THEN ASM_SIMP_TAC[MOD_LT]);;

(* HOL4 [local] *)

let pan_to_crepProof_pair_map_I = prove
 (`(\(x:A,y:B). (x,y)) = I`,
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; I_THM]);;

(* the exception numbering *)

let PP2CAUX_B_length_exceptions = prove
 (`!pc:((A)decl)list. LENGTH (exceptions pc) = size_of_eids pc`,
  REWRITE_TAC[size_of_eids_def] THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[exceptions_def; FILTER; LENGTH] THEN
  QCASES_ON "h" THEN ASM_REWRITE_TAC[exceptions_def; is_exn_decl_def; FILTER; LENGTH]);;

let PP2CAUX_B_map_uncurry_pair = prove
 (`!l:(A#B)list. MAP (UNCURRY (\x y. x,y)) l = l`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP] THEN
  SPEC_TAC(`h:A#B`,`h:A#B`) THEN REWRITE_TAC[FORALL_PAIR_THM; UNCURRY_DEF]);;

let PP2CAUX_B_get_eids_alist = prove
 (`!pc:((A)decl)list.
     get_eids_from_decls pc =
     alist_to_fmap (ZIP (MAP FST (exceptions pc))
                        (list_of_seq (\x. (word x):A word) (LENGTH (MAP FST (exceptions pc)))))`,
  GEN_TAC THEN REWRITE_TAC[get_eids_from_decls_def; LET_DEF; LET_END_DEF] THEN
  AP_TERM_TAC THEN SIMP_TAC[MAP2_ZIP; LENGTH_LIST_OF_SEQ; PP2CAUX_B_map_uncurry_pair]);;

let get_eids_imp_excp_rel = prove
 (`!(seids:(mlstring,B)fmap) (pc:((A)decl)list).
     size_of_eids pc < dimword (:A) /\
     FDOM seids = FDOM (get_eids_from_decls pc) ==>
     excp_rel (get_eids_from_decls pc) seids`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[excp_rel_def] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[PP2CAUX_B_get_eids_alist; CONJUNCT1 ALOOKUP_EQ_FLOOKUP] THEN
  (SUBGOAL_THEN `LENGTH (MAP FST (exceptions (pc:((A)decl)list))) < dimword (:A)` MP_TAC THENL
    [ASM_REWRITE_TAC[LENGTH_MAP; PP2CAUX_B_length_exceptions]; ALL_TAC]) THEN
  SPEC_TAC(`MAP FST (exceptions (pc:((A)decl)list))`,`eids:mlstring list`) THEN
  GEN_TAC THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:mlstring`; `e':mlstring`; `n:A word`; `n':A word`] THEN
  STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP ALOOKUP_MEM o check (fun th ->
    try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "ALOOKUP" with Failure _ -> false))) THEN
  ASM_SIMP_TAC[MEM_ZIP; LENGTH_LIST_OF_SEQ; PAIR_EQ] THEN
  DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
  (SUBGOAL_THEN `i < dimword (:A) /\ j < dimword (:A)` STRIP_ASSUME_TAC THENL
    [CONJ_TAC THEN MATCH_MP_TAC LT_TRANS THEN EXISTS_TAC `LENGTH (eids:mlstring list)` THEN
     ASM_REWRITE_TAC[];
     ALL_TAC]) THEN
  SUBGOAL_THEN `i:num = j` (fun th -> ASM_REWRITE_TAC[th]) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) && lhs(concl th) = `n':A word` &&
    free_in `i:num` (concl th))) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) && lhs(concl th) = `n':A word` &&
    free_in `j:num` (concl th))) THEN
  ASM_SIMP_TAC[EL_LIST_OF_SEQ] THEN DISCH_THEN SUBST1_TAC THEN
  DISCH_THEN(MP_TAC o AP_TERM `val:A word->num`) THEN
  REWRITE_TAC[VAL_WORD; GSYM dimword_def] THEN ASM_SIMP_TAC[MOD_LT] THEN
  MESON_TAC[]);;

let mk_ctxt_imp_locals_rel = prove
 (`!(pc:(mlstring#(mlstring#shape)list#C#shape)list) (lcl:(num,(A)word_lab)fmap)
    (es:(mlstring,B word)fmap).
     pan_to_crepProof_locals_rel (pan_to_crep_mk_ctxt FEMPTY (pan_to_crep_make_funcs pc) 0 es)
       (FEMPTY:(mlstring,(A)pan_v)fmap) lcl`,
  REWRITE_TAC[pan_to_crepProof_locals_rel_def; pan_commonProps_no_overlap_def;
              pan_commonProps_ctxt_max_def; pan_to_crep_mk_ctxt_def;
              pan_to_crep_context_INFO.ri_accessors; FLOOKUP_EMPTY; distinctness "option";
              LE_0]);;

(* the parameters of compiled functions are distinct *)

let PP2CAUX_B_all_distinct_crep_vars = prove
 (`!params:(B#shape)list. ALL_DISTINCT (crep_vars params)`,
  REWRITE_TAC[crep_vars_def; LET_DEF; LET_END_DEF; ALL_DISTINCT_GENLIST; I_THM] THEN
  MESON_TAC[]);;

let PP2CAUX_B_params_compile_inl_prog = prove
 (`!(inl_fs:(mlstring,num list # (A)crep_prog)fmap) (l:(mlstring#B#(A)crep_prog)list)
    (P:B->bool).
     ALL (\(name,params,body). P params) (compile_inl_prog inl_fs l) <=>
     ALL (\(name,params,body). P params) l`,
  GEN_TAC THEN REWRITE_TAC[compile_inl_prog_def] THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[MAP; ALL] THEN
  SPEC_TAC(`h:mlstring#B#(A)crep_prog`,`h:mlstring#B#(A)crep_prog`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  ASM_REWRITE_TAC[]);;

let PP2CAUX_B_params_compile_to_crep = prove
 (`!prog:((A)decl)list.
     ALL (\(name,params,body). ALL_DISTINCT params) (compile_to_crep prog)`,
  GEN_TAC THEN REWRITE_TAC[compile_to_crep_def; LET_DEF; LET_END_DEF] THEN
  SPEC_TAC(`pan_to_crep_comp_func (pan_to_crep_make_funcs (functions (prog:((A)decl)list)))
              (get_eids_from_decls prog)`,
           `cf:(mlstring#shape)list->(A)panLang_prog->(A)crep_prog`) THEN
  SPEC_TAC(`functions (prog:((A)decl)list)`,
           `l:(mlstring#(mlstring#shape)list#(A)panLang_prog#shape)list`) THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; ALL] THEN
  SPEC_TAC(`h:mlstring#(mlstring#shape)list#(A)panLang_prog#shape`,
           `h:mlstring#(mlstring#shape)list#(A)panLang_prog#shape`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  ASM_REWRITE_TAC[PP2CAUX_B_all_distinct_crep_vars]);;

let pan_to_crepProof_compile_prog_distinct_params = prove
 (`!prog:((A)decl)list.
     ALL (\(name,params,body). ALL_DISTINCT params) (pan_to_crep_compile_prog prog)`,
  REWRITE_TAC[pan_to_crep_compile_prog_def; compile_inl_top_def; LET_DEF; LET_END_DEF;
              PP2CAUX_B_params_compile_inl_prog; PP2CAUX_B_params_compile_to_crep]);;

(* the observable results of pan and crep runs that correspond *)

let PP2CAUX_B_res_cases = prove
 (CASE_TERM
  `!(rp:((A)pan_result)option) (rc:((B)crep_result)option).
     (match rp with
        SOME pan_TimeOut -> rc = SOME crep_TimeOut
      | SOME (pan_FinalFFI f) -> rc = SOME (crep_FinalFFI f)
      | SOME (pan_Return v) -> (?w. rc = SOME (crepSem_Return w))
      | _ -> F) ==>
     ((match rp with
         SOME pan_TimeOut -> F
       | SOME (pan_FinalFFI _) -> F
       | SOME (pan_Return _) -> F
       | _ -> T) <=> F) /\
     ((match rc with
         SOME crep_TimeOut -> F
       | SOME (crep_FinalFFI _) -> F
       | SOME (crepSem_Return _) -> F
       | _ -> T) <=> F) /\
     (!outcome.
        (match rp with
           SOME (pan_FinalFFI e) -> outcome = FFI_outcome e
         | SOME (pan_Return _) -> outcome = Success
         | _ -> F) <=>
        (match rc with
           SOME (crep_FinalFFI e) -> outcome = FFI_outcome e
         | SOME (crepSem_Return _) -> outcome = Success
         | _ -> F))`,
  GEN_TAC THEN QCASES_ON "rp" THEN REWRITE_TAC[case_def "option"] THEN
  TRY(QCASES_ON "a") THEN REWRITE_TAC[case_def "pan_result"] THEN GEN_TAC THEN
  DISCH_THEN(REPEAT_TCL CHOOSE_THEN SUBST1_TAC) THEN
  REWRITE_TAC[case_def "option"; case_def "crep_result"]);;

(* pan and crep runs of the start function that correspond at every clock *)
(* have the same semantics                                                  *)

let PP2CAUX_B_sem_eq = prove
 (CASE_TERM
  `!(s:(A,FFI)pan_state) (t:(B,FFI)crep_state) start.
     (!k. (match FST (pan_evaluate (panLang_Call NONE start [],pan_state_clock_fupd (K k) s)) with
             SOME pan_TimeOut ->
               FST (crep_evaluate (crep_Call NONE start [],crep_state_clock_fupd (K k) t)) =
               SOME crep_TimeOut
           | SOME (pan_FinalFFI f) ->
               FST (crep_evaluate (crep_Call NONE start [],crep_state_clock_fupd (K k) t)) =
               SOME (crep_FinalFFI f)
           | SOME (pan_Return v) ->
               (?w. FST (crep_evaluate (crep_Call NONE start [],crep_state_clock_fupd (K k) t)) =
                    SOME (crepSem_Return w))
           | _ -> F) /\
          crep_state_ffi (SND (crep_evaluate (crep_Call NONE start [],
                                              crep_state_clock_fupd (K k) t))) =
          pan_state_ffi (SND (pan_evaluate (panLang_Call NONE start [],
                                            pan_state_clock_fupd (K k) s))))
     ==> crep_semantics t start = pan_semantics s start`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o GEN `k:num` o MATCH_MP PP2CAUX_B_res_cases o CONJUNCT1 o
              SPEC `k:num`) THEN
  REWRITE_TAC[pan_semantics_def; crep_semantics_def; LET_DEF; LET_END_DEF] THEN
  ASM_REWRITE_TAC[EXISTS_SIMP] THEN
  SUBGOAL_THEN (CASE_TERM
   `!res:behaviour.
      (?k t' (r:((B)crep_result)option) outcome.
         crep_evaluate (crep_Call NONE start [],
                        crep_state_clock_fupd (K k) (t:(B,FFI)crep_state)) = (r,t') /\
         (match r with
            SOME (crep_FinalFFI e) -> outcome = FFI_outcome e
          | SOME (crepSem_Return _) -> outcome = Success
          | _ -> F) /\
         res = Terminate outcome (ffi_state_io_events (crep_state_ffi t'))) <=>
      (?k t' (r:((A)pan_result)option) outcome.
         pan_evaluate (panLang_Call NONE start [],
                       pan_state_clock_fupd (K k) (s:(A,FFI)pan_state)) = (r,t') /\
         (match r with
            SOME (pan_FinalFFI e) -> outcome = FFI_outcome e
          | SOME (pan_Return _) -> outcome = Success
          | _ -> F) /\
         res = Terminate outcome (ffi_state_io_events (pan_state_ffi t')))`)
   (fun th -> REWRITE_TAC[th]) THEN
  GEN_TAC THEN EQ_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `k:num` THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (is_forall o concl))) THEN
  ASM_REWRITE_TAC[FST; SND] THEN REPEAT STRIP_TAC THENL
   [MAP_EVERY EXISTS_TAC
     [`SND (pan_evaluate (panLang_Call NONE start [],
                          pan_state_clock_fupd (K k) (s:(A,FFI)pan_state)))`;
      `FST (pan_evaluate (panLang_Call NONE start [],
                          pan_state_clock_fupd (K k) (s:(A,FFI)pan_state)))`;
      `outcome:outcome`] THEN
    ASM_REWRITE_TAC[PAIR];
    MAP_EVERY EXISTS_TAC
     [`SND (crep_evaluate (crep_Call NONE start [],
                           crep_state_clock_fupd (K k) (t:(B,FFI)crep_state)))`;
      `FST (crep_evaluate (crep_Call NONE start [],
                           crep_state_clock_fupd (K k) (t:(B,FFI)crep_state)))`;
      `outcome:outcome`] THEN
    ASM_REWRITE_TAC[PAIR] THEN ASM_MESON_TAC[]]);;

let state_rel_imp_semantics_to_crep = prove
 (`!(s:(A,FFI)pan_state) (t:(A,FFI)crep_state) (pan_code:((A)decl)list) start.
     pan_to_crepProof_state_rel s t /\
     ALL_DISTINCT (MAP FST (functions pan_code)) /\
     pan_state_code s = alist_to_fmap (functions pan_code) /\
     crep_state_code t = alist_to_fmap (compile_to_crep pan_code) /\
     pan_state_locals s = FEMPTY /\
     ALL (localised_prog o FST o SND o SND) (functions pan_code) /\
     size_of_eids pan_code < dimword (:A) /\
     FDOM (pan_state_eshapes s) = FDOM (get_eids_from_decls pan_code) /\
     ~(pan_semantics s start = Fail) ==>
     crep_semantics t start = pan_semantics s start`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `nctxt = pan_to_crep_mk_ctxt FEMPTY
                (pan_to_crep_make_funcs (functions (pan_code:((A)decl)list))) 0
                (get_eids_from_decls pan_code)` THEN
  (SUBGOAL_THEN `pan_to_crepProof_code_rel nctxt (pan_state_code (s:(A,FFI)pan_state))
                   (crep_state_code (t:(A,FFI)crep_state))` ASSUME_TAC THENL
    [ASM_REWRITE_TAC[] THEN EXPAND_TAC "nctxt" THEN MATCH_MP_TAC mk_ctxt_code_imp_code_rel THEN
     ASM_REWRITE_TAC[];
     ALL_TAC]) THEN
  (SUBGOAL_THEN `excp_rel (pan_to_crep_context_eids (nctxt:(A)pan_to_crep_context))
                   (pan_state_eshapes (s:(A,FFI)pan_state))` ASSUME_TAC THENL
    [EXPAND_TAC "nctxt" THEN
     REWRITE_TAC[pan_to_crep_mk_ctxt_def; pan_to_crep_context_INFO.ri_accessors] THEN
     MATCH_MP_TAC get_eids_imp_excp_rel THEN ASM_REWRITE_TAC[];
     ALL_TAC]) THEN
  (SUBGOAL_THEN `pan_to_crepProof_locals_rel (nctxt:(A)pan_to_crep_context)
                   (pan_state_locals (s:(A,FFI)pan_state)) (crep_state_locals (t:(A,FFI)crep_state))`
     ASSUME_TAC THENL
    [REWRITE_TAC[ASSUME `pan_state_locals (s:(A,FFI)pan_state) = FEMPTY`] THEN
     EXPAND_TAC "nctxt" THEN REWRITE_TAC[mk_ctxt_imp_locals_rel];
     ALL_TAC]) THEN
  MATCH_MP_TAC PP2CAUX_B_sem_eq THEN X_GEN_TAC `k:num` THEN
  (SUBGOAL_THEN (CASE_TERM
    `~(match FST (pan_evaluate (panLang_Call NONE start [],
                                pan_state_clock_fupd (K k) (s:(A,FFI)pan_state))) with
         SOME pan_TimeOut -> F
       | SOME (pan_FinalFFI _) -> F
       | SOME (pan_Return _) -> F
       | _ -> T)`) ASSUME_TAC THENL
    [UNDISCH_TAC `~(pan_semantics (s:(A,FFI)pan_state) start = Fail)` THEN
     REWRITE_TAC[pan_semantics_def; LET_DEF; LET_END_DEF] THEN
     COND_CASES_TAC THEN REWRITE_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o REWRITE_RULE[NOT_EXISTS_THM]) THEN
     REWRITE_TAC[];
     ALL_TAC]) THEN
  MP_TAC(ISPECL [`panLang_Call NONE start []:(A)panLang_prog`;
                 `pan_state_clock_fupd (K k) (s:(A,FFI)pan_state)`;
                 `FST (pan_evaluate (panLang_Call NONE start [],
                                     pan_state_clock_fupd (K k) (s:(A,FFI)pan_state)))`;
                 `SND (pan_evaluate (panLang_Call NONE start [],
                                     pan_state_clock_fupd (K k) (s:(A,FFI)pan_state)))`;
                 `crep_state_clock_fupd (K k) (t:(A,FFI)crep_state)`;
                 `nctxt:(A)pan_to_crep_context`] pc_compile_correct) THEN
  (ANTS_TAC THENL
    [REWRITE_TAC[PAIR; pan_state_INFO.ri_accfupds; crep_state_INFO.ri_accfupds; K_THM;
                 localised_prog_def; ALL; case_def "option"] THEN
     REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
      [DISCH_TAC THEN UNDISCH_TAC (CASE_TERM
         `~(match FST (pan_evaluate (panLang_Call NONE start [],
                                     pan_state_clock_fupd (K k) (s:(A,FFI)pan_state))) with
              SOME pan_TimeOut -> F
            | SOME (pan_FinalFFI _) -> F
            | SOME (pan_Return _) -> F
            | _ -> T)`) THEN
       ASM_REWRITE_TAC[case_def "option"; case_def "pan_result"];
       QPAT_X_ASSUM "pan_to_crepProof_state_rel s t" MP_TAC THEN
       REWRITE_TAC[pan_to_crepProof_state_rel_def; pan_state_INFO.ri_accfupds;
                   crep_state_INFO.ri_accfupds; K_THM] THEN SIMP_TAC[]];
     ALL_TAC]) THEN
  (SUBGOAL_THEN `pan_to_crep_compile (nctxt:(A)pan_to_crep_context) (panLang_Call NONE start []) =
                 crep_Call NONE start []` SUBST1_TAC THENL
    [ONCE_REWRITE_TAC[pan_to_crep_compile_def] THEN
     REWRITE_TAC[MAP; FLAT; LET_DEF; LET_END_DEF; case_def "option"];
     ALL_TAC]) THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:((A)crep_result)option`
    (X_CHOOSE_THEN `t1:(A,FFI)crep_state` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    QPAT_X_ASSUM "pan_to_crepProof_state_rel _ t1" MP_TAC THEN
    SIMP_TAC[pan_to_crepProof_state_rel_def]] THEN
  UNDISCH_TAC (CASE_TERM
    `~(match FST (pan_evaluate (panLang_Call NONE start [],
                                pan_state_clock_fupd (K k) (s:(A,FFI)pan_state))) with
         SOME pan_TimeOut -> F
       | SOME (pan_FinalFFI _) -> F
       | SOME (pan_Return _) -> F
       | _ -> T)`) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> free_in `r1:((A)crep_result)option` (concl th) &&
                                          not (is_eq (concl th)))) THEN
  SPEC_TAC(`FST (pan_evaluate (panLang_Call NONE start [],
                               pan_state_clock_fupd (K k) (s:(A,FFI)pan_state)))`,
           `rp:((A)pan_result)option`) THEN
  GEN_TAC THEN QCASES_ON "rp" THEN REWRITE_TAC[case_def "option"] THEN
  TRY(QCASES_ON "a") THEN REWRITE_TAC[case_def "pan_result"] THEN MESON_TAC[]);;

(* HOL4 [local] *)

let decs_stcnames_lemma = prove
 (`ALL (\d. is_function d \/ is_exn_decl d) (code:((A)decl)list) ==>
   decs_stcnames ctxt code = SOME ctxt`,
  DISCH_TAC THEN MATCH_MP_TAC decs_stcnames_only_functions THEN
  POP_ASSUM MP_TAC THEN MATCH_MP_TAC MONO_ALL THEN REWRITE_TAC[] THEN MESON_TAC[]);;

(* the code of the program after evaluate_decls *)

let PP2CAUX_B_fdom_get_eids = prove
 (`!pc:((A)decl)list.
     FDOM (get_eids_from_decls pc) = set_of_list (MAP FST (exceptions pc))`,
  GEN_TAC THEN REWRITE_TAC[PP2CAUX_B_get_eids_alist; FDOM_alist_to_fmap] THEN
  SIMP_TAC[MAP_FST_ZIP; LENGTH_LIST_OF_SEQ]);;

let state_rel_imp_semantics_decls_to_crep = prove
 (`!(s:(A,FFI)pan_state) (t:(A,FFI)crep_state) (pan_code:((A)decl)list) start.
     pan_to_crepProof_state_rel (pan_state_structs_fupd (K []) s) t /\
     ALL_DISTINCT (MAP FST (functions pan_code)) /\
     pan_state_code s = FEMPTY /\
     crep_state_code t = alist_to_fmap (compile_to_crep pan_code) /\
     pan_state_locals s = FEMPTY /\
     pan_state_eshapes s = FEMPTY /\
     ALL (localised_prog o FST o SND o SND) (functions pan_code) /\
     ALL (\x. is_function x \/ is_exn_decl x) pan_code /\
     size_of_eids pan_code < dimword (:A) /\
     ~(semantics_decls s start pan_code = Fail) ==>
     crep_semantics t start = semantics_decls s start pan_code`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o ISPEC `[]:(mlstring#struct_info)list` o MATCH_MP
    (GEN_ALL decs_stcnames_lemma)) THEN
  UNDISCH_TAC `~(semantics_decls (s:(A,FFI)pan_state) start pan_code = Fail)` THEN
  ASM_REWRITE_TAC[semantics_decls_def; case_def "option"] THEN
  QCASES_ON "evaluate_decls (pan_state_structs_fupd (K []) (s:(A,FFI)pan_state)) pan_code" THEN
  ASM_REWRITE_TAC[case_def "option"] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP evaluate_decls_only_funs_and_exn_decls o
    CONJ (ASSUME `ALL (\x. is_function x \/ is_exn_decl x) (pan_code:((A)decl)list)`)) THEN
  ASM_REWRITE_TAC[pan_state_INFO.ri_accfupds; K_THM] THEN DISCH_THEN SUBST_ALL_TAC THEN
  MATCH_MP_TAC state_rel_imp_semantics_to_crep THEN EXISTS_TAC `pan_code:((A)decl)list` THEN
  ASM_REWRITE_TAC[pan_state_INFO.ri_accfupds; K_THM] THEN
  ASM_SIMP_TAC[FMAPAUX_FEMPTY_FUPDATE_LIST; FDOM_FUPDATE_LIST; FDOM_FEMPTY; UNION_EMPTY;
               PP2CAUX_B_fdom_get_eids] THEN
  QPAT_X_ASSUM "pan_to_crepProof_state_rel _ t" MP_TAC THEN
  REWRITE_TAC[pan_to_crepProof_state_rel_def; pan_state_INFO.ri_accfupds; K_THM]);;

(* a crep program whose semantics is not Fail has the start function *)

let PP2CAUX_B_crep_sem_has_start = prove
 (`!(t:(A,FFI)crep_state) start.
     ~(crep_semantics t start = Fail) ==>
     ?ns prog. FLOOKUP (crep_state_code t) start = SOME (ns,prog)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN DISCH_TAC THEN
  SUBGOAL_THEN `FLOOKUP (crep_state_code (t:(A,FFI)crep_state)) start = NONE` ASSUME_TAC THENL
   [MP_TAC(ISPEC `FLOOKUP (crep_state_code (t:(A,FFI)crep_state)) start` (cases "option")) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[PAIR];
    ALL_TAC] THEN
  REWRITE_TAC[crep_semantics_def; LET_DEF; LET_END_DEF] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `0` o REWRITE_RULE[NOT_EXISTS_THM]) THEN
  ONCE_REWRITE_TAC[crep_evaluate_def] THEN
  ASM_REWRITE_TAC[OPT_MMAP_def; crep_lookup_code_def; LENGTH; crep_state_INFO.ri_accfupds;
                  K_THM; case_def "option"; case_def "crep_result"]);;

let pan_to_crepProof_state_rel_imp_semantics = prove
 (`!(s:(A,FFI)pan_state) (t:(A,FFI)crep_state) (pan_code:((A)decl)list) start.
     pan_to_crepProof_state_rel s t /\
     ALL_DISTINCT (MAP FST (functions pan_code)) /\
     pan_state_code s = alist_to_fmap (functions pan_code) /\
     crep_state_code t = alist_to_fmap (pan_to_crep_compile_prog pan_code) /\
     pan_state_locals s = FEMPTY /\
     ALL (localised_prog o FST o SND o SND) (functions pan_code) /\
     size_of_eids pan_code < dimword (:A) /\
     FDOM (pan_state_eshapes s) = FDOM (get_eids_from_decls pan_code) /\
     ~(pan_semantics s start = Fail) ==>
     crep_semantics t start = pan_semantics s start`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:(A,FFI)pan_state`;
                 `crep_state_code_fupd (K (alist_to_fmap (compile_to_crep (pan_code:((A)decl)list))))
                    (t:(A,FFI)crep_state)`;
                 `pan_code:((A)decl)list`; `start:mlstring`] state_rel_imp_semantics_to_crep) THEN
  (ANTS_TAC THENL
    [ASM_REWRITE_TAC[crep_state_INFO.ri_accfupds; K_THM] THEN
     QPAT_X_ASSUM "pan_to_crepProof_state_rel s t" MP_TAC THEN
     REWRITE_TAC[pan_to_crepProof_state_rel_def; crep_state_INFO.ri_accfupds; K_THM];
     ALL_TAC]) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `~(crep_semantics (crep_state_code_fupd (K (alist_to_fmap
                   (compile_to_crep (pan_code:((A)decl)list)))) (t:(A,FFI)crep_state)) start = Fail)`
    ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `ns:num list` (X_CHOOSE_TAC `prog:(A)crep_prog`) o
    MATCH_MP PP2CAUX_B_crep_sem_has_start) THEN
  FIRST_X_ASSUM(fun th -> if is_eq(concl th) &&
      (try fst(dest_const(rator(rator(lhs(concl th))))) = "crep_semantics" with Failure _ -> false)
    then SUBST1_TAC(SYM th) else NO_TAC) THEN
  MATCH_MP_TAC crep_inlineProof_state_rel_imp_semantics THEN
  MAP_EVERY EXISTS_TAC [`compile_to_crep (pan_code:((A)decl)list)`;
                        `MAP FST (functions (FILTER inlinable (pan_code:((A)decl)list)))`;
                        `ns:num list`; `prog:(A)crep_prog`] THEN
  ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[crep_state_INFO.ri_accfupds; K_THM]) THEN
  ASM_SIMP_TAC[first_compile_to_crep_all_distinct; state_rel_code_def; locals_strong_rel_def;
               crep_state_INFO.ri_accfupds; K_THM] THEN
  REWRITE_TAC[pan_to_crep_compile_prog_def; LET_DEF; LET_END_DEF]);;

let pan_to_crepProof_state_rel_imp_semantics_decls = prove
 (`!(s:(A,FFI)pan_state) (t:(A,FFI)crep_state) (pan_code:((A)decl)list) start.
     pan_to_crepProof_state_rel (pan_state_structs_fupd (K []) s) t /\
     ALL_DISTINCT (MAP FST (functions pan_code)) /\
     pan_state_code s = FEMPTY /\
     crep_state_code t = alist_to_fmap (pan_to_crep_compile_prog pan_code) /\
     pan_state_locals s = FEMPTY /\
     pan_state_eshapes s = FEMPTY /\
     ALL (localised_prog o FST o SND o SND) (functions pan_code) /\
     ALL (\x. is_function x \/ is_exn_decl x) pan_code /\
     size_of_eids pan_code < dimword (:A) /\
     ~(semantics_decls s start pan_code = Fail) ==>
     crep_semantics t start = semantics_decls s start pan_code`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o ISPEC `[]:(mlstring#struct_info)list` o MATCH_MP
    (GEN_ALL decs_stcnames_lemma)) THEN
  UNDISCH_TAC `~(semantics_decls (s:(A,FFI)pan_state) start pan_code = Fail)` THEN
  ASM_REWRITE_TAC[semantics_decls_def; case_def "option"] THEN
  QCASES_ON "evaluate_decls (pan_state_structs_fupd (K []) (s:(A,FFI)pan_state)) pan_code" THEN
  ASM_REWRITE_TAC[case_def "option"] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP evaluate_decls_only_funs_and_exn_decls o
    CONJ (ASSUME `ALL (\x. is_function x \/ is_exn_decl x) (pan_code:((A)decl)list)`)) THEN
  ASM_REWRITE_TAC[pan_state_INFO.ri_accfupds; K_THM] THEN DISCH_THEN SUBST_ALL_TAC THEN
  MATCH_MP_TAC pan_to_crepProof_state_rel_imp_semantics THEN
  EXISTS_TAC `pan_code:((A)decl)list` THEN
  ASM_REWRITE_TAC[pan_state_INFO.ri_accfupds; K_THM] THEN
  ASM_SIMP_TAC[FMAPAUX_FEMPTY_FUPDATE_LIST; FDOM_FUPDATE_LIST; FDOM_FEMPTY; UNION_EMPTY;
               PP2CAUX_B_fdom_get_eids] THEN
  QPAT_X_ASSUM "pan_to_crepProof_state_rel _ t" MP_TAC THEN
  REWRITE_TAC[pan_to_crepProof_state_rel_def; pan_state_INFO.ri_accfupds; K_THM]);;
