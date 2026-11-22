(* ========================================================================= *)
(* crep_to_loopProof: port of HOL4 pancake/proofs/crep_to_loopProofScript.sml *)
(* (CakeML v3479).  Correctness proof for crep_to_loop.                      *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - Names as notes/naming/names.tsv says (state_rel, globals_rel, ctxt_fc,  *)
(*   code_rel, ctxt_max, locals_rel, ... get the prefix crep_to_loopProof_). *)
(*   crepSem's names are crep_..., loopSem's loop_..., wordLang's word_loc   *)
(*   constructors wl_Word and wl_Loc; panSem's word_lab constructor is Word. *)
(* - HOL4 states ncompile_correct first and proves it case by case          *)
(*   (suspend and Resume).  Here PC2LAUX_ncompile_stmt is its statement,     *)
(*   PC2LAUX_ncompile_case c the case of crep_evaluate_ind for the crepLang *)
(*   constructor c (the goal of HOL4's Resume ncompile_correct[c]), each    *)
(*   case is the lemma PC2LAUX_ncompile_<c>, and ncompile_correct follows    *)
(*   them (HOL4 Finalise).  Other PC2LAUX_ names are local helpers for       *)
(*   steps HOL4 does inline.                                                 *)
(* - HOL4 temp_delsimps of sptree rewrites: the kit has no file-local        *)
(*   deletion (cake_del_simps acts everywhere), so the proofs live with the *)
(*   sptree rewrites of the kit's simpset.  HOL4 [local] theorems are bound  *)
(*   globally here (no name clashes).                                        *)
(* - GENLIST f n is list_of_seq f n, $+ n is (+) n, EVERY is ALL, ZIP (a,b)  *)
(*   is ZIP a b, IS_PREFIX ev ev' is ev' <<= ev, LUB is build_lprefix_lub,  *)
(*   fromList is llist_fromList; r with <| f1 := v1; f2 := v2 |> is          *)
(*   rec_f2_fupd (K v2) (rec_f1_fupd (K v1) r).  Every MAP2 and ZIP of the   *)
(*   statements has lists of equal lengths (no deviations).                  *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "pancake/semantics/crepProps.ml";;
needs "pancake/semantics/loopProps.ml";;
needs "pancake/semantics/pan_commonProps.ml";;
needs "pancake/proofs/loop_liveProof.ml";;
needs "pancake/semantics/crepSem.ml";;
needs "pancake/loopLang.ml";;
needs "pancake/semantics/loopSem.ml";;
needs "pancake/pan_common.ml";;
needs "pancake/proofs/crep_arithProof.ml";;
needs "pancake/crep_to_loop.ml";;

prioritize_num();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)

(* HOL4 temp_delsimps fromAList_def, domain_union, domain_inter,           *)
(* domain_difference, domain_map, map_def, lookup_rwts, insert_notEmpty,   *)
(* isEmpty_union: the kit has no file-local deletion (cake_del_simps acts  *)
(* everywhere), so the proofs here live with the sptree rewrites of the    *)
(* kit's simpset.                                                           *)

let evaluate_nested_seq_append_first = CONJUNCT1 evaluate_nested_seq_cases;;

let evaluate_none_nested_seq_append =
  CONJUNCT1 (CONJUNCT2 evaluate_nested_seq_cases);;

let evaluate_not_none_nested_seq_append =
  CONJUNCT2 (CONJUNCT2 evaluate_nested_seq_cases);;

(* state relation *)

let crep_to_loopProof_state_rel_def = cake_def
  `crep_to_loopProof_state_rel (s:(A,FFI)crep_state) (t:(A,FFI)loop_state) <=>
     crep_state_memaddrs s = loop_state_mdomain t /\
     crep_state_sh_memaddrs s = loop_state_sh_mdomain t /\
     crep_state_clock s = loop_state_clock t /\
     crep_state_be s = loop_state_be t /\
     crep_state_ffi s = loop_state_ffi t /\
     crep_state_base_addr s = loop_state_base_addr t /\
     crep_state_top_addr s = loop_state_top_addr t`;;

(* Loc encodes label of a function, e.g: Loc n1 n2 represents the label n2  *)
(* inside the function n1                                                   *)

let wlab_wloc_def = cake_def
  `wlab_wloc (Word (w:A word)) = wl_Word w`;;

let mem_rel_def = cake_def
  `mem_rel smem tmem dom <=>
     !ad:B. ad IN dom ==> wlab_wloc (smem ad:(A)word_lab) = tmem ad`;;

let crep_to_loopProof_globals_rel_def = cake_def
  `crep_to_loopProof_globals_rel sglobals tglobals <=>
     !(ad:B) (v:(A)word_lab). FLOOKUP sglobals ad = SOME v ==>
       FLOOKUP tglobals ad = SOME (wlab_wloc v)`;;

let distinct_funcs_def = cake_def
  `distinct_funcs (fm:(A,B#C)fmap) <=>
     !x y n m rm rm'. FLOOKUP fm x = SOME (n,rm) /\
       FLOOKUP fm y = SOME (m,rm') /\ n = m ==> x = y`;;

(* could have been stated differently *)

let crep_to_loopProof_ctxt_fc_def = cake_def
  `crep_to_loopProof_ctxt_fc c cvs ns args =
     crep_to_loop_context_REC (FEMPTY |++ ZIP ns args) cvs (MAX_LIST args) c`;;

let crep_to_loopProof_code_rel_def = cake_def
  `crep_to_loopProof_code_rel ctxt
     (s_code:(mlstring,num list#(A)crep_prog)fmap)
     (t_code:(num list#(A)loop_prog)spt) <=>
   distinct_funcs (crep_to_loop_context_funcs ctxt) /\
   !f ns prog.
     FLOOKUP s_code f = SOME (ns,prog) ==>
     ?loc len. FLOOKUP (crep_to_loop_context_funcs ctxt) f = SOME (loc,len) /\
       LENGTH ns = len /\
       (let args = list_of_seq I len in
        let nctxt = crep_to_loopProof_ctxt_fc (crep_to_loop_context_target ctxt)
                      (crep_to_loop_context_funcs ctxt) ns args in
        lookup loc t_code =
          SOME (args,ocompile nctxt (list_to_num_set args) prog))`;;

let crep_to_loopProof_ctxt_max_def = cake_def
  `crep_to_loopProof_ctxt_max (n:num) (fm:(A,num)fmap) <=>
     !v m. FLOOKUP fm v = SOME m ==> m <= n`;;

let distinct_vars_def = cake_def
  `distinct_vars (fm:(A,B)fmap) <=>
     (!x y n m. FLOOKUP fm x = SOME n /\
                FLOOKUP fm y = SOME m /\ n = m ==> x = y)`;;

let crep_to_loopProof_locals_rel_def = cake_def
  `crep_to_loopProof_locals_rel ctxt (l:num_set)
     (s_locals:(num,(A)word_lab)fmap) t_locals <=>
   distinct_vars (crep_to_loop_context_vars ctxt) /\
   crep_to_loopProof_ctxt_max (crep_to_loop_context_vmax ctxt)
     (crep_to_loop_context_vars ctxt) /\
   domain l SUBSET domain t_locals /\
   !vname v.
     FLOOKUP s_locals vname = SOME v ==>
     ?n. FLOOKUP (crep_to_loop_context_vars ctxt) vname = SOME n /\ n IN domain l /\
         lookup n t_locals = SOME (wlab_wloc v)`;;

let crep_to_loopProof_state_rel_intro = prove
 (`crep_to_loopProof_state_rel (s:(A,FFI)crep_state) (t:(A,FFI)loop_state) <=>
     crep_state_memaddrs s = loop_state_mdomain t /\
     crep_state_sh_memaddrs s = loop_state_sh_mdomain t /\
     crep_state_clock s = loop_state_clock t /\
     crep_state_be s = loop_state_be t /\
     crep_state_ffi s = loop_state_ffi t /\
     crep_state_base_addr s = loop_state_base_addr t /\
     crep_state_top_addr s = loop_state_top_addr t`,
  RW[crep_to_loopProof_state_rel_def]);;

let crep_to_loopProof_locals_rel_intro = prove
 (`crep_to_loopProof_locals_rel ctxt l (s_locals:(num,(A)word_lab)fmap) t_locals ==>
   distinct_vars (crep_to_loop_context_vars ctxt) /\
   crep_to_loopProof_ctxt_max (crep_to_loop_context_vmax ctxt)
     (crep_to_loop_context_vars ctxt) /\
   domain l SUBSET domain t_locals /\
   !vname v.
     FLOOKUP s_locals vname = SOME v ==>
     ?n. FLOOKUP (crep_to_loop_context_vars ctxt) vname = SOME n /\ n IN domain l /\
         lookup n t_locals = SOME (wlab_wloc v)`,
  RW[crep_to_loopProof_locals_rel_def]);;

let crep_to_loopProof_code_rel_intro = prove
 (`crep_to_loopProof_code_rel ctxt
     (s_code:(mlstring,num list#(A)crep_prog)fmap) t_code ==>
   distinct_funcs (crep_to_loop_context_funcs ctxt) /\
   !f ns prog.
     FLOOKUP s_code f = SOME (ns,prog) ==>
     ?loc len. FLOOKUP (crep_to_loop_context_funcs ctxt) f = SOME (loc,len) /\
       LENGTH ns = len /\
       (let args = list_of_seq I len in
        let nctxt = crep_to_loopProof_ctxt_fc (crep_to_loop_context_target ctxt)
                      (crep_to_loop_context_funcs ctxt) ns args in
        lookup loc t_code =
          SOME (args,ocompile nctxt (list_to_num_set args) prog))`,
  RW[crep_to_loopProof_code_rel_def]);;

let mem_rel_intro = prove
 (`mem_rel smem tmem dm ==>
   !ad:B. ad IN dm ==> wlab_wloc (smem ad:(A)word_lab) = tmem ad`,
  RW[mem_rel_def] THEN ASM_METIS_TAC[]);;

let crep_to_loopProof_globals_rel_intro = prove
 (`crep_to_loopProof_globals_rel sglobals tglobals ==>
   !(ad:B) (v:(A)word_lab). FLOOKUP sglobals ad = SOME v ==>
     FLOOKUP tglobals ad = SOME (wlab_wloc v)`,
  RW[crep_to_loopProof_globals_rel_def] THEN ASM_METIS_TAC[]);;

let state_rel_clock_add_zero = prove
 (`!(s:(A,FFI)crep_state) (t:(A,FFI)loop_state).
     crep_to_loopProof_state_rel s t ==>
     ?ck. crep_to_loopProof_state_rel s
            (loop_state_clock_fupd (K (ck + loop_state_clock t)) t)`,
  RW[] THEN QEXISTS_TAC "0" THEN
  FS[crep_to_loopProof_state_rel_def; loop_state_component_equality]);;

let locals_rel_insert_gt_vmax = prove
 (`!ct cset lcl lcl' n (w:(A)word_loc).
     crep_to_loopProof_locals_rel ct cset lcl lcl' /\
     crep_to_loop_context_vmax ct < n ==>
     crep_to_loopProof_locals_rel ct cset lcl (insert n w lcl')`,
  RW[] THEN
  FS([crep_to_loopProof_locals_rel_def; SUBSET_INSERT_RIGHT; lookup_insert;
      crep_to_loopProof_ctxt_max_def] @ all_case_eqs()) THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP th)) THEN
  QEXISTS_TAC "n'" THEN ASM_REWRITE_TAC[] THEN DISJ2_TAC THEN ASM_REWRITE_TAC[] THEN
  RES_TAC THEN ASM_ARITH_TAC);;

let locals_rel_cutset_prop = prove
 (`!ct cset (lcl:(num,(A)word_lab)fmap) lcl' cset' lcl''.
     crep_to_loopProof_locals_rel ct cset lcl lcl' /\
     crep_to_loopProof_locals_rel ct cset' lcl lcl'' /\
     subspt cset cset' ==>
     crep_to_loopProof_locals_rel ct cset lcl lcl''`,
  RW[crep_to_loopProof_locals_rel_def] THENL
   [ASM_METIS_TAC[subspt_domain; SUBSET_TRANS];
    RES_TAC THEN FS[] THEN RVEQ_TAC THEN FS[]]);;

let write_bytearray_mem_rel = prove
 (`!nb (sm:A word->(A)word_lab) tm w dm be.
     mem_rel sm tm dm ==>
     mem_rel (pan_write_bytearray w nb sm dm be) (write_bytearray w nb tm dm be) dm`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[pan_write_bytearray_def; write_bytearray_def] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`sm:A word->(A)word_lab`; `tm:A word->(A)word_loc`;
    `word_add w (word 1):A word`; `dm:A word->bool`; `be:bool`]) THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY ABBREV_TAC
   [`sm1 = pan_write_bytearray (word_add (w:A word) (word 1)) t sm dm be`;
    `tm1 = write_bytearray (word_add (w:A word) (word 1)) t tm dm be`] THEN
  DISCH_TAC THEN REWRITE_TAC[pan_mem_store_byte_def; mem_store_byte_aux_def] THEN
  QCASES_ON "sm1 (byte_align w:A word)" THEN CASE_REWRITE_TAC[] THEN
  ASM_CASES_TAC `byte_align (w:A word) IN dm` THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `(tm1:A word->(A)word_loc) (byte_align (w:A word)) = wl_Word (a:A word)`
      SUBST1_TAC THENL
     [FIRST_ASSUM(MP_TAC o SPEC `byte_align (w:A word)` o REWRITE_RULE[mem_rel_def]) THEN
      ASM_REWRITE_TAC[wlab_wloc_def] THEN MESON_TAC[];
      ALL_TAC] THEN
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[mem_rel_def; APPLY_UPDATE_THM] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[wlab_wloc_def] THEN
    ASM_MESON_TAC[mem_rel_def];
    QCASES_ON "tm1 (byte_align w:A word)" THEN CASE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[]]);;

let evaluate_comb_seq = prove
 (`!p (s:(A,FFI)loop_state) t q r.
     loop_evaluate (p,s) = (NONE,t) /\ loop_evaluate (q,t) = (NONE,r) ==>
     loop_evaluate (loop_Seq p q,s) = (NONE,r)`,
  RW[] THEN FS[loop_evaluate_def]);;

let cut_sets_MAPi_Assign = prove
 (`!(les:((A)loop_exp)list) cs offset.
     cut_sets cs (loop_nested_seq (MAPi (\n. loop_Assign (n + offset)) les)) =
     list_insert (list_of_seq ((+) offset) (LENGTH les)) cs`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAPi_DEF; LENGTH; loop_nested_seq_def; cut_sets_def; LIST_OF_SEQ;
              list_insert_def; o_DEF] THEN
  REPEAT GEN_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`insert offset one cs`; `SUC offset`]) THEN
  REWRITE_TAC[ADD_CLAUSES] THEN DISCH_THEN SUBST1_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN ARITH_TAC);;

let assigned_vars_MAPi_Assign = prove
 (`!(les:((A)loop_exp)list) offset.
     loop_assigned_vars (loop_nested_seq (MAPi (\n. loop_Assign (n + offset)) les)) =
     list_of_seq ((+) offset) (LENGTH les)`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAPi_DEF; LENGTH; loop_nested_seq_def; loop_assigned_vars_def;
              LIST_OF_SEQ; o_DEF; APPEND] THEN
  GEN_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `SUC offset`) THEN
  REWRITE_TAC[ADD_CLAUSES] THEN DISCH_THEN SUBST1_TAC THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN ARITH_TAC);;

let survives_MAPi_Assign = prove
 (`!n (les:((A)loop_exp)list) offset.
     survives n (loop_nested_seq (MAPi (\n. loop_Assign (n + offset)) les)) = T`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[MAPi_DEF; loop_nested_seq_def; survives_def; o_DEF] THEN
  GEN_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `SUC offset`) THEN
  REWRITE_TAC[ADD_CLAUSES]);;

let insert_insert_eq = prove
 (`insert a (b:A) (insert a b c) = insert a b c`,
  RW[ONCE insert_insert]);;

let list_insert_SNOC = prove
 (`!y l x. list_insert (SNOC x y) l = insert x one (list_insert y l)`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[list_insert_def; SNOC]);;

let compile_exps_alt = prove
 (CASE_TERM
  `crep_to_loop_compile_exps ctxt tmp l ([]:((A)crep_exp)list) = ([],[],tmp,l) /\
   crep_to_loop_compile_exps ctxt tmp l (CONS (e:(A)crep_exp) es) =
     let (p,le,tmp',l') = crep_to_loop_compile_exp ctxt tmp l e in
     let (p1,les,tmp'',l'') = crep_to_loop_compile_exps ctxt tmp' l' es in
     (APPEND p p1,CONS le les,tmp'',l'')`,
  CONJ_TAC THEN GEN_REWRITE_TAC LAND_CONV [crep_to_loop_compile_exp_def] THEN
  CASE_REWRITE_TAC[]);;

let crep_to_loopProof_list_insert_insert = prove
 (`!x xs l. insert x one (list_insert xs l) = list_insert xs (insert x one l)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[list_insert_def] THEN
  GEN_TAC THEN AP_TERM_TAC THEN ASM_CASES_TAC `h:num = x` THEN
  ASM_SIMP_TAC[insert_shadow; insert_swap]);;

let list_insert_append = prove
 (`!xs ys l. list_insert (APPEND xs ys) l = list_insert xs (list_insert ys l)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[list_insert_def; APPEND; crep_to_loopProof_list_insert_insert]);;

(* ------------------------------------------------------------------------- *)

(* HOL4 lines 420-770: compile_exp_out_rel_cases ..                        *)
(* compile_exps_le_tmp_domain                                               *)

(* the cases of an induction on crep_to_loop_compile_exp_ind for statements *)
(* about crep_to_loop_compile_exp ct tmp l e = (p,le,ntmp,nl): the         *)
(* hypotheses are stripped and the equation is unfolded once               *)

let PC2LAUX_CE_SETUP_TAC =
  let is_ce th =
    let t = concl th in
    is_eq t &&
    (let h,_ = strip_comb (lhs t) in
     is_const h &&
     mem (fst(dest_const h)) ["crep_to_loop_compile_exp"; "crep_to_loop_compile_exps"]) in
  REPEAT (GEN_TAC ORELSE DISCH_THEN STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(fun th ->
    if is_ce th then MP_TAC (ONCE_REWRITE_RULE[crep_to_loop_compile_exp_def] th)
    else failwith "PC2LAUX_CE_SETUP_TAC");;

let PC2LAUX_Assign_add_comm = prove
 (`!tmp. (\n. loop_Assign (tmp + n)):num->(A)loop_exp->(A)loop_prog =
         (\n. loop_Assign (n + tmp))`,
  REWRITE_TAC[FUN_EQ_THM] THEN MESON_TAC[ADD_SYM]);;

let PC2LAUX_comp_syntax_ok_MAPi_Assign = prove
 (`!(les:((A)loop_exp)list) cs offset.
     comp_syntax_ok cs (loop_nested_seq (MAPi (\n. loop_Assign (n + offset)) les))`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAPi_DEF; loop_nested_seq_def; comp_syntax_ok_def; o_DEF] THEN
  REPEAT GEN_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
    [`cut_sets cs (loop_Assign (0 + offset) (h:(A)loop_exp))`; `SUC offset`]) THEN
  REWRITE_TAC[ADD_CLAUSES]);;

let compile_exp_out_rel_cases = prove
 (`(!ct tmp l (e:(A)crep_exp) p le ntmp nl.
     crep_to_loop_compile_exp ct tmp l e = (p,le,ntmp,nl) ==>
     comp_syntax_ok l (loop_nested_seq p) /\ tmp <= ntmp /\
     nl = cut_sets l (loop_nested_seq p)) /\
   (!ct tmp l (e:((A)crep_exp)list) p le ntmp nl.
     crep_to_loop_compile_exps ct tmp l e = (p,le,ntmp,nl) ==>
     comp_syntax_ok l (loop_nested_seq p) /\ tmp <= ntmp /\
     nl = cut_sets l (loop_nested_seq p) /\ LENGTH le = LENGTH e)`,
  MATCH_MP_TAC crep_to_loop_compile_exp_ind THEN REPEAT CONJ_TAC THEN
  PC2LAUX_CE_SETUP_TAC THEN
  TRY (DISCH_TAC THEN REPEAT PAIRARG_TAC THEN RFS[] THEN RVEQ_TAC THEN
       RFS[loop_nested_seq_def; comp_syntax_ok_def; cut_sets_def] THEN NO_TAC) THENL
   [(* Load32 *)
    DISCH_TAC THEN REPEAT PAIRARG_TAC THEN RFS[] THEN RVEQ_TAC THEN
    ASM_SIMP_TAC[comp_syn_ok_nested_seq; cut_sets_nested_seq; loop_nested_seq_def;
                 comp_syntax_ok_def; cut_sets_def; insert_shadow] THEN
    ASM_ARITH_TAC;
    (* LoadByte *)
    DISCH_TAC THEN REPEAT PAIRARG_TAC THEN RFS[] THEN RVEQ_TAC THEN
    ASM_SIMP_TAC[comp_syn_ok_nested_seq; cut_sets_nested_seq; loop_nested_seq_def;
                 comp_syntax_ok_def; cut_sets_def; insert_shadow] THEN
    ASM_ARITH_TAC;
    (* Crepop *)
    DISCH_TAC THEN REPEAT PAIRARG_TAC THEN RFS[] THEN RVEQ_TAC THEN
    QCASES_ON "cop" THEN
    QPAT_X_ASSUM "compile_crepop _ _ _ _ _ _ = _"
      (MP_TAC o REWRITE_RULE[compile_crepop_def]) THEN
    COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    (CONJ_TAC THENL
      [MATCH_MP_TAC comp_syn_ok_nested_seq THEN CONJ_TAC THENL
        [MATCH_MP_TAC comp_syn_ok_nested_seq THEN
         ASM_REWRITE_TAC[PC2LAUX_Assign_add_comm; PC2LAUX_comp_syntax_ok_MAPi_Assign];
         REWRITE_TAC[loop_nested_seq_def; comp_syntax_ok_def]];
       ALL_TAC] THEN
     CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
     REWRITE_TAC[cut_sets_nested_seq; PC2LAUX_Assign_add_comm; cut_sets_MAPi_Assign;
                 loop_nested_seq_def; cut_sets_def] THEN
     CASE_REWRITE_TAC[]) THENL
     [SUBGOAL_THEN `((tmp + LENGTH (les:((A)loop_exp)list)) + 1) - tmp = SUC (LENGTH les)`
        SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[GENLIST; list_insert_SNOC] THEN
      MATCH_MP_TAC insert_swap THEN ARITH_TAC;
      REWRITE_TAC[ARITH_RULE `(tmp + n) - tmp = n`; insert_shadow]];
    (* Cmp *)
    DISCH_TAC THEN REPEAT PAIRARG_TAC THEN RFS[] THEN RVEQ_TAC THEN
    REWRITE_TAC[prog_if_def] THEN CONJ_TAC THENL
     [MATCH_MP_TAC comp_syn_ok_nested_seq THEN CONJ_TAC THENL
       [MATCH_MP_TAC comp_syn_ok_nested_seq THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[cut_sets_nested_seq; loop_nested_seq_def; comp_syntax_ok_def;
                    cut_sets_def; list_insert_def] THEN
        EXISTS_TAC `[]:num list` THEN REWRITE_TAC[FOLDL]];
      CONJ_TAC THENL
       [ASM_ARITH_TAC;
        REWRITE_TAC[cut_sets_nested_seq; loop_nested_seq_def; cut_sets_def]]];
    (* Shift *)
    DISCH_TAC THEN REPEAT PAIRARG_TAC THEN RFS[] THEN RVEQ_TAC THEN
    ASM_SIMP_TAC[cut_sets_nested_seq; comp_syn_ok_nested_seq] THEN ASM_ARITH_TAC;
    (* compile_exps *)
    QCASES_ON "cps" THEN CASE_REWRITE_TAC[] THEN DISCH_TAC THEN REPEAT PAIRARG_TAC THEN
    RFS[] THEN RVEQ_TAC THENL
     [REWRITE_TAC[loop_nested_seq_def; comp_syntax_ok_def; cut_sets_def];
      ASM_SIMP_TAC[cut_sets_nested_seq; comp_syn_ok_nested_seq; LENGTH] THEN
      ASM_ARITH_TAC]]);;

let compile_exp_out_rel = CONJUNCT1 compile_exp_out_rel_cases;;

let compile_exps_out_rel = CONJUNCT2 compile_exp_out_rel_cases;;

let comp_exp_assigned_vars_tmp_bound_cases = prove
 (`(!ct tmp l (e:(A)crep_exp) p le ntmp nl n.
     crep_to_loop_compile_exp ct tmp l e = (p,le,ntmp,nl) /\
     MEM n (loop_assigned_vars (loop_nested_seq p)) ==>
     tmp <= n /\ n < ntmp) /\
   (!ct tmp l (e:((A)crep_exp)list) p le ntmp nl n.
     crep_to_loop_compile_exps ct tmp l e = (p,le,ntmp,nl) /\
     MEM n (loop_assigned_vars (loop_nested_seq p)) ==>
     tmp <= n /\ n < ntmp)`,
  MATCH_MP_TAC crep_to_loop_compile_exp_ind THEN REPEAT CONJ_TAC THEN
  PC2LAUX_CE_SETUP_TAC THEN
  TRY (QCASES_ON "cps" THEN CASE_REWRITE_TAC[]) THEN
  DISCH_TAC THEN REPEAT PAIRARG_TAC THEN RFS[] THEN RVEQ_TAC THEN
  TRY (QCASES_ON "cop" THEN
       QPAT_X_ASSUM "compile_crepop _ _ _ _ _ _ = _"
         (MP_TAC o REWRITE_RULE[compile_crepop_def]) THEN
       COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC) THEN
  IMP_RES_TAC compile_exp_out_rel THEN IMP_RES_TAC compile_exps_out_rel THEN
  RFS[assigned_vars_nested_seq_split; loop_nested_seq_def; loop_assigned_vars_def;
      MEM_APPEND; MEM; prog_if_def; PC2LAUX_Assign_add_comm; assigned_vars_MAPi_Assign;
      MEM_GENLIST] THEN
  TRY (RES_TAC THEN ASM_ARITH_TAC));;

let comp_exp_assigned_vars_tmp_bound = CONJUNCT1 comp_exp_assigned_vars_tmp_bound_cases;;

let comp_exps_assigned_vars_tmp_bound = CONJUNCT2 comp_exp_assigned_vars_tmp_bound_cases;;

(* the two kinds of goals that remain for compound expressions: a variable *)
(* of the first part (its induction hypothesis, then cut_sets keeps it) and *)
(* of the second part (its induction hypothesis, with the domain grown)     *)

let PC2LAUX_LE_TMP_FIRST_TAC =
  RES_TAC THEN CONJ_TAC THENL
   [ASM_ARITH_TAC; MATCH_MP_TAC comp_syn_cut_sets_mem_domain THEN ASM_REWRITE_TAC[]];;

let PC2LAUX_LE_TMP_SECOND_TAC =
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `m:num` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[cut_sets_union_domain_subset; SUBSET];;

let compile_exp_le_tmp_domain_cases = prove
 (`(!ct tmp l (e:(A)crep_exp) p le tmp' l' n.
     crep_to_loopProof_ctxt_max (crep_to_loop_context_vmax ct)
       (crep_to_loop_context_vars ct) /\
     crep_to_loop_compile_exp ct tmp l e = (p,le,tmp',l') /\
     crep_to_loop_context_vmax ct < tmp /\
     (!n. MEM n (var_cexp e) ==>
          ?m. FLOOKUP (crep_to_loop_context_vars ct) n = SOME m /\ m IN domain l) /\
     MEM n (locals_touched le) ==>
     n < tmp' /\ n IN domain l') /\
   (!ct tmp l (es:((A)crep_exp)list) p les tmp' l' n.
     crep_to_loopProof_ctxt_max (crep_to_loop_context_vmax ct)
       (crep_to_loop_context_vars ct) /\
     crep_to_loop_compile_exps ct tmp l es = (p,les,tmp',l') /\
     crep_to_loop_context_vmax ct < tmp /\
     (!n. MEM n (FLAT (MAP var_cexp es)) ==>
          ?m. FLOOKUP (crep_to_loop_context_vars ct) n = SOME m /\ m IN domain l) /\
     MEM n (FLAT (MAP locals_touched les)) ==>
     n < tmp' /\ n IN domain l')`,
  MATCH_MP_TAC crep_to_loop_compile_exp_ind THEN REPEAT CONJ_TAC THEN
  PC2LAUX_CE_SETUP_TAC THEN
  TRY (QCASES_ON "cps" THEN CASE_REWRITE_TAC[]) THEN
  DISCH_TAC THEN REPEAT PAIRARG_TAC THEN RFS[] THEN RVEQ_TAC THEN
  TRY (QCASES_ON "cop" THEN
       QPAT_X_ASSUM "compile_crepop _ _ _ _ _ _ = _"
         (MP_TAC o REWRITE_RULE[compile_crepop_def]) THEN
       COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC) THEN
  IMP_RES_TAC compile_exp_out_rel THEN IMP_RES_TAC compile_exps_out_rel THEN
  RFS[locals_touched_def; var_cexp_def; MEM; MEM_APPEND; FLAT; MAP; ETA_AX;
      domain_insert; IN_INSERT; domain_list_insert; IN_UNION; set_of_list] THEN
  RVEQ_TAC THENL
   [(* Var *)
    ASM_REWRITE_TAC[crep_to_loop_find_var_def] THEN
    CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
    QPAT_X_ASSUM "crep_to_loopProof_ctxt_max _ _"
      (MP_TAC o REWRITE_RULE[crep_to_loopProof_ctxt_max_def]) THEN
    DISCH_THEN(MP_TAC o SPECL [`v:num`; `m:num`]) THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC;
    (* Shift *)
    PC2LAUX_LE_TMP_FIRST_TAC;
    PC2LAUX_LE_TMP_SECOND_TAC;
    (* compile_exps *)
    PC2LAUX_LE_TMP_FIRST_TAC;
    PC2LAUX_LE_TMP_SECOND_TAC]);;

let compile_exp_le_tmp_domain = CONJUNCT1 compile_exp_le_tmp_domain_cases;;

let compile_exps_le_tmp_domain = CONJUNCT2 compile_exp_le_tmp_domain_cases;;

(* ------------------------------------------------------------------------- *)

(* HOL4 lines 772-1318: comp_exp_preserves_eval, comp_exps_preserves_eval.  *)
(* The PC2LAUX_ helpers below factor steps that HOL4's proofs inline:        *)
(* memory loads under mem_rel, inversion of crep_eval on the compound        *)
(* expressions, the compile_exp_le_tmp_domain argument at the state level,   *)
(* locals_rel through fresh temporaries, and the induction over the         *)
(* expression list (HOL4's comp_exps_preserves_eval proof, with the         *)
(* induction hypothesis of comp_exp_preserves_eval in place of that         *)
(* theorem), which the cases Op and Crepop and comp_exps_preserves_eval use. *)


let PC2LAUX_mem_load_32_some_rel = prove
 (`!(sm:A word->(A)word_lab) tm dm be w x.
     mem_rel sm tm dm /\ pan_mem_load_32 sm dm be w = SOME x ==>
     mem_load_32 tm dm be w = SOME x`,
  REWRITE_TAC[pan_mem_load_32_def; mem_load_32_def; mem_rel_def] THEN REPEAT GEN_TAC THEN
  QCASES_ON "sm (byte_align w:A word)" THEN CASE_REWRITE_TAC[] THEN
  FS[COND_CASE_EQ] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `byte_align (w:A word)`) THEN
  ASM_REWRITE_TAC[wlab_wloc_def] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[]);;

let PC2LAUX_mem_load_byte_some_rel = prove
 (`!(sm:A word->(A)word_lab) tm dm be w x.
     mem_rel sm tm dm /\ pan_mem_load_byte sm dm be w = SOME x ==>
     mem_load_byte_aux tm dm be w = SOME x`,
  REWRITE_TAC[pan_mem_load_byte_def; mem_load_byte_aux_def; mem_rel_def] THEN REPEAT GEN_TAC THEN
  QCASES_ON "sm (byte_align w:A word)" THEN CASE_REWRITE_TAC[] THEN
  FS[COND_CASE_EQ] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `byte_align (w:A word)`) THEN
  ASM_REWRITE_TAC[wlab_wloc_def] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[]);;
let PC2LAUX_state_mem_load_32 = prove
 (`!(s:(A,FFI)crep_state) (t:(A,FFI)loop_state) w x.
   crep_to_loopProof_state_rel s t /\
   mem_rel (crep_state_memory s) (loop_state_memory t) (crep_state_memaddrs s) /\
   pan_mem_load_32 (crep_state_memory s) (crep_state_memaddrs s) (crep_state_be s) w = SOME x
   ==> mem_load_32 (loop_state_memory t) (loop_state_mdomain t) (loop_state_be t) w = SOME x`,
  REWRITE_TAC[crep_to_loopProof_state_rel_def] THEN REPEAT STRIP_TAC THEN
  QPAT_X_ASSUM "crep_state_memaddrs s = _" (SUBST_ALL_TAC o SYM) THEN
  QPAT_X_ASSUM "crep_state_be s = _" (SUBST_ALL_TAC o SYM) THEN
  MATCH_MP_TAC PC2LAUX_mem_load_32_some_rel THEN
  EXISTS_TAC `crep_state_memory (s:(A,FFI)crep_state)` THEN ASM_REWRITE_TAC[]);;

let PC2LAUX_state_mem_load_byte = prove
 (`!(s:(A,FFI)crep_state) (t:(A,FFI)loop_state) w x.
   crep_to_loopProof_state_rel s t /\
   mem_rel (crep_state_memory s) (loop_state_memory t) (crep_state_memaddrs s) /\
   pan_mem_load_byte (crep_state_memory s) (crep_state_memaddrs s) (crep_state_be s) w = SOME x
   ==> mem_load_byte_aux (loop_state_memory t) (loop_state_mdomain t) (loop_state_be t) w =
       SOME x`,
  REWRITE_TAC[crep_to_loopProof_state_rel_def] THEN REPEAT STRIP_TAC THEN
  QPAT_X_ASSUM "crep_state_memaddrs s = _" (SUBST_ALL_TAC o SYM) THEN
  QPAT_X_ASSUM "crep_state_be s = _" (SUBST_ALL_TAC o SYM) THEN
  MATCH_MP_TAC PC2LAUX_mem_load_byte_some_rel THEN
  EXISTS_TAC `crep_state_memory (s:(A,FFI)crep_state)` THEN ASM_REWRITE_TAC[]);;


let PC2LAUX_crep_eval_Shift = prove
 (`!(s:(A,FFI)crep_state) sh e1 e2 v.
     crep_eval s (crep_Shift sh e1 e2) = SOME v <=>
     ?w1 w2 z. crep_eval s e1 = SOME (Word w1) /\ crep_eval s e2 = SOME (Word w2) /\
               word_sh sh w1 (val w2) = SOME z /\ v = Word z`,
  REPEAT GEN_TAC THEN REWRITE_TAC[crep_eval_def] THEN
  QCASES_ON "crep_eval (s:(A,FFI)crep_state) e1" THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  QCASES_ON "crep_eval (s:(A,FFI)crep_state) e2" THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[option_DISTINCT; option_INJ] THENL
   [QCASES_ON "a" THEN CASE_REWRITE_TAC[option_DISTINCT];
    QCASES_ON "a" THEN QCASES_ON "a'" THEN CASE_REWRITE_TAC[injectivity "word_lab"] THEN
    QCASES_ON "word_sh sh a'' (val a''')" THEN
    REWRITE_TAC[OPTION_MAP_DEF; option_DISTINCT; option_INJ] THEN
    ASM_MESON_TAC[option_DISTINCT; option_INJ]]);;

let PC2LAUX_crep_eval_Cmp = prove
 (`!(s:(A,FFI)crep_state) cmp e1 e2 v.
     crep_eval s (crep_Cmp cmp e1 e2) = SOME v <=>
     ?w1 w2. crep_eval s e1 = SOME (Word w1) /\ crep_eval s e2 = SOME (Word w2) /\
             v = Word (v2w [asm_word_cmp cmp w1 w2])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[crep_eval_def] THEN
  QCASES_ON "crep_eval (s:(A,FFI)crep_state) e1" THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  QCASES_ON "crep_eval (s:(A,FFI)crep_state) e2" THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[option_DISTINCT; option_INJ] THENL
   [QCASES_ON "a" THEN CASE_REWRITE_TAC[option_DISTINCT];
    QCASES_ON "a" THEN QCASES_ON "a'" THEN CASE_REWRITE_TAC[injectivity "word_lab"] THEN
    REWRITE_TAC[option_DISTINCT; option_INJ] THEN MESON_TAC[]]);;


let PC2LAUX_le_tmp_domain_eval = prove
 (`!(s:(A,FFI)crep_state) ctxt l tl tmp e p le tmp' l' n v.
     crep_eval s e = SOME v /\
     crep_to_loopProof_locals_rel ctxt l (crep_state_locals s) tl /\
     crep_to_loop_compile_exp ctxt tmp l e = (p,le,tmp',l') /\
     crep_to_loop_context_vmax ctxt < tmp /\
     MEM n (locals_touched le) ==>
     n < tmp' /\ n IN domain l'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC compile_exp_le_tmp_domain THEN
  MAP_EVERY QEXISTS_TAC ["ctxt"; "tmp"; "l"; "e"; "p"; "le"] THEN
  IMP_RES_TAC crep_to_loopProof_locals_rel_intro THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN IMP_RES_TAC eval_some_var_cexp_local_lookup THEN
  RES_TAC THEN ASM_MESON_TAC[]);;

let PC2LAUX_les_tmp_domain_eval = prove
 (`!(s:(A,FFI)crep_state) ctxt l tl tmp es p les tmp' l' n vs.
     OPT_MMAP (crep_eval s) es = SOME vs /\
     crep_to_loopProof_locals_rel ctxt l (crep_state_locals s) tl /\
     crep_to_loop_compile_exps ctxt tmp l es = (p,les,tmp',l') /\
     crep_to_loop_context_vmax ctxt < tmp /\
     MEM n (FLAT (MAP locals_touched les)) ==>
     n < tmp' /\ n IN domain l'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC compile_exps_le_tmp_domain THEN
  MAP_EVERY QEXISTS_TAC ["ctxt"; "tmp"; "l"; "es"; "p"; "les"] THEN
  IMP_RES_TAC crep_to_loopProof_locals_rel_intro THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN IMP_RES_TAC opt_mmap_eval_some_var_cexp_local_lookup THEN
  RES_TAC THEN ASM_MESON_TAC[]);;


let PC2LAUX_locals_rel_cmp = prove
 (`!ctxt L (sl:(num,(A)word_lab)fmap) tl n m a b c.
     crep_to_loopProof_locals_rel ctxt L sl tl /\
     crep_to_loop_context_vmax ctxt < n /\ crep_to_loop_context_vmax ctxt < m ==>
     crep_to_loopProof_locals_rel ctxt (list_insert [n; m] L) sl
       (inter (insert n a (insert m b (insert n c tl))) (list_insert [n; m] L))`,
  REWRITE_TAC[crep_to_loopProof_locals_rel_def; crep_to_loopProof_ctxt_max_def] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; domain_inter; IN_INTER; domain_insert; IN_INSERT;
                domain_list_insert; MEM] THEN
    ASM SET_TAC[];
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`vname:num`; `v:(A)word_lab`]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN EXISTS_TAC `n':num` THEN
    ASM_REWRITE_TAC[domain_list_insert; lookup_inter_alt; lookup_insert; MEM] THEN
    RES_TAC THEN SUBGOAL_THEN `~(n':num = n) /\ ~(n' = m)` STRIP_ASSUME_TAC THENL
     [ASM_ARITH_TAC; ASM_REWRITE_TAC[]]]);;


let PC2LAUX_OPT_MMAP_CONS_SOME = prove
 (`!(f:A->B option) h t vs.
     OPT_MMAP f (CONS h t) = SOME vs <=>
     ?v1 vs1. f h = SOME v1 /\ OPT_MMAP f t = SOME vs1 /\ vs = CONS v1 vs1`,
  REWRITE_TAC[OPT_MMAP_def; OPTION_BIND_EQUALS_OPTION; option_INJ] THEN MESON_TAC[]);;


let PC2LAUX_comp_exps_preserves_eval_gen = prove
 (`!es s vs (t:(A,FFI)loop_state) ctxt tmp l p les ntmp nl.
     (!e. MEM e es ==>
          !v (t:(A,FFI)loop_state) ctxt tmp l p le ntmp nl.
            crep_eval s e = SOME v /\
            crep_to_loopProof_state_rel s t /\
            mem_rel (crep_state_memory s) (loop_state_memory t) (crep_state_memaddrs s) /\
            crep_to_loopProof_globals_rel (crep_state_globals s) (loop_state_globals t) /\
            crep_to_loopProof_code_rel ctxt (crep_state_code s) (loop_state_code t) /\
            crep_to_loopProof_locals_rel ctxt l (crep_state_locals s) (loop_state_locals t) /\
            crep_to_loop_compile_exp ctxt tmp l e = (p,le,ntmp,nl) /\
            crep_to_loop_context_vmax ctxt < tmp ==>
            ?ck st.
              loop_evaluate (loop_nested_seq p,
                loop_state_clock_fupd (K (loop_state_clock t + ck)) t) = (NONE,st) /\
              loop_eval st le = SOME (wlab_wloc v) /\
              crep_to_loopProof_state_rel s st /\
              mem_rel (crep_state_memory s) (loop_state_memory st) (crep_state_memaddrs s) /\
              crep_to_loopProof_globals_rel (crep_state_globals s) (loop_state_globals st) /\
              crep_to_loopProof_code_rel ctxt (crep_state_code s) (loop_state_code st) /\
              crep_to_loopProof_locals_rel ctxt nl (crep_state_locals s)
                (loop_state_locals st)) /\
     OPT_MMAP (crep_eval s) es = SOME vs /\
     crep_to_loopProof_state_rel s t /\
     mem_rel (crep_state_memory s) (loop_state_memory t) (crep_state_memaddrs s) /\
     crep_to_loopProof_globals_rel (crep_state_globals s) (loop_state_globals t) /\
     crep_to_loopProof_code_rel ctxt (crep_state_code s) (loop_state_code t) /\
     crep_to_loopProof_locals_rel ctxt l (crep_state_locals s) (loop_state_locals t) /\
     crep_to_loop_compile_exps ctxt tmp l es = (p,les,ntmp,nl) /\
     crep_to_loop_context_vmax ctxt < tmp ==>
     ?ck st.
       loop_evaluate (loop_nested_seq p,
                      loop_state_clock_fupd (K (loop_state_clock t + ck)) t) = (NONE,st) /\
       OPT_MMAP (loop_eval st) les = SOME (MAP wlab_wloc vs) /\
       crep_to_loopProof_state_rel s st /\
       mem_rel (crep_state_memory s) (loop_state_memory st) (crep_state_memaddrs s) /\
       crep_to_loopProof_globals_rel (crep_state_globals s) (loop_state_globals st) /\
       crep_to_loopProof_code_rel ctxt (crep_state_code s) (loop_state_code st) /\
       crep_to_loopProof_locals_rel ctxt nl (crep_state_locals s) (loop_state_locals st)`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THENL
   [FS[OPT_MMAP_def; compile_exps_alt] THEN RVEQ_TAC THEN QEXISTS_TAC "0" THEN
    FS[loop_nested_seq_def; loop_evaluate_def; OPT_MMAP_def; MAP; ADD_0; RECORD_SELFID_ss];
    ALL_TAC] THEN
  QPAT_X_ASSUM "OPT_MMAP _ (CONS _ _) = _"
    (STRIP_ASSUME_TAC o REWRITE_RULE[PC2LAUX_OPT_MMAP_CONS_SOME]) THEN
  RVEQ_TAC THEN FS[compile_exps_alt] THEN
  REPEAT(PAIRARG_TAC THEN FS[]) THEN RVEQ_TAC THEN
  QPAT_ASSUM "!e. e = h \/ MEM e t ==> _" (MP_TAC o SPEC `h:(A)crep_exp`) THEN
  REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`v1:(A)word_lab`; `t':(A,FFI)loop_state`;
    `ctxt:crep_to_loop_context`; `tmp:num`; `l:num_set`; `p':((A)loop_prog)list`;
    `le:(A)loop_exp`; `tmp':num`; `l':num_set`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  IMP_RES_TAC compile_exp_out_rel THEN
  QBY "crep_to_loop_context_vmax ctxt < tmp'" DECIDE_TAC THEN
  LAST_X_ASSUM(MP_TAC o SPECL [`s:(A,FFI)crep_state`; `vs1:((A)word_lab)list`;
    `st:(A,FFI)loop_state`; `ctxt:crep_to_loop_context`; `tmp':num`; `l':num_set`;
    `p1:((A)loop_prog)list`; `les':((A)loop_exp)list`; `ntmp:num`; `nl:num_set`]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [X_GEN_TAC `e:(A)crep_exp` THEN DISCH_TAC THEN
    QPAT_ASSUM "!e. e = h \/ MEM e t ==> _" (MATCH_MP_TAC o SPEC `e:(A)crep_exp`) THEN
    ASM_REWRITE_TAC[];
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`loop_nested_seq p':(A)loop_prog`;
                 `loop_state_clock_fupd (K (loop_state_clock t' + ck)) (t':(A,FFI)loop_state)`;
                 `NONE:((A)loop_result)option`; `st:(A,FFI)loop_state`; `ck':num`]
                loop_evaluate_add_clock_eq) THEN
  ASM_REWRITE_TAC[option_DISTINCT] THEN SIMP[GSYM ADD_ASSOC] THEN DISCH_TAC THEN
  EXISTS_TAC `ck + ck':num` THEN EXISTS_TAC `st':(A,FFI)loop_state` THEN
  ASM_SIMP_TAC[evaluate_none_nested_seq_append] THEN
  REWRITE_TAC[OPT_MMAP_def] THEN
  MATCH_MP_TAC nested_seq_pure_evaluation THEN
  MAP_EVERY EXISTS_TAC [`p':((A)loop_prog)list`; `p1:((A)loop_prog)list`;
    `t':(A,FFI)loop_state`; `st:(A,FFI)loop_state`; `l:num_set`; `tmp':num`;
    `ck:num`; `ck':num`] THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN ASM_REWRITE_TAC[] THEN
  TRY(QPAT_X_ASSUM "l' = cut_sets l _" (SUBST_ALL_TAC)) THEN
  IMP_RES_TAC compile_exps_out_rel THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
  IMP_RES_TAC comp_exp_assigned_vars_tmp_bound THEN
  IMP_RES_TAC comp_exps_assigned_vars_tmp_bound THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`s:(A,FFI)crep_state`; `ctxt:crep_to_loop_context`; `l:num_set`;
    `loop_state_locals (t':(A,FFI)loop_state)`; `tmp:num`; `h:(A)crep_exp`;
    `p':((A)loop_prog)list`; `le:(A)loop_exp`; `tmp':num`;
    `cut_sets l (loop_nested_seq (p':((A)loop_prog)list))`; `n:num`; `v1:(A)word_lab`]
    PC2LAUX_le_tmp_domain_eval) THEN ASM_SIMP_TAC[]);;


let PC2LAUX_crep_eval_Op = prove
 (CASE_TERM
  `!(s:(A,FFI)crep_state) op es v.
     crep_eval s (crep_Op op es) = SOME v <=>
     ?ws z. OPT_MMAP (crep_eval s) es = SOME ws /\
            word_op op (MAP (\w. match w with Word n -> n) ws) = SOME z /\ v = Word z`,
  REPEAT GEN_TAC THEN REWRITE_TAC[crep_eval_def] THEN
  QCASES_ON "OPT_MMAP (crep_eval (s:(A,FFI)crep_state)) es" THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  SUBGOAL_THEN (CASE_TERM `ALL (\w:(A)word_lab. match w with Word _ -> T) a`)
    (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[GSYM ALL_MEM] THEN GEN_TAC THEN QCASES_ON "x:(A)word_lab" THEN
    CASE_REWRITE_TAC[];
    REWRITE_TAC[OPTION_MAP_EQ_SOME] THEN MESON_TAC[]]);;

let PC2LAUX_crep_eval_Crepop = prove
 (CASE_TERM
  `!(s:(A,FFI)crep_state) op es v.
     crep_eval s (Crepop op es) = SOME v <=>
     ?ws z. OPT_MMAP (crep_eval s) es = SOME ws /\
            crep_op op (MAP (\w. match w with Word n -> n) ws) = SOME z /\ v = Word z`,
  REPEAT GEN_TAC THEN REWRITE_TAC[crep_eval_def] THEN
  QCASES_ON "OPT_MMAP (crep_eval (s:(A,FFI)crep_state)) es" THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  SUBGOAL_THEN (CASE_TERM `ALL (\w:(A)word_lab. match w with Word _ -> T) a`)
    (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[GSYM ALL_MEM] THEN GEN_TAC THEN QCASES_ON "x:(A)word_lab" THEN
    CASE_REWRITE_TAC[];
    REWRITE_TAC[OPTION_MAP_EQ_SOME] THEN MESON_TAC[]]);;

let PC2LAUX_the_words_MAP = prove
 (CASE_TERM
  `!les (f:B->((A)word_loc)option) ws.
     OPT_MMAP f les = SOME (MAP wlab_wloc ws) ==>
     the_words (MAP f les) = SOME (MAP (\w. match w with Word n -> n) ws)`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[OPT_MMAP_def; MAP; the_words_def] THENL
   [QCASES_ON "ws:((A)word_lab)list" THEN REWRITE_TAC[MAP; option_INJ; NOT_CONS_NIL];
    REWRITE_TAC[OPTION_BIND_EQUALS_OPTION; option_INJ] THEN STRIP_TAC THEN
    QCASES_ON "ws:((A)word_lab)list" THEN
    FS[MAP; NOT_CONS_NIL; injectivity "list"] THEN RVEQ_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`f:B->((A)word_loc)option`; `a1:((A)word_lab)list`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    QCASES_ON "a0:(A)word_lab" THEN FS[wlab_wloc_def] THEN CASE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[]]);;


let PC2LAUX_locals_rel_extend = prove
 (`!ctxt L L' (sl:(num,(A)word_lab)fmap) tl tl'.
     crep_to_loopProof_locals_rel ctxt L sl tl /\
     domain L SUBSET domain L' /\ domain L' SUBSET domain tl' /\
     (!n. n <= crep_to_loop_context_vmax ctxt ==> lookup n tl' = lookup n tl) ==>
     crep_to_loopProof_locals_rel ctxt L' sl tl'`,
  REWRITE_TAC[crep_to_loopProof_locals_rel_def; crep_to_loopProof_ctxt_max_def] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`vname:num`; `v:(A)word_lab`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN EXISTS_TAC `n:num` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> REWRITE_TAC[GSYM th]) THEN
  FIRST_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]);;


let PC2LAUX_crep_op_Mul = prove
 (CASE_TERM
  `!op (ws:((A)word_lab)list) z.
     crep_op op (MAP (\w. match w with Word n -> n) ws) = SOME z <=>
     ?a b. ws = [Word a; Word b] /\ z = word_mul a b`,
  GEN_TAC THEN QCASES_ON "op" THEN GEN_TAC THEN
  QCASES_ON "ws:((A)word_lab)list" THEN
  REWRITE_TAC[MAP; crep_op_def; option_DISTINCT; NOT_NIL_CONS] THEN
  QCASES_ON "a0:(A)word_lab" THEN QCASES_ON "a1:((A)word_lab)list" THEN
  REWRITE_TAC[MAP; crep_op_def; option_DISTINCT; NOT_NIL_CONS; injectivity "list"] THEN
  CASE_REWRITE_TAC[] THEN
  QCASES_ON "a0:(A)word_lab" THEN QCASES_ON "a1':((A)word_lab)list" THEN
  REWRITE_TAC[MAP; crep_op_def; option_DISTINCT; option_INJ; NOT_NIL_CONS; NOT_CONS_NIL;
              injectivity "list"; injectivity "word_lab"] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[crep_op_def; option_DISTINCT; option_INJ] THEN
  MESON_TAC[]);;


let PC2LAUX_OPT_MMAP_EQ_PAIR = prove
 (`!(f:A->B option) l x y.
     OPT_MMAP f l = SOME [x; y] <=> ?l1 l2. l = [l1; l2] /\ f l1 = SOME x /\ f l2 = SOME y`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `l:A list` list_CASES) THEN
  REWRITE_TAC[OPT_MMAP_def; OPTION_BIND_EQUALS_OPTION; option_INJ; NOT_CONS_NIL;
              NOT_NIL_CONS; injectivity "list"] THEN
  STRUCT_CASES_TAC (ISPEC `t:A list` list_CASES) THEN
  REWRITE_TAC[OPT_MMAP_def; OPTION_BIND_EQUALS_OPTION; option_INJ; NOT_CONS_NIL;
              NOT_NIL_CONS; injectivity "list"] THENL
   [MESON_TAC[NOT_CONS_NIL]; ALL_TAC] THEN
  STRUCT_CASES_TAC (ISPEC `t':A list` list_CASES) THEN
  REWRITE_TAC[OPT_MMAP_def; OPTION_BIND_EQUALS_OPTION; option_INJ; NOT_CONS_NIL;
              NOT_NIL_CONS; injectivity "list"] THEN
  MESON_TAC[NOT_CONS_NIL; injectivity "list"]);;


let PC2LAUX_list_of_seq_23 = prove
 (`list_of_seq ((+) n) 2 = [n; n + 1] /\ list_of_seq ((+) n) 3 = [n; n + 1; n + 2]`,
  REWRITE_TAC[num_CONV `3`; num_CONV `2`; num_CONV `1`; list_of_seq; APPEND] THEN
  REWRITE_TAC[injectivity "list"] THEN ARITH_TAC);;

let PC2LAUX_CPE_TRIV_TAC =
  REPEAT STRIP_TAC THEN FS[crep_eval_def; crep_to_loop_compile_exp_def] THEN RVEQ_TAC THEN
  QEXISTS_TAC "0" THEN
  FS[loop_nested_seq_def; loop_evaluate_def; loop_eval_def; wlab_wloc_def; ADD_0;
     RECORD_SELFID_ss];;

let PC2LAUX_CPE_LOAD_TAC =
  FS[crep_eval_def] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  TOP_CASE_TAC THEN FS[] THEN TOP_CASE_TAC THEN FS[] THEN RW[] THEN
  FS[crep_to_loop_compile_exp_def] THEN REPEAT(PAIRARG_TAC THEN FS[]) THEN RVEQ_TAC THEN
  LAST_X_ASSUM DRULE_ALL THEN STRIP_TAC THEN QEXISTS_TAC "ck" THEN FS[] THEN
  FS[loop_eval_def; wlab_wloc_def] THEN FS[crep_mem_load_def; loop_mem_load_def] THEN
  RVEQ_TAC THEN IMP_RES_TAC crep_to_loopProof_state_rel_intro THEN GVS[mem_rel_def] THEN
  RFS[crep_to_loopProof_state_rel_def];;

let PC2LAUX_CPE_LOADN_TAC (th,fact) =
  FS[crep_eval_def] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  TOP_CASE_TAC THEN FS[] THEN TOP_CASE_TAC THEN FS[] THEN TOP_CASE_TAC THEN FS[] THEN RW[] THEN
  FS[crep_to_loop_compile_exp_def] THEN REPEAT(PAIRARG_TAC THEN FS[]) THEN RVEQ_TAC THEN
  LAST_X_ASSUM DRULE_ALL THEN STRIP_TAC THEN QEXISTS_TAC "ck" THEN
  ASM_SIMP_TAC[evaluate_none_nested_seq_append] THEN
  QBY fact (MATCH_MP_TAC th THEN QEXISTS_TAC "s" THEN ASM_REWRITE_TAC[]) THEN
  ASM_REWRITE_TAC[loop_nested_seq_def; loop_evaluate_def] THEN
  FS[wlab_wloc_def; loop_set_var_def; lookup_insert] THEN
  SIMP[insert_shadow; loop_eval_def; lookup_insert] THEN
  CONJ_TAC THENL [FS[crep_to_loopProof_state_rel_def]; ALL_TAC] THEN
  IMP_RES_TAC compile_exp_out_rel THEN
  FS[crep_to_loopProof_locals_rel_def; SUBSET_INSERT_RIGHT; domain_insert] THEN
  RW[] THENL
   [ASM SET_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPECL [`vname:num`; `v:(A)word_lab`]) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN QEXISTS_TAC "n" THEN ASM_REWRITE_TAC[lookup_insert] THEN
    QBY "~(n = tmp')"
     (QPAT_X_ASSUM "crep_to_loopProof_ctxt_max _ _"
        (MP_TAC o SPECL [`vname:num`; `n:num`] o REWRITE_RULE[crep_to_loopProof_ctxt_max_def]) THEN
      ASM_REWRITE_TAC[] THEN DECIDE_TAC) THEN
    ASM_REWRITE_TAC[]];;

let PC2LAUX_CPE_OP_TAC =
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[PC2LAUX_crep_eval_Op] THEN STRIP_TAC THEN
  QPAT_X_ASSUM "crep_to_loop_compile_exp _ _ _ (crep_Op _ _) = _"
    (MP_TAC o ONCE_REWRITE_RULE[crep_to_loop_compile_exp_def]) THEN
  REPEAT(PAIRARG_TAC THEN FS[]) THEN STRIP_TAC THEN RVEQ_TAC THEN
  MP_TAC(ISPECL [`es:((A)crep_exp)list`; `s:(A,FFI)crep_state`; `ws:((A)word_lab)list`;
    `t:(A,FFI)loop_state`; `ctxt:crep_to_loop_context`; `tmp:num`; `l:num_set`;
    `p:((A)loop_prog)list`; `les:((A)loop_exp)list`; `ntmp:num`; `nl:num_set`]
    PC2LAUX_comp_exps_preserves_eval_gen) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`ck:num`; `st:(A,FFI)loop_state`] THEN
  ASM_REWRITE_TAC[loop_eval_def] THEN
  IMP_RES_TAC PC2LAUX_the_words_MAP THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[OPTION_MAP_DEF; wlab_wloc_def];;

let PC2LAUX_CPE_CREPOP_END_TAC =
  SIMP[loop_eval_def; lookup_insert; wlab_wloc_def; WORD_MUL; WORD_VAL] THEN
  (CONJ_TAC THENL [FS[crep_to_loopProof_state_rel_def]; ALL_TAC]) THEN
  MATCH_MP_TAC PC2LAUX_locals_rel_extend THEN
  EXISTS_TAC `l':num_set` THEN EXISTS_TAC `loop_state_locals (st:(A,FFI)loop_state)` THEN
  ASM_REWRITE_TAC[] THEN
  QPAT_ASSUM "crep_to_loopProof_locals_rel ctxt l' _ (loop_state_locals st)"
    (STRIP_ASSUME_TAC o MATCH_MP crep_to_loopProof_locals_rel_intro) THEN
  IMP_RES_TAC compile_exps_out_rel THEN
  REWRITE_TAC[ARITH_RULE `(n + 2) + 1 = n + 3`] THEN
  REWRITE_TAC[SUBSET; domain_insert; IN_INSERT; domain_list_insert; MEM; lookup_insert;
              ARITH_RULE `(n + 3) - n = 3 /\ (n + 2) - n = 2`; PC2LAUX_list_of_seq_23] THEN
  REPEAT CONJ_TAC THENL
   [MESON_TAC[];
    QPAT_X_ASSUM "domain l' SUBSET _" (MP_TAC o REWRITE_RULE[SUBSET]) THEN MESON_TAC[];
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `n < tmp':num` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REPEAT(COND_CASES_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN REWRITE_TAC[]];;

let PC2LAUX_CPE_CREPOP_TAC =
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[PC2LAUX_crep_eval_Crepop; PC2LAUX_crep_op_Mul] THEN STRIP_TAC THEN RVEQ_TAC THEN
  QPAT_X_ASSUM "crep_to_loop_compile_exp _ _ _ (Crepop _ _) = _"
    (MP_TAC o ONCE_REWRITE_RULE[crep_to_loop_compile_exp_def]) THEN
  REPEAT(PAIRARG_TAC THEN FS[]) THEN STRIP_TAC THEN RVEQ_TAC THEN
  MP_TAC(ISPECL [`es:((A)crep_exp)list`; `s:(A,FFI)crep_state`;
    `[Word a; Word b]:((A)word_lab)list`;
    `t:(A,FFI)loop_state`; `ctxt:crep_to_loop_context`; `tmp:num`; `l:num_set`;
    `p':((A)loop_prog)list`; `les:((A)loop_exp)list`; `tmp':num`; `l':num_set`]
    PC2LAUX_comp_exps_preserves_eval_gen) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  QPAT_X_ASSUM "OPT_MMAP (loop_eval st) les = _"
    (STRIP_ASSUME_TAC o REWRITE_RULE[MAP; wlab_wloc_def; PC2LAUX_OPT_MMAP_EQ_PAIR]) THEN
  RVEQ_TAC THEN QCASES_ON "op" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[compile_crepop_def; LENGTH; ARITH_RULE `SUC(SUC 0) = 2`]) THEN
  EXISTS_TAC `ck:num` THEN
  REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  QPAT_ASSUM "loop_evaluate (loop_nested_seq p',_) = _"
    (fun th -> REWRITE_TAC[GEN_ALL(MATCH_MP evaluate_none_nested_seq_append th)]) THEN
  REWRITE_TAC[MAPi_DEF; o_DEF; APPEND; ADD_0] THEN
  SUBGOAL_THEN `!n. MEM n (locals_touched (l2:(A)loop_exp)) ==> n < tmp'` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`s:(A,FFI)crep_state`; `ctxt:crep_to_loop_context`; `l:num_set`;
      `loop_state_locals (t:(A,FFI)loop_state)`; `tmp:num`; `es:((A)crep_exp)list`;
      `p':((A)loop_prog)list`; `[l1; l2]:((A)loop_exp)list`; `tmp':num`; `l':num_set`; `n:num`;
      `[Word a; Word b]:((A)word_lab)list`] PC2LAUX_les_tmp_domain_eval) THEN
    ASM_SIMP_TAC[MAP; FLAT; APPEND; MEM_APPEND];
    ALL_TAC] THEN
  SUBGOAL_THEN `loop_eval (loop_set_var tmp' (wl_Word a) (st:(A,FFI)loop_state)) l2 =
                SOME (wl_Word b)`
    ASSUME_TAC THENL
   [QPAT_ASSUM "loop_eval st l2 = _" (fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
    REWRITE_TAC[loop_set_var_def] THEN MATCH_MP_TAC locals_touched_eq_eval_eq THEN
    SIMP[lookup_insert] THEN REPEAT STRIP_TAC THEN RES_TAC THEN
    SUBGOAL_THEN `~(n:num = tmp')` (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[loop_set_var_def]) THEN
  REWRITE_TAC[GSYM ONE] THEN
  QPAT_X_ASSUM "(if crep_to_loop_context_target ctxt = ARMv7 then _ else _) = _" MP_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  ASM_SIMP_TAC[loop_nested_seq_def] THEN
  SIMP[loop_evaluate_def; loop_arith_def; loop_set_var_def; lookup_insert;
       ARITH_RULE `~(n + 1 = n) /\ ~(n = n + 1)`] THEN
  CASE_REWRITE_TAC[] THEN
  PC2LAUX_CPE_CREPOP_END_TAC;;

let PC2LAUX_CPE_CMP_TAC1 =
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[PC2LAUX_crep_eval_Cmp] THEN STRIP_TAC THEN
  FS[crep_to_loop_compile_exp_def] THEN REPEAT(PAIRARG_TAC THEN FS[]) THEN RVEQ_TAC THEN
  LAST_X_ASSUM DRULE_ALL THEN STRIP_TAC THEN
  IMP_RES_TAC compile_exp_out_rel THEN
  QBY "crep_to_loop_context_vmax ctxt < tmp'" DECIDE_TAC THEN
  LAST_X_ASSUM(QSPECL_THEN ["Word w2"; "st"; "ctxt"; "tmp'"; "l'"; "p''"; "le''"; "tmp''"; "l''"]
    MP_TAC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  QSPECL_THEN ["loop_nested_seq p'"; "loop_state_clock_fupd (K (loop_state_clock t + ck)) t";
               "NONE"; "st"; "ck' + 1"] MP_TAC loop_evaluate_add_clock_eq THEN
  QSPECL_THEN ["loop_nested_seq p''"; "loop_state_clock_fupd (K (loop_state_clock st + ck')) st";
               "NONE"; "st'"; "1"] MP_TAC loop_evaluate_add_clock_eq THEN
  ASM_REWRITE_TAC[option_DISTINCT] THEN SIMP[GSYM ADD_ASSOC] THEN
  REPEAT DISCH_TAC THEN
  QEXISTS_TAC "ck + ck' + 1" THEN
  REWRITE_TAC[prog_if_def; GSYM APPEND_ASSOC] THEN
  ASM_SIMP_TAC[evaluate_none_nested_seq_append] THEN
  QPAT_ASSUM "loop_evaluate (loop_nested_seq p'',_) = _"
    (fun th -> REWRITE_TAC[GEN_ALL(MATCH_MP evaluate_none_nested_seq_append th)]) THEN
  REWRITE_TAC[loop_nested_seq_def] THEN ONCE_REWRITE_TAC[loop_evaluate_def] THEN
  SIMP[] THEN
  QSUBGOAL "loop_eval st' le' = SOME (wl_Word w1)" THENL
   [MATCH_MP_TAC nested_seq_pure_evaluation THEN
    MAP_EVERY QEXISTS_TAC ["p'"; "p''"; "t"; "st"; "l"; "tmp'"; "ck"; "ck'"] THEN
    ONCE_REWRITE_TAC[ADD_SYM] THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[wlab_wloc_def]) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[wlab_wloc_def] THEN
    TRY(QPAT_X_ASSUM "l' = cut_sets l _" (SUBST_ALL_TAC)) THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
    IMP_RES_TAC comp_exp_assigned_vars_tmp_bound THEN ASM_REWRITE_TAC[] THEN
    QSPECL_THEN ["s"; "ctxt"; "l"; "loop_state_locals t"; "tmp"; "e1"; "p'"; "le'"; "tmp'";
                 "cut_sets l (loop_nested_seq p')"; "n"; "Word w1"]
      MP_TAC PC2LAUX_le_tmp_domain_eval THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  QSUBGOAL "loop_eval (loop_set_var (tmp'' + 1) (wl_Word w1) st') le'' = SOME (wl_Word w2)" THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[wlab_wloc_def]) THEN
    QPAT_ASSUM "loop_eval st' le'' = _" (fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
    REWRITE_TAC[loop_set_var_def] THEN MATCH_MP_TAC locals_touched_eq_eval_eq THEN
    SIMP[lookup_insert] THEN REPEAT STRIP_TAC THEN
    QSPECL_THEN ["s"; "ctxt"; "l'"; "loop_state_locals st"; "tmp'"; "e2"; "p''"; "le''"; "tmp''";
                 "l''"; "n"; "Word w2"]
      MP_TAC PC2LAUX_le_tmp_domain_eval THEN ASM_SIMP_TAC[] THEN STRIP_TAC THEN
    QBY "~(n = tmp'' + 1)" DECIDE_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[loop_set_var_def]) THEN
  SIMP[loop_evaluate_def; loop_set_var_def; loop_eval_upd_clock_eq;
       eval_upd_locals_clock_eq; lookup_insert; get_var_imm_def;
       ARITH_RULE `~(n + 1 = n + 2) /\ ~(n + 2 = n + 1)`] THEN
  QPAT_ASSUM ("crep_to_loopProof_locals_rel ctxt (cut_sets (cut_sets l _) _) _ " ^
              "(loop_state_locals st')")
    (STRIP_ASSUME_TAC o MATCH_MP crep_to_loopProof_locals_rel_intro) THEN
  QBY ("domain (list_insert [tmp'' + 1; tmp'' + 2] (cut_sets (cut_sets l " ^
       "(loop_nested_seq p')) (loop_nested_seq p''))) SUBSET (tmp'' + 1) INSERT " ^
       "(tmp'' + 2) INSERT (tmp'' + 1) INSERT domain (loop_state_locals st')")
   (REWRITE_TAC[SUBSET; domain_list_insert; MEM; IN_INSERT] THEN
    QPAT_X_ASSUM "domain _ SUBSET domain (loop_state_locals st')"
      (MP_TAC o REWRITE_RULE[SUBSET]) THEN
    MESON_TAC[]);;

let PC2LAUX_CPE_CMP_TAC =
  PC2LAUX_CPE_CMP_TAC1 THEN
  ASM_CASES_TAC `asm_word_cmp cmp (w1:A word) w2` THEN ASM_REWRITE_TAC[] THEN
  SIMP[loop_evaluate_def; loop_eval_def; loop_set_var_def; cut_res_def; cut_state_def;
       domain_insert; loop_dec_clock_def] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN SIMP[ADD_EQ_0; ARITH_EQ; ADD_SUB] THEN
  SIMP[lookup_inter_alt; domain_list_insert; MEM; lookup_insert; wlab_wloc_def; v2w_sing] THEN
  (CONJ_TAC THENL [FS[crep_to_loopProof_state_rel_def]; ALL_TAC]) THEN
  MATCH_MP_TAC PC2LAUX_locals_rel_cmp THEN ASM_REWRITE_TAC[] THEN DECIDE_TAC;;

let PC2LAUX_CPE_SHIFT_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[PC2LAUX_crep_eval_Shift] THEN STRIP_TAC THEN
  FS[crep_to_loop_compile_exp_def] THEN REPEAT(PAIRARG_TAC THEN FS[]) THEN RVEQ_TAC THEN
  LAST_X_ASSUM DRULE_ALL THEN STRIP_TAC THEN
  IMP_RES_TAC compile_exp_out_rel THEN
  QBY "crep_to_loop_context_vmax ctxt < tmp'" DECIDE_TAC THEN
  LAST_X_ASSUM(QSPECL_THEN ["Word w2"; "st"; "ctxt"; "tmp'"; "l'"; "p''"; "le''"; "ntmp"; "nl"]
    MP_TAC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  QSPECL_THEN ["loop_nested_seq p'"; "loop_state_clock_fupd (K (loop_state_clock t + ck)) t";
               "NONE"; "st"; "ck'"] MP_TAC loop_evaluate_add_clock_eq THEN
  ASM_REWRITE_TAC[option_DISTINCT] THEN SIMP[GSYM ADD_ASSOC] THEN DISCH_TAC THEN
  QEXISTS_TAC "ck + ck'" THEN QEXISTS_TAC "st'" THEN
  ASM_SIMP_TAC[evaluate_none_nested_seq_append] THEN
  QSUBGOAL "loop_eval st' le' = SOME (wl_Word w1)" THENL
   [MATCH_MP_TAC nested_seq_pure_evaluation THEN
    MAP_EVERY QEXISTS_TAC ["p'"; "p''"; "t"; "st"; "l"; "tmp'"; "ck"; "ck'"] THEN
    ONCE_REWRITE_TAC[ADD_SYM] THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[wlab_wloc_def]) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[wlab_wloc_def] THEN
    QPAT_X_ASSUM "l' = cut_sets l _" (SUBST_ALL_TAC) THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
    IMP_RES_TAC comp_exp_assigned_vars_tmp_bound THEN ASM_REWRITE_TAC[] THEN
    QSPECL_THEN ["s"; "ctxt"; "l"; "loop_state_locals t"; "tmp"; "e1"; "p'"; "le'"; "tmp'";
                 "cut_sets l (loop_nested_seq p')"; "n"; "Word w1"]
      MP_TAC PC2LAUX_le_tmp_domain_eval THEN ASM_SIMP_TAC[];
    ASM_REWRITE_TAC[loop_eval_def; wlab_wloc_def] THEN CASE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[OPTION_MAP_DEF]];;

let crep_to_loopProof_comp_exp_preserves_eval = prove
 (`!s e v (t:(A,FFI)loop_state) ctxt tmp l p le ntmp nl.
     crep_eval s e = SOME v /\
     crep_to_loopProof_state_rel s t /\
     mem_rel (crep_state_memory s) (loop_state_memory t) (crep_state_memaddrs s) /\
     crep_to_loopProof_globals_rel (crep_state_globals s) (loop_state_globals t) /\
     crep_to_loopProof_code_rel ctxt (crep_state_code s) (loop_state_code t) /\
     crep_to_loopProof_locals_rel ctxt l (crep_state_locals s) (loop_state_locals t) /\
     crep_to_loop_compile_exp ctxt tmp l e = (p,le,ntmp,nl) /\
     crep_to_loop_context_vmax ctxt < tmp ==>
     ?ck st.
       loop_evaluate (loop_nested_seq p,
                      loop_state_clock_fupd (K (loop_state_clock t + ck)) t) = (NONE,st) /\
       loop_eval st le = SOME (wlab_wloc v) /\
       crep_to_loopProof_state_rel s st /\
       mem_rel (crep_state_memory s) (loop_state_memory st) (crep_state_memaddrs s) /\
       crep_to_loopProof_globals_rel (crep_state_globals s) (loop_state_globals st) /\
       crep_to_loopProof_code_rel ctxt (crep_state_code s) (loop_state_code st) /\
       crep_to_loopProof_locals_rel ctxt nl (crep_state_locals s) (loop_state_locals st)`,
  REC_IND_TAC crep_eval_ind THEN REPEAT CONJ_TAC THENL
   [(* crep_Const *) PC2LAUX_CPE_TRIV_TAC;
    (* crep_Var *)
    PC2LAUX_CPE_TRIV_TAC THEN IMP_RES_TAC crep_to_loopProof_locals_rel_intro THEN
    FS[crep_to_loop_find_var_def] THEN RES_TAC THEN FS[];
    (* crep_Load *) PC2LAUX_CPE_LOAD_TAC;
    (* crep_Load32 *)
    PC2LAUX_CPE_LOADN_TAC (PC2LAUX_state_mem_load_32,
      "mem_load_32 (loop_state_memory st) (loop_state_mdomain st) (loop_state_be st) a' = " ^
      "SOME a''");
    (* crep_LoadByte *)
    PC2LAUX_CPE_LOADN_TAC (PC2LAUX_state_mem_load_byte,
      "mem_load_byte_aux (loop_state_memory st) (loop_state_mdomain st) (loop_state_be st) " ^
      "a' = SOME a''");
    (* LoadGlob *)
    PC2LAUX_CPE_TRIV_TAC THEN IMP_RES_TAC crep_to_loopProof_globals_rel_intro THEN RES_TAC THEN
    ASM_REWRITE_TAC[];
    (* crep_Op *) PC2LAUX_CPE_OP_TAC;
    (* Crepop *) PC2LAUX_CPE_CREPOP_TAC;
    (* crep_Cmp *) PC2LAUX_CPE_CMP_TAC;
    (* crep_Shift *) PC2LAUX_CPE_SHIFT_TAC;
    (* crep_BaseAddr *) PC2LAUX_CPE_TRIV_TAC THEN FS[crep_to_loopProof_state_rel_def];
    (* crep_TopAddr *) PC2LAUX_CPE_TRIV_TAC THEN FS[crep_to_loopProof_state_rel_def]]);;

let comp_exps_preserves_eval = prove
 (`!es s vs (t:(A,FFI)loop_state) ctxt tmp l p les ntmp nl.
     OPT_MMAP (crep_eval s) es = SOME vs /\
     crep_to_loopProof_state_rel s t /\
     mem_rel (crep_state_memory s) (loop_state_memory t) (crep_state_memaddrs s) /\
     crep_to_loopProof_globals_rel (crep_state_globals s) (loop_state_globals t) /\
     crep_to_loopProof_code_rel ctxt (crep_state_code s) (loop_state_code t) /\
     crep_to_loopProof_locals_rel ctxt l (crep_state_locals s) (loop_state_locals t) /\
     crep_to_loop_compile_exps ctxt tmp l es = (p,les,ntmp,nl) /\
     crep_to_loop_context_vmax ctxt < tmp ==>
     ?ck st.
       loop_evaluate (loop_nested_seq p,
                      loop_state_clock_fupd (K (loop_state_clock t + ck)) t) = (NONE,st) /\
       OPT_MMAP (loop_eval st) les = SOME (MAP wlab_wloc vs) /\
       crep_to_loopProof_state_rel s st /\
       mem_rel (crep_state_memory s) (loop_state_memory st) (crep_state_memaddrs s) /\
       crep_to_loopProof_globals_rel (crep_state_globals s) (loop_state_globals st) /\
       crep_to_loopProof_code_rel ctxt (crep_state_code s) (loop_state_code st) /\
       crep_to_loopProof_locals_rel ctxt nl (crep_state_locals s) (loop_state_locals st)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`es:((A)crep_exp)list`; `s:(A,FFI)crep_state`; `vs:((A)word_lab)list`;
    `t:(A,FFI)loop_state`; `ctxt:crep_to_loop_context`; `tmp:num`; `l:num_set`;
    `p:((A)loop_prog)list`; `les:((A)loop_exp)list`; `ntmp:num`; `nl:num_set`]
    PC2LAUX_comp_exps_preserves_eval_gen) THEN
  ASM_REWRITE_TAC[crep_to_loopProof_comp_exp_preserves_eval]);;

(* ------------------------------------------------------------------------- *)

(* HOL4 lines 1321-1568: member_cutset_survives_comp_exp_cases ..          *)
(* assigned_vars_nested_seq_assign                                          *)

let member_cutset_survives_comp_exp_cases = prove
 (`(!ct tmp l (e:(A)crep_exp) p le ntmp nl n.
     n IN domain l /\
     crep_to_loop_compile_exp ct tmp l e = (p,le,ntmp,nl) ==>
     survives n (loop_nested_seq p)) /\
   (!ct tmp l (e:((A)crep_exp)list) p le ntmp nl n.
     n IN domain l /\
     crep_to_loop_compile_exps ct tmp l e = (p,le,ntmp,nl) ==>
     survives n (loop_nested_seq p))`,
  MATCH_MP_TAC crep_to_loop_compile_exp_ind THEN REPEAT CONJ_TAC THEN
  PC2LAUX_CE_SETUP_TAC THEN
  TRY (QCASES_ON "cps" THEN CASE_REWRITE_TAC[]) THEN
  DISCH_TAC THEN REPEAT PAIRARG_TAC THEN RFS[] THEN RVEQ_TAC THEN
  TRY (QCASES_ON "cop" THEN
       QPAT_X_ASSUM "compile_crepop _ _ _ _ _ _ = _"
         (MP_TAC o REWRITE_RULE[compile_crepop_def]) THEN
       COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC) THEN
  IMP_RES_TAC compile_exp_out_rel THEN IMP_RES_TAC compile_exps_out_rel THEN RVEQ_TAC THEN
  REWRITE_TAC[prog_if_def] THEN
  REPEAT (MATCH_MP_TAC survives_nested_seq_intro THEN CONJ_TAC) THEN
  ASM_SIMP_TAC[loop_nested_seq_def; survives_def; PC2LAUX_Assign_add_comm;
               survives_MAPi_Assign; domain_list_insert; IN_UNION] THEN
  TRY (ASM_MESON_TAC[comp_syn_cut_sets_mem_domain]));;

let member_cutset_survives_comp_exp = CONJUNCT1 member_cutset_survives_comp_exp_cases;;

let member_cutset_survives_comp_exps = CONJUNCT2 member_cutset_survives_comp_exp_cases;;

(* HOL4: [local] *)

let member_cutset_survives_comp_exp_flip =
  ONCE_REWRITE_RULE[CONJ_COMM] member_cutset_survives_comp_exp;;

(* HOL4: [local] *)

let member_cutset_survives_comp_exps_flip =
  ONCE_REWRITE_RULE[CONJ_COMM] member_cutset_survives_comp_exps;;

let member_cutset_survives_comp_prog = prove
 (`!ctxt l (p:(A)crep_prog) n.
     n IN domain l ==> survives n (crep_to_loop_compile ctxt l p)`,
  MATCH_MP_TAC crep_to_loop_compile_ind THEN REPEAT CONJ_TAC THEN
  REPEAT (GEN_TAC ORELSE DISCH_THEN STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[crep_to_loop_compile_def; LET_DEF; LET_END_DEF] THEN
  REPEAT PAIRARG_TAC THEN RFS[] THEN RVEQ_TAC THEN
  IMP_RES_TAC member_cutset_survives_comp_exp_flip THEN
  IMP_RES_TAC member_cutset_survives_comp_exps_flip THEN
  IMP_RES_TAC compile_exp_out_rel THEN IMP_RES_TAC compile_exps_out_rel THEN RVEQ_TAC THEN
  REPEAT TOP_CASE_TAC THEN
  REPEAT (MATCH_MP_TAC survives_nested_seq_intro THEN CONJ_TAC) THEN
  ASM_SIMP_TAC[loop_nested_seq_def; survives_def; gen_temps_def; nested_assigns_survives;
               LENGTH_LIST_OF_SEQ; domain_insert; IN_INSERT] THEN
  TRY (ASM_MESON_TAC[comp_syn_cut_sets_mem_domain]) THEN
  (* While: the body under Loop *)
  TRY (MATCH_MP_TAC survives_nested_seq_intro THEN
       ASM_SIMP_TAC[loop_nested_seq_def; survives_def] THEN NO_TAC) THEN
  (* Call: the return and handler parts *)
  QPAT_X_ASSUM "_ = (rt1,rt2)" MP_TAC THEN REPEAT TOP_CASE_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN RFS[survives_def]);;

(* HOL4 proves this by induction on compile_exp_ind; here it follows from  *)
(* comp_exp_assigned_vars_tmp_bound_cases (every assigned variable is at   *)
(* least tmp)                                                               *)

let not_mem_assigned_mem_gt_comp_exp_cases = prove
 (`(!ctxt tmp l (e:(A)crep_exp) p le ntmp nl n.
     crep_to_loop_compile_exp ctxt tmp l e = (p,le,ntmp,nl) /\
     crep_to_loopProof_ctxt_max (crep_to_loop_context_vmax ctxt)
       (crep_to_loop_context_vars ctxt) /\
     (!v m. FLOOKUP (crep_to_loop_context_vars ctxt) v = SOME m ==> ~(n = m)) /\
     n < tmp ==>
     ~MEM n (loop_assigned_vars (loop_nested_seq p))) /\
   (!ctxt tmp l (e:((A)crep_exp)list) p le ntmp nl n.
     crep_to_loop_compile_exps ctxt tmp l e = (p,le,ntmp,nl) /\
     crep_to_loopProof_ctxt_max (crep_to_loop_context_vmax ctxt)
       (crep_to_loop_context_vars ctxt) /\
     (!v m. FLOOKUP (crep_to_loop_context_vars ctxt) v = SOME m ==> ~(n = m)) /\
     n < tmp ==>
     ~MEM n (loop_assigned_vars (loop_nested_seq p)))`,
  CONJ_TAC THEN REPEAT STRIP_TAC THEN
  IMP_RES_TAC comp_exp_assigned_vars_tmp_bound THEN
  IMP_RES_TAC comp_exps_assigned_vars_tmp_bound THEN ASM_ARITH_TAC);;

let not_mem_assigned_mem_gt_comp_exp = CONJUNCT1 not_mem_assigned_mem_gt_comp_exp_cases;;

let not_mem_assigned_mem_gt_comp_exps = CONJUNCT2 not_mem_assigned_mem_gt_comp_exp_cases;;

let assigned_vars_nested_seq_assign = prove
 (`!vs (es:((A)loop_exp)list).
     LENGTH vs = LENGTH es ==>
     loop_assigned_vars (loop_nested_seq (MAP2 loop_Assign vs es)) = vs`,
  LIST_INDUCT_TAC THEN RW[MAP2; loop_nested_seq_def; loop_assigned_vars_def] THEN
  QCASES_ON "es" THEN FS[LENGTH; MAP2; HD; TL; loop_nested_seq_def;
                         loop_assigned_vars_def; APPEND]);;

(* ------------------------------------------------------------------------- *)

(* HOL4 lines 1570-1644: not_mem_context_assigned_mem_gt                   *)

(* strip quantifiers and implications, but not a negated goal               *)

let PC2LAUX_STRIP_IMP_TAC : tactic =
  REPEAT (GEN_TAC ORELSE
          (fun (asl,w as g) ->
             if is_imp w then DISCH_THEN STRIP_ASSUME_TAC g else failwith "STRIP_IMP"));;

(* ~MEM n (assigned vars of the code of an expression compiled from tmp)  *)
(* from not_mem_assigned_mem_gt_comp_exp(s) and an assumption              *)
(* crep_to_loop_compile_exp(s) ctxt tmp l e = (p,le,ntmp,nl), n < tmp      *)

let PC2LAUX_NMC_EXP_TAC th0 =
  FIRST_ASSUM(fun th ->
    MATCH_MP_TAC (REWRITE_RULE[IMP_IMP] (MATCH_MP (REWRITE_RULE[IMP_CONJ] th0) th))) THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;;

let PC2LAUX_NMC_FINISH_TAC : tactic = fun (asl,w as g) ->
  let t = dest_neg w in
  if is_eq t then
    (ASM_ARITH_TAC ORELSE (RES_TAC THEN FIRST_ASSUM ACCEPT_TAC)) g
  else
    let l = rand t in
    if is_var l then ASM_MESON_TAC[OPT_MMAP_MEM_IMP] g
    else (PC2LAUX_NMC_EXP_TAC not_mem_assigned_mem_gt_comp_exp ORELSE
          PC2LAUX_NMC_EXP_TAC not_mem_assigned_mem_gt_comp_exps ORELSE
          (FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC)) g;;

let PC2LAUX_NMC_CALL_TAC =
  REPEAT CONJ_TAC THEN
  FIRST
   [ASM_ARITH_TAC;
    REWRITE_TAC[rt_vars_def] THEN TOP_CASE_TAC THEN REWRITE_TAC[MEM] THEN
    (ASM_ARITH_TAC ORELSE ASM_MESON_TAC[OPT_MMAP_MEM_IMP]);
    RFS[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];;

let crep_to_loopProof_not_mem_context_assigned_mem_gt = prove
 (`!ctxt l (p:(A)crep_prog) n.
     crep_to_loopProof_ctxt_max (crep_to_loop_context_vmax ctxt)
       (crep_to_loop_context_vars ctxt) /\
     (!v m. FLOOKUP (crep_to_loop_context_vars ctxt) v = SOME m ==> ~(n = m)) /\
     n <= crep_to_loop_context_vmax ctxt ==>
     ~MEM n (loop_assigned_vars (crep_to_loop_compile ctxt l p))`,
  MATCH_MP_TAC crep_to_loop_compile_ind THEN REPEAT CONJ_TAC THEN
  PC2LAUX_STRIP_IMP_TAC THEN
  REWRITE_TAC[crep_to_loop_compile_def; LET_DEF; LET_END_DEF] THEN
  REPEAT PAIRARG_TAC THEN RFS[] THEN RVEQ_TAC THEN
  IMP_RES_TAC compile_exp_out_rel THEN IMP_RES_TAC compile_exps_out_rel THEN RVEQ_TAC THEN
  REPEAT TOP_CASE_TAC THEN
  REWRITE_TAC[loop_nested_seq_def; assigned_vars_nested_seq_split; loop_assigned_vars_def;
              MEM_APPEND; MEM; DE_MORGAN_THM] THEN
  REPEAT CONJ_TAC THEN TRY PC2LAUX_NMC_FINISH_TAC THENL
   [(* Return: the temporaries *)
    ASM_SIMP_TAC[assigned_vars_nested_seq_assign; gen_temps_def; LENGTH_LIST_OF_SEQ;
                 MEM_GENLIST] THEN REPEAT STRIP_TAC THEN ASM_ARITH_TAC;
    (* Dec: the induction hypothesis for the new context *)
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[crep_to_loopProof_ctxt_max_def; FLOOKUP_UPDATE] THEN
    QPAT_X_ASSUM "crep_to_loopProof_ctxt_max _ _"
      (MP_TAC o REWRITE_RULE[crep_to_loopProof_ctxt_max_def]) THEN
    REPEAT STRIP_TAC THEN
    TRY (QPAT_X_ASSUM "(if _ then _ else _) = SOME _" MP_TAC THEN COND_CASES_TAC THEN
         REWRITE_TAC[option_INJ] THEN STRIP_TAC) THEN
    RVEQ_TAC THEN RES_TAC THEN ASM_ARITH_TAC;
    (* Call: the temporaries *)
    ASM_SIMP_TAC[assigned_vars_nested_seq_assign; gen_temps_def; LENGTH_LIST_OF_SEQ;
                 MEM_GENLIST] THEN REPEAT STRIP_TAC THEN ASM_ARITH_TAC;
    (* Call: the returned variables and the handler *)
    QPAT_X_ASSUM "_ = (rt1,rt2)" MP_TAC THEN REPEAT TOP_CASE_TAC THEN
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    REWRITE_TAC[loop_assigned_vars_def; MEM_APPEND; MEM; DE_MORGAN_THM] THEN
    PC2LAUX_NMC_CALL_TAC]);;

(* ------------------------------------------------------------------------- *)

(* HOL4: ncompile_correct is stated here and proved case by case (suspend  *)
(* and Resume).  In this file: PC2LAUX_ncompile_stmt is its statement,      *)
(* PC2LAUX_ncompile_P the predicate of the induction on crep_evaluate_ind  *)
(* (HOL4 recInduct evaluate_ind), PC2LAUX_ncompile_case c the case of the   *)
(* induction theorem for the crepLang constructor c, beta-reduced as the    *)
(* goal of HOL4's Resume ncompile_correct[c]; each case is proved below as *)
(* PC2LAUX_ncompile_c, and ncompile_correct follows them (HOL4 Finalise).  *)

let PC2LAUX_ncompile_stmt = CASE_TERM
 `!v (v1:(A,FFI)crep_state) res s1 (t:(A,FFI)loop_state) ctxt l.
    crep_evaluate (v,v1) = (res,s1) /\ ~(res = SOME crep_Error) /\
    crep_to_loopProof_state_rel v1 t /\
    mem_rel (crep_state_memory v1) (loop_state_memory t) (crep_state_memaddrs v1) /\
    crep_to_loopProof_globals_rel (crep_state_globals v1) (loop_state_globals t) /\
    crep_to_loopProof_code_rel ctxt (crep_state_code v1) (loop_state_code t) /\
    crep_to_loopProof_locals_rel ctxt l (crep_state_locals v1) (loop_state_locals t) ==>
    ?ck res1 t1.
      loop_evaluate (crep_to_loop_compile ctxt l v,
                     loop_state_clock_fupd (K (loop_state_clock t + ck)) t) = (res1,t1) /\
      crep_to_loopProof_state_rel s1 t1 /\
      mem_rel (crep_state_memory s1) (loop_state_memory t1) (crep_state_memaddrs s1) /\
      crep_to_loopProof_globals_rel (crep_state_globals s1) (loop_state_globals t1) /\
      crep_to_loopProof_code_rel ctxt (crep_state_code s1) (loop_state_code t1) /\
      res1 = (match res with
                NONE -> NONE
              | SOME (crepSem_Break n) -> SOME (loopSem_Break n)
              | SOME (crepSem_Continue n) -> SOME (loopSem_Continue n)
              | SOME (crepSem_Return vs) -> SOME (loop_Result (MAP wlab_wloc vs))
              | SOME (crep_Exception eid) -> SOME (loop_Exception (wl_Word eid))
              | SOME crep_TimeOut -> SOME loop_TimeOut
              | SOME (crep_FinalFFI f) -> SOME (loop_FinalFFI f)
              | SOME crep_Error -> SOME loop_Error) /\
      (match res with
         NONE ->
           crep_to_loopProof_locals_rel ctxt l (crep_state_locals s1) (loop_state_locals t1)
       | SOME (crepSem_Break n) ->
           crep_to_loopProof_locals_rel ctxt l (crep_state_locals s1) (loop_state_locals t1)
       | SOME (crepSem_Continue n) ->
           crep_to_loopProof_locals_rel ctxt l (crep_state_locals s1) (loop_state_locals t1)
       | SOME (crepSem_Return vs) -> T
       | SOME crep_Error -> F
       | _ -> T)`;;

let PC2LAUX_ncompile_P =
  let v,b = dest_forall PC2LAUX_ncompile_stmt in
  let v1,b = dest_forall b in
  let p = mk_var("p",mk_type("prod",[type_of v; type_of v1])) in
  let fst_p = mk_icomb(`FST:A#B->A`,p) and snd_p = mk_icomb(`SND:A#B->B`,p) in
  mk_abs(p,vsubst [fst_p,v; snd_p,v1] b);;

let PC2LAUX_ncompile_case =
  let th = ISPEC PC2LAUX_ncompile_P crep_evaluate_ind in
  let cs = conjuncts (lhand (concl th)) in
  let ctor c = let _,b = strip_forall c in
               let b = if is_imp b then rand b else b in
               fst(dest_const(fst(strip_comb(lhand(rand b))))) in
  let red c = rhs(concl((DEPTH_CONV BETA_CONV THENC REWRITE_CONV[FST; SND]) c)) in
  fun name -> red (find (fun c -> ctor c = name) cs);;

(* ------------------------------------------------------------------------- *)

(* shared local helpers for the cases of ncompile_correct (PC2L): the     *)
(* locals relation after compiling an expression and after an assignment *)

(* local helpers: the locals relation after compiling an expression (the     *)
(* cut set grows from l to nl) and after an assignment of a variable         *)

let PC2LAUX_locals_rel_exp_restrict = prove
 (`!ctxt tmp l (e:(A)crep_exp) p le tmp' nl sl tl0 tl.
   crep_to_loop_compile_exp ctxt tmp l e = (p,le,tmp',nl) /\
   crep_to_loopProof_locals_rel ctxt l (sl:(num,(A)word_lab)fmap) tl0 /\
   crep_to_loopProof_locals_rel ctxt nl sl (tl:((A)word_loc)spt) ==>
   crep_to_loopProof_locals_rel ctxt l sl tl`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC locals_rel_cutset_prop THEN
  MAP_EVERY EXISTS_TAC [`tl0:((A)word_loc)spt`; `nl:num_set`] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP compile_exp_out_rel) THEN
  ASM_MESON_TAC[comp_syn_impl_cut_sets_subspt]);;

let PC2LAUX_locals_rel_update = prove
 (`!ctxt l (sl:(num,(A)word_lab)fmap) tl v n w.
   crep_to_loopProof_locals_rel ctxt l sl tl /\
   FLOOKUP (crep_to_loop_context_vars ctxt) v = SOME n /\ n IN domain l ==>
   crep_to_loopProof_locals_rel ctxt l (sl |+ (v,w)) (insert n (wlab_wloc w) tl)`,
  REWRITE_TAC[crep_to_loopProof_locals_rel_def; domain_insert] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[FLOOKUP_UPDATE] THEN
  COND_CASES_TAC THENL
   [RW[] THEN ASM_REWRITE_TAC[lookup_insert]; ALL_TAC] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`vname:num`; `v':(A)word_lab`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN QEXISTS_TAC "n'" THEN
  ASM_REWRITE_TAC[lookup_insert] THEN
  QBY "~(n' = n)" (ASM_MESON_TAC[distinct_vars_def]) THEN ASM_REWRITE_TAC[]);;

let PC2LAUX_LOCALS_EXP_TAC : tactic =
  let restrict = MATCH_MP_TAC PC2LAUX_locals_rel_exp_restrict THEN ASM_EXISTS_TAC THEN
                 ASM_REWRITE_TAC[] THEN NO_TAC in
  restrict ORELSE
  (ONCE_REWRITE_TAC[GSYM wlab_wloc_def] THEN MATCH_MP_TAC PC2LAUX_locals_rel_update THEN
   ASM_REWRITE_TAC[] THEN restrict);;


(* ------------------------------------------------------------------------- *)

(* HOL4 lines 1646-1756: the cases Skip, Break, Continue, Tick, Seq, Return  *)
(* and Raise of ncompile_correct (HOL4 Resume ncompile_correct[...]).        *)

let PC2LAUX_NC_SIMPLE_TAC =
  REPEAT STRIP_TAC THEN FS[crep_evaluate_def; loop_evaluate_def; crep_to_loop_compile_def] THEN
  RVEQ_TAC THEN QEXISTS_TAC "0" THEN FS[ADD_0; RECORD_SELFID_ss] THEN CASE_REWRITE_TAC[];;

(* HOL4: Resume ncompile_correct[Skip] *)

let PC2LAUX_ncompile_Skip = prove
 (PC2LAUX_ncompile_case "crep_Skip",
  PC2LAUX_NC_SIMPLE_TAC);;

(* HOL4: Resume ncompile_correct[Break] *)

let PC2LAUX_ncompile_Break = prove
 (PC2LAUX_ncompile_case "crep_Break",
  PC2LAUX_NC_SIMPLE_TAC);;

(* HOL4: Resume ncompile_correct[Continue] *)

let PC2LAUX_ncompile_Continue = prove
 (PC2LAUX_ncompile_case "crep_Continue",
  PC2LAUX_NC_SIMPLE_TAC);;

(* HOL4: Resume ncompile_correct[Tick] *)

let PC2LAUX_ncompile_Tick = prove
 (PC2LAUX_ncompile_case "crep_Tick",
  RW[] THEN
  FS([crep_evaluate_def; loop_evaluate_def; crep_to_loop_compile_def] @ all_case_eqs()) THEN
  RVEQ_TAC THEN
  FS[crep_to_loopProof_state_rel_def; crep_empty_locals_def; crep_dec_clock_def;
     loop_dec_clock_def] THEN
  GVS[] THEN QEXISTS_TAC "0" THEN FS[ADD_0; RECORD_SELFID_ss] THEN CASE_REWRITE_TAC[]);;

(* HOL4: Resume ncompile_correct[Seq] *)

let PC2LAUX_ncompile_Seq = prove
 (PC2LAUX_ncompile_case "crep_Seq",
  RW[] THEN FS[crep_evaluate_def] THEN PAIRARG_TAC THEN FS[] THEN
  ASM_CASES_TAC `res':((A)crep_result)option = NONE` THEN FS[] THEN RVEQ_TAC THENL
   [FS[crep_to_loop_compile_def; loop_evaluate_def] THEN
    LAST_X_ASSUM(MP_TAC o SPECL [`t:(A,FFI)loop_state`; `ctxt:crep_to_loop_context`;
                                 `l:num_set`]) THEN
    ASM_REWRITE_TAC[option_DISTINCT] THEN CASE_REWRITE_TAC[] THEN STRIP_TAC THEN RVEQ_TAC THEN
    LAST_X_ASSUM(MP_TAC o SPECL [`res:((A)crep_result)option`; `s1:(A,FFI)crep_state`;
      `t1:(A,FFI)loop_state`; `ctxt:crep_to_loop_context`; `l:num_set`]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`crep_to_loop_compile ctxt l (c1:(A)crep_prog)`;
      `loop_state_clock_fupd (K (loop_state_clock t + ck)) (t:(A,FFI)loop_state)`;
      `NONE:((A)loop_result)option`; `t1:(A,FFI)loop_state`; `ck':num`]
      loop_evaluate_add_clock_eq) THEN
    ASM_REWRITE_TAC[option_DISTINCT] THEN SIMP[GSYM ADD_ASSOC] THEN DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC [`ck + ck':num`; `t1':(A,FFI)loop_state`] THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[];
    QPAT_X_ASSUM "(if res' = NONE then _ else _) = _" MP_TAC THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
    STRIP_TAC THEN RVEQ_TAC THEN
    FS[crep_to_loop_compile_def; loop_evaluate_def] THEN
    LAST_X_ASSUM(MP_TAC o SPECL [`t:(A,FFI)loop_state`; `ctxt:crep_to_loop_context`;
                                 `l:num_set`]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`ck:num`; `t1:(A,FFI)loop_state`] THEN ASM_REWRITE_TAC[] THEN
    NAMED_CASES_ON "res" ["";"r"] THEN FS[] THEN NAMED_CASES_ON "r" [] THEN
    CASE_REWRITE_TAC[] THEN FS[option_DISTINCT]]);;

(* HOL4: Resume ncompile_correct[Return] *)

let PC2LAUX_ncompile_Return = prove
 (PC2LAUX_ncompile_case "crep_Return",
  RW[] THEN
  FS([crep_evaluate_def; crep_to_loop_compile_def] @ all_case_eqs()) THEN RVEQ_TAC THEN
  REPEAT(PAIRARG_TAC THEN FS[]) THEN RVEQ_TAC THEN
  MP_TAC(ISPECL [`es:((A)crep_exp)list`; `s:(A,FFI)crep_state`; `a:((A)word_lab)list`;
    `t:(A,FFI)loop_state`; `ctxt:crep_to_loop_context`; `crep_to_loop_context_vmax ctxt + 1`;
    `l:num_set`; `p:((A)loop_prog)list`; `les:((A)loop_exp)list`; `ntmp:num`; `nl:num_set`]
    comp_exps_preserves_eval) THEN
  ASM_REWRITE_TAC[ARITH_RULE `n < n + 1`] THEN STRIP_TAC THEN
  EXISTS_TAC `ck:num` THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  QPAT_ASSUM "loop_evaluate (loop_nested_seq p,_) = _"
    (fun th -> REWRITE_TAC[GEN_ALL(MATCH_MP evaluate_none_nested_seq_append th)]) THEN
  SUBGOAL_THEN `ALL_DISTINCT (gen_temps ntmp (LENGTH (les:((A)loop_exp)list))) /\
                distinct_lists (gen_temps ntmp (LENGTH les)) (FLAT (MAP locals_touched les))`
    STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[gen_temps_def; ALL_DISTINCT_GENLIST; distinct_lists_def; EVERY_GENLIST] THEN
    CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`s:(A,FFI)crep_state`; `ctxt:crep_to_loop_context`; `l:num_set`;
      `loop_state_locals (t:(A,FFI)loop_state)`; `crep_to_loop_context_vmax ctxt + 1`;
      `es:((A)crep_exp)list`; `p:((A)loop_prog)list`; `les:((A)loop_exp)list`; `ntmp:num`;
      `nl:num_set`; `ntmp + i:num`; `a:((A)word_lab)list`] PC2LAUX_les_tmp_domain_eval) THEN
    ASM_REWRITE_TAC[ARITH_RULE `n < n + 1`] THEN ARITH_TAC;
    ALL_TAC] THEN
  QSUBGOAL "LENGTH (gen_temps ntmp (LENGTH les)) = LENGTH les" THENL
   [REWRITE_TAC[gen_temps_def; LENGTH_LIST_OF_SEQ]; ALL_TAC] THEN
  QSUBGOAL "LENGTH (les:((A)loop_exp)list) = LENGTH (MAP wlab_wloc (a:((A)word_lab)list))" THENL
   [ASM_MESON_TAC[opt_mmap_length_eq]; ALL_TAC] THEN
  MP_TAC(ISPECL [`les:((A)loop_exp)list`; `gen_temps ntmp (LENGTH (les:((A)loop_exp)list))`;
    `st:(A,FFI)loop_state`; `MAP wlab_wloc (a:((A)word_lab)list)`]
    loop_eval_nested_assign_distinct_eq) THEN
  ASM_REWRITE_TAC[GSYM opt_mmap_eq_some] THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GEN_ALL(MATCH_MP evaluate_none_nested_seq_append th)]) THEN
  REWRITE_TAC[loop_nested_seq_def] THEN ONCE_REWRITE_TAC[loop_evaluate_def] THEN
  SIMP[loop_evaluate_def] THEN
  MP_TAC(ISPECL [`gen_temps ntmp (LENGTH (les:((A)loop_exp)list))`;
    `MAP wlab_wloc (a:((A)word_lab)list)`; `st:(A,FFI)loop_state`]
    get_vars_local_update_some_eq) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_TAC] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  SIMP[call_env_def; crep_empty_locals_def; option_DISTINCT] THEN
  FS[crep_to_loopProof_state_rel_def]);;

(* HOL4: Resume ncompile_correct[Raise] *)

let PC2LAUX_ncompile_Raise = prove
 (PC2LAUX_ncompile_case "crep_Raise",
  RW[] THEN
  FS[crep_evaluate_def; loop_evaluate_def; crep_to_loop_compile_def; loop_eval_def;
     loop_set_var_def; lookup_insert; call_env_def; crep_to_loopProof_state_rel_def;
     crep_empty_locals_def] THEN RVEQ_TAC THEN
  FS[mem_rel_def] THEN QEXISTS_TAC "0" THEN FS[ADD_0; RECORD_SELFID_ss] THEN
  CASE_REWRITE_TAC[] THEN FS[]);;

(* ------------------------------------------------------------------------- *)

(* HOL4 lines 1758-2104: the cases Store, Store32, StoreByte and StoreGlob  *)
(* of ncompile_correct.  Local helpers: the two expressions of a store      *)
(* compiled and evaluated one after the other (HOL4 does it inline, twice    *)
(* comp_exp_preserves_eval and nested_seq_pure_evaluation), inversion of     *)
(* crep_evaluate on the stores, and the memory stores under mem_rel.  The    *)
(* cases need PC2LAUX_LOCALS_EXP_TAC of the shared helpers (f05k).          *)

let PC2LAUX_comp_exp_two_eval = prove
 (`!s e1 e2 v1 v2 (t:(A,FFI)loop_state) ctxt tmp l p1 le1 tmp1 l1 p2 le2 tmp2 l2.
     crep_eval s e1 = SOME v1 /\ crep_eval s e2 = SOME v2 /\
     crep_to_loopProof_state_rel s t /\
     mem_rel (crep_state_memory s) (loop_state_memory t) (crep_state_memaddrs s) /\
     crep_to_loopProof_globals_rel (crep_state_globals s) (loop_state_globals t) /\
     crep_to_loopProof_code_rel ctxt (crep_state_code s) (loop_state_code t) /\
     crep_to_loopProof_locals_rel ctxt l (crep_state_locals s) (loop_state_locals t) /\
     crep_to_loop_compile_exp ctxt tmp l e1 = (p1,le1,tmp1,l1) /\
     crep_to_loop_compile_exp ctxt tmp1 l1 e2 = (p2,le2,tmp2,l2) /\
     crep_to_loop_context_vmax ctxt < tmp ==>
     ?ck st.
       loop_evaluate (loop_nested_seq (APPEND p1 p2),
                      loop_state_clock_fupd (K (loop_state_clock t + ck)) t) = (NONE,st) /\
       loop_eval st le1 = SOME (wlab_wloc v1) /\ loop_eval st le2 = SOME (wlab_wloc v2) /\
       crep_to_loopProof_state_rel s st /\
       mem_rel (crep_state_memory s) (loop_state_memory st) (crep_state_memaddrs s) /\
       crep_to_loopProof_globals_rel (crep_state_globals s) (loop_state_globals st) /\
       crep_to_loopProof_code_rel ctxt (crep_state_code s) (loop_state_code st) /\
       crep_to_loopProof_locals_rel ctxt l2 (crep_state_locals s) (loop_state_locals st) /\
       tmp <= tmp1 /\ tmp1 <= tmp2 /\ subspt l l2 /\
       (!n. MEM n (locals_touched le1) ==> n < tmp1) /\
       (!n. MEM n (locals_touched le2) ==> n < tmp2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:(A,FFI)crep_state`; `e1:(A)crep_exp`; `v1:(A)word_lab`;
    `t:(A,FFI)loop_state`; `ctxt:crep_to_loop_context`; `tmp:num`; `l:num_set`;
    `p1:((A)loop_prog)list`; `le1:(A)loop_exp`; `tmp1:num`; `l1:num_set`]
    crep_to_loopProof_comp_exp_preserves_eval) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  IMP_RES_TAC compile_exp_out_rel THEN
  SUBGOAL_THEN `crep_to_loop_context_vmax ctxt < tmp1` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:(A,FFI)crep_state`; `e2:(A)crep_exp`; `v2:(A)word_lab`;
    `st:(A,FFI)loop_state`; `ctxt:crep_to_loop_context`; `tmp1:num`; `l1:num_set`;
    `p2:((A)loop_prog)list`; `le2:(A)loop_exp`; `tmp2:num`; `l2:num_set`]
    crep_to_loopProof_comp_exp_preserves_eval) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`loop_nested_seq p1:(A)loop_prog`;
    `loop_state_clock_fupd (K (loop_state_clock t + ck)) (t:(A,FFI)loop_state)`;
    `NONE:((A)loop_result)option`; `st:(A,FFI)loop_state`; `ck':num`]
    loop_evaluate_add_clock_eq) THEN
  ASM_REWRITE_TAC[option_DISTINCT] THEN SIMP[GSYM ADD_ASSOC] THEN DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC [`ck + ck':num`; `st':(A,FFI)loop_state`] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP evaluate_none_nested_seq_append th]) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC nested_seq_pure_evaluation THEN
    MAP_EVERY EXISTS_TAC [`p1:((A)loop_prog)list`; `p2:((A)loop_prog)list`;
      `t:(A,FFI)loop_state`; `st:(A,FFI)loop_state`; `l:num_set`; `tmp1:num`;
      `ck:num`; `ck':num`] THEN
    ONCE_REWRITE_TAC[ADD_SYM] THEN ASM_REWRITE_TAC[] THEN
    TRY(QPAT_X_ASSUM "l1 = cut_sets l _" (SUBST_ALL_TAC)) THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
    IMP_RES_TAC comp_exp_assigned_vars_tmp_bound THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`s:(A,FFI)crep_state`; `ctxt:crep_to_loop_context`; `l:num_set`;
      `loop_state_locals (t:(A,FFI)loop_state)`; `tmp:num`; `e1:(A)crep_exp`;
      `p1:((A)loop_prog)list`; `le1:(A)loop_exp`; `tmp1:num`;
      `cut_sets l (loop_nested_seq (p1:((A)loop_prog)list))`; `n:num`; `v1:(A)word_lab`]
      PC2LAUX_le_tmp_domain_eval) THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC (GEN_ALL subspt_trans) THEN EXISTS_TAC `l1:num_set` THEN
    ASM_MESON_TAC[comp_syn_impl_cut_sets_subspt];
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`s:(A,FFI)crep_state`; `ctxt:crep_to_loop_context`; `l:num_set`;
      `loop_state_locals (t:(A,FFI)loop_state)`; `tmp:num`; `e1:(A)crep_exp`;
      `p1:((A)loop_prog)list`; `le1:(A)loop_exp`; `tmp1:num`; `l1:num_set`; `n:num`;
      `v1:(A)word_lab`] PC2LAUX_le_tmp_domain_eval) THEN ASM_SIMP_TAC[];
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`s:(A,FFI)crep_state`; `ctxt:crep_to_loop_context`; `l1:num_set`;
      `loop_state_locals (st:(A,FFI)loop_state)`; `tmp1:num`; `e2:(A)crep_exp`;
      `p2:((A)loop_prog)list`; `le2:(A)loop_exp`; `tmp2:num`; `l2:num_set`; `n:num`;
      `v2:(A)word_lab`] PC2LAUX_le_tmp_domain_eval) THEN ASM_SIMP_TAC[]]);;

let PC2LAUX_crep_evaluate_Store = prove
 (`!dst src (s:(A,FFI)crep_state) res s1.
     crep_evaluate (crep_Store dst src,s) = (res,s1) /\ ~(res = SOME crep_Error) ==>
     ?adr w m. crep_eval s dst = SOME (Word adr) /\ crep_eval s src = SOME w /\
               pan_mem_store adr w (crep_state_memaddrs s) (crep_state_memory s) = SOME m /\
               res = NONE /\ s1 = crep_state_memory_fupd (K m) s`,
  REPEAT STRIP_TAC THEN GVS([crep_evaluate_def] @ all_case_eqs()));;

let PC2LAUX_crep_evaluate_Store32 = prove
 (`!dst src (s:(A,FFI)crep_state) res s1.
     crep_evaluate (crep_Store32 dst src,s) = (res,s1) /\ ~(res = SOME crep_Error) ==>
     ?adr w m. crep_eval s dst = SOME (Word adr) /\ crep_eval s src = SOME (Word w) /\
               pan_mem_store_32 (crep_state_memory s) (crep_state_memaddrs s)
                 (crep_state_be s) adr (word_zx w) = SOME m /\
               res = NONE /\ s1 = crep_state_memory_fupd (K m) s`,
  REPEAT STRIP_TAC THEN GVS([crep_evaluate_def] @ all_case_eqs()));;

let PC2LAUX_crep_evaluate_StoreByte = prove
 (`!dst src (s:(A,FFI)crep_state) res s1.
     crep_evaluate (crep_StoreByte dst src,s) = (res,s1) /\ ~(res = SOME crep_Error) ==>
     ?adr w m. crep_eval s dst = SOME (Word adr) /\ crep_eval s src = SOME (Word w) /\
               pan_mem_store_byte (crep_state_memory s) (crep_state_memaddrs s)
                 (crep_state_be s) adr (word_zx w) = SOME m /\
               res = NONE /\ s1 = crep_state_memory_fupd (K m) s`,
  REPEAT STRIP_TAC THEN GVS([crep_evaluate_def] @ all_case_eqs()));;

let PC2LAUX_crep_evaluate_StoreGlob = prove
 (`!dst src (s:(A,FFI)crep_state) res s1.
     crep_evaluate (StoreGlob dst src,s) = (res,s1) /\ ~(res = SOME crep_Error) ==>
     ?w. crep_eval s src = SOME w /\ res = NONE /\ s1 = crep_set_globals dst w s`,
  REPEAT STRIP_TAC THEN GVS([crep_evaluate_def] @ all_case_eqs()));;

let PC2LAUX_mem_store_rel = prove
 (`!(adr:A word) w dm (sm:A word->(A)word_lab) tm sm'.
     mem_rel sm tm dm /\ pan_mem_store adr w dm sm = SOME sm' ==>
     adr IN dm /\ mem_rel sm' ((adr =+ wlab_wloc w) tm) dm`,
  REWRITE_TAC[pan_mem_store_def; mem_rel_def] THEN REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[APPLY_UPDATE_THM] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[]);;
let PC2LAUX_STORE_REL_TAC defs =
  REWRITE_TAC defs THEN REPEAT GEN_TAC THEN
  TRY(ASM_CASES_TAC `alignment_aligned 2 (w:A word)` THEN ASM_REWRITE_TAC[option_DISTINCT]) THEN
  QCASES_ON "sm (byte_align w:A word)" THEN CASE_REWRITE_TAC[] THEN
  ASM_CASES_TAC `byte_align (w:A word) IN dm` THEN ASM_REWRITE_TAC[option_DISTINCT] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `byte_align (w:A word)` o REWRITE_RULE[mem_rel_def]) THEN
  ASM_REWRITE_TAC[wlab_wloc_def] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  CASE_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LET_DEF; LET_END_DEF; option_INJ]) THEN
  ASM_REWRITE_TAC[LET_DEF; LET_END_DEF; option_INJ; RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[mem_rel_def; APPLY_UPDATE_THM] THEN REPEAT STRIP_TAC THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[wlab_wloc_def] THEN ASM_MESON_TAC[mem_rel_def];;

let PC2LAUX_mem_store_32_rel = prove
 (`!(sm:A word->(A)word_lab) tm dm be w hw sm'.
     mem_rel sm tm dm /\ pan_mem_store_32 sm dm be w hw = SOME sm' ==>
     ?tm'. mem_store_32 tm dm be w hw = SOME tm' /\ mem_rel sm' tm' dm`,
  PC2LAUX_STORE_REL_TAC [pan_mem_store_32_def; mem_store_32_def]);;

let PC2LAUX_mem_store_byte_rel = prove
 (`!(sm:A word->(A)word_lab) tm dm be w b sm'.
     mem_rel sm tm dm /\ pan_mem_store_byte sm dm be w b = SOME sm' ==>
     ?tm'. mem_store_byte_aux tm dm be w b = SOME tm' /\ mem_rel sm' tm' dm`,
  PC2LAUX_STORE_REL_TAC [pan_mem_store_byte_def; mem_store_byte_aux_def]);;

(* HOL4: Resume ncompile_correct[Store] *)

let PC2LAUX_ncompile_Store = prove
 (PC2LAUX_ncompile_case "crep_Store",
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`dst:(A)crep_exp`; `src:(A)crep_exp`; `s:(A,FFI)crep_state`;
    `res:((A)crep_result)option`; `s1:(A,FFI)crep_state`] PC2LAUX_crep_evaluate_Store) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[crep_to_loop_compile_def] THEN
  NAMED_CASES_ON "crep_to_loop_compile_exp ctxt (crep_to_loop_context_vmax ctxt + 1) l dst"
    ["dp dle dtmp dl"] THEN CASE_REWRITE_TAC[] THEN
  NAMED_CASES_ON "crep_to_loop_compile_exp ctxt dtmp dl src" ["sp sle stmp sl"] THEN
  CASE_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`s:(A,FFI)crep_state`; `dst:(A)crep_exp`; `src:(A)crep_exp`;
    `Word adr:(A)word_lab`; `w:(A)word_lab`; `t:(A,FFI)loop_state`; `ctxt:crep_to_loop_context`;
    `crep_to_loop_context_vmax ctxt + 1`; `l:num_set`;
    `dp:((A)loop_prog)list`; `dle:(A)loop_exp`; `dtmp:num`; `dl:num_set`;
    `sp:((A)loop_prog)list`; `sle:(A)loop_exp`; `stmp:num`; `sl:num_set`]
    PC2LAUX_comp_exp_two_eval) THEN
  ASM_REWRITE_TAC[ARITH_RULE `n < n + 1`] THEN STRIP_TAC THEN
  EXISTS_TAC `ck:num` THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP evaluate_none_nested_seq_append th]) THEN
  SUBGOAL_THEN `loop_eval (loop_set_var stmp (wlab_wloc w) (st:(A,FFI)loop_state)) dle =
                SOME (wl_Word adr)` ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[wlab_wloc_def]) THEN
    QPAT_ASSUM "loop_eval st dle = _" (fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
    REWRITE_TAC[loop_set_var_def] THEN MATCH_MP_TAC locals_touched_eq_eval_eq THEN
    SIMP[lookup_insert] THEN REPEAT STRIP_TAC THEN RES_TAC THEN
    SUBGOAL_THEN `~(n:num = stmp)` (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`adr:A word`; `w:(A)word_lab`; `crep_state_memaddrs (s:(A,FFI)crep_state)`;
    `crep_state_memory (s:(A,FFI)crep_state)`; `loop_state_memory (st:(A,FFI)loop_state)`;
    `m:A word->(A)word_lab`] PC2LAUX_mem_store_rel) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[loop_set_var_def]) THEN
  SIMP[loop_nested_seq_def; loop_evaluate_def; loop_set_var_def; lookup_insert;
       loop_mem_store_def] THEN
  QBY "adr IN loop_state_mdomain st" (ASM_MESON_TAC[crep_to_loopProof_state_rel_def]) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN SIMP[] THEN
  CONJ_TAC THENL [FS[crep_to_loopProof_state_rel_def]; ALL_TAC] THEN
  MATCH_MP_TAC locals_rel_insert_gt_vmax THEN
  CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
  MATCH_MP_TAC locals_rel_cutset_prop THEN
  MAP_EVERY EXISTS_TAC [`loop_state_locals (t:(A,FFI)loop_state)`; `sl:num_set`] THEN
  ASM_REWRITE_TAC[]);;

(* the cases Store32 and StoreByte: inv_th inverts the crep evaluation,      *)
(* rel_th relates the two memory stores, zxw is the stored value word_zx w  *)

let PC2LAUX_NC_STORE_N_TAC (inv_th,rel_th,zxw) =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`dst:(A)crep_exp`; `src:(A)crep_exp`; `s:(A,FFI)crep_state`;
    `res:((A)crep_result)option`; `s1:(A,FFI)crep_state`] inv_th) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[crep_to_loop_compile_def] THEN
  NAMED_CASES_ON "crep_to_loop_compile_exp ctxt (crep_to_loop_context_vmax ctxt + 1) l dst"
    ["dp dle dtmp dl"] THEN CASE_REWRITE_TAC[] THEN
  NAMED_CASES_ON "crep_to_loop_compile_exp ctxt dtmp dl src" ["sp sle stmp sl"] THEN
  CASE_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`s:(A,FFI)crep_state`; `dst:(A)crep_exp`; `src:(A)crep_exp`;
    `Word adr:(A)word_lab`; `Word w:(A)word_lab`; `t:(A,FFI)loop_state`;
    `ctxt:crep_to_loop_context`;
    `crep_to_loop_context_vmax ctxt + 1`; `l:num_set`;
    `dp:((A)loop_prog)list`; `dle:(A)loop_exp`; `dtmp:num`; `dl:num_set`;
    `sp:((A)loop_prog)list`; `sle:(A)loop_exp`; `stmp:num`; `sl:num_set`]
    PC2LAUX_comp_exp_two_eval) THEN
  ASM_REWRITE_TAC[ARITH_RULE `n < n + 1`] THEN STRIP_TAC THEN
  EXISTS_TAC `ck:num` THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP evaluate_none_nested_seq_append th]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wlab_wloc_def]) THEN
  SUBGOAL_THEN `loop_eval (loop_set_var stmp (wl_Word adr) (st:(A,FFI)loop_state)) sle =
                SOME (wl_Word w)` ASSUME_TAC THENL
   [QPAT_ASSUM "loop_eval st sle = _" (fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
    REWRITE_TAC[loop_set_var_def] THEN MATCH_MP_TAC locals_touched_eq_eval_eq THEN
    SIMP[lookup_insert] THEN REPEAT STRIP_TAC THEN RES_TAC THEN
    SUBGOAL_THEN `~(n:num = stmp)` (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  QPAT_ASSUM "crep_to_loopProof_state_rel s st"
    (fun th -> let ths = CONJUNCTS (REWRITE_RULE[crep_to_loopProof_state_rel_def] th) in
               RULE_ASSUM_TAC(REWRITE_RULE ths) THEN REWRITE_TAC ths) THEN
  MP_TAC(ISPECL [`crep_state_memory (s:(A,FFI)crep_state)`;
    `loop_state_memory (st:(A,FFI)loop_state)`; `loop_state_mdomain (st:(A,FFI)loop_state)`;
    `loop_state_be (st:(A,FFI)loop_state)`; `adr:A word`; zxw;
    `m:A word->(A)word_lab`] rel_th) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[loop_set_var_def]) THEN
  SIMP[loop_nested_seq_def; loop_evaluate_def; loop_set_var_def; lookup_insert;
       ARITH_RULE `~(n + 1 = n) /\ ~(n = n + 1)`] THEN
  CASE_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [FS[crep_to_loopProof_state_rel_def];
    QPAT_ASSUM "crep_to_loopProof_state_rel s st"
      (fun th -> REWRITE_TAC (CONJUNCTS (REWRITE_RULE[crep_to_loopProof_state_rel_def] th))) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC locals_rel_insert_gt_vmax THEN
    CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
    MATCH_MP_TAC locals_rel_insert_gt_vmax THEN
    CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
    MATCH_MP_TAC locals_rel_cutset_prop THEN
    MAP_EVERY EXISTS_TAC [`loop_state_locals (t:(A,FFI)loop_state)`; `sl:num_set`] THEN
    ASM_REWRITE_TAC[]];;

(* HOL4: Resume ncompile_correct[Store32] *)

let PC2LAUX_ncompile_Store32 = prove
 (PC2LAUX_ncompile_case "crep_Store32",
  PC2LAUX_NC_STORE_N_TAC
    (PC2LAUX_crep_evaluate_Store32,PC2LAUX_mem_store_32_rel,`word_zx (w:A word):int32`));;

(* HOL4: Resume ncompile_correct[StoreByte] *)

let PC2LAUX_ncompile_StoreByte = prove
 (PC2LAUX_ncompile_case "crep_StoreByte",
  PC2LAUX_NC_STORE_N_TAC
    (PC2LAUX_crep_evaluate_StoreByte,PC2LAUX_mem_store_byte_rel,`word_zx (w:A word):byte`));;

(* HOL4: Resume ncompile_correct[StoreGlob] *)

let PC2LAUX_ncompile_StoreGlob = prove
 (PC2LAUX_ncompile_case "StoreGlob",
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`dst:5 word`; `src:(A)crep_exp`; `s:(A,FFI)crep_state`;
    `res:((A)crep_result)option`; `s1:(A,FFI)crep_state`] PC2LAUX_crep_evaluate_StoreGlob) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[crep_to_loop_compile_def] THEN
  NAMED_CASES_ON "crep_to_loop_compile_exp ctxt (crep_to_loop_context_vmax ctxt + 1) l src"
    ["p le tmp nl"] THEN CASE_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`s:(A,FFI)crep_state`; `src:(A)crep_exp`; `w:(A)word_lab`;
    `t:(A,FFI)loop_state`; `ctxt:crep_to_loop_context`; `crep_to_loop_context_vmax ctxt + 1`;
    `l:num_set`; `p:((A)loop_prog)list`; `le:(A)loop_exp`; `tmp:num`; `nl:num_set`]
    crep_to_loopProof_comp_exp_preserves_eval) THEN
  ASM_REWRITE_TAC[ARITH_RULE `n < n + 1`] THEN STRIP_TAC THEN
  EXISTS_TAC `ck:num` THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP evaluate_none_nested_seq_append th]) THEN
  SIMP[loop_nested_seq_def; loop_evaluate_def; crep_set_globals_def; loop_set_globals_def] THEN
  REPEAT CONJ_TAC THENL
   [FS[crep_to_loopProof_state_rel_def];
    IMP_RES_TAC crep_to_loopProof_globals_rel_intro THEN
    REWRITE_TAC[crep_to_loopProof_globals_rel_def; FLOOKUP_UPDATE] THEN
    REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[option_INJ] THEN
    STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[];
    PC2LAUX_LOCALS_EXP_TAC]);;

(* ------------------------------------------------------------------------- *)

(* HOL4 lines 2106-2406: cases ShMem and Assign; opt_mmap_rhss_locals_rel .. *)
(* crep_primop_loop_primop; case Primitive                                    *)

(* HOL4: Resume ncompile_correct[ShMem] *)

let PC2LAUX_ncompile_ShMem = prove
 (PC2LAUX_ncompile_case "crep_ShMem",
  RW[] THEN
  FS[crep_evaluate_def; loop_evaluate_def; crep_to_loop_compile_def;
     case_eq "option"; case_eq "word_lab"] THEN RVEQ_TAC THEN FS[] THEN
  QCASES_ON "FLOOKUP (crep_state_locals s) v" THEN FS[] THEN
  QCASES_ON "a'" THEN FS[] THEN
  IMP_RES_TAC crep_to_loopProof_locals_rel_intro THEN RES_TAC THEN FS[] THEN
  NAMED_CASES_ON "crep_to_loop_compile_exp ctxt (crep_to_loop_context_vmax ctxt + 1) l ad"
    ["p le tmp nl"] THEN FS[] THEN
  DRULE crep_to_loopProof_comp_exp_preserves_eval THEN
  REPEAT (DISCH_THEN (DRULE_AT (Pos hd))) THEN
  FS[ARITH_ss] THEN STRIP_TAC THEN FS[] THEN QEXISTS_TAC "ck" THEN FS[] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP evaluate_none_nested_seq_append th]) THEN
  REWRITE_TAC[loop_nested_seq_def] THEN
  QPAT_ASSUM "crep_to_loopProof_locals_rel ctxt nl _ _"
    (STRIP_ASSUME_TAC o MATCH_MP crep_to_loopProof_locals_rel_intro) THEN
  RES_TAC THEN GVS[loop_evaluate_def; wlab_wloc_def] THEN
  QCASES_ON "op" THEN
  GVS[crep_sh_mem_op_def; crep_sh_mem_load_def; crep_sh_mem_store_def;
      loop_sh_mem_op_def; loop_sh_mem_load_def; loop_sh_mem_store_def;
      crep_empty_locals_def; call_env_def; case_eq "option"; COND_CASE_EQ;
      case_eq "ffi_result"; crep_to_loopProof_state_rel_def;
      crep_set_var_def; loop_set_var_def] THEN
  PC2LAUX_LOCALS_EXP_TAC);;

(* HOL4: Resume ncompile_correct[Assign] *)

let PC2LAUX_ncompile_Assign = prove
 (PC2LAUX_ncompile_case "crep_Assign",
  RW[] THEN
  FS([crep_evaluate_def; loop_evaluate_def; crep_to_loop_compile_def] @ all_case_eqs()) THEN
  RVEQ_TAC THEN FS[] THEN
  IMP_RES_TAC crep_to_loopProof_locals_rel_intro THEN RES_TAC THEN FS[] THEN
  NAMED_CASES_ON "crep_to_loop_compile_exp ctxt (crep_to_loop_context_vmax ctxt + 1) l src"
    ["p le tmp nl"] THEN FS[] THEN
  DRULE crep_to_loopProof_comp_exp_preserves_eval THEN
  REPEAT (DISCH_THEN (DRULE_AT (Pos hd))) THEN
  FS[ARITH_ss] THEN STRIP_TAC THEN FS[] THEN QEXISTS_TAC "ck" THEN FS[] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP evaluate_none_nested_seq_append th]) THEN
  REWRITE_TAC[loop_nested_seq_def] THEN
  GVS[loop_evaluate_def; crep_set_var_def; loop_set_var_def;
      crep_to_loopProof_state_rel_def] THEN
  PC2LAUX_LOCALS_EXP_TAC);;
let opt_mmap_rhss_locals_rel = prove
 (`!rhss ws (s:(A,B)crep_state) (t:(A,C)loop_state) ctxt l.
     OPT_MMAP (FLOOKUP (crep_state_locals s)) rhss = SOME ws /\
     crep_to_loopProof_locals_rel ctxt l (crep_state_locals s) (loop_state_locals t) ==>
     ?nrhss.
       OPT_MMAP (FLOOKUP (crep_to_loop_context_vars ctxt)) rhss = SOME nrhss /\
       LENGTH nrhss = LENGTH rhss /\
       ALL (\n. n IN domain l) nrhss /\
       get_vars nrhss t = SOME (MAP wlab_wloc ws)`,
  LIST_INDUCT_TAC THEN RW[OPT_MMAP_def; get_vars_def] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP crep_to_loopProof_locals_rel_intro) THEN
  FIRST_ASSUM(fun th -> FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP th)) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:((A)word_lab)list`; `s:(A,B)crep_state`;
    `t':(A,C)loop_state`; `ctxt:crep_to_loop_context`; `l:num_set`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN QEXISTS_TAC "CONS n nrhss" THEN
  ASM_REWRITE_TAC[LENGTH; ALL; get_vars_def; option_INJ; CONS_11] THEN
  CONJ_TAC THENL [MESON_TAC[]; CASE_REWRITE_TAC[]]);;

let opt_mmap_lhss_locals_rel = prove
 (`!lhss (s:(A,B)crep_state) (t:(A,C)loop_state) ctxt l.
     ALL (\v. IS_SOME (FLOOKUP (crep_state_locals s) v)) lhss /\ ALL_DISTINCT lhss /\
     crep_to_loopProof_locals_rel ctxt l (crep_state_locals s) (loop_state_locals t) ==>
     ?nlhss.
       OPT_MMAP (FLOOKUP (crep_to_loop_context_vars ctxt)) lhss = SOME nlhss /\
       LENGTH nlhss = LENGTH lhss /\ ALL (\n. n IN domain l) nlhss /\
       ALL_DISTINCT nlhss`,
  LIST_INDUCT_TAC THEN RW[OPT_MMAP_def; ALL; ALL_DISTINCT] THEN
  QPAT_X_ASSUM "IS_SOME (FLOOKUP _ h)" (STRIP_ASSUME_TAC o REWRITE_RULE[IS_SOME_EXISTS]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP crep_to_loopProof_locals_rel_intro) THEN
  FIRST_ASSUM(fun th -> FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP th)) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`s:(A,B)crep_state`;
    `t':(A,C)loop_state`; `ctxt:crep_to_loop_context`; `l:num_set`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN QEXISTS_TAC "CONS n nlhss" THEN
  ASM_REWRITE_TAC[LENGTH; ALL; ALL_DISTINCT; option_INJ; CONS_11] THEN
  CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN
  QPAT_X_ASSUM "OPT_MMAP _ t = SOME nlhss" (MP_TAC o REWRITE_RULE[opt_mmap_eq_some]) THEN
  DISCH_THEN(MP_TAC o AP_TERM `MEM (SOME (n:num))`) THEN
  ASM_REWRITE_TAC[MEM_MAP; option_INJ] THEN
  REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o snd o EQ_IMP_RULE) THEN ANTS_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
  QPAT_X_ASSUM "distinct_vars _" (MP_TAC o REWRITE_RULE[distinct_vars_def]) THEN
  DISCH_THEN(MP_TAC o SPECL [`x':num`; `h:num`; `n:num`; `n:num`]) THEN
  ASM_MESON_TAC[]);;

let not_mem_nlhss_lemma = prove
 (`!ctxt vname lhss n nlhss.
     distinct_vars (crep_to_loop_context_vars ctxt) /\
     ~MEM vname lhss /\
     FLOOKUP (crep_to_loop_context_vars ctxt) vname = SOME n /\
     OPT_MMAP (FLOOKUP (crep_to_loop_context_vars ctxt)) lhss = SOME nlhss ==>
     ~MEM n nlhss`,
  REPEAT STRIP_TAC THEN
  QPAT_X_ASSUM "OPT_MMAP _ lhss = SOME nlhss" (MP_TAC o REWRITE_RULE[opt_mmap_eq_some]) THEN
  DISCH_THEN(MP_TAC o AP_TERM `MEM (SOME (n:num))`) THEN
  ASM_REWRITE_TAC[MEM_MAP; option_INJ] THEN
  REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o snd o EQ_IMP_RULE) THEN ANTS_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:num` STRIP_ASSUME_TAC) THEN
  QPAT_X_ASSUM "distinct_vars _" (MP_TAC o REWRITE_RULE[distinct_vars_def]) THEN
  DISCH_THEN(MP_TAC o SPECL [`y:num`; `vname:num`; `n:num`; `n:num`]) THEN
  ASM_MESON_TAC[]);;

let crep_primop_loop_primop = prove
 (`!pop ws (res_ws:((A)word_lab)list).
     crep_primop pop ws = SOME res_ws ==>
     loop_primop pop (MAP wlab_wloc ws) = SOME (MAP wlab_wloc res_ws)`,
  GEN_TAC THEN QCASES_ON "pop" THEN REWRITE_TAC[crep_primop_def; loop_primop_def] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; ARITH_RULE `~(0 = 3)`; option_DISTINCT] THEN
  QCASES_ON "t" THEN REWRITE_TAC[LENGTH; ARITH_RULE `~(SUC 0 = 3)`; option_DISTINCT] THEN
  QCASES_ON "a1" THEN
  REWRITE_TAC[LENGTH; ARITH_RULE `~(SUC (SUC 0) = 3)`; option_DISTINCT] THEN
  QCASES_ON "a1'" THEN
  REWRITE_TAC[LENGTH; ARITH_RULE `~(SUC (SUC (SUC (SUC n))) = 3) /\ SUC (SUC (SUC 0)) = 3`;
              option_DISTINCT] THEN
  QCASES_ON "h" THEN QCASES_ON "a0" THEN QCASES_ON "a0'" THEN
  REWRITE_TAC[MAP; wlab_wloc_def; ALL; pan_isWord_def; isWord_def; LENGTH; EL; HD; TL;
              ONE; TWO; ARITH_RULE `SUC (SUC (SUC 0)) = 3`] THEN
  REWRITE_TAC[GSYM ONE; GSYM TWO; pan_theWord_def; theWord_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN GEN_TAC THEN
  PAIR_CASES_ON `word_add_carry (a:A word) a' a''` THEN CASE_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o SYM o REWRITE_RULE[option_INJ]) THEN
  REWRITE_TAC[MAP; wlab_wloc_def]);;

(* HOL4: Resume ncompile_correct[Primitive] *)

let PC2LAUX_ncompile_Primitive = prove
 (PC2LAUX_ncompile_case "crep_Primitive",
  RW[] THEN
  GVS([crep_evaluate_def; loop_evaluate_def; crep_to_loop_compile_def] @ all_case_eqs()) THEN
  IMP_RES_TAC opt_mmap_rhss_locals_rel THEN IMP_RES_TAC opt_mmap_lhss_locals_rel THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN QEXISTS_TAC "0" THEN
  REWRITE_TAC[ADD_CLAUSES] THEN ONCE_REWRITE_TAC[loop_evaluate_def] THEN
  REWRITE_TAC[get_vars_clock_upd_eq] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP crep_primop_loop_primop) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[LENGTH_MAP] THEN
  REWRITE_TAC[set_vars_def] THEN
  SIMP[PAIR_EQ] THEN FS[crep_to_loopProof_state_rel_def; loop_state_component_equality] THEN
  FS[crep_to_loopProof_locals_rel_def] THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[domain_alist_insert; LENGTH_MAP] THEN ASM SET_TAC[]; ALL_TAC] THEN
  RW[] THEN ASM_CASES_TAC `MEM (vname:num) lhss` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC o REWRITE_RULE[MEM_EXISTS_EL]) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    QBY "FLOOKUP (crep_state_locals s |++ ZIP lhss a') (EL k lhss) = SOME (EL k a')"
      (MATCH_MP_TAC update_eq_zip_flookup THEN ASM_REWRITE_TAC[]) THEN
    FS[] THEN RVEQ_TAC THEN QEXISTS_TAC "EL k nlhss" THEN
    QBY "FLOOKUP (crep_to_loop_context_vars ctxt) (EL k lhss) = SOME (EL k nlhss)"
      (MATCH_MP_TAC opt_mmap_el THEN ASM_REWRITE_TAC[]) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [QPAT_X_ASSUM "ALL _ nlhss" (MP_TAC o REWRITE_RULE[EVERY_EL]) THEN
      DISCH_THEN(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[lookup_alist_insert; LENGTH_MAP] THEN
    QBY "ALOOKUP (ZIP nlhss (MAP wlab_wloc a')) (EL k nlhss) =
         SOME (EL k (MAP wlab_wloc a'))"
     (MP_TAC(ISPECL [`ZIP (nlhss:num list) (MAP wlab_wloc (a':((A)word_lab)list))`; `k:num`]
        ALOOKUP_ALL_DISTINCT_EL) THEN
      ASM_SIMP_TAC[MAP_FST_ZIP; LENGTH_ZIP; LENGTH_MAP; EL_ZIP] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC) THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    MATCH_MP_TAC EL_MAP THEN ASM_ARITH_TAC;
    QBY "FLOOKUP (crep_state_locals s) vname = SOME v"
      (FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN CONV_TAC SYM_CONV THEN
       MATCH_MP_TAC flookup_fupdate_zip_not_mem THEN ASM_REWRITE_TAC[]) THEN
    FIRST_X_ASSUM(fun th -> FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP th)) THEN
    QEXISTS_TAC "n" THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[lookup_alist_insert; LENGTH_MAP] THEN
    QBY "~MEM n nlhss" (MATCH_MP_TAC not_mem_nlhss_lemma THEN ASM_MESON_TAC[]) THEN
    QBY "ALOOKUP (ZIP nlhss (MAP wlab_wloc a')) n = NONE"
      (ASM_SIMP_TAC[ALOOKUP_NONE; MAP_FST_ZIP; LENGTH_MAP]) THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)

(* HOL4 lines 2408-2714: cases Dec, If, ExtCall                              *)

(* local helpers for the case Dec: the record theorems of the context, and  *)
(* the locals relation for the body of a declaration                        *)

let PC2LAUX_ctxt_accfupds = (record_info "crep_to_loop_context").ri_accfupds;;

let PC2LAUX_locals_rel_dec = prove
 (`!ctxt l nl (sl:(num,(A)word_lab)fmap) tl0 tl v tmp w.
     crep_to_loopProof_locals_rel ctxt l sl tl0 /\
     crep_to_loopProof_locals_rel ctxt nl sl tl /\
     domain l SUBSET domain nl /\
     crep_to_loop_context_vmax ctxt < tmp ==>
     crep_to_loopProof_locals_rel
       (crep_to_loop_context_vars_fupd (K (crep_to_loop_context_vars ctxt |+ (v,tmp)))
          (crep_to_loop_context_vmax_fupd (K tmp) ctxt))
       (insert tmp one l) (sl |+ (v,w)) (insert tmp (wlab_wloc w) tl)`,
  REWRITE_TAC[crep_to_loopProof_locals_rel_def; crep_to_loopProof_ctxt_max_def;
              distinct_vars_def; PC2LAUX_ctxt_accfupds; K_THM; domain_insert;
              FLOOKUP_UPDATE] THEN
  REPEAT STRIP_TAC THENL
   [QPAT_X_ASSUM "(if v = x then _ else _) = SOME n" MP_TAC THEN
    QPAT_X_ASSUM "(if v = y then _ else _) = SOME m" MP_TAC THEN
    REPEAT COND_CASES_TAC THEN REWRITE_TAC[option_INJ] THEN REPEAT STRIP_TAC THEN
    RVEQ_TAC THEN ASM_REWRITE_TAC[] THENL
     [ASM_MESON_TAC[ARITH_RULE `m <= n /\ n < p ==> ~(m = p)`];
      ASM_MESON_TAC[ARITH_RULE `m <= n /\ n < p ==> ~(m = p)`];
      ASM_MESON_TAC[]];
    QPAT_X_ASSUM "(if v = v' then _ else _) = SOME m" MP_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC[option_INJ] THENL [ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN RES_TAC THEN ASM_ARITH_TAC;
    ASM SET_TAC[];
    POP_ASSUM MP_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[option_INJ] THENL
     [DISCH_THEN(SUBST1_TAC o SYM) THEN QEXISTS_TAC "tmp" THEN
      REWRITE_TAC[IN_INSERT; lookup_insert];
      DISCH_TAC THEN
      MAP_EVERY (fun tac -> FIRST_X_ASSUM(fun th ->
          MP_TAC(MATCH_MP th
            (ASSUME `FLOOKUP (sl:(num,(A)word_lab)fmap) vname = SOME v'`))))
       [(); ()] THEN
      DISCH_THEN(X_CHOOSE_THEN `n1:num` STRIP_ASSUME_TAC) THEN
      DISCH_THEN(X_CHOOSE_THEN `n2:num` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `n2 = n1:num` SUBST_ALL_TAC THENL
       [ASM_MESON_TAC[option_INJ]; ALL_TAC] THEN
      QEXISTS_TAC "n1" THEN
      SUBGOAL_THEN `~(n1 = tmp:num)` ASSUME_TAC THENL
       [ASM_MESON_TAC[ARITH_RULE `m <= n /\ n < p ==> ~(m = p)`]; ALL_TAC] THEN
      ASM_REWRITE_TAC[IN_INSERT; lookup_insert]]]);;
let PC2LAUX_locals_rel_res_var = prove
 (`!ctxt l tmp v (sl:(num,(A)word_lab)fmap) stl tl tl1.
     crep_to_loopProof_locals_rel ctxt l sl tl /\
     crep_to_loopProof_locals_rel
       (crep_to_loop_context_vars_fupd (K (crep_to_loop_context_vars ctxt |+ (v,tmp)))
          (crep_to_loop_context_vmax_fupd (K tmp) ctxt))
       (insert tmp one l) stl tl1 /\
     crep_to_loop_context_vmax ctxt < tmp /\
     (!pv pn. FLOOKUP sl v = SOME pv /\ FLOOKUP (crep_to_loop_context_vars ctxt) v = SOME pn
              ==> lookup pn tl1 = SOME (wlab_wloc pv)) ==>
     crep_to_loopProof_locals_rel ctxt l (crep_res_var stl (v,FLOOKUP sl v)) tl1`,
  REWRITE_TAC[crep_to_loopProof_locals_rel_def; crep_to_loopProof_ctxt_max_def;
              PC2LAUX_ctxt_accfupds; K_THM; domain_insert; FLOOKUP_UPDATE] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [ASM_MESON_TAC[]; ASM SET_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `vname:num = v` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    QCASES_ON "FLOOKUP (sl:(num,(A)word_lab)fmap) v" THEN
    FS[crep_res_var_def; FLOOKUP_UPDATE; DOMSUB_FLOOKUP_THM] THEN RVEQ_TAC THEN
    FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP th
       (ASSUME `FLOOKUP (sl:(num,(A)word_lab)fmap) v = SOME v'`))) THEN
    STRIP_TAC THEN QEXISTS_TAC "n" THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FLOOKUP (stl:(num,(A)word_lab)fmap) vname = SOME v'` ASSUME_TAC THENL
   [QPAT_X_ASSUM "FLOOKUP (crep_res_var _ _) vname = _" MP_TAC THEN
    QCASES_ON "FLOOKUP (sl:(num,(A)word_lab)fmap) v" THEN
    ASM_REWRITE_TAC[crep_res_var_def; FLOOKUP_UPDATE; DOMSUB_FLOOKUP_THM];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP th
     (ASSUME `FLOOKUP (stl:(num,(A)word_lab)fmap) vname = SOME v'`))) THEN
  ASM_REWRITE_TAC[IN_INSERT] THEN STRIP_TAC THEN QEXISTS_TAC "n" THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[ARITH_RULE `m <= n /\ n < p ==> ~(m = p)`]);;

let PC2LAUX_code_rel_fupds = prove
 (`(!f ctxt sc (tc:(num list#(A)loop_prog)spt).
      crep_to_loopProof_code_rel (crep_to_loop_context_vars_fupd f ctxt) sc tc <=>
      crep_to_loopProof_code_rel ctxt sc tc) /\
   (!f ctxt sc (tc:(num list#(A)loop_prog)spt).
      crep_to_loopProof_code_rel (crep_to_loop_context_vmax_fupd f ctxt) sc tc <=>
      crep_to_loopProof_code_rel ctxt sc tc)`,
  REWRITE_TAC[crep_to_loopProof_code_rel_def; PC2LAUX_ctxt_accfupds]);;

let PC2LAUX_DEC_LOCALS_TAC : tactic =
  MATCH_MP_TAC PC2LAUX_locals_rel_res_var THEN
  MAP_EVERY EXISTS_TAC [`tmp:num`; `loop_state_locals (t:(A,FFI)loop_state)`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o C MATCH_MP (CONJ
    (ASSUME `FLOOKUP (crep_state_locals (s:(A,FFI)crep_state)) v = SOME pv`)
    (ASSUME `FLOOKUP (crep_to_loop_context_vars ctxt) v = SOME pn`))) THEN
  STRIP_TAC THEN
  QPAT_X_ASSUM "loop_evaluate (lp,_) = _"
    (MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] loop_unassigned_vars_evaluate_same)) THEN
  DISCH_THEN(MP_TAC o SPECL [`pn:num`; `wlab_wloc (pv:(A)word_lab)`]) THEN
  SIMP[lookup_insert] THEN ASM_REWRITE_TAC[] THEN SIMP[];;

(* HOL4: Resume ncompile_correct[Dec] *)

let PC2LAUX_ncompile_Dec = prove
 (PC2LAUX_ncompile_case "crep_Dec",
  RW[] THEN
  FS([crep_evaluate_def; loop_evaluate_def; crep_to_loop_compile_def] @ all_case_eqs()) THEN
  RVEQ_TAC THEN FS[] THEN
  NAMED_CASES_ON "crep_to_loop_compile_exp ctxt (crep_to_loop_context_vmax ctxt + 1) l e"
    ["p le tmp nl"] THEN FS[] THEN
  RENAME_TAC ["crep_eval s e = SOME value"; "crep_evaluate _ = (res,st)"] THEN
  DRULE crep_to_loopProof_comp_exp_preserves_eval THEN
  REPEAT (DISCH_THEN (DRULE_AT (Pos hd))) THEN
  FS[ARITH_ss] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP compile_exp_out_rel) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `value:(A)word_lab`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`res:((A)crep_result)option`; `st:(A,FFI)crep_state`;
     `loop_state_locals_fupd (K (insert tmp (wlab_wloc (value:(A)word_lab))
        (loop_state_locals (st':(A,FFI)loop_state)))) st'`;
     `crep_to_loop_context_vars_fupd (K (crep_to_loop_context_vars ctxt |+ (v,tmp)))
        (crep_to_loop_context_vmax_fupd (K tmp) ctxt)`;
     `insert tmp one l`]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [FS[crep_to_loopProof_state_rel_def] THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[PC2LAUX_code_rel_fupds];
      MATCH_MP_TAC PC2LAUX_locals_rel_dec THEN ASM_EXISTS_TAC THEN CONJ_TAC THENL
       [ASM_MESON_TAC[cut_sets_union_domain_subset];
        QPAT_X_ASSUM "crep_to_loop_compile_exp _ _ _ _ = _"
          (MP_TAC o CONJUNCT1 o CONJUNCT2 o MATCH_MP compile_exp_out_rel) THEN ARITH_TAC]];
    ALL_TAC] THEN
  STRIP_TAC THEN QEXISTS_TAC "ck + ck'" THEN
  QPAT_X_ASSUM "loop_evaluate (loop_nested_seq p,_) = (NONE,st')"
    (MP_TAC o SPEC `ck':num` o MATCH_MP (REWRITE_RULE[IMP_CONJ] loop_evaluate_add_clock_eq)) THEN
  SIMP[option_DISTINCT; o_DEF; ADD_ASSOC] THEN
  DISCH_TAC THEN ONCE_REWRITE_TAC[loop_evaluate_def] THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[] THEN ONCE_REWRITE_TAC[loop_evaluate_def] THEN
  REWRITE_TAC[loop_eval_upd_clock_eq] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[loop_evaluate_def] THEN
  REWRITE_TAC[loop_eval_upd_clock_eq] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[loop_set_var_def] THEN SAME_RUN_TAC[] THEN
  QEXISTS_TAC "t1" THEN REWRITE_TAC[] THEN
  FS[crep_to_loopProof_state_rel_def; PC2LAUX_code_rel_fupds] THEN
  ABBREV_TAC `nctxt = crep_to_loop_context_vars_fupd
     (K (crep_to_loop_context_vars ctxt |+ (v,tmp)))
     (crep_to_loop_context_vmax_fupd (K tmp) ctxt)` THEN
  ABBREV_TAC `lp = crep_to_loop_compile nctxt (insert tmp one l) (prog:(A)crep_prog)` THEN
  SUBGOAL_THEN
   `!pv pn. FLOOKUP (crep_state_locals (s:(A,FFI)crep_state)) v = SOME pv /\
            FLOOKUP (crep_to_loop_context_vars ctxt) v = SOME pn
            ==> lookup pn (loop_state_locals (st':(A,FFI)loop_state)) = SOME (wlab_wloc pv) /\
                ~(pn = tmp) /\
                ~MEM pn (loop_assigned_vars (lp:(A)loop_prog)) /\ survives pn lp`
   ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    QPAT_ASSUM "crep_to_loopProof_locals_rel ctxt nl _ _"
      (STRIP_ASSUME_TAC o MATCH_MP crep_to_loopProof_locals_rel_intro) THEN
    FIRST_X_ASSUM(fun th -> MP_TAC(MATCH_MP th
      (ASSUME `FLOOKUP (crep_state_locals (s:(A,FFI)crep_state)) v = SOME pv`))) THEN
    ASM_REWRITE_TAC[option_INJ] THEN
    DISCH_THEN(X_CHOOSE_THEN `n0:num` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `pn <= crep_to_loop_context_vmax ctxt` ASSUME_TAC THENL
     [ASM_MESON_TAC[crep_to_loopProof_ctxt_max_def]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [EXPAND_TAC "lp" THEN
      MATCH_MP_TAC crep_to_loopProof_not_mem_context_assigned_mem_gt THEN
      EXPAND_TAC "nctxt" THEN
      REWRITE_TAC[PC2LAUX_ctxt_accfupds; K_THM; FLOOKUP_UPDATE;
                  crep_to_loopProof_ctxt_max_def] THEN
      REPEAT CONJ_TAC THEN
      TRY (REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[option_INJ]) THEN
      REPEAT STRIP_TAC THEN TRY ASM_ARITH_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[crep_to_loopProof_ctxt_max_def; distinct_vars_def]) THEN
      RES_TAC THEN TRY ASM_ARITH_TAC THEN ASM_MESON_TAC[];
      EXPAND_TAC "lp" THEN MATCH_MP_TAC member_cutset_survives_comp_prog THEN
      REWRITE_TAC[domain_insert; IN_INSERT] THEN DISJ2_TAC THEN
      QPAT_ASSUM "crep_to_loopProof_locals_rel ctxt l _ _"
        (STRIP_ASSUME_TAC o MATCH_MP crep_to_loopProof_locals_rel_intro) THEN
      FIRST_X_ASSUM(fun th -> MP_TAC(MATCH_MP th
        (ASSUME `FLOOKUP (crep_state_locals (s:(A,FFI)crep_state)) v = SOME pv`))) THEN
      ASM_REWRITE_TAC[option_INJ] THEN MESON_TAC[]];
    ALL_TAC] THEN
  QCASES_ON "res" THEN CASE_REWRITE_TAC[] THEN RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THENL
   [PC2LAUX_DEC_LOCALS_TAC;
    TOP_CASE_TAC THEN RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
    FIRST [FS[] THEN NO_TAC; PC2LAUX_DEC_LOCALS_TAC]]);;

(* local helper: the locals relation survives the cut of a conditional *)

let PC2LAUX_locals_rel_inter = prove
 (`!ctxt l (sl:(num,(A)word_lab)fmap) tl.
     crep_to_loopProof_locals_rel ctxt l sl tl ==>
     crep_to_loopProof_locals_rel ctxt l sl (inter tl l)`,
  REWRITE_TAC[crep_to_loopProof_locals_rel_def; domain_inter] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL [ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP th)) THEN
  QEXISTS_TAC "n" THEN ASM_REWRITE_TAC[lookup_inter] THEN CASE_REWRITE_TAC[] THEN
  QPAT_X_ASSUM "n IN domain l" (STRIP_ASSUME_TAC o REWRITE_RULE[domain_lookup]) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]);;

(* HOL4: Resume ncompile_correct[If] *)

let PC2LAUX_ncompile_If = prove
 (PC2LAUX_ncompile_case "crep_If",
  RW[] THEN
  FS([crep_evaluate_def; loop_evaluate_def; crep_to_loop_compile_def] @ all_case_eqs()) THEN
  RVEQ_TAC THEN FS[] THEN
  NAMED_CASES_ON "crep_to_loop_compile_exp ctxt (crep_to_loop_context_vmax ctxt + 1) l e"
    ["np le tmp nl"] THEN FS[] THEN
  DRULE crep_to_loopProof_comp_exp_preserves_eval THEN
  REPEAT (DISCH_THEN (DRULE_AT (Pos hd))) THEN
  FS[ARITH_ss; wlab_wloc_def] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP compile_exp_out_rel) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `a:A word`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`res:((A)crep_result)option`; `s1:(A,FFI)crep_state`;
     `loop_state_locals_fupd (K (insert tmp (wl_Word (a:A word))
        (loop_state_locals (st:(A,FFI)loop_state)))) st`;
     `ctxt:crep_to_loop_context`; `l:num_set`]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [FS[crep_to_loopProof_state_rel_def] THEN
    MATCH_MP_TAC locals_rel_insert_gt_vmax THEN CONJ_TAC THENL
     [MATCH_MP_TAC PC2LAUX_locals_rel_exp_restrict THEN ASM_EXISTS_TAC THEN
      ASM_REWRITE_TAC[];
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  STRIP_TAC THEN
  QCASES_ON "res" THEN CASE_REWRITE_TAC[] THEN RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THENL
   [QEXISTS_TAC "ck + ck' + 1" THEN
    QBY "loop_evaluate (loop_nested_seq np,
           loop_state_clock_fupd (K (loop_state_clock t + ck + ck' + 1)) t) =
         (NONE,loop_state_clock_fupd (K (loop_state_clock st + ck' + 1)) st)"
     (QPAT_X_ASSUM "loop_evaluate (loop_nested_seq np,_) = (NONE,st)"
       (MP_TAC o SPEC `ck' + 1` o
        MATCH_MP (REWRITE_RULE[IMP_CONJ] loop_evaluate_add_clock_eq)) THEN
      SIMP[option_DISTINCT; o_DEF; ADD_ASSOC]);
    QEXISTS_TAC "ck + ck'" THEN
    QBY "loop_evaluate (loop_nested_seq np,
           loop_state_clock_fupd (K (loop_state_clock t + ck + ck')) t) =
         (NONE,loop_state_clock_fupd (K (loop_state_clock st + ck')) st)"
     (QPAT_X_ASSUM "loop_evaluate (loop_nested_seq np,_) = (NONE,st)"
       (MP_TAC o SPEC `ck':num` o
        MATCH_MP (REWRITE_RULE[IMP_CONJ] loop_evaluate_add_clock_eq)) THEN
      SIMP[option_DISTINCT; o_DEF; ADD_ASSOC])] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP evaluate_none_nested_seq_append th]) THEN
  REWRITE_TAC[loop_nested_seq_def] THEN
  ONCE_REWRITE_TAC[loop_evaluate_def] THEN ONCE_REWRITE_TAC[loop_evaluate_def] THEN
  REWRITE_TAC[loop_eval_upd_clock_eq] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[loop_set_var_def] THEN ONCE_REWRITE_TAC[loop_evaluate_def] THEN
  ONCE_REWRITE_TAC[loop_evaluate_def] THEN
  SIMP[lookup_insert; get_var_imm_def; asm_word_cmp_def] THEN CASE_REWRITE_TAC[] THENL
   [QPAT_X_ASSUM "loop_evaluate (crep_to_loop_compile ctxt l _,_) = _"
      (MP_TAC o ONCE_REWRITE_RULE[COND_RAND] o SPEC `1` o
       MATCH_MP (REWRITE_RULE[IMP_CONJ] loop_evaluate_add_clock_eq)) THEN
    REWRITE_TAC[option_DISTINCT] THEN DISCH_TAC THEN SAME_RUN_TAC[] THEN
    QPAT_ASSUM "crep_to_loopProof_locals_rel ctxt l (crep_state_locals s1) _"
      (STRIP_ASSUME_TAC o MATCH_MP crep_to_loopProof_locals_rel_intro) THEN
    SIMP[cut_res_def; cut_state_def; loop_dec_clock_def; ARITH_RULE `~(n + 1 = 0)`] THEN
    CASE_REWRITE_TAC[] THEN SIMP[ADD_SUB] THEN
    FS[crep_to_loopProof_state_rel_def] THEN
    MATCH_MP_TAC PC2LAUX_locals_rel_inter THEN ASM_REWRITE_TAC[];
    QPAT_X_ASSUM "loop_evaluate (crep_to_loop_compile ctxt l _,_) = _"
      (MP_TAC o ONCE_REWRITE_RULE[COND_RAND]) THEN
    DISCH_TAC THEN SAME_RUN_TAC[] THEN
    QCASES_ON "a'" THEN CASE_REWRITE_TAC[] THEN RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
    SIMP[cut_res_def; option_DISTINCT] THEN CASE_REWRITE_TAC[] THEN
    FS[crep_to_loopProof_state_rel_def]]);;

(* local helper: loading bytes from related memories *)

let PC2LAUX_mem_load_byte_rel = prove
 (`!(smem:A word->(A)word_lab) tmem dm be.
     mem_rel smem tmem dm ==>
     mem_load_byte_aux tmem dm be = pan_mem_load_byte smem dm be`,
  REWRITE_TAC[mem_rel_def; FUN_EQ_THM; mem_load_byte_aux_def; pan_mem_load_byte_def] THEN
  REPEAT STRIP_TAC THEN QCASES_ON "smem (byte_align x:A word)" THEN CASE_REWRITE_TAC[] THEN
  ASM_CASES_TAC `byte_align (x:A word) IN dm` THEN ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `byte_align (x:A word)`) THEN
    ASM_REWRITE_TAC[wlab_wloc_def] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[];
    QCASES_ON "tmem (byte_align x:A word)" THEN CASE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[]]);;

(* HOL4: Resume ncompile_correct[ExtCall] *)

let PC2LAUX_ncompile_ExtCall = prove
 (PC2LAUX_ncompile_case "crep_ExtCall",
  RW[] THEN
  FS([crep_evaluate_def; loop_evaluate_def; crep_to_loop_compile_def] @ all_case_eqs()) THEN
  RVEQ_TAC THEN FS[] THEN
  IMP_RES_TAC crep_to_loopProof_locals_rel_intro THEN RES_TAC THEN FS[wlab_wloc_def] THEN
  QEXISTS_TAC "0" THEN ONCE_REWRITE_TAC[loop_evaluate_def] THEN
  FS[crep_to_loopProof_state_rel_def] THEN RFS[] THEN
  FIRST_ASSUM(fun th -> ASSUME_TAC(MATCH_MP PC2LAUX_mem_load_byte_rel th)) THEN
  FS[cut_state_def; ADD_CLAUSES] THEN CASE_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SIMP[PAIR_EQ; call_env_def] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC write_bytearray_mem_rel THEN ASM_MESON_TAC[];
    MATCH_MP_TAC PC2LAUX_locals_rel_inter THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)

(* HOL4 lines 2717-3130: case While                                         *)

(* local helpers for the case While: the tail of the compiled loop body (the *)
(* test of the condition), and the cut at the entry of a loop               *)

let PC2LAUX_while_tail = prove
 (CASE_TERM
  `!tmp le (lp:(A)loop_prog) l (st:(A,FFI)loop_state) w.
     loop_eval st le = SOME (wl_Word w) ==>
     loop_evaluate (loop_nested_seq [loop_Assign tmp le;
         loop_If NotEqual tmp (Imm (word 0)) (loop_Seq lp (loop_Continue 0))
           (loop_Break 0) l], st) =
     (let st1 = loop_state_locals_fupd (K (insert tmp (wl_Word w) (loop_state_locals st))) st in
      if w = word 0 then (SOME (loopSem_Break 0),st1)
      else match loop_evaluate (lp,st1) with
             (NONE,t1) -> (SOME (loopSem_Continue 0),t1)
           | (r,t1) -> (r,t1))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[loop_nested_seq_def] THEN
  ONCE_REWRITE_TAC[loop_evaluate_def] THEN ONCE_REWRITE_TAC[loop_evaluate_def] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[loop_set_var_def] THEN
  ONCE_REWRITE_TAC[loop_evaluate_def] THEN ONCE_REWRITE_TAC[loop_evaluate_def] THEN
  SIMP[lookup_insert; get_var_imm_def; asm_word_cmp_def] THEN CASE_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_CASES_TAC `w = word 0:A word` THEN ASM_REWRITE_TAC[] THENL
   [ONCE_REWRITE_TAC[loop_evaluate_def] THEN REWRITE_TAC[cut_res_def; option_DISTINCT] THEN
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[option_DISTINCT];
    ONCE_REWRITE_TAC[loop_evaluate_def] THEN
    NAMED_CASES_ON "loop_evaluate (lp,loop_state_locals_fupd
      (K (insert tmp (wl_Word w) (loop_state_locals st))) st)" ["r t1"] THEN
    CASE_REWRITE_TAC[] THEN QCASES_ON "r" THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[cut_res_def; option_DISTINCT] THEN
    ONCE_REWRITE_TAC[loop_evaluate_def] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[cut_res_def; option_DISTINCT] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[option_DISTINCT]]);;

let PC2LAUX_loop_entry = prove
 (`!(l:num_set) (s:(A,FFI)loop_state).
     domain l SUBSET domain (loop_state_locals s) ==>
     cut_res l (NONE:((A)loop_result)option,s) =
     if loop_state_clock s = 0
     then (SOME loop_TimeOut,
           loop_state_locals_fupd (K LN)
             (loop_state_locals_fupd (K (inter (loop_state_locals s) l)) s))
     else (NONE,loop_dec_clock
                  (loop_state_locals_fupd (K (inter (loop_state_locals s) l)) s))`,
  SIMP[cut_res_def; cut_state_def] THEN REPEAT STRIP_TAC);;

let PC2LAUX_ONE_BINDER_TAC (ttac:thm_tactic) : tactic =
  FIRST_X_ASSUM(fun th ->
    let vs,b = strip_forall(concl th) in
    if length vs = 1 && is_imp b then ttac th else failwith "PC2LAUX_ONE_BINDER_TAC");;

(* the next-iteration induction hypotheses of the While case, after their   *)
(* premises were simplified with the evaluation of the condition            *)

let PC2LAUX_WHILE_IH_TAC : tactic =
  FIRST_X_ASSUM(fun th -> let vs,_ = strip_forall(concl th) in
    if length vs = 2 && type_of(hd vs) = `:A word` then
      MP_TAC(SPECL [`w:A word`; `s2:(A,FFI)crep_state`] th) else failwith "") THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`res:((A)crep_result)option`; `s1:(A,FFI)crep_state`;
    `t1:(A,FFI)loop_state`; `ctxt:crep_to_loop_context`; `l:num_set`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC;;

(* one iteration that exits the loop: the clock of the expression, then of *)
(* the body                                                                 *)

let PC2LAUX_WHILE_EXIT_TAC : tactic =
  FIRST_X_ASSUM(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM) o
    check (is_conj o concl)) THEN
  QPAT_X_ASSUM "loop_state_clock t = crep_state_clock s" (ASSUME_TAC o SYM) THEN
  QEXISTS_TAC "ck + ck'" THEN
  QBY "loop_evaluate (loop_nested_seq np,
         loop_state_locals_fupd (K (inter (loop_state_locals t) l))
           (loop_state_clock_fupd (K ((loop_state_clock t + ck + ck') - 1)) t)) =
       (NONE,loop_state_clock_fupd (K (loop_state_clock st + ck')) st)"
   (QPAT_X_ASSUM "loop_evaluate (loop_nested_seq np,_) = (NONE,st)"
     (MP_TAC o SPEC `ck':num` o MATCH_MP (REWRITE_RULE[IMP_CONJ] loop_evaluate_add_clock_eq)) THEN
    SIMP[option_DISTINCT] THEN DISCH_TAC THEN SAME_RUN_TAC[]) THEN
  QBY "~(loop_state_clock t + ck + ck' = 0)" ASM_ARITH_TAC THEN
  ONCE_REWRITE_TAC[loop_evaluate_def] THEN
  SIMP[PC2LAUX_loop_entry; loop_dec_clock_def] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP evaluate_none_nested_seq_append th]) THEN
  SUBGOAL_THEN `loop_eval (loop_state_clock_fupd (K (loop_state_clock st + ck'))
                  (st:(A,FFI)loop_state)) le = SOME (wl_Word (w:A word))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[loop_eval_upd_clock_eq; GSYM wlab_wloc_def]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP PC2LAUX_while_tail th]) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[] THEN SAME_RUN_TAC[] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  SIMP[crep_exit_loop_def; loop_exit_loop_def] THEN CASE_REWRITE_TAC[] THEN
  FS[crep_to_loopProof_state_rel_def];;

(* one iteration that continues the loop (the body returns NONE or         *)
(* Continue 0): then the loop run of the next-iteration hypothesis          *)

let PC2LAUX_WHILE_NEXT_TAC : tactic =
  QEXISTS_TAC "ck + ck' + ck''" THEN
  QBY "loop_evaluate (loop_nested_seq np,
         loop_state_locals_fupd (K (inter (loop_state_locals t) l))
           (loop_state_clock_fupd (K ((loop_state_clock t + ck + ck' + ck'') - 1)) t)) =
       (NONE,loop_state_clock_fupd (K (loop_state_clock st + ck' + ck'')) st)"
   (QPAT_X_ASSUM "loop_evaluate (loop_nested_seq np,_) = (NONE,st)"
     (MP_TAC o SPEC `ck' + ck''` o
      MATCH_MP (REWRITE_RULE[IMP_CONJ] loop_evaluate_add_clock_eq)) THEN
    SIMP[option_DISTINCT] THEN DISCH_TAC THEN SAME_RUN_TAC[]) THEN
  QPAT_X_ASSUM "loop_state_clock t = crep_state_clock s" (ASSUME_TAC o SYM) THEN
  QBY "~(loop_state_clock t + ck + ck' + ck'' = 0)" ASM_ARITH_TAC THEN
  ONCE_REWRITE_TAC[loop_evaluate_def] THEN
  SIMP[PC2LAUX_loop_entry; loop_dec_clock_def] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP evaluate_none_nested_seq_append th]) THEN
  SUBGOAL_THEN `loop_eval (loop_state_clock_fupd (K (loop_state_clock st + ck' + ck''))
                  (st:(A,FFI)loop_state)) le = SOME (wl_Word (w:A word))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[loop_eval_upd_clock_eq; GSYM wlab_wloc_def]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP PC2LAUX_while_tail th]) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[] THEN
  QPAT_X_ASSUM "loop_evaluate (crep_to_loop_compile ctxt l c,_) = _"
    (MP_TAC o SPEC `ck'':num` o MATCH_MP (REWRITE_RULE[IMP_CONJ] loop_evaluate_add_clock_eq)) THEN
  ASM_REWRITE_TAC[option_DISTINCT] THEN
  SIMP[option_DISTINCT] THEN DISCH_TAC THEN SAME_RUN_TAC[] THEN
  CASE_REWRITE_TAC[] THEN
  QPAT_X_ASSUM "loop_evaluate (crep_to_loop_compile ctxt l (crep_While e c),_) = _"
    (MP_TAC o REWRITE_RULE[crep_to_loop_compile_def]) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN ASM_REWRITE_TAC[];;

(* HOL4: Resume ncompile_correct[While] *)

let PC2LAUX_ncompile_While = prove
 (PC2LAUX_ncompile_case "crep_While",
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  QPAT_X_ASSUM "crep_evaluate (crep_While e c,s) = (res,s1)" MP_TAC THEN
  ONCE_REWRITE_TAC[crep_evaluate_def] THEN
  QCASES_ON "crep_eval s e" THEN CASE_REWRITE_TAC[] THENL
   [ASM_MESON_TAC[PAIR_EQ]; ALL_TAC] THEN
  QCASES_ON "a" THEN CASE_REWRITE_TAC[] THEN RENAME1 "crep_eval s e = SOME (Word w)" THEN
  REWRITE_TAC[crep_to_loop_compile_def] THEN
  NAMED_CASES_ON "crep_to_loop_compile_exp ctxt (crep_to_loop_context_vmax ctxt + 1) l e"
    ["np le tmp nl"] THEN CASE_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  QPAT_ASSUM "crep_to_loopProof_locals_rel ctxt l _ _"
    (STRIP_ASSUME_TAC o MATCH_MP crep_to_loopProof_locals_rel_intro) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP compile_exp_out_rel) THEN
  ASM_CASES_TAC `w = word 0:A word` THEN ASM_REWRITE_TAC[] THENL
   [(* the condition is false: one test of the condition, then the exit *)
    REWRITE_TAC[PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) THEN
    MP_TAC(ISPECL [`s:(A,FFI)crep_state`; `e:(A)crep_exp`; `Word (w:A word)`;
       `loop_state_locals_fupd (K (inter (loop_state_locals (t:(A,FFI)loop_state))
          (l:num_set))) t`;
       `ctxt:crep_to_loop_context`; `crep_to_loop_context_vmax ctxt + 1`; `l:num_set`;
       `np:((A)loop_prog)list`; `le:(A)loop_exp`; `tmp:num`; `nl:num_set`]
       crep_to_loopProof_comp_exp_preserves_eval) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[ARITH_RULE `n < n + 1`] THEN FS[crep_to_loopProof_state_rel_def] THEN
      MATCH_MP_TAC PC2LAUX_locals_rel_inter THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    STRIP_TAC THEN QEXISTS_TAC "ck + 2" THEN
    QPAT_X_ASSUM "loop_evaluate (loop_nested_seq np,_) = (NONE,st)"
      (MP_TAC o SPEC `1` o MATCH_MP (REWRITE_RULE[IMP_CONJ] loop_evaluate_add_clock_eq)) THEN
    SIMP[option_DISTINCT] THEN DISCH_TAC THEN
    ONCE_REWRITE_TAC[loop_evaluate_def] THEN
    SIMP[PC2LAUX_loop_entry] THEN
    SIMP[ARITH_RULE `~(c + ck + 2 = 0)`; loop_dec_clock_def] THEN
    REWRITE_TAC[ARITH_RULE `(a + b + 2) - 1 = (a + b) + 1`] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP evaluate_none_nested_seq_append th]) THEN
    SUBGOAL_THEN `loop_eval (loop_state_clock_fupd (K (loop_state_clock st + 1))
                    (st:(A,FFI)loop_state)) le = SOME (wl_Word (w:A word))` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[loop_eval_upd_clock_eq; wlab_wloc_def]; ALL_TAC] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP PC2LAUX_while_tail th]) THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    SUBGOAL_THEN `domain (l:num_set) SUBSET domain (loop_state_locals (st:(A,FFI)loop_state))`
      ASSUME_TAC THENL
     [QPAT_ASSUM "crep_to_loopProof_locals_rel ctxt nl _ _"
        (STRIP_ASSUME_TAC o MATCH_MP crep_to_loopProof_locals_rel_intro) THEN
      ASM_MESON_TAC[cut_sets_union_domain_subset; SUBSET_TRANS];
      ALL_TAC] THEN
    SIMP[PC2LAUX_loop_entry; domain_insert] THEN
    SUBGOAL_THEN `domain (l:num_set) SUBSET
                  tmp INSERT domain (loop_state_locals (st:(A,FFI)loop_state))`
      ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SIMP[PC2LAUX_loop_entry; domain_insert; ARITH_RULE `~(n + 1 = 0)`; loop_dec_clock_def] THEN
    CONJ_TAC THENL
     [FS[crep_to_loopProof_state_rel_def];
      MATCH_MP_TAC PC2LAUX_locals_rel_inter THEN
      MATCH_MP_TAC locals_rel_insert_gt_vmax THEN CONJ_TAC THENL
       [MATCH_MP_TAC PC2LAUX_locals_rel_exp_restrict THEN ASM_EXISTS_TAC THEN
        ASM_REWRITE_TAC[] THEN
        EXISTS_TAC `inter (loop_state_locals (t:(A,FFI)loop_state)) (l:num_set)` THEN
        MATCH_MP_TAC PC2LAUX_locals_rel_inter THEN ASM_REWRITE_TAC[];
        ASM_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `loop_state_clock (t:(A,FFI)loop_state) = crep_state_clock (s:(A,FFI)crep_state)`
    ASSUME_TAC THENL [ASM_MESON_TAC[crep_to_loopProof_state_rel_def]; ALL_TAC] THEN
  ASM_CASES_TAC `crep_state_clock (s:(A,FFI)crep_state) = 0` THEN ASM_REWRITE_TAC[] THENL
   [(* out of clock at the entry of the loop *)
    REWRITE_TAC[PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) THEN
    QEXISTS_TAC "0" THEN ONCE_REWRITE_TAC[loop_evaluate_def] THEN
    SIMP[PC2LAUX_loop_entry] THEN CASE_REWRITE_TAC[] THEN
    FS[crep_to_loopProof_state_rel_def; crep_empty_locals_def];
    ALL_TAC] THEN
  (* the body is run *)
  NAMED_CASES_ON "crep_evaluate (c,crep_dec_clock s)" ["r s2"] THEN CASE_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`crep_dec_clock (s:(A,FFI)crep_state)`; `e:(A)crep_exp`; `Word (w:A word)`;
     `loop_state_clock_fupd (K (loop_state_clock t - 1))
        (loop_state_locals_fupd (K (inter (loop_state_locals (t:(A,FFI)loop_state))
           (l:num_set))) t)`;
     `ctxt:crep_to_loop_context`; `crep_to_loop_context_vmax ctxt + 1`; `l:num_set`;
     `np:((A)loop_prog)list`; `le:(A)loop_exp`; `tmp:num`; `nl:num_set`]
     crep_to_loopProof_comp_exp_preserves_eval) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[ARITH_RULE `n < n + 1`; crep_dec_clock_def; crep_eval_upd_clock_eq] THEN
    FS[crep_to_loopProof_state_rel_def] THEN
    MATCH_MP_TAC PC2LAUX_locals_rel_inter THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN
  PC2LAUX_ONE_BINDER_TAC(MP_TAC o SPEC `w:A word`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`r:((A)crep_result)option`; `s2:(A,FFI)crep_state`;
     `loop_state_locals_fupd (K (insert tmp (wl_Word (w:A word))
        (loop_state_locals (st:(A,FFI)loop_state)))) st`;
     `ctxt:crep_to_loop_context`; `l:num_set`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(LABEL_TAC "ihb") THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(r = SOME (crep_Error:(A)crep_result))` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN FS[crep_exit_loop_def]; ALL_TAC] THEN
  REMOVE_THEN "ihb" MP_TAC THEN ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [FS[crep_to_loopProof_state_rel_def; crep_dec_clock_def] THEN
    MATCH_MP_TAC locals_rel_insert_gt_vmax THEN CONJ_TAC THENL
     [MATCH_MP_TAC PC2LAUX_locals_rel_exp_restrict THEN ASM_EXISTS_TAC THEN
      ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `inter (loop_state_locals (t:(A,FFI)loop_state)) (l:num_set)` THEN
      MATCH_MP_TAC PC2LAUX_locals_rel_inter THEN ASM_REWRITE_TAC[];
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  STRIP_TAC THEN
  QCASES_ON "r" THEN CASE_REWRITE_TAC[] THEN RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THENL
   [(* the body ends normally: the next iteration *)
    FIRST_X_ASSUM SUBST_ALL_TAC THEN PC2LAUX_WHILE_IH_TAC THEN PC2LAUX_WHILE_NEXT_TAC;
    ALL_TAC] THEN
  QCASES_ON "a''" THEN CASE_REWRITE_TAC[] THEN RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THENL
   [FS[crep_exit_loop_def];
    PC2LAUX_WHILE_EXIT_TAC;
    ASM_CASES_TAC `a''' = 0` THEN
    QPAT_X_ASSUM "(if _ then _ else _) = (res,s1)" MP_TAC THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
    DISCH_TAC THENL
     [(* Break 0: the exit of the loop, one more tick for its cut *)
      FIRST_X_ASSUM(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM) o
        check (is_conj o concl)) THEN
      QPAT_X_ASSUM "loop_state_clock t = crep_state_clock s" (ASSUME_TAC o SYM) THEN
      QEXISTS_TAC "ck + ck' + 1" THEN
      QBY "loop_evaluate (loop_nested_seq np,
             loop_state_locals_fupd (K (inter (loop_state_locals t) l))
               (loop_state_clock_fupd (K ((loop_state_clock t + ck + ck' + 1) - 1)) t)) =
           (NONE,loop_state_clock_fupd (K (loop_state_clock st + ck' + 1)) st)"
       (QPAT_X_ASSUM "loop_evaluate (loop_nested_seq np,_) = (NONE,st)"
         (MP_TAC o SPEC `ck' + 1` o
          MATCH_MP (REWRITE_RULE[IMP_CONJ] loop_evaluate_add_clock_eq)) THEN
        SIMP[option_DISTINCT] THEN DISCH_TAC THEN SAME_RUN_TAC[]) THEN
      QBY "~(loop_state_clock t + ck + ck' + 1 = 0)" ASM_ARITH_TAC THEN
      ONCE_REWRITE_TAC[loop_evaluate_def] THEN
      SIMP[PC2LAUX_loop_entry; loop_dec_clock_def] THEN
      FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP evaluate_none_nested_seq_append th]) THEN
      SUBGOAL_THEN `loop_eval (loop_state_clock_fupd (K (loop_state_clock st + ck' + 1))
                      (st:(A,FFI)loop_state)) le = SOME (wl_Word (w:A word))`
        ASSUME_TAC THENL
       [ASM_REWRITE_TAC[loop_eval_upd_clock_eq; GSYM wlab_wloc_def]; ALL_TAC] THEN
      FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP PC2LAUX_while_tail th]) THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[] THEN
      QPAT_X_ASSUM "loop_evaluate (crep_to_loop_compile ctxt l c,_) = _"
        (MP_TAC o SPEC `1` o MATCH_MP (REWRITE_RULE[IMP_CONJ] loop_evaluate_add_clock_eq)) THEN
      ASM_REWRITE_TAC[option_DISTINCT; option_INJ; GSYM CONJ_ASSOC] THEN
      SIMP[option_DISTINCT] THEN DISCH_TAC THEN SAME_RUN_TAC[] THEN
      CASE_REWRITE_TAC[] THEN
      QPAT_ASSUM "crep_to_loopProof_locals_rel ctxt l (crep_state_locals s2) _"
        (STRIP_ASSUME_TAC o MATCH_MP crep_to_loopProof_locals_rel_intro) THEN
      SIMP[PC2LAUX_loop_entry; loop_dec_clock_def; ARITH_RULE `~(n + 1 = 0)`; ADD_SUB] THEN
      FS[crep_to_loopProof_state_rel_def] THEN
      MATCH_MP_TAC PC2LAUX_locals_rel_inter THEN ASM_REWRITE_TAC[];
      PC2LAUX_WHILE_EXIT_TAC];
    ASM_CASES_TAC `a''' = 0` THEN
    QPAT_X_ASSUM "(if _ then _ else _) = (res,s1)" MP_TAC THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
    DISCH_TAC THENL
     [(* Continue 0: the next iteration *)
      PC2LAUX_WHILE_IH_TAC THEN PC2LAUX_WHILE_NEXT_TAC;
      PC2LAUX_WHILE_EXIT_TAC];
    PC2LAUX_WHILE_EXIT_TAC;
    PC2LAUX_WHILE_EXIT_TAC;
    PC2LAUX_WHILE_EXIT_TAC]);;

(* ------------------------------------------------------------------------- *)

(* HOL4 lines 3133-3715: call_preserve_state_code_locals_rel ..           *)
(* all_distinct_ctxt_lookup_all_distinct; case Call                         *)

let PC2LAUX_ctxt_accessors = (record_info "crep_to_loop_context").ri_accessors;;

let crep_to_loopProof_call_preserve_state_code_locals_rel = prove
 (`!ns lns args (s:(A,FFI)crep_state) (st:(A,FFI)loop_state) ctxt nl fname argexps prog loc.
     ALL_DISTINCT ns /\ ALL_DISTINCT lns /\
     LENGTH ns = LENGTH lns /\ LENGTH args = LENGTH lns /\
     crep_to_loopProof_state_rel s st /\
     mem_rel (crep_state_memory s) (loop_state_memory st) (crep_state_memaddrs s) /\
     crep_to_loopProof_globals_rel (crep_state_globals s) (loop_state_globals st) /\
     crep_to_loopProof_code_rel ctxt (crep_state_code s) (loop_state_code st) /\
     crep_to_loopProof_locals_rel ctxt nl (crep_state_locals s) (loop_state_locals st) /\
     FLOOKUP (crep_state_code s) fname = SOME (ns,prog) /\
     FLOOKUP (crep_to_loop_context_funcs ctxt) fname = SOME (loc,LENGTH lns) /\
     MAP (crep_eval s) argexps = MAP SOME args ==>
     (let nctxt = crep_to_loopProof_ctxt_fc (crep_to_loop_context_target ctxt)
                    (crep_to_loop_context_funcs ctxt) ns lns in
      crep_to_loopProof_state_rel
        (crep_state_clock_fupd (K (crep_state_clock s - 1))
           (crep_state_locals_fupd (K (FEMPTY |++ ZIP ns args)) s))
        (loop_state_clock_fupd (K (loop_state_clock st - 1))
           (loop_state_locals_fupd (K (fromAList (ZIP lns (MAP wlab_wloc args)))) st)) /\
      crep_to_loopProof_code_rel nctxt (crep_state_code s) (loop_state_code st) /\
      crep_to_loopProof_locals_rel nctxt (list_to_num_set lns) (FEMPTY |++ ZIP ns args)
        (fromAList (ZIP lns (MAP wlab_wloc args))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[crep_to_loopProof_ctxt_fc_def] THEN REPEAT CONJ_TAC THENL
   [FS[crep_to_loopProof_state_rel_def];
    QPAT_X_ASSUM "crep_to_loopProof_code_rel _ _ _" MP_TAC THEN
    REWRITE_TAC[crep_to_loopProof_code_rel_def; PC2LAUX_ctxt_accessors];
    ALL_TAC] THEN
  REWRITE_TAC[crep_to_loopProof_locals_rel_def; PC2LAUX_ctxt_accessors; distinct_vars_def;
              crep_to_loopProof_ctxt_max_def] THEN REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`ns:num list`; `lns:num list`; `x:num`; `n:num`] fm_empty_zip_flookup) THEN
    MP_TAC(ISPECL [`ns:num list`; `lns:num list`; `y:num`; `m:num`] fm_empty_zip_flookup) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `EL i (ns:num list) = x /\ EL i (lns:num list) = m /\
                  EL j ns = y /\ EL j lns = m` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[EL_ZIP; PAIR_EQ]; ALL_TAC] THEN
    SUBGOAL_THEN `i = j:num` (fun th -> ASM_MESON_TAC[th]) THEN
    ASM_MESON_TAC[ALL_DISTINCT_EL_IMP];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MAX_LIST_PROPERTY THEN
    MP_TAC(ISPECL [`ns:num list`; `lns:num list`; `v:num`; `m:num`] fm_empty_zip_flookup) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `EL i (lns:num list) = m` (SUBST1_TAC o SYM) THENL
     [ASM_MESON_TAC[EL_ZIP; PAIR_EQ]; ASM_MESON_TAC[MEM_EL]];
    REWRITE_TAC[SUBSET; domain_list_to_num_set; domain_fromAList] THEN
    ASM_SIMP_TAC[MAP_FST_ZIP; LENGTH_MAP; IN_SET_OF_LIST];
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`ns:num list`; `args:((A)word_lab)list`; `vname:num`; `v:(A)word_lab`]
      fm_empty_zip_flookup) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`ns:num list`; `args:((A)word_lab)list`; `i:num`] EL_ZIP) THEN
    ASM_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
    QEXISTS_TAC "EL i lns" THEN REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC update_eq_zip_flookup THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[domain_list_to_num_set] THEN MATCH_MP_TAC MEM_EL THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[lookup_fromAList] THEN
      MP_TAC(ISPECL [`ZIP (lns:num list) (MAP wlab_wloc (args:((A)word_lab)list))`; `i:num`]
        ALOOKUP_ALL_DISTINCT_EL) THEN
      ASM_SIMP_TAC[MAP_FST_ZIP; LENGTH_ZIP; LENGTH_MAP; EL_ZIP; EL_MAP]]]);;

let evaluate_none_nested_seq_append_eq = prove
 (`loop_evaluate (loop_nested_seq p,(s:(A,FFI)loop_state)) = (NONE,s1) /\
   loop_evaluate (loop_nested_seq q,s1) = res_s
   ==> loop_evaluate (loop_nested_seq (APPEND p q),s) = res_s`,
  RW[] THEN ASM_SIMP_TAC[evaluate_none_nested_seq_append]);;

let find_code_collapse_cases = prove
 (CASE_TERM
  `(~(dest = NONE) ==> dest = SOME loc) ==>
   find_code dest
     (APPEND args1 (TAKE (match dest with NONE -> 1 | SOME _ -> 0) [wl_Loc loc 0]))
     (loop_state_code (st:(A,FFI)loop_state)) =
   (match lookup loc (loop_state_code st) with
      NONE -> NONE
    | SOME (params,exp) ->
        if LENGTH args1 = LENGTH params
        then SOME (fromAList (ZIP params args1),exp)
        else NONE)`,
  QCASES_ON "dest" THEN FS[find_code_def; FRONT_APPEND]);;

let OPT_MMAP_APPEND = prove
 (`OPT_MMAP (f:A->B option) (APPEND xs ys) =
   OPTION_BIND (OPT_MMAP f xs)
     (\xsv. OPTION_BIND (OPT_MMAP f ys) (\ysv. SOME (APPEND xsv ysv)))`,
  QINDUCT_ON "xs" THEN SIMP[OPT_MMAP_def; APPEND] THEN REPEAT STRIP_TAC THEN
  TRY(QCASES_ON "f (a0:A):B option") THEN
  TRY(QCASES_ON "OPT_MMAP (f:A->B option) a1") THEN
  QCASES_ON "OPT_MMAP (f:A->B option) ys" THEN SIMP[OPTION_BIND_DEF]);;

let case_le = prove
 (CASE_TERM `(match (dest:A option) with NONE -> 1 | SOME v1 -> 0) <= 1`,
  QCASES_ON "dest" THEN CASE_REWRITE_TAC[] THEN ARITH_TAC);;

let crep_eval_upd_clock = prove
 (`crep_eval (crep_state_clock_fupd (K v) s) = crep_eval (s:(A,FFI)crep_state)`,
  SIMP[FUN_EQ_THM; crep_eval_upd_clock_eq]);;

let loop_eval_upd_clock = prove
 (`loop_eval (loop_state_clock_fupd (K v) s) = loop_eval (s:(A,FFI)loop_state)`,
  SIMP[FUN_EQ_THM; loop_eval_upd_clock_eq]);;

let UNCURRY_eq_case = prove
 (CASE_TERM `UNCURRY (f:A->B->C) x = (match x with (a,b) -> f a b)`,
  PAIR_CASES_ON `x:A#B` THEN REWRITE_TAC[UNCURRY_DEF] THEN CASE_REWRITE_TAC[]);;

let locals_rel_lookup_same = prove
 (`crep_to_loopProof_locals_rel ctxt l locs1 (locs2:((A)word_loc)spt) ==>
   (!n. lookup n locs2 = lookup n locs3) ==>
   crep_to_loopProof_locals_rel ctxt l locs1 locs3`,
  SIMP[crep_to_loopProof_locals_rel_def; SUBSET; domain_lookup] THEN
  MESON_TAC[]);;

let locals_rel_inter_helper = prove
 (`crep_to_loopProof_locals_rel ctxt l locs1 (locs2:((A)word_loc)spt) ==>
   ALL (\i. lookup i l = NONE) xs ==>
   LENGTH xs = LENGTH ys ==>
   crep_to_loopProof_locals_rel ctxt l locs1 (inter (alist_insert xs ys locs2) l)`,
  SIMP[crep_to_loopProof_locals_rel_def; SUBSET; domain_lookup; lookup_inter;
       lookup_alist_insert] THEN
  RW[] THENL
   [QCASES_ON "ALOOKUP (ZIP xs ys) x" THEN CASE_REWRITE_TAC[] THENL
     [QPAT_X_ASSUM "!x. (?v. lookup x l = SOME v) ==> _" (MP_TAC o SPEC `x:num`) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
      CASE_REWRITE_TAC[] THEN MESON_TAC[];
      MESON_TAC[]];
    FIRST_X_ASSUM(MP_TAC o SPECL [`vname:num`; `v:(A)word_lab`]) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN QEXISTS_TAC "n" THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    QBY "ALOOKUP (ZIP xs ys) n = NONE"
     (ASM_SIMP_TAC[ALOOKUP_NONE; MAP_FST_ZIP] THEN
      QPAT_X_ASSUM "ALL _ xs" (MP_TAC o REWRITE_RULE[GSYM ALL_MEM]) THEN
      REWRITE_TAC[] THEN DISCH_THEN(fun th -> DISCH_THEN(MP_TAC o MATCH_MP th)) THEN
      ASM_REWRITE_TAC[option_DISTINCT]) THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]]);;

let all_distinct_ctxt_lookup_all_distinct = prove
 (`ALL_DISTINCT rts /\ distinct_vars (crep_to_loop_context_vars ctxt) ==>
   ALL_DISTINCT (rt_vars (crep_to_loop_context_vars ctxt) rts n)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rt_vars_def] THEN
  QCASES_ON "OPT_MMAP (FLOOKUP (crep_to_loop_context_vars ctxt)) rts" THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[ALL_DISTINCT; MEM] THEN
  MATCH_MP_TAC (ISPEC `SOME:num->num option` ALL_DISTINCT_MAP) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(REWRITE_RULE[opt_mmap_eq_some] th)]) THEN
  MATCH_MP_TAC ALL_DISTINCT_MAP_INJ THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `x:num` o MATCH_MP (REWRITE_RULE[IMP_CONJ] opt_mmap_mem_func)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  QPAT_X_ASSUM "distinct_vars _" (MP_TAC o REWRITE_RULE[distinct_vars_def]) THEN
  ASM_MESON_TAC[]);;

let PC2LAUX_call_prefix = prove
 (`!p nargs les (c:(A)loop_prog) (s0:(A,FFI)loop_state) st ev.
     loop_evaluate (loop_nested_seq p,s0) = (NONE,st) /\
     MAP (loop_eval st) les = MAP SOME ev /\
     distinct_lists nargs (FLAT (MAP locals_touched les)) /\ ALL_DISTINCT nargs /\
     LENGTH nargs = LENGTH les ==>
     loop_evaluate (loop_nested_seq (APPEND (APPEND p (MAP2 loop_Assign nargs les)) [c]),s0) =
     loop_evaluate (c,loop_state_locals_fupd
                        (K (alist_insert nargs ev (loop_state_locals st))) st)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP evaluate_none_nested_seq_append th]) THEN
  MP_TAC(ISPECL [`les:((A)loop_exp)list`; `nargs:num list`; `st:(A,FFI)loop_state`;
    `ev:((A)word_loc)list`] loop_eval_nested_assign_distinct_eq) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP evaluate_none_nested_seq_append th]) THEN
  REWRITE_TAC[loop_nested_seq_def] THEN ONCE_REWRITE_TAC[loop_evaluate_def] THEN
  NAMED_CASES_ON "loop_evaluate (c:(A)loop_prog,loop_state_locals_fupd
    (K (alist_insert nargs ev (loop_state_locals st))) st)" ["r s1"] THEN
  CASE_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[loop_evaluate_def] THEN REWRITE_TAC[]);;

(* the common part of the Call case: the arguments, the code of the callee *)

let PC2LAUX_CALL_COMMON_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ihc") (LABEL_TAC "ihh")) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  QPAT_X_ASSUM "crep_evaluate (crep_Call caltyp fname argexps,s) = (res,s1)" MP_TAC THEN
  ONCE_REWRITE_TAC[crep_evaluate_def] THEN REWRITE_TAC[crep_lookup_code_def] THEN
  NAMED_CASES_ON "OPT_MMAP (crep_eval s) argexps" ["";"args"] THEN CASE_REWRITE_TAC[] THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  NAMED_CASES_ON "FLOOKUP (crep_state_code s) fname" ["";"np"] THEN CASE_REWRITE_TAC[] THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  NAMED_CASES_ON "np" ["ns prog"] THEN CASE_REWRITE_TAC[] THEN
  ASM_CASES_TAC `LENGTH (ns:num list) = LENGTH (args:((A)word_lab)list) /\ ALL_DISTINCT ns` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  FIRST_X_ASSUM STRIP_ASSUME_TAC THEN
  ASM_CASES_TAC (CASE_TERM
    `(match (caltyp:((num list)#((A word#(A)crep_prog)option))option) with
        NONE -> F
      | SOME (rts,y) -> ~ALL_DISTINCT rts):bool`) THEN
  ASM_REWRITE_TAC[] THENL [ASM_MESON_TAC[PAIR_EQ]; ALL_TAC] THEN
  REWRITE_TAC[crep_to_loop_compile_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  NAMED_CASES_ON "crep_to_loop_compile_exps ctxt (crep_to_loop_context_vmax ctxt + 1) l argexps"
    ["p les tmp nl"] THEN CASE_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  MP_TAC(ISPECL [`argexps:((A)crep_exp)list`; `s:(A,FFI)crep_state`; `args:((A)word_lab)list`;
     `t:(A,FFI)loop_state`; `ctxt:crep_to_loop_context`; `crep_to_loop_context_vmax ctxt + 1`;
     `l:num_set`; `p:((A)loop_prog)list`; `les:((A)loop_exp)list`; `tmp:num`; `nl:num_set`]
     comp_exps_preserves_eval) THEN
  ASM_REWRITE_TAC[ARITH_RULE `n < n + 1`] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP compile_exps_out_rel) THEN
  SUBGOAL_THEN `distinct_lists (gen_temps tmp (LENGTH (les:((A)loop_exp)list)))
                  (FLAT (MAP locals_touched les)) /\
                ALL_DISTINCT (gen_temps tmp (LENGTH les)) /\
                LENGTH (gen_temps tmp (LENGTH les)) = LENGTH les /\
                MAP (loop_eval (st:(A,FFI)loop_state)) les = MAP SOME (MAP wlab_wloc args)`
    STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[gen_temps_def; LENGTH_LIST_OF_SEQ] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[distinct_lists_def; GSYM ALL_MEM; MEM_GENLIST] THEN
      REPEAT STRIP_TAC THEN
      QPAT_ASSUM "crep_to_loopProof_locals_rel ctxt l _ _"
        (STRIP_ASSUME_TAC o MATCH_MP crep_to_loopProof_locals_rel_intro) THEN
      MP_TAC(ISPECL [`ctxt:crep_to_loop_context`; `crep_to_loop_context_vmax ctxt + 1`;
        `l:num_set`; `argexps:((A)crep_exp)list`; `p:((A)loop_prog)list`;
        `les:((A)loop_exp)list`; `tmp:num`; `nl:num_set`; `x:num`]
        compile_exps_le_tmp_domain) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[ARITH_RULE `n < n + 1`] THEN REPEAT STRIP_TAC THEN
        MP_TAC(ISPECL [`s:(A,FFI)crep_state`; `argexps:((A)crep_exp)list`;
          `args:((A)word_lab)list`; `n:num`] opt_mmap_eval_some_var_cexp_local_lookup) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_MESON_TAC[];
        ASM_ARITH_TAC];
      REWRITE_TAC[ALL_DISTINCT_GENLIST] THEN ARITH_TAC;
      ASM_MESON_TAC[opt_mmap_eq_some]];
    ALL_TAC] THEN
  QPAT_ASSUM "crep_to_loopProof_code_rel ctxt (crep_state_code s) (loop_state_code st)"
    (MP_TAC o CONJUNCT2 o REWRITE_RULE[crep_to_loopProof_code_rel_def]) THEN
  DISCH_THEN(MP_TAC o SPECL [`fname:mlstring`; `ns:num list`; `prog:(A)crep_prog`]) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN `loc:num` (X_CHOOSE_THEN `len:num` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `crep_to_loop_find_lab ctxt fname = loc` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[crep_to_loop_find_lab_def] THEN CASE_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[];;

(* the arguments of a call: the code of the expressions, then the          *)
(* assignments of the temporaries, at the clock of the state stt           *)

let PC2LAUX_CALL_PREFIX_CK_TAC (stt:term) : tactic =
  SUBST1_TAC (SYM (ASSUME
    `LENGTH (les:((A)loop_exp)list) = LENGTH (argexps:((A)crep_exp)list)`)) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP PC2LAUX_call_prefix (end_itlist CONJ
    [th; ASSUME (subst [stt,`stt:(A,FFI)loop_state`]
       `MAP (loop_eval (stt:(A,FFI)loop_state)) (les:((A)loop_exp)list) =
        MAP SOME (MAP wlab_wloc (args:((A)word_lab)list))`);
     ASSUME `distinct_lists (gen_temps tmp (LENGTH (les:((A)loop_exp)list)))
               (FLAT (MAP locals_touched les))`;
     ASSUME `ALL_DISTINCT (gen_temps tmp (LENGTH (les:((A)loop_exp)list)))`;
     ASSUME `LENGTH (gen_temps tmp (LENGTH (les:((A)loop_exp)list))) = LENGTH les`])]);;

(* the call: its arguments are the temporaries, its code is found at loc  *)

let PC2LAUX_CALL_FIND_TAC (stt:term) : tactic =
  ONCE_REWRITE_TAC[loop_evaluate_def] THEN
  SUBGOAL_THEN (subst [stt,`stt:(A,FFI)loop_state`]
    `get_vars (gen_temps tmp (LENGTH (les:((A)loop_exp)list)))
       (loop_state_locals_fupd (K (alist_insert (gen_temps tmp (LENGTH les))
          (MAP wlab_wloc (args:((A)word_lab)list)) (loop_state_locals (stt:(A,FFI)loop_state))))
          stt) = SOME (MAP wlab_wloc args)`) SUBST1_TAC THENL
   [MATCH_MP_TAC get_vars_local_update_some_eq THEN ASM_REWRITE_TAC[LENGTH_MAP] THEN
    MP_TAC(MATCH_MP opt_mmap_length_eq
      (ASSUME `OPT_MMAP (crep_eval (s:(A,FFI)crep_state)) argexps =
               SOME (args:((A)word_lab)list)`)) THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  CASE_REWRITE_TAC[] THEN SIMP[find_code_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[];;

(* a result of the callee of a tail call *)

let PC2LAUX_TAILCALL_RES_TAC : tactic =
  QPAT_X_ASSUM "loop_evaluate (crep_to_loop_compile _ _ prog,_) = _"
    (MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] loop_liveProof_optimise_correct)) THEN
  ASM_REWRITE_TAC[option_DISTINCT; option_INJ; distinctness "loop_result"] THEN
  DISCH_TAC THEN QEXISTS_TAC "ck + ck'" THEN
  QBY "loop_evaluate (loop_nested_seq p,
         loop_state_clock_fupd (K (loop_state_clock t + ck + ck')) t) =
       (NONE,loop_state_clock_fupd (K (loop_state_clock st + ck')) st)"
   (QPAT_X_ASSUM "loop_evaluate (loop_nested_seq p,_) = (NONE,st)"
     (MP_TAC o SPEC `ck':num` o MATCH_MP (REWRITE_RULE[IMP_CONJ] loop_evaluate_add_clock_eq)) THEN
    SIMP[option_DISTINCT; ADD_ASSOC]) THEN
  SUBGOAL_THEN `MAP (loop_eval (loop_state_clock_fupd (K (loop_state_clock st + ck'))
                  (st:(A,FFI)loop_state))) les = MAP SOME (MAP wlab_wloc (args:((A)word_lab)list))`
    ASSUME_TAC THENL [ASM_REWRITE_TAC[loop_eval_upd_clock]; ALL_TAC] THEN
  PC2LAUX_CALL_PREFIX_CK_TAC
    `loop_state_clock_fupd (K (loop_state_clock st + ck')) (st:(A,FFI)loop_state)` THEN
  PC2LAUX_CALL_FIND_TAC
    `loop_state_clock_fupd (K (loop_state_clock st + ck')) (st:(A,FFI)loop_state)` THEN
  SUBGOAL_THEN `~(loop_state_clock (st:(A,FFI)loop_state) = 0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[crep_to_loopProof_state_rel_def]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[ocompile_def; o_THM; loop_dec_clock_def] THEN
  SAME_RUN_TAC[] THEN CASE_REWRITE_TAC[] THEN
  QPAT_X_ASSUM "crep_to_loopProof_code_rel (crep_to_loopProof_ctxt_fc _ _ _ _) _ _" MP_TAC THEN
  REWRITE_TAC[crep_to_loopProof_code_rel_def; crep_to_loopProof_ctxt_fc_def;
              PC2LAUX_ctxt_accessors] THEN
  DISCH_TAC THEN
  FS[crep_to_loopProof_state_rel_def; crep_empty_locals_def; crep_to_loopProof_code_rel_def] THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq(concl th) &&
    is_var(rhs(concl th)) && mem (fst(dest_var(rhs(concl th)))) ["res";"s1"]))) THEN
  FS[crep_empty_locals_def];;

(* the tail call: caltyp = NONE *)

let PC2LAUX_CALL_NONE_TAC : tactic =
  ASM_CASES_TAC `crep_state_clock (s:(A,FFI)crep_state) = 0` THEN ASM_REWRITE_TAC[] THENL
   [(* out of clock at the call *)
    REWRITE_TAC[PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) THEN
    QEXISTS_TAC "ck" THEN
    PC2LAUX_CALL_PREFIX_CK_TAC `st:(A,FFI)loop_state` THEN
    PC2LAUX_CALL_FIND_TAC `st:(A,FFI)loop_state` THEN
    SUBGOAL_THEN `loop_state_clock (st:(A,FFI)loop_state) = 0` SUBST1_TAC THENL
     [ASM_MESON_TAC[crep_to_loopProof_state_rel_def]; ALL_TAC] THEN
    REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    FS[crep_to_loopProof_state_rel_def; crep_empty_locals_def];
    ALL_TAC] THEN
  (* the callee runs *)
  NAMED_CASES_ON "crep_evaluate (prog,crep_state_locals_fupd (K (FEMPTY |++ ZIP ns args))
     (crep_dec_clock s))" ["x st1"] THEN CASE_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(x = SOME (crep_Error:(A)crep_result)) /\ ~(x = NONE) /\
                (!n. ~(x = SOME (crepSem_Break n))) /\ (!n. ~(x = SOME (crepSem_Continue n)))`
    STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(CASE_REWRITE_RULE[PAIR_EQ]) THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "ihc" (MP_TAC o SPECL [`args:((A)word_lab)list`; `prog:(A)crep_prog`;
     `FEMPTY |++ ZIP (ns:num list) (args:((A)word_lab)list)`]) THEN
  ASM_REWRITE_TAC[crep_lookup_code_def] THEN CASE_REWRITE_TAC[] THEN
  SUBGOAL_THEN `LENGTH (ns:num list) = len` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`x:((A)crep_result)option`; `st1:(A,FFI)crep_state`;
     `loop_state_clock_fupd (K (loop_state_clock st - 1))
        (loop_state_locals_fupd (K (fromAList (ZIP (list_of_seq I len)
          (MAP wlab_wloc (args:((A)word_lab)list))))) (st:(A,FFI)loop_state))`;
     `crep_to_loopProof_ctxt_fc (crep_to_loop_context_target ctxt)
        (crep_to_loop_context_funcs ctxt) (ns:num list) (list_of_seq I len)`;
     `list_to_num_set (list_of_seq I len)`]) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`ns:num list`; `list_of_seq I len`; `args:((A)word_lab)list`;
     `s:(A,FFI)crep_state`; `st:(A,FFI)loop_state`; `ctxt:crep_to_loop_context`;
     `nl:num_set`; `fname:mlstring`; `argexps:((A)crep_exp)list`; `prog:(A)crep_prog`;
     `loc:num`] crep_to_loopProof_call_preserve_state_code_locals_rel) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_LIST_OF_SEQ; ALL_DISTINCT_GENLIST; I_THM] THEN
    ASM_MESON_TAC[opt_mmap_eq_some];
    ALL_TAC] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN ANTS_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[crep_to_loopProof_state_rel_def]) THEN
    FS[crep_dec_clock_def; crep_to_loopProof_state_rel_def];
    ALL_TAC] THEN
  STRIP_TAC THEN
  QCASES_ON "x" THEN
  TRY(FIRST_X_ASSUM(MP_TAC o check (fun th ->
        concl th = `~(NONE = NONE:((A)crep_result)option)`)) THEN REWRITE_TAC[] THEN NO_TAC) THEN
  QCASES_ON "a" THEN RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[option_INJ; injectivity "crep_result";
                              distinctness "crep_result"]) THEN
  TRY(FIRST_X_ASSUM CONTR_TAC) THEN
  TRY(FIRST_X_ASSUM(MP_TAC o SPEC `a':num`) THEN REWRITE_TAC[] THEN NO_TAC) THEN
  PC2LAUX_TAILCALL_RES_TAC;;

(* the returning call: caltyp = SOME (rts,hdl) (helper H2 of PC2L) *)

let PC2LAUX_domain_alist_insert_sub = prove
 (`!(l:num_set) xs (ys:A list) t.
     LENGTH xs = LENGTH ys /\ domain l SUBSET domain t ==>
     domain l SUBSET domain (alist_insert xs ys t)`,
  SIMP_TAC[domain_alist_insert] THEN SET_TAC[]);;

let PC2LAUX_lookup_alist_insert_el = prove
 (`!xs (ys:A list) t i.
     ALL_DISTINCT xs /\ LENGTH xs = LENGTH ys /\ i < LENGTH xs ==>
     lookup (EL i xs) (alist_insert xs ys t) = SOME (EL i ys)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[lookup_alist_insert] THEN
  MP_TAC(ISPECL [`ZIP (xs:num list) (ys:A list)`; `i:num`] ALOOKUP_ALL_DISTINCT_EL) THEN
  ASM_SIMP_TAC[LENGTH_ZIP; MAP_FST_ZIP; EL_ZIP] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC THEN CASE_REWRITE_TAC[]]);;

let PC2LAUX_lookup_alist_insert_not_mem = prove
 (`!xs (ys:A list) t n.
     ~MEM n xs /\ LENGTH xs = LENGTH ys ==>
     lookup n (alist_insert xs ys t) = lookup n t`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[lookup_alist_insert] THEN
  SUBGOAL_THEN `ALOOKUP (ZIP (xs:num list) (ys:A list)) n = NONE` SUBST1_TAC THENL
   [ASM_SIMP_TAC[ALOOKUP_NONE; MAP_FST_ZIP]; CASE_REWRITE_TAC[]]);;
let PC2LAUX_locals_rel_call_ret = prove
 (`!ctxt l (sl:(num,(A)word_lab)fmap) tl rts retvs nrhss X.
     crep_to_loopProof_locals_rel ctxt l sl tl /\
     OPT_MMAP (FLOOKUP (crep_to_loop_context_vars ctxt)) rts = SOME nrhss /\
     ALL (\n. n IN domain l) nrhss /\ ALL_DISTINCT nrhss /\
     LENGTH retvs = LENGTH rts /\ ALL_DISTINCT rts /\
     domain l SUBSET domain X /\
     (!n. n IN domain l /\ n <= crep_to_loop_context_vmax ctxt ==> lookup n X = lookup n tl) ==>
     crep_to_loopProof_locals_rel ctxt l (sl |++ ZIP rts retvs)
       (inter (alist_insert nrhss (MAP wlab_wloc retvs) X) l)`,
  REWRITE_TAC[crep_to_loopProof_locals_rel_def; crep_to_loopProof_ctxt_max_def] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `LENGTH (nrhss:num list) = LENGTH (rts:num list)` ASSUME_TAC THENL
   [ASM_MESON_TAC[opt_mmap_length_eq]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[domain_inter; domain_alist_insert; LENGTH_MAP] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `MEM (vname:num) rts` THENL
   [(FIRST_ASSUM(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC o REWRITE_RULE[MEM_EXISTS_EL]) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MP_TAC(ISPECL [`rts:num list`; `sl:(num,(A)word_lab)fmap`; `retvs:((A)word_lab)list`; `i:num`]
    update_eq_zip_flookup) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `v = EL i (retvs:((A)word_lab)list)` SUBST_ALL_TAC THENL
   [ASM_MESON_TAC[option_INJ]; ALL_TAC] THEN
  EXISTS_TAC `EL i (nrhss:num list)` THEN
  SUBGOAL_THEN `i < LENGTH (nrhss:num list)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC opt_mmap_el THEN ASM_REWRITE_TAC[];
    QPAT_X_ASSUM "ALL _ nrhss" (MP_TAC o REWRITE_RULE[GSYM ALL_MEM]) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[MEM_EL];
    REWRITE_TAC[lookup_inter_alt] THEN
    SUBGOAL_THEN `EL i (nrhss:num list) IN domain (l:num_set)` (fun th -> REWRITE_TAC[th]) THENL
     [QPAT_X_ASSUM "ALL _ nrhss" (MP_TAC o REWRITE_RULE[GSYM ALL_MEM]) THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[MEM_EL];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`nrhss:num list`; `MAP wlab_wloc (retvs:((A)word_lab)list)`;
      `X:((A)word_loc)spt`; `i:num`] PC2LAUX_lookup_alist_insert_el) THEN
    ASM_REWRITE_TAC[LENGTH_MAP] THEN DISCH_THEN SUBST1_TAC THEN
    AP_TERM_TAC THEN MATCH_MP_TAC EL_MAP THEN ASM_ARITH_TAC]);
    (SUBGOAL_THEN `FLOOKUP (sl:(num,(A)word_lab)fmap) vname = SOME v` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`rts:num list`; `retvs:((A)word_lab)list`; `sl:(num,(A)word_lab)fmap`;
                   `vname:num`] flookup_fupdate_zip_not_mem) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`vname:num`; `v:(A)word_lab`] o
    check (fun th -> is_forall (concl th) &&
           can (find_term ((=) `sl:(num,(A)word_lab)fmap`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN EXISTS_TAC `n:num` THEN
  ASM_REWRITE_TAC[lookup_inter_alt] THEN
     SUBGOAL_THEN `~MEM (n:num) nrhss` ASSUME_TAC THENL
   [DISCH_TAC THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC o REWRITE_RULE[MEM_EXISTS_EL]) THEN
    SUBGOAL_THEN `FLOOKUP (crep_to_loop_context_vars ctxt) (EL j (rts:num list)) =
                  SOME (EL j (nrhss:num list))` ASSUME_TAC THENL
     [MATCH_MP_TAC opt_mmap_el THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `vname = EL j (rts:num list)` ASSUME_TAC THENL
     [QPAT_X_ASSUM "distinct_vars _" (MP_TAC o REWRITE_RULE[distinct_vars_def]) THEN
      DISCH_THEN MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`n:num`; `EL j (nrhss:num list)`] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `~MEM (vname:num) rts` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MEM_EL THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`nrhss:num list`; `MAP wlab_wloc (retvs:((A)word_lab)list)`;
    `X:((A)word_loc)spt`; `n:num`] PC2LAUX_lookup_alist_insert_not_mem) THEN
  ASM_REWRITE_TAC[LENGTH_MAP] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `n <= crep_to_loop_context_vmax ctxt` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_MESON_TAC[])]);;

let PC2LAUX_SOME_PREFIX_TAC (stt:term) : tactic =
  SUBST1_TAC (SYM (ASSUME `LENGTH (les:((A)loop_exp)list) = LENGTH (argexps:((A)crep_exp)list)`))
    THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP PC2LAUX_call_prefix (end_itlist CONJ
    [th; ASSUME (subst [stt,`stt:(A,FFI)loop_state`]
       `MAP (loop_eval (stt:(A,FFI)loop_state)) les = MAP SOME (MAP wlab_wloc
           (args:((A)word_lab)list))`);
     ASSUME `distinct_lists (gen_temps tmp (LENGTH (les:((A)loop_exp)list)))
               (FLAT (MAP locals_touched les))`;
     ASSUME `ALL_DISTINCT (gen_temps tmp (LENGTH (les:((A)loop_exp)list)))`;
     ASSUME `LENGTH (gen_temps tmp (LENGTH (les:((A)loop_exp)list))) = LENGTH les`])]);;

let PC2LAUX_SOME_ENTER_TAC (xt:term) : tactic =
  let stt = subst [xt,`xt:num`]
    `loop_state_clock_fupd (K (loop_state_clock st + xt)) (st:(A,FFI)loop_state)` in
  MP_TAC(SPEC xt (MATCH_MP (REWRITE_RULE[IMP_CONJ] loop_evaluate_add_clock_eq)
    (ASSUME `loop_evaluate (loop_nested_seq p,loop_state_clock_fupd
       (K (loop_state_clock t + ck)) (t:(A,FFI)loop_state)) = (NONE,st)`))) THEN
  SIMP[option_DISTINCT; GSYM ADD_ASSOC] THEN DISCH_TAC THEN
  EXISTS_TAC (subst [xt,`xt:num`] `ck + xt:num`) THEN
  SUBGOAL_THEN (subst [stt,`stt:(A,FFI)loop_state`]
     `MAP (loop_eval (stt:(A,FFI)loop_state)) les = MAP SOME (MAP wlab_wloc
         (args:((A)word_lab)list))`)
    ASSUME_TAC THENL [ASM_REWRITE_TAC[loop_eval_upd_clock]; ALL_TAC] THEN
  PC2LAUX_SOME_PREFIX_TAC stt THEN
  PC2LAUX_CALL_FIND_TAC stt THEN
  MP_TAC(ISPECL [`l:num_set`; subst [stt,`stt:(A,FFI)loop_state`]
    `loop_state_locals_fupd (K (alist_insert (gen_temps tmp (LENGTH (argexps:((A)crep_exp)list)))
       (MAP wlab_wloc (args:((A)word_lab)list)) (loop_state_locals (st:(A,FFI)loop_state))))
       (stt:(A,FFI)loop_state)`]
    PC2LAUX_loop_entry) THEN
  ANTS_TAC THENL
   [SIMP[] THEN MATCH_MP_TAC PC2LAUX_domain_alist_insert_sub THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[gen_temps_def; LENGTH_LIST_OF_SEQ; LENGTH_MAP] THEN
    MATCH_MP_TAC opt_mmap_length_eq THEN
    EXISTS_TAC `crep_eval (s:(A,FFI)crep_state)` THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  SIMP[ADD_EQ_0] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[ocompile_def; o_THM];;

let PC2LAUX_CALLEE_RUN_TAC (ttac:thm_tactic) : tactic =
  FIRST_X_ASSUM(ttac o check (fun th -> is_eq (concl th) &&
    (try let f,args = strip_comb(lhs(concl th)) in
         fst(dest_const f) = "loop_evaluate" &&
         (let c,cargs = strip_comb(fst(dest_pair(hd args))) in
          fst(dest_const c) = "crep_to_loop_compile" &&
          last cargs = `prog:(A)crep_prog`)
     with _ -> false)));;
let PC2LAUX_SOME_CALLEE_TAC : tactic =
  PC2LAUX_CALLEE_RUN_TAC
    (MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] loop_liveProof_optimise_correct)) THEN
  ASM_REWRITE_TAC[option_DISTINCT; option_INJ; distinctness "loop_result"] THEN
  DISCH_TAC THEN REWRITE_TAC[loop_dec_clock_def] THEN
  SAME_RUN_TAC[] THEN CASE_REWRITE_TAC[];;
let PC2LAUX_SOME_CALLEE_PLUS_TAC (et:term) : tactic =
  PC2LAUX_CALLEE_RUN_TAC
    (fun th -> MP_TAC (SPEC et (MATCH_MP (REWRITE_RULE[IMP_CONJ] loop_evaluate_add_clock_eq) th)))
      THEN
  ASM_REWRITE_TAC[option_DISTINCT; option_INJ; distinctness "loop_result"] THEN DISCH_TAC THEN
  PC2LAUX_SOME_CALLEE_TAC;;

let PC2LAUX_HANDLER_RUN_TAC (ttac:thm_tactic) : tactic =
  FIRST_X_ASSUM(ttac o check (fun th -> is_eq (concl th) &&
    (try let f,args = strip_comb(lhs(concl th)) in
         fst(dest_const f) = "loop_evaluate" &&
         (let c,cargs = strip_comb(fst(dest_pair(hd args))) in
          fst(dest_const c) = "crep_to_loop_compile" &&
          last cargs = `p':(A)crep_prog`)
     with _ -> false)));;

let PC2LAUX_domain_inter_sub = prove
 (`!(l:num_set) (t:A spt). domain l SUBSET domain t ==> domain l SUBSET domain (inter t l)`,
  REWRITE_TAC[domain_inter] THEN SET_TAC[]);;

let PC2LAUX_CUT_RES_TAC (dtac:tactic) : tactic = fun (asl,w as g) ->
  let tm = find_term (fun t -> try let f,args = strip_comb t in
                        fst(dest_const f) = "cut_res" && length args = 2 &&
                        is_const(fst(dest_pair(el 1 args))) &&
                        fst(dest_const(fst(dest_pair(el 1 args)))) = "NONE"
                      with _ -> false) w in
  let args = snd(strip_comb tm) in
  let l = hd args and st = snd(dest_pair(el 1 args)) in
  (MP_TAC(ISPECL [l; st] PC2LAUX_loop_entry) THEN ANTS_TAC THENL
    [dtac; DISCH_THEN SUBST1_TAC]) g;;

let PC2LAUX_ARGS_LENGTH_TAC : tactic =
  REWRITE_TAC[gen_temps_def; LENGTH_LIST_OF_SEQ; LENGTH_MAP] THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE
   (MATCH_MP_TAC opt_mmap_length_eq THEN
    EXISTS_TAC `crep_eval (s:(A,FFI)crep_state)` THEN ASM_REWRITE_TAC[]) ORELSE
   ASM_REWRITE_TAC[LENGTH_MAP]);;
let PC2LAUX_DOMAIN_TAC : tactic =
  SIMP[] THEN
  REPEAT((MATCH_MP_TAC PC2LAUX_domain_alist_insert_sub THEN CONJ_TAC THENL
            [PC2LAUX_ARGS_LENGTH_TAC; ALL_TAC]) ORELSE
         MATCH_MP_TAC PC2LAUX_domain_inter_sub) THEN
  ASM_REWRITE_TAC[];;

let PC2LAUX_CALL_SOME_TAC : tactic =
  SUBGOAL_THEN `ALL_DISTINCT (rts:num list)` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg (concl th) &&
         can (find_term ((=) `ALL_DISTINCT:num list->bool`)) (concl th))) THEN
      CASE_REWRITE_TAC[] THEN REWRITE_TAC[];
      ALL_TAC] THEN
    QPAT_ASSUM "crep_to_loopProof_locals_rel ctxt l (crep_state_locals s) (loop_state_locals t)"
      (STRIP_ASSUME_TAC o MATCH_MP crep_to_loopProof_locals_rel_intro) THEN
    SUBGOAL_THEN `crep_to_loopProof_locals_rel ctxt l (crep_state_locals (s:(A,FFI)crep_state))
                    (loop_state_locals (st:(A,FFI)loop_state))` ASSUME_TAC THENL
     [MATCH_MP_TAC locals_rel_cutset_prop THEN
      MAP_EVERY EXISTS_TAC [`loop_state_locals (t:(A,FFI)loop_state)`; `nl:num_set`] THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[comp_syn_impl_cut_sets_subspt];
      ALL_TAC] THEN
    SUBGOAL_THEN `ALL_DISTINCT (rt_vars (crep_to_loop_context_vars ctxt) rts
                                  (crep_to_loop_context_vmax ctxt + 1))` ASSUME_TAC THENL
     [MATCH_MP_TAC all_distinct_ctxt_lookup_all_distinct THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `domain (l:num_set) SUBSET domain (loop_state_locals (st:(A,FFI)loop_state))`
      ASSUME_TAC THENL
     [QPAT_ASSUM "crep_to_loopProof_locals_rel ctxt l (crep_state_locals s) (loop_state_locals st)"
        (MP_TAC o MATCH_MP crep_to_loopProof_locals_rel_intro) THEN SIMP_TAC[];
      ALL_TAC] THEN
  ASM_CASES_TAC `crep_state_clock (s:(A,FFI)crep_state) = 0` THEN ASM_REWRITE_TAC[] THENL
   [(* no clock left at the call: TimeOut *)
    REWRITE_TAC[PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) THEN
    QEXISTS_TAC "ck" THEN
    PC2LAUX_SOME_PREFIX_TAC `st:(A,FFI)loop_state` THEN
    PC2LAUX_CALL_FIND_TAC `st:(A,FFI)loop_state` THEN
    PC2LAUX_CUT_RES_TAC PC2LAUX_DOMAIN_TAC THEN
    SUBGOAL_THEN `loop_state_clock (st:(A,FFI)loop_state) = 0` ASSUME_TAC THENL
     [ASM_MESON_TAC[crep_to_loopProof_state_rel_def]; ALL_TAC] THEN
    SIMP[] THEN CASE_REWRITE_TAC[] THEN
    FS[crep_to_loopProof_state_rel_def; crep_empty_locals_def];
    (* the callee runs *)
    NAMED_CASES_ON "crep_evaluate (prog,crep_state_locals_fupd (K (FEMPTY |++ ZIP ns args))
         (crep_dec_clock s))" ["x st1"] THEN CASE_REWRITE_TAC[] THEN DISCH_TAC THEN
      SUBGOAL_THEN `~(x = SOME (crep_Error:(A)crep_result)) /\ ~(x = NONE) /\
                    (!n. ~(x = SOME (crepSem_Break n))) /\ (!n. ~(x = SOME (crepSem_Continue n)))`
        STRIP_ASSUME_TAC THENL
       [REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
        RULE_ASSUM_TAC(CASE_REWRITE_RULE[PAIR_EQ]) THEN ASM_MESON_TAC[];
        ALL_TAC] THEN
      REMOVE_THEN "ihc" (MP_TAC o SPECL [`args:((A)word_lab)list`; `prog:(A)crep_prog`;
         `FEMPTY |++ ZIP (ns:num list) (args:((A)word_lab)list)`]) THEN
      ASM_REWRITE_TAC[crep_lookup_code_def] THEN CASE_REWRITE_TAC[] THEN
      SUBGOAL_THEN `LENGTH (ns:num list) = len` ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPECL [`x:((A)crep_result)option`; `st1:(A,FFI)crep_state`;
         `loop_state_clock_fupd (K (loop_state_clock st - 1))
            (loop_state_locals_fupd (K (fromAList (ZIP (list_of_seq I len)
              (MAP wlab_wloc (args:((A)word_lab)list))))) (st:(A,FFI)loop_state))`;
         `crep_to_loopProof_ctxt_fc (crep_to_loop_context_target ctxt)
            (crep_to_loop_context_funcs ctxt) (ns:num list) (list_of_seq I len)`;
         `list_to_num_set (list_of_seq I len)`]) THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`ns:num list`; `list_of_seq I len`; `args:((A)word_lab)list`;
         `s:(A,FFI)crep_state`; `st:(A,FFI)loop_state`; `ctxt:crep_to_loop_context`;
         `nl:num_set`; `fname:mlstring`; `argexps:((A)crep_exp)list`; `prog:(A)crep_prog`;
         `loc:num`] crep_to_loopProof_call_preserve_state_code_locals_rel) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[LENGTH_LIST_OF_SEQ; ALL_DISTINCT_GENLIST; I_THM] THEN
        ASM_MESON_TAC[opt_mmap_eq_some];
        ALL_TAC] THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN ANTS_TAC THENL
       [RULE_ASSUM_TAC(REWRITE_RULE[crep_to_loopProof_state_rel_def]) THEN
        FS[crep_dec_clock_def; crep_to_loopProof_state_rel_def];
        ALL_TAC] THEN
      STRIP_TAC THEN
    SUBGOAL_THEN `crep_to_loopProof_code_rel ctxt (crep_state_code (st1:(A,FFI)crep_state))
                      (loop_state_code (t1:(A,FFI)loop_state))` ASSUME_TAC THENL
       [QPAT_X_ASSUM "crep_to_loopProof_code_rel (crep_to_loopProof_ctxt_fc _ _ _ _) _ _" MP_TAC
         THEN
        REWRITE_TAC[crep_to_loopProof_code_rel_def; crep_to_loopProof_ctxt_fc_def;
                    PC2LAUX_ctxt_accessors];
        ALL_TAC] THEN
      SUBGOAL_THEN `~(loop_state_clock (st:(A,FFI)loop_state) = 0)` ASSUME_TAC THENL
       [ASM_MESON_TAC[crep_to_loopProof_state_rel_def]; ALL_TAC] THEN
      QCASES_ON "x" THEN
      TRY(FIRST_X_ASSUM(MP_TAC o check (fun th ->
            concl th = `~(NONE = NONE:((A)crep_result)option)`)) THEN REWRITE_TAC[] THEN
              NO_TAC) THEN
      QCASES_ON "a" THEN RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[option_INJ; injectivity "crep_result";
                                  distinctness "crep_result"]) THEN
      TRY(FIRST_X_ASSUM CONTR_TAC) THEN
      TRY(FIRST_X_ASSUM(MP_TAC o SPEC `a':num`) THEN REWRITE_TAC[] THEN NO_TAC) THENL
     [(* callee TimeOut *)
      PC2LAUX_SOME_ENTER_TAC `ck':num` THEN PC2LAUX_SOME_CALLEE_TAC THEN
      QPAT_X_ASSUM "_ = res /\\ _ = s1" (CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
        CASE_REWRITE_TAC[] THEN REWRITE_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
        FS[crep_to_loopProof_state_rel_def; crep_empty_locals_def];
      (* callee Return: the return values are assigned *)
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
           rand (concl th) = `res:((A)crep_result)option,(s1:(A,FFI)crep_state)`)) THEN
        COND_CASES_TAC THENL [REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
        NAMED_CASES_ON "OPT_MMAP (FLOOKUP (crep_state_locals s)) rts" ["";"vs"] THEN
        CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
        DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
        MP_TAC(ISPECL [`rts:num list`; `vs:((A)word_lab)list`; `s:(A,FFI)crep_state`;
          `st:(A,FFI)loop_state`; `ctxt:crep_to_loop_context`; `l:num_set`]
          opt_mmap_rhss_locals_rel) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `nrhss:num list` STRIP_ASSUME_TAC) THEN
        SUBGOAL_THEN `rt_vars (crep_to_loop_context_vars ctxt) rts
                        (crep_to_loop_context_vmax ctxt + 1) = nrhss` ASSUME_TAC THENL
         [ASM_REWRITE_TAC[rt_vars_def] THEN CASE_REWRITE_TAC[]; ALL_TAC] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `rt_vars (crep_to_loop_context_vars ctxt) rts
                        (crep_to_loop_context_vmax ctxt + 1) = nrhss`]) THEN
        ASM_REWRITE_TAC[] THEN
      PC2LAUX_SOME_ENTER_TAC `ck' + 1` THEN PC2LAUX_SOME_CALLEE_PLUS_TAC `1` THEN
      REWRITE_TAC[rt_vars_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
        SUBGOAL_THEN `LENGTH (MAP wlab_wloc (a':((A)word_lab)list)) = LENGTH (nrhss:num list)`
          ASSUME_TAC THENL [ASM_REWRITE_TAC[LENGTH_MAP]; ALL_TAC] THEN
        ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[loop_evaluate_def] THEN
        SIMP[set_vars_def] THEN
      PC2LAUX_CUT_RES_TAC PC2LAUX_DOMAIN_TAC THEN SIMP[ADD_EQ_0; ARITH_EQ] THEN
      REWRITE_TAC[loop_dec_clock_def] THEN SIMP[ADD_SUB] THEN
      CONJ_TAC THENL [FS[crep_to_loopProof_state_rel_def]; ALL_TAC] THEN
        MATCH_MP_TAC PC2LAUX_locals_rel_call_ret THEN
        EXISTS_TAC `loop_state_locals (st:(A,FFI)loop_state)` THEN ASM_REWRITE_TAC[] THEN
        CONJ_TAC THENL [PC2LAUX_DOMAIN_TAC; ALL_TAC] THEN
        REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[lookup_inter_alt] THEN
        MATCH_MP_TAC PC2LAUX_lookup_alist_insert_not_mem THEN
        CONJ_TAC THENL [ALL_TAC; PC2LAUX_ARGS_LENGTH_TAC] THEN
        REWRITE_TAC[gen_temps_def; MEM_GENLIST] THEN STRIP_TAC THEN ASM_ARITH_TAC;
      (* callee Exception *)
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
           rand (concl th) = `res:((A)crep_result)option,(s1:(A,FFI)crep_state)`)) THEN
        NAMED_CASES_ON "hdl" ["";"hp"] THEN CASE_REWRITE_TAC[] THENL
       [(* no handler *)
        REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
          PC2LAUX_SOME_ENTER_TAC `ck':num` THEN PC2LAUX_SOME_CALLEE_TAC THEN
        ONCE_REWRITE_TAC[loop_evaluate_def] THEN
          SIMP[loop_set_var_def; lookup_insert; cut_res_def; call_env_def] THEN
          REWRITE_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
          FS[crep_to_loopProof_state_rel_def; crep_empty_locals_def];
        NAMED_CASES_ON "hp" ["eid' p'"] THEN CASE_REWRITE_TAC[] THEN COND_CASES_TAC THENL
         [(* the handler catches the exception *)
          DISCH_TAC THEN QPAT_X_ASSUM "a' = eid'" (SUBST_ALL_TAC o SYM) THEN
            SUBGOAL_THEN `crep_to_loopProof_locals_rel ctxt l (crep_state_locals
                (s:(A,FFI)crep_state))
               (insert (crep_to_loop_context_vmax ctxt + 1) (wl_Word a')
                 (inter (alist_insert (gen_temps tmp (LENGTH (argexps:((A)crep_exp)list)))
                    (MAP wlab_wloc (args:((A)word_lab)list)) (loop_state_locals
                      (st:(A,FFI)loop_state))) l))`
              ASSUME_TAC THENL
             [MATCH_MP_TAC locals_rel_insert_gt_vmax THEN REWRITE_TAC[ARITH_RULE `n < n + 1`] THEN
              MATCH_MP_TAC PC2LAUX_locals_rel_inter THEN
              MATCH_MP_TAC PC2LAUX_locals_rel_extend THEN
              MAP_EVERY EXISTS_TAC [`l:num_set`; `loop_state_locals (st:(A,FFI)loop_state)`] THEN
              ASM_REWRITE_TAC[SUBSET_REFL] THEN CONJ_TAC THENL
               [MATCH_MP_TAC PC2LAUX_domain_alist_insert_sub THEN ASM_REWRITE_TAC[] THEN
                PC2LAUX_ARGS_LENGTH_TAC;
                REPEAT STRIP_TAC THEN MATCH_MP_TAC PC2LAUX_lookup_alist_insert_not_mem THEN
                CONJ_TAC THENL [ALL_TAC; PC2LAUX_ARGS_LENGTH_TAC] THEN
                REWRITE_TAC[gen_temps_def; MEM_GENLIST] THEN STRIP_TAC THEN ASM_ARITH_TAC];
              ALL_TAC] THEN
          REMOVE_THEN "ihh" (MP_TAC o SPECL [`args:((A)word_lab)list`; `prog:(A)crep_prog`;
               `FEMPTY |++ ZIP (ns:num list) (args:((A)word_lab)list)`; `rts:num list`; `a':A word`;
               `p':(A)crep_prog`; `st1:(A,FFI)crep_state`]) THEN
            ASM_REWRITE_TAC[crep_lookup_code_def] THEN CASE_REWRITE_TAC[] THEN
              ASM_REWRITE_TAC[] THEN
            DISCH_THEN(MP_TAC o SPECL [`res:((A)crep_result)option`; `s1:(A,FFI)crep_state`;
              `loop_state_locals_fupd (K (insert (crep_to_loop_context_vmax ctxt + 1) (wl_Word
                  (a':A word))
                 (inter (alist_insert (gen_temps tmp (LENGTH (argexps:((A)crep_exp)list)))
                    (MAP wlab_wloc (args:((A)word_lab)list)) (loop_state_locals
                      (st:(A,FFI)loop_state))) (l:num_set))))
                 (t1:(A,FFI)loop_state)`;
              `ctxt:crep_to_loop_context`; `l:num_set`]) THEN
            ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
             [FS[crep_to_loopProof_state_rel_def]; STRIP_TAC] THEN
          NAMED_CASES_ON "res" ["";"r"] THENL
           [(* the handler ends normally: two more cut_res, two more ticks *)
            SUBGOAL_THEN `res1':((A)loop_result)option = NONE` ASSUME_TAC THENL
               [QPAT_X_ASSUM "res1' = _" SUBST1_TAC THEN CASE_REWRITE_TAC[]; ALL_TAC] THEN
              RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
              PC2LAUX_SOME_ENTER_TAC `ck' + 1 + ck'' + 2` THEN
              PC2LAUX_SOME_CALLEE_PLUS_TAC `1 + ck'' + 2` THEN
              SIMP[loop_evaluate_def; loop_set_var_def; lookup_insert; get_var_imm_def;
                asm_word_cmp_def] THEN
              CASE_REWRITE_TAC[] THEN SIMP[ADD_EQ_0; ARITH_EQ; loop_dec_clock_def] THEN
            PC2LAUX_HANDLER_RUN_TAC
                (fun th -> MP_TAC (SPEC `2` (MATCH_MP (REWRITE_RULE[IMP_CONJ]
                  loop_evaluate_add_clock_eq) th))) THEN
              ASM_REWRITE_TAC[option_DISTINCT] THEN DISCH_TAC THEN SAME_RUN_TAC[] THEN
              QPAT_ASSUM "crep_to_loopProof_locals_rel ctxt l (crep_state_locals s1) _"
                (STRIP_ASSUME_TAC o MATCH_MP crep_to_loopProof_locals_rel_intro) THEN
              PC2LAUX_CUT_RES_TAC (SIMP[] THEN ASM_REWRITE_TAC[]) THEN
              SIMP[ADD_EQ_0; ARITH_EQ; loop_dec_clock_def] THEN
              PC2LAUX_CUT_RES_TAC (SIMP[] THEN MATCH_MP_TAC PC2LAUX_domain_inter_sub THEN
                ASM_REWRITE_TAC[]) THEN
              SIMP[ADD_EQ_0; ARITH_EQ; loop_dec_clock_def] THEN
            REWRITE_TAC[ARITH_RULE `!n. ~((n + 2) - 1 = 0) /\ ((n + 2) - 1) - 1 = n`; PAIR_EQ] THEN
              REWRITE_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN SIMP[RECORD_SELFID_ss] THEN
              CONJ_TAC THENL [FS[crep_to_loopProof_state_rel_def]; ALL_TAC] THEN
              REPEAT(MATCH_MP_TAC PC2LAUX_locals_rel_inter) THEN ASM_REWRITE_TAC[];
            (* any other result of the handler *)
            SUBGOAL_THEN `~(res1':((A)loop_result)option = NONE)` ASSUME_TAC THENL
               [QPAT_X_ASSUM "res1' = _" SUBST1_TAC THEN CASE_REWRITE_TAC[] THEN
                QCASES_ON "r" THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[option_DISTINCT];
                ALL_TAC] THEN
            PC2LAUX_SOME_ENTER_TAC `ck' + 1 + ck''` THEN
              PC2LAUX_SOME_CALLEE_PLUS_TAC `1 + ck''` THEN
            SIMP[loop_evaluate_def; loop_set_var_def; lookup_insert; get_var_imm_def;
              asm_word_cmp_def] THEN
              CASE_REWRITE_TAC[] THEN SIMP[ADD_EQ_0; ARITH_EQ; loop_dec_clock_def] THEN
            SAME_RUN_TAC[] THEN
              REWRITE_TAC[cut_res_def; ASSUME `~(res1':((A)loop_result)option = NONE)`] THEN
              EXISTS_TAC `t1':(A,FFI)loop_state` THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
            CASE_REWRITE_TAC[] THEN RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN ASM_REWRITE_TAC[]];
          (* another exception id: raised again *)
          REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
            PC2LAUX_SOME_ENTER_TAC `ck':num` THEN PC2LAUX_SOME_CALLEE_TAC THEN
            SIMP[loop_evaluate_def; loop_set_var_def; lookup_insert; get_var_imm_def;
              asm_word_cmp_def] THEN
            CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
            SIMP[loop_evaluate_def; lookup_insert; cut_res_def; call_env_def] THEN
            REWRITE_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
            FS[crep_to_loopProof_state_rel_def; crep_empty_locals_def]]];
      (* callee FinalFFI *)
      PC2LAUX_SOME_ENTER_TAC `ck':num` THEN PC2LAUX_SOME_CALLEE_TAC THEN
        QPAT_X_ASSUM "_ = res /\\ _ = s1" (CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
        CASE_REWRITE_TAC[] THEN REWRITE_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
        FS[crep_to_loopProof_state_rel_def; crep_empty_locals_def]]];;

(* HOL4: Resume ncompile_correct[Call] *)

let PC2LAUX_ncompile_Call = prove
 (PC2LAUX_ncompile_case "crep_Call",
  PC2LAUX_CALL_COMMON_TAC THEN
  NAMED_CASES_ON "caltyp" ["";"rh"] THEN CASE_REWRITE_TAC[] THENL
   [PC2LAUX_CALL_NONE_TAC;
    NAMED_CASES_ON "rh" ["rts hdl"] THEN CASE_REWRITE_TAC[] THEN PC2LAUX_CALL_SOME_TAC]);;

(* ------------------------------------------------------------------------- *)

(* HOL4: Finalise ncompile_correct.  The theorem stated at HOL4 line 110:   *)
(* the induction on crep_evaluate_ind (HOL4 recInduct evaluate_ind) with    *)
(* the predicate PC2LAUX_ncompile_P, whose cases (beta-reduced as           *)
(* PC2LAUX_ncompile_case gives them) are the lemmas PC2LAUX_ncompile_Skip   *)
(* .. PC2LAUX_ncompile_ExtCall above (HOL4 Resume ncompile_correct[...]);   *)
(* its conclusion quantifies over the pair (prog,state)                      *)

let ncompile_correct = prove
 (PC2LAUX_ncompile_stmt,
  MP_TAC(CONV_RULE (DEPTH_CONV BETA_CONV THENC REWRITE_CONV[FST; SND])
           (ISPEC PC2LAUX_ncompile_P crep_evaluate_ind)) THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN
  REWRITE_TAC[PC2LAUX_ncompile_Skip; PC2LAUX_ncompile_Dec; PC2LAUX_ncompile_Primitive;
              PC2LAUX_ncompile_Assign; PC2LAUX_ncompile_Store; PC2LAUX_ncompile_Store32;
              PC2LAUX_ncompile_StoreByte; PC2LAUX_ncompile_StoreGlob;
              PC2LAUX_ncompile_ShMem; PC2LAUX_ncompile_Seq; PC2LAUX_ncompile_If;
              PC2LAUX_ncompile_Break; PC2LAUX_ncompile_Continue; PC2LAUX_ncompile_While;
              PC2LAUX_ncompile_Return; PC2LAUX_ncompile_Raise; PC2LAUX_ncompile_Tick;
              PC2LAUX_ncompile_Call; PC2LAUX_ncompile_ExtCall]);;

(* the statement is HOL4's (PC2LAUX_ncompile_stmt) *)

let () =
  if not (aconv (concl ncompile_correct) PC2LAUX_ncompile_stmt && hyp ncompile_correct = [])
  then failwith "ncompile_correct: not the statement of PC2LAUX_ncompile_stmt";;

(* ------------------------------------------------------------------------- *)

(* HOL4 lines 3720-4064: ocompile_correct .. evaluate_twice_cases          *)

let ocompile_correct = prove
 (CASE_TERM
  `crep_evaluate (p,s:(A,FFI)crep_state) = (res,s1) /\
   crep_to_loopProof_state_rel s (t:(A,FFI)loop_state) /\
   mem_rel (crep_state_memory s) (loop_state_memory t) (crep_state_memaddrs s) /\
   crep_to_loopProof_globals_rel (crep_state_globals s) (loop_state_globals t) /\
   crep_to_loopProof_code_rel ctxt (crep_state_code s) (loop_state_code t) /\
   crep_to_loopProof_locals_rel ctxt l (crep_state_locals s) (loop_state_locals t) /\
   ~(res = SOME crep_Error) /\ (!n. ~(res = SOME (crepSem_Break n))) /\
   (!n. ~(res = SOME (crepSem_Continue n))) /\ ~(res = NONE) ==>
   ?ck res1 t1.
     loop_evaluate (ocompile ctxt l p,
                    loop_state_clock_fupd (K (loop_state_clock t + ck)) t) = (res1,t1) /\
     crep_to_loopProof_state_rel s1 t1 /\
     mem_rel (crep_state_memory s1) (loop_state_memory t1) (crep_state_memaddrs s1) /\
     crep_to_loopProof_globals_rel (crep_state_globals s1) (loop_state_globals t1) /\
     crep_to_loopProof_code_rel ctxt (crep_state_code s1) (loop_state_code t1) /\
     (match res with
        NONE -> F
      | SOME crep_Error -> F
      | SOME crep_TimeOut -> res1 = SOME loop_TimeOut
      | SOME (crepSem_Break n) -> F
      | SOME (crepSem_Continue n) -> F
      | SOME (crepSem_Return v) -> res1 = SOME (loop_Result (MAP wlab_wloc v))
      | SOME (crep_Exception eid) -> res1 = SOME (loop_Exception (wl_Word eid))
      | SOME (crep_FinalFFI f) -> res1 = SOME (loop_FinalFFI f))`,
  RW[] THEN DRULE_ALL ncompile_correct THEN STRIP_TAC THEN FS[ocompile_def; o_THM] THEN
  QCASES_ON "res" THEN FS[] THEN QCASES_ON "a" THEN FS[] THEN
  TRY (FIRST_X_ASSUM(MP_TAC o SPEC `a':num` o check (is_forall o concl)) THEN
       REWRITE_TAC[] THEN NO_TAC) THEN RVEQ_TAC THEN
  QPAT_X_ASSUM "loop_evaluate _ = _"
    (MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] loop_liveProof_optimise_correct)) THEN
  SIMP[] THEN DISCH_TAC THEN QEXISTS_TAC "ck" THEN QEXISTS_TAC "t1" THEN
  ASM_REWRITE_TAC[]);;

let distinct_make_funcs = prove
 (`!crep_code:(mlstring#(num list)#(A)crep_prog)list.
     distinct_funcs (crep_to_loop_make_funcs crep_code)`,
  REWRITE_TAC[distinct_funcs_def; crep_to_loop_make_funcs_def; LET_DEF; LET_END_DEF;
              ALOOKUP_EQ_FLOOKUP] THEN REPEAT STRIP_TAC THEN
  IMP_RES_TAC ALOOKUP_MEM THEN RULE_ASSUM_TAC(REWRITE_RULE[MEM_EXISTS_EL]) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
  RULE_ASSUM_TAC(SIMP_RULE[LENGTH_MAP2; LENGTH_MAP; LENGTH_LIST_OF_SEQ]) THEN
  FS[EL_MAP2; LENGTH_MAP2; LENGTH_MAP; LENGTH_LIST_OF_SEQ; EL_MAP; EL_LIST_OF_SEQ;
     PAIR_EQ]);;

let map_map2_fst = prove
 (`!xs (ys:(B#(C list)#D)list) (h:C list->D->E).
     LENGTH (xs:A list) = LENGTH ys ==>
     MAP FST (MAP2 (\x (n,p,b). (x,list_of_seq I (LENGTH p),h p b)) xs ys) = xs`,
  LIST_INDUCT_TAC THEN GEN_TAC THEN QCASES_ON "ys" THEN
  REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ; MAP2; MAP; HD; TL; CONS_11] THEN
  REPEAT STRIP_TAC THEN PAIR_CASES_ON `a0:B#(C list)#D` THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN ASM_SIMP_TAC[FST]);;

(* HOL4 proves this by induction on xs; here by lookup_fromAList *)

let mem_lookup_fromalist_some = prove
 (`!xs n (x:A).
     ALL_DISTINCT (MAP FST xs) /\ MEM (n,x) xs ==> lookup n (fromAList xs) = SOME x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lookup_fromAList] THEN
  MATCH_MP_TAC ALOOKUP_ALL_DISTINCT_MEM THEN ASM_REWRITE_TAC[]);;

let PC2LAUX_MAP_FST_MAP2 = prove
 (`!(l1:A list) (l2:B list) (f:A->B->A#C).
     LENGTH l1 = LENGTH l2 /\ (!a b. FST (f a b) = a) ==> MAP FST (MAP2 f l1 l2) = l1`,
  LIST_INDUCT_TAC THEN GEN_TAC THEN QCASES_ON "l2" THEN
  ASM_SIMP_TAC[LENGTH; NOT_SUC; SUC_INJ; MAP2; MAP; HD; TL; CONS_11]);;

let crep_to_loopProof_first_compile_prog_all_distinct = prove
 (`!c (crep_code:(mlstring#(num list)#(A)crep_prog)list).
     ALL_DISTINCT (MAP FST (crep_to_loop_compile_prog c crep_code))`,
  REWRITE_TAC[crep_to_loop_compile_prog_def; LET_DEF; LET_END_DEF] THEN REPEAT GEN_TAC THEN
  DEP_REWRITE_TAC[PC2LAUX_MAP_FST_MAP2] THEN
  REWRITE_TAC[LENGTH_LIST_OF_SEQ; ALL_DISTINCT_GENLIST] THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN PAIR_CASES_ON `b:mlstring#(num list)#(A)crep_prog` THEN
    CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[FST];
    ARITH_TAC]);;

let code_rel2_def = cake_def
  `code_rel2 ctxt (s_code:(mlstring,num list#(A)crep_prog)fmap)
     (t_code:(num list#(A)loop_prog)spt) <=>
   crep_to_loopProof_code_rel ctxt
     (FMAP_MAP2 (\(s,n,p). (n,simp_prog p)) s_code) t_code`;;

(* HOL4: [local] *)

let ALOOKUP_EQ_EL = prove
 (`n < LENGTH (xs:(A#B)list) ==>
   FST (EL n xs) = nm ==>
   ALL_DISTINCT (MAP FST xs) ==>
   y = SND (EL n xs) ==>
   ALOOKUP xs nm = SOME y`,
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN MATCH_MP_TAC ALOOKUP_ALL_DISTINCT_EL THEN
  ASM_REWRITE_TAC[]);;

let mk_ctxt_code_imp_code_rel2 = prove
 (`!c (crep_code:(mlstring#(num list)#(A)crep_prog)list) start np.
     ALL_DISTINCT (MAP FST crep_code) /\
     ALOOKUP crep_code start = SOME ([],np) ==>
     code_rel2 (crep_to_loop_mk_ctxt c FEMPTY (crep_to_loop_make_funcs crep_code) 0)
       (alist_to_fmap crep_code)
       (fromAList (crep_to_loop_compile_prog c crep_code))`,
  RW[code_rel2_def; crep_to_loopProof_code_rel_def; crep_to_loop_mk_ctxt_def] THEN
  FS[distinct_make_funcs; FLOOKUP_FMAP_MAP2; ALOOKUP_EQ_FLOOKUP] THEN
  PAIR_CASES_ON `z:num list#(A)crep_prog` THEN
  RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV GEN_BETA_CONV)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ALOOKUP_MEM) THEN
  REWRITE_TAC[MEM_EXISTS_EL] THEN DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `i + first_name` THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN RVEQ_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o
    check (fun th -> is_eq (concl th) && is_pair (lhs (concl th)))) THEN
  CONJ_TAC THENL
   [(* the function's entry in make_funcs *)
    REWRITE_TAC[crep_to_loop_make_funcs_def; LET_DEF; LET_END_DEF; ALOOKUP_EQ_FLOOKUP] THEN
    MATCH_MP_TAC (REWRITE_RULE[IMP_IMP] (GEN_ALL ALOOKUP_EQ_EL)) THEN EXISTS_TAC `i:num` THEN
    ASM_SIMP_TAC[LENGTH_MAP2; LENGTH_MAP; LENGTH_LIST_OF_SEQ; EL_MAP2; EL_MAP;
                 EL_LIST_OF_SEQ; o_THM; PAIR_EQ] THEN
    DEP_REWRITE_TAC[PC2LAUX_MAP_FST_MAP2] THEN
    ASM_SIMP_TAC[LENGTH_MAP2; LENGTH_MAP; LENGTH_LIST_OF_SEQ];
    (* its code in compile_prog *)
    REWRITE_TAC[lookup_fromAList] THEN
    MATCH_MP_TAC (REWRITE_RULE[IMP_IMP] (GEN_ALL ALOOKUP_EQ_EL)) THEN EXISTS_TAC `i:num` THEN
    REWRITE_TAC[crep_to_loopProof_first_compile_prog_all_distinct] THEN
    REWRITE_TAC[crep_to_loop_compile_prog_def; LET_DEF; LET_END_DEF] THEN
    ASM_SIMP_TAC[LENGTH_MAP2; LENGTH_LIST_OF_SEQ; EL_MAP2; EL_LIST_OF_SEQ] THEN
    CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
    REWRITE_TAC[ocompile_def; o_THM; crep_to_loop_comp_func_def; crep_to_loop_mk_ctxt_def;
                crep_to_loopProof_ctxt_fc_def; crep_to_loop_make_vmap_def;
                MAX_LIST_i_genlist; LET_DEF; LET_END_DEF; LENGTH_LIST_OF_SEQ]]);;

(* HOL4 make_funcs_ALOOKUP_compile_prog is inside a comment in v3479 (not a *)
(* theorem of the theory)                                                   *)

let make_funcs_domain_compile_prog = prove
 (`!start lc (crep_code:(mlstring#(num list)#(A)crep_prog)list) c.
     FLOOKUP (crep_to_loop_make_funcs crep_code) start = SOME (lc,0) ==>
     lc IN domain (fromAList (crep_to_loop_compile_prog c crep_code))`,
  REWRITE_TAC[crep_to_loop_make_funcs_def; LET_DEF; LET_END_DEF; ALOOKUP_EQ_FLOOKUP;
              domain_fromAList; crep_to_loop_compile_prog_def] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP ALOOKUP_MEM) THEN REWRITE_TAC[MEM_EXISTS_EL] THEN
  SIMP_TAC[LENGTH_MAP2; LENGTH_MAP; LENGTH_LIST_OF_SEQ] THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
  FS[EL_MAP2; LENGTH_MAP2; LENGTH_MAP; LENGTH_LIST_OF_SEQ; EL_MAP; EL_LIST_OF_SEQ;
     PAIR_EQ] THEN
  DEP_REWRITE_TAC[PC2LAUX_MAP_FST_MAP2] THEN
  REWRITE_TAC[LENGTH_LIST_OF_SEQ; IN_SET_OF_LIST; MEM_GENLIST] THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN PAIR_CASES_ON `b:mlstring#(num list)#(A)crep_prog` THEN
    CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[FST];
    EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[]]);;

(* HOL4 proves this by induction on prog; here by ALOOKUP_ALL_DISTINCT_EL *)

let alookup_el_pair_eq_el = prove
 (`!(prog:(A#(B list)#C)list) start cp n.
     EL n prog = (start,[],SND (SND (EL n prog))) /\
     ALL_DISTINCT (MAP FST prog) /\ n < LENGTH prog /\
     ALOOKUP prog start = SOME ([],cp) ==>
     EL n prog = (start,[],cp)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`prog:(A#(B list)#C)list`; `n:num`] ALOOKUP_ALL_DISTINCT_EL) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(fun th ->
    if is_eq (concl th) && lhs(concl th) = `EL n (prog:(A#(B list)#C)list)`
    then ONCE_REWRITE_TAC[th] else failwith "") THEN
  REWRITE_TAC[FST; SND] THEN
  QPAT_ASSUM "ALOOKUP prog start = _" (fun th -> REWRITE_TAC[th; option_INJ; PAIR_EQ]) THEN
  MESON_TAC[]);;

let initial_prog_make_funcs_el = prove
 (`!(prog:(mlstring#(num list)#(A)crep_prog)list) start n.
     FLOOKUP (crep_to_loop_make_funcs prog) start = SOME (n + first_name,0) ==>
     (start,[],(SND o SND) (EL n prog)) = EL n prog /\ n < LENGTH prog`,
  REWRITE_TAC[crep_to_loop_make_funcs_def; LET_DEF; LET_END_DEF; ALOOKUP_EQ_FLOOKUP] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP ALOOKUP_MEM) THEN
  REWRITE_TAC[MEM_EXISTS_EL] THEN
  SIMP_TAC[LENGTH_MAP2; LENGTH_MAP; LENGTH_LIST_OF_SEQ] THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
  FS[EL_MAP2; LENGTH_MAP2; LENGTH_MAP; LENGTH_LIST_OF_SEQ; EL_MAP; EL_LIST_OF_SEQ;
     PAIR_EQ; o_THM; EQ_ADD_RCANCEL] THEN RVEQ_TAC THEN
  PAIR_CASES_ON `EL i (prog:(mlstring#(num list)#(A)crep_prog)list)` THEN FS[]);;

let crep_to_loopProof_compile_prog_distinct_params = prove
 (`!(prog:(mlstring#(num list)#(A)crep_prog)list) c.
     ALL (\(name,params,body). ALL_DISTINCT params) prog ==>
     ALL (\(name,params,body). ALL_DISTINCT params) (crep_to_loop_compile_prog c prog)`,
  REWRITE_TAC[GSYM ALL_MEM; crep_to_loop_compile_prog_def; LET_DEF; LET_END_DEF;
              MEM_EXISTS_EL] THEN
  SIMP_TAC[LENGTH_MAP2; LENGTH_LIST_OF_SEQ] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[EL_MAP2; LENGTH_LIST_OF_SEQ; EL_LIST_OF_SEQ] THEN
  PAIR_CASES_ON `EL i (prog:(mlstring#(num list)#(A)crep_prog)list)` THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[o_THM; ALL_DISTINCT_GENLIST; I_THM] THEN MESON_TAC[]);;

(* HOL4: [local] *)

let evaluate_Seq_Skip = prove
 (`loop_evaluate (loop_Seq prog loop_Skip,(s:(A,FFI)loop_state)) =
   loop_evaluate (prog,s)`,
  GEN_REWRITE_TAC LAND_CONV [loop_evaluate_def] THEN PAIRARG_TAC THEN
  REWRITE_TAC[loop_evaluate_def] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

(* HOL4: [local] *)

let evaluate_less_clock_cases = prove
 (`loop_evaluate (prog,(s:(A,FFI)loop_state)) = (res,s2) ==>
   ck <= loop_state_clock s ==>
   ?res2 s3.
     loop_evaluate (prog,loop_state_clock_fupd (K ck) s) = (res2,s3) /\
     ((res = res2 /\ (?ck2. s3 = loop_state_clock_fupd (K ck2) s2)) \/
      res2 = SOME loop_TimeOut)`,
  REPEAT STRIP_TAC THEN
  PAIR_CASES_ON `loop_evaluate (prog,loop_state_clock_fupd (K ck) (s:(A,FFI)loop_state))` THEN
  MAP_EVERY EXISTS_TAC [`p0:((A)loop_result)option`; `p1:(A,FFI)loop_state`] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `p0 = SOME (loop_TimeOut:(A)loop_result)` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`prog:(A)loop_prog`; `loop_state_clock_fupd (K ck) (s:(A,FFI)loop_state)`;
                 `p0:((A)loop_result)option`; `p1:(A,FFI)loop_state`;
                 `loop_state_clock (s:(A,FFI)loop_state) - ck`] loop_evaluate_add_clock_eq) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `loop_state_clock_fupd
                  (K (loop_state_clock (loop_state_clock_fupd (K ck) s) +
                      loop_state_clock (s:(A,FFI)loop_state) - ck))
                  (loop_state_clock_fupd (K ck) s) = s` SUBST1_TAC THENL
   [REWRITE_TAC[loop_state_component_equality] THEN SIMP[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  QEXISTS_TAC "loop_state_clock p1" THEN
  REWRITE_TAC[loop_state_component_equality] THEN SIMP[]);;

(* HOL4: [local] *)

let evaluate_twice_cases = prove
 (`loop_evaluate (prog,(s:(A,FFI)loop_state)) = (res,s2) ==>
   loop_evaluate (prog,s3) = (res2,s4) ==>
   loop_state_clock_fupd (K 0) s = loop_state_clock_fupd (K 0) s3 ==>
   (loop_state_clock s <= loop_state_clock s3 /\
    (res = SOME loop_TimeOut \/
     (res = res2 /\ (?ck. s2 = loop_state_clock_fupd (K ck) s4)))) \/
   (loop_state_clock s3 <= loop_state_clock s /\
    (res2 = SOME loop_TimeOut \/
     (res2 = res /\ (?ck. s4 = loop_state_clock_fupd (K ck) s2))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `s3 = loop_state_clock_fupd (K (loop_state_clock s3)) (s:(A,FFI)loop_state)`
    SUBST_ALL_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[loop_state_component_equality]) THEN
    REWRITE_TAC[loop_state_component_equality] THEN SIMP[];
    ALL_TAC] THEN
  ABBREV_TAC `ck = loop_state_clock (s3:(A,FFI)loop_state)` THEN
  REWRITE_TAC[(record_info "loop_state").ri_accfupds; K_THM] THEN
  ASM_CASES_TAC `loop_state_clock (s:(A,FFI)loop_state) <= ck` THENL
   [DISJ1_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`prog:(A)loop_prog`; `loop_state_clock_fupd (K ck) (s:(A,FFI)loop_state)`;
                   `res2:((A)loop_result)option`; `s4:(A,FFI)loop_state`;
                   `loop_state_clock (s:(A,FFI)loop_state)`]
          (GENL [`prog:(A)loop_prog`; `s:(A,FFI)loop_state`; `res:((A)loop_result)option`;
                 `s2:(A,FFI)loop_state`; `ck:num`] evaluate_less_clock_cases)) THEN
    ASM_REWRITE_TAC[] THEN SIMP[RECORD_SELFID_ss] THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN FS[PAIR_EQ] THEN RVEQ_TAC THEN MESON_TAC[];
    DISJ2_TAC THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`prog:(A)loop_prog`; `s:(A,FFI)loop_state`;
                   `res:((A)loop_result)option`; `s2:(A,FFI)loop_state`; `ck:num`]
          (GENL [`prog:(A)loop_prog`; `s:(A,FFI)loop_state`; `res:((A)loop_result)option`;
                 `s2:(A,FFI)loop_state`; `ck:num`] evaluate_less_clock_cases)) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN FS[PAIR_EQ] THEN RVEQ_TAC THEN ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)

(* HOL4 lines 4066-4406: evaluate_io_mono_rephrases ..                     *)
(* crep_to_loop_compile_prog_lab_min                                        *)

(* HOL4: [local]; the io_events of a run grow with the clock (crepProps and *)
(* loopProps evaluate_add_clock_io_events_mono for s with clock := k)      *)

let evaluate_io_mono_rephrases =
  CONJ
   (CAKE_SIMP_RULE[]
     (ISPECL [`exs:(A)crep_prog`; `crep_state_clock_fupd (K k) (s:(A,FFI)crep_state)`]
        crep_evaluate_add_clock_io_events_mono))
   (CAKE_SIMP_RULE[]
     (ISPECL [`exs:(A)loop_prog`; `loop_state_clock_fupd (K k) (s:(A,FFI)loop_state)`]
        loop_evaluate_add_clock_io_events_mono));;

let code_rel_evaluate_call_correct = prove
 (CASE_TERM
  `code_rel2 nctxt s_code t_code ==>
   crep_evaluate (crep_Call NONE start [],(s:(A,FFI)crep_state)) = (res,s') ==>
   crep_state_be s = loop_state_be (t:(A,FFI)loop_state) /\
   crep_state_sh_memaddrs s = loop_state_sh_mdomain t /\
   crep_state_memaddrs s = loop_state_mdomain t /\
   crep_state_clock s = loop_state_clock t /\
   crep_state_ffi s = loop_state_ffi t /\
   crep_state_base_addr s = loop_state_base_addr t /\
   crep_state_top_addr s = loop_state_top_addr t /\
   mem_rel (crep_state_memory s) (loop_state_memory t) (crep_state_memaddrs s) /\
   crep_to_loopProof_globals_rel (crep_state_globals s) (loop_state_globals t) /\
   crep_state_locals s = FEMPTY /\
   crep_state_code s = s_code /\ loop_state_code t = t_code ==>
   FLOOKUP (crep_to_loop_make_funcs crep_code) start =
     SOME (crep_to_loop_find_lab nctxt start,0) ==>
   crep_to_loop_find_lab nctxt start = lc /\
   crep_state_code s = alist_to_fmap crep_code /\
   crep_to_loop_context_funcs nctxt = crep_to_loop_make_funcs crep_code /\
   ALOOKUP crep_code start = SOME ([],prog) /\
   distinct_vars (crep_to_loop_context_vars nctxt) /\
   crep_to_loopProof_ctxt_max (crep_to_loop_context_vmax nctxt)
     (crep_to_loop_context_vars nctxt) ==>
   ~(res = SOME crep_Error) ==>
   ?k res' t'.
     loop_evaluate (loop_Call NONE (SOME (crep_to_loop_find_lab nctxt start)) [] NONE,
                    loop_state_clock_fupd (K (loop_state_clock t + k)) t) = (res',t') /\
     crep_to_loopProof_state_rel s' t' /\
     res' = (match res with
               NONE -> NONE
             | SOME (crepSem_Break n) -> SOME (loopSem_Break n)
             | SOME (crepSem_Continue n) -> SOME (loopSem_Continue n)
             | SOME (crepSem_Return vs) -> SOME (loop_Result (MAP wlab_wloc vs))
             | SOME (crep_Exception eid) -> SOME (loop_Exception (wl_Word eid))
             | SOME crep_TimeOut -> SOME loop_TimeOut
             | SOME (crep_FinalFFI f) -> SOME (loop_FinalFFI f)
             | SOME crep_Error -> SOME loop_Error)`,
  RW[] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] simp_prog_correct)) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[simp_prog_def; simp_exp_def; MAP; LET_DEF; LET_END_DEF] THEN
  CASE_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] ncompile_correct)) THEN
  DISCH_THEN(MP_TAC o SPECL [`t:(A,FFI)loop_state`; `nctxt:crep_to_loop_context`;
                             `LN:num_set`]) THEN
  ASM_REWRITE_TAC[] THEN
  FS[crep_to_loopProof_state_rel_def; crep_to_loopProof_locals_rel_def; code_rel2_def;
     FLOOKUP_EMPTY; domain_def; EMPTY_SUBSET] THEN
  DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN `t1:(A,FFI)loop_state` STRIP_ASSUME_TAC)) THEN
  QPAT_X_ASSUM "loop_evaluate _ = _"
    (MP_TAC o CASE_REWRITE_RULE[] o
     REWRITE_RULE[crep_to_loop_compile_def; LET_DEF; LET_END_DEF; CONJUNCT1 compile_exps_alt;
                  gen_temps_def; LENGTH; list_of_seq; MAP2; APPEND; loop_nested_seq_def]) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; LENGTH; list_of_seq; MAP2; APPEND; loop_nested_seq_def;
              evaluate_Seq_Skip] THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; LENGTH; list_of_seq; MAP2; APPEND; loop_nested_seq_def;
              evaluate_Seq_Skip] THEN
  DISCH_TAC THEN MAP_EVERY QEXISTS_TAC ["ck"; "t1"] THEN ASM_REWRITE_TAC[]);;

let crep_to_loopProof_semantics_run_res_INDUCT,
    crep_to_loopProof_semantics_run_res_RECURSION = cake_type
  "crep_to_loopProof_semantics_run_res =
     crep_to_loopProof_RunError
   | crep_to_loopProof_CompleteResult A
   | crep_to_loopProof_Incomplete";;

let crep_to_loopProof_semantics_wrapper_def = cake_def
  `crep_to_loopProof_semantics_wrapper f =
     if ?k v. f k = (crep_to_loopProof_RunError,v) then Fail
     else match (some res. ?k r ev. f k = (crep_to_loopProof_CompleteResult r,ev) /\
                                    res = Terminate r ev) with
            SOME res -> res
          | NONE -> Diverge (build_lprefix_lub (IMAGE (llist_fromList o SND o f) (:num)))`;;

(* crep_sem_is_wrapper and loop_sem_is_wrapper: a semantics of the form of  *)
(* crep_semantics and loop_semantics is the wrapper of the run function    *)
(* (g ## io) o E (HOL4 proves each with COND_CONG and option_case_cong)     *)

let PC2LAUX_wrapper_lemma = prove
 (CASE_TERM
  `!(E:num->R#S) (M:R->bool) (Mo:R->outcome->bool)
     (g:R->(outcome)crep_to_loopProof_semantics_run_res) (io:S->(io_event)list).
     (!r. M r <=> g r = crep_to_loopProof_RunError) /\
     (!r outcome. Mo r outcome <=> g r = crep_to_loopProof_CompleteResult outcome) ==>
     (if ?k. M (FST (E k)) then Fail
      else match (some res. ?k t r outcome.
                    E k = (r,t) /\ Mo r outcome /\ res = Terminate outcome (io t)) with
             SOME res -> res
           | NONE -> Diverge (build_lprefix_lub
                       (IMAGE (\k. llist_fromList (io (SND (E k)))) (:num)))) =
     crep_to_loopProof_semantics_wrapper ((g ## io) o E)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[crep_to_loopProof_semantics_wrapper_def; o_THM; PAIR_MAP_DEF; PAIR_EQ] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(?k v. (g:R->(outcome)crep_to_loopProof_semantics_run_res) (FST ((E:num->R#S) k)) =
           crep_to_loopProof_RunError /\ (io:S->(io_event)list) (SND (E k)) = v) <=>
    (?k. g (FST (E k)) = crep_to_loopProof_RunError)` SUBST1_TAC THENL
   [MESON_TAC[]; ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `llist_fromList o SND o
    (\p. (g:R->(outcome)crep_to_loopProof_semantics_run_res) (FST p),
         (io:S->(io_event)list) (SND p)) o (E:num->R#S) =
    (\k. llist_fromList (io (SND (E k))))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL
   [MAP_EVERY EXISTS_TAC [`k:num`; `outcome:outcome`; `io (t:S):(io_event)list`] THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_eq o concl) o
      check (fun th -> is_pair (rhs (concl th)))) THEN
    ASM_REWRITE_TAC[FST; SND];
    MAP_EVERY EXISTS_TAC [`k:num`; `SND ((E:num->R#S) k)`; `FST ((E:num->R#S) k)`;
                          `r:outcome`] THEN
    ASM_REWRITE_TAC[PAIR]]);;

let crep_sem_is_wrapper = prove
 (CASE_TERM
  `crep_semantics (s:(A,FFI)crep_state) start =
   let prog = crep_Call NONE start [] in
   crep_to_loopProof_semantics_wrapper
     (((\res. match res with
                SOME crep_TimeOut -> crep_to_loopProof_Incomplete
              | SOME (crep_FinalFFI e) -> crep_to_loopProof_CompleteResult (FFI_outcome e)
              | SOME (crepSem_Return _) -> crep_to_loopProof_CompleteResult Success
              | _ -> crep_to_loopProof_RunError) ##
       (\s. ffi_state_io_events (crep_state_ffi s))) o
      (\k. crep_evaluate (prog,crep_state_clock_fupd (K k) s)))`,
  REWRITE_TAC[crep_semantics_def; LET_DEF; LET_END_DEF] THEN
  MATCH_MP_TAC (BETA_RULE (ISPECL
   [`\k. crep_evaluate (crep_Call NONE start [],
                        crep_state_clock_fupd (K k) (s:(A,FFI)crep_state))`;
    CASE_TERM `\r:((A)crep_result)option. match r with
                 SOME crep_TimeOut -> F
               | SOME (crep_FinalFFI _) -> F
               | SOME (crepSem_Return _) -> F
               | _ -> T`;
    CASE_TERM `\(r:((A)crep_result)option) outcome. match r with
                 SOME (crep_FinalFFI e) -> outcome = FFI_outcome e
               | SOME (crepSem_Return _) -> outcome = Success
               | _ -> F`;
    CASE_TERM `\res:((A)crep_result)option. match res with
                 SOME crep_TimeOut -> crep_to_loopProof_Incomplete
               | SOME (crep_FinalFFI e) -> crep_to_loopProof_CompleteResult (FFI_outcome e)
               | SOME (crepSem_Return _) -> crep_to_loopProof_CompleteResult Success
               | _ -> crep_to_loopProof_RunError`;
    `\s:(A,FFI)crep_state. ffi_state_io_events (crep_state_ffi s)`]
   PC2LAUX_wrapper_lemma)) THEN
  CONJ_TAC THEN REPEAT GEN_TAC THEN QCASES_ON "r" THEN
  CASE_REWRITE_TAC[] THEN TRY (QCASES_ON "a") THEN CASE_REWRITE_TAC[] THEN
  SIMP[] THEN MESON_TAC[]);;
let loop_sem_is_wrapper = prove
 (CASE_TERM
  `loop_semantics (s:(A,FFI)loop_state) start =
   let prog = loop_Call NONE (SOME start) [] NONE in
   crep_to_loopProof_semantics_wrapper
     (((\res. match res with
                SOME loop_TimeOut -> crep_to_loopProof_Incomplete
              | SOME (loop_FinalFFI e) -> crep_to_loopProof_CompleteResult (FFI_outcome e)
              | SOME (loop_Result _) -> crep_to_loopProof_CompleteResult Success
              | _ -> crep_to_loopProof_RunError) ##
       (\s. ffi_state_io_events (loop_state_ffi s))) o
      (\k. loop_evaluate (prog,loop_state_clock_fupd (K k) s)))`,
  REWRITE_TAC[loop_semantics_def; LET_DEF; LET_END_DEF] THEN
  MATCH_MP_TAC (BETA_RULE (ISPECL
   [`\k. loop_evaluate (loop_Call NONE (SOME start) [] NONE,
                        loop_state_clock_fupd (K k) (s:(A,FFI)loop_state))`;
    CASE_TERM `\r:((A)loop_result)option. match r with
                 SOME loop_TimeOut -> F
               | SOME (loop_FinalFFI _) -> F
               | SOME (loop_Result _) -> F
               | _ -> T`;
    CASE_TERM `\(r:((A)loop_result)option) outcome. match r with
                 SOME (loop_FinalFFI e) -> outcome = FFI_outcome e
               | SOME (loop_Result _) -> outcome = Success
               | _ -> F`;
    CASE_TERM `\res:((A)loop_result)option. match res with
                 SOME loop_TimeOut -> crep_to_loopProof_Incomplete
               | SOME (loop_FinalFFI e) -> crep_to_loopProof_CompleteResult (FFI_outcome e)
               | SOME (loop_Result _) -> crep_to_loopProof_CompleteResult Success
               | _ -> crep_to_loopProof_RunError`;
    `\s:(A,FFI)loop_state. ffi_state_io_events (loop_state_ffi s)`]
   PC2LAUX_wrapper_lemma)) THEN
  CONJ_TAC THEN REPEAT GEN_TAC THEN QCASES_ON "r" THEN
  CASE_REWRITE_TAC[] THEN TRY (QCASES_ON "a") THEN CASE_REWRITE_TAC[] THEN
  SIMP[] THEN MESON_TAC[]);;

(* semantics_wrapper_eq: HOL4's proof splits on the value of the wrapper   *)
(* of absf (Terminate or Diverge); here the two cases are the helpers      *)
(* PC2LAUX_wrapper_terminate (a run with a complete result fixes the       *)
(* wrapper's value) and PC2LAUX_wrapper_diverge (only incomplete runs),    *)
(* with PC2LAUX_wrapper_chain for the lprefix chains of the io events      *)

let PC2LAUX_SOME_INTRO_TAC : tactic = fun (asl,w as g) ->
  let t = find_term (fun t -> is_comb t &&
                       (try fst(dest_const(rator t)) = "some" with Failure _ -> false)) w in
  let v = genvar(type_of t) in
  let th = BETA_CONV (mk_comb(mk_abs(v,subst [v,t] w),t)) in
  (CONV_TAC(K(SYM th)) THEN MATCH_MP_TAC some_intro THEN
   CONV_TAC(DEPTH_CONV BETA_CONV)) g;;

let PC2LAUX_wrapper_terminate = prove
 (`!f k0 r0 ev0.
     f k0 = (crep_to_loopProof_CompleteResult r0,ev0) /\
     (!k k' r ev. f k = (r,ev) ==> ~(r = crep_to_loopProof_Incomplete) ==>
                  f (k + k') = (r,ev)) ==>
     crep_to_loopProof_semantics_wrapper f = Terminate r0 ev0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!k r v. (f:num->(outcome)crep_to_loopProof_semantics_run_res#(io_event)list) k = (r,v)
            ==> (r,v) = f k0 \/ r = crep_to_loopProof_Incomplete`
    ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN DISJ_CASES_TAC(SPECL [`k0:num`; `k:num`] LE_CASES) THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `d:num` SUBST_ALL_TAC o REWRITE_RULE[LE_EXISTS]) THENL
     [DISJ1_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL
        [`k0:num`; `d:num`;
         `crep_to_loopProof_CompleteResult r0:(outcome)crep_to_loopProof_semantics_run_res`;
         `ev0:(io_event)list`]) THEN
      ASM_REWRITE_TAC[distinctness "crep_to_loopProof_semantics_run_res"] THEN
      ASM_MESON_TAC[];
      ASM_CASES_TAC
        `r = crep_to_loopProof_Incomplete:(outcome)crep_to_loopProof_semantics_run_res` THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL
        [`k:num`; `d:num`; `r:(outcome)crep_to_loopProof_semantics_run_res`;
         `v:(io_event)list`]) THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[crep_to_loopProof_semantics_wrapper_def] THEN COND_CASES_TAC THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `v:(io_event)list` ASSUME_TAC)) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
      [`k:num`; `crep_to_loopProof_RunError:(outcome)crep_to_loopProof_semantics_run_res`;
       `v:(io_event)list`]) THEN
    ASM_REWRITE_TAC[PAIR_EQ; distinctness "crep_to_loopProof_semantics_run_res"];
    PC2LAUX_SOME_INTRO_TAC THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL
        [`k:num`;
         `crep_to_loopProof_CompleteResult r:(outcome)crep_to_loopProof_semantics_run_res`;
         `ev:(io_event)list`]) THEN
      ASM_REWRITE_TAC[PAIR_EQ; distinctness "crep_to_loopProof_semantics_run_res";
                      injectivity "crep_to_loopProof_semantics_run_res"] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[option_CASE];
      DISCH_THEN(MP_TAC o SPEC `Terminate r0 ev0`) THEN REWRITE_TAC[] THEN
      ASM_MESON_TAC[]]]);;

let PC2LAUX_wrapper_diverge = prove
 (`!f. (!k. FST (f k) = crep_to_loopProof_Incomplete) ==>
       crep_to_loopProof_semantics_wrapper f =
       Diverge (build_lprefix_lub (IMAGE (llist_fromList o SND o f) (:num)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[crep_to_loopProof_semantics_wrapper_def] THEN
  SUBGOAL_THEN `!k r ev. ~((f:num->(outcome)crep_to_loopProof_semantics_run_res#(io_event)list) k =
                           (r,ev)) \/ r = crep_to_loopProof_Incomplete` MP_TAC THENL
   [REPEAT GEN_TAC THEN
    ASM_CASES_TAC
      `(f:num->(outcome)crep_to_loopProof_semantics_run_res#(io_event)list) k = (r,ev)` THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[FST];
    ALL_TAC] THEN
  REWRITE_TAC[TAUT `~a \/ b <=> a ==> b`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(?k v. (f:num->(outcome)crep_to_loopProof_semantics_run_res#(io_event)list) k =
                        (crep_to_loopProof_RunError,v))` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_MESON_TAC[distinctness "crep_to_loopProof_semantics_run_res"]; ALL_TAC] THEN
  SUBGOAL_THEN `!k r ev. ~((f:num->(outcome)crep_to_loopProof_semantics_run_res#(io_event)list) k =
                           (crep_to_loopProof_CompleteResult r,ev))` ASSUME_TAC THENL
   [ASM_MESON_TAC[distinctness "crep_to_loopProof_semantics_run_res"]; ALL_TAC] THEN
  ASM_REWRITE_TAC[some_F; option_CASE]);;

let PC2LAUX_wrapper_chain = prove
 (`!f:num->(outcome)crep_to_loopProof_semantics_run_res#(io_event)list.
     (!k k' ev. f (k + k') = (crep_to_loopProof_Incomplete,ev) ==>
                ?r' ev'. f k = (r',ev') /\ ev' <<= ev) /\
     (!k. FST (f k) = crep_to_loopProof_Incomplete) ==>
     lprefix_chain (IMAGE (llist_fromList o SND o f) (:num))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!k1 d. SND ((f:num->(outcome)crep_to_loopProof_semantics_run_res#(io_event)list) k1)
                       <<= SND (f (k1 + d))` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL
      [`k1:num`; `d:num`; `SND ((f:num->(outcome)crep_to_loopProof_semantics_run_res#(io_event)list)
                                (k1 + d))`]) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[PAIR]; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[SND];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k1 k2. SND ((f:num->(outcome)crep_to_loopProof_semantics_run_res#(io_event)list) k1)
            <<= SND (f k2) \/ SND (f k2) <<= SND (f k1)` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISJ_CASES_TAC(SPECL [`k1:num`; `k2:num`] LE_CASES) THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `d:num` SUBST1_TAC o REWRITE_RULE[LE_EXISTS]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IMAGE_o] THEN MATCH_MP_TAC prefix_chain_lprefix_chain THEN
  REWRITE_TAC[prefix_chain_def; IN_IMAGE; IN_UNIV; o_THM] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let crep_to_loopProof_semantics_wrapper_eq = prove
 (`~(crep_to_loopProof_semantics_wrapper absf = Fail) ==>
   (!k r ev. absf k = (r,ev) /\ ~(r = crep_to_loopProof_RunError) ==>
             ?k'. concf (k + k') = (r,ev)) ==>
   (!k k' r ev. concf k = (r,ev) ==> ~(r = crep_to_loopProof_Incomplete) ==>
                concf (k + k') = (r,ev)) ==>
   (!k k' r ev. absf k = (r,ev) ==> ~(r = crep_to_loopProof_Incomplete) ==>
                absf (k + k') = (r,ev)) ==>
   (!k k' ev. absf (k + k') = (crep_to_loopProof_Incomplete,ev) ==>
              ?r' ev'. absf k = (r',ev') /\ ev' <<= ev) ==>
   (!k k' ev. concf (k + k') = (crep_to_loopProof_Incomplete,ev) ==>
              ?r' ev'. concf k = (r',ev') /\ ev' <<= ev) ==>
   crep_to_loopProof_semantics_wrapper concf = crep_to_loopProof_semantics_wrapper absf`,
  DISCH_THEN(LABEL_TAC "nf") THEN DISCH_THEN(LABEL_TAC "ac") THEN
  DISCH_THEN(LABEL_TAC "cm") THEN DISCH_THEN(LABEL_TAC "am") THEN
  DISCH_THEN(LABEL_TAC "ai") THEN DISCH_THEN(LABEL_TAC "ci") THEN
  SUBGOAL_THEN
   `!k v. ~((absf:num->(outcome)crep_to_loopProof_semantics_run_res#(io_event)list) k =
            (crep_to_loopProof_RunError,v))` (LABEL_TAC "ne") THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN REMOVE_THEN "nf" MP_TAC THEN
    REWRITE_TAC[crep_to_loopProof_semantics_wrapper_def] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC
   `?k r ev. (absf:num->(outcome)crep_to_loopProof_semantics_run_res#(io_event)list) k =
             (crep_to_loopProof_CompleteResult r,ev)` THENL
   [(* Terminate *)
    FIRST_X_ASSUM(X_CHOOSE_THEN `k0:num` (X_CHOOSE_THEN `r0:outcome`
      (X_CHOOSE_THEN `ev0:(io_event)list` ASSUME_TAC))) THEN
    MP_TAC(ISPECL [`absf:num->(outcome)crep_to_loopProof_semantics_run_res#(io_event)list`;
                   `k0:num`; `r0:outcome`; `ev0:(io_event)list`] PC2LAUX_wrapper_terminate) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN USE_THEN "am" ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    REMOVE_THEN "ac" (MP_TAC o SPECL [`k0:num`;
      `crep_to_loopProof_CompleteResult r0:(outcome)crep_to_loopProof_semantics_run_res`;
      `ev0:(io_event)list`]) THEN
    ASM_REWRITE_TAC[distinctness "crep_to_loopProof_semantics_run_res"] THEN
    DISCH_THEN(X_CHOOSE_TAC `k':num`) THEN
    MATCH_MP_TAC PC2LAUX_wrapper_terminate THEN EXISTS_TAC `k0 + k':num` THEN
    ASM_REWRITE_TAC[];
    (* Diverge: every run of absf, and so of concf, is incomplete *)
    SUBGOAL_THEN
     `!k. FST ((absf:num->(outcome)crep_to_loopProof_semantics_run_res#(io_event)list) k) =
          crep_to_loopProof_Incomplete` (LABEL_TAC "afi") THENL
     [GEN_TAC THEN
      MP_TAC(ISPEC
        `FST ((absf:num->(outcome)crep_to_loopProof_semantics_run_res#(io_event)list) k)`
        (cases "crep_to_loopProof_semantics_run_res")) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[PAIR];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!k. FST ((concf:num->(outcome)crep_to_loopProof_semantics_run_res#(io_event)list) k) =
          crep_to_loopProof_Incomplete` (LABEL_TAC "cfi") THENL
     [GEN_TAC THEN
      USE_THEN "ac" (MP_TAC o SPECL [`k:num`;
        `crep_to_loopProof_Incomplete:(outcome)crep_to_loopProof_semantics_run_res`;
        `SND ((absf:num->(outcome)crep_to_loopProof_semantics_run_res#(io_event)list) k)`]) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[distinctness "crep_to_loopProof_semantics_run_res"] THEN
        ASM_MESON_TAC[PAIR];
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_TAC `k':num`) THEN
      ASM_CASES_TAC
       `FST ((concf:num->(outcome)crep_to_loopProof_semantics_run_res#(io_event)list) k) =
        crep_to_loopProof_Incomplete` THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "cm" (MP_TAC o SPECL [`k:num`; `k':num`;
        `FST ((concf:num->(outcome)crep_to_loopProof_semantics_run_res#(io_event)list) k)`;
        `SND ((concf:num->(outcome)crep_to_loopProof_semantics_run_res#(io_event)list) k)`]) THEN
      REWRITE_TAC[PAIR] THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o AP_TERM
        `FST:(outcome)crep_to_loopProof_semantics_run_res#(io_event)list->
             (outcome)crep_to_loopProof_semantics_run_res`) THEN
      ASM_REWRITE_TAC[FST];
      ALL_TAC] THEN
    ASM_SIMP_TAC[PC2LAUX_wrapper_diverge] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC IMP_build_lprefix_lub_EQ THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC PC2LAUX_wrapper_chain THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC PC2LAUX_wrapper_chain THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[lprefix_rel_def; FORALL_IN_IMAGE; EXISTS_IN_IMAGE; IN_UNIV; o_THM;
                  LPREFIX_fromList; from_toList; option_CASE] THEN
      X_GEN_TAC `k:num` THEN EXISTS_TAC `k:num` THEN
      USE_THEN "ac" (MP_TAC o SPECL [`k:num`;
        `crep_to_loopProof_Incomplete:(outcome)crep_to_loopProof_semantics_run_res`;
        `SND ((absf:num->(outcome)crep_to_loopProof_semantics_run_res#(io_event)list) k)`]) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[distinctness "crep_to_loopProof_semantics_run_res"] THEN
        ASM_MESON_TAC[PAIR];
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_TAC `k':num`) THEN
      USE_THEN "ci" (MP_TAC o SPECL [`k:num`; `k':num`;
        `SND ((absf:num->(outcome)crep_to_loopProof_semantics_run_res#(io_event)list) k)`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[SND];
      REWRITE_TAC[lprefix_rel_def; FORALL_IN_IMAGE; EXISTS_IN_IMAGE; IN_UNIV; o_THM;
                  LPREFIX_fromList; from_toList; option_CASE] THEN
      X_GEN_TAC `k:num` THEN
      USE_THEN "ac" (MP_TAC o SPECL [`k:num`;
        `crep_to_loopProof_Incomplete:(outcome)crep_to_loopProof_semantics_run_res`;
        `SND ((absf:num->(outcome)crep_to_loopProof_semantics_run_res#(io_event)list) k)`]) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[distinctness "crep_to_loopProof_semantics_run_res"] THEN
        ASM_MESON_TAC[PAIR];
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_TAC `k':num`) THEN EXISTS_TAC `k + k':num` THEN
      ASM_REWRITE_TAC[SND; IS_PREFIX_REFL]]]);;

(* HOL4: [local] *)

let PAIR_MAP_EQ_UNCURRY = prove
 (`((f:A->C) ## (g:B->D)) = (\(x,y). (f x,g y))`,
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; PAIR_MAP_THM] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[]);;

(* state_rel_imp_semantics: both semantics are wrappers (crep_sem_is_wrapper, *)
(* loop_sem_is_wrapper) of run functions (g ## io) o E; the hypotheses of  *)
(* semantics_wrapper_eq about clock monotonicity and io prefixes hold for  *)
(* every such run function whose runs grow with the clock                  *)

let PC2LAUX_run_mono = prove
 (`!(E:num->R#S) (g:R->(outcome)crep_to_loopProof_semantics_run_res)
    (io:S->(io_event)list) (TO:R).
     g TO = crep_to_loopProof_Incomplete /\
     (!k k'. ~(FST (E k) = TO) ==>
             FST (E (k + k')) = FST (E k) /\ io (SND (E (k + k'))) = io (SND (E k))) ==>
     !k k' r ev. ((g ## io) o E) k = (r,ev) ==> ~(r = crep_to_loopProof_Incomplete) ==>
                 ((g ## io) o E) (k + k') = (r,ev)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[o_THM; PAIR_MAP_DEF; PAIR_EQ] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`; `k':num`]) THEN ANTS_TAC THENL
   [ASM_MESON_TAC[]; STRIP_TAC THEN ASM_REWRITE_TAC[]]);;

let PC2LAUX_run_prefix = prove
 (`!(E:num->R#S) (g:R->(outcome)crep_to_loopProof_semantics_run_res)
    (io:S->(io_event)list).
     (!k k'. io (SND (E k)) <<= io (SND (E (k + k')))) ==>
     !k k' ev. ((g ## io) o E) (k + k') = (crep_to_loopProof_Incomplete,ev) ==>
               ?r' ev'. ((g ## io) o E) k = (r',ev') /\ ev' <<= ev`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[o_THM; PAIR_MAP_DEF; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN MAP_EVERY EXISTS_TAC
   [`(g:R->(outcome)crep_to_loopProof_semantics_run_res) (FST ((E:num->R#S) k))`;
    `(io:S->(io_event)list) (SND ((E:num->R#S) k))`] THEN
  ASM_MESON_TAC[]);;

let PC2LAUX_crep_clock_prop = prove
 (`!p (s:(A,FFI)crep_state) k k'.
     ~(FST (crep_evaluate (p,crep_state_clock_fupd (K k) s)) = SOME crep_TimeOut) ==>
     FST (crep_evaluate (p,crep_state_clock_fupd (K (k + k')) s)) =
     FST (crep_evaluate (p,crep_state_clock_fupd (K k) s)) /\
     ffi_state_io_events (crep_state_ffi (SND (crep_evaluate
       (p,crep_state_clock_fupd (K (k + k')) s)))) =
     ffi_state_io_events (crep_state_ffi (SND (crep_evaluate
       (p,crep_state_clock_fupd (K k) s))))`,
  REPEAT GEN_TAC THEN
  PAIR_CASES_ON `crep_evaluate (p,crep_state_clock_fupd (K k) (s:(A,FFI)crep_state))` THEN
  REWRITE_TAC[FST; SND] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`p:(A)crep_prog`; `crep_state_clock_fupd (K k) (s:(A,FFI)crep_state)`;
                 `p0:((A)crep_result)option`; `p1:(A,FFI)crep_state`; `k':num`]
         crep_evaluate_add_clock_eq) THEN
  ASM_REWRITE_TAC[] THEN SIMP[] THEN DISCH_THEN SUBST1_TAC THEN SIMP[]);;

let PC2LAUX_loop_clock_prop = prove
 (`!p (s:(A,FFI)loop_state) k k'.
     ~(FST (loop_evaluate (p,loop_state_clock_fupd (K k) s)) = SOME loop_TimeOut) ==>
     FST (loop_evaluate (p,loop_state_clock_fupd (K (k + k')) s)) =
     FST (loop_evaluate (p,loop_state_clock_fupd (K k) s)) /\
     ffi_state_io_events (loop_state_ffi (SND (loop_evaluate
       (p,loop_state_clock_fupd (K (k + k')) s)))) =
     ffi_state_io_events (loop_state_ffi (SND (loop_evaluate
       (p,loop_state_clock_fupd (K k) s))))`,
  REPEAT GEN_TAC THEN
  PAIR_CASES_ON `loop_evaluate (p,loop_state_clock_fupd (K k) (s:(A,FFI)loop_state))` THEN
  REWRITE_TAC[FST; SND] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`p:(A)loop_prog`; `loop_state_clock_fupd (K k) (s:(A,FFI)loop_state)`;
                 `p0:((A)loop_result)option`; `p1:(A,FFI)loop_state`; `k':num`]
         loop_evaluate_add_clock_eq) THEN
  ASM_REWRITE_TAC[] THEN SIMP[] THEN DISCH_THEN SUBST1_TAC THEN SIMP[]);;

let crep_to_loopProof_state_rel_imp_semantics = prove
 (`!(s:(A,FFI)crep_state) (t:(A,FFI)loop_state)
     (crep_code:(mlstring#(num list)#(A)crep_prog)list) start lc c.
     crep_state_memaddrs s = loop_state_mdomain t /\
     crep_state_be s = loop_state_be t /\
     crep_state_sh_memaddrs s = loop_state_sh_mdomain t /\
     crep_state_ffi s = loop_state_ffi t /\
     crep_state_base_addr s = loop_state_base_addr t /\
     crep_state_top_addr s = loop_state_top_addr t /\
     mem_rel (crep_state_memory s) (loop_state_memory t) (crep_state_memaddrs s) /\
     crep_to_loopProof_globals_rel (crep_state_globals s) (loop_state_globals t) /\
     ALL_DISTINCT (MAP FST crep_code) /\
     crep_state_code s = alist_to_fmap crep_code /\
     loop_state_code t = fromAList (crep_to_loop_compile_prog c crep_code) /\
     crep_state_locals s = FEMPTY /\
     FLOOKUP (crep_to_loop_make_funcs crep_code) start = SOME (lc,0) /\
     ~(crep_semantics s start = Fail) ==>
     loop_semantics t lc = crep_semantics s start`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `?prog. ALOOKUP (crep_code:(mlstring#(num list)#(A)crep_prog)list) start =
                        SOME ([],prog)` THENL
   [ALL_TAC;
    (* no code with no parameters for start: then the semantics is Fail *)
    QPAT_X_ASSUM "~(crep_semantics _ _ = Fail)" MP_TAC THEN REWRITE_TAC[] THEN
    REWRITE_TAC[crep_semantics_def; LET_DEF; LET_END_DEF] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `0` o REWRITE_RULE[NOT_EXISTS_THM]) THEN
    ONCE_REWRITE_TAC[crep_evaluate_def] THEN
    ASM_REWRITE_TAC[OPT_MMAP_def; crep_lookup_code_def; LENGTH; ALOOKUP_EQ_FLOOKUP] THEN
    SIMP[] THEN
    QCASES_ON "ALOOKUP (crep_code:(mlstring#(num list)#(A)crep_prog)list) start" THEN
    CASE_REWRITE_TAC[] THEN TRY (PAIR_CASES_ON `a:num list#(A)crep_prog`) THEN
    CASE_REWRITE_TAC[] THEN TRY COND_CASES_TAC THEN CASE_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC) THEN RVEQ_TAC THEN ASM_MESON_TAC[]] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `prog:(A)crep_prog`) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[crep_sem_is_wrapper; LET_DEF; LET_END_DEF]) THEN
  REWRITE_TAC[crep_sem_is_wrapper; loop_sem_is_wrapper; LET_DEF; LET_END_DEF] THEN
  IRULE crep_to_loopProof_semantics_wrapper_eq THEN ASM_REWRITE_TAC[] THENL
   [(* a crep run that is no error is matched by a loop run with more clock *)
    REWRITE_TAC[o_THM; PAIR_MAP_DEF; PAIR_EQ] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    PAIR_CASES_ON `crep_evaluate (crep_Call NONE start [],
                                  crep_state_clock_fupd (K k) (s:(A,FFI)crep_state))` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[FST; SND]) THEN
    MP_TAC(SPECL [`c:architecture`; `crep_code:(mlstring#(num list)#(A)crep_prog)list`;
                  `start:mlstring`; `prog:(A)crep_prog`] mk_ctxt_code_imp_code_rel2) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (INST
      [`crep_state_clock_fupd (K k) (s:(A,FFI)crep_state)`,`s:(A,FFI)crep_state`;
       `p0:((A)crep_result)option`,`res:((A)crep_result)option`;
       `p1:(A,FFI)crep_state`,`s':(A,FFI)crep_state`;
       `loop_state_clock_fupd (K k) (t:(A,FFI)loop_state)`,`t:(A,FFI)loop_state`]
      code_rel_evaluate_call_correct)) THEN
    ASM_REWRITE_TAC[] THEN
    SIMP[crep_to_loop_find_lab_def; crep_to_loop_mk_ctxt_def; distinct_vars_def;
         crep_to_loopProof_ctxt_max_def; FLOOKUP_EMPTY] THEN
    CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ANTS_TAC THENL
     [DISCH_TAC THEN
      UNDISCH_TAC
        `~(r = crep_to_loopProof_RunError:(outcome)crep_to_loopProof_semantics_run_res)` THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o
        check (fun th -> rhs(concl th) = `r:(outcome)crep_to_loopProof_semantics_run_res`)) THEN
      ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `k':num` (X_CHOOSE_THEN `t':(A,FFI)loop_state`
      STRIP_ASSUME_TAC)) THEN
    QEXISTS_TAC "k'" THEN ASM_REWRITE_TAC[FST; SND] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o
        check (fun th -> rhs(concl th) = `r:(outcome)crep_to_loopProof_semantics_run_res`)) THEN
      QCASES_ON "p0" THEN CASE_REWRITE_TAC[] THEN TRY (QCASES_ON "a") THEN
      CASE_REWRITE_TAC[];
      FIRST_X_ASSUM(SUBST1_TAC o SYM o
        check (fun th -> rhs(concl th) = `ev:(io_event)list`)) THEN
      FS[crep_to_loopProof_state_rel_def]];
    (* the loop runs, the crep runs: complete results stay with more clock *)
    MATCH_MP_TAC PC2LAUX_run_mono THEN
    EXISTS_TAC `SOME loop_TimeOut:((A)loop_result)option` THEN BETA_TAC THEN
    CONJ_TAC THENL [CASE_REWRITE_TAC[]; MATCH_ACCEPT_TAC PC2LAUX_loop_clock_prop];
    MATCH_MP_TAC PC2LAUX_run_mono THEN
    EXISTS_TAC `SOME crep_TimeOut:((A)crep_result)option` THEN BETA_TAC THEN
    CONJ_TAC THENL [CASE_REWRITE_TAC[]; MATCH_ACCEPT_TAC PC2LAUX_crep_clock_prop];
    (* the io events grow with the clock *)
    MATCH_MP_TAC PC2LAUX_run_prefix THEN BETA_TAC THEN REPEAT GEN_TAC THEN
    MATCH_ACCEPT_TAC (GEN_ALL (CONJUNCT1 evaluate_io_mono_rephrases));
    MATCH_MP_TAC PC2LAUX_run_prefix THEN BETA_TAC THEN REPEAT GEN_TAC THEN
    MATCH_ACCEPT_TAC (GEN_ALL (CONJUNCT2 evaluate_io_mono_rephrases))]);;

(* first_name offset *)

let crep_to_loop_compile_prog_lab_min = prove
 (`crep_to_loop_compile_prog c (cprog:(mlstring#(num list)#(A)crep_prog)list) = lprog ==>
   ALL (\prog. 60 <= FST prog) lprog`,
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[GSYM ALL_MEM; crep_to_loop_compile_prog_def; LET_DEF; LET_END_DEF;
              MEM_EXISTS_EL] THEN
  SIMP_TAC[LENGTH_MAP2; LENGTH_LIST_OF_SEQ] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[EL_MAP2; LENGTH_LIST_OF_SEQ; EL_LIST_OF_SEQ] THEN
  PAIR_CASES_ON `EL i (cprog:(mlstring#(num list)#(A)crep_prog)list)` THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[FST; first_name_def] THEN
  ARITH_TAC);;
