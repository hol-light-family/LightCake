(* ========================================================================= *)
(* word_to_wordProof: port of HOL4 compiler/backend/proofs/                  *)
(* word_to_wordProofScript.sml (CakeML v3479), HOL4 lines 1-2489.           *)
(* Correctness proof for word_to_word.                                       *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - Names as in names.tsv: this script's code_rel is                        *)
(*   word_to_wordProof_code_rel; word_to_word's compile and compile_single   *)
(*   are word_to_word_compile and word_to_word_compile_single; wordSem's     *)
(*   evaluate, find_code, pop_env, semantics are wl_evaluate ...; wordLang's *)
(*   Call is wl_Call (HOL4 brings it to the front); wordSem's result         *)
(*   constructors are wl_Error, wordSem_Break, wordSem_Continue; the states  *)
(*   are (A,C,FFI)wl_state.                                                  *)
(* - HOL4's extract_labels and no_install are wordConvs' (wordConvs_         *)
(*   prefix); the asm Overloads addr_offset_ok ac 0w etc. are written out    *)
(*   as asm_offset_ok 0 (asm_config_addr_offset ac) (word 0) (as asm.ml).    *)
(* - Library: EVERY = ALL, EVERY2 = ALL2, set = set_of_list, ZIP (l1,l2) =   *)
(*   ZIP l1 l2 (all ZIPs here zip lists of equal lengths); r with f := x is  *)
(*   RECTYPE_f_fupd (K x) r; the wildcards of HOL4's paired lambdas and lets *)
(*   are named variables.                                                    *)
(* - HOL4's unused binder clk of panLang_compile_word_to_word_thm is left    *)
(*   out.  The derived theorems cond16bit_inst_select_exp (SIMP_RULE        *)
(*   std_ss [] of cond16bit_inst_select_exp'), code_rel_P, code_rel_no_alloc *)
(*   and code_rel_no_install are stated; rmt_thms and rmd_thms (HOL4 lines   *)
(*   902-904) are ML lists of the conjuncts of                               *)
(*   remove_must_terminate_conventions and remove_dead_prog_conventions.     *)
(* - HOL4 proves compile_single_correct by complete induction on termdep,   *)
(*   clock and prog_size, with one suspended subproof per constructor; here  *)
(*   one well-founded induction on the lexicographic combination, with one   *)
(*   top-level lemma per constructor.  no_install_no_alloc_compile_single_   *)
(*   correct (HOL4: the same induction again) is derived from               *)
(*   compile_single_correct and a lemma proved with evaluate_ind: a program  *)
(*   without Install, in code without Install, evaluates the same for every  *)
(*   compiler and compiler oracle.  W2WPAUX_ names are local helpers.        *)
(* - The HOL4 ancestor word_elimProof is not needed by any proof here and   *)
(*   is not loaded.                                                          *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/semantics/wordProps.ml";;
needs "compiler/backend/semantics/wordConvs.ml";;
needs "compiler/backend/word_alloc.ml";;
needs "compiler/backend/word_inst.ml";;
needs "compiler/backend/word_remove.ml";;
needs "compiler/backend/word_unreach.ml";;
needs "compiler/backend/word_elim.ml";;
needs "compiler/backend/word_to_word.ml";;
needs "compiler/backend/proofs/word_simpProof.ml";;
needs "compiler/backend/proofs/word_allocProof.ml";;
needs "compiler/backend/proofs/word_removeProof.ml";;
needs "compiler/backend/proofs/word_instProof.ml";;
needs "compiler/backend/proofs/word_cseProof.ml";;
needs "compiler/backend/proofs/word_unreachProof.ml";;
needs "compiler/backend/proofs/wordConvsProof.ml";;
needs "compiler/backend/proofs/word_copyProof.ml";;

prioritize_num();;
type_invention_error := true;;

(* HOL4 lines 13-19: simpset settings, bring_to_front_overload "Call", the *)
(* tactic is_phy_var_tac                                                     *)

(* HOL4 line 25 *)
let FST_compile_single = prove
 (`!a b c (d:(A)asm_config) e. FST (word_to_word_compile_single a b c d e) = FST (FST e)`,
  REWRITE_TAC[FORALL_PAIR_THM; word_to_word_compile_single_def; LET_DEF; LET_END_DEF; FST]);;
let _ = cake_add_simps [FST_compile_single];;

(* ------------------------------------------------------------------------- *)
(* Local helpers (W2WPAUX_) for the result cases of the pass theorems        *)
(* ------------------------------------------------------------------------- *)

(* the result cases of the pass theorems (NONE, Break and Continue need no *)
(* agreement of the locals) as a disjunction                               *)
let W2WPAUX_res_case = prove
 (CASE_TERM
  `!(res:((A)wl_result)option) P.
     (match res with
        NONE -> T
      | SOME (wordSem_Break _) -> T
      | SOME (wordSem_Continue _) -> T
      | SOME _ -> P) <=>
     (res = NONE \/ (?n. res = SOME (wordSem_Break n)) \/
      (?n. res = SOME (wordSem_Continue n)) \/ P)`,
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `res:((A)wl_result)option` (cases "option")) THEN
  CASE_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  STRUCT_CASES_TAC (ISPEC `a:(A)wl_result` (cases "wl_result")) THEN
  CASE_REWRITE_TAC[] THEN MESON_TAC[]);;

let W2WPAUX_res_case_imp = prove
 (CASE_TERM
  `!(res:((A)wl_result)option) P Q.
     (match res with
        NONE -> Q
      | SOME (wordSem_Break _) -> Q
      | SOME (wordSem_Continue _) -> Q
      | SOME _ -> P)
     ==> (res = NONE \/ (?n. res = SOME (wordSem_Break n)) \/
          (?n. res = SOME (wordSem_Continue n)) \/ P)`,
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `res:((A)wl_result)option` (cases "option")) THEN
  CASE_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  STRUCT_CASES_TAC (ISPEC `a:(A)wl_result` (cases "wl_result")) THEN
  CASE_REWRITE_TAC[] THEN MESON_TAC[]);;

(* take the assumption in which the term tm occurs *)
let W2WPAUX_X_ASM_TAC tm (ttac:thm_tactic) : tactic =
  FIRST_X_ASSUM(fun th -> if can (find_term ((=) tm)) (concl th) then ttac th
                          else failwith "W2WPAUX_X_ASM_TAC");;

let W2WPAUX_wser_locals = prove
 (`(word_state_eq_rel (wl_state_locals_fupd (K x) (s:(A,C,FFI)wl_state)) t <=>
    word_state_eq_rel s t) /\
   (word_state_eq_rel s (wl_state_locals_fupd (K x) t) <=> word_state_eq_rel s t)`,
  REWRITE_TAC[word_state_eq_rel_def] THEN SIMP[]);;

(* the disjunctions res = NONE \/ Break \/ Continue \/ X of the pass        *)
(* theorems: generalise the first three disjuncts to a boolean, then MESON  *)
let W2WPAUX_BC_TAC (res:term) : tactic =
  let ty = type_of res in
  let rty = hd(snd(dest_type ty)) in
  let bk = mk_const("wordSem_Break",[hd(snd(dest_type rty)),`:W`])
  and ct = mk_const("wordSem_Continue",[hd(snd(dest_type rty)),`:W`]) in
  let n = `n:num` in
  let some = mk_const("SOME",[rty,`:A`]) in
  let bc = mk_disj(mk_disj(mk_eq(res,mk_const("NONE",[rty,`:A`])),
                           mk_exists(n,mk_eq(res,mk_comb(some,mk_comb(bk,n))))),
                   mk_exists(n,mk_eq(res,mk_comb(some,mk_comb(ct,n))))) in
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_disj o concl))) THEN
  REWRITE_TAC[DISJ_ASSOC] THEN SPEC_TAC(bc,`bc:bool`) THEN GEN_TAC THEN MESON_TAC[];;

(* HOL4 line 32: chains up the compile_single theorems *)
let compile_single_lem = prove
 (CASE_TERM
  `!prog n (st:(A,C,FFI)wl_state) t k a c name col.
     domain (wl_state_locals st) = set_of_list (even_list n) /\
     gc_fun_const_ok (wl_state_gc_fun st)
     ==> ?perm'.
           let (res,rst) = wl_evaluate (prog,wl_state_permute_fupd (K perm') st) in
           let (x1,x2,cprog) =
             word_to_word_compile_single t k a c ((name,n,prog),col) in
           if res = SOME wl_Error then T else
           let (res',rcst) = wl_evaluate (cprog,st) in
             res = res' /\
             word_state_eq_rel rst rcst /\
             (match res with
                NONE -> T
              | SOME (wordSem_Break _) -> T
              | SOME (wordSem_Continue _) -> T
              | SOME _ -> wl_state_locals rst = wl_state_locals rcst)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[word_to_word_compile_single_def; LET_DEF; LET_END_DEF] THEN
  CASE_REWRITE_TAC[W2WPAUX_res_case] THEN
  ABBREV_TAC `p0 = word_simp_compile_exp (prog:(A)wl_prog)` THEN
  ABBREV_TAC `p1 = inst_select (c:(A)asm_config) (max_var (p0:(A)wl_prog) + 1) p0` THEN
  ABBREV_TAC `p2 = full_ssa_cc_trans n (p1:(A)wl_prog)` THEN
  ABBREV_TAC `p3 = remove_dead_prog (p2:(A)wl_prog)` THEN
  ABBREV_TAC `p4 = copy_prop (word_common_subexp_elim (p3:(A)wl_prog))` THEN
  ABBREV_TAC `p5 = three_to_two_reg_prog t (p4:(A)wl_prog)` THEN
  ABBREV_TAC `p6 = remove_unreach (p5:(A)wl_prog)` THEN
  ABBREV_TAC `p7 = remove_dead_prog (p6:(A)wl_prog)` THEN
  (* the syntactic conventions the passes need *)
  SUBGOAL_THEN `flat_exp_conventions (p2:(A)wl_prog) /\ flat_exp_conventions (p3:(A)wl_prog) /\
                every_inst distinct_tar_reg (p4:(A)wl_prog) /\
                flat_exp_conventions (p6:(A)wl_prog) /\ wf_cutsets (p7:(A)wl_prog)`
    STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `a /\ (a ==> b) /\ (b ==> c) /\ (b ==> d) /\ e
                       ==> a /\ b /\ c /\ d /\ e`) THEN
    REPEAT CONJ_TAC THENL
     [EXPAND_TAC "p2" THEN MATCH_MP_TAC full_ssa_cc_trans_flat_exp_conventions THEN
      EXPAND_TAC "p1" THEN REWRITE_TAC[inst_select_flat_exp_conventions];
      EXPAND_TAC "p3" THEN REWRITE_TAC[remove_dead_prog_conventions];
      DISCH_TAC THEN EXPAND_TAC "p4" THEN MATCH_MP_TAC every_inst_distinct_tar_reg_copy_prop THEN
      MATCH_MP_TAC every_inst_distinct_tar_reg_word_common_subexp_elim THEN
      EXPAND_TAC "p3" THEN EXPAND_TAC "p2" THEN
      SIMP_TAC[remove_dead_prog_conventions; full_ssa_cc_trans_distinct_tar_reg];
      DISCH_TAC THEN EXPAND_TAC "p6" THEN MATCH_MP_TAC flat_exp_conventions_remove_unreach THEN
      EXPAND_TAC "p5" THEN MATCH_MP_TAC three_to_two_reg_prog_flat_exp_conventions THEN
      EXPAND_TAC "p4" THEN MATCH_MP_TAC flat_exp_conventions_copy_prop THEN
      MATCH_MP_TAC flat_exp_conventions_word_common_subexp_elim THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "p7" THEN MATCH_MP_TAC (el 4 (CONJUNCTS remove_dead_prog_conventions)) THEN
      EXPAND_TAC "p6" THEN MATCH_MP_TAC wf_cutsets_remove_unreach THEN
      EXPAND_TAC "p5" THEN MATCH_MP_TAC three_to_two_reg_prog_wf_cutsets THEN
      EXPAND_TAC "p4" THEN MATCH_MP_TAC wf_cutsets_copy_prop THEN
      MATCH_MP_TAC wf_cutsets_word_common_subexp_elim THEN
      EXPAND_TAC "p3" THEN MATCH_MP_TAC (el 4 (CONJUNCTS remove_dead_prog_conventions)) THEN
      EXPAND_TAC "p2" THEN REWRITE_TAC[full_ssa_cc_trans_wf_cutsets]];
    ALL_TAC] THEN
  (* word_alloc *)
  MP_TAC(ISPECL [`name:num`; `c:(A)asm_config`; `a:num`; `p7:(A)wl_prog`; `k:num`;
                 `col:(num spt)option`; `st:(A,C,FFI)wl_state`] word_alloc_correct) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[even_starting_locals_def; IN_SET_OF_LIST; even_list_def; MEM_GENLIST;
                    is_phy_var_def] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[MOD_MULT; ARITH_EQ];
    ALL_TAC] THEN
  CASE_REWRITE_TAC[W2WPAUX_res_case] THEN
  DISCH_THEN(X_CHOOSE_TAC `perm1:num->num->num`) THEN
  (* SSA *)
  MP_TAC(ISPECL [`p1:(A)wl_prog`; `wl_state_permute_fupd (K perm1) (st:(A,C,FFI)wl_state)`;
                 `n:num`] full_ssa_cc_trans_correct) THEN
  ANTS_TAC THENL [SIMP[]; ALL_TAC] THEN
  CASE_REWRITE_TAC[W2WPAUX_res_case] THEN SIMP[] THEN
  DISCH_THEN(X_CHOOSE_TAC `perm2:num->num->num`) THEN
  EXISTS_TAC `perm2:num->num->num` THEN PAIRARG_TAC THEN
  ASM_CASES_TAC `res = SOME (wl_Error:(A)wl_result)` THEN ASM_REWRITE_TAC[] THEN
  (* word_simp *)
  SUBGOAL_THEN `wl_evaluate (p0:(A)wl_prog,
                             wl_state_permute_fupd (K perm2) (st:(A,C,FFI)wl_state)) = (res,rst)`
    ASSUME_TAC THENL
   [EXPAND_TAC "p0" THEN MATCH_MP_TAC word_simpProof_compile_exp_thm THEN
    ASM_SIMP_TAC[] THEN SIMP[];
    ALL_TAC] THEN
  (* inst_select *)
  MP_TAC(ISPECL [`c:(A)asm_config`; `max_var (p0:(A)wl_prog) + 1`; `p0:(A)wl_prog`;
                 `wl_state_permute_fupd (K perm2) (st:(A,C,FFI)wl_state)`;
                 `res:((A)wl_result)option`; `rst:(A,C,FFI)wl_state`;
                 `wl_state_locals (st:(A,C,FFI)wl_state)`] inst_select_thm) THEN
  ANTS_TAC THENL
   [SIMP[locals_rel_def] THEN MATCH_MP_TAC every_var_mono THEN
    EXISTS_TAC `\x:num. x <= max_var (p0:(A)wl_prog)` THEN
    REWRITE_TAC[max_var_max] THEN ARITH_TAC;
    ALL_TAC] THEN
  CASE_REWRITE_TAC[W2WPAUX_res_case] THEN
  SUBGOAL_THEN `!perm. wl_state_locals_fupd (K (wl_state_locals st))
                         (wl_state_permute_fupd (K perm) st) =
                       wl_state_permute_fupd (K perm) (st:(A,C,FFI)wl_state)`
    (fun th -> REWRITE_TAC[th]) THENL
   [SIMP[wl_state_component_equality]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `loc1:((A)word_loc)spt` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP W2WPAUX_res_case_imp) THEN DISCH_TAC THEN
  (* back to SSA *)
  W2WPAUX_X_ASM_TAC `wl_evaluate (p2:(A)wl_prog,
                                  wl_state_permute_fupd (K perm1) (st:(A,C,FFI)wl_state))` MP_TAC THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN PAIRARG_TAC THEN
  SIMP[] THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
                check (fun th -> concl th = `res = res':((A)wl_result)option`)) THEN
  (* first remove_dead *)
  MP_TAC(ISPECL [`p2:(A)wl_prog`; `wl_state_permute_fupd (K perm1) (st:(A,C,FFI)wl_state)`;
                 `rcst:(A,C,FFI)wl_state`; `res:((A)wl_result)option`]
                evaluate_remove_dead_prog) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[W2WPAUX_res_case] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:((A)word_loc)spt` (CONJUNCTS_THEN ASSUME_TAC)) THEN
  (* word_cse, word_copy, three_to_two_reg, remove_unreach *)
  SUBGOAL_THEN `wl_evaluate (p6:(A)wl_prog,
                             wl_state_permute_fupd (K perm1) (st:(A,C,FFI)wl_state)) =
                (res, wl_state_locals_fupd (K t1) rcst)` ASSUME_TAC THENL
   [EXPAND_TAC "p6" THEN MATCH_MP_TAC evaluate_remove_unreach THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "p5" THEN MATCH_MP_TAC evaluate_three_to_two_reg_prog THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "p4" THEN
    SUBGOAL_THEN `wl_evaluate (word_common_subexp_elim (p3:(A)wl_prog),
                               wl_state_permute_fupd (K perm1) (st:(A,C,FFI)wl_state)) =
                  (res, wl_state_locals_fupd (K t1) rcst)` ASSUME_TAC THENL
     [MATCH_MP_TAC word_common_subexp_elim_correct THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[evaluate_copy_prop; FST];
    ALL_TAC] THEN
  (* second remove_dead *)
  MP_TAC(ISPECL [`p6:(A)wl_prog`; `wl_state_permute_fupd (K perm1) (st:(A,C,FFI)wl_state)`;
                 `wl_state_locals_fupd (K t1) (rcst:(A,C,FFI)wl_state)`;
                 `res:((A)wl_result)option`] evaluate_remove_dead_prog) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[W2WPAUX_res_case] THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:((A)word_loc)spt` (CONJUNCTS_THEN ASSUME_TAC)) THEN
  (* back to word_alloc *)
  W2WPAUX_X_ASM_TAC `word_alloc name (c:(A)asm_config) a k (p7:(A)wl_prog) col` MP_TAC THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`wl_evaluate (word_alloc name (c:(A)asm_config) a k (p7:(A)wl_prog) col,
                         st:(A,C,FFI)wl_state)`,
           `q:((A)wl_result)option#(A,C,FFI)wl_state`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN CASE_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`res7:((A)wl_result)option`; `s7:(A,C,FFI)wl_state`] THEN
  REWRITE_TAC[W2WPAUX_wser_locals; wl_state_INFO.ri_accfupds; K_THM] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
                check (fun th -> concl th = `res = res7:((A)wl_result)option`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[W2WPAUX_wser_locals; wl_state_INFO.ri_accfupds; K_THM]) THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC WALLOCPAUX_word_state_eq_rel_trans THEN
    EXISTS_TAC `rcst:(A,C,FFI)wl_state` THEN ASM_REWRITE_TAC[];
    W2WPAUX_BC_TAC `res:((A)wl_result)option`]);;

(* HOL4 line 159 *)
let rm_perm = prove
 (`!s:(A,C,FFI)wl_state. wl_state_permute_fupd (K (wl_state_permute s)) s = s`,
  SIMP[wl_state_component_equality]);;

(* HOL4 line 165: val size_tac (a tactic) *)

let W2WPAUX_SND_compile_single = prove
 (`!t k a (c:(A)asm_config) n m p col.
     SND (word_to_word_compile_single t k a c ((n,m,p),col)) =
     (m,SND (SND (word_to_word_compile_single t k a c ((n,m,p),col))))`,
  REWRITE_TAC[word_to_word_compile_single_def; LET_DEF; LET_END_DEF; SND]);;

(* the two clauses of find_code as equivalences *)
let W2WPAUX_find_code_SOME = prove
 (`!p (args:((A)word_loc)list) (code:(num#B)spt) (ssize:(C)spt) a e ls.
     wl_find_code (SOME p) args code ssize = SOME (a,e,ls) <=>
     ?m. lookup p code = SOME (m,e) /\ LENGTH args = m /\ a = args /\
         ls = lookup p ssize`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_find_code_def] THEN
  STRUCT_CASES_TAC (ISPEC `lookup p (code:(num#B)spt)` (cases "option")) THEN
  CASE_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  SPEC_TAC(`a':num#B`,`q:num#B`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  CASE_REWRITE_TAC[PAIR_EQ] THEN REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ] THEN
  ASM_MESON_TAC[]);;

let W2WPAUX_find_code_NONE = prove
 (`!(args:((A)word_loc)list) (code:(num#B)spt) (ssize:(C)spt) a e ls.
     wl_find_code NONE args code ssize = SOME (a,e,ls) <=>
     ~(args = []) /\
     ?loc m. LAST args = wl_Loc loc 0 /\ lookup loc code = SOME (m,e) /\
             LENGTH args = m + 1 /\ a = BUTLAST args /\ ls = lookup loc ssize`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[wl_find_code_def] THEN COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
    CASES_ON `LAST (args:((A)word_loc)list)` THEN CASE_REWRITE_TAC[option_DISTINCT] THEN
    COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
    CASES_ON `lookup a0 (code:(num#B)spt)` THEN CASE_REWRITE_TAC[option_DISTINCT] THEN
    PAIRARG_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ] THEN
    ASM_MESON_TAC[];
    STRIP_TAC THEN ASM_REWRITE_TAC[wl_find_code_def] THEN CASE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]]);;

(* HOL4 line 167 *)
let word_to_wordProof_find_code_thm = prove
 (`!(st:(A,C,FFI)wl_state) l o1 (o':(D#E#G#num#num)option) (x:((B)word_loc)list) args
    prog locsize.
     (!n v. lookup n (wl_state_code st) = SOME v
            ==> ?t k a c col.
                  lookup n l = SOME (SND (word_to_word_compile_single t k a c ((n,v),col)))) /\
     wl_find_code o1 (add_ret_loc o' x) (wl_state_code st) (wl_state_stack_size st) =
       SOME (args,prog,locsize)
     ==> ?t k a c col n prog'.
           SND (word_to_word_compile_single t k a c ((n,LENGTH args,prog),col)) =
             (LENGTH args,prog') /\
           wl_find_code o1 (add_ret_loc o' x) l (wl_state_stack_size st) =
             SOME (args,prog',locsize)`,
  REPEAT GEN_TAC THEN
  SPEC_TAC(`add_ret_loc (o':(D#E#G#num#num)option) (x:((B)word_loc)list)`,
           `xs:((B)word_loc)list`) THEN
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `o1:num option` (cases "option")) THEN
  REWRITE_TAC[W2WPAUX_find_code_SOME; W2WPAUX_find_code_NONE] THEN STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`loc:num`; `(m:num,prog:(A)wl_prog)`]);
    FIRST_X_ASSUM(MP_TAC o SPECL [`a:num`; `(m:num,prog:(A)wl_prog)`])] THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[W2WPAUX_SND_compile_single] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`t:bool`; `k:num`; `a1:num`; `c:(A)asm_config`;
                       `col:(num spt)option`] THEN DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC [`t:bool`; `k:num`; `a1:num`; `c:(A)asm_config`;
                        `col:(num spt)option`] THEN
  ASM_SIMP_TAC[LENGTH_FRONT; ARITH_RULE `PRE (m + 1) = m`] THENL
   [EXISTS_TAC `loc:num`; EXISTS_TAC `a:num`] THEN
  REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[]);;

(* HOL4 line 191 *)
let pop_env_termdep = prove
 (`!(rst:(A,C,FFI)wl_state) x.
     wl_pop_env rst = SOME x ==> wl_state_termdep x = wl_state_termdep rst`,
  MESON_TAC[wl_pop_env_const]);;

(* HOL4 line 198 *)
let word_to_wordProof_code_rel_def = cake_def
  `word_to_wordProof_code_rel (stc:(num # (A)wl_prog)spt) ttc <=>
     (!n v. lookup n stc = SOME v
            ==> ?col t k a c.
                  lookup n ttc = SOME (SND (word_to_word_compile_single t k a c ((n,v),col))))`;;

(* HOL4 line 205 *)
let compile_single_eta = prove
 (`!t k a (c:(A)asm_config) p x y.
     word_to_word_compile_single t k a c ((p,x),y) =
     (p,SND (word_to_word_compile_single t k a c ((p,x),y)))`,
  REWRITE_TAC[FORALL_PAIR_THM; word_to_word_compile_single_def; LET_DEF; LET_END_DEF; SND]);;

(* ALOOKUP through the compiled list *)
let W2WPAUX_ALOOKUP_compile_single = prove
 (`!(ls:(num#num#(A)wl_prog)list) t k a (c:(A)asm_config) n.
     ALOOKUP (MAP (\p. word_to_word_compile_single t k a c (p,NONE)) ls) n =
     OPTION_MAP (\v. SND (word_to_word_compile_single t k a c ((n,v),NONE)))
       (ALOOKUP ls n)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; ALOOKUP_DEF; OPTION_MAP_DEF] THEN
  SPEC_TAC(`h:num#num#(A)wl_prog`,`h:num#num#(A)wl_prog`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[compile_single_eta] THEN ASM_REWRITE_TAC[ALOOKUP_THM] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[OPTION_MAP_DEF]);;

(* HOL4 line 213 *)
let code_rel_union_fromAList = prove
 (`!s l ls t k a (c:(A)asm_config).
     word_to_wordProof_code_rel s l /\ domain s = domain l
     ==> word_to_wordProof_code_rel (sptree_union s (fromAList ls))
           (sptree_union l (fromAList (MAP (\p. word_to_word_compile_single t k a c (p,NONE)) ls)))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[word_to_wordProof_code_rel_def; lookup_union; lookup_fromAList;
              W2WPAUX_ALOOKUP_compile_single] THEN
  STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`n:num`; `v:num#(A)wl_prog`] THEN
  CASES_ON `lookup n (s:(num#(A)wl_prog)spt)` THEN CASE_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `lookup n (l:(num#(A)wl_prog)spt) = NONE` SUBST1_TAC THENL
     [ASM_MESON_TAC[lookup_NONE_domain]; ALL_TAC] THEN
    CASE_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[OPTION_MAP_DEF] THEN
    MESON_TAC[];
    REWRITE_TAC[option_INJ] THEN DISCH_THEN SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `v:num#(A)wl_prog`]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* compile_single_correct: one well-founded induction (HOL4: completeInduct  *)
(* on termdep, clock and prog_size) with one W2WPAUX_ lemma per constructor *)
(* of wordLang; W2WPAUX_csc_P is the statement for one program and state.  *)
(* ------------------------------------------------------------------------- *)

(* W2WPAUX_lex_ind: HOL4's completeInduct_on termdep, clock and prog_size  *)
let W2WPAUX_lex_ind = prove
 (`!P. (!(prog:(A)wl_prog) (st:(A,C,FFI)wl_state).
          (!prog' st'.
             wl_state_termdep st' < wl_state_termdep st \/
             (wl_state_termdep st' = wl_state_termdep st /\
              (wl_state_clock st' < wl_state_clock st \/
               (wl_state_clock st' = wl_state_clock st /\
                wl_prog_size (\x:A. 0) prog' < wl_prog_size (\x:A. 0) prog)))
             ==> P prog' st')
          ==> P prog st)
       ==> !prog st. P prog st`,
  GEN_TAC THEN DISCH_THEN(LABEL_TAC "H") THEN
  SUBGOAL_THEN `!p:(A)wl_prog#(A,C,FFI)wl_state. P (FST p) (SND p)`
    (fun th -> REPEAT GEN_TAC THEN MP_TAC(SPEC `(prog:(A)wl_prog,st:(A,C,FFI)wl_state)` th) THEN
               REWRITE_TAC[FST; SND]) THEN
  MATCH_MP_TAC(REWRITE_RULE[WF_IND]
    (prove(`WF (inv_image (MEASURE I LEX MEASURE I LEX MEASURE (wl_prog_size (\x:A. 0)))
               (\p:(A)wl_prog#(A,C,FFI)wl_state.
                  (wl_state_termdep (SND p), wl_state_clock (SND p), FST p)))`,
           WF_TAC))) THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(LABEL_TAC "IH") THEN REMOVE_THEN "H" MATCH_MP_TAC THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN REMOVE_THEN "IH" MATCH_MP_TAC THEN
  REWRITE_TAC(WF_REL_THMS @ [I_THM; FST; SND]) THEN ASM_REWRITE_TAC[]);;

(* head beta-reduction of an application of a lambda to arguments *)
let rec W2WPAUX_head_beta t =
  if is_comb t then
    let f,x = dest_comb t in
    let f' = W2WPAUX_head_beta f in
    let t' = mk_comb(f',x) in
    if is_abs f' then rhs(concl(BETA_CONV t')) else t'
  else t;;

(* the lexicographic order of W2WPAUX_lex_ind *)
let W2WPAUX_LT =
 `\(prog':(A)wl_prog) (st':(A,C,FFI)wl_state) (prog:(A)wl_prog) (st:(A,C,FFI)wl_state).
    wl_state_termdep st' < wl_state_termdep st \/
    (wl_state_termdep st' = wl_state_termdep st /\
     (wl_state_clock st' < wl_state_clock st \/
      (wl_state_clock st' = wl_state_clock st /\
       wl_prog_size (\x:A. 0) prog' < wl_prog_size (\x:A. 0) prog)))`;;

(* the statement of a case lemma for the predicate pP and the program p:   *)
(* !vars st. P p st, or with the induction hypothesis                       *)
let W2WPAUX_case_goal pP ih p =
  let st = `st:(A,C,FFI)wl_state` in
  let c = W2WPAUX_head_beta (list_mk_comb(pP,[p;st])) in
  let g =
    if ih then
      let pr' = `prog':(A)wl_prog` and st' = `st':(A,C,FFI)wl_state` in
      let lt = W2WPAUX_head_beta (list_mk_comb(W2WPAUX_LT,[pr';st';p;st])) in
      let pc = W2WPAUX_head_beta (list_mk_comb(pP,[pr';st'])) in
      mk_imp(list_mk_forall([pr';st'],mk_imp(lt,pc)),c)
    else c in
  list_mk_forall(frees p @ [st],g);;

(* compile_single_correct for one program and state *)
let W2WPAUX_csc_P = CASE_TERM
 `\(prog:(A)wl_prog) (st:(A,C,FFI)wl_state).
  !l coracle cc tt kk aa co.
     word_to_wordProof_code_rel (wl_state_code st) l /\
     domain (wl_state_code st) = domain l /\
     wl_state_compile st =
       (\conf progs.
          cc conf (MAP (\p. word_to_word_compile_single tt kk aa co (p,NONE)) progs)) /\
     coracle = (I ## MAP (\p. word_to_word_compile_single tt kk aa co (p,NONE))) o
               wl_state_compile_oracle st /\
     gc_fun_const_ok (wl_state_gc_fun st)
     ==> ?perm'.
           let (res,rst) = wl_evaluate (prog,wl_state_permute_fupd (K perm') st) in
           if res = SOME wl_Error then T
           else
             let (res1,rst1) =
               wl_evaluate (prog,wl_state_code_fupd (K l)
                                   (wl_state_compile_oracle_fupd (K coracle)
                                      (wl_state_compile_fupd (K cc) st))) in
             res1 = res /\
             word_to_wordProof_code_rel (wl_state_code rst) (wl_state_code rst1) /\
             domain (wl_state_code rst) = domain (wl_state_code rst1) /\
             rst1 = wl_state_code_fupd (K (wl_state_code rst1))
                      (wl_state_compile_oracle_fupd
                         (K ((I ## MAP (\p. word_to_word_compile_single tt kk aa co
                                               (p,NONE))) o
                             wl_state_compile_oracle rst))
                         (wl_state_compile_fupd (K cc) rst))`;;

let W2WPAUX_flush_state_upd = prove
 (`wl_flush_state b (wl_state_code_fupd (K x) (s:(A,C,FFI)wl_state)) =
     wl_state_code_fupd (K x) (wl_flush_state b s) /\
   wl_flush_state b (wl_state_compile_oracle_fupd (K y) s) =
     wl_state_compile_oracle_fupd (K y) (wl_flush_state b s) /\
   wl_flush_state b (wl_state_compile_fupd (K z) s) =
     wl_state_compile_fupd (K z) (wl_flush_state b s)`,
  BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[wl_flush_state_def] THEN SIMP[]);;

let W2WPAUX_jump_exc_upd = prove
 (CASE_TERM
  `wl_jump_exc (wl_state_code_fupd (K x) (s:(A,C,FFI)wl_state)) =
     OPTION_MAP (\p. match p with (s,t) -> (wl_state_code_fupd (K x) s, t))
       (wl_jump_exc s) /\
   wl_jump_exc (wl_state_compile_oracle_fupd (K y) s) =
     OPTION_MAP (\p. match p with (s,t) -> (wl_state_compile_oracle_fupd (K y) s, t))
       (wl_jump_exc s) /\
   wl_jump_exc (wl_state_compile_fupd (K z) s) =
     OPTION_MAP (\p. match p with (s,t) -> (wl_state_compile_fupd (K z) s, t))
       (wl_jump_exc s)`,
  REPEAT CONJ_TAC THEN REWRITE_TAC[wl_jump_exc_def] THEN SIMP[] THEN
  REPEAT (TOP_CASE_TAC THEN SIMP[OPTION_MAP_DEF]));;

let W2WPAUX_sh_mem_set_var_upd = prove
 (`sh_mem_set_var res v (wl_state_code_fupd (K x) (s:(A,C,FFI)wl_state)) =
     (I ## (\s. wl_state_code_fupd (K x) s))
       (sh_mem_set_var res v s:((W)wl_result)option#(A,C,FFI)wl_state) /\
   sh_mem_set_var res v (wl_state_compile_oracle_fupd (K y) s) =
     (I ## (\s. wl_state_compile_oracle_fupd (K y) s))
       (sh_mem_set_var res v s:((W)wl_result)option#(A,C,FFI)wl_state) /\
   sh_mem_set_var res v (wl_state_compile_fupd (K z) s) =
     (I ## (\s. wl_state_compile_fupd (K z) s))
       (sh_mem_set_var res v s:((W)wl_result)option#(A,C,FFI)wl_state)`,
  STRUCT_CASES_TAC (ISPEC `res:((FFI)ffi_result)option` (cases "option")) THEN
  TRY(STRUCT_CASES_TAC (ISPEC `a:(FFI)ffi_result` (cases "ffi_result"))) THEN
  REWRITE_TAC[sh_mem_set_var_def; PAIR_MAP_THM; I_THM] THEN
  SIMP[W2WPAUX_flush_state_upd]);;

let W2WPAUX_share_inst_upd = prove
 (`share_inst op v c (wl_state_code_fupd (K x) (s:(A,C,FFI)wl_state)) =
     (I ## (\s. wl_state_code_fupd (K x) s))
       (share_inst op v c s:((W)wl_result)option#(A,C,FFI)wl_state) /\
   share_inst op v c (wl_state_compile_oracle_fupd (K y) s) =
     (I ## (\s. wl_state_compile_oracle_fupd (K y) s))
       (share_inst op v c s:((W)wl_result)option#(A,C,FFI)wl_state) /\
   share_inst op v c (wl_state_compile_fupd (K z) s) =
     (I ## (\s. wl_state_compile_fupd (K z) s))
       (share_inst op v c s:((W)wl_result)option#(A,C,FFI)wl_state)`,
  STRUCT_CASES_TAC (ISPEC `op:memop` (cases "memop")) THEN
  REWRITE_TAC[share_inst_def; wl_sh_mem_store_def; wl_sh_mem_store_byte_def;
              wl_sh_mem_store16_def; wl_sh_mem_store32_def;
              wl_sh_mem_load_def; wl_sh_mem_load_byte_def; wl_sh_mem_load16_def;
              wl_sh_mem_load32_def; W2WPAUX_sh_mem_set_var_upd] THEN
  SIMP[] THEN
  REPEAT (TOP_CASE_TAC THEN SIMP[PAIR_MAP_THM; I_THM; W2WPAUX_flush_state_upd]));;

let W2WPAUX_I_PAIR_MAP = prove
 (`!(f:B->C) (p:A#B). (I ## f) p = (FST p, f (SND p))`,
  REWRITE_TAC[FORALL_PAIR_THM; PAIR_MAP_THM; I_THM; FST; SND]);;

let W2WPAUX_compile_single_eq = prove
 (`!t k a (c:(A)asm_config) n v col x y.
     word_to_word_compile_single t k a c ((n,v),col) = (x,y) <=>
     x = n /\ y = SND (word_to_word_compile_single t k a c ((n,v),col))`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[compile_single_eta] THEN
  REWRITE_TAC[PAIR_EQ; SND] THEN MESON_TAC[]);;

let W2WPAUX_MAP_FST_compile_single = prove
 (`!(ls:(num#num#(A)wl_prog)list) t k a (c:(A)asm_config).
     MAP FST (MAP (\p. word_to_word_compile_single t k a c (p,NONE)) ls) = MAP FST ls`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; FST_compile_single; FST]);;

(* split an evaluation (or any pair) into named components *)
let W2WPAUX_NAME_PAIR_TAC (tm:term) (v1:term) (v2:term) : tactic =
  MP_TAC(ISPEC tm PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN v1 (X_CHOOSE_THEN v2
    (fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th))) THEN
  CASE_REWRITE_TAC[];;

let W2WPAUX_size = type_size_def "wl_prog";;

(* specialise the statement of an induction hypothesis at the code l and   *)
(* the oracle co, with the variables cc tt kk aa co of the goal            *)
let W2WPAUX_SPEC_IH (l:term) (cor:term) : thm_tactic = fun th (asl,w as g) ->
  let fvs = itlist (union o frees o concl o snd) asl (frees w) in
  let fnd s = find (fun v -> fst(dest_var v) = s) fvs in
  MP_TAC (SPECL [l; cor; fnd "cc"; fnd "tt"; fnd "kk"; fnd "aa"; fnd "co"] th) g;;

(* name the components of an evaluation wl_evaluate (p,s) of the goal whose *)
(* state s satisfies ok (and has no bound variables)                        *)
let W2WPAUX_SPLIT_EVAL_TAC (p:term) (ok:term->bool) (v1:term) (v2:term) : tactic =
  fun (asl,w as g) ->
    let fvs = frees w in
    let cand t =
      is_comb t && is_const(rator t) && fst(dest_const(rator t)) = "wl_evaluate" &&
      (let a = rand t in is_pair a && fst(dest_pair a) = p && ok (snd(dest_pair a))) &&
      subset (frees t) fvs in
    let t = find_term cand w in
    W2WPAUX_NAME_PAIR_TAC t v1 v2 g;;

let W2WPAUX_has_perm t =
  can (find_term (fun u -> is_const u && fst(dest_const u) = "wl_state_permute_fupd")) t;;

let W2WPAUX_CONSTS = [inst_const_full; mem_store_const; wl_alloc_const; jump_exc_const;
                      share_inst_const];;
let W2WPAUX_UPD_THMS = [W2WPAUX_flush_state_upd; W2WPAUX_jump_exc_upd;
                        W2WPAUX_share_inst_upd; W2WPAUX_I_PAIR_MAP];;

(* the constructors without subprograms: the second run is the first one   *)
(* with the code, the oracle and the compiler replaced                      *)
let W2WPAUX_CSC_SIMPLE_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN EXISTS_TAC `wl_state_permute (st:(A,C,FFI)wl_state)` THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ASM_REWRITE_TAC[rm_perm; wl_evaluate_def] THEN SIMP W2WPAUX_UPD_THMS THEN
  REPEAT (CASE_TAC THEN SIMP W2WPAUX_UPD_THMS) THEN
  MAP_EVERY (fun th -> TRY (IMP_RES_TAC th)) W2WPAUX_CONSTS THEN
  SIMP[wl_state_component_equality; wl_dec_clock_def];;

let W2WPAUX_csc_simple =
  map (fun tm -> prove(W2WPAUX_case_goal W2WPAUX_csc_P false tm, W2WPAUX_CSC_SIMPLE_TAC))
   [`wl_Skip:(A)wl_prog`; `wl_Move pri moves:(A)wl_prog`; `wl_Inst i:(A)wl_prog`;
    `wl_Assign v e:(A)wl_prog`; `wl_Get v name:(A)wl_prog`; `wl_Set v e:(A)wl_prog`;
    `wl_Store e v:(A)wl_prog`; `wl_StoreConsts t1 t2 addr offset words:(A)wl_prog`;
    `wl_Raise n:(A)wl_prog`; `wl_Return n ms:(A)wl_prog`; `wl_Break n:(A)wl_prog`;
    `wl_Continue n:(A)wl_prog`; `wl_Tick:(A)wl_prog`; `wl_OpCurrHeap b dst src:(A)wl_prog`;
    `wl_LocValue r l1:(A)wl_prog`; `wl_CodeBufferWrite r1 r2:(A)wl_prog`;
    `wl_DataBufferWrite r1 r2:(A)wl_prog`;
    `wl_FFI ffi_index ptr1 len1 ptr2 len2 names:(A)wl_prog`; `ShareInst op v e:(A)wl_prog`;
    `wl_Alloc n names:(A)wl_prog`];;

let W2WPAUX_csc_Install = prove
 (W2WPAUX_case_goal W2WPAUX_csc_P false `wl_Install ptr len dptr dlen names:(A)wl_prog`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN EXISTS_TAC `wl_state_permute (st:(A,C,FFI)wl_state)` THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ASM_REWRITE_TAC[rm_perm; wl_evaluate_def] THEN SIMP W2WPAUX_UPD_THMS THEN
  REPEAT (CASE_TAC THEN SIMP W2WPAUX_UPD_THMS) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[shift_seq_def; o_THM; W2WPAUX_I_PAIR_MAP; FST;
                              W2WPAUX_compile_single_eq]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  RVEQ_TAC THEN
  TRY(FIRST_X_ASSUM(fun th -> MP_TAC th THEN REWRITE_TAC[] THEN NO_TAC)) THEN
  FIRST_ASSUM(fun th ->
    let l,r = dest_eq(concl th) in
    if is_comb l && rator l = `wl_state_compile_oracle (st:(A,C,FFI)wl_state)` then
      MP_TAC(ISPECL [`wl_state_code (st:(A,C,FFI)wl_state)`; `l:(num#(A)wl_prog)spt`;
                     rand r; `tt:bool`; `kk:num`; `aa:num`; `co:(A)asm_config`]
                    code_rel_union_fromAList)
    else failwith "") THEN
  ASM_REWRITE_TAC[MAP] THEN ONCE_REWRITE_TAC[compile_single_eta] THEN
  REWRITE_TAC[fromAList_def; SND] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[domain_union; domain_insert; domain_fromAList;
                  W2WPAUX_MAP_FST_compile_single] THEN
  SIMP[wl_state_component_equality; shift_seq_def; o_DEF]);;

let W2WPAUX_csc_Seq = prove
 (W2WPAUX_case_goal W2WPAUX_csc_P true `wl_Seq p1 p2:(A)wl_prog`,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "IH") THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[wl_evaluate_def] THEN
  (* the first program *)
  USE_THEN "IH" (MP_TAC o SPECL [`p1:(A)wl_prog`; `st:(A,C,FFI)wl_state`]) THEN
  ANTS_TAC THENL [REWRITE_TAC[W2WPAUX_size] THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC_ALL) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `perm1:num->num->num` MP_TAC) THEN
  W2WPAUX_NAME_PAIR_TAC
    `wl_evaluate (p1:(A)wl_prog, wl_state_permute_fupd (K perm1) (st:(A,C,FFI)wl_state))`
    `r1:((A)wl_result)option` `s1:(A,C,FFI)wl_state` THEN
  ASM_CASES_TAC `r1 = SOME (wl_Error:(A)wl_result)` THENL
   [DISCH_TAC THEN EXISTS_TAC `perm1:num->num->num` THEN ASM_REWRITE_TAC[] THEN
    CASE_REWRITE_TAC[option_DISTINCT];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  W2WPAUX_NAME_PAIR_TAC
    `wl_evaluate (p1:(A)wl_prog, wl_state_code_fupd (K l)
        (wl_state_compile_oracle_fupd
           (K ((I ## MAP (\p. word_to_word_compile_single tt kk aa co (p,NONE))) o
               wl_state_compile_oracle (st:(A,C,FFI)wl_state)))
           (wl_state_compile_fupd (K cc) (st:(A,C,FFI)wl_state))))`
    `r1':((A)wl_result)option` `s1':(A,C,FFI)wl_state` THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_CASES_TAC `r1:((A)wl_result)option = NONE` THENL
   [ALL_TAC;
    EXISTS_TAC `perm1:num->num->num` THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM ACCEPT_TAC] THEN
  (* the second program, from s1 *)
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `wl_state_clock (s1:(A,C,FFI)wl_state) <= wl_state_clock (st:(A,C,FFI)wl_state) /\
                wl_state_termdep s1 = wl_state_termdep st /\
                wl_state_compile s1 = wl_state_compile st /\
                wl_state_gc_fun s1 = wl_state_gc_fun st` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`p1:(A)wl_prog`; `wl_state_permute_fupd (K perm1) (st:(A,C,FFI)wl_state)`;
                   `NONE:((A)wl_result)option`; `s1:(A,C,FFI)wl_state`] wl_evaluate_clock) THEN
    MP_TAC(ISPECL [`p1:(A)wl_prog`; `wl_state_permute_fupd (K perm1) (st:(A,C,FFI)wl_state)`;
                   `NONE:((A)wl_result)option`; `s1:(A,C,FFI)wl_state`] wl_evaluate_consts) THEN
    ASM_REWRITE_TAC[] THEN SIMP[];
    ALL_TAC] THEN
  USE_THEN "IH" (MP_TAC o SPECL [`p2:(A)wl_prog`; `s1:(A,C,FFI)wl_state`]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[W2WPAUX_size] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `wl_state_clock (s1:(A,C,FFI)wl_state) <= wl_state_clock (st:(A,C,FFI)wl_state)` THEN
    ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(W2WPAUX_SPEC_IH
    `wl_state_code (s1':(A,C,FFI)wl_state)`
    `(I ## MAP (\p. word_to_word_compile_single tt kk aa co (p,NONE))) o
      wl_state_compile_oracle (s1:(A,C,FFI)wl_state)`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `perm2:num->num->num` MP_TAC) THEN
  (* the first program again, ending with the permutation perm2 *)
  MP_TAC(ISPECL [`p1:(A)wl_prog`; `wl_state_permute_fupd (K perm1) (st:(A,C,FFI)wl_state)`;
                 `perm2:num->num->num`] permute_swap_lemma) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[option_DISTINCT] THEN SIMP[] THEN
  DISCH_THEN(X_CHOOSE_TAC `perm3:num->num->num`) THEN
  DISCH_TAC THEN EXISTS_TAC `perm3:num->num->num` THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN
  FIRST_ASSUM(SUBST1_TAC o check (fun th ->
     is_eq(concl th) && lhs(concl th) = `s1':(A,C,FFI)wl_state`)) THEN
  POP_ASSUM MP_TAC THEN SIMP_NOASM[]);;

(* use the induction hypothesis on a subprogram evaluated in the same state *)
let W2WPAUX_IH_SAME_TAC (p:term) : tactic =
  USE_THEN "IH" (MP_TAC o SPECL [p; `st:(A,C,FFI)wl_state`]) THEN
  ANTS_TAC THENL [REWRITE_TAC[W2WPAUX_size] THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC_ALL) THEN ASM_REWRITE_TAC[] THEN SIMP[] THEN NO_TAC;;

let W2WPAUX_csc_If = prove
 (W2WPAUX_case_goal W2WPAUX_csc_P true `wl_If cmp r1 ri c1 c2:(A)wl_prog`,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "IH") THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[wl_evaluate_def] THEN SIMP W2WPAUX_UPD_THMS THEN
  REPEAT (CASE_TAC THEN SIMP W2WPAUX_UPD_THMS) THEN
  TRY (EXISTS_TAC `wl_state_permute (st:(A,C,FFI)wl_state)` THEN SIMP[rm_perm] THEN NO_TAC) THEN
  FIRST [W2WPAUX_IH_SAME_TAC `c1:(A)wl_prog`; W2WPAUX_IH_SAME_TAC `c2:(A)wl_prog`]);;

let W2WPAUX_csc_MustTerminate = prove
 (W2WPAUX_case_goal W2WPAUX_csc_P true `MustTerminate p:(A)wl_prog`,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "IH") THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[wl_evaluate_def] THEN SIMP[] THEN
  ASM_CASES_TAC `wl_state_termdep (st:(A,C,FFI)wl_state) = 0` THEN ASM_REWRITE_TAC[] THENL
   [EXISTS_TAC `wl_state_permute (st:(A,C,FFI)wl_state)` THEN SIMP[]; ALL_TAC] THEN
  USE_THEN "IH" (MP_TAC o SPECL
    [`p:(A)wl_prog`;
     `wl_state_clock_fupd (K (MustTerminate_limit (:A)))
        (wl_state_termdep_fupd (K (wl_state_termdep st - 1)) (st:(A,C,FFI)wl_state))`]) THEN
  ANTS_TAC THENL [SIMP[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC_ALL) THEN SIMP[] THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `perm1:num->num->num` THEN DISCH_TAC THEN
  EXISTS_TAC `perm1:num->num->num` THEN POP_ASSUM MP_TAC THEN
  W2WPAUX_NAME_PAIR_TAC
    `wl_evaluate (p:(A)wl_prog,
       wl_state_permute_fupd (K perm1) (wl_state_clock_fupd (K (MustTerminate_limit (:A)))
        (wl_state_termdep_fupd (K (wl_state_termdep st - 1)) (st:(A,C,FFI)wl_state))))`
    `r1:((A)wl_result)option` `s1:(A,C,FFI)wl_state` THEN
  ASM_CASES_TAC `r1 = SOME (wl_Error:(A)wl_result)` THEN ASM_REWRITE_TAC[] THENL
   [CASE_REWRITE_TAC[option_DISTINCT; option_INJ]; ALL_TAC] THEN
  ASM_CASES_TAC `r1 = SOME (wl_TimeOut:(A)wl_result)` THEN ASM_REWRITE_TAC[] THENL
   [CASE_REWRITE_TAC[]; ALL_TAC] THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  W2WPAUX_SPLIT_EVAL_TAC `p:(A)wl_prog` (not o W2WPAUX_has_perm)
    `r1':((A)wl_result)option` `s1':(A,C,FFI)wl_state` THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(SUBST1_TAC o check (fun th ->
     is_eq(concl th) && lhs(concl th) = `s1':(A,C,FFI)wl_state`)) THEN
  ASM_REWRITE_TAC[] THEN SIMP[]);;

let W2WPAUX_csc_Loop = prove
 (W2WPAUX_case_goal W2WPAUX_csc_P true `wl_Loop names body exit_names:(A)wl_prog`,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "IH") THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[wl_evaluate_def] THEN SIMP[] THEN
  MP_TAC(ISPEC `wl_cut_state (names,LN) (st:(A,C,FFI)wl_state)` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2
    (fun th -> REWRITE_TAC[th] THEN CASE_REWRITE_TAC[OPTION_MAP_DEF] THEN
               EXISTS_TAC `wl_state_permute (st:(A,C,FFI)wl_state)` THEN SIMP[rm_perm])
    (X_CHOOSE_THEN `stt:(A,C,FFI)wl_state` (fun th -> ASSUME_TAC th THEN REWRITE_TAC[th]))) THEN
  CASE_REWRITE_TAC[OPTION_MAP_DEF] THEN
  SUBGOAL_THEN `wl_state_code (stt:(A,C,FFI)wl_state) = wl_state_code (st:(A,C,FFI)wl_state) /\
                wl_state_compile stt = wl_state_compile st /\
                wl_state_compile_oracle stt = wl_state_compile_oracle st /\
                wl_state_gc_fun stt = wl_state_gc_fun st /\
                wl_state_clock stt = wl_state_clock st /\
                wl_state_termdep stt = wl_state_termdep st` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(X_CHOOSE_TAC `lc:((A)word_loc)spt` o MATCH_MP cut_state_const) THEN
    ASM_REWRITE_TAC[] THEN SIMP[];
    ALL_TAC] THEN
  (* the body *)
  USE_THEN "IH" (MP_TAC o SPECL [`body:(A)wl_prog`; `stt:(A,C,FFI)wl_state`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[W2WPAUX_size] THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC_ALL) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `perm1:num->num->num` MP_TAC) THEN
  W2WPAUX_NAME_PAIR_TAC
    `wl_evaluate (body:(A)wl_prog, wl_state_permute_fupd (K perm1) (stt:(A,C,FFI)wl_state))`
    `r1:((A)wl_result)option` `s1:(A,C,FFI)wl_state` THEN
  ASM_CASES_TAC `r1 = SOME (wl_Error:(A)wl_result)` THENL
   [DISCH_TAC THEN EXISTS_TAC `perm1:num->num->num` THEN ASM_REWRITE_TAC[] THEN SIMP[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN SIMP_NOASM[] THEN
  W2WPAUX_SPLIT_EVAL_TAC `body:(A)wl_prog` (not o W2WPAUX_has_perm)
    `r1':((A)wl_result)option` `s1':(A,C,FFI)wl_state` THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `r1':((A)wl_result)option = r1`)) THEN
  SUBGOAL_THEN `wl_state_clock (s1:(A,C,FFI)wl_state) <= wl_state_clock (st:(A,C,FFI)wl_state) /\
                wl_state_termdep s1 = wl_state_termdep st /\
                wl_state_compile s1 = wl_state_compile st /\
                wl_state_gc_fun s1 = wl_state_gc_fun st` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`body:(A)wl_prog`; `wl_state_permute_fupd (K perm1) (stt:(A,C,FFI)wl_state)`;
                   `r1:((A)wl_result)option`; `s1:(A,C,FFI)wl_state`] wl_evaluate_clock) THEN
    MP_TAC(ISPECL [`body:(A)wl_prog`; `wl_state_permute_fupd (K perm1) (stt:(A,C,FFI)wl_state)`;
                   `r1:((A)wl_result)option`; `s1:(A,C,FFI)wl_state`] wl_evaluate_consts) THEN
    ASM_REWRITE_TAC[] THEN SIMP[];
    ALL_TAC] THEN
  ASM_CASES_TAC `wl_cont_loop (r1:((A)wl_result)option)` THEN ASM_REWRITE_TAC[] THENL
   [ASM_CASES_TAC `wl_state_clock (s1:(A,C,FFI)wl_state) = 0` THENL
     [(* TimeOut *)
      EXISTS_TAC `perm1:num->num->num` THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(SUBST1_TAC o check (fun th ->
        is_eq(concl th) && lhs(concl th) = `s1':(A,C,FFI)wl_state`)) THEN
      SIMP[W2WPAUX_flush_state_upd];
      (* the next iteration *)
      USE_THEN "IH" (MP_TAC o SPECL [`wl_Loop names body exit_names:(A)wl_prog`;
                                     `wl_dec_clock (s1:(A,C,FFI)wl_state)`]) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[wl_dec_clock_def] THEN SIMP[] THEN
        UNDISCH_TAC `wl_state_clock (s1:(A,C,FFI)wl_state) <=
                     wl_state_clock (st:(A,C,FFI)wl_state)` THEN
        UNDISCH_TAC `~(wl_state_clock (s1:(A,C,FFI)wl_state) = 0)` THEN ARITH_TAC;
        ALL_TAC] THEN
      DISCH_THEN(W2WPAUX_SPEC_IH
       `wl_state_code (s1':(A,C,FFI)wl_state)`
       `(I ## MAP (\p. word_to_word_compile_single tt kk aa co (p,NONE))) o
         wl_state_compile_oracle (s1:(A,C,FFI)wl_state)`) THEN
      REWRITE_TAC[wl_dec_clock_def] THEN SIMP[] THEN
      DISCH_THEN(X_CHOOSE_THEN `perm2:num->num->num` MP_TAC) THEN
      MP_TAC(ISPECL [`body:(A)wl_prog`; `wl_state_permute_fupd (K perm1) (stt:(A,C,FFI)wl_state)`;
                     `perm2:num->num->num`] permute_swap_lemma) THEN
      ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN SIMP_NOASM[] THEN
      DISCH_THEN(X_CHOOSE_TAC `perm3:num->num->num`) THEN
      DISCH_TAC THEN EXISTS_TAC `perm3:num->num->num` THEN ASM_REWRITE_TAC[] THEN
      CASE_REWRITE_TAC[] THEN SIMP[wl_STOP_def; wl_dec_clock_def] THEN
      FIRST_ASSUM(SUBST1_TAC o check (fun th ->
        is_eq(concl th) && lhs(concl th) = `s1':(A,C,FFI)wl_state`)) THEN
      POP_ASSUM MP_TAC THEN SIMP_NOASM[wl_STOP_def; wl_dec_clock_def] THEN
      ASM_REWRITE_TAC[] THEN SIMP_NOASM[]];
    (* leaving the loop *)
    EXISTS_TAC `perm1:num->num->num` THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(SUBST1_TAC o check (fun th ->
      is_eq(concl th) && lhs(concl th) = `s1':(A,C,FFI)wl_state`)) THEN
    ASM_CASES_TAC `r1 = SOME (wordSem_Break 0:(A)wl_result)` THEN ASM_REWRITE_TAC[] THEN
    SIMP[] THEN REPEAT (CASE_TAC THEN SIMP[]) THEN
    IMP_RES_TAC cut_state_const THEN ASM_REWRITE_TAC[] THEN SIMP[]]);;

(* two states related by word_state_eq_rel with the same locals differ   *)
(* only in the permutation                                                 *)
let W2WPAUX_wser_eq = prove
 (`!(s:(A,C,FFI)wl_state) t.
     word_state_eq_rel s t /\ wl_state_locals s = wl_state_locals t
     ==> t = wl_state_permute_fupd (K (wl_state_permute t)) s`,
  REWRITE_TAC[word_state_eq_rel_def; wl_state_component_equality] THEN
  REPEAT STRIP_TAC THEN SIMP[]);;

(* push_env with a permutation whose head is the one of the state *)
let W2WPAUX_push_env_perm = prove
 (`!envs h (s:(A,C,FFI)wl_state) p.
     wl_push_env envs h
       (wl_state_permute_fupd (K (\n. if n = 0 then wl_state_permute s 0 else p (n - 1))) s) =
     wl_state_permute_fupd (K p) (wl_push_env envs h s)`,
  GEN_TAC THEN GEN_TAC THEN
  SPEC_TAC(`h:(num#(A)wl_prog#num#num)option`,`h:(num#(A)wl_prog#num#num)option`) THEN
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; wl_push_env_def; env_to_list_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN SIMP[] THEN
  REWRITE_TAC[ARITH_RULE `~(n + 1 = 0) /\ (n + 1) - 1 = n`; ETA_AX] THEN SIMP[]);;

(* the body of a call: the compiled body prog' runs in the second state     *)
(* like the source body prog in the first one (induction hypothesis on     *)
(* prog', then compile_single_lem, then permute_swap_lemma)                *)
let W2WPAUX_csc_body_goal =
  let ih = W2WPAUX_head_beta
             (list_mk_comb(W2WPAUX_csc_P,[`prog':(A)wl_prog`; `S0:(A,C,FFI)wl_state`])) in
  let rest = CASE_TERM
   `word_to_wordProof_code_rel (wl_state_code (S0:(A,C,FFI)wl_state)) l /\
    domain (wl_state_code S0) = domain l /\
    wl_state_compile S0 =
      (\conf progs.
         cc conf (MAP (\p. word_to_word_compile_single tt kk aa co (p,NONE)) progs)) /\
    coracle = (I ## MAP (\p. word_to_word_compile_single tt kk aa co (p,NONE))) o
              wl_state_compile_oracle S0 /\
    gc_fun_const_ok (wl_state_gc_fun S0) /\
    SND (word_to_word_compile_single t k a c ((name,m,prog),col)) = (m,prog') /\
    domain (wl_state_locals S0) = set_of_list (even_list m)
    ==> ?perm.
          let (r,s) = wl_evaluate (prog,wl_state_permute_fupd (K perm) S0) in
          r = SOME wl_Error \/ r = NONE \/ (?n. r = SOME (wordSem_Break n)) \/
          (?n. r = SOME (wordSem_Continue n)) \/
          ?c1. wl_evaluate (prog',wl_state_code_fupd (K l)
                                   (wl_state_compile_oracle_fupd (K coracle)
                                      (wl_state_compile_fupd (K cc) S0))) =
               (r,wl_state_code_fupd (K c1)
                    (wl_state_compile_oracle_fupd
                       (K ((I ## MAP (\p. word_to_word_compile_single tt kk aa co
                                             (p,NONE))) o wl_state_compile_oracle s))
                       (wl_state_compile_fupd (K cc) s))) /\
               word_to_wordProof_code_rel (wl_state_code s) c1 /\
               domain (wl_state_code s) = domain c1` in
  let tm = mk_imp(ih,rest) in
  let fv = frees tm in
  let vs = map (fun n -> find (fun v -> fst(dest_var v) = n) fv)
     ["prog"; "prog'"; "S0"; "l"; "coracle"; "cc"; "tt"; "kk"; "aa"; "co";
      "t"; "k"; "a"; "c"; "name"; "m"; "col"] in
  list_mk_forall(vs,tm);;

let W2WPAUX_csc_body = prove
 (W2WPAUX_csc_body_goal,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "IHB") THEN STRIP_TAC THEN
  REMOVE_THEN "IHB" (MP_TAC o SPEC_ALL) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `perm1:num->num->num` MP_TAC) THEN
  (* compile_single_lem on the source body *)
  MP_TAC(ISPECL [`prog:(A)wl_prog`; `m:num`; `wl_state_permute_fupd (K perm1) (S0:(A,C,FFI)wl_state)`;
                 `t:bool`; `k:num`; `a:num`; `c:(A)asm_config`; `name:num`;
                 `col:(num spt)option`] compile_single_lem) THEN
  ANTS_TAC THENL [SIMP[]; ALL_TAC] THEN
  SUBGOAL_THEN `word_to_word_compile_single t k a (c:(A)asm_config) ((name,m,prog),col) =
                (name,m,prog')` SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[compile_single_eta] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CASE_REWRITE_TAC[W2WPAUX_res_case] THEN SIMP[] THEN
  DISCH_THEN(X_CHOOSE_THEN `perm2:num->num->num` MP_TAC) THEN
  W2WPAUX_NAME_PAIR_TAC
    `wl_evaluate (prog:(A)wl_prog, wl_state_permute_fupd (K perm2) (S0:(A,C,FFI)wl_state))`
    `r2:((A)wl_result)option` `s2:(A,C,FFI)wl_state` THEN
  ASM_CASES_TAC `r2 = SOME (wl_Error:(A)wl_result) \/ r2 = NONE \/
                 (?n. r2 = SOME (wordSem_Break n)) \/ (?n. r2 = SOME (wordSem_Continue n))` THENL
   [DISCH_TAC THEN DISCH_TAC THEN EXISTS_TAC `perm2:num->num->num` THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[DE_MORGAN_THM; NOT_EXISTS_THM]) THEN
  ASM_REWRITE_TAC[] THEN
  W2WPAUX_NAME_PAIR_TAC
    `wl_evaluate (prog':(A)wl_prog, wl_state_permute_fupd (K perm1) (S0:(A,C,FFI)wl_state))`
    `r1:((A)wl_result)option` `s1:(A,C,FFI)wl_state` THEN
  STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
    check (fun th -> concl th = `r2:((A)wl_result)option = r1`)) THEN
  ASM_REWRITE_TAC[] THEN
  W2WPAUX_SPLIT_EVAL_TAC `prog':(A)wl_prog` (not o W2WPAUX_has_perm)
    `r3:((A)wl_result)option` `s3:(A,C,FFI)wl_state` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`prog:(A)wl_prog`; `wl_state_permute_fupd (K perm2) (S0:(A,C,FFI)wl_state)`;
                 `wl_state_permute (s1:(A,C,FFI)wl_state)`] permute_swap_lemma) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN SIMP_NOASM[] THEN
  DISCH_THEN(X_CHOOSE_TAC `perm3:num->num->num`) THEN
  EXISTS_TAC `perm3:num->num->num` THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `s1 = wl_state_permute_fupd (K (wl_state_permute s1)) (s2:(A,C,FFI)wl_state)`
    ASSUME_TAC THENL
   [MATCH_MP_TAC W2WPAUX_wser_eq THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `wl_state_code (s3:(A,C,FFI)wl_state)` THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    is_eq(concl th) && lhs(concl th) = `s1:(A,C,FFI)wl_state`)) THEN
  REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

(* find_code_thm from code_rel *)
let W2WPAUX_find_code_rel = prove
 (`!(st:(A,C,FFI)wl_state) l o1 (o':(D#E#G#num#num)option) (x:((B)word_loc)list) args
    prog locsize.
     word_to_wordProof_code_rel (wl_state_code st) l /\
     wl_find_code o1 (add_ret_loc o' x) (wl_state_code st) (wl_state_stack_size st) =
       SOME (args,prog,locsize)
     ==> ?t k a c col n prog'.
           SND (word_to_word_compile_single t k a c ((n,LENGTH args,prog),col)) =
             (LENGTH args,prog') /\
           wl_find_code o1 (add_ret_loc o' x) l (wl_state_stack_size st) =
             SOME (args,prog',locsize)`,
  REWRITE_TAC[word_to_wordProof_code_rel_def] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC word_to_wordProof_find_code_thm THEN ASM_MESON_TAC[]);;

(* case split on an option-valued term tm of the goal; the NONE case is an  *)
(* error of the first run (witness: the permutation of st)                  *)
let W2WPAUX_OPT_CASES_TAC (tm:term) (v:term) : tactic =
  MP_TAC(ISPEC tm (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2
    (fun th -> REWRITE_TAC[th] THEN CASE_REWRITE_TAC[] THEN
               EXISTS_TAC `wl_state_permute (st:(A,C,FFI)wl_state)` THEN SIMP[rm_perm])
    (X_CHOOSE_THEN v (fun th -> ASSUME_TAC th THEN REWRITE_TAC[th]))) THEN
  CASE_REWRITE_TAC[];;

(* the common part of the Call cases: the arguments, the destination and   *)
(* the code found (find_code_thm gives the compiled code in l)              *)
let W2WPAUX_CALL_PREFIX_TAC (ret:term) : tactic =
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "IH") THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[wl_evaluate_def] THEN SIMP[] THEN
  W2WPAUX_OPT_CASES_TAC `wl_get_vars args (st:(A,C,FFI)wl_state)` `xs:((A)word_loc)list` THEN
  ASM_CASES_TAC `bad_dest_args (dest:num option) (args:num list)` THEN ASM_REWRITE_TAC[] THENL
   [EXISTS_TAC `wl_state_permute (st:(A,C,FFI)wl_state)` THEN SIMP[rm_perm]; ALL_TAC] THEN
  W2WPAUX_OPT_CASES_TAC
    (subst [ret,`r:(num list#cutsets#(A)wl_prog#num#num)option`]
       `wl_find_code dest (add_ret_loc (r:(num list#cutsets#(A)wl_prog#num#num)option)
          (xs:((A)word_loc)list)) (wl_state_code (st:(A,C,FFI)wl_state))
          (wl_state_stack_size st)`)
    `q:((A)word_loc)list#(A)wl_prog#num option` THEN
  W2WPAUX_NAME_PAIR_TAC `q:((A)word_loc)list#(A)wl_prog#num option`
    `args1:((A)word_loc)list` `q1:(A)wl_prog#num option` THEN
  W2WPAUX_NAME_PAIR_TAC `q1:(A)wl_prog#num option` `prog:(A)wl_prog` `ss:num option` THEN
  MP_TAC(ISPECL [`st:(A,C,FFI)wl_state`; `l:(num#(A)wl_prog)spt`; `dest:num option`;
                 ret; `xs:((A)word_loc)list`; `args1:((A)word_loc)list`;
                 `prog:(A)wl_prog`; `ss:num option`] W2WPAUX_find_code_rel) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:bool` (X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `a:num`
    (X_CHOOSE_THEN `c:(A)asm_config` (X_CHOOSE_THEN `col:(num spt)option`
    (X_CHOOSE_THEN `name:num` (X_CHOOSE_THEN `prog':(A)wl_prog` STRIP_ASSUME_TAC))))))) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[];;

(* use W2WPAUX_csc_body for the call state S0 (the induction hypothesis on *)
(* the compiled body prog' at S0 is the assumption "IHC")                  *)
let W2WPAUX_BODY_TAC (s0:term) (m:term) : tactic =
  MP_TAC(ISPECL [`prog:(A)wl_prog`; `prog':(A)wl_prog`; s0; `l:(num#(A)wl_prog)spt`;
     subst [s0,`S0x:(A,C,FFI)wl_state`]
       `(I ## MAP (\p. word_to_word_compile_single tt kk aa co (p,NONE))) o
        wl_state_compile_oracle (S0x:(A,C,FFI)wl_state)`;
     `cc:C->(num#num#(A)wl_prog)list->(byte list#(A word)list#C)option`;
     `tt:bool`; `kk:num`; `aa:num`; `co:(A)asm_config`; `t:bool`; `k:num`; `a:num`;
     `c:(A)asm_config`; `name:num`; m; `col:(num spt)option`] W2WPAUX_csc_body) THEN
  ANTS_TAC THENL [USE_THEN "IHC" ACCEPT_TAC; ALL_TAC];;

let W2WPAUX_csc_Call_tail = prove
 (W2WPAUX_case_goal W2WPAUX_csc_P true `wl_Call NONE dest args handler:(A)wl_prog`,
  W2WPAUX_CALL_PREFIX_TAC `NONE:(num list#cutsets#(A)wl_prog#num#num)option` THEN
  ASM_CASES_TAC `handler:(num#(A)wl_prog#num#num)option = NONE` THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC; EXISTS_TAC `wl_state_permute (st:(A,C,FFI)wl_state)` THEN SIMP[rm_perm]] THEN
  ASM_CASES_TAC `wl_state_clock (st:(A,C,FFI)wl_state) = 0` THEN ASM_REWRITE_TAC[] THENL
   [EXISTS_TAC `wl_state_permute (st:(A,C,FFI)wl_state)` THEN
    SIMP[rm_perm; W2WPAUX_flush_state_upd] THEN
    SIMP[wl_state_component_equality; wl_flush_state_def];
    ALL_TAC] THEN
  (* the body, in the state S0 *)
  USE_THEN "IH" (MP_TAC o SPECL
    [`prog':(A)wl_prog`; `wl_call_env args1 ss (wl_dec_clock (st:(A,C,FFI)wl_state))`]) THEN
  ANTS_TAC THENL
   [SIMP[wl_dec_clock_def] THEN UNDISCH_TAC `~(wl_state_clock (st:(A,C,FFI)wl_state) = 0)` THEN
    ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "IHC") THEN
  W2WPAUX_BODY_TAC `wl_call_env args1 ss (wl_dec_clock (st:(A,C,FFI)wl_state))`
    `LENGTH (args1:((A)word_loc)list)` THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN SIMP[wl_dec_clock_def; wl_call_env_def; domain_fromList2;
                               even_list_def];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `perm:num->num->num` (LABEL_TAC "BODY")) THEN
  EXISTS_TAC `perm:num->num->num` THEN REMOVE_THEN "BODY" MP_TAC THEN
  SIMP[IL2AUX_dec_clock_permute] THEN
  W2WPAUX_NAME_PAIR_TAC
    `wl_evaluate (prog:(A)wl_prog, wl_state_permute_fupd (K perm)
       (wl_call_env args1 ss (wl_dec_clock (st:(A,C,FFI)wl_state))))`
    `r:((A)wl_result)option` `s:(A,C,FFI)wl_state` THEN
  SIMP[wl_dec_clock_def] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN SIMP[] THEN
  ASM_CASES_TAC `wl_bad_fun_return (r:((A)wl_result)option)` THEN ASM_REWRITE_TAC[] THEN
  SIMP[]);;

let W2WPAUX_push_env_dec_perm = prove
 (`!envs h (st:(A,C,FFI)wl_state) p.
     wl_push_env envs h (wl_dec_clock (wl_state_permute_fupd
       (K (\n. if n = 0 then wl_state_permute st 0 else p (n - 1))) st)) =
     wl_state_permute_fupd (K p) (wl_push_env envs h (wl_dec_clock st))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IL2AUX_dec_clock_permute] THEN
  MP_TAC(ISPECL [`envs:((A)word_loc)spt#((A)word_loc)spt`; `h:(num#(A)wl_prog#num#num)option`;
                 `wl_dec_clock (st:(A,C,FFI)wl_state)`; `p:num->num->num`]
                W2WPAUX_push_env_perm) THEN
  REWRITE_TAC[wl_dec_clock_const]);;

(* the witness of the returning calls: the head of the permutation is the  *)
(* one of st (push_env uses it), the rest is perm                           *)
let W2WPAUX_RET_WITNESS_TAC (perm:term) : tactic =
  EXISTS_TAC (mk_abs(`n:num`,
     mk_cond(`n = 0`, `wl_state_permute (st:(A,C,FFI)wl_state) 0`,
             mk_comb(perm,`n - 1`)))) THEN
  REWRITE_TAC[W2WPAUX_push_env_dec_perm] THEN SIMP[];;

(* case split on an option-valued term tm; the NONE case is closed by ntac *)
let W2WPAUX_OPT_CASES_THEN (tm:term) (v:term) (ntac:tactic) : tactic =
  MP_TAC(ISPEC tm (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2
    (fun th -> ASSUME_TAC th THEN ntac)
    (X_CHOOSE_THEN v (fun th -> ASSUME_TAC th)));;

let W2WPAUX_dec_clock_upd = prove
 (`wl_dec_clock (wl_state_code_fupd (K x) (s:(A,C,FFI)wl_state)) =
     wl_state_code_fupd (K x) (wl_dec_clock s) /\
   wl_dec_clock (wl_state_compile_oracle_fupd (K y) s) =
     wl_state_compile_oracle_fupd (K y) (wl_dec_clock s) /\
   wl_dec_clock (wl_state_compile_fupd (K z) s) =
     wl_state_compile_fupd (K z) (wl_dec_clock s)`,
  REWRITE_TAC[wl_dec_clock_def] THEN SIMP[]);;

(* the assumption wl_evaluate (p,s) = (r,t) whose state s satisfies ok *)
let W2WPAUX_EVAL_ASM (p:term) (ok:term->bool) (ttac:thm_tactic) : tactic =
  FIRST_ASSUM(fun th ->
    let l = lhs(concl th) in
    if is_comb l && is_const(rator l) && fst(dest_const(rator l)) = "wl_evaluate" &&
       fst(dest_pair(rand l)) = p && ok (snd(dest_pair(rand l)))
    then ttac th else failwith "W2WPAUX_EVAL_ASM");;

(* returning calls *)
let W2WPAUX_csc_Call_ret = prove
 (W2WPAUX_case_goal W2WPAUX_csc_P true
    `wl_Call (SOME (xn,xnames,xrh,xl1,xl2)) dest args handler:(A)wl_prog`,
  W2WPAUX_CALL_PREFIX_TAC `SOME (xn,xnames,xrh,xl1,xl2):(num list#cutsets#(A)wl_prog#num#num)option` THEN
   ASM_CASES_TAC `domain (FST (xnames:cutsets)) = {} \/ ~ALL_DISTINCT (xn:num list)` THEN
   ASM_REWRITE_TAC[] THENL
    [EXISTS_TAC `wl_state_permute (st:(A,C,FFI)wl_state)` THEN SIMP[rm_perm]; ALL_TAC] THEN
   W2WPAUX_OPT_CASES_TAC `cut_envs xnames (wl_state_locals (st:(A,C,FFI)wl_state))`
     `envs:((A)word_loc)spt#((A)word_loc)spt` THEN
   ASM_CASES_TAC `wl_state_clock (st:(A,C,FFI)wl_state) = 0` THEN ASM_REWRITE_TAC[] THENL
    [EXISTS_TAC `wl_state_permute (st:(A,C,FFI)wl_state)` THEN
     SIMP[rm_perm; W2WPAUX_flush_state_upd] THEN
     SIMP[wl_state_component_equality; wl_flush_state_def];
     ALL_TAC] THEN
   USE_THEN "IH" (MP_TAC o SPECL
    [`prog':(A)wl_prog`;
     `wl_call_env args1 ss (wl_push_env envs handler (wl_dec_clock (st:(A,C,FFI)wl_state)))`]) THEN
   ANTS_TAC THENL
    [SIMP[wl_dec_clock_def; wl_push_env_clock; IL2AUX_push_env_termdep] THEN
     UNDISCH_TAC `~(wl_state_clock (st:(A,C,FFI)wl_state) = 0)` THEN ARITH_TAC;
     ALL_TAC] THEN
   DISCH_THEN(LABEL_TAC "IHC") THEN
   W2WPAUX_BODY_TAC
     `wl_call_env args1 ss (wl_push_env envs handler (wl_dec_clock (st:(A,C,FFI)wl_state)))`
     `LENGTH (args1:((A)word_loc)list)` THEN
   ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN SIMP[wl_call_env_def; domain_fromList2; even_list_def];
     ALL_TAC] THEN
   DISCH_THEN(X_CHOOSE_THEN `perm:num->num->num` MP_TAC) THEN
   W2WPAUX_NAME_PAIR_TAC
     `wl_evaluate (prog:(A)wl_prog, wl_state_permute_fupd (K perm)
        (wl_call_env args1 ss (wl_push_env envs handler (wl_dec_clock (st:(A,C,FFI)wl_state)))))`
     `r:((A)wl_result)option` `s:(A,C,FFI)wl_state` THEN
   SIMP[W2WPAUX_dec_clock_upd] THEN
   DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (DISJ_CASES_THEN2 ASSUME_TAC
     (DISJ_CASES_THEN2 STRIP_ASSUME_TAC (DISJ_CASES_THEN2 STRIP_ASSUME_TAC
        (X_CHOOSE_THEN `c1:(num#(A)wl_prog)spt` STRIP_ASSUME_TAC))))) THEN
   TRY (W2WPAUX_RET_WITNESS_TAC `perm:num->num->num` THEN ASM_REWRITE_TAC[] THEN
        SIMP[W2WPAUX_dec_clock_upd] THEN NO_TAC) THEN
   DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `rr:(A)wl_result` SUBST_ALL_TAC)
     (ISPEC `r:((A)wl_result)option` (cases "option")) THEN
   TRY (W2WPAUX_RET_WITNESS_TAC `perm:num->num->num` THEN ASM_REWRITE_TAC[] THEN
        SIMP[W2WPAUX_dec_clock_upd] THEN NO_TAC) THEN
   REPEAT_TCL DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC)
     (ISPEC `rr:(A)wl_result` (cases "wl_result")) THEN
   TRY (W2WPAUX_RET_WITNESS_TAC `perm:num->num->num` THEN ASM_REWRITE_TAC[] THEN
        SIMP[W2WPAUX_dec_clock_upd] THEN NO_TAC) THENL
   [(* Result *)
    ASM_CASES_TAC `~(a0:(A)word_loc = wl_Loc xl1 xl2) \/ ~(LENGTH (a1:((A)word_loc)list) = LENGTH (xn:num list))` THENL
    [W2WPAUX_RET_WITNESS_TAC `perm:num->num->num` THEN ASM_REWRITE_TAC[] THEN
     SIMP[W2WPAUX_dec_clock_upd];
     ALL_TAC] THEN
   W2WPAUX_OPT_CASES_THEN `wl_pop_env (s:(A,C,FFI)wl_state)` `s1:(A,C,FFI)wl_state`
     (W2WPAUX_RET_WITNESS_TAC `perm:num->num->num` THEN ASM_REWRITE_TAC[] THEN
      SIMP[W2WPAUX_dec_clock_upd]) THEN
   ASM_CASES_TAC `domain (wl_state_locals (s1:(A,C,FFI)wl_state)) =
                  domain (FST (envs:((A)word_loc)spt#((A)word_loc)spt)) UNION domain (SND envs)` THENL
    [ALL_TAC;
     W2WPAUX_RET_WITNESS_TAC `perm:num->num->num` THEN ASM_REWRITE_TAC[] THEN
     SIMP[W2WPAUX_dec_clock_upd]] THEN
   SUBGOAL_THEN `wl_state_clock (s1:(A,C,FFI)wl_state) < wl_state_clock (st:(A,C,FFI)wl_state) /\
                 wl_state_termdep s1 = wl_state_termdep st /\
                 wl_state_code s1 = wl_state_code (s:(A,C,FFI)wl_state) /\
                 wl_state_compile s1 = wl_state_compile st /\
                 wl_state_gc_fun s1 = wl_state_gc_fun st /\
                 wl_state_compile_oracle s1 = wl_state_compile_oracle s` STRIP_ASSUME_TAC THENL
    [W2WPAUX_EVAL_ASM `prog:(A)wl_prog` W2WPAUX_has_perm (fun th ->
       MP_TAC(MATCH_MP wl_evaluate_clock th) THEN MP_TAC(MATCH_MP wl_evaluate_consts th)) THEN
     FIRST_ASSUM(MP_TAC o MATCH_MP wl_pop_env_const o
       check (fun th -> lhs(concl th) = `wl_pop_env (s:(A,C,FFI)wl_state)`)) THEN
     SIMP[wl_dec_clock_def; wl_push_env_clock; IL2AUX_push_env_termdep] THEN
     REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
     UNDISCH_TAC `~(wl_state_clock (st:(A,C,FFI)wl_state) = 0)` THEN ASM_ARITH_TAC;
     ALL_TAC] THEN
   USE_THEN "IH" (MP_TAC o SPECL [`xrh:(A)wl_prog`; `wl_set_vars xn a1 (s1:(A,C,FFI)wl_state)`]) THEN
   ANTS_TAC THENL [SIMP[]; ALL_TAC] THEN
   DISCH_THEN(W2WPAUX_SPEC_IH `c1:(num#(A)wl_prog)spt`
     `(I ## MAP (\p. word_to_word_compile_single tt kk aa co (p,NONE))) o
      wl_state_compile_oracle (wl_set_vars xn a1 (s1:(A,C,FFI)wl_state))`) THEN
   ANTS_TAC THENL [SIMP[]; ALL_TAC] THEN
   DISCH_THEN(X_CHOOSE_THEN `permh:num->num->num` (LABEL_TAC "IHH")) THEN
   MP_TAC(ISPECL [`prog:(A)wl_prog`;
     `wl_state_permute_fupd (K perm) (wl_call_env args1 ss (wl_push_env envs handler
        (wl_dec_clock (st:(A,C,FFI)wl_state))))`;
     `permh:num->num->num`] permute_swap_lemma) THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN SIMP_NOASM[] THEN
   DISCH_THEN(X_CHOOSE_TAC `perm2:num->num->num`) THEN
   W2WPAUX_RET_WITNESS_TAC `perm2:num->num->num` THEN ASM_REWRITE_TAC[] THEN
   SIMP[W2WPAUX_dec_clock_upd] THEN
   REMOVE_THEN "IHH" MP_TAC THEN SIMP[];
    (* Exception *)
    DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `hh:num#(A)wl_prog#num#num` SUBST_ALL_TAC)
     (ISPEC `handler:(num#(A)wl_prog#num#num)option` (cases "option")) THENL
    [W2WPAUX_RET_WITNESS_TAC `perm:num->num->num` THEN ASM_REWRITE_TAC[] THEN
     SIMP[W2WPAUX_dec_clock_upd];
     ALL_TAC] THEN
   W2WPAUX_NAME_PAIR_TAC `hh:num#(A)wl_prog#num#num` `hn:num` `hq:(A)wl_prog#num#num` THEN
   W2WPAUX_NAME_PAIR_TAC `hq:(A)wl_prog#num#num` `hp:(A)wl_prog` `hl:num#num` THEN
   W2WPAUX_NAME_PAIR_TAC `hl:num#num` `hl1:num` `hl2:num` THEN
   ASM_CASES_TAC `~(a0:(A)word_loc = wl_Loc hl1 hl2)` THENL
    [W2WPAUX_RET_WITNESS_TAC `perm:num->num->num` THEN ASM_REWRITE_TAC[] THEN
     SIMP[W2WPAUX_dec_clock_upd];
     ALL_TAC] THEN
   ASM_CASES_TAC `domain (wl_state_locals (s:(A,C,FFI)wl_state)) =
                  domain (FST (envs:((A)word_loc)spt#((A)word_loc)spt)) UNION domain (SND envs)` THENL
    [ALL_TAC;
     W2WPAUX_RET_WITNESS_TAC `perm:num->num->num` THEN ASM_REWRITE_TAC[] THEN
     SIMP[W2WPAUX_dec_clock_upd]] THEN
   SUBGOAL_THEN `wl_state_clock (s:(A,C,FFI)wl_state) < wl_state_clock (st:(A,C,FFI)wl_state) /\
                 wl_state_termdep s = wl_state_termdep st /\
                 wl_state_compile s = wl_state_compile st /\
                 wl_state_gc_fun s = wl_state_gc_fun st` STRIP_ASSUME_TAC THENL
    [W2WPAUX_EVAL_ASM `prog:(A)wl_prog` W2WPAUX_has_perm (fun th ->
       MP_TAC(MATCH_MP wl_evaluate_clock th) THEN MP_TAC(MATCH_MP wl_evaluate_consts th)) THEN
     SIMP[wl_dec_clock_def; wl_push_env_clock; IL2AUX_push_env_termdep] THEN
     REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
     UNDISCH_TAC `~(wl_state_clock (st:(A,C,FFI)wl_state) = 0)` THEN ASM_ARITH_TAC;
     ALL_TAC] THEN
   USE_THEN "IH" (MP_TAC o SPECL [`hp:(A)wl_prog`; `wl_set_var hn a1 (s:(A,C,FFI)wl_state)`]) THEN
   ANTS_TAC THENL [SIMP[]; ALL_TAC] THEN
   DISCH_THEN(W2WPAUX_SPEC_IH `c1:(num#(A)wl_prog)spt`
     `(I ## MAP (\p. word_to_word_compile_single tt kk aa co (p,NONE))) o
      wl_state_compile_oracle (wl_set_var hn a1 (s:(A,C,FFI)wl_state))`) THEN
   ANTS_TAC THENL [SIMP[]; ALL_TAC] THEN
   DISCH_THEN(X_CHOOSE_THEN `permh:num->num->num` (LABEL_TAC "IHH")) THEN
   MP_TAC(ISPECL [`prog:(A)wl_prog`;
     `wl_state_permute_fupd (K perm) (wl_call_env args1 ss (wl_push_env envs
        (SOME (hn,hp,hl1,hl2)) (wl_dec_clock (st:(A,C,FFI)wl_state))))`;
     `permh:num->num->num`] permute_swap_lemma) THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN SIMP_NOASM[] THEN
   DISCH_THEN(X_CHOOSE_TAC `perm2:num->num->num`) THEN
   W2WPAUX_RET_WITNESS_TAC `perm2:num->num->num` THEN ASM_REWRITE_TAC[] THEN
   SIMP[W2WPAUX_dec_clock_upd] THEN
   REMOVE_THEN "IHH" MP_TAC THEN SIMP[]]);;

let W2WPAUX_csc_Call = prove
 (W2WPAUX_case_goal W2WPAUX_csc_P true `wl_Call ret dest args handler:(A)wl_prog`,
  GEN_REWRITE_TAC I [FORALL_OPTION_THM] THEN CONJ_TAC THENL
   [MATCH_ACCEPT_TAC W2WPAUX_csc_Call_tail;
    REPEAT(GEN_REWRITE_TAC I [FORALL_PAIR_THM] THEN GEN_TAC) THEN REPEAT GEN_TAC THEN
    MATCH_ACCEPT_TAC W2WPAUX_csc_Call_ret]);;

(* the induction: one lemma per constructor *)
let W2WPAUX_csc_all = prove
 (let tm = W2WPAUX_head_beta
             (list_mk_comb(W2WPAUX_csc_P,[`prog:(A)wl_prog`; `st:(A,C,FFI)wl_state`])) in
  list_mk_forall([`prog:(A)wl_prog`; `st:(A,C,FFI)wl_state`],tm),
  MATCH_MP_TAC (CONV_RULE (DEPTH_CONV BETA_CONV) (ISPEC W2WPAUX_csc_P W2WPAUX_lex_ind)) THEN
  GEN_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `prog:(A)wl_prog` (nchotomy_of_type `:(A)wl_prog`)) THEN
  FIRST (map (fun th -> DISCH_THEN(K ALL_TAC) THEN MATCH_ACCEPT_TAC th)
           (W2WPAUX_csc_Install :: W2WPAUX_csc_simple) @
         map MATCH_ACCEPT_TAC
           [W2WPAUX_csc_MustTerminate; W2WPAUX_csc_Call; W2WPAUX_csc_Seq; W2WPAUX_csc_If;
            W2WPAUX_csc_Loop]));;

(* HOL4 line 235 *)
let compile_single_correct = prove
 (CASE_TERM
  `!prog (st:(A,C,FFI)wl_state) l coracle cc tt kk aa co.
     word_to_wordProof_code_rel (wl_state_code st) l /\
     domain (wl_state_code st) = domain l /\
     wl_state_compile st =
       (\conf progs.
          cc conf (MAP (\p. word_to_word_compile_single tt kk aa co (p,NONE)) progs)) /\
     coracle = (I ## MAP (\p. word_to_word_compile_single tt kk aa co (p,NONE))) o
               wl_state_compile_oracle st /\
     gc_fun_const_ok (wl_state_gc_fun st)
     ==> ?perm'.
           let (res,rst) = wl_evaluate (prog,wl_state_permute_fupd (K perm') st) in
           if res = SOME wl_Error then T
           else
             let (res1,rst1) =
               wl_evaluate (prog,wl_state_code_fupd (K l)
                                   (wl_state_compile_oracle_fupd (K coracle)
                                      (wl_state_compile_fupd (K cc) st))) in
             res1 = res /\
             word_to_wordProof_code_rel (wl_state_code rst) (wl_state_code rst1) /\
             domain (wl_state_code rst) = domain (wl_state_code rst1) /\
             rst1 = wl_state_code_fupd (K (wl_state_code rst1))
                      (wl_state_compile_oracle_fupd
                         (K ((I ## MAP (\p. word_to_word_compile_single tt kk aa co
                                               (p,NONE))) o
                             wl_state_compile_oracle rst))
                         (wl_state_compile_fupd (K cc) rst))`,
  ACCEPT_TAC W2WPAUX_csc_all);;

(* full_compile_single is compile_single followed by remove_must_terminate *)
let W2WPAUX_fcs = prove
 (`!t k a (c:(A)asm_config) p.
     full_compile_single t k a c p =
     (I ## I ## remove_must_terminate) (word_to_word_compile_single t k a c p)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[full_compile_single_def] THEN
  SPEC_TAC(`word_to_word_compile_single t k a (c:(A)asm_config) p`,`q:num#num#(A)wl_prog`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN CASE_REWRITE_TAC[PAIR_MAP_THM; I_THM]);;

let W2WPAUX_MAP_fcs = prove
 (`!t k a (c:(A)asm_config) (progs:(num#num#(A)wl_prog)list).
     MAP (I ## I ## remove_must_terminate)
       (MAP (\p. word_to_word_compile_single t k a c (p,NONE)) progs) =
     MAP (\p. full_compile_single t k a c (p,NONE)) progs`,
  REWRITE_TAC[MAP_MAP_o; o_DEF; W2WPAUX_fcs]);;

let W2WPAUX_oracle_fcs = prove
 (`!t k a (c:(A)asm_config) (f:num->C#(num#num#(A)wl_prog)list).
     (I ## MAP (I ## I ## remove_must_terminate)) o
     ((I ## MAP (\p. word_to_word_compile_single t k a c (p,NONE))) o f) =
     (I ## MAP (\p. full_compile_single t k a c (p,NONE))) o f`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM] THEN X_GEN_TAC `x:num` THEN
  SPEC_TAC(`(f:num->C#(num#num#(A)wl_prog)list) x`,`q:C#(num#num#(A)wl_prog)list`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; PAIR_MAP_THM; I_THM; W2WPAUX_MAP_fcs]);;

(* HOL4 line 851 *)
let compile_word_to_word_thm = prove
 (CASE_TERM
  `!(st:(A,C,FFI)wl_state) l cc tt kk aa co coracle start.
     word_to_wordProof_code_rel (wl_state_code st) l /\
     domain (wl_state_code st) = domain l /\
     wl_state_compile st =
       (\conf progs. cc conf (MAP (\p. full_compile_single tt kk aa co (p,NONE)) progs)) /\
     coracle = (I ## MAP (\p. full_compile_single tt kk aa co (p,NONE))) o
               wl_state_compile_oracle st /\
     gc_fun_const_ok (wl_state_gc_fun st)
     ==> ?perm' clk.
           let prog = wl_Call NONE (SOME start) [0] NONE in
           let (res,rst) = wl_evaluate (prog,wl_state_permute_fupd (K perm') st) in
           if res = SOME wl_Error then T else
           let (res1,rst1) =
             wl_evaluate (prog,
               wl_state_code_fupd (K (sptree_map (I ## remove_must_terminate) l))
                 (wl_state_clock_fupd (K (wl_state_clock st + clk))
                    (wl_state_termdep_fupd (K 0)
                       (wl_state_compile_fupd (K cc)
                          (wl_state_compile_oracle_fupd (K coracle) st))))) in
           res1 = res /\
           wl_state_clock rst1 = wl_state_clock rst /\
           wl_state_ffi rst1 = wl_state_ffi rst /\
           wl_state_stack_max rst1 = wl_state_stack_max rst`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  (* compile_single_correct with the compiler cc after remove_must_terminate *)
  MP_TAC(ISPECL [`wl_Call NONE (SOME start) [0] NONE:(A)wl_prog`; `st:(A,C,FFI)wl_state`;
                 `l:(num#(A)wl_prog)spt`;
                 `(I ## MAP (\p. word_to_word_compile_single tt kk aa co (p,NONE))) o
                  wl_state_compile_oracle (st:(A,C,FFI)wl_state)`;
                 `\conf. (cc:C->(num#num#(A)wl_prog)list->(byte list#(A word)list#C)option)
                           conf o MAP (I ## I ## remove_must_terminate)`;
                 `tt:bool`; `kk:num`; `aa:num`; `co:(A)asm_config`] compile_single_correct) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[FUN_EQ_THM; o_THM; W2WPAUX_MAP_fcs]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `perm:num->num->num` MP_TAC) THEN
  W2WPAUX_NAME_PAIR_TAC `wl_evaluate (wl_Call NONE (SOME start) [0] NONE:(A)wl_prog,
                           wl_state_permute_fupd (K perm) (st:(A,C,FFI)wl_state))`
    `res:((A)wl_result)option` `rst:(A,C,FFI)wl_state` THEN
  ASM_CASES_TAC `res = SOME (wl_Error:(A)wl_result)` THENL
   [DISCH_TAC THEN MAP_EVERY EXISTS_TAC [`perm:num->num->num`; `0`] THEN ASM_REWRITE_TAC[] THEN
    CASE_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  W2WPAUX_SPLIT_EVAL_TAC `wl_Call NONE (SOME start) [0] NONE:(A)wl_prog`
    (not o W2WPAUX_has_perm) `res1:((A)wl_result)option` `rst1:(A,C,FFI)wl_state` THEN
  STRIP_TAC THEN
  (* word_remove_correct *)
  MP_TAC(ISPECL [`wl_Call NONE (SOME start) [0] NONE:(A)wl_prog`]
    (INST [`cc:C->(num#num#(A)wl_prog)list->(((8)word)list#((A)word)list#C)option`,
           `c:C->(num#num#(A)wl_prog)list->(((8)word)list#((A)word)list#C)option`]
          word_remove_correct)) THEN
  W2WPAUX_EVAL_ASM `wl_Call NONE (SOME start) [0] NONE:(A)wl_prog` (not o W2WPAUX_has_perm)
    (fun th -> DISCH_THEN(MP_TAC o C MATCH_MP th o REWRITE_RULE[IMP_CONJ] o SPEC_ALL)) THEN
  SIMP[] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `clk:num`) THEN
  MAP_EVERY EXISTS_TAC [`perm:num->num->num`; `clk:num`] THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  W2WPAUX_X_ASM_TAC `compile_state 0 cc (rst1:(A,C,FFI)wl_state)` MP_TAC THEN
  SIMP[compile_state_def; remove_must_terminate_def; W2WPAUX_oracle_fcs] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  FIRST_ASSUM(SUBST1_TAC o check (fun th ->
    is_eq(concl th) && lhs(concl th) = `rst1:(A,C,FFI)wl_state`)) THEN SIMP[]);;

(* HOL4 lines 902-904: rmt_thms and rmd_thms, the conjuncts of           *)
(* remove_must_terminate_conventions and remove_dead_prog_conventions      *)
let W2WPAUX_rmt_thms =
  CONJUNCTS (REWRITE_RULE[LET_DEF; LET_END_DEF] (SPEC_ALL remove_must_terminate_conventions));;
let W2WPAUX_rmd_thms = CONJUNCTS remove_dead_prog_conventions;;

let W2WPAUX_nsi_inst_select_exp = prove
 (`!(c:(A)asm_config) tar temp exp. no_share_inst (inst_select_exp c tar temp exp)`,
  MATCH_MP_TAC inst_select_exp_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  TRY DISCH_TAC THEN ONCE_REWRITE_TAC[inst_select_exp_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REPEAT (FIRST [COND_CASES_TAC; TOP_CASE_TAC] THEN
          SIMP[no_share_inst_def]) THEN
  SIMP[no_share_inst_def] THEN ASM_MESON_TAC[]);;

let W2WPAUX_nsi_inst_select = prove
 (`!(c:(A)asm_config) temp p. no_share_inst p ==> no_share_inst (inst_select c temp p)`,
  let gen_tac =
    REPEAT DISCH_TAC THEN ONCE_REWRITE_TAC[inst_select_def] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[no_share_inst_def]) THEN
    REPEAT (FIRST [COND_CASES_TAC; TOP_CASE_TAC] THEN
            SIMP[no_share_inst_def; o_THM; W2WPAUX_nsi_inst_select_exp]) THEN
    SIMP[no_share_inst_def; o_THM; W2WPAUX_nsi_inst_select_exp] in
  let call_tac =
    STRUCT_CASES_TAC
      (ISPEC `ret:(num list#cutsets#(A)wl_prog#num#num)option` (cases "option")) THEN
    STRUCT_CASES_TAC (ISPEC `handler:(num#(A)wl_prog#num#num)option` (cases "option")) THEN
    REWRITE_TAC[option_DISTINCT; option_INJ] THEN
    (fun (asl,w as g) ->
       MAP_EVERY (fun v -> SPEC_TAC(v,v))
         (filter (fun v -> can dest_type (type_of v) &&
                           fst(dest_type(type_of v)) = "prod") (frees w)) g) THEN
    REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ] THEN REPEAT GEN_TAC THEN
    REPEAT DISCH_TAC THEN ONCE_REWRITE_TAC[inst_select_def] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CASE_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[no_share_inst_def]) THEN
    REWRITE_TAC[no_share_inst_def] THEN CASE_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
    SIMP[distinctness "wl_prog"] THEN ASM_MESON_TAC[] in
  MATCH_MP_TAC inst_select_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  (fun (asl,w as g) ->
     if can (find_term (fun t -> is_var t && fst(dest_var t) = "handler")) w
     then call_tac g else gen_tac g));;

(* HOL4 line 906 *)
let cond16bit_inst_select_exp' = prove
 (`!x c t1 t2 exp.
     x = inst_select_exp c t1 t2 exp
     ==> no_share_inst x \/ ~(asm_config_ISA (c:(A)asm_config) = Ag32)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[W2WPAUX_nsi_inst_select_exp]);;

(* HOL4 line 917: val cond16bit_inst_select_exp =                          *)
(* cond16bit_inst_select_exp' |> SIMP_RULE std_ss [] (the same statement)   *)
let cond16bit_inst_select_exp = prove
 (`!x c t1 t2 exp.
     x = inst_select_exp c t1 t2 exp
     ==> no_share_inst x \/ ~(asm_config_ISA (c:(A)asm_config) = Ag32)`,
  ACCEPT_TAC cond16bit_inst_select_exp');;

(* HOL4 line 919 *)
let cond16bit_inst_select = prove
 (`!x c n p.
     x = inst_select c n p /\
     (no_share_inst p \/ ~(asm_config_ISA (c:(A)asm_config) = Ag32))
     ==> no_share_inst x \/ ~(asm_config_ISA c = Ag32)`,
  MESON_TAC[W2WPAUX_nsi_inst_select]);;

(* HOL4 line 932 *)
let remove_must_terminate_no_share_inst = prove
 (`!p:(A)wl_prog. no_share_inst p ==> no_share_inst (remove_must_terminate p)`,
  WPROOF2AUX_RMT_TAC [no_share_inst_def]);;

(* HOL4 line 942 *)
let full_compile_single_no_share_inst = prove
 (`!prog_info two_reg_arith reg_count alg (c:(A)asm_config).
     no_share_inst (SND (SND (FST prog_info)))
     ==> no_share_inst
           (SND (SND (full_compile_single two_reg_arith reg_count alg c prog_info)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `no_share_inst (SND (SND (word_to_word_compile_single two_reg_arith reg_count
                  alg (c:(A)asm_config) prog_info)))` MP_TAC THENL
   [REWRITE_TAC[no_share_inst_subprogs_def] THEN
    MATCH_MP_TAC compile_single_not_created_subprogs THEN
    ASM_REWRITE_TAC[GSYM no_share_inst_subprogs_def];
    ALL_TAC] THEN
  REWRITE_TAC[W2WPAUX_fcs] THEN
  SPEC_TAC(`word_to_word_compile_single two_reg_arith reg_count alg (c:(A)asm_config)
              prog_info`,`q:num#num#(A)wl_prog`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; PAIR_MAP_THM; I_THM; SND] THEN
  REWRITE_TAC[remove_must_terminate_no_share_inst]);;

(* the program that full_compile_single produces *)
let W2WPAUX_fcs_prog = prove
 (`!tra rc alg (ac:(A)asm_config) n m prog col.
     SND (SND (full_compile_single tra rc alg ac ((n,m,prog),col))) =
     remove_must_terminate
       (word_alloc n ac alg rc
          (remove_dead_prog (remove_unreach (three_to_two_reg_prog tra
             (copy_prop (word_common_subexp_elim (remove_dead_prog
                (full_ssa_cc_trans m (inst_select ac (max_var (word_simp_compile_exp prog) + 1)
                                        (word_simp_compile_exp prog)))))))))
          col)`,
  REWRITE_TAC[W2WPAUX_fcs; word_to_word_compile_single_def; LET_DEF; LET_END_DEF;
              PAIR_MAP_THM; I_THM; SND]);;

let W2WPAUX_fcs_labels = prove
 (`!tra rc alg (ac:(A)asm_config) n m prog col.
     labels_rel (wordConvs_extract_labels prog)
       (wordConvs_extract_labels (SND (SND (full_compile_single tra rc alg ac ((n,m,prog),col)))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[W2WPAUX_fcs_prog] THEN
  REWRITE_TAC[GSYM (el 4 W2WPAUX_rmt_thms); GSYM word_alloc_lab_pres;
              GSYM (el 5 W2WPAUX_rmd_thms)] THEN
  MATCH_MP_TAC labels_rel_TRANS THEN
  EXISTS_TAC `wordConvs_extract_labels (three_to_two_reg_prog tra
    (copy_prop (word_common_subexp_elim (remove_dead_prog
      (full_ssa_cc_trans m (inst_select (ac:(A)asm_config)
         (max_var (word_simp_compile_exp prog) + 1) (word_simp_compile_exp prog)))))))` THEN
  REWRITE_TAC[labels_rel_remove_unreach] THEN
  REWRITE_TAC[GSYM three_to_two_reg_prog_lab_pres; extract_labels_copy_prop;
              extract_labels_word_common_subexp_elim; GSYM (el 5 W2WPAUX_rmd_thms);
              GSYM full_ssa_cc_trans_lab_pres; GSYM inst_select_lab_pres;
              extract_labels_compile_exp]);;

let W2WPAUX_fcs_conventions = prove
 (`!tra rc alg (ac:(A)asm_config) n m prog col.
     let q = SND (SND (full_compile_single tra rc alg ac ((n,m,prog),col))) in
     flat_exp_conventions q /\
     post_alloc_conventions rc q /\
     (every_inst (inst_ok_less ac) prog /\
      asm_offset_ok 0 (asm_config_addr_offset ac) (word 0) /\
      asm_offset_ok 0 (asm_config_hw_offset ac) (word 0) /\
      asm_offset_ok 0 (asm_config_byte_offset ac) (word 0)
      ==> full_inst_ok_less ac q) /\
     (tra ==> every_inst two_reg_inst q)`,
  REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[W2WPAUX_fcs_prog] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC (el 0 W2WPAUX_rmt_thms) THEN
    MATCH_MP_TAC word_alloc_flat_exp_conventions THEN
    MATCH_MP_TAC (el 0 W2WPAUX_rmd_thms) THEN
    MATCH_MP_TAC flat_exp_conventions_remove_unreach THEN
    MATCH_MP_TAC three_to_two_reg_prog_flat_exp_conventions THEN
    MATCH_MP_TAC flat_exp_conventions_copy_prop THEN
    MATCH_MP_TAC flat_exp_conventions_word_common_subexp_elim THEN
    MATCH_MP_TAC (el 0 W2WPAUX_rmd_thms) THEN
    MATCH_MP_TAC full_ssa_cc_trans_flat_exp_conventions THEN
    REWRITE_TAC[inst_select_flat_exp_conventions];
    MATCH_MP_TAC (el 2 W2WPAUX_rmt_thms) THEN
    MATCH_MP_TAC pre_post_conventions_word_alloc THEN
    MATCH_MP_TAC (el 2 W2WPAUX_rmd_thms) THEN
    MATCH_MP_TAC pre_alloc_conventions_remove_unreach THEN
    MATCH_MP_TAC three_to_two_reg_prog_pre_alloc_conventions THEN
    MATCH_MP_TAC pre_alloc_conventions_copy_prop THEN
    MATCH_MP_TAC pre_alloc_conventions_word_common_subexp_elim THEN
    MATCH_MP_TAC (el 2 W2WPAUX_rmd_thms) THEN
    REWRITE_TAC[full_ssa_cc_trans_pre_alloc_conventions];
    STRIP_TAC THEN
    MATCH_MP_TAC (el 1 W2WPAUX_rmt_thms) THEN
    MATCH_MP_TAC word_alloc_full_inst_ok_less THEN
    MATCH_MP_TAC (el 1 W2WPAUX_rmd_thms) THEN
    MATCH_MP_TAC full_inst_ok_less_remove_unreach THEN
    MATCH_MP_TAC three_to_two_reg_prog_full_inst_ok_less THEN
    MATCH_MP_TAC full_inst_ok_less_copy_prop THEN
    MATCH_MP_TAC full_inst_ok_less_word_common_subexp_elim THEN
    MATCH_MP_TAC (el 1 W2WPAUX_rmd_thms) THEN
    MATCH_MP_TAC full_ssa_cc_trans_full_inst_ok_less THEN
    MATCH_MP_TAC inst_select_full_inst_ok_less THEN
    ASM_SIMP_TAC[compile_exp_no_inst];
    DISCH_TAC THEN
    MATCH_MP_TAC (el 3 W2WPAUX_rmt_thms) THEN
    MATCH_MP_TAC word_alloc_two_reg_inst THEN
    MATCH_MP_TAC (el 3 W2WPAUX_rmd_thms) THEN
    MATCH_MP_TAC every_inst_remove_unreach THEN
    MATCH_MP_TAC three_to_two_reg_prog_two_reg_inst THEN ASM_REWRITE_TAC[]]);;

(* lists of compiled functions, element by element *)
let W2WPAUX_MAP_ZIP_FST = prove
 (`!(f:(K#V)#B->K#W) (p:(K#V)list) (os:B list).
     LENGTH os = LENGTH p /\ (!x y. FST (f (x,y)) = FST x)
     ==> MAP FST (MAP f (ZIP p os)) = MAP FST p`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; NOT_SUC; GSYM NOT_SUC; SUC_INJ; ZIP; MAP; CONS_11] THEN
  ASM_MESON_TAC[]);;

let W2WPAUX_ALL2_MAP_ZIP = prove
 (`!(R:C->C->bool) (f:A#B->A) (g:A->C) (p:(A)list) (os:B list).
     LENGTH os = LENGTH p /\ (!x y. R (g x) (g (f (x,y))))
     ==> ALL2 R (MAP g p) (MAP g (MAP f (ZIP p os)))`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; NOT_SUC; GSYM NOT_SUC; SUC_INJ; ZIP; MAP; ALL2] THEN
  ASM_MESON_TAC[]);;

let W2WPAUX_ALL_MAP_ZIP = prove
 (`!(P:C->bool) (f:A#B->C) (p:(A)list) (os:B list).
     LENGTH os = LENGTH p /\ (!x y. MEM x p ==> P (f (x,y)))
     ==> ALL P (MAP f (ZIP p os))`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; NOT_SUC; GSYM NOT_SUC; SUC_INJ; ZIP; MAP; ALL; MEM] THEN
  ASM_MESON_TAC[]);;

let W2WPAUX_fcs_eta = prove
 (`!tra rc alg (ac:(A)asm_config) n m prog col.
     full_compile_single tra rc alg ac ((n,m,prog),col) =
     (n,m,SND (SND (full_compile_single tra rc alg ac ((n,m,prog),col))))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`tra:bool`; `rc:num`; `alg:num`; `ac:(A)asm_config`; `n:num`; `m:num`;
                 `prog:(A)wl_prog`; `col:(num spt)option`] WPROOF2AUX_fcs_FST) THEN
  SPEC_TAC(`full_compile_single tra rc alg (ac:(A)asm_config) ((n,m,prog),col)`,
           `q:num#num#(A)wl_prog`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST; SND; PAIR_EQ] THEN MESON_TAC[]);;

(* HOL4 line 958 *)
let compile_to_word_conventions = prove
 (CASE_TERM
  `!p (ac:(A)asm_config) wc.
     ALL (\(x1,x2,prg). no_share_inst prg \/ ~(asm_config_ISA ac = Ag32)) p
     ==> let (col,progs) = word_to_word_compile wc ac p in
         MAP FST progs = MAP FST p /\
         ALL2 labels_rel (MAP (wordConvs_extract_labels o SND o SND) p)
                         (MAP (wordConvs_extract_labels o SND o SND) progs) /\
         ALL (\(n,m,prog).
                flat_exp_conventions prog /\
                post_alloc_conventions
                  (asm_config_reg_count ac - (5 + LENGTH (asm_config_avoid_regs ac))) prog /\
                (ALL (\(n,m,prog). every_inst (inst_ok_less ac) prog) p /\
                 asm_offset_ok 0 (asm_config_addr_offset ac) (word 0) /\
                 asm_offset_ok 0 (asm_config_hw_offset ac) (word 0) /\
                 asm_offset_ok 0 (asm_config_byte_offset ac) (word 0)
                 ==> full_inst_ok_less ac prog) /\
                (asm_config_two_reg_arith ac ==> every_inst two_reg_inst prog) /\
                (no_share_inst prog \/ ~(asm_config_ISA ac = Ag32))) progs`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPEC `word_to_word_compile wc (ac:(A)asm_config) p` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `col:((num spt)option)list` (X_CHOOSE_THEN
    `progs:(num#num#(A)wl_prog)list` (fun th -> REWRITE_TAC[th] THEN
      MP_TAC(AP_TERM `SND:((num spt)option)list#(num#num#(A)wl_prog)list->
                          (num#num#(A)wl_prog)list` th)))) THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[WPROOF2AUX_w2w_SND; SND] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  ABBREV_TAC `os = FST (next_n_oracle (LENGTH (p:(num#num#(A)wl_prog)list))
                          (word_to_word_config_col_oracle wc))` THEN
  SUBGOAL_THEN `LENGTH (os:((num spt)option)list) = LENGTH (p:(num#num#(A)wl_prog)list)`
    ASSUME_TAC THENL
   [EXPAND_TAC "os" THEN REWRITE_TAC[WPROOF2AUX_next_n_oracle_LENGTH]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC W2WPAUX_MAP_ZIP_FST THEN ASM_REWRITE_TAC[FORALL_PAIR_THM] THEN
    REWRITE_TAC[WPROOF2AUX_fcs_FST];
    MATCH_MP_TAC W2WPAUX_ALL2_MAP_ZIP THEN ASM_REWRITE_TAC[FORALL_PAIR_THM; o_THM; SND] THEN
    REWRITE_TAC[W2WPAUX_fcs_labels];
    MATCH_MP_TAC W2WPAUX_ALL_MAP_ZIP THEN ASM_REWRITE_TAC[FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `m:num`; `prog:(A)wl_prog`; `y:(num spt)option`] THEN
    DISCH_TAC THEN ONCE_REWRITE_TAC[W2WPAUX_fcs_eta] THEN
    CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
    MP_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV) (SPECL
      [`asm_config_two_reg_arith (ac:(A)asm_config)`;
       `asm_config_reg_count (ac:(A)asm_config) - (5 + LENGTH (asm_config_avoid_regs ac))`;
       `word_to_word_config_reg_alg wc`; `ac:(A)asm_config`; `n:num`; `m:num`;
       `prog:(A)wl_prog`; `y:(num spt)option`] W2WPAUX_fcs_conventions)) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `inst_ok_less (ac:(A)asm_config)`)) (concl th))) THEN
      REWRITE_TAC[GSYM ALL_MEM] THEN DISCH_THEN(MP_TAC o SPEC `(n:num,m:num,prog:(A)wl_prog)`) THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[];
      UNDISCH_TAC `ALL (\(x1,x2,prg). no_share_inst prg \/ ~(asm_config_ISA (ac:(A)asm_config) = Ag32))
                       (p:(num#num#(A)wl_prog)list)` THEN
      REWRITE_TAC[GSYM ALL_MEM] THEN DISCH_THEN(MP_TAC o SPEC `(n:num,m:num,prog:(A)wl_prog)`) THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
      MP_TAC(REWRITE_RULE[FST; SND] (ISPECL
        [`((n:num,m:num,prog:(A)wl_prog),(y:(num spt)option))`;
         `asm_config_two_reg_arith (ac:(A)asm_config)`;
         `asm_config_reg_count (ac:(A)asm_config) - (5 + LENGTH (asm_config_avoid_regs ac))`;
         `word_to_word_config_reg_alg wc`; `ac:(A)asm_config`]
        full_compile_single_no_share_inst)) THEN
      CONV_TAC TAUT]]);;

let W2WPAUX_code_rel_lookup = prove
 (`!(c1:(num#(A)wl_prog)spt) c2 n m e m' e'.
     word_to_wordProof_code_rel c1 c2 /\ lookup n c1 = SOME (m,e) /\
     lookup n c2 = SOME (m',e')
     ==> ?t k a c col.
           e' = SND (SND (word_to_word_compile_single t k a c ((n,m,e),col)))`,
  REWRITE_TAC[word_to_wordProof_code_rel_def] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `(m:num,e:(A)wl_prog)`]) THEN
  ASM_REWRITE_TAC[option_INJ] THEN
  ONCE_REWRITE_TAC[W2WPAUX_SND_compile_single] THEN
  REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[]);;

let W2WPAUX_cs_ncs = prove
 (`!P t k a (c:(A)asm_config) n m e col.
     not_created_subprogs P e
     ==> not_created_subprogs P (SND (SND (word_to_word_compile_single t k a c ((n,m,e),col))))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC compile_single_not_created_subprogs THEN
  ASM_REWRITE_TAC[FST; SND]);;

(* HOL4 line 1067 *)
let code_rel_not_created_subprogs = prove
 (`!op (args:((B)word_loc)list) c1 (sz:(C)spt) v c2 P v'.
     wl_find_code op args c1 sz = SOME v /\
     word_to_wordProof_code_rel (c1:(num # (A)wl_prog)spt) c2 /\
     not_created_subprogs P (FST (SND v)) /\
     wl_find_code op args c2 sz = SOME v'
     ==> not_created_subprogs P (FST (SND v'))`,
  REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `op:num option` (cases "option")) THEN
  REWRITE_TAC[W2WPAUX_find_code_SOME; W2WPAUX_find_code_NONE] THEN STRIP_TAC THENL
   [SUBGOAL_THEN `loc' = loc:num` SUBST_ALL_TAC THENL
     [UNDISCH_TAC `LAST (args:((B)word_loc)list) = wl_Loc loc 0` THEN
      ASM_REWRITE_TAC[injectivity "word_loc"] THEN MESON_TAC[];
      ALL_TAC];
    ALL_TAC] THEN
  ASM_MESON_TAC[W2WPAUX_code_rel_lookup; W2WPAUX_cs_ncs]);;

(* HOL4 line 1082: code_rel_P = Q.GEN P code_rel_not_created_subprogs   *)
let code_rel_P = prove
 (`!P op (args:((B)word_loc)list) c1 (sz:(C)spt) v c2 v'.
     wl_find_code op args c1 sz = SOME v /\
     word_to_wordProof_code_rel (c1:(num # (A)wl_prog)spt) c2 /\
     not_created_subprogs P (FST (SND v)) /\
     wl_find_code op args c2 sz = SOME v'
     ==> not_created_subprogs P (FST (SND v'))`,
  MESON_TAC[code_rel_not_created_subprogs]);;

(* HOL4 line 1084: code_rel_P at (<>) (Alloc 0 (LN,LN)), folded with      *)
(* GSYM no_alloc_subprogs_def                                                *)
let code_rel_no_alloc = prove
 (`!op (args:((B)word_loc)list) c1 (sz:(C)spt) v c2 v'.
     wl_find_code op args c1 sz = SOME v /\
     word_to_wordProof_code_rel (c1:(num # (A)wl_prog)spt) c2 /\
     no_alloc (FST (SND v)) /\
     wl_find_code op args c2 sz = SOME v'
     ==> no_alloc (FST (SND v'))`,
  REWRITE_TAC[no_alloc_subprogs_def; code_rel_P]);;

(* HOL4 line 1087: code_rel_P at (<>) (Install 0 0 0 0 (LN,LN)), folded    *)
(* with GSYM no_install_subprogs_def                                         *)
let code_rel_no_install = prove
 (`!op (args:((B)word_loc)list) c1 (sz:(C)spt) v c2 v'.
     wl_find_code op args c1 sz = SOME v /\
     word_to_wordProof_code_rel (c1:(num # (A)wl_prog)spt) c2 /\
     wordConvs_no_install (FST (SND v)) /\
     wl_find_code op args c2 sz = SOME v'
     ==> wordConvs_no_install (FST (SND v'))`,
  REWRITE_TAC[wordConvs_no_install_subprogs_def; code_rel_P]);;

(* ------------------------------------------------------------------------- *)
(* no_install_no_alloc_compile_single_correct (HOL4 proves it like           *)
(* compile_single_correct, case by case): here it follows from               *)
(* compile_single_correct and W2WPAUX_ni_irr, an induction with evaluate_ind *)
(* showing that programs without Install (in code without Install) evaluate  *)
(* the same for every compiler and compiler oracle.                          *)
(* ------------------------------------------------------------------------- *)

(* evaluation of programs without Install (in a code without Install) does  *)
(* not depend on the compiler and the oracle                                 *)
let W2WPAUX_ni_P = `\(prog:(A)wl_prog) (s:(A,C,FFI)wl_state).
   !c orc. wordConvs_no_install prog /\ no_install_code (wl_state_code s)
   ==> wl_evaluate (prog, wl_state_compile_fupd (K c) (wl_state_compile_oracle_fupd (K orc) s)) =
       (I ## (\t. wl_state_compile_fupd (K c) (wl_state_compile_oracle_fupd (K orc) t)))
         (wl_evaluate (prog,s))`;;

let W2WPAUX_NI_NONREC_TAC : tactic =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [wl_evaluate_def] THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [wl_evaluate_def] THEN
  SIMP (W2WPAUX_dec_clock_upd :: W2WPAUX_UPD_THMS) THEN
  REPEAT (CASE_TAC THEN SIMP (PAIR_MAP_THM :: I_THM :: W2WPAUX_dec_clock_upd ::
                             W2WPAUX_UPD_THMS)) THEN
  SIMP[PAIR_MAP_THM; I_THM; W2WPAUX_flush_state_upd; W2WPAUX_dec_clock_upd];;

(* unfold one step of evaluate on both sides of the goal *)
let W2WPAUX_NI_UNFOLD_TAC : tactic =
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [wl_evaluate_def] THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [wl_evaluate_def];;

let W2WPAUX_NI_SIMPS = PAIR_MAP_THM :: I_THM :: W2WPAUX_dec_clock_upd :: W2WPAUX_UPD_THMS;;

(* code that runs without Install keeps its code *)
let W2WPAUX_ni_code = prove
 (`!prog (s:(A,C,FFI)wl_state) r t.
     wl_evaluate (prog,s) = (r,t) /\ wordConvs_no_install prog /\
     no_install_code (wl_state_code s)
     ==> wl_state_code t = wl_state_code s /\ no_install_code (wl_state_code t)`,
  MESON_TAC[no_install_evaluate_const_code]);;

(* use the induction hypothesis th on the program p at the state s' *)
let W2WPAUX_NI_IH_TAC (th:thm) : tactic =
  MP_TAC(SPECL [`c:C->(num#num#(A)wl_prog)list->(byte list#(A word)list#C)option`;
                `orc:num->C#(num#num#(A)wl_prog)list`] th) THEN
  TRY(ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SIMP[] THEN ASM_MESON_TAC[W2WPAUX_ni_code];
                      ALL_TAC]) THEN
  SIMP_NOASM W2WPAUX_NI_SIMPS THEN DISCH_THEN(fun th -> REWRITE_TAC[th]);;

let W2WPAUX_NI_MT_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "ih") THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wordConvs_no_install_def]) THEN
  W2WPAUX_NI_UNFOLD_TAC THEN SIMP W2WPAUX_NI_SIMPS THEN
 COND_CASES_TAC THENL [ASM_REWRITE_TAC[PAIR_MAP_THM; I_THM] THEN SIMP[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REMOVE_THEN "ih" (MP_TAC o C MATCH_MP (ASSUME `~(wl_state_termdep (s:(A,C,FFI)wl_state) = 0)`)) THEN
  DISCH_THEN W2WPAUX_NI_IH_TAC THEN
  W2WPAUX_SPLIT_EVAL_TAC `p:(A)wl_prog` (K true) `r1:((A)wl_result)option` `s1:(A,C,FFI)wl_state` THEN
  REWRITE_TAC[PAIR_MAP_THM; I_THM] THEN CASE_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN SIMP W2WPAUX_NI_SIMPS;;

let W2WPAUX_NI_SEQ_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wordConvs_no_install_def]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  W2WPAUX_NI_UNFOLD_TAC THEN
  REMOVE_THEN "ih1" W2WPAUX_NI_IH_TAC THEN
  W2WPAUX_NAME_PAIR_TAC `wl_evaluate (c1:(A)wl_prog,s:(A,C,FFI)wl_state)`
    `r1:((A)wl_result)option` `s1:(A,C,FFI)wl_state` THEN
  REWRITE_TAC[PAIR_MAP_THM; I_THM] THEN CASE_REWRITE_TAC[] THEN
  ASM_CASES_TAC `r1:((A)wl_result)option = NONE` THEN ASM_REWRITE_TAC[PAIR_MAP_THM; I_THM] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  REMOVE_THEN "ih2" (MP_TAC o SPEC `s1:(A,C,FFI)wl_state`) THEN
  REWRITE_TAC[] THEN DISCH_THEN W2WPAUX_NI_IH_TAC;;

let W2WPAUX_NI_CLOSE_TAC : tactic = SIMP W2WPAUX_NI_SIMPS THEN NO_TAC;;

(* the induction hypothesis th applied at the terms xs, then closing *)
let W2WPAUX_NI_IH_AT_TAC (lab:string) (xs:term list) : tactic =
  REMOVE_THEN lab (fun th ->
    MP_TAC(SPECL (xs @ [`c:C->(num#num#(A)wl_prog)list->(byte list#(A word)list#C)option`;
                        `orc:num->C#(num#num#(A)wl_prog)list`])
                 (REWRITE_RULE[IMP_IMP; RIGHT_IMP_FORALL_THM] th))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[add_ret_loc_def; wl_STOP_def; wordConvs_no_install_def] THEN SIMP[] THEN
    ASM_MESON_TAC[W2WPAUX_ni_code];
    ALL_TAC] THEN
  SIMP_NOASM (wl_STOP_def :: W2WPAUX_NI_SIMPS) THEN DISCH_THEN(fun th -> REWRITE_TAC[th]);;

let W2WPAUX_NI_IF_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wordConvs_no_install_def]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  W2WPAUX_NI_UNFOLD_TAC THEN SIMP W2WPAUX_NI_SIMPS THEN
  WPROOF1AUX_OCASES_TAC "wl_get_var" `x:(A)word_loc` THEN TRY W2WPAUX_NI_CLOSE_TAC THEN
  WPROOF1AUX_OCASES_TAC "wl_get_var_imm" `y:(A)word_loc` THEN TRY W2WPAUX_NI_CLOSE_TAC THEN
  WPROOF1AUX_OCASES_TAC "wl_word_cmp" `b:bool` THEN TRY W2WPAUX_NI_CLOSE_TAC THEN
  COND_CASES_TAC THENL
   [W2WPAUX_NI_IH_AT_TAC "ih1" [`x:(A)word_loc`; `y:(A)word_loc`; `b:bool`];
    W2WPAUX_NI_IH_AT_TAC "ih2" [`x:(A)word_loc`; `y:(A)word_loc`; `b:bool`]];;

let W2WPAUX_NI_LOOP_TAC : tactic =
  WPROOF1AUX_NAMED_GEN_TAC ["names"; "body"; "exit_names"; "s"] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wordConvs_no_install_def]) THEN
  W2WPAUX_NI_UNFOLD_TAC THEN SIMP W2WPAUX_NI_SIMPS THEN
  WPROOF1AUX_OCASES_TAC "wl_cut_state" `s':(A,C,FFI)wl_state` THEN TRY W2WPAUX_NI_CLOSE_TAC THEN
  REWRITE_TAC[OPTION_MAP_DEF] THEN CASE_REWRITE_TAC[] THEN
  SUBGOAL_THEN `no_install_code (wl_state_code (s':(A,C,FFI)wl_state))` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP cut_state_const o
      check (fun th -> can (term_match [] `wl_cut_state x (y:(A,C,FFI)wl_state) = SOME z`)
                           (concl th))) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN SIMP[];
    ALL_TAC] THEN
  W2WPAUX_NI_IH_AT_TAC "ih2" [`s':(A,C,FFI)wl_state`] THEN
  W2WPAUX_NAME_PAIR_TAC `wl_evaluate (body:(A)wl_prog,s':(A,C,FFI)wl_state)`
    `r1:((A)wl_result)option` `s1:(A,C,FFI)wl_state` THEN
  REWRITE_TAC[PAIR_MAP_THM; I_THM] THEN CASE_REWRITE_TAC[] THEN SIMP W2WPAUX_NI_SIMPS THEN
  ASM_CASES_TAC `wl_cont_loop (r1:((A)wl_result)option)` THEN ASM_REWRITE_TAC[] THENL
   [ASM_CASES_TAC `wl_state_clock (s1:(A,C,FFI)wl_state) = 0` THEN ASM_REWRITE_TAC[] THEN
    TRY W2WPAUX_NI_CLOSE_TAC THEN REWRITE_TAC[wl_STOP_def] THEN
    W2WPAUX_NI_IH_AT_TAC "ih1" [`s':(A,C,FFI)wl_state`; `r1:((A)wl_result)option`;
                                `s1:(A,C,FFI)wl_state`];
    COND_CASES_TAC THEN TRY W2WPAUX_NI_CLOSE_TAC THEN
    WPROOF1AUX_OCASES_TAC "wl_cut_state" `s2:(A,C,FFI)wl_state` THEN
    REWRITE_TAC[OPTION_MAP_DEF] THEN CASE_REWRITE_TAC[] THEN W2WPAUX_NI_CLOSE_TAC];;

let W2WPAUX_NI_INSTALL_TAC : tactic =
  REPEAT GEN_TAC THEN REWRITE_TAC[wordConvs_no_install_def] THEN SIMP[];;

let W2WPAUX_NI_CALL_TAC : tactic =
  WPROOF1AUX_NAMED_GEN_TAC ["ret"; "dest"; "args"; "handler"; "s"] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ihT") (CONJUNCTS_THEN2 (LABEL_TAC "ihR")
    (CONJUNCTS_THEN2 (LABEL_TAC "ihE") (LABEL_TAC "ihB")))) THEN
  REPEAT GEN_TAC THEN
  DISJ_CASES_THEN2 SUBST_ALL_TAC
   (X_CHOOSE_THEN `rv:num list#cutsets#(A)wl_prog#num#num` SUBST_ALL_TAC)
   (ISPEC `ret:(num list#cutsets#(A)wl_prog#num#num)option` (cases "option")) THEN
  DISJ_CASES_THEN2 SUBST_ALL_TAC
   (X_CHOOSE_THEN `hv:num#(A)wl_prog#num#num` SUBST_ALL_TAC)
   (ISPEC `handler:(num#(A)wl_prog#num#num)option` (cases "option")) THEN
  TRY(MP_TAC(ISPEC `rv:num list#cutsets#(A)wl_prog#num#num` BASICAUX_TUPLE5) THEN
      DISCH_THEN(X_CHOOSE_THEN `n:num list` (X_CHOOSE_THEN `names:cutsets`
        (X_CHOOSE_THEN `rh:(A)wl_prog` (X_CHOOSE_THEN `l1:num`
          (X_CHOOSE_THEN `l2:num` SUBST_ALL_TAC)))))) THEN
  TRY(MP_TAC(ISPEC `hv:num#(A)wl_prog#num#num` BASICAUX_TUPLE4) THEN
      DISCH_THEN(X_CHOOSE_THEN `hn:num` (X_CHOOSE_THEN `hp:(A)wl_prog`
        (X_CHOOSE_THEN `hl1:num` (X_CHOOSE_THEN `hl2:num` SUBST_ALL_TAC))))) THEN
  STRIP_TAC THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[] o REWRITE_RULE[wordConvs_no_install_def]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  W2WPAUX_NI_UNFOLD_TAC THEN SIMP (add_ret_loc_def :: W2WPAUX_NI_SIMPS) THEN
  WPROOF1AUX_OCASES_TAC "wl_get_vars" `xs:((A)word_loc)list` THEN TRY W2WPAUX_NI_CLOSE_TAC THEN
  (ASM_CASES_TAC `bad_dest_args (dest:num option) (args:num list)` THEN ASM_REWRITE_TAC[]) THEN
  TRY W2WPAUX_NI_CLOSE_TAC THEN
  WPROOF1AUX_OCASES_TAC "wl_find_code"
    `(args1:((A)word_loc)list,prog:(A)wl_prog,ss:num option)` THEN TRY W2WPAUX_NI_CLOSE_TAC THEN
  (SUBGOAL_THEN `wordConvs_no_install (prog:(A)wl_prog)` ASSUME_TAC THENL
    [ASM_MESON_TAC[no_install_find_code]; ALL_TAC]);;

let W2WPAUX_NI_TAILCALL_TAC : tactic =
  COND_CASES_TAC THENL [W2WPAUX_NI_CLOSE_TAC; ALL_TAC] THEN
  W2WPAUX_NI_IH_AT_TAC "ihT" [`xs:((A)word_loc)list`; `prog:(A)wl_prog`;
                              `args1:((A)word_loc)list`; `ss:num option`] THEN
  W2WPAUX_NAME_PAIR_TAC
    `wl_evaluate (prog:(A)wl_prog, wl_call_env args1 ss (wl_dec_clock (s:(A,C,FFI)wl_state)))`
    `r:((A)wl_result)option` `t:(A,C,FFI)wl_state` THEN
  REWRITE_TAC[FST; SND] THEN COND_CASES_TAC THEN W2WPAUX_NI_CLOSE_TAC;;

let W2WPAUX_has_U t =
  can (find_term (fun u -> is_const u && fst(dest_const u) = "wl_state_compile_fupd")) t;;

(* the code after an evaluation (without Install) of the program p *)
let W2WPAUX_NI_CODE_TAC (p:term) : tactic =
  W2WPAUX_EVAL_ASM p (not o W2WPAUX_has_U) (fun th ->
    let q,x = dest_pair(rand(lhs(concl th))) in
    let r,t = dest_pair(rhs(concl th)) in
    MP_TAC (ISPECL [q; x; r; t] W2WPAUX_ni_code)) THEN
  ASM_REWRITE_TAC[] THEN SIMP[] THEN STRIP_TAC;;

let W2WPAUX_NI_RETCALL_TAC : tactic =
  COND_CASES_TAC THENL [W2WPAUX_NI_CLOSE_TAC; ALL_TAC] THEN
  WPROOF1AUX_OCASES_TAC "cut_envs" `envs:((A)word_loc)spt#((A)word_loc)spt` THEN
  TRY W2WPAUX_NI_CLOSE_TAC THEN
  COND_CASES_TAC THENL [W2WPAUX_NI_CLOSE_TAC; ALL_TAC] THEN
  W2WPAUX_NI_IH_AT_TAC "ihB" [`xs:((A)word_loc)list`; `rh:(A)wl_prog`; `l1:num`; `l2:num`;
     `n:num list`; `names:cutsets`; `prog:(A)wl_prog`; `args1:((A)word_loc)list`;
     `ss:num option`; `envs:((A)word_loc)spt#((A)word_loc)spt`] THEN
  W2WPAUX_SPLIT_EVAL_TAC `prog:(A)wl_prog` (not o W2WPAUX_has_U)
    `r:((A)wl_result)option` `s2:(A,C,FFI)wl_state` THEN
  REWRITE_TAC[FST; SND] THEN W2WPAUX_NI_CODE_TAC `prog:(A)wl_prog` THEN
  DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `rr:(A)wl_result` SUBST_ALL_TAC)
   (ISPEC `r:((A)wl_result)option` (cases "option")) THEN
  CASE_REWRITE_TAC[] THEN TRY W2WPAUX_NI_CLOSE_TAC THEN
  REPEAT_TCL DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC)
    (ISPEC `rr:(A)wl_result` (cases "wl_result")) THEN
  CASE_REWRITE_TAC[] THEN TRY W2WPAUX_NI_CLOSE_TAC THEN
  ALL_TAC;;

let W2WPAUX_NI_RESULT_TAC : tactic =
  COND_CASES_TAC THENL [W2WPAUX_NI_CLOSE_TAC; ALL_TAC] THEN
  WPROOF1AUX_OCASES_TAC "wl_pop_env" `s1:(A,C,FFI)wl_state` THEN
  REWRITE_TAC[OPTION_MAP_DEF] THEN CASE_REWRITE_TAC[] THEN TRY W2WPAUX_NI_CLOSE_TAC THEN
  SIMP W2WPAUX_NI_SIMPS THEN
  COND_CASES_TAC THENL [ALL_TAC; W2WPAUX_NI_CLOSE_TAC] THEN
  SUBGOAL_THEN `no_install_code (wl_state_code (s1:(A,C,FFI)wl_state))` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP wl_pop_env_const o
      check (fun th -> can (term_match [] `wl_pop_env (x:(A,C,FFI)wl_state) = SOME y`)
                           (concl th))) THEN
    SIMP[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  W2WPAUX_NI_IH_AT_TAC "ihR" [`xs:((A)word_loc)list`; `names:cutsets`; `prog:(A)wl_prog`;
     `args1:((A)word_loc)list`; `ss:num option`; `a0:(A)word_loc`; `l1:num`; `l2:num`;
     `s2:(A,C,FFI)wl_state`; `envs:((A)word_loc)spt#((A)word_loc)spt`; `rh:(A)wl_prog`;
     `n:num list`; `a1:((A)word_loc)list`; `s1:(A,C,FFI)wl_state`];;

let W2WPAUX_NI_EXC_TAC : tactic =
  COND_CASES_TAC THENL [W2WPAUX_NI_CLOSE_TAC; ALL_TAC] THEN
  COND_CASES_TAC THENL [ALL_TAC; W2WPAUX_NI_CLOSE_TAC] THEN
  W2WPAUX_NI_IH_AT_TAC "ihE" [`xs:((A)word_loc)list`; `rh:(A)wl_prog`; `l1:num`; `l2:num`;
     `n:num list`; `names:cutsets`; `prog:(A)wl_prog`; `args1:((A)word_loc)list`;
     `ss:num option`; `a0:(A)word_loc`; `hl1:num`; `hl2:num`;
     `envs:((A)word_loc)spt#((A)word_loc)spt`; `hp:(A)wl_prog`; `hn:num`;
     `a1:(A)word_loc`; `s2:(A,C,FFI)wl_state`];;

let W2WPAUX_ni_irr = prove
 (let g = W2WPAUX_head_beta
            (list_mk_comb(W2WPAUX_ni_P,[`prog:(A)wl_prog`;`s:(A,C,FFI)wl_state`])) in
  list_mk_forall([`prog:(A)wl_prog`;`s:(A,C,FFI)wl_state`], g),
  IL2AUX_EVAL_IND_TAC wl_evaluate_ind THEN REPEAT CONJ_TAC THENL
   (replicate W2WPAUX_NI_NONREC_TAC 11 @
    [W2WPAUX_NI_MT_TAC; W2WPAUX_NI_SEQ_TAC] @
    replicate W2WPAUX_NI_NONREC_TAC 4 @
    [W2WPAUX_NI_IF_TAC; W2WPAUX_NI_LOOP_TAC; W2WPAUX_NI_NONREC_TAC; W2WPAUX_NI_INSTALL_TAC] @
    replicate W2WPAUX_NI_NONREC_TAC 4 @
    [W2WPAUX_NI_CALL_TAC THENL
      [W2WPAUX_NI_TAILCALL_TAC;
       W2WPAUX_NI_RETCALL_TAC THEN W2WPAUX_NI_RESULT_TAC;
       W2WPAUX_NI_RETCALL_TAC THENL [W2WPAUX_NI_RESULT_TAC; W2WPAUX_NI_EXC_TAC]]]));;

(* the irrelevance lemma as an equation of pairs, and the oracle and the  *)
(* compiler of the result                                                 *)
let W2WPAUX_ni_irr2 = prove
 (`!prog (s:(A,C,FFI)wl_state) c orc res t.
     wordConvs_no_install prog /\ no_install_code (wl_state_code s) /\
     wl_evaluate (prog,s) = (res,t)
     ==> wl_evaluate (prog, wl_state_compile_fupd (K c) (wl_state_compile_oracle_fupd (K orc) s)) =
         (res, wl_state_compile_fupd (K c) (wl_state_compile_oracle_fupd (K orc) t)) /\
         wl_state_compile_oracle t = wl_state_compile_oracle s /\
         wl_state_compile t = wl_state_compile s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MP_TAC(SPECL [`prog:(A)wl_prog`; `s:(A,C,FFI)wl_state`] W2WPAUX_ni_irr) THEN
    ASM_REWRITE_TAC[PAIR_MAP_THM; I_THM] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  MP_TAC(SPECL [`prog:(A)wl_prog`; `s:(A,C,FFI)wl_state`] W2WPAUX_ni_irr) THEN
  ASM_REWRITE_TAC[PAIR_MAP_THM; I_THM] THEN
  DISCH_THEN(MP_TAC o SPECL [`wl_state_compile (s:(A,C,FFI)wl_state)`;
                             `wl_state_compile_oracle (s:(A,C,FFI)wl_state)`]) THEN
  SUBGOAL_THEN `wl_state_compile_fupd (K (wl_state_compile s))
                  (wl_state_compile_oracle_fupd (K (wl_state_compile_oracle s)) s) =
                (s:(A,C,FFI)wl_state)` SUBST1_TAC THENL
   [SIMP[wl_state_component_equality]; ALL_TAC] THEN
  ASM_REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th]) THEN SIMP[]);;

(* code related to a code without a construct has no such construct *)
let W2WPAUX_code_rel_nc = prove
 (`!(c1:(num#(A)wl_prog)spt) c2 P.
     word_to_wordProof_code_rel c1 c2 /\ domain c1 = domain c2 /\
     (!k n p. lookup k c1 = SOME (n,p) ==> not_created_subprogs P p)
     ==> (!k n p. lookup k c2 = SOME (n,p) ==> not_created_subprogs P p)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?m e. lookup k (c1:(num#(A)wl_prog)spt) = SOME (m,e)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `domain (c1:(num#(A)wl_prog)spt) = domain (c2:(num#(A)wl_prog)spt)` THEN
    REWRITE_TAC[EXTENSION; domain_lookup; EXISTS_PAIR_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `k:num`) THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c1:(num#(A)wl_prog)spt`; `c2:(num#(A)wl_prog)spt`; `k:num`; `m:num`;
                 `e:(A)wl_prog`; `n:num`; `p:(A)wl_prog`] W2WPAUX_code_rel_lookup) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC W2WPAUX_cs_ncs THEN ASM_MESON_TAC[]);;

let W2WPAUX_oracle_same = prove
 (`!s:(A,C,FFI)wl_state. wl_state_compile_oracle_fupd (K (wl_state_compile_oracle s)) s = s`,
  SIMP[wl_state_component_equality]);;

(* HOL4 line 1092: derived from compile_single_correct (for a compiler of   *)
(* the form compile_single_correct needs, ARB here) and W2WPAUX_ni_irr2:     *)
(* without Install the compiler and the oracle do not matter                *)
let no_install_no_alloc_compile_single_correct = prove
 (CASE_TERM
  `!prog (st:(A,C,FFI)wl_state) l.
     word_to_wordProof_code_rel (wl_state_code st) l /\
     wordConvs_no_install prog /\ no_alloc prog /\
     no_install_code (wl_state_code st) /\ no_alloc_code (wl_state_code st) /\
     domain (wl_state_code st) = domain l /\
     gc_fun_const_ok (wl_state_gc_fun st)
     ==> ?perm'.
           let (res,rst) = wl_evaluate (prog,wl_state_permute_fupd (K perm') st) in
           if res = SOME wl_Error then T
           else
             let (res1,rst1) = wl_evaluate (prog,wl_state_code_fupd (K l) st) in
             res1 = res /\
             word_to_wordProof_code_rel (wl_state_code rst) (wl_state_code rst1) /\
             domain (wl_state_code rst) = domain (wl_state_code rst1) /\
             rst1 = wl_state_code_fupd (K (wl_state_code rst1)) rst`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `no_install_code (l:(num#(A)wl_prog)spt)` ASSUME_TAC THENL
   [UNDISCH_TAC `no_install_code (wl_state_code (st:(A,C,FFI)wl_state))` THEN
    REWRITE_TAC[no_install_code_def; wordConvs_no_install_subprogs_def] THEN
    DISCH_TAC THEN MATCH_MP_TAC W2WPAUX_code_rel_nc THEN
    EXISTS_TAC `wl_state_code (st:(A,C,FFI)wl_state)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`prog:(A)wl_prog`;
     `wl_state_compile_fupd
        (K (\conf progs. (ARB:C->(num#num#(A)wl_prog)list->(byte list#(A word)list#C)option)
                          conf (MAP (\p. word_to_word_compile_single F 0 0 (ARB:(A)asm_config) (p,NONE))
                                progs)))
        (st:(A,C,FFI)wl_state)`;
     `l:(num#(A)wl_prog)spt`;
     `(I ## MAP (\p. word_to_word_compile_single F 0 0 (ARB:(A)asm_config) (p,NONE))) o
      wl_state_compile_oracle (st:(A,C,FFI)wl_state)`;
     `ARB:C->(num#num#(A)wl_prog)list->(byte list#(A word)list#C)option`;
     `F`; `0`; `0`; `ARB:(A)asm_config`] compile_single_correct) THEN
  ASM_REWRITE_TAC[] THEN SIMP[] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `perm:num->num->num` (LABEL_TAC "CSC")) THEN
   EXISTS_TAC `perm:num->num->num` THEN REMOVE_THEN "CSC" MP_TAC THEN
   W2WPAUX_NAME_PAIR_TAC `wl_evaluate (prog:(A)wl_prog, wl_state_permute_fupd (K perm)
                            (st:(A,C,FFI)wl_state))` `res:((A)wl_result)option` `rst:(A,C,FFI)wl_state` THEN
   W2WPAUX_NAME_PAIR_TAC `wl_evaluate (prog:(A)wl_prog, wl_state_code_fupd (K l)
                            (st:(A,C,FFI)wl_state))` `res1:((A)wl_result)option` `rst1:(A,C,FFI)wl_state` THEN
   MP_TAC(ISPECL [`prog:(A)wl_prog`; `wl_state_permute_fupd (K perm) (st:(A,C,FFI)wl_state)`;
     `\conf progs. (ARB:C->(num#num#(A)wl_prog)list->(byte list#(A word)list#C)option)
                     conf (MAP (\p. word_to_word_compile_single F 0 0 (ARB:(A)asm_config) (p,NONE))
                                progs)`;
     `wl_state_compile_oracle (wl_state_permute_fupd (K perm) (st:(A,C,FFI)wl_state))`;
     `res:((A)wl_result)option`; `rst:(A,C,FFI)wl_state`] W2WPAUX_ni_irr2) THEN
   REWRITE_TAC[W2WPAUX_oracle_same] THEN ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SIMP[]; ALL_TAC] THEN
   DISCH_THEN(STRIP_ASSUME_TAC o CAKE_SIMP_RULE[]) THEN
   MP_TAC(ISPECL [`prog:(A)wl_prog`; `wl_state_code_fupd (K l) (st:(A,C,FFI)wl_state)`;
     `ARB:C->(num#num#(A)wl_prog)list->(byte list#(A word)list#C)option`;
     `(I ## MAP (\p. word_to_word_compile_single F 0 0 (ARB:(A)asm_config) (p,NONE))) o
      wl_state_compile_oracle (st:(A,C,FFI)wl_state)`;
     `res1:((A)wl_result)option`; `rst1:(A,C,FFI)wl_state`] W2WPAUX_ni_irr2) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SIMP[]; ALL_TAC] THEN
   STRIP_TAC THEN SIMP[] THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `res = SOME (wl_Error:(A)wl_result)` THEN ASM_REWRITE_TAC[] THEN
   DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
   FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) && W2WPAUX_has_U (lhs(concl th)) &&
                                          not (is_comb (lhs(concl th)) &&
                                               is_const(rator(lhs(concl th))) &&
                                               fst(dest_const(rator(lhs(concl th)))) = "wl_evaluate"))) THEN
   REWRITE_TAC[wl_state_component_equality] THEN SIMP[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
   SIMP[]);;

(* HOL4 line 2102 *)
let no_mt_remove_must_terminate_const = prove
 (`!prog:(A)wl_prog. no_mt prog ==> remove_must_terminate prog = prog`,
  WPROOF2AUX_RMT_TAC [no_mt_def]);;

(* HOL4 line 2111 *)
let no_mt_full_compile_single = prove
 (`!x tt kk aa (c:(A)asm_config).
     no_mt (SND (SND (FST x)))
     ==> full_compile_single tt kk aa c x = word_to_word_compile_single tt kk aa c x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `no_mt (SND (SND (word_to_word_compile_single tt kk aa (c:(A)asm_config) x)))`
    MP_TAC THENL
   [REWRITE_TAC[no_mt_subprogs_def] THEN MATCH_MP_TAC compile_single_not_created_subprogs THEN
    ASM_REWRITE_TAC[GSYM no_mt_subprogs_def];
    ALL_TAC] THEN
  REWRITE_TAC[W2WPAUX_fcs] THEN
  SPEC_TAC(`word_to_word_compile_single tt kk aa (c:(A)asm_config) x`,`q:num#num#(A)wl_prog`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; PAIR_MAP_THM; I_THM; SND; PAIR_EQ] THEN
  REWRITE_TAC[no_mt_remove_must_terminate_const]);;

(* HOL4 line 2126 (the ZIP zips lists of equal lengths) *)
let no_mt_code_full_compile_single = prove
 (`!progs x tt kk aa (co:(A)asm_config).
     no_mt_code (fromAList progs) /\
     ALL_DISTINCT (MAP FST progs) /\
     LENGTH x = LENGTH progs
     ==> MAP (full_compile_single tt kk aa co) (ZIP progs x) =
         MAP (word_to_word_compile_single tt kk aa co) (ZIP progs x)`,
  LIST_INDUCT_TAC THENL [REWRITE_TAC[ZIP; MAP]; ALL_TAC] THEN
  X_GEN_TAC `x:((num spt)option)list` THEN
  STRUCT_CASES_TAC (ISPEC `x:((num spt)option)list` list_CASES) THEN
  REWRITE_TAC[LENGTH; NOT_SUC; GSYM NOT_SUC; SUC_INJ; ZIP; MAP; CONS_11] THEN
  SPEC_TAC(`h:num#num#(A)wl_prog`,`h:num#num#(A)wl_prog`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN
  MAP_EVERY X_GEN_TAC [`k0:num`; `n0:num`; `p0:(A)wl_prog`] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[no_mt_code_def; lookup_fromAList; ALL_DISTINCT; MAP; FST] THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC no_mt_full_compile_single THEN REWRITE_TAC[FST; SND] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN MAP_EVERY EXISTS_TAC [`k0:num`; `n0:num`] THEN
    REWRITE_TAC[ALOOKUP_THM];
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[no_mt_code_def; lookup_fromAList] THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`k:num`; `n:num`] THEN
    SUBGOAL_THEN `~(k0 = k:num)` (fun th -> ASM_REWRITE_TAC[ALOOKUP_THM; th]) THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `~MEM (k:num) (MAP FST (t:(num#num#(A)wl_prog)list))` THEN
    REWRITE_TAC[] THEN
    UNDISCH_TAC `ALOOKUP (t:(num#num#(A)wl_prog)list) k = SOME (n,p)` THEN
    REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM; FST] THEN MESON_TAC[ALOOKUP_MEM]]);;

(* HOL4 line 2144 *)
let code_rel_ext_def = cake_def
  `code_rel_ext (code:(num # (A)wl_prog)spt) l <=>
     (!n p_1 p_2.
        SOME (p_1,p_2) = lookup n code
        ==> ?t' k' a' c' col.
              SOME (SND (full_compile_single t' k' a' c' ((n,p_1,p_2),col))) =
              lookup n l)`;;

let W2WPAUX_fcs_FST_pair = prove
 (`!tra rc alg (c:(A)asm_config) n v col.
     full_compile_single tra rc alg c ((n,v),col) =
     (n,SND (full_compile_single tra rc alg c ((n,v),col)))`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [W2WPAUX_fcs_eta] THEN REWRITE_TAC[PAIR_EQ] THEN
  ONCE_REWRITE_TAC[W2WPAUX_fcs_eta] THEN REWRITE_TAC[SND]);;

let W2WPAUX_ALOOKUP_fcs = prove
 (`!tra rc alg (c:(A)asm_config) (code:(num#num#(A)wl_prog)list) os n v.
     LENGTH os = LENGTH code /\ ALOOKUP code n = SOME v
     ==> ?col. ALOOKUP (MAP (full_compile_single tra rc alg c) (ZIP code os)) n =
               SOME (SND (full_compile_single tra rc alg c ((n,v),col)))`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALOOKUP_THM; option_DISTINCT] THEN
  X_GEN_TAC `os:((num spt)option)list` THEN
  STRUCT_CASES_TAC (ISPEC `os:((num spt)option)list` list_CASES) THEN
  REWRITE_TAC[LENGTH; NOT_SUC; GSYM NOT_SUC; SUC_INJ; ZIP; MAP] THEN
  SPEC_TAC(`h:num#num#(A)wl_prog`,`h:num#num#(A)wl_prog`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[W2WPAUX_fcs_FST_pair] THEN REWRITE_TAC[ALOOKUP_THM] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_INJ] THENL
   [STRIP_TAC THEN EXISTS_TAC `h':(num spt)option` THEN ASM_REWRITE_TAC[];
    ASM_MESON_TAC[]]);;

(* HOL4 line 2154: val code_rel_ext_def = definition "code_rel_ext_def"    *)
(* (an alias)                                                                *)

(* HOL4 line 2156 *)
let code_rel_ext_word_to_word = prove
 (`!code c1 col code' (c2:(A)asm_config).
     word_to_word_compile c1 c2 code = (col,code')
     ==> code_rel_ext (fromAList code) (fromAList code')`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o AP_TERM `SND:((num spt)option)list#(num#num#(A)wl_prog)list->
                                   (num#num#(A)wl_prog)list`) THEN
  REWRITE_TAC[WPROOF2AUX_w2w_SND; SND] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[code_rel_ext_def; lookup_fromAList] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`asm_config_two_reg_arith (c2:(A)asm_config)`;
                 `asm_config_reg_count (c2:(A)asm_config) - (5 + LENGTH (asm_config_avoid_regs c2))`;
                 `word_to_word_config_reg_alg c1`; `c2:(A)asm_config`;
                 `code:(num#num#(A)wl_prog)list`;
                 `FST (next_n_oracle (LENGTH (code:(num#num#(A)wl_prog)list))
                        (word_to_word_config_col_oracle c1))`;
                 `n:num`; `(p_1:num,p_2:(A)wl_prog)`] W2WPAUX_ALOOKUP_fcs) THEN
  ASM_REWRITE_TAC[WPROOF2AUX_next_n_oracle_LENGTH] THEN
  DISCH_THEN(X_CHOOSE_TAC `col':(num spt)option`) THEN
  MAP_EVERY EXISTS_TAC [`asm_config_two_reg_arith (c2:(A)asm_config)`;
    `asm_config_reg_count (c2:(A)asm_config) - (5 + LENGTH (asm_config_avoid_regs c2))`;
    `word_to_word_config_reg_alg c1`; `c2:(A)asm_config`; `col':(num spt)option`] THEN
  ASM_REWRITE_TAC[]);;

(* HOL4 line 2185 *)
let no_mt_code_rel_ext = prove
 (`!cd1 cd2. no_mt_code (cd1:(num # (A)wl_prog)spt) /\ code_rel_ext cd1 cd2
             ==> word_to_wordProof_code_rel cd1 cd2`,
  REWRITE_TAC[no_mt_code_def; code_rel_ext_def; word_to_wordProof_code_rel_def] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `q:num`; `r:(A)wl_prog`] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `q:num`; `r:(A)wl_prog`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t':bool` (X_CHOOSE_THEN `k':num` (X_CHOOSE_THEN `a':num`
    (X_CHOOSE_THEN `c':(A)asm_config` (X_CHOOSE_THEN `col:(num spt)option` ASSUME_TAC))))) THEN
  MAP_EVERY EXISTS_TAC [`col:(num spt)option`; `t':bool`; `k':num`; `a':num`; `c':(A)asm_config`] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC no_mt_full_compile_single THEN REWRITE_TAC[FST; SND] THEN
  ASM_MESON_TAC[]);;

(* HOL4 line 2206 *)
let code_rel_no_share_inst = prove
 (`!op (args:((B)word_loc)list) c1 (sz:(C)spt) v c2 v'.
     wl_find_code op args c1 sz = SOME v /\
     word_to_wordProof_code_rel (c1:(num # (A)wl_prog)spt) c2 /\
     no_share_inst (FST (SND v)) /\
     wl_find_code op args c2 sz = SOME v'
     ==> no_share_inst (FST (SND v'))`,
  REWRITE_TAC[no_share_inst_subprogs_def; code_rel_P]);;

(* HOL4 line 2219 (HOL4's unused binder clk is left out) *)
let panLang_compile_word_to_word_thm = prove
 (CASE_TERM
  `!(st:(A,C,FFI)wl_state) l start.
     word_to_wordProof_code_rel (wl_state_code st) l /\
     no_install_code (wl_state_code st) /\ no_alloc_code (wl_state_code st) /\
     no_mt_code (wl_state_code st) /\
     domain (wl_state_code st) = domain l /\
     gc_fun_const_ok (wl_state_gc_fun st)
     ==> ?perm'.
           let prog = wl_Call NONE (SOME start) [0] NONE in
           let (res,rst) = wl_evaluate (prog,wl_state_permute_fupd (K perm') st) in
           if res = SOME wl_Error then T else
           let (res1,rst1) = wl_evaluate (prog,wl_state_code_fupd (K l) st) in
           res1 = res /\
           wl_state_clock rst1 = wl_state_clock rst /\
           wl_state_ffi rst1 = wl_state_ffi rst /\
           wl_state_stack_max rst1 = wl_state_stack_max rst`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  MP_TAC(ISPECL [`wl_Call NONE (SOME start) [0] NONE:(A)wl_prog`; `st:(A,C,FFI)wl_state`;
                 `l:(num#(A)wl_prog)spt`] no_install_no_alloc_compile_single_correct) THEN
  ASM_REWRITE_TAC[wordConvs_no_install_def; no_alloc_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[distinctness "wl_prog"] THEN
  DISCH_THEN(X_CHOOSE_THEN `perm:num->num->num` MP_TAC) THEN
  DISCH_TAC THEN EXISTS_TAC `perm:num->num->num` THEN POP_ASSUM MP_TAC THEN
  W2WPAUX_NAME_PAIR_TAC `wl_evaluate (wl_Call NONE (SOME start) [0] NONE:(A)wl_prog,
                           wl_state_permute_fupd (K perm) (st:(A,C,FFI)wl_state))`
    `res:((A)wl_result)option` `rst:(A,C,FFI)wl_state` THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  W2WPAUX_NAME_PAIR_TAC `wl_evaluate (wl_Call NONE (SOME start) [0] NONE:(A)wl_prog,
                           wl_state_code_fupd (K l) (st:(A,C,FFI)wl_state))`
    `res1:((A)wl_result)option` `rst1:(A,C,FFI)wl_state` THEN
  STRIP_TAC THEN FIRST_ASSUM(SUBST1_TAC o check (fun th ->
    is_eq(concl th) && lhs(concl th) = `rst1:(A,C,FFI)wl_state`)) THEN
  ASM_REWRITE_TAC[] THEN SIMP[]);;

(* the semantics only depends on the results and the ffi states of the     *)
(* evaluations                                                              *)
let W2WPAUX_sem_obs = prove
 (`!(s:(A,B,FFI)wl_state) (t:(A,B,FFI)wl_state) start.
     (!k. FST (wl_evaluate (wl_Call NONE (SOME start) [0] NONE, wl_state_clock_fupd (K k) s)) =
          FST (wl_evaluate (wl_Call NONE (SOME start) [0] NONE, wl_state_clock_fupd (K k) t)) /\
          wl_state_ffi (SND (wl_evaluate (wl_Call NONE (SOME start) [0] NONE,
                                          wl_state_clock_fupd (K k) s))) =
          wl_state_ffi (SND (wl_evaluate (wl_Call NONE (SOME start) [0] NONE,
                                          wl_state_clock_fupd (K k) t))))
     ==> wl_semantics s start = wl_semantics t start`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FORALL_AND_THM] THEN STRIP_TAC THEN
  REWRITE_TAC[wl_semantics_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN
   `!(x:(A)wl_prog#(A,B,FFI)wl_state) r t'.
      wl_evaluate x = (r,t') <=> FST (wl_evaluate x) = r /\ SND (wl_evaluate x) = t'`
   (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT GEN_TAC THEN
    SPEC_TAC(`wl_evaluate (x:(A)wl_prog#(A,B,FFI)wl_state)`,
             `q:((A)wl_result)option#(A,B,FFI)wl_state`) THEN
    REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ; FST; SND];
    ALL_TAC] THEN
  SIMP_NOASM[] THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 2267 *)
let word_to_word_compile_semantics = prove
 (`!wconf acomf wprog0 col wprog (s:(A,B,FFI)wl_state) (t:(A,B,FFI)wl_state) start.
     word_to_word_compile wconf acomf wprog0 = (col,wprog) /\
     gc_fun_const_ok (wl_state_gc_fun s) /\
     no_install_code (fromAList wprog0) /\
     no_alloc_code (fromAList wprog0) /\
     no_install_code (wl_state_code s) /\ no_alloc_code (wl_state_code s) /\
     no_mt_code (fromAList wprog0) /\
     ALL_DISTINCT (MAP FST wprog0) /\ wl_state_stack s = [] /\
     wl_state_code t = fromAList wprog /\
     lookup 0 (wl_state_locals t) = SOME (wl_Loc 1 0) /\
     t = wl_state_code_fupd (K (wl_state_code t)) s /\
     wl_state_code s = fromAList wprog0 /\
     ~(wl_semantics s start = Fail)
     ==> wl_semantics s start = wl_semantics t start`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* the code relation *)
  SUBGOAL_THEN `word_to_wordProof_code_rel (fromAList (wprog0:(num#num#(A)wl_prog)list))
                  (fromAList (wprog:(num#num#(A)wl_prog)list))` ASSUME_TAC THENL
   [MATCH_MP_TAC no_mt_code_rel_ext THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC code_rel_ext_word_to_word THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `domain (fromAList (wprog0:(num#num#(A)wl_prog)list)) =
                domain (fromAList (wprog:(num#num#(A)wl_prog)list))`
    ASSUME_TAC THENL
   [REWRITE_TAC[domain_fromAList] THEN AP_TERM_TAC THEN
    FIRST_X_ASSUM(MP_TAC o AP_TERM `SND:((num spt)option)list#(num#num#(A)wl_prog)list->
                                       (num#num#(A)wl_prog)list` o
      check (fun th -> can (find_term (fun u -> is_const u &&
                              fst(dest_const u) = "word_to_word_compile")) (concl th))) THEN
    REWRITE_TAC[WPROOF2AUX_w2w_SND; SND] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC W2WPAUX_MAP_ZIP_FST THEN
    REWRITE_TAC[WPROOF2AUX_next_n_oracle_LENGTH; FORALL_PAIR_THM; WPROOF2AUX_fcs_FST];
    ALL_TAC] THEN
  SUBGOAL_THEN `!k. ~(FST (wl_evaluate (wl_Call NONE (SOME start) [0] NONE:(A)wl_prog,
                   wl_state_clock_fupd (K k) (s:(A,B,FFI)wl_state))) = SOME wl_Error)`
     ASSUME_TAC THENL
    [X_GEN_TAC `k:num` THEN UNDISCH_TAC `~(wl_semantics (s:(A,B,FFI)wl_state) start = Fail)` THEN
     REWRITE_TAC[wl_semantics_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
     COND_CASES_TAC THEN REWRITE_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o REWRITE_RULE[NOT_EXISTS_THM]) THEN
     ONCE_REWRITE_TAC[TAUT `(~a ==> ~b) <=> (b ==> a)`] THEN
     DISCH_THEN SUBST1_TAC THEN CASE_REWRITE_TAC[];
     ALL_TAC] THEN
  MATCH_MP_TAC W2WPAUX_sem_obs THEN X_GEN_TAC `k:num` THEN
   MP_TAC(ISPECL [`wl_state_clock_fupd (K k) (s:(A,B,FFI)wl_state)`;
                  `fromAList (wprog:(num#num#(A)wl_prog)list)`; `start:num`]
                 panLang_compile_word_to_word_thm) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SIMP[]; ALL_TAC] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   DISCH_THEN(X_CHOOSE_THEN `perm:num->num->num` MP_TAC) THEN
  FIRST_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = `t:(A,B,FFI)wl_state`
                          then SUBST1_TAC th else failwith "") THEN
   ASM_REWRITE_TAC[] THEN SIMP_NOASM[] THEN
   MP_TAC(ISPECL [`wl_Call NONE (SOME start) [0] NONE:(A)wl_prog`;
                  `wl_state_clock_fupd (K k) (s:(A,B,FFI)wl_state)`; `perm:num->num->num`;
                  `[]:((A)stack_frame)list`] permute_swap_lemma3) THEN
   W2WPAUX_NAME_PAIR_TAC `wl_evaluate (wl_Call NONE (SOME start) [0] NONE:(A)wl_prog,
                            wl_state_clock_fupd (K k) (s:(A,B,FFI)wl_state))`
     `r0:((A)wl_result)option` `s0:(A,B,FFI)wl_state` THEN
   ANTS_TAC THENL
    [FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (is_forall o concl)) THEN
     ASM_REWRITE_TAC[FST] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
     SIMP[no_alloc_def; wordConvs_no_install_def; distinctness "wl_prog"; ALL];
     ALL_TAC] THEN
   DISCH_THEN(X_CHOOSE_THEN `perm2:num->num->num` (X_CHOOSE_THEN
     `stack2:((A)stack_frame)list` STRIP_ASSUME_TAC)) THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (is_forall o concl)) THEN
   ASM_REWRITE_TAC[FST] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  W2WPAUX_SPLIT_EVAL_TAC `wl_Call NONE (SOME start) [0] NONE:(A)wl_prog` (K true)
     `r1:((A)wl_result)option` `s1:(A,B,FFI)wl_state` THEN
   REWRITE_TAC[FST; SND] THEN SIMP[] THEN MESON_TAC[]);;
