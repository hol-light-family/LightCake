(* ========================================================================= *)
(* loop_liveProof: port of HOL4 pancake/proofs/loop_liveProofScript.sml      *)
(* (CakeML v3479).                                                           *)
(* Correctness proof for loop_live.                                          *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - Names as notes/naming/names.tsv says: compile_correct is                *)
(*   loop_liveProof_compile_correct, domain_list_delete is                   *)
(*   loop_liveProof_domain_list_delete, optimise_correct is                  *)
(*   loop_liveProof_optimise_correct; shrink is loop_live_shrink, comp is    *)
(*   loop_live_comp.                                                         *)
(* - HOL4 ZIP (xs,ys) is ZIP xs ys; set is set_of_list; s with locals := l   *)
(*   is loop_state_locals_fupd (K l) s.                                      *)
(* - HOL4 proves compile_correct first, by recInduct with one suspended goal *)
(*   per case (Resume blocks after the lemmas they use).  Here the lemmas    *)
(*   come first; the statement for one program and state is the local        *)
(*   predicate PLOOPAUX_live_P (its case expression on the result is         *)
(*   PLOOPAUX_live_post), each case is a lemma PLOOPAUX_live_CASE, the       *)
(*   induction is PLOOPAUX_live_main, and compile_correct folds HOL4's       *)
(*   statement into it.                                                      *)
(* - eval_lemma' keeps HOL4's unused bound variable l (of type B here).      *)
(* - HOL4's [local] theorems are ordinary theorems.                          *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/backend_common.ml";;
needs "pancake/semantics/loopSem.ml";;
needs "pancake/semantics/loopProps.ml";;
needs "pancake/loop_live.ml";;
needs "pancake/proofs/loop_callProof.ml";;

prioritize_num();;
type_invention_error := true;;

let subspt_IMP_domain = prove
 (`subspt (l1:A spt) l2 ==> domain l1 SUBSET domain l2`,
  REWRITE_TAC[subspt_def; SUBSET] THEN MESON_TAC[]);;

let subspt_inter_domain_cut = prove
 (`!(X:B spt) (m1:A spt) m2.
     domain X SUBSET domain m1 /\ subspt (inter m1 X) m2 ==>
     domain X SUBSET domain m2`,
  REWRITE_TAC[SUBSET; subspt_lookup; lookup_inter_alt] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:num`) THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[domain_lookup]);;

(* HOL4 names the variables A B C D; here they are a b c d *)

let subspt_inter_union_R = prove
 (`!(a:A spt) (b:B spt) c (d:A spt).
     subspt (inter a (union b c)) d ==> subspt (inter a c) d`,
  REWRITE_TAC[subspt_lookup; lookup_inter_alt; domain_union; IN_UNION] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  POP_ASSUM MP_TAC THEN REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT] THEN
  ASM_MESON_TAC[]);;

let PLOOPAUX_vars_of_exp_list_clauses = prove
 (`(!l. vars_of_exp_list ([]:((A)loop_exp)list) l = l) /\
   (!(x:(A)loop_exp) xs l.
      vars_of_exp_list (CONS x xs) l = vars_of_exp x (vars_of_exp_list xs l))`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [vars_of_exp_def] THEN
  REWRITE_TAC[case_def "list"]);;

let PLOOPAUX_vars_of_exp_rws =
  CONJ (end_itlist CONJ (butlast (CONJUNCTS vars_of_exp_def)))
       PLOOPAUX_vars_of_exp_list_clauses;;

let PLOOPAUX_vars_of_exp_acc = prove
 (`(!(exp:(A)loop_exp) l.
      domain (vars_of_exp exp l) = domain (vars_of_exp exp LN) UNION domain l) /\
   (!(exps:((A)loop_exp)list) l.
      domain (vars_of_exp_list exps l) =
      domain (vars_of_exp_list exps LN) UNION domain l)`,
  MATCH_MP_TAC loop_exp_INDUCT THEN
  REWRITE_TAC[PLOOPAUX_vars_of_exp_rws; domain_insert; domain_def; UNION_EMPTY] THEN
  REPEAT CONJ_TAC THEN TRY (SET_TAC[] THEN NO_TAC) THEN
  REPEAT STRIP_TAC THEN
  ONCE_ASM_REWRITE_TAC[] THEN ONCE_ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[domain_def; UNION_EMPTY] THEN SET_TAC[]);;

let vars_of_exp_acc = prove
 (`!(exp:(A)loop_exp) l.
     domain (vars_of_exp exp l) = domain (union (vars_of_exp exp LN) l)`,
  REWRITE_TAC[domain_union] THEN MESON_TAC[PLOOPAUX_vars_of_exp_acc]);;

let PLOOPAUX_vars_of_exp_mono = prove
 (`(!(exp:(A)loop_exp) (l:num_set). subspt l (vars_of_exp exp l)) /\
   (!(exps:((A)loop_exp)list) (l:num_set). subspt l (vars_of_exp_list exps l))`,
  MATCH_MP_TAC loop_exp_INDUCT THEN
  REWRITE_TAC[PLOOPAUX_vars_of_exp_rws; subspt_insert; subspt_refl] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[subspt_trans]);;

let vars_of_exp_mono = prove
 (`!(exp:(A)loop_exp) (l:num_set). subspt l (vars_of_exp exp l)`,
  REWRITE_TAC[PLOOPAUX_vars_of_exp_mono]);;

let PLOOPAUX_the_words_mono = prove
 (`!(l:((A)loop_exp)list) (f:(A)loop_exp->((A)word_loc)option) g.
     (!a w. MEM a l /\ f a = SOME w ==> g a = SOME w) ==>
     !ws. the_words (MAP f l) = SOME ws ==> the_words (MAP g l) = SOME ws`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; MEM; the_words_def] THEN REPEAT GEN_TAC THEN
  DISCH_TAC THEN GEN_TAC THEN
  REWRITE_TAC[case_eq "option"; case_eq "word_loc"; option_DISTINCT] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[option_INJ]) THEN RVEQ_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`f:(A)loop_exp->((A)word_loc)option`;
                                `g:(A)loop_exp->((A)word_loc)option`]) THEN
  ASM_MESON_TAC[]);;

let PLOOPAUX_eval_lemma' = prove
 (`!(s:(A,FFI)loop_state) exp w.
     loop_eval s exp = SOME w /\ subspt (loop_state_locals s) locals ==>
     loop_eval (loop_state_locals_fupd (K locals) s) exp = SOME w`,
  MATCH_MP_TAC loop_eval_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[loop_eval_def; loop_mem_load_def; loop_state_INFO.ri_accfupds; K_THM] THEN
  REWRITE_TAC[case_eq "option"; case_eq "word_loc"; case_eq "prod"; PAIR_EQ;
              option_DISTINCT] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN TRY (ASM_MESON_TAC[subspt_lookup] THEN NO_TAC) THEN
  ASM_MESON_TAC[PLOOPAUX_the_words_mono]);;

let eval_lemma' = prove
 (`!(s:(A,FFI)loop_state) exp w (l:B).
     loop_eval s exp = SOME w /\ subspt (loop_state_locals s) locals ==>
     loop_eval (loop_state_locals_fupd (K locals) s) exp = SOME w`,
  REWRITE_TAC[PLOOPAUX_eval_lemma']);;

let PLOOPAUX_subspt_inter_mono = prove
 (`!(X:B spt) (m:A spt) (Y:C spt) n.
     domain Y SUBSET domain X /\ subspt (inter m X) n ==> subspt (inter m Y) n`,
  REWRITE_TAC[SUBSET; subspt_lookup; lookup_inter_alt] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  POP_ASSUM MP_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
  ASM_MESON_TAC[]);;

let PLOOPAUX_vars_of_exp_sub = prove
 (`!(e:(A)loop_exp) l.
     domain (vars_of_exp e LN) SUBSET domain (vars_of_exp e l) /\
     domain l SUBSET domain (vars_of_exp e l)`,
  ONCE_REWRITE_TAC[CONJUNCT1 PLOOPAUX_vars_of_exp_acc] THEN
  REWRITE_TAC[domain_def; UNION_EMPTY] THEN SET_TAC[]);;

let PLOOPAUX_vars_of_exp_list_MEM = prove
 (`!(vs:((A)loop_exp)list) a l.
     MEM a vs ==> domain (vars_of_exp a LN) SUBSET domain (vars_of_exp_list vs l)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; PLOOPAUX_vars_of_exp_list_clauses] THEN
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [CONJUNCT1 PLOOPAUX_vars_of_exp_acc] THEN
  STRIP_TAC THENL
   [ASM_REWRITE_TAC[] THEN SET_TAC[];
    ASM_MESON_TAC[SUBSET_UNION; SUBSET_TRANS]]);;

let PLOOPAUX_eval_lemma = prove
 (`!(s:(A,FFI)loop_state) exp w.
     loop_eval s exp = SOME w /\
     subspt (inter (loop_state_locals s) (vars_of_exp exp LN)) locals ==>
     loop_eval (loop_state_locals_fupd (K locals) s) exp = SOME w`,
  MATCH_MP_TAC loop_eval_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[loop_eval_def; loop_mem_load_def; loop_state_INFO.ri_accfupds; K_THM;
              PLOOPAUX_vars_of_exp_rws] THEN
  REWRITE_TAC[case_eq "option"; case_eq "word_loc"; case_eq "prod"; PAIR_EQ;
              option_DISTINCT] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[] THENL
   [(* Var *)
    RULE_ASSUM_TAC(REWRITE_RULE[subspt_lookup; lookup_inter_alt; domain_insert;
                                IN_INSERT]) THEN
    ASM_MESON_TAC[];
    (* Load *)
    ASM_MESON_TAC[];
    (* Op *)
    MP_TAC(ISPECL [`wexps:((A)loop_exp)list`; `loop_eval (s:(A,FFI)loop_state)`;
                   `loop_eval (loop_state_locals_fupd (K locals) (s:(A,FFI)loop_state))`]
                  PLOOPAUX_the_words_mono) THEN
    ANTS_TAC THENL
     [MAP_EVERY X_GEN_TAC [`e0:(A)loop_exp`; `w0:(A)word_loc`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `e0:(A)loop_exp`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(ISPECL [`vars_of_exp_list (wexps:((A)loop_exp)list) LN`;
                           `loop_state_locals (s:(A,FFI)loop_state)`]
                     PLOOPAUX_subspt_inter_mono) THEN
      ASM_SIMP_TAC[PLOOPAUX_vars_of_exp_list_MEM];
      ASM_MESON_TAC[]];
    (* Shift *)
    SUBGOAL_THEN
     `subspt (inter (loop_state_locals (s:(A,FFI)loop_state))
                    (vars_of_exp (wexp1:(A)loop_exp) LN)) locals /\
      subspt (inter (loop_state_locals s) (vars_of_exp (wexp2:(A)loop_exp) LN)) locals`
     STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN
      MATCH_MP_TAC(ISPECL [`vars_of_exp (wexp1:(A)loop_exp)
                                        (vars_of_exp (wexp2:(A)loop_exp) LN)`;
                           `loop_state_locals (s:(A,FFI)loop_state)`]
                     PLOOPAUX_subspt_inter_mono) THEN
      ASM_REWRITE_TAC[PLOOPAUX_vars_of_exp_sub];
      ALL_TAC] THEN
    RES_TAC THEN
    ASM_REWRITE_TAC[option_INJ; UNWIND_THM1; injectivity "word_loc"; UNWIND_THM2]]);;

let eval_lemma = prove
 (`!(s:(A,FFI)loop_state) exp w l.
     loop_eval s exp = SOME w /\
     subspt (inter (loop_state_locals s) (vars_of_exp exp l)) locals ==>
     loop_eval (loop_state_locals_fupd (K locals) s) exp = SOME w`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PLOOPAUX_eval_lemma THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(ISPECL [`vars_of_exp (exp:(A)loop_exp) l`;
                       `loop_state_locals (s:(A,FFI)loop_state)`]
                 PLOOPAUX_subspt_inter_mono) THEN
  ASM_REWRITE_TAC[PLOOPAUX_vars_of_exp_sub]);;

(* HOL4: domain_list_delete [simp] *)

let loop_liveProof_domain_list_delete = prove
 (`!vs (s:A spt). domain (list_delete vs s) = domain s DIFF set_of_list vs`,
  REWRITE_TAC[EXTENSION; domain_lookup; lookup_list_delete; IN_DIFF; IN_SET_OF_LIST] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT]);;

let dom_vars_of_exp_in = prove
 (`v IN domain (l:num_set) ==> v IN domain (vars_of_exp (x:(A)loop_exp) l)`,
  MESON_TAC[PLOOPAUX_vars_of_exp_sub; SUBSET]);;

let PLOOPAUX_subspt_inter_lookup = prove
 (`!(m:A spt) (X:B spt) n k v.
     subspt (inter m X) n /\ k IN domain X /\ lookup k m = SOME v ==>
     lookup k n = SOME v`,
  REWRITE_TAC[subspt_lookup; lookup_inter_alt] THEN MESON_TAC[]);;

let get_vars_subspt = prove
 (`!rhss ws (s:(A,FFI)loop_state) (extra:num_set) locals.
     get_vars rhss s = SOME ws /\
     subspt (inter (loop_state_locals s) (list_insert rhss extra)) locals ==>
     get_vars rhss (loop_state_locals_fupd (K locals) s) = SOME ws`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[get_vars_def; loop_state_INFO.ri_accfupds; K_THM; list_insert_def] THEN
  REWRITE_TAC[case_eq "option"; option_DISTINCT] THEN REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[option_INJ]) THEN RVEQ_TAC THEN
  SUBGOAL_THEN `h IN domain (list_insert t (insert h one (extra:num_set)))` ASSUME_TAC
  THENL [REWRITE_TAC[domain_list_insert; domain_insert; IN_INSERT]; ALL_TAC] THEN
  ASM_MESON_TAC[PLOOPAUX_subspt_inter_lookup]);;

(* ------------------------------------------------------------------------- *)
(* compile_correct.  The postcondition (the case expression of HOL4's        *)
(* statement) is the local predicate PLOOPAUX_live_post, and the statement   *)
(* for one program and state is PLOOPAUX_live_P; each case of the induction *)
(* on the semantics is a lemma PLOOPAUX_live_CASE.                           *)
(* ------------------------------------------------------------------------- *)

let PLOOPAUX_live_post_def = new_definition (CASE_TERM
 `PLOOPAUX_live_post (lt:(num_set#num_set)list) (l0:num_set)
                     (res:((A)loop_result)option) (s1:(A,FFI)loop_state)
                     (new_locals:((A)word_loc)spt) <=>
    match res with
      NONE -> subspt (inter (loop_state_locals s1) l0) new_locals
    | SOME (loop_Result v5) -> new_locals = loop_state_locals s1
    | SOME (loop_Exception v6) -> new_locals = loop_state_locals s1
    | SOME (loopSem_Break n) ->
        (match oEL n lt with
           SOME (_, brk) -> subspt (inter (loop_state_locals s1) brk) new_locals
         | NONE -> T)
    | SOME (loopSem_Continue n) ->
        (match oEL n lt with
           SOME (cont, _) -> subspt (inter (loop_state_locals s1) cont) new_locals
         | NONE -> T)
    | SOME loop_TimeOut -> new_locals = loop_state_locals s1
    | SOME (loop_FinalFFI v7) -> new_locals = loop_state_locals s1
    | SOME loop_Error -> new_locals = loop_state_locals s1`);;

let PLOOPAUX_live_post_thm = prove
 (`(PLOOPAUX_live_post lt l0 NONE (s1:(A,FFI)loop_state) nl <=>
      subspt (inter (loop_state_locals s1) l0) nl) /\
   (PLOOPAUX_live_post lt l0 (SOME (loop_Result v)) (s1:(A,FFI)loop_state) nl <=>
      nl = loop_state_locals s1) /\
   (PLOOPAUX_live_post lt l0 (SOME (loop_Exception w)) (s1:(A,FFI)loop_state) nl <=>
      nl = loop_state_locals s1) /\
   (PLOOPAUX_live_post lt l0 (SOME (loopSem_Break n)) (s1:(A,FFI)loop_state) nl <=>
      !c b. oEL n lt = SOME (c,b) ==> subspt (inter (loop_state_locals s1) b) nl) /\
   (PLOOPAUX_live_post lt l0 (SOME (loopSem_Continue n)) (s1:(A,FFI)loop_state) nl <=>
      !c b. oEL n lt = SOME (c,b) ==> subspt (inter (loop_state_locals s1) c) nl) /\
   (PLOOPAUX_live_post lt l0 (SOME loop_TimeOut) (s1:(A,FFI)loop_state) nl <=>
      nl = loop_state_locals s1) /\
   (PLOOPAUX_live_post lt l0 (SOME (loop_FinalFFI f)) (s1:(A,FFI)loop_state) nl <=>
      nl = loop_state_locals s1) /\
   (PLOOPAUX_live_post lt l0 (SOME loop_Error) (s1:(A,FFI)loop_state) nl <=>
      nl = loop_state_locals s1)`,
  REWRITE_TAC[PLOOPAUX_live_post_def; case_def "option"; case_def "loop_result"] THEN
  REPEAT CONJ_TAC THEN
  STRUCT_CASES_TAC (ISPEC `oEL n (lt:(num_set#num_set)list)` (cases "option")) THEN
  REWRITE_TAC[case_def "option"; option_DISTINCT; option_INJ] THEN
  TRY (PAIR_CASES_ON `a:num_set#num_set`) THEN
  REWRITE_TAC[case_def "prod"; PAIR_EQ] THEN MESON_TAC[]);;

let PLOOPAUX_live_P_def = new_definition
 `PLOOPAUX_live_P (prog:(A)loop_prog) (s:(A,FFI)loop_state) <=>
    !res s1 lt locals prog1 l1 l0.
      loop_evaluate (prog,s) = (res,s1) /\ ~(res = SOME loop_Error) /\
      loop_live_shrink lt prog l0 = (prog1,l1) /\
      subspt (inter (loop_state_locals s) l1) locals ==>
      ?new_locals.
        loop_evaluate (prog1, loop_state_locals_fupd (K locals) s) =
        (res, loop_state_locals_fupd (K new_locals) s1) /\
        PLOOPAUX_live_post lt l0 res s1 new_locals`;;

let PLOOPAUX_shrink_rws =
  end_itlist CONJ (butlast (CONJUNCTS loop_live_shrink_def));;

let PLOOPAUX_live_Skip = prove
 (`!s:(A,FFI)loop_state. PLOOPAUX_live_P loop_Skip s`,
  REWRITE_TAC[PLOOPAUX_live_P_def; PLOOPAUX_shrink_rws; PLOOPAUX_eval_clause "loop_Skip";
              PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN EXISTS_TAC `locals:((A)word_loc)spt` THEN
  ASM_REWRITE_TAC[PLOOPAUX_live_post_thm; PLOOPAUX_eval_clause "loop_Skip"]);;

let PLOOPAUX_live_Fail = prove
 (`!s:(A,FFI)loop_state. PLOOPAUX_live_P loop_Fail s`,
  REWRITE_TAC[PLOOPAUX_live_P_def; PLOOPAUX_eval_clause "loop_Fail"; PAIR_EQ] THEN
  MESON_TAC[]);;

let PLOOPAUX_live_Tick = prove
 (`!s:(A,FFI)loop_state. PLOOPAUX_live_P loop_Tick s`,
  REWRITE_TAC[PLOOPAUX_live_P_def; PLOOPAUX_shrink_rws; PLOOPAUX_eval_clause "loop_Tick";
              PAIR_EQ] THEN
  REPEAT GEN_TAC THEN SIMP[loop_dec_clock_def] THEN COND_CASES_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN RVEQ_TAC THENL
   [EXISTS_TAC `LN:((A)word_loc)spt`; EXISTS_TAC `locals:((A)word_loc)spt`] THEN
  REWRITE_TAC[PLOOPAUX_eval_clause "loop_Tick"] THEN
  SIMP[PLOOPAUX_live_post_thm; loop_dec_clock_def]);;

let PLOOPAUX_live_Break = prove
 (`!k (s:(A,FFI)loop_state). PLOOPAUX_live_P (loop_Break k) s`,
  REWRITE_TAC[PLOOPAUX_live_P_def; PLOOPAUX_shrink_rws; PLOOPAUX_eval_clause "loop_Break";
              PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN EXISTS_TAC `locals:((A)word_loc)spt` THEN
  REWRITE_TAC[PLOOPAUX_live_post_thm; PLOOPAUX_eval_clause "loop_Break"] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_comb (concl th) &&
     (try fst(dest_const(fst(strip_comb(concl th)))) = "subspt" with Failure _ -> false))) THEN
  ASM_REWRITE_TAC[case_def "option"; case_def "prod"]);;

let PLOOPAUX_live_Continue = prove
 (`!k (s:(A,FFI)loop_state). PLOOPAUX_live_P (loop_Continue k) s`,
  REWRITE_TAC[PLOOPAUX_live_P_def; PLOOPAUX_shrink_rws; PLOOPAUX_eval_clause "loop_Continue";
              PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN EXISTS_TAC `locals:((A)word_loc)spt` THEN
  REWRITE_TAC[PLOOPAUX_live_post_thm; PLOOPAUX_eval_clause "loop_Continue"] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_comb (concl th) &&
     (try fst(dest_const(fst(strip_comb(concl th)))) = "subspt" with Failure _ -> false))) THEN
  ASM_REWRITE_TAC[case_def "option"; case_def "prod"]);;

let PLOOPAUX_live_Mark = prove
 (`!p (s:(A,FFI)loop_state). PLOOPAUX_live_P p s ==> PLOOPAUX_live_P (Mark p) s`,
  REWRITE_TAC[PLOOPAUX_live_P_def; PLOOPAUX_shrink_rws; PLOOPAUX_eval_clause "Mark"]);;

let PLOOPAUX_live_Return = prove
 (`!ns (s:(A,FFI)loop_state). PLOOPAUX_live_P (loop_Return ns) s`,
  REWRITE_TAC[PLOOPAUX_live_P_def; PLOOPAUX_shrink_rws; PLOOPAUX_eval_clause "loop_Return";
              PAIR_EQ] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[case_eq "option"; PAIR_EQ; option_DISTINCT] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE PLOOPAUX_result_rws) THEN TRY (FIRST_ASSUM CONTR_TAC) THEN
  EXISTS_TAC `fromList [] :((A)word_loc)spt` THEN
  REWRITE_TAC[PLOOPAUX_live_post_thm; PLOOPAUX_eval_clause "loop_Return"] THEN
  MP_TAC(ISPECL [`ns:num list`; `a:((A)word_loc)list`; `s:(A,FFI)loop_state`;
                 `LN:num_set`; `locals:((A)word_loc)spt`] get_vars_subspt) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[case_def "option"; call_env_def] THEN SIMP[]);;

let PLOOPAUX_live_Raise = prove
 (`!n (s:(A,FFI)loop_state). PLOOPAUX_live_P (loop_Raise n) s`,
  REWRITE_TAC[PLOOPAUX_live_P_def; PLOOPAUX_shrink_rws; PLOOPAUX_eval_clause "loop_Raise";
              PAIR_EQ] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[case_eq "option"; PAIR_EQ; option_DISTINCT] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE PLOOPAUX_result_rws) THEN TRY (FIRST_ASSUM CONTR_TAC) THEN
  EXISTS_TAC `fromList [] :((A)word_loc)spt` THEN
  REWRITE_TAC[PLOOPAUX_live_post_thm; PLOOPAUX_eval_clause "loop_Raise"] THEN
  SUBGOAL_THEN `lookup n (locals:((A)word_loc)spt) = SOME a` ASSUME_TAC THENL
   [MATCH_MP_TAC(ISPECL [`loop_state_locals (s:(A,FFI)loop_state)`;
                         `insert n one LN:num_set`] PLOOPAUX_subspt_inter_lookup) THEN
    ASM_REWRITE_TAC[domain_insert; IN_INSERT];
    REWRITE_TAC[call_env_def] THEN SIMP[] THEN ASM_REWRITE_TAC[case_def "option"]]);;

let PLOOPAUX_subspt_inter_insert_out = prove
 (`!(m:A spt) (l0:num_set) n v x.
     subspt (inter m l0) n /\ lookup v l0 = NONE ==>
     subspt (inter (insert v x m) l0) n`,
  REWRITE_TAC[subspt_lookup; lookup_inter_alt; lookup_insert; domain_lookup] THEN
  REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN
  REPEAT COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
  ASM_MESON_TAC[option_DISTINCT]);;

let PLOOPAUX_IN_domain_rws = prove
 (`(!k v (t:A spt) x. x IN domain (insert k v t) <=> x = k \/ x IN domain t) /\
   (!k (t:A spt) x. x IN domain (delete k t) <=> ~(x = k) /\ x IN domain t) /\
   (!(a:A spt) (b:B spt) x. x IN domain (inter a b) <=> x IN domain a /\ x IN domain b) /\
   (!(a:A spt) b x. x IN domain (union a b) <=> x IN domain a \/ x IN domain b)`,
  REWRITE_TAC[domain_insert; domain_delete; domain_inter; domain_union; IN_INSERT;
              IN_DELETE; IN_INTER; IN_UNION] THEN MESON_TAC[]);;

let PLOOPAUX_vars_of_exp_in = REWRITE_RULE[SUBSET] PLOOPAUX_vars_of_exp_sub;;

(* tools for the cases of compile_correct *)

let PLOOPAUX_live_post_not_NONE = prove
 (`!lt l0 l0' res (s:(A,FFI)loop_state) nl.
     ~(res = NONE) ==>
     (PLOOPAUX_live_post lt l0 res s nl <=> PLOOPAUX_live_post lt l0' res s nl)`,
  REWRITE_TAC[PLOOPAUX_live_post_def] THEN REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `res:((A)loop_result)option` (cases "option")) THEN
  REWRITE_TAC[case_def "option"]);;

(* instantiate PLOOPAUX_live_P pst (an assumption) at insts, prove the      *)
(* antecedents from the assumptions, and choose the new locals nl          *)

let PLOOPAUX_P_SPEC_TAC (pst:term) (insts:term list) (nl:term) : tactic =
  MP_TAC(SPECL insts (REWRITE_RULE[PLOOPAUX_live_P_def] (ASSUME pst))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC PLOOPAUX_result_rws; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN nl (STRIP_ASSUME_TAC o REWRITE_RULE[PLOOPAUX_live_post_thm]));;

(* the same for the first assumption PLOOPAUX_live_P c st with assumptions *)
(* loop_evaluate (c,st) = (r,t) and loop_live_shrink lt c l0 = (p,l1): the  *)
(* locals are loc, and fin proves the antecedents left by rewriting         *)

let PLOOPAUX_LIVE_IH_TAC (loc:term) (nl:term) (fin:tactic) : tactic = fun (asl,w as g) ->
  let is_P t = try fst(dest_const(fst(strip_comb t))) = "PLOOPAUX_live_P"
               with Failure _ -> false in
  let facts = map (concl o snd) asl in
  let try_one pth =
    let c,st = match snd(strip_comb (concl pth)) with [c;st] -> c,st | _ -> failwith "" in
    let ev = find (fun tm -> is_eq tm &&
                     (try let f,x = dest_comb (lhs tm) in
                          fst(dest_const f) = "loop_evaluate" && x = mk_pair(c,st)
                      with Failure _ -> false)) facts in
    let sh = find (fun tm -> is_eq tm &&
                     (try let f,args = strip_comb (lhs tm) in
                          fst(dest_const f) = "loop_live_shrink" && el 1 args = c
                      with Failure _ -> false)) facts in
    let r,t = dest_pair (rhs ev) in
    let lt,l0 = (match snd(strip_comb(lhs sh)) with [lt;_;l0] -> lt,l0 | _ -> failwith "") in
    let p,l1 = dest_pair (rhs sh) in
    MP_TAC(SPECL [r;t;lt;loc;p;l1;l0] (REWRITE_RULE[PLOOPAUX_live_P_def] pth)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC PLOOPAUX_result_rws THEN fin; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN nl (STRIP_ASSUME_TAC o REWRITE_RULE[PLOOPAUX_live_post_thm])) in
  let pths = mapfilter (fun (_,th) -> if is_P (concl th) then th else failwith "") asl in
  FIRST (map (fun pth -> try try_one pth with Failure _ -> NO_TAC) pths) g;;

let PLOOPAUX_DOM_RWS =
  [SUBSET; domain_insert; domain_union; domain_inter; domain_delete; domain_def;
   loop_liveProof_domain_list_delete; domain_list_insert; IN_INSERT; IN_UNION; IN_INTER;
   IN_DELETE; IN_DIFF; IN_SET_OF_LIST; NOT_IN_EMPTY];;

(* the facts MESON uses for the domains left by PLOOPAUX_DOM_RWS (those of  *)
(* vars_of_exp, which keep insert, delete, ... in their arguments)          *)

let PLOOPAUX_DOM_FACTS = [PLOOPAUX_vars_of_exp_in; PLOOPAUX_IN_domain_rws];;

(* subspt (inter m X) n from an assumption subspt (inter m Y) n, with       *)
(* domain X SUBSET domain Y by rewriting                                    *)

let PLOOPAUX_SUBSPT_TAC : tactic = fun (asl,w as g) ->
  let parts t =
    match strip_comb t with
      (f,[a;n]) when fst(dest_const f) = "subspt" ->
        (match strip_comb a with
           (g,[m;x]) when fst(dest_const g) = "inter" -> (m,x,n)
         | _ -> failwith "")
    | _ -> failwith "" in
  let (m,x,n) = parts w in
  let cands = mapfilter (fun (_,th) -> let (m',y,n') = parts (concl th) in
                          if m' = m && n' = n then (y,th) else failwith "") asl in
  FIRST (map (fun (y,th) ->
     MATCH_MP_TAC (ISPECL [y; m] PLOOPAUX_subspt_inter_mono) THEN
     CONJ_TAC THENL
      [REWRITE_TAC PLOOPAUX_DOM_RWS THEN REPEAT COND_CASES_TAC THEN
       ASM_REWRITE_TAC[] THEN ASM_MESON_TAC PLOOPAUX_DOM_FACTS;
       ACCEPT_TAC th]) cands) g;;

(* lookup k n = SOME v from assumptions subspt (inter m X) n and            *)
(* lookup k m = SOME v, with k IN domain X by rewriting                     *)

let PLOOPAUX_LOOKUP_TAC : tactic = fun (asl,w as g) ->
  let k,n = match strip_comb (lhs w) with (_,[k;n]) -> k,n | _ -> failwith "" in
  let parts t =
    match strip_comb t with
      (f,[a;n']) when fst(dest_const f) = "subspt" && n' = n ->
        (match strip_comb a with
           (g,[m;x]) when fst(dest_const g) = "inter" -> (m,x)
         | _ -> failwith "")
    | _ -> failwith "" in
  let cands = mapfilter (fun (_,th) -> parts (concl th)) asl in
  FIRST (map (fun (m,x) ->
     MATCH_MP_TAC (ISPECL [m; x] PLOOPAUX_subspt_inter_lookup) THEN
     ASM_REWRITE_TAC PLOOPAUX_DOM_RWS THEN ASM_MESON_TAC PLOOPAUX_DOM_FACTS) cands) g;;

let PLOOPAUX_cut_res_live = prove
 (`!(lo:num_set) (L:num_set) (l0:num_set) lt r (t:(A,FFI)loop_state) nl res s1.
     cut_res lo (r,t) = (res,s1) /\ ~(res = SOME loop_Error) /\
     domain L SUBSET domain lo /\ domain l0 INTER domain lo SUBSET domain L /\
     PLOOPAUX_live_post lt L r t nl ==>
     ?nl'. cut_res L (r, loop_state_locals_fupd (K nl) t) =
           (res, loop_state_locals_fupd (K nl') s1) /\
           PLOOPAUX_live_post lt l0 res s1 nl'`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `r:((A)loop_result)option = NONE` THENL
  [ALL_TAC;
   ASM_REWRITE_TAC[cut_res_def; PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
   EXISTS_TAC `nl:((A)word_loc)spt` THEN ASM_MESON_TAC[PLOOPAUX_live_post_not_NONE]] THEN
  ASM_REWRITE_TAC[cut_res_def; cut_state_def; PLOOPAUX_live_post_thm] THEN
  COND_CASES_TAC THEN REWRITE_TAC[case_def "option"; PAIR_EQ] THENL
  [ALL_TAC; MESON_TAC PLOOPAUX_result_rws] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `domain (L:num_set) SUBSET domain (nl:((A)word_loc)spt)` ASSUME_TAC THENL
  [MATCH_MP_TAC(ISPECL [`L:num_set`; `loop_state_locals (t:(A,FFI)loop_state)`]
                  subspt_inter_domain_cut) THEN
   ASM_MESON_TAC[SUBSET_TRANS]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_cond o lhs o concl)) THEN SIMP[] THEN
  COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THENL
  [EXISTS_TAC `LN:((A)word_loc)spt` THEN SIMP[PLOOPAUX_live_post_thm];
   EXISTS_TAC `inter nl (L:num_set):((A)word_loc)spt` THEN
   SIMP[PLOOPAUX_live_post_thm; loop_dec_clock_def] THEN
   POP_ASSUM_LIST(fun ths -> MAP_EVERY MP_TAC (filter (fun th -> let c = concl th in
     can (find_term ((=) `L:num_set`)) c) ths)) THEN
   REWRITE_TAC[SUBSET; IN_INTER; subspt_lookup; lookup_inter_alt] THEN
   REPEAT DISCH_TAC THEN REPEAT GEN_TAC THEN
   REPEAT COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN ASM_MESON_TAC[]]);;

let PLOOPAUX_live_Seq = prove
 (`!c1 c2 (s:(A,FFI)loop_state).
     (!s1. loop_evaluate (c1,s) = (NONE,s1) ==> PLOOPAUX_live_P c2 s1) /\
     PLOOPAUX_live_P c1 s ==> PLOOPAUX_live_P (loop_Seq c1 c2) s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[PLOOPAUX_live_P_def] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[PLOOPAUX_shrink_rws; PLOOPAUX_eval_clause "loop_Seq"] THEN
  REPEAT PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  ASM_CASES_TAC `res':((A)loop_result)option = NONE` THEN
  FIRST_X_ASSUM(MP_TAC o check (is_cond o lhs o concl)) THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THENL
  [PLOOPAUX_P_SPEC_TAC `PLOOPAUX_live_P (c1:(A)loop_prog) (s:(A,FFI)loop_state)`
     [`NONE:((A)loop_result)option`; `s1':(A,FFI)loop_state`; `lt:(num_set#num_set)list`;
      `locals:((A)word_loc)spt`; `p1:(A)loop_prog`; `l1:num_set`; `l:num_set`]
     `nl1:((A)word_loc)spt` THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `s1':(A,FFI)loop_state` o
     check (fun th -> is_forall (concl th) && free_in `c2:(A)loop_prog` (concl th))) THEN
   REWRITE_TAC[] THEN DISCH_TAC THEN
   PLOOPAUX_P_SPEC_TAC `PLOOPAUX_live_P (c2:(A)loop_prog) (s1':(A,FFI)loop_state)`
     [`res:((A)loop_result)option`; `s1:(A,FFI)loop_state`; `lt:(num_set#num_set)list`;
      `nl1:((A)word_loc)spt`; `p2:(A)loop_prog`; `l:num_set`; `l0:num_set`]
     `nl2:((A)word_loc)spt` THEN
   EXISTS_TAC `nl2:((A)word_loc)spt` THEN
   ASM_REWRITE_TAC[PLOOPAUX_eval_clause "loop_Seq"; case_def "prod"];
   PLOOPAUX_P_SPEC_TAC `PLOOPAUX_live_P (c1:(A)loop_prog) (s:(A,FFI)loop_state)`
     [`res:((A)loop_result)option`; `s1:(A,FFI)loop_state`; `lt:(num_set#num_set)list`;
      `locals:((A)word_loc)spt`; `p1:(A)loop_prog`; `l1:num_set`; `l:num_set`]
     `nl1:((A)word_loc)spt` THEN
   EXISTS_TAC `nl1:((A)word_loc)spt` THEN
   ASM_REWRITE_TAC[PLOOPAUX_eval_clause "loop_Seq"; case_def "prod"] THEN
   ASM_MESON_TAC[PLOOPAUX_live_post_not_NONE]]);;

(* for the assumptions lookup k (loop_state_locals s) = v, add              *)
(* lookup k loc = v when PLOOPAUX_LOOKUP_TAC proves it                      *)

let PLOOPAUX_LOOKUPS_TAC (loc:term) : tactic = fun (asl,w as g) ->
  let tms = mapfilter (fun (_,th) -> let tm = concl th in
     match strip_comb (lhs tm) with
       (f,[k;m]) when fst(dest_const f) = "lookup" && not (m = loc) &&
          (try fst(dest_const(rator m)) = "loop_state_locals" with Failure _ -> false) ->
         mk_eq(mk_comb(mk_comb(f,k),loc), rhs tm)
     | _ -> failwith "") asl in
  MAP_EVERY (fun tm -> TRY(SUBGOAL_THEN tm ASSUME_TAC THENL
                             [PLOOPAUX_LOOKUP_TAC THEN NO_TAC; ALL_TAC])) tms g;;

let PLOOPAUX_cut_res_live_imp = REWRITE_RULE[IMP_CONJ] PLOOPAUX_cut_res_live;;

let PLOOPAUX_live_If = prove
 (`!cmp r1 ri c1 c2 live_out (s:(A,FFI)loop_state).
    (!x y. lookup r1 (loop_state_locals s) = SOME (wl_Word x) /\
           get_var_imm ri s = SOME (wl_Word y)
           ==> PLOOPAUX_live_P (if asm_word_cmp cmp x y then c1 else c2) s)
    ==> PLOOPAUX_live_P (loop_If cmp r1 ri c1 c2 live_out) s`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `ri:(A)reg_imm` (cases "reg_imm")) THEN
  REWRITE_TAC[get_var_imm_def; case_def "reg_imm"] THEN DISCH_TAC THEN
  REWRITE_TAC[PLOOPAUX_live_P_def] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[PLOOPAUX_shrink_rws; PLOOPAUX_eval_clause "loop_If"; get_var_imm_def;
              case_def "reg_imm"] THEN
  REPEAT PAIRARG_TAC THEN REWRITE_TAC[LET_DEF; LET_END_DEF; PAIR_EQ] THEN
  REWRITE_TAC PLOOPAUX_clock_case_eqs THEN REWRITE_TAC[PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE PLOOPAUX_result_rws) THEN TRY (FIRST_ASSUM CONTR_TAC) THEN
  FIRST_X_ASSUM(fun ih -> FIRST_ASSUM(fun th1 -> FIRST_ASSUM(fun th2 ->
      ASSUME_TAC(MATCH_MP ih (CONJ th1 th2))))) THEN
  PLOOPAUX_SPLIT_EVAL_TAC THEN PLOOPAUX_COND_EQ_FACT_TAC THEN
  IMP_RES_TAC PLOOPAUX_cut_res_not_error THEN
  PLOOPAUX_LIVE_IH_TAC `locals:((A)word_loc)spt` `nl:((A)word_loc)spt`
    PLOOPAUX_SUBSPT_TAC THEN
  PLOOPAUX_LOOKUPS_TAC `locals:((A)word_loc)spt` THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP PLOOPAUX_cut_res_live_imp) THEN
  DISCH_THEN(MP_TAC o SPECL [`inter (l0:num_set) (live_out:num_set)`; `l0:num_set`;
                             `lt:(num_set#num_set)list`; `nl:((A)word_loc)spt`]) THEN
  ASM_REWRITE_TAC PLOOPAUX_DOM_RWS THEN
  (ANTS_TAC THENL [MESON_TAC[]; ALL_TAC]) THEN
  DISCH_THEN(X_CHOOSE_THEN `nl2:((A)word_loc)spt` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `nl2:((A)word_loc)spt` THEN
  ASM_REWRITE_TAC[PLOOPAUX_eval_clause "loop_If"; get_var_imm_def] THEN
  SIMP[LET_DEF; LET_END_DEF]);;

let PLOOPAUX_subspt_inter_insert = prove
 (`!(m:A spt) (X:num_set) n v x (l0:num_set).
     subspt (inter m X) n /\ domain l0 DELETE v SUBSET domain X ==>
     subspt (inter (insert v x m) l0) (insert v x n)`,
  REWRITE_TAC[SUBSET; IN_DELETE; subspt_lookup; lookup_inter_alt; lookup_insert] THEN
  REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN
  REPEAT COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN ASM_MESON_TAC[]);;

(* subspt (inter (insert v x m) l0) (insert v x n) from an assumption       *)
(* subspt (inter m X) n, with domain l0 DELETE v SUBSET domain X by          *)
(* rewriting                                                                 *)

let PLOOPAUX_SUBSPT_INS_TAC : tactic = fun (asl,w as g) ->
  let parts t =
    match strip_comb t with
      (f,[a;n]) when fst(dest_const f) = "subspt" ->
        (match strip_comb a with
           (g,[m;x]) when fst(dest_const g) = "inter" -> (m,x,n)
         | _ -> failwith "")
    | _ -> failwith "" in
  let (im,_,ins) = parts w in
  let m = match strip_comb im with
            (f,[_;_;m]) when fst(dest_const f) = "insert" -> m | _ -> failwith "" in
  let n = match strip_comb ins with
            (f,[_;_;n]) when fst(dest_const f) = "insert" -> n | _ -> failwith "" in
  let cands = mapfilter (fun (_,th) -> let (m',y,n') = parts (concl th) in
                          if m' = m && n' = n then (y,th) else failwith "") asl in
  FIRST (map (fun (y,th) ->
     MATCH_MP_TAC (ISPECL [m; y] PLOOPAUX_subspt_inter_insert) THEN
     CONJ_TAC THENL
      [ACCEPT_TAC th;
       REWRITE_TAC PLOOPAUX_DOM_RWS THEN REPEAT COND_CASES_TAC THEN
       ASM_REWRITE_TAC[] THEN ASM_MESON_TAC PLOOPAUX_DOM_FACTS]) cands) g;;

(* choose the new locals: a candidate t from a subterm                       *)
(* loop_state_locals_fupd (K t) x of the goal, for which fin succeeds         *)

let PLOOPAUX_NL_TAC (fin:tactic) : tactic = fun (asl,w as g) ->
  let nl,body = dest_exists w in
  let is_upd f k =
    (try fst(dest_const f) = "loop_state_locals_fupd" with Failure _ -> false) &&
    (try fst(dest_const k) = "K" with Failure _ -> false) in
  let cand t =
    match t with
      Comb(Comb(f,Comb(k,x)),_) when is_upd f k && not (free_in nl x) -> x
    | _ -> failwith "" in
  (* also the locals of the state that the new locals update *)
  let cand2 t =
    match t with
      Comb(Comb(f,Comb(k,x)),st) when is_upd f k && x = nl && not (free_in nl st) ->
        mk_icomb(mk_const("loop_state_locals",[]),st)
    | _ -> failwith "" in
  let subs = find_terms (fun _ -> true) body in
  let cands = setify (mapfilter cand subs) in
  let cands2 = subtract (setify (mapfilter cand2 subs)) cands in
  FIRST (map (fun t -> EXISTS_TAC t THEN fin THEN NO_TAC) (cands @ cands2)) g;;

let PLOOPAUX_subspt_insert_step = prove
 (`!(m:A spt) (l0:num_set) n v x.
     subspt (inter m (delete v l0)) n ==>
     subspt (inter (insert v x m) l0) (insert v x n)`,
  REWRITE_TAC[subspt_lookup; lookup_inter_alt; lookup_insert; domain_delete; IN_DELETE] THEN
  REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN
  REPEAT COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN ASM_MESON_TAC[]);;

let PLOOPAUX_LIVE_FIN_TAC : tactic =
  SIMP[PLOOPAUX_live_post_thm; record_fupdselfid "loop_state"] THEN REPEAT CONJ_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE PLOOPAUX_SUBSPT_TAC ORELSE
   (REPEAT (MATCH_MP_TAC PLOOPAUX_subspt_insert_step) THEN
    (FIRST_ASSUM ACCEPT_TAC ORELSE PLOOPAUX_SUBSPT_TAC)) ORELSE
   (MATCH_MP_TAC PLOOPAUX_subspt_inter_insert_out THEN ASM_REWRITE_TAC[] THEN
    (FIRST_ASSUM ACCEPT_TAC ORELSE PLOOPAUX_SUBSPT_TAC)));;

let PLOOPAUX_LIVE_SIMPLE_TAC (c:string) (rws:thm list) : tactic =
  REPEAT GEN_TAC THEN REWRITE_TAC[PLOOPAUX_live_P_def] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC([PLOOPAUX_shrink_rws; PLOOPAUX_eval_clause c; ARITH_EQ] @ rws) THEN
  REWRITE_TAC (PLOOPAUX_clock_case_eqs @ [PAIR_EQ; LET_DEF; LET_END_DEF]) THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE PLOOPAUX_result_rws) THEN TRY (FIRST_ASSUM CONTR_TAC) THEN
  RVEQ_TAC THEN
  PLOOPAUX_LOOKUPS_TAC `locals:((A)word_loc)spt` THEN
  IMP_RES_TAC eval_lemma THEN
  REWRITE_TAC([PLOOPAUX_eval_clause c; PLOOPAUX_eval_clause "loop_Skip"; ARITH_EQ] @ rws) THEN
  SIMP rws THEN
  PLOOPAUX_NL_TAC PLOOPAUX_LIVE_FIN_TAC;;

let PLOOPAUX_live_Store32 = prove
 (`!a w (s:(A,FFI)loop_state). PLOOPAUX_live_P (loop_Store32 a w) s`,
  PLOOPAUX_LIVE_SIMPLE_TAC "loop_Store32" []);;

let PLOOPAUX_live_StoreByte = prove
 (`!a w (s:(A,FFI)loop_state). PLOOPAUX_live_P (loop_StoreByte a w) s`,
  PLOOPAUX_LIVE_SIMPLE_TAC "loop_StoreByte" []);;

let PLOOPAUX_live_Load32 = prove
 (`!a v (s:(A,FFI)loop_state). PLOOPAUX_live_P (loop_Load32 a v) s`,
  PLOOPAUX_LIVE_SIMPLE_TAC "loop_Load32" [loop_set_var_def]);;

let PLOOPAUX_live_LoadByte = prove
 (`!a v (s:(A,FFI)loop_state). PLOOPAUX_live_P (loop_LoadByte a v) s`,
  PLOOPAUX_LIVE_SIMPLE_TAC "loop_LoadByte" [loop_set_var_def]);;

let PLOOPAUX_live_SetGlobal = prove
 (`!dst exp (s:(A,FFI)loop_state). PLOOPAUX_live_P (loop_SetGlobal dst exp) s`,
  PLOOPAUX_LIVE_SIMPLE_TAC "loop_SetGlobal" [loop_set_globals_def]);;

let PLOOPAUX_live_Store = prove
 (`!exp v (s:(A,FFI)loop_state). PLOOPAUX_live_P (loop_Store exp v) s`,
  PLOOPAUX_LIVE_SIMPLE_TAC "loop_Store" [loop_mem_store_def]);;

let PLOOPAUX_live_Assign = prove
 (`!v exp (s:(A,FFI)loop_state). PLOOPAUX_live_P (loop_Assign v exp) s`,
  PLOOPAUX_LIVE_SIMPLE_TAC "loop_Assign" [loop_set_var_def]);;

let PLOOPAUX_live_LocValue = prove
 (`!r l1 (s:(A,FFI)loop_state). PLOOPAUX_live_P (LocValue r l1) s`,
  PLOOPAUX_LIVE_SIMPLE_TAC "LocValue" [loop_set_var_def]);;

let PLOOPAUX_live_LLongMul = prove
 (`!r1 r2 r3 r4 (s:(A,FFI)loop_state).
     PLOOPAUX_live_P (loop_Arith (LLongMul r1 r2 r3 r4)) s`,
  PLOOPAUX_LIVE_SIMPLE_TAC "loop_Arith"
    [loop_arith_def; arith_vars; loop_set_var_def; LET_DEF; LET_END_DEF]);;

let PLOOPAUX_live_LDiv = prove
 (`!r1 r2 r3 (s:(A,FFI)loop_state). PLOOPAUX_live_P (loop_Arith (LDiv r1 r2 r3)) s`,
  PLOOPAUX_LIVE_SIMPLE_TAC "loop_Arith"
    [loop_arith_def; arith_vars; loop_set_var_def; LET_DEF; LET_END_DEF]);;

let PLOOPAUX_live_LLongDiv = prove
 (`!r1 r2 r3 r4 r5 (s:(A,FFI)loop_state).
     PLOOPAUX_live_P (loop_Arith (LLongDiv r1 r2 r3 r4 r5)) s`,
  PLOOPAUX_LIVE_SIMPLE_TAC "loop_Arith"
    [loop_arith_def; arith_vars; loop_set_var_def; LET_DEF; LET_END_DEF; VAL_EQ_0]);;

let PLOOPAUX_live_Arith = prove
 (`!arith (s:(A,FFI)loop_state). PLOOPAUX_live_P (loop_Arith arith) s`,
  MATCH_MP_TAC loop_arith_INDUCT THEN
  REWRITE_TAC[PLOOPAUX_live_LLongMul; PLOOPAUX_live_LDiv; PLOOPAUX_live_LLongDiv]);;

let PLOOPAUX_live_ShMem = prove
 (`!op v ad (s:(A,FFI)loop_state). PLOOPAUX_live_P (loop_ShMem op v ad) s`,
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `op:memop` (cases "memop")) THEN
  PLOOPAUX_LIVE_SIMPLE_TAC "loop_ShMem"
    [loop_sh_mem_op_def; loop_sh_mem_load_def; loop_sh_mem_store_def; is_load_def;
     loop_set_var_def; call_env_def]);;

let PLOOPAUX_subspt_alist_insert = prove
 (`!xs ys (m:A spt) (l0:num_set) n.
     LENGTH xs = LENGTH ys /\ subspt (inter m (list_delete xs l0)) n ==>
     subspt (inter (alist_insert xs ys m) l0) (alist_insert xs ys n)`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; NOT_SUC; ARITH_RULE `~(SUC n = 0)`; SUC_INJ; alist_insert_def;
              list_delete_def] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PLOOPAUX_subspt_insert_step THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let PLOOPAUX_live_Primitive = prove
 (`!lhss pop rhss (s:(A,FFI)loop_state).
     PLOOPAUX_live_P (loop_Primitive lhss pop rhss) s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[PLOOPAUX_live_P_def] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[PLOOPAUX_shrink_rws; PLOOPAUX_eval_clause "loop_Primitive"; set_vars_def] THEN
  REWRITE_TAC (PLOOPAUX_clock_case_eqs @ [PAIR_EQ; LET_DEF; LET_END_DEF]) THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE PLOOPAUX_result_rws) THEN TRY (FIRST_ASSUM CONTR_TAC) THEN
  RVEQ_TAC THEN IMP_RES_TAC get_vars_subspt THEN
  REWRITE_TAC[PLOOPAUX_eval_clause "loop_Primitive"; set_vars_def] THEN SIMP[] THEN
  PLOOPAUX_NL_TAC
   (SIMP[PLOOPAUX_live_post_thm] THEN
    MATCH_MP_TAC PLOOPAUX_subspt_alist_insert THEN ASM_REWRITE_TAC[] THEN
    PLOOPAUX_SUBSPT_TAC));;

let PLOOPAUX_subspt_cut = prove
 (`!(m:A spt) (C:num_set) (l0:num_set) n (X:num_set).
     subspt (inter m X) n /\ domain (inter C l0) SUBSET domain X ==>
     subspt (inter (inter m C) l0) (inter n (inter C l0))`,
  REWRITE_TAC[SUBSET; subspt_lookup; lookup_inter_alt; domain_inter; IN_INTER] THEN
  REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN
  REPEAT COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN ASM_MESON_TAC[]);;

let PLOOPAUX_CUT_FIN_TAC : tactic =
  SIMP[PLOOPAUX_live_post_thm] THEN MATCH_MP_TAC PLOOPAUX_subspt_cut THEN
  FIRST_ASSUM(fun th ->
    let x = rand(rand(rator(concl th))) in
    if not (fst(dest_const(fst(strip_comb(concl th)))) = "subspt") then failwith "" else
    EXISTS_TAC x THEN CONJ_TAC THENL
     [ACCEPT_TAC th;
      REWRITE_TAC PLOOPAUX_DOM_RWS THEN ASM_MESON_TAC PLOOPAUX_DOM_FACTS]);;

let PLOOPAUX_live_FFI = prove
 (`!ffi_index ptr1 len1 ptr2 len2 cutset (s:(A,FFI)loop_state).
     PLOOPAUX_live_P (loop_FFI ffi_index ptr1 len1 ptr2 len2 cutset) s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[PLOOPAUX_live_P_def] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[PLOOPAUX_shrink_rws; PLOOPAUX_eval_clause "loop_FFI"; cut_state_def;
              call_env_def] THEN
  REWRITE_TAC (PLOOPAUX_clock_case_eqs @ [PAIR_EQ; LET_DEF; LET_END_DEF]) THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE PLOOPAUX_result_rws) THEN TRY (FIRST_ASSUM CONTR_TAC) THEN
  RVEQ_TAC THEN PLOOPAUX_LOOKUPS_TAC `locals:((A)word_loc)spt` THEN
  (SUBGOAL_THEN
     `domain (inter (cutset:num_set) (l0:num_set)) SUBSET domain (locals:((A)word_loc)spt)`
     ASSUME_TAC THENL
   [MATCH_MP_TAC(ISPECL [`inter (cutset:num_set) (l0:num_set)`;
                         `loop_state_locals (s:(A,FFI)loop_state)`]
                   subspt_inter_domain_cut) THEN
    CONJ_TAC THENL [REWRITE_TAC[domain_inter] THEN ASM SET_TAC[]; PLOOPAUX_SUBSPT_TAC];
    ALL_TAC]) THEN
  REWRITE_TAC[PLOOPAUX_eval_clause "loop_FFI"; cut_state_def; call_env_def] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[loop_state_INFO.ri_accfupds; K_THM; domain_inter]) THEN
  SIMP[] THEN
  PLOOPAUX_NL_TAC (PLOOPAUX_CUT_FIN_TAC ORELSE PLOOPAUX_LIVE_FIN_TAC));;

(* the Loop case: one round of loop_evaluate (loop_Loop ...) after a cut and *)
(* a run of the body                                                         *)

let PLOOPAUX_loop_unfold = prove
 (`!L (b:(A)loop_prog) L2 (s0:(A,FFI)loop_state) s0' r t0.
     cut_res (L:num_set) (NONE:((A)loop_result)option, s0) = (NONE, s0') /\
     loop_evaluate (b, s0') = (r, t0) ==>
     (r = NONE ==>
      loop_evaluate (loop_Loop L b L2, s0) = loop_evaluate (loop_Loop L b L2, t0)) /\
     (r = SOME (loopSem_Continue 0) ==>
      loop_evaluate (loop_Loop L b L2, s0) = loop_evaluate (loop_Loop L b L2, t0)) /\
     (r = SOME (loopSem_Break 0) ==>
      loop_evaluate (loop_Loop L b L2, s0) = cut_res L2 (NONE, t0)) /\
     (~(r = NONE) /\ ~(r = SOME (loopSem_Continue 0)) /\ ~(r = SOME (loopSem_Break 0)) ==>
      loop_evaluate (loop_Loop L b L2, s0) = (loop_exit_loop r, t0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBST1_TAC(SPECL [`L:num_set`; `b:(A)loop_prog`; `L2:num_set`; `s0:(A,FFI)loop_state`]
                (PLOOPAUX_eval_clause "loop_Loop")) THEN
  ASM_REWRITE_TAC[case_def "prod"; case_def "option"] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN
  STRUCT_CASES_TAC (ISPEC `r:((A)loop_result)option` (cases "option")) THEN
  REWRITE_TAC[case_def "option"; option_DISTINCT; option_INJ] THEN
  STRUCT_CASES_TAC (ISPEC `a:(A)loop_result` (cases "loop_result")) THEN
  REWRITE_TAC[case_def "loop_result"; distinctness "loop_result";
              injectivity "loop_result"] THEN
  TRY COND_CASES_TAC THEN ASM_REWRITE_TAC[loop_exit_loop_def]);;

let PLOOPAUX_cut_res_NONE_cases = prove
 (`!(L:num_set) (s:(A,FFI)loop_state) q s'.
     cut_res L (NONE:((A)loop_result)option, s) = (q, s') ==>
     q = SOME loop_Error \/
     (domain L SUBSET domain (loop_state_locals s) /\ loop_state_clock s = 0 /\
      q = SOME loop_TimeOut /\ s' = loop_state_locals_fupd (K LN) s) \/
     (domain L SUBSET domain (loop_state_locals s) /\ ~(loop_state_clock s = 0) /\
      q = NONE /\
      s' = loop_dec_clock (loop_state_locals_fupd (K (inter (loop_state_locals s) L)) s))`,
  REWRITE_TAC[cut_res_def; cut_state_def] THEN REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[case_def "option"; PAIR_EQ] THENL
   [SIMP[] THEN COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
    RVEQ_TAC THEN SIMP[];
    MESON_TAC[]]);;

let PLOOPAUX_cut_res_NONE_eq = prove
 (`!(L:num_set) (s:(A,FFI)loop_state).
     domain L SUBSET domain (loop_state_locals s) ==>
     cut_res L (NONE:((A)loop_result)option, s) =
     if loop_state_clock s = 0 then (SOME loop_TimeOut, loop_state_locals_fupd (K LN) s)
     else (NONE, loop_dec_clock (loop_state_locals_fupd (K (inter (loop_state_locals s) L)) s))`,
  REWRITE_TAC[cut_res_def; cut_state_def] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[case_def "option"] THEN SIMP[]);;

let PLOOPAUX_live_post_exit = prove
 (`!x lt l0 l0' r (t:(A,FFI)loop_state) nl.
     ~(r = NONE) /\ ~(r = SOME (loopSem_Continue 0)) /\ ~(r = SOME (loopSem_Break 0)) /\
     PLOOPAUX_live_post (CONS x lt) l0' r t nl ==>
     PLOOPAUX_live_post lt l0 (loop_exit_loop r) t nl`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `r:((A)loop_result)option` (cases "option")) THEN
  REWRITE_TAC[option_DISTINCT; option_INJ; loop_exit_loop_def] THEN
  STRUCT_CASES_TAC (ISPEC `a:(A)loop_result` (cases "loop_result")) THEN
  REWRITE_TAC[distinctness "loop_result"; injectivity "loop_result"; loop_exit_loop_def;
              PLOOPAUX_live_post_thm] THEN
  REWRITE_TAC[oEL_def] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_REWRITE_TAC[]);;

let PLOOPAUX_loop_cut_not_NONE = prove
 (`!L (b:(A)loop_prog) L2 (s0:(A,FFI)loop_state) q s0'.
     cut_res (L:num_set) (NONE:((A)loop_result)option, s0) = (q, s0') /\ ~(q = NONE) ==>
     loop_evaluate (loop_Loop L b L2, s0) = (q, s0')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBST1_TAC(SPECL [`L:num_set`; `b:(A)loop_prog`; `L2:num_set`; `s0:(A,FFI)loop_state`]
                (PLOOPAUX_eval_clause "loop_Loop")) THEN
  ASM_REWRITE_TAC[case_def "prod"] THEN
  UNDISCH_TAC `~(q:((A)loop_result)option = NONE)` THEN
  STRUCT_CASES_TAC (ISPEC `q:((A)loop_result)option` (cases "option")) THEN
  REWRITE_TAC[case_def "option"]);;

let PLOOPAUX_subspt_loop_entry = prove
 (`!(m:A spt) (L1:num_set) n (li:num_set) (X:num_set).
     subspt (inter m L1) n /\ domain li INTER domain X SUBSET domain L1 ==>
     subspt (inter (inter m li) X) (inter n L1)`,
  REWRITE_TAC[SUBSET; subspt_lookup; lookup_inter_alt; IN_INTER] THEN
  REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN
  REPEAT COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN ASM_MESON_TAC[]);;

let PLOOPAUX_is_P_var_ih tm =
  is_forall tm &&
  (let _,bd = strip_forall tm in
   is_imp bd &&
   (let f,args = strip_comb (rand bd) in
    (try fst(dest_const f) = "PLOOPAUX_live_P" with Failure _ -> false) &&
    is_var (hd args)));;

let PLOOPAUX_is_P_loop_ih (cont:bool) tm =
  is_forall tm &&
  (let _,bd = strip_forall tm in
   is_imp bd &&
   (let f,args = strip_comb (rand bd) in
    (try fst(dest_const f) = "PLOOPAUX_live_P" with Failure _ -> false) &&
    (try fst(dest_const(fst(strip_comb(hd args)))) = "loop_Loop" with Failure _ -> false)) &&
   (can (find_term (fun t -> try fst(dest_const t) = "loopSem_Continue"
                             with Failure _ -> false)) tm = cont));;

(* the Loop case for a shrunk loop loop_Loop L1 b (inter lo l0) whose body *)
(* b was shrunk in the context CONS (L1,BRK) lt (both shapes of shrink:   *)
(* with and without a fixed point)                                        *)

let PLOOPAUX_live_Loop_core = prove
 (`!li body lo (s:(A,FFI)loop_state) lt l0 L1 b X BRK.
    (!s'' s'. cut_res li (NONE:((A)loop_result)option,s) = (NONE,s'') /\
              loop_evaluate (body,s'') = (SOME (loopSem_Continue 0),s')
              ==> PLOOPAUX_live_P (loop_Loop li body lo) s') /\
    (!s'' s'. cut_res li (NONE:((A)loop_result)option,s) = (NONE,s'') /\
              loop_evaluate (body,s'') = (NONE,s')
              ==> PLOOPAUX_live_P (loop_Loop li body lo) s') /\
    (!s'. cut_res li (NONE:((A)loop_result)option,s) = (NONE,s')
          ==> PLOOPAUX_live_P body s') /\
    loop_live_shrink lt (loop_Loop li body lo) l0 = (loop_Loop L1 b (inter lo l0), L1) /\
    loop_live_shrink (CONS (L1,BRK) lt) body (union li (inter lo l0)) = (b,X) /\
    domain L1 SUBSET domain li /\ domain li INTER domain X SUBSET domain L1 /\
    domain (inter lo l0) SUBSET domain BRK ==>
    !res s1 locals.
      loop_evaluate (loop_Loop li body lo,s) = (res,s1) /\ ~(res = SOME loop_Error) /\
      subspt (inter (loop_state_locals s) L1) locals ==>
      ?nl. loop_evaluate (loop_Loop L1 b (inter lo l0),
                          loop_state_locals_fupd (K locals) s) =
           (res, loop_state_locals_fupd (K nl) s1) /\
           PLOOPAUX_live_post lt l0 res s1 nl`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  PAIR_CASES_ON `cut_res (li:num_set) (NONE:((A)loop_result)option, s:(A,FFI)loop_state)` THEN
  FIRST_ASSUM(DISJ_CASES_THEN2 ASSUME_TAC (DISJ_CASES_THEN STRIP_ASSUME_TAC) o
              MATCH_MP PLOOPAUX_cut_res_NONE_cases) THENL
  [(* the cut fails *)
   MP_TAC(ISPECL [`li:num_set`; `body:(A)loop_prog`; `lo:num_set`; `s:(A,FFI)loop_state`;
                  `p0:((A)loop_result)option`; `p1:(A,FFI)loop_state`]
                 PLOOPAUX_loop_cut_not_NONE) THEN
   ASM_REWRITE_TAC[option_DISTINCT] THEN ASM_MESON_TAC[PAIR_EQ];
   (* the clock runs out at the cut *)
   RVEQ_TAC THEN
   SUBGOAL_THEN `domain (L1:num_set) SUBSET domain (locals:((A)word_loc)spt)` ASSUME_TAC
   THENL
   [MATCH_MP_TAC(ISPECL [`L1:num_set`; `loop_state_locals (s:(A,FFI)loop_state)`]
                   subspt_inter_domain_cut) THEN ASM_MESON_TAC[SUBSET_TRANS]; ALL_TAC] THEN
   MP_TAC(ISPECL [`li:num_set`; `body:(A)loop_prog`; `lo:num_set`; `s:(A,FFI)loop_state`;
                  `SOME loop_TimeOut:((A)loop_result)option`;
                  `loop_state_locals_fupd (K LN) (s:(A,FFI)loop_state)`]
                 PLOOPAUX_loop_cut_not_NONE) THEN
   ASM_REWRITE_TAC[option_DISTINCT] THEN DISCH_TAC THEN
   SUBGOAL_THEN `res = SOME loop_TimeOut:((A)loop_result)option /\
                 s1 = loop_state_locals_fupd (K LN) (s:(A,FFI)loop_state)`
     STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[PAIR_EQ]; ALL_TAC] THEN
   RVEQ_TAC THEN
   MP_TAC(ISPECL [`L1:num_set`; `loop_state_locals_fupd (K locals) (s:(A,FFI)loop_state)`]
                 PLOOPAUX_cut_res_NONE_eq) THEN
   SIMP[] THEN DISCH_TAC THEN
   MP_TAC(ISPECL [`L1:num_set`; `b:(A)loop_prog`; `inter (lo:num_set) (l0:num_set)`;
                  `loop_state_locals_fupd (K locals) (s:(A,FFI)loop_state)`;
                  `SOME loop_TimeOut:((A)loop_result)option`;
                  `loop_state_locals_fupd (K LN) (s:(A,FFI)loop_state)`]
                 PLOOPAUX_loop_cut_not_NONE) THEN
   ASM_SIMP_TAC[option_DISTINCT] THEN DISCH_TAC THEN
   EXISTS_TAC `LN:((A)word_loc)spt` THEN SIMP[PLOOPAUX_live_post_thm];
   (* the body runs *)
   RVEQ_TAC THEN
   SUBGOAL_THEN `domain (L1:num_set) SUBSET domain (locals:((A)word_loc)spt)` ASSUME_TAC
   THENL
   [MATCH_MP_TAC(ISPECL [`L1:num_set`; `loop_state_locals (s:(A,FFI)loop_state)`]
                   subspt_inter_domain_cut) THEN ASM_MESON_TAC[SUBSET_TRANS]; ALL_TAC] THEN
   ABBREV_TAC `s2 = loop_dec_clock (loop_state_locals_fupd
                      (K (inter (loop_state_locals s) (li:num_set))) (s:(A,FFI)loop_state))` THEN
   SUBGOAL_THEN
     `cut_res (L1:num_set) (NONE:((A)loop_result)option,
                            loop_state_locals_fupd (K locals) (s:(A,FFI)loop_state)) =
      (NONE, loop_state_locals_fupd (K (inter locals L1)) s2)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[PLOOPAUX_cut_res_NONE_eq; loop_state_INFO.ri_accfupds; K_THM] THEN
    EXPAND_TAC "s2" THEN SIMP_NOASM[loop_dec_clock_def]; ALL_TAC] THEN
   PAIR_CASES_ON `loop_evaluate (body:(A)loop_prog, s2:(A,FFI)loop_state)` THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `s2:(A,FFI)loop_state` o
     check (PLOOPAUX_is_P_var_ih o concl)) THEN
   REWRITE_TAC[] THEN DISCH_TAC THEN
   MP_TAC(ISPECL [`li:num_set`; `body:(A)loop_prog`; `lo:num_set`; `s:(A,FFI)loop_state`;
                  `s2:(A,FFI)loop_state`; `p0':((A)loop_result)option`;
                  `p1':(A,FFI)loop_state`] PLOOPAUX_loop_unfold) THEN
   ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
   SUBGOAL_THEN `~(p0':((A)loop_result)option = SOME loop_Error)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
                                            is_conj (lhand (concl th)))) THEN
    ASM_REWRITE_TAC(loop_exit_loop_def :: PAIR_EQ :: PLOOPAUX_result_rws);
    ALL_TAC] THEN
   SUBGOAL_THEN `subspt (inter (loop_state_locals (s2:(A,FFI)loop_state)) (X:num_set))
                        (inter (locals:((A)word_loc)spt) (L1:num_set))` ASSUME_TAC THENL
   [EXPAND_TAC "s2" THEN SIMP_NOASM[loop_dec_clock_def] THEN
    MATCH_MP_TAC PLOOPAUX_subspt_loop_entry THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   PLOOPAUX_P_SPEC_TAC `PLOOPAUX_live_P (body:(A)loop_prog) (s2:(A,FFI)loop_state)`
     [`p0':((A)loop_result)option`; `p1':(A,FFI)loop_state`;
      `CONS (L1:num_set,BRK:num_set) lt`;
      `inter (locals:((A)word_loc)spt) (L1:num_set)`; `b:(A)loop_prog`; `X:num_set`;
      `union (li:num_set) (inter (lo:num_set) (l0:num_set))`]
     `nl1:((A)word_loc)spt` THEN
   MP_TAC(ISPECL [`L1:num_set`; `b:(A)loop_prog`; `inter (lo:num_set) (l0:num_set)`;
                  `loop_state_locals_fupd (K locals) (s:(A,FFI)loop_state)`;
                  `loop_state_locals_fupd (K (inter (locals:((A)word_loc)spt) (L1:num_set)))
                     (s2:(A,FFI)loop_state)`;
                  `p0':((A)loop_result)option`;
                  `loop_state_locals_fupd (K nl1) (p1':(A,FFI)loop_state)`]
                 PLOOPAUX_loop_unfold) THEN
   ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
   ASM_CASES_TAC `p0':((A)loop_result)option = NONE` THENL
   [(* the body ends normally: the next round *)
    POP_ASSUM SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE (PLOOPAUX_live_post_thm :: PLOOPAUX_result_rws)) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`s2:(A,FFI)loop_state`; `p1':(A,FFI)loop_state`] o
      check (PLOOPAUX_is_P_loop_ih false o concl)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[SUBSET]) THEN
    SUBGOAL_THEN `subspt (inter (loop_state_locals (p1':(A,FFI)loop_state)) (L1:num_set))
                         (nl1:((A)word_loc)spt)` ASSUME_TAC THENL
    [PLOOPAUX_SUBSPT_TAC; ALL_TAC] THEN
    PLOOPAUX_P_SPEC_TAC `PLOOPAUX_live_P (loop_Loop li body lo) (p1':(A,FFI)loop_state)`
      [`res:((A)loop_result)option`; `s1:(A,FFI)loop_state`; `lt:(num_set#num_set)list`;
       `nl1:((A)word_loc)spt`;
       `loop_Loop L1 (b:(A)loop_prog) (inter (lo:num_set) (l0:num_set))`;
       `L1:num_set`; `l0:num_set`] `nl2:((A)word_loc)spt` THEN
    EXISTS_TAC `nl2:((A)word_loc)spt` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `p0':((A)loop_result)option = SOME (loopSem_Continue 0)` THENL
   [(* Continue 0: the next round *)
    POP_ASSUM SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE (PLOOPAUX_live_post_thm :: oEL_def :: PAIR_EQ ::
                                 PLOOPAUX_result_rws)) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`s2:(A,FFI)loop_state`; `p1':(A,FFI)loop_state`] o
      check (PLOOPAUX_is_P_loop_ih true o concl)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `subspt (inter (loop_state_locals (p1':(A,FFI)loop_state)) (L1:num_set))
                         (nl1:((A)word_loc)spt)` ASSUME_TAC THENL
    [ASM_MESON_TAC[]; ALL_TAC] THEN
    PLOOPAUX_P_SPEC_TAC `PLOOPAUX_live_P (loop_Loop li body lo) (p1':(A,FFI)loop_state)`
      [`res:((A)loop_result)option`; `s1:(A,FFI)loop_state`; `lt:(num_set#num_set)list`;
       `nl1:((A)word_loc)spt`;
       `loop_Loop L1 (b:(A)loop_prog) (inter (lo:num_set) (l0:num_set))`;
       `L1:num_set`; `l0:num_set`] `nl2:((A)word_loc)spt` THEN
    EXISTS_TAC `nl2:((A)word_loc)spt` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `p0':((A)loop_result)option = SOME (loopSem_Break 0)` THENL
   [(* Break 0: the exit cut *)
    POP_ASSUM SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE (PLOOPAUX_live_post_thm :: oEL_def :: PAIR_EQ ::
                                 PLOOPAUX_result_rws)) THEN
    SUBGOAL_THEN `subspt (inter (loop_state_locals (p1':(A,FFI)loop_state)) (BRK:num_set))
                         (nl1:((A)word_loc)spt)` ASSUME_TAC THENL
    [ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`lo:num_set`; `inter (lo:num_set) (l0:num_set)`; `l0:num_set`;
                   `lt:(num_set#num_set)list`; `NONE:((A)loop_result)option`;
                   `p1':(A,FFI)loop_state`; `nl1:((A)word_loc)spt`;
                   `res:((A)loop_result)option`; `s1:(A,FFI)loop_state`]
                  PLOOPAUX_cut_res_live) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[SUBSET]) THEN
    ASM_REWRITE_TAC[PLOOPAUX_live_post_thm] THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; domain_inter; IN_INTER] THEN MESON_TAC[];
        REWRITE_TAC[SUBSET; domain_inter; IN_INTER] THEN MESON_TAC[];
        PLOOPAUX_SUBSPT_TAC];
      DISCH_THEN ACCEPT_TAC];
    ALL_TAC] THEN
  (* the other results leave the loop *)
  SUBGOAL_THEN `res = loop_exit_loop (p0':((A)loop_result)option) /\
                (s1:(A,FFI)loop_state) = p1'` STRIP_ASSUME_TAC THENL
  [ASM_MESON_TAC[PAIR_EQ]; ALL_TAC] THEN
  EXISTS_TAC `nl1:((A)word_loc)spt` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
  [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_imp (concl th) &&
      is_conj (lhand (concl th)) &&
      (try fst(dest_const(fst(strip_comb(lhs(rand(concl th)))))) = "loop_evaluate"
       with Failure _ -> false) &&
      free_in `L1:num_set` (concl th))) THEN ASM_REWRITE_TAC[];
   MATCH_MP_TAC(ISPECL [`(L1:num_set,BRK:num_set)`; `lt:(num_set#num_set)list`;
                        `l0:num_set`; `union (li:num_set) (inter (lo:num_set) (l0:num_set))`]
                  PLOOPAUX_live_post_exit) THEN
   ASM_REWRITE_TAC[]]]);;

let PLOOPAUX_live_Loop_core' =
  REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP] PLOOPAUX_live_Loop_core;;

let PLOOPAUX_live_Loop = prove
 (`!live_in body live_out (s:(A,FFI)loop_state).
     (!s'' s'. cut_res live_in (NONE:((A)loop_result)option,s) = (NONE,s'') /\
               loop_evaluate (body,s'') = (SOME (loopSem_Continue 0),s')
               ==> PLOOPAUX_live_P (loop_Loop live_in body live_out) s') /\
     (!s'' s'. cut_res live_in (NONE:((A)loop_result)option,s) = (NONE,s'') /\
               loop_evaluate (body,s'') = (NONE,s')
               ==> PLOOPAUX_live_P (loop_Loop live_in body live_out) s') /\
     (!s'. cut_res live_in (NONE:((A)loop_result)option,s) = (NONE,s')
           ==> PLOOPAUX_live_P body s')
     ==> PLOOPAUX_live_P (loop_Loop live_in body live_out) s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  GEN_REWRITE_TAC I [PLOOPAUX_live_P_def] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
    (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "loop_live_shrink"
     with Failure _ -> false))) THEN
  REWRITE_TAC[PLOOPAUX_shrink_rws; LET_DEF; LET_END_DEF] THEN
  STRIP_ASSUME_TAC(ISPEC `fixedpoint (lt:(num_set#num_set)list) live_in LN
       (union live_in (inter live_out (l0:num_set))) (body:(A)loop_prog)` (cases "option")) THEN
  ASM_REWRITE_TAC[case_def "option"] THENL
  [(* no fixed point: the body shrunk once *)
   PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
   MATCH_MP_TAC PLOOPAUX_live_Loop_core' THEN ASM_EXISTS_TAC THEN SET_TAC[];
   (* a fixed point *)
   PAIR_CASES_ON `a:(A)loop_prog#num_set` THEN
   REWRITE_TAC[case_def "prod"; LET_DEF; LET_END_DEF; PAIR_EQ] THEN STRIP_TAC THEN
   RVEQ_TAC THEN
   FIRST_ASSUM(ASSUME_TAC o MATCH_MP fixedpoint_thm) THEN
   MATCH_MP_TAC PLOOPAUX_live_Loop_core' THEN ASM_EXISTS_TAC THEN
   REWRITE_TAC[domain_inter; domain_union] THEN SET_TAC[]]);;

(* the Call case *)

let PLOOPAUX_domain_args = prove
 (`!args. domain (fromAList (MAP (\x. (x,one)) args)) = set_of_list args`,
  REWRITE_TAC[domain_fromAList] THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[MAP; set_of_list]);;

let PLOOPAUX_get_vars_dom = prove
 (`!xs ws (s:(A,FFI)loop_state) (L:num_set) locals.
     get_vars xs s = SOME ws /\ set_of_list xs SUBSET domain L /\
     subspt (inter (loop_state_locals s) L) locals ==>
     get_vars xs (loop_state_locals_fupd (K locals) s) = SOME ws`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC get_vars_subspt THEN
  EXISTS_TAC `LN:num_set` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(ISPECL [`L:num_set`; `loop_state_locals (s:(A,FFI)loop_state)`]
                 PLOOPAUX_subspt_inter_mono) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET; domain_list_insert; domain_def; NOT_IN_EMPTY] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; IN_SET_OF_LIST]) THEN ASM_MESON_TAC[]);;

let PLOOPAUX_live_post_mono = prove
 (`!lt (l0:num_set) (L:num_set) res (t:(A,FFI)loop_state) nl.
     PLOOPAUX_live_post lt l0 res t nl /\ domain L SUBSET domain l0 ==>
     PLOOPAUX_live_post lt L res t nl`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `res:((A)loop_result)option = NONE` THENL
  [ASM_REWRITE_TAC[PLOOPAUX_live_post_thm] THEN STRIP_TAC THEN
   MATCH_MP_TAC(ISPECL [`l0:num_set`; `loop_state_locals (t:(A,FFI)loop_state)`]
                  PLOOPAUX_subspt_inter_mono) THEN ASM_REWRITE_TAC[];
   ASM_MESON_TAC[PLOOPAUX_live_post_not_NONE]]);;

let PLOOPAUX_get_vars_dom_imp = REWRITE_RULE[IMP_CONJ] PLOOPAUX_get_vars_dom;;

(* for assumptions get_vars xs s = SOME ws and                               *)
(* subspt (inter (loop_state_locals s) L) loc, add                          *)
(* get_vars xs (loop_state_locals_fupd (K loc) s) = SOME ws (set xs is in   *)
(* domain L by rewriting)                                                   *)

let PLOOPAUX_CALL_GV_TAC : tactic = fun (asl,w as g) ->
  let ths = map snd asl in
  let is_gv th = let t = concl th in is_eq t &&
     (try fst(dest_const(fst(strip_comb(lhs t)))) = "get_vars" &&
          is_var (rand(lhs t)) with Failure _ -> false) in
  let sp_parts th =
     match strip_comb (concl th) with
       (f,[a;n]) when fst(dest_const f) = "subspt" ->
         (match strip_comb a with
            (g,[m;x]) when fst(dest_const g) = "inter" &&
                           fst(dest_const(rator m)) = "loop_state_locals" -> (rand m, x, n)
          | _ -> failwith "")
     | _ -> failwith "" in
  let pairs = flat (map (fun gv ->
     let st = rand(lhs(concl gv)) in
     mapfilter (fun sp -> let (st',x,n) = sp_parts sp in
                          if st' = st then (gv,x,n,sp) else failwith "") ths)
     (filter is_gv ths)) in
  MAP_EVERY (fun (gv,x,n,sp) ->
     TRY (fun g ->
          (MP_TAC(SPECL [x;n] (MATCH_MP PLOOPAUX_get_vars_dom_imp gv)) THEN
           ANTS_TAC THENL
            [REWRITE_TAC (PLOOPAUX_domain_args :: PLOOPAUX_DOM_RWS) THEN MESON_TAC[];
             DISCH_THEN(ASSUME_TAC o C MP sp)]) g)) pairs g;;

let PLOOPAUX_live_Call_NONE = prove
 (`!dest args handler (s:(A,FFI)loop_state).
     PLOOPAUX_live_P (loop_Call NONE dest args handler) s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[PLOOPAUX_live_P_def] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[PLOOPAUX_shrink_rws; LET_DEF; LET_END_DEF; case_def "option";
              PLOOPAUX_eval_clause "loop_Call"] THEN
  REWRITE_TAC (PLOOPAUX_clock_case_eqs @ [PAIR_EQ]) THEN STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE PLOOPAUX_result_rws) THEN TRY (FIRST_ASSUM CONTR_TAC) THEN
  RVEQ_TAC THEN PLOOPAUX_CALL_GV_TAC THEN
  RULE_ASSUM_TAC(fun th -> if PLOOPAUX_is_eval_eq (concl th)
                           then CAKE_SIMP_RULE[loop_dec_clock_def] th else th) THEN
  REWRITE_TAC[PLOOPAUX_eval_clause "loop_Call"] THEN SIMP[loop_dec_clock_def] THEN
  PLOOPAUX_NL_TAC PLOOPAUX_LIVE_FIN_TAC);;

let PLOOPAUX_cut_res_sub_NONE = prove
 (`!(L:num_set) (s:(A,FFI)loop_state) s' (L':num_set) locals.
     cut_res L (NONE:((A)loop_result)option, s) = (NONE, s') /\
     domain L' SUBSET domain L /\ subspt (inter (loop_state_locals s) L') locals ==>
     cut_res L' (NONE:((A)loop_result)option, loop_state_locals_fupd (K locals) s) =
     (NONE, loop_state_locals_fupd (K (inter locals L')) s')`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o MATCH_MP PLOOPAUX_cut_res_NONE_cases) STRIP_ASSUME_TAC) THEN
  REWRITE_TAC PLOOPAUX_result_rws THEN STRIP_TAC THEN RVEQ_TAC THEN
  SUBGOAL_THEN `domain (L':num_set) SUBSET domain (locals:((A)word_loc)spt)` ASSUME_TAC THENL
  [MATCH_MP_TAC(ISPECL [`L':num_set`; `loop_state_locals (s:(A,FFI)loop_state)`]
                  subspt_inter_domain_cut) THEN ASM_MESON_TAC[SUBSET_TRANS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`L':num_set`; `loop_state_locals_fupd (K locals) (s:(A,FFI)loop_state)`]
                PLOOPAUX_cut_res_NONE_eq) THEN
  SIMP[loop_dec_clock_def]);;

let PLOOPAUX_cut_res_sub_TO = prove
 (`!(L:num_set) (s:(A,FFI)loop_state) s' (L':num_set) locals.
     cut_res L (NONE:((A)loop_result)option, s) = (SOME loop_TimeOut, s') /\
     domain L' SUBSET domain L /\ subspt (inter (loop_state_locals s) L') locals ==>
     cut_res L' (NONE:((A)loop_result)option, loop_state_locals_fupd (K locals) s) =
     (SOME loop_TimeOut, s')`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o MATCH_MP PLOOPAUX_cut_res_NONE_cases) STRIP_ASSUME_TAC) THEN
  REWRITE_TAC PLOOPAUX_result_rws THEN STRIP_TAC THEN RVEQ_TAC THEN
  SUBGOAL_THEN `domain (L':num_set) SUBSET domain (locals:((A)word_loc)spt)` ASSUME_TAC THENL
  [MATCH_MP_TAC(ISPECL [`L':num_set`; `loop_state_locals (s:(A,FFI)loop_state)`]
                  subspt_inter_domain_cut) THEN ASM_MESON_TAC[SUBSET_TRANS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`L':num_set`; `loop_state_locals_fupd (K locals) (s:(A,FFI)loop_state)`]
                PLOOPAUX_cut_res_NONE_eq) THEN
  SIMP[]);;

let PLOOPAUX_subspt_entry2 = prove
 (`!(m:A spt) (X:num_set) n (live:num_set) (Y:num_set) (L':num_set).
     subspt (inter m X) n /\ domain live INTER domain Y SUBSET domain L' /\
     domain L' SUBSET domain X ==>
     subspt (inter (inter m live) Y) (inter n L')`,
  REWRITE_TAC[SUBSET; subspt_lookup; lookup_inter_alt; IN_INTER] THEN
  REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN
  REPEAT COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN ASM_MESON_TAC[]);;

let PLOOPAUX_cut_res_sub_NONE_imp = REWRITE_RULE[IMP_CONJ] PLOOPAUX_cut_res_sub_NONE;;
let PLOOPAUX_cut_res_sub_TO_imp = REWRITE_RULE[IMP_CONJ] PLOOPAUX_cut_res_sub_TO;;

(* for an assumption cut_res L (NONE,s) = (q,s') with q NONE or TimeOut,     *)
(* add the cut of the new state at L' (and, for NONE, the locals of s')      *)

let PLOOPAUX_CALL_CUT_TAC (L':term) (loc:term) : tactic = fun (asl,w as g) ->
  let is_cut th = let c = concl th in is_eq c &&
     (try fst(dest_const(fst(strip_comb(lhs c)))) = "cut_res" &&
          is_var (snd(dest_pair(rand(lhs c)))) with Failure _ -> false) in
  let cuts = filter is_cut (map snd asl) in
  let one th =
    let q = fst(dest_pair(rhs(concl th))) in
    let lem = if is_const q then PLOOPAUX_cut_res_sub_NONE_imp else PLOOPAUX_cut_res_sub_TO_imp in
    MP_TAC(SPECL [L'; loc] (MATCH_MP lem th)) THEN
    ANTS_TAC THENL [REWRITE_TAC PLOOPAUX_DOM_RWS THEN MESON_TAC[]; ALL_TAC] THEN
    ANTS_TAC THENL [PLOOPAUX_SUBSPT_TAC; DISCH_TAC] THEN
    (if is_const q then
       MP_TAC(MATCH_MP PLOOPAUX_cut_res_NONE_cases th) THEN
       REWRITE_TAC PLOOPAUX_result_rws THEN STRIP_TAC
     else ALL_TAC) in
  MAP_EVERY (fun th -> TRY (fun g -> one th g)) cuts g;;

(* subspt (inter (inter m live) Y) (inter n L') from an assumption           *)
(* subspt (inter m X) n, with the domain conditions by rewriting            *)

let PLOOPAUX_ENTRY2_TAC : tactic =
  MATCH_MP_TAC PLOOPAUX_subspt_entry2 THEN
  FIRST_ASSUM(fun th ->
    let c = concl th in
    if not (try fst(dest_const(fst(strip_comb c))) = "subspt" with Failure _ -> false)
    then failwith "" else
    let x = rand(rand(rator c)) in
    EXISTS_TAC x THEN REPEAT CONJ_TAC THENL
     [ACCEPT_TAC th;
      REWRITE_TAC PLOOPAUX_DOM_RWS THEN ASM_MESON_TAC PLOOPAUX_DOM_FACTS;
      REWRITE_TAC (PLOOPAUX_domain_args :: PLOOPAUX_DOM_RWS) THEN
      ASM_MESON_TAC PLOOPAUX_DOM_FACTS]);;

let PLOOPAUX_CALL_FIN_TAC : tactic =
  SIMP[PLOOPAUX_live_post_thm; record_fupdselfid "loop_state"] THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE
   (MATCH_MP_TAC PLOOPAUX_subspt_alist_insert THEN ASM_REWRITE_TAC[] THEN
    PLOOPAUX_ENTRY2_TAC));;

(* an assumption cut_res L (NONE,s) = (SOME v,s') with v a variable: v is   *)
(* TimeOut (the other results of a cut of NONE are excluded)                *)

let PLOOPAUX_CUT_CASES_TAC : tactic = fun (asl,w as g) ->
  let is_cut th = let c = concl th in is_eq c &&
     (try fst(dest_const(fst(strip_comb(lhs c)))) = "cut_res" &&
          (let q = fst(dest_pair(rhs c)) in is_comb q && is_var (rand q))
      with Failure _ -> false) in
  let cuts = filter is_cut (map snd asl) in
  MAP_EVERY (fun th -> fun g ->
     (MP_TAC(MATCH_MP PLOOPAUX_cut_res_NONE_cases th) THEN
      REWRITE_TAC PLOOPAUX_result_rws THEN STRIP_TAC THEN RVEQ_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE PLOOPAUX_result_rws) THEN
      TRY (FIRST_ASSUM CONTR_TAC)) g) cuts g;;

let PLOOPAUX_live_Call_SOME_NONE = prove
 (`!ns live dest args (s:(A,FFI)loop_state).
     PLOOPAUX_live_P (loop_Call (SOME (ns,live)) dest args NONE) s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[PLOOPAUX_live_P_def] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[PLOOPAUX_shrink_rws; LET_DEF; LET_END_DEF; case_def "option"; case_def "prod";
              PLOOPAUX_eval_clause "loop_Call"] THEN
  REWRITE_TAC (PLOOPAUX_clock_case_eqs @ [PAIR_EQ]) THEN STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE PLOOPAUX_result_rws) THEN TRY (FIRST_ASSUM CONTR_TAC) THEN
  RVEQ_TAC THEN PLOOPAUX_CUT_CASES_TAC THEN PLOOPAUX_CALL_GV_TAC THEN
  PLOOPAUX_CALL_CUT_TAC `list_delete ns (inter (l0:num_set) (live:num_set))`
    `locals:((A)word_loc)spt` THEN
  RVEQ_TAC THEN
  RULE_ASSUM_TAC(fun th -> if PLOOPAUX_is_eval_eq (concl th)
                           then CAKE_SIMP_RULE[loop_dec_clock_def] th else th) THEN
  REWRITE_TAC[PLOOPAUX_eval_clause "loop_Call"] THEN
  SIMP[loop_dec_clock_def; set_vars_def; loop_set_var_def] THEN
  PLOOPAUX_NL_TAC PLOOPAUX_CALL_FIN_TAC);;

(* the handler programs of a call: the induction hypothesis for the state   *)
(* set_vars ns retvs X (or loop_set_var e exn X), with the new locals       *)
(* alist_insert ns retvs newl (or insert e exn newl)                        *)

let PLOOPAUX_HANDLER_IH_TAC (newl:term) (nl:term) (fin:tactic) : tactic = fun (asl,w as g) ->
  let is_P t = try fst(dest_const(fst(strip_comb t))) = "PLOOPAUX_live_P"
               with Failure _ -> false in
  let pst = find is_P (map (concl o snd) asl) in
  let st = rand pst in
  let f,args = strip_comb st in
  let loc = match (fst(dest_const f), args) with
      ("set_vars", [ns;retvs;_]) ->
         mk_icomb(mk_icomb(mk_icomb(mk_const("alist_insert",[]),ns),retvs),newl)
    | ("loop_set_var", [e;exn;_]) ->
         mk_icomb(mk_icomb(mk_icomb(mk_const("insert",[]),e),exn),newl)
    | _ -> failwith "PLOOPAUX_HANDLER_IH_TAC" in
  PLOOPAUX_LIVE_IH_TAC loc nl fin g;;

let PLOOPAUX_HANDLER_FIN_TAC : tactic =
  SIMP[set_vars_def; loop_set_var_def; loop_dec_clock_def] THEN
  ((MATCH_MP_TAC PLOOPAUX_subspt_alist_insert THEN ASM_REWRITE_TAC[] THEN
    PLOOPAUX_ENTRY2_TAC) ORELSE
   (MATCH_MP_TAC PLOOPAUX_subspt_insert_step THEN PLOOPAUX_ENTRY2_TAC));;

let PLOOPAUX_PAIR_VARS_TAC : tactic =
  RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  REPEAT(FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if is_eq c && is_var (lhs c) && is_var (rhs c) && not (lhs c = rhs c)
    then SUBST_ALL_TAC (SYM th) else failwith ""));;

(* a branch of the call that runs a handler program (the induction          *)
(* hypothesis was added), and one that does not                            *)

let PLOOPAUX_CALL_HANDLER_TAC (newl:term) : tactic =
  PLOOPAUX_SPLIT_EVAL_TAC THEN IMP_RES_TAC PLOOPAUX_cut_res_not_error THEN
  PLOOPAUX_HANDLER_IH_TAC newl `nl:((A)word_loc)spt` PLOOPAUX_HANDLER_FIN_TAC THEN
  RULE_ASSUM_TAC(fun th -> if PLOOPAUX_is_eval_eq (concl th)
     then CAKE_SIMP_RULE[set_vars_def; loop_set_var_def; loop_dec_clock_def] th else th) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP PLOOPAUX_cut_res_live_imp o
    check (fun th -> is_eq (concl th) && is_pair (rand(lhs(concl th))) &&
                     (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "cut_res"
                      with Failure _ -> false) &&
                     not (is_const (fst(dest_pair(rand(lhs(concl th)))))))) THEN
  DISCH_THEN(MP_TAC o SPECL [`inter (l0:num_set) (lo:num_set)`; `l0:num_set`;
                             `lt:(num_set#num_set)list`; `nl:((A)word_loc)spt`]) THEN
  ASM_REWRITE_TAC PLOOPAUX_DOM_RWS THEN
  ANTS_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC PLOOPAUX_live_post_mono THEN EXISTS_TAC `l0:num_set` THEN
    ASM_REWRITE_TAC[domain_inter; INTER_SUBSET];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `nl2:((A)word_loc)spt` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `nl2:((A)word_loc)spt` THEN
  REWRITE_TAC[PLOOPAUX_eval_clause "loop_Call"] THEN
  SIMP[set_vars_def; loop_set_var_def; loop_dec_clock_def];;

let PLOOPAUX_CALL_PLAIN_TAC : tactic =
  RULE_ASSUM_TAC(fun th -> if PLOOPAUX_is_eval_eq (concl th)
                           then CAKE_SIMP_RULE[loop_dec_clock_def] th else th) THEN
  REWRITE_TAC[PLOOPAUX_eval_clause "loop_Call"] THEN
  SIMP[loop_dec_clock_def; set_vars_def; loop_set_var_def] THEN
  PLOOPAUX_NL_TAC PLOOPAUX_CALL_FIN_TAC;;

let PLOOPAUX_live_Call_SOME_SOME = prove
 (`!ns live dest args e h r lo (s:(A,FFI)loop_state).
    (!argvals prog env retvs s' st.
       get_vars args s = SOME argvals /\
       find_code dest argvals (loop_state_code s) = SOME (env,prog) /\
       ALL_DISTINCT ns /\ cut_res live (NONE:((A)loop_result)option,s) = (NONE,s') /\
       loop_evaluate (prog, loop_state_locals_fupd (K env) s') =
         (SOME (loop_Result retvs),st) /\
       LENGTH retvs = LENGTH ns
       ==> PLOOPAUX_live_P r
             (set_vars ns retvs (loop_state_locals_fupd (K (loop_state_locals s')) st))) /\
    (!argvals prog env exn s' st.
       get_vars args s = SOME argvals /\
       find_code dest argvals (loop_state_code s) = SOME (env,prog) /\
       ALL_DISTINCT ns /\ cut_res live (NONE:((A)loop_result)option,s) = (NONE,s') /\
       loop_evaluate (prog, loop_state_locals_fupd (K env) s') =
         (SOME (loop_Exception exn),st)
       ==> PLOOPAUX_live_P h
             (loop_set_var e exn (loop_state_locals_fupd (K (loop_state_locals s')) st)))
    ==> PLOOPAUX_live_P (loop_Call (SOME (ns,live)) dest args (SOME (e,h,r,lo))) s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[PLOOPAUX_live_P_def] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[PLOOPAUX_shrink_rws; LET_DEF; LET_END_DEF; case_def "option"; case_def "prod"] THEN
  REPEAT PAIRARG_TAC THEN
  REWRITE_TAC[PLOOPAUX_eval_clause "loop_Call"] THEN
  REWRITE_TAC (PLOOPAUX_clock_case_eqs @ [PAIR_EQ]) THEN STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE PLOOPAUX_result_rws) THEN TRY (FIRST_ASSUM CONTR_TAC) THEN
  RVEQ_TAC THEN PLOOPAUX_PAIR_VARS_TAC THEN
  PLOOPAUX_IHS2_TAC ALL_TAC THEN
  PLOOPAUX_CUT_CASES_TAC THEN PLOOPAUX_CALL_GV_TAC THEN
  PLOOPAUX_CALL_CUT_TAC
    `inter (live:num_set) (union (list_delete ns (l2:num_set)) (delete e (l3:num_set)))`
    `locals:((A)word_loc)spt` THEN
  RVEQ_TAC THEN
  (fun (asl,w as g) ->
     if exists (fun (_,th) -> try fst(dest_const(fst(strip_comb(concl th)))) =
                                  "PLOOPAUX_live_P" with Failure _ -> false) asl
     then PLOOPAUX_CALL_HANDLER_TAC
            `inter (locals:((A)word_loc)spt)
               (inter (live:num_set) (union (list_delete ns (l2:num_set))
                                            (delete e (l3:num_set))))` g
     else PLOOPAUX_CALL_PLAIN_TAC g));;

let PLOOPAUX_live_Call = prove
 (`!ret dest argvars handler (s:(A,FFI)loop_state).
     (!argvals live prog env x x' live_out r ns retvs s' st.
        get_vars argvars s = SOME argvals /\
        find_code dest argvals (loop_state_code s) = SOME (env,prog) /\
        ret = SOME (ns,live) /\ ALL_DISTINCT ns /\
        cut_res live (NONE:((A)loop_result)option,s) = (NONE,s') /\
        loop_evaluate (prog,loop_state_locals_fupd (K env) s') =
          (SOME (loop_Result retvs),st) /\
        LENGTH retvs = LENGTH ns /\ handler = SOME (x,x',r,live_out)
        ==> PLOOPAUX_live_P r
              (set_vars ns retvs (loop_state_locals_fupd (K (loop_state_locals s')) st))) /\
     (!argvals ns live prog env x live_out h n exn s' st.
        get_vars argvars s = SOME argvals /\
        find_code dest argvals (loop_state_code s) = SOME (env,prog) /\
        ret = SOME (ns,live) /\ ALL_DISTINCT ns /\
        cut_res live (NONE:((A)loop_result)option,s) = (NONE,s') /\
        loop_evaluate (prog,loop_state_locals_fupd (K env) s') =
          (SOME (loop_Exception exn),st) /\
        handler = SOME (n,h,x,live_out)
        ==> PLOOPAUX_live_P h
              (loop_set_var n exn (loop_state_locals_fupd (K (loop_state_locals s')) st))) /\
     (!argvals ns live prog env s'.
        get_vars argvars s = SOME argvals /\
        find_code dest argvals (loop_state_code s) = SOME (env,prog) /\
        ret = SOME (ns,live) /\ ALL_DISTINCT ns /\
        cut_res live (NONE:((A)loop_result)option,s) = (NONE,s')
        ==> PLOOPAUX_live_P prog (loop_state_locals_fupd (K env) s')) /\
     (!argvals prog env.
        get_vars argvars s = SOME argvals /\
        find_code dest argvals (loop_state_code s) = SOME (env,prog) /\
        ret = NONE /\ handler = NONE /\ ~(loop_state_clock s = 0)
        ==> PLOOPAUX_live_P prog (loop_state_locals_fupd (K env) (loop_dec_clock s)))
     ==> PLOOPAUX_live_P (loop_Call ret dest argvars handler) s`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `ret:(num list#num_set)option` (cases "option")) THEN
  REWRITE_TAC[PLOOPAUX_live_Call_NONE] THEN
  PAIR_CASES_ON `a:num list#num_set` THEN
  STRUCT_CASES_TAC (ISPEC `handler:(num#(A)loop_prog#(A)loop_prog#num_set)option`
                      (cases "option")) THEN
  REWRITE_TAC[PLOOPAUX_live_Call_SOME_NONE] THEN
  PAIR_CASES_ON `a:num#(A)loop_prog#(A)loop_prog#num_set` THEN
  REWRITE_TAC[option_INJ; option_DISTINCT; PAIR_EQ] THEN STRIP_TAC THEN
  MATCH_MP_TAC PLOOPAUX_live_Call_SOME_SOME THEN CONJ_TAC THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]);;

(* the induction *)

let PLOOPAUX_live_main = prove
 (`!p (s:(A,FFI)loop_state). PLOOPAUX_live_P p s`,
  SUBGOAL_THEN `!x:(A)loop_prog#(A,FFI)loop_state. PLOOPAUX_live_P (FST x) (SND x)`
    (fun th -> REWRITE_TAC[REWRITE_RULE[FORALL_PAIR_THM; FST; SND] th]) THEN
  MATCH_MP_TAC loop_evaluate_ind THEN REWRITE_TAC[FST; SND] THEN REPEAT CONJ_TAC THEN
  FIRST (map MATCH_ACCEPT_TAC
    [PLOOPAUX_live_Skip; PLOOPAUX_live_Fail; PLOOPAUX_live_Assign; PLOOPAUX_live_Primitive;
     PLOOPAUX_live_Arith; PLOOPAUX_live_Store; PLOOPAUX_live_SetGlobal;
     PLOOPAUX_live_Load32; PLOOPAUX_live_LoadByte; PLOOPAUX_live_Store32;
     PLOOPAUX_live_StoreByte; PLOOPAUX_live_Seq; PLOOPAUX_live_If; PLOOPAUX_live_Mark;
     PLOOPAUX_live_Break; PLOOPAUX_live_Continue; PLOOPAUX_live_Loop; PLOOPAUX_live_Raise;
     PLOOPAUX_live_Return; PLOOPAUX_live_ShMem; PLOOPAUX_live_Tick; PLOOPAUX_live_LocValue;
     PLOOPAUX_live_Call; PLOOPAUX_live_FFI]));;

(* HOL4: compile_correct *)

let loop_liveProof_compile_correct = prove
 (CASE_TERM
  `!v (v1:(A,FFI)loop_state) res s1 lt locals prog1 l1 l0.
     loop_evaluate (v,v1) = (res,s1) /\ ~(res = SOME loop_Error) /\
     loop_live_shrink lt v l0 = (prog1,l1) /\
     subspt (inter (loop_state_locals v1) l1) locals ==>
     ?new_locals.
       loop_evaluate (prog1, loop_state_locals_fupd (K locals) v1) =
       (res, loop_state_locals_fupd (K new_locals) s1) /\
       (match res with
          NONE -> subspt (inter (loop_state_locals s1) l0) new_locals
        | SOME (loop_Result v5) -> new_locals = loop_state_locals s1
        | SOME (loop_Exception v6) -> new_locals = loop_state_locals s1
        | SOME (loopSem_Break n) ->
            (match oEL n lt with
               SOME (_, brk) -> subspt (inter (loop_state_locals s1) brk) new_locals
             | NONE -> T)
        | SOME (loopSem_Continue n) ->
            (match oEL n lt with
               SOME (cont, _) -> subspt (inter (loop_state_locals s1) cont) new_locals
             | NONE -> T)
        | SOME loop_TimeOut -> new_locals = loop_state_locals s1
        | SOME (loop_FinalFFI v7) -> new_locals = loop_state_locals s1
        | SOME loop_Error -> new_locals = loop_state_locals s1)`,
  REWRITE_TAC[GSYM PLOOPAUX_live_post_def; GSYM PLOOPAUX_live_P_def; PLOOPAUX_live_main]);;

(* ------------------------------------------------------------------------- *)
(* mark_correct: a Mark is transparent, so marking evaluates the same; the  *)
(* equation is proved for every state, by induction on the semantics        *)
(* ------------------------------------------------------------------------- *)

let PLOOPAUX_cond_mark = prove
 (`!t (p:(A)loop_prog) (s:(A,FFI)loop_state).
     loop_evaluate ((if t then Mark p else p), s) = loop_evaluate (p, s)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[PLOOPAUX_eval_clause "Mark"]);;

let PLOOPAUX_MARK_SUBST_TAC : tactic =
  REPEAT(FIRST_X_ASSUM(fun th ->
    if is_eq (concl th) &&
       (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "mark_all"
        with Failure _ -> false)
    then SUBST_ALL_TAC th else NO_TAC)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FST]) THEN REWRITE_TAC[FST];;

let PLOOPAUX_mark_eq = prove
 (`!x:(A)loop_prog#(A,FFI)loop_state.
     loop_evaluate (FST (mark_all (FST x)), SND x) = loop_evaluate x`,
  MATCH_MP_TAC loop_evaluate_ind THEN REWRITE_TAC[FST; SND] THEN REPEAT CONJ_TAC THEN
  TRY (REPEAT GEN_TAC THEN REWRITE_TAC[mark_all_def; PLOOPAUX_eval_clause "Mark"] THEN
       NO_TAC) THENL
  [(* Seq *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[mark_all_def; LET_DEF; LET_END_DEF] THEN
   PAIR_CASES_ON `mark_all (c1:(A)loop_prog)` THEN
   PAIR_CASES_ON `mark_all (c2:(A)loop_prog)` THEN
   RULE_ASSUM_TAC(REWRITE_RULE[FST]) THEN
   REWRITE_TAC[case_def "prod"; FST; PLOOPAUX_cond_mark; PLOOPAUX_seq_clause] THEN
   ASM_REWRITE_TAC[] THEN
   PAIR_CASES_ON `loop_evaluate (c1:(A)loop_prog, s:(A,FFI)loop_state)` THEN
   REWRITE_TAC[case_def "prod"] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
   (* If *)
   REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[mark_all_def; LET_DEF; LET_END_DEF] THEN
   PAIR_CASES_ON `mark_all (c1:(A)loop_prog)` THEN
   PAIR_CASES_ON `mark_all (c2:(A)loop_prog)` THEN
   REWRITE_TAC[case_def "prod"; FST; PLOOPAUX_cond_mark] THEN
   REWRITE_TAC[PLOOPAUX_eval_clause "loop_If"] THEN
   REPEAT TOP_CASE_TAC THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
   FIRST_X_ASSUM(MP_TAC o CAKE_SIMP_RULE[] o check (is_forall o concl)) THEN
   COND_CASES_TAC THEN ASM_REWRITE_TAC[FST] THEN DISCH_THEN SUBST1_TAC THEN
   REWRITE_TAC[];
   (* Loop *)
   REPEAT GEN_TAC THEN
   REWRITE_TAC[mark_all_def; LET_DEF; LET_END_DEF] THEN
   PAIR_CASES_ON `mark_all (body:(A)loop_prog)` THEN REWRITE_TAC[case_def "prod"; FST] THEN
   STRIP_TAC THEN
   PAIR_CASES_ON `cut_res (live_in:num_set) (NONE:((A)loop_result)option,
                                            s:(A,FFI)loop_state)` THEN
   ASM_CASES_TAC `p0':((A)loop_result)option = NONE` THENL
   [ALL_TAC;
    MP_TAC(ISPECL [`live_in:num_set`; `p0:(A)loop_prog`; `live_out:num_set`;
                   `s:(A,FFI)loop_state`; `p0':((A)loop_result)option`;
                   `p1':(A,FFI)loop_state`] PLOOPAUX_loop_cut_not_NONE) THEN
    MP_TAC(ISPECL [`live_in:num_set`; `body:(A)loop_prog`; `live_out:num_set`;
                   `s:(A,FFI)loop_state`; `p0':((A)loop_result)option`;
                   `p1':(A,FFI)loop_state`] PLOOPAUX_loop_cut_not_NONE) THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[]] THEN
   POP_ASSUM SUBST_ALL_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN
   PAIR_CASES_ON `loop_evaluate (body:(A)loop_prog, p1':(A,FFI)loop_state)` THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `p1':(A,FFI)loop_state` o
     check (fun th -> is_forall (concl th) && length (fst(strip_forall (concl th))) = 1)) THEN
   ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   MP_TAC(ISPECL [`live_in:num_set`; `p0:(A)loop_prog`; `live_out:num_set`;
                  `s:(A,FFI)loop_state`; `p1':(A,FFI)loop_state`;
                  `p0'':((A)loop_result)option`; `p1'':(A,FFI)loop_state`]
                 PLOOPAUX_loop_unfold) THEN
   MP_TAC(ISPECL [`live_in:num_set`; `body:(A)loop_prog`; `live_out:num_set`;
                  `s:(A,FFI)loop_state`; `p1':(A,FFI)loop_state`;
                  `p0'':((A)loop_result)option`; `p1'':(A,FFI)loop_state`]
                 PLOOPAUX_loop_unfold) THEN
   ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
   ASM_CASES_TAC `p0'':((A)loop_result)option = NONE` THENL
   [POP_ASSUM SUBST_ALL_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE PLOOPAUX_result_rws) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
   ASM_CASES_TAC `p0'':((A)loop_result)option = SOME (loopSem_Continue 0)` THENL
   [POP_ASSUM SUBST_ALL_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE PLOOPAUX_result_rws) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
   ASM_CASES_TAC `p0'':((A)loop_result)option = SOME (loopSem_Break 0)` THENL
   [POP_ASSUM SUBST_ALL_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE PLOOPAUX_result_rws) THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
   ASM_SIMP_TAC[];
   (* Call *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[mark_all_def] THEN
   DISJ_CASES_THEN2 SUBST_ALL_TAC
     (X_CHOOSE_THEN `hd:num#(A)loop_prog#(A)loop_prog#num_set` SUBST_ALL_TAC)
     (ISPEC `handler:(num#(A)loop_prog#(A)loop_prog#num_set)option` (cases "option")) THEN
   REWRITE_TAC[case_def "option"; FST; PLOOPAUX_eval_clause "Mark"] THEN
   PAIR_CASES_ON `hd:num#(A)loop_prog#(A)loop_prog#num_set` THEN
   REWRITE_TAC[case_def "prod"; LET_DEF; LET_END_DEF] THEN
   PAIR_CASES_ON `mark_all (hd1:(A)loop_prog)` THEN
   PAIR_CASES_ON `mark_all (hd2:(A)loop_prog)` THEN
   REWRITE_TAC[case_def "prod"; FST; PLOOPAUX_cond_mark] THEN
   REWRITE_TAC[PLOOPAUX_eval_clause "loop_Call"] THEN REPEAT TOP_CASE_TAC THEN
   ASM_REWRITE_TAC[] THEN
   RULE_ASSUM_TAC(fun th -> if is_forall (concl th)
                            then CAKE_SIMP_RULE[option_INJ; PAIR_EQ] th else th) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
   PLOOPAUX_IHS2_TAC (ASM_REWRITE_TAC[]) THEN
   PLOOPAUX_MARK_SUBST_TAC THEN ASM_REWRITE_TAC[]]);;

let mark_correct = prove
 (`!prog (s:(A,FFI)loop_state) res s1.
     loop_evaluate (prog,s) = (res,s1) ==>
     loop_evaluate (FST (mark_all prog),s) = (res,s1)`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(SPEC `(prog:(A)loop_prog, s:(A,FFI)loop_state)` PLOOPAUX_mark_eq) THEN
  REWRITE_TAC[FST; SND]);;

let comp_correct = prove
 (`loop_evaluate (prog,(s:(A,FFI)loop_state)) = (res,s1) /\
   ~(res = SOME loop_Error) /\
   (!n. ~(res = SOME (loopSem_Break n))) /\
   (!n. ~(res = SOME (loopSem_Continue n))) /\
   ~(res = NONE) ==>
   loop_evaluate (loop_live_comp prog,s) = (res,s1)`,
  STRIP_TAC THEN REWRITE_TAC[loop_live_comp_def] THEN
  PAIR_CASES_ON `loop_live_shrink ([]:(num_set#num_set)list) (prog:(A)loop_prog) LN` THEN
  REWRITE_TAC[FST] THEN MATCH_MP_TAC mark_correct THEN
  MP_TAC(ISPECL [`prog:(A)loop_prog`; `s:(A,FFI)loop_state`; `res:((A)loop_result)option`;
                 `s1:(A,FFI)loop_state`; `[]:(num_set#num_set)list`;
                 `loop_state_locals (s:(A,FFI)loop_state)`; `p0:(A)loop_prog`;
                 `p1:num_set`; `LN:num_set`] loop_liveProof_compile_correct) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[subspt_lookup; lookup_inter_alt] THEN REPEAT GEN_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT];
    ALL_TAC] THEN
  REWRITE_TAC[record_fupdselfid "loop_state"] THEN
  DISCH_THEN(X_CHOOSE_THEN `nl:((A)word_loc)spt` MP_TAC) THEN
  UNDISCH_TAC `~(res:((A)loop_result)option = NONE)` THEN
  UNDISCH_TAC `!n. ~(res:((A)loop_result)option = SOME (loopSem_Continue n))` THEN
  UNDISCH_TAC `!n. ~(res:((A)loop_result)option = SOME (loopSem_Break n))` THEN
  UNDISCH_TAC `~(res:((A)loop_result)option = SOME loop_Error)` THEN
  STRUCT_CASES_TAC (ISPEC `res:((A)loop_result)option` (cases "option")) THEN
  REWRITE_TAC[case_def "option"; option_DISTINCT; option_INJ] THEN
  STRUCT_CASES_TAC (ISPEC `a:(A)loop_result` (cases "loop_result")) THEN
  REWRITE_TAC[case_def "loop_result"; distinctness "loop_result"; injectivity "loop_result"] THEN
  MESON_TAC[record_fupdselfid "loop_state"]);;

let loop_liveProof_optimise_correct = prove
 (`loop_evaluate (prog,(s:(A,FFI)loop_state)) = (res,s1) /\
   ~(res = SOME loop_Error) /\
   (!n. ~(res = SOME (loopSem_Break n))) /\
   (!n. ~(res = SOME (loopSem_Continue n))) /\
   ~(res = NONE) ==>
   loop_evaluate (optimise prog,s) = (res,s1)`,
  STRIP_TAC THEN REWRITE_TAC[optimise_def; o_THM] THEN
  PAIR_CASES_ON `loop_call_comp LN (prog:(A)loop_prog)` THEN REWRITE_TAC[FST] THEN
  MATCH_MP_TAC comp_correct THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`prog:(A)loop_prog`; `s:(A,FFI)loop_state`; `res:((A)loop_result)option`;
                 `s1:(A,FFI)loop_state`; `LN:num spt`; `p0:(A)loop_prog`; `p1:num spt`]
                loop_callProof_compile_correct) THEN
  ASM_SIMP_TAC[labels_in_def; lookup_def; option_DISTINCT]);;
